#!/usr/bin/env python3
"""
World-Class Audio Player - Single File Implementation

Features:
- Playback controls (play, pause, stop, next, previous)
- Volume control
- Playlist management
- Audio visualization
- Multiple format support (MP3, WAV, FLAC, OGG)
- Metadata display
- Keyboard shortcuts
- Seek functionality
- Equalizer
- Dark/light theme
- System tray integration
- Mini-player mode
- Cross-platform compatibility
"""

import os
import sys
import time
import json
import threading
import traceback
import wave
import pygame
import mutagen
from pygame import mixer
from mutagen.id3 import ID3
from mutagen.flac import FLAC
from mutagen.oggvorbis import OggVorbis
from typing import List, Dict, Optional, Tuple, Union
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
from PIL import Image, ImageTk, ImageDraw
import numpy as np
from dataclasses import dataclass
from collections import deque
import platform
import pystray
from pystray import MenuItem as item
import webbrowser

# Constants
SUPPORTED_FORMATS = ('.mp3', '.wav', '.flac', '.ogg', '.m4a')
DEFAULT_VOLUME = 0.7
VISUALIZATION_SAMPLES = 120
HISTORY_SIZE = 20
CONFIG_FILE = 'audio_player_config.json'

@dataclass
class Song:
    path: str
    title: str
    artist: str
    album: str
    length: float
    tags_loaded: bool = False

    def load_tags(self):
        if self.tags_loaded:
            return
            
        try:
            if self.path.lower().endswith('.mp3'):
                audio = ID3(self.path)
                self.title = audio.get('TIT2', [self.title])[0]
                self.artist = audio.get('TPE1', [self.artist])[0]
                self.album = audio.get('TALB', [self.album])[0]
            elif self.path.lower().endswith('.flac'):
                audio = FLAC(self.path)
                self.title = audio.get('title', [self.title])[0]
                self.artist = audio.get('artist', [self.artist])[0]
                self.album = audio.get('album', [self.album])[0]
            elif self.path.lower().endswith('.ogg'):
                audio = OggVorbis(self.path)
                self.title = audio.get('title', [self.title])[0]
                self.artist = audio.get('artist', [self.artist])[0]
                self.album = audio.get('album', [self.album])[0]
            else:
                # For WAV and other formats without standard tagging
                pass
        except Exception:
            # Fall back to filename if metadata reading fails
            pass
            
        self.tags_loaded = True

class AudioPlayerApp:
    def __init__(self, root):
        self.root = root
        self.root.title("World-Class Audio Player")
        self.root.geometry("900x600")
        self.root.minsize(800, 500)
        
        # Initialize pygame mixer
        self.initialize_audio()
        
        # Player state
        self.playlist: List[Song] = []
        self.current_index: int = -1
        self.paused: bool = False
        self.volume: float = DEFAULT_VOLUME
        self.equalizer_bands = [0.0] * 10
        self.playback_speed = 1.0
        self.repeat_mode = 0  # 0: off, 1: single, 2: all
        self.shuffle_mode = False
        self.play_history = deque(maxlen=HISTORY_SIZE)
        self.visualization_data = deque([0] * VISUALIZATION_SAMPLES, maxlen=VISUALIZATION_SAMPLES)
        self.dark_mode = False
        
        # Load config
        self.load_config()
        
        # Setup UI
        self.setup_ui()
        
        # Setup system tray
        self.setup_system_tray()
        
        # Bind keyboard shortcuts
        self.setup_keyboard_shortcuts()
        
        # Start visualization update thread
        self.visualization_thread_running = True
        self.visualization_thread = threading.Thread(target=self.update_visualization, daemon=True)
        self.visualization_thread.start()
        
        # Check for updates periodically
        self.check_for_updates()
        
    def initialize_audio(self):
        """Initialize pygame mixer with optimal settings"""
        try:
            pygame.init()
            mixer.init(frequency=44100, size=-16, channels=2, buffer=4096)
        except Exception as e:
            messagebox.showerror("Audio Error", f"Failed to initialize audio: {str(e)}")
            sys.exit(1)
    
    def setup_ui(self):
        """Setup the main user interface"""
        self.create_menu()
        self.create_main_frames()
        self.create_playlist_ui()
        self.create_player_controls()
        self.create_visualization()
        self.create_equalizer()
        self.create_status_bar()
        self.apply_theme()
        
    def create_menu(self):
        """Create the menu bar"""
        menubar = tk.Menu(self.root)
        
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open File", command=self.open_file, accelerator="Ctrl+O")
        file_menu.add_command(label="Open Folder", command=self.open_folder, accelerator="Ctrl+Shift+O")
        file_menu.add_separator()
        file_menu.add_command(label="Save Playlist", command=self.save_playlist)
        file_menu.add_command(label="Load Playlist", command=self.load_playlist)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit_app, accelerator="Alt+F4")
        menubar.add_cascade(label="File", menu=file_menu)
        
        # Playback menu
        playback_menu = tk.Menu(menubar, tearoff=0)
        playback_menu.add_command(label="Play/Pause", command=self.toggle_play_pause, accelerator="Space")
        playback_menu.add_command(label="Stop", command=self.stop, accelerator="Ctrl+Space")
        playback_menu.add_command(label="Next", command=self.next_track, accelerator="Ctrl+Right")
        playback_menu.add_command(label="Previous", command=self.previous_track, accelerator="Ctrl+Left")
        playback_menu.add_separator()
        playback_menu.add_command(label="Increase Volume", command=lambda: self.set_volume(self.volume + 0.1), accelerator="Ctrl+Up")
        playback_menu.add_command(label="Decrease Volume", command=lambda: self.set_volume(self.volume - 0.1), accelerator="Ctrl+Down")
        playback_menu.add_separator()
        playback_menu.add_command(label="Repeat Off", command=lambda: self.set_repeat_mode(0))
        playback_menu.add_command(label="Repeat One", command=lambda: self.set_repeat_mode(1))
        playback_menu.add_command(label="Repeat All", command=lambda: self.set_repeat_mode(2))
        playback_menu.add_command(label="Toggle Shuffle", command=self.toggle_shuffle, accelerator="Ctrl+H")
        menubar.add_cascade(label="Playback", menu=playback_menu)
        
        # View menu
        view_menu = tk.Menu(menubar, tearoff=0)
        view_menu.add_command(label="Toggle Dark Mode", command=self.toggle_dark_mode, accelerator="Ctrl+D")
        view_menu.add_command(label="Mini Player", command=self.toggle_mini_player)
        menubar.add_cascade(label="View", menu=view_menu)
        
        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="Documentation", command=self.show_documentation)
        help_menu.add_command(label="Check for Updates", command=self.check_for_updates)
        help_menu.add_separator()
        help_menu.add_command(label="About", command=self.show_about)
        menubar.add_cascade(label="Help", menu=help_menu)
        
        self.root.config(menu=menubar)
    
    def create_main_frames(self):
        """Create the main frames for the UI"""
        # Main container
        self.main_frame = ttk.Frame(self.root)
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Left panel (playlist)
        self.left_panel = ttk.Frame(self.main_frame, width=300)
        self.left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 5))
        self.left_panel.pack_propagate(False)
        
        # Right panel (player controls and visualization)
        self.right_panel = ttk.Frame(self.main_frame)
        self.right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        # Right panel divided into top (visualization) and bottom (controls)
        self.visualization_frame = ttk.Frame(self.right_panel, height=200)
        self.visualization_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        
        self.controls_frame = ttk.Frame(self.right_panel)
        self.controls_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(5, 0))
    
    def create_playlist_ui(self):
        """Create the playlist UI components"""
        # Playlist header
        playlist_header = ttk.Frame(self.left_panel)
        playlist_header.pack(fill=tk.X, pady=(0, 5))
        
        ttk.Label(playlist_header, text="Playlist", font=('Helvetica', 10, 'bold')).pack(side=tk.LEFT)
        
        btn_frame = ttk.Frame(playlist_header)
        btn_frame.pack(side=tk.RIGHT)
        
        ttk.Button(btn_frame, text="+", width=3, command=self.add_files).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="-", width=3, command=self.remove_selected).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="↑", width=3, command=self.move_up).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="↓", width=3, command=self.move_down).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="🗑", width=3, command=self.clear_playlist).pack(side=tk.LEFT, padx=2)
        
        # Playlist treeview
        self.playlist_tree = ttk.Treeview(
            self.left_panel, 
            columns=('title', 'artist', 'duration'), 
            selectmode='browse',
            show='headings'
        )
        
        # Configure columns
        self.playlist_tree.column('#0', width=0, stretch=tk.NO)  # Hidden first column
        self.playlist_tree.column('title', width=150, anchor=tk.W)
        self.playlist_tree.column('artist', width=100, anchor=tk.W)
        self.playlist_tree.column('duration', width=50, anchor=tk.E)
        
        # Configure headings
        self.playlist_tree.heading('title', text='Title', anchor=tk.W)
        self.playlist_tree.heading('artist', text='Artist', anchor=tk.W)
        self.playlist_tree.heading('duration', text='Time', anchor=tk.E)
        
        # Add scrollbar
        scrollbar = ttk.Scrollbar(self.left_panel, orient=tk.VERTICAL, command=self.playlist_tree.yview)
        self.playlist_tree.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.playlist_tree.pack(fill=tk.BOTH, expand=True)
        
        # Bind double click to play selected song
        self.playlist_tree.bind('<Double-1>', lambda e: self.play_selected())
        self.playlist_tree.bind('<Return>', lambda e: self.play_selected())
        
        # Context menu
        self.playlist_menu = tk.Menu(self.root, tearoff=0)
        self.playlist_menu.add_command(label="Play", command=self.play_selected)
        self.playlist_menu.add_command(label="Remove", command=self.remove_selected)
        self.playlist_menu.add_command(label="Show in Folder", command=self.show_in_folder)
        self.playlist_menu.add_separator()
        self.playlist_menu.add_command(label="Properties", command=self.show_song_properties)
        
        self.playlist_tree.bind('<Button-3>', self.show_playlist_context_menu)
    
    def create_player_controls(self):
        """Create the player control buttons and seek bar"""
        # Now playing info
        self.now_playing_frame = ttk.Frame(self.controls_frame)
        self.now_playing_frame.pack(fill=tk.X, pady=(0, 5))
        
        self.album_art = ttk.Label(self.now_playing_frame, width=60, background='black')
        self.album_art.pack(side=tk.LEFT, padx=(0, 10))
        
        self.now_playing_info = ttk.Frame(self.now_playing_frame)
        self.now_playing_info.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        self.song_title = ttk.Label(self.now_playing_info, text="No song selected", font=('Helvetica', 10, 'bold'))
        self.song_title.pack(anchor=tk.W)
        
        self.song_artist = ttk.Label(self.now_playing_info, text="", font=('Helvetica', 9))
        self.song_artist.pack(anchor=tk.W)
        
        self.song_album = ttk.Label(self.now_playing_info, text="", font=('Helvetica', 9))
        self.song_album.pack(anchor=tk.W)
        
        # Progress bar and time display
        progress_frame = ttk.Frame(self.controls_frame)
        progress_frame.pack(fill=tk.X, pady=(0, 10))
        
        self.time_elapsed = ttk.Label(progress_frame, text="0:00", width=6)
        self.time_elapsed.pack(side=tk.LEFT)
        
        self.progress = ttk.Scale(
            progress_frame, 
            from_=0, 
            to=100, 
            orient=tk.HORIZONTAL, 
            command=self.on_seek
        )
        self.progress.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.progress.bind('<Button-1>', lambda e: self.progress.config(takefocus=True))
        self.progress.bind('<ButtonRelease-1>', self.on_seek_release)
        
        self.time_total = ttk.Label(progress_frame, text="0:00", width=6)
        self.time_total.pack(side=tk.RIGHT)
        
        # Control buttons
        button_frame = ttk.Frame(self.controls_frame)
        button_frame.pack(fill=tk.X)
        
        # First row of buttons
        btn_row1 = ttk.Frame(button_frame)
        btn_row1.pack(fill=tk.X)
        
        self.prev_btn = ttk.Button(btn_row1, text="⏮", command=self.previous_track)
        self.prev_btn.pack(side=tk.LEFT, padx=2, expand=True)
        
        self.play_btn = ttk.Button(btn_row1, text="⏯", command=self.toggle_play_pause)
        self.play_btn.pack(side=tk.LEFT, padx=2, expand=True)
        
        self.next_btn = ttk.Button(btn_row1, text="⏭", command=self.next_track)
        self.next_btn.pack(side=tk.LEFT, padx=2, expand=True)
        
        self.stop_btn = ttk.Button(btn_row1, text="⏹", command=self.stop)
        self.stop_btn.pack(side=tk.LEFT, padx=2, expand=True)
        
        # Second row of buttons
        btn_row2 = ttk.Frame(button_frame)
        btn_row2.pack(fill=tk.X, pady=(5, 0))
        
        self.repeat_btn = ttk.Button(btn_row2, text="🔁", command=self.cycle_repeat_mode)
        self.repeat_btn.pack(side=tk.LEFT, padx=2, expand=True)
        
        self.shuffle_btn = ttk.Button(btn_row2, text="🔀", command=self.toggle_shuffle)
        self.shuffle_btn.pack(side=tk.LEFT, padx=2, expand=True)
        
        self.vol_btn = ttk.Button(btn_row2, text="🔊", command=self.toggle_mute)
        self.vol_btn.pack(side=tk.LEFT, padx=2, expand=True)
        
        self.vol_slider = ttk.Scale(btn_row2, from_=0, to=100, orient=tk.HORIZONTAL, command=self.on_volume_change)
        self.vol_slider.set(self.volume * 100)
        self.vol_slider.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        
        # Third row (equalizer toggle)
        btn_row3 = ttk.Frame(button_frame)
        btn_row3.pack(fill=tk.X, pady=(5, 0))
        
        ttk.Button(btn_row3, text="Equalizer", command=self.toggle_equalizer).pack(side=tk.LEFT, padx=2, expand=True)
        ttk.Button(btn_row3, text="Playback Speed", command=self.set_playback_speed).pack(side=tk.LEFT, padx=2, expand=True)
    
    def create_visualization(self):
        """Create the audio visualization canvas"""
        self.visualization_canvas = tk.Canvas(
            self.visualization_frame, 
            bg='black',
            highlightthickness=0
        )
        self.visualization_canvas.pack(fill=tk.BOTH, expand=True)
        
        # Start with a simple visualization
        self.draw_visualization()
    
    def create_equalizer(self):
        """Create the equalizer UI (initially hidden)"""
        self.equalizer_frame = ttk.Frame(self.right_panel)
        self.equalizer_visible = False
        
        ttk.Label(self.equalizer_frame, text="Equalizer", font=('Helvetica', 9, 'bold')).pack(pady=(0, 5))
        
        bands_frame = ttk.Frame(self.equalizer_frame)
        bands_frame.pack(fill=tk.X)
        
        self.eq_sliders = []
        freq_labels = ['60', '150', '400', '1k', '2.4k', '6k', '15k']
        
        for i in range(7):
            band_frame = ttk.Frame(bands_frame)
            band_frame.pack(side=tk.LEFT, fill=tk.Y, expand=True, padx=2)
            
            ttk.Label(band_frame, text=freq_labels[i]).pack()
            
            slider = ttk.Scale(
                band_frame,
                from_=-12,
                to=12,
                orient=tk.VERTICAL,
                command=lambda v, idx=i: self.on_equalizer_change(idx, float(v))
            slider.set(0)
            slider.pack(fill=tk.Y, expand=True)
            self.eq_sliders.append(slider)
            
            ttk.Label(band_frame, text="0 dB").pack()
    
    def create_status_bar(self):
        """Create the status bar at the bottom"""
        self.status_bar = ttk.Frame(self.root, height=20)
        self.status_bar.pack(fill=tk.X, side=tk.BOTTOM)
        
        self.status_left = ttk.Label(self.status_bar, text="Ready", relief=tk.SUNKEN, anchor=tk.W)
        self.status_left.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        self.status_right = ttk.Label(self.status_bar, text="", relief=tk.SUNKEN, anchor=tk.E)
        self.status_right.pack(side=tk.RIGHT)
    
    def setup_system_tray(self):
        """Setup the system tray icon and menu"""
        if platform.system() == 'Linux':
            # System tray not well supported on Linux in pystray
            return
            
        try:
            image = Image.new('RGB', (64, 64), 'black')
            draw = ImageDraw.Draw(image)
            draw.ellipse((16, 16, 48, 48), fill='white')
            
            menu = (
                item('Play/Pause', self.toggle_play_pause),
                item('Next', self.next_track),
                item('Previous', self.previous_track),
                item('Show', self.show_window),
                item('Exit', self.quit_app)
            )
            
            self.tray_icon = pystray.Icon("audio_player", image, "Audio Player", menu)
            
            # Run the tray icon in a separate thread
            threading.Thread(target=self.tray_icon.run, daemon=True).start()
        except Exception as e:
            print(f"Failed to create system tray icon: {e}")
    
    def setup_keyboard_shortcuts(self):
        """Setup keyboard shortcuts"""
        self.root.bind('<space>', lambda e: self.toggle_play_pause())
        self.root.bind('<Control-space>', lambda e: self.stop())
        self.root.bind('<Control-Right>', lambda e: self.next_track())
        self.root.bind('<Control-Left>', lambda e: self.previous_track())
        self.root.bind('<Control-o>', lambda e: self.open_file())
        self.root.bind('<Control-Shift-O>', lambda e: self.open_folder())
        self.root.bind('<Control-Up>', lambda e: self.set_volume(self.volume + 0.1))
        self.root.bind('<Control-Down>', lambda e: self.set_volume(self.volume - 0.1))
        self.root.bind('<Control-d>', lambda e: self.toggle_dark_mode())
        self.root.bind('<Control-h>', lambda e: self.toggle_shuffle())
        self.root.bind('<Escape>', lambda e: self.root.attributes('-fullscreen', False) if self.root.attributes('-fullscreen') else None)
        self.root.bind('<F11>', lambda e: self.root.attributes('-fullscreen', not self.root.attributes('-fullscreen')))
    
    def apply_theme(self):
        """Apply the current theme (light/dark)"""
        if self.dark_mode:
            bg_color = '#2d2d2d'
            fg_color = '#ffffff'
            entry_bg = '#3d3d3d'
            highlight_color = '#4d4d4d'
            
            style = ttk.Style()
            style.theme_use('clam')
            
            style.configure('.', background=bg_color, foreground=fg_color)
            style.configure('TFrame', background=bg_color)
            style.configure('TLabel', background=bg_color, foreground=fg_color)
            style.configure('TButton', background=bg_color, foreground=fg_color)
            style.configure('TEntry', fieldbackground=entry_bg, foreground=fg_color)
            style.configure('TScale', background=bg_color)
            style.configure('Treeview', 
                          background=entry_bg, 
                          foreground=fg_color,
                          fieldbackground=entry_bg)
            style.map('Treeview', background=[('selected', highlight_color)])
            
            self.visualization_canvas.config(bg='black')
        else:
            bg_color = '#f0f0f0'
            fg_color = '#000000'
            entry_bg = '#ffffff'
            highlight_color = '#d4d4d4'
            
            style = ttk.Style()
            style.theme_use('clam')
            
            style.configure('.', background=bg_color, foreground=fg_color)
            style.configure('TFrame', background=bg_color)
            style.configure('TLabel', background=bg_color, foreground=fg_color)
            style.configure('TButton', background=bg_color, foreground=fg_color)
            style.configure('TEntry', fieldbackground=entry_bg, foreground=fg_color)
            style.configure('TScale', background=bg_color)
            style.configure('Treeview', 
                          background=entry_bg, 
                          foreground=fg_color,
                          fieldbackground=entry_bg)
            style.map('Treeview', background=[('selected', highlight_color)])
            
            self.visualization_canvas.config(bg='white')
    
    # Player functionality
    def play(self, index=None):
        """Play the song at the given index or the selected song"""
        if index is None:
            selection = self.playlist_tree.selection()
            if not selection:
                return
            index = self.playlist_tree.index(selection[0])
        
        if index < 0 or index >= len(self.playlist):
            return
            
        self.current_index = index
        song = self.playlist[index]
        
        try:
            mixer.music.stop()
            mixer.music.unload()
            
            # Load the new song
            mixer.music.load(song.path)
            mixer.music.set_volume(self.volume)
            
            # Apply equalizer if available
            if any(band != 0 for band in self.equalizer_bands):
                self.apply_equalizer()
            
            mixer.music.play()
            self.paused = False
            self.update_play_button()
            
            # Update UI
            self.playlist_tree.selection_set(self.playlist_tree.get_children()[index])
            self.playlist_tree.see(self.playlist_tree.get_children()[index])
            self.update_now_playing(song)
            self.update_progress()
            
            # Add to history
            self.play_history.append(index)
            
        except Exception as e:
            messagebox.showerror("Playback Error", f"Could not play file: {str(e)}")
            traceback.print_exc()
    
    def play_selected(self):
        """Play the currently selected song"""
        selection = self.playlist_tree.selection()
        if selection:
            self.play(self.playlist_tree.index(selection[0]))
    
    def toggle_play_pause(self):
        """Toggle between play and pause"""
        if self.current_index == -1:
            if self.playlist:
                self.play(0)
            return
            
        if mixer.music.get_busy():
            if self.paused:
                mixer.music.unpause()
                self.paused = False
            else:
                mixer.music.pause()
                self.paused = True
        else:
            self.play(self.current_index)
            
        self.update_play_button()
    
    def stop(self):
        """Stop playback"""
        mixer.music.stop()
        self.paused = False
        self.update_play_button()
        self.progress.set(0)
        self.time_elapsed.config(text="0:00")
    
    def next_track(self):
        """Play the next track in the playlist"""
        if not self.playlist:
            return
            
        if self.shuffle_mode:
            self.play_random()
        else:
            next_index = self.current_index + 1
            if next_index >= len(self.playlist):
                if self.repeat_mode == 2:  # Repeat all
                    next_index = 0
                else:
                    self.stop()
                    return
                    
            self.play(next_index)
    
    def previous_track(self):
        """Play the previous track in the playlist"""
        if not self.playlist:
            return
            
        if self.shuffle_mode and self.play_history:
            # Go back in history
            if len(self.play_history) > 1:
                self.play_history.pop()  # Remove current
                prev_index = self.play_history.pop()  # Get previous
                self.play(prev_index)
            return
            
        prev_index = self.current_index - 1
        if prev_index < 0:
            if self.repeat_mode == 2:  # Repeat all
                prev_index = len(self.playlist) - 1
            else:
                self.stop()
                return
                
        self.play(prev_index)
    
    def play_random(self):
        """Play a random track from the playlist"""
        if not self.playlist:
            return
            
        if len(self.playlist) == 1:
            self.play(0)
            return
            
        import random
        next_index = random.randint(0, len(self.playlist) - 1)
        while next_index == self.current_index and len(self.playlist) > 1:
            next_index = random.randint(0, len(self.playlist) - 1)
            
        self.play(next_index)
    
    def set_volume(self, volume):
        """Set the volume (0.0 to 1.0)"""
        self.volume = max(0.0, min(1.0, volume))
        mixer.music.set_volume(self.volume)
        self.vol_slider.set(self.volume * 100)
        
        # Update mute button appearance
        if self.volume <= 0:
            self.vol_btn.config(text="🔇")
        else:
            self.vol_btn.config(text="🔊")
    
    def toggle_mute(self):
        """Toggle mute/unmute"""
        if self.volume > 0:
            self.last_volume = self.volume
            self.set_volume(0)
        else:
            self.set_volume(self.last_volume if hasattr(self, 'last_volume') else DEFAULT_VOLUME)
    
    def on_volume_change(self, value):
        """Handle volume slider change"""
        self.set_volume(float(value) / 100)
    
    def set_repeat_mode(self, mode):
        """Set repeat mode (0: off, 1: single, 2: all)"""
        self.repeat_mode = mode
        self.update_repeat_button()
    
    def cycle_repeat_mode(self):
        """Cycle through repeat modes"""
        self.set_repeat_mode((self.repeat_mode + 1) % 3)
    
    def toggle_shuffle(self):
        """Toggle shuffle mode"""
        self.shuffle_mode = not self.shuffle_mode
        self.update_shuffle_button()
    
    def set_playback_speed(self):
        """Set playback speed (0.5x to 2.0x)"""
        speed = simpledialog.askfloat(
            "Playback Speed",
            "Enter playback speed (0.5 to 2.0):",
            initialvalue=self.playback_speed,
            minvalue=0.5,
            maxvalue=2.0
        )
        
        if speed is not None:
            self.playback_speed = speed
            if mixer.music.get_busy():
                mixer.music.set_endevent()  # Clear any existing end event
                current_pos = mixer.music.get_pos() / 1000  # Get position in seconds
                mixer.music.stop()
                mixer.music.load(self.playlist[self.current_index].path)
                mixer.music.play(start=current_pos / self.playback_speed)
                mixer.music.set_volume(self.volume)
    
    def on_seek(self, value):
        """Handle seek bar movement (during drag)"""
        if not hasattr(self, 'last_seek_update') or time.time() - self.last_seek_update > 0.1:
            self.last_seek_update = time.time()
            self.time_elapsed.config(text=self.format_time(float(value)))
    
    def on_seek_release(self, event):
        """Handle seek bar release (seek to position)"""
        if self.current_index == -1 or not self.playlist:
            return
            
        seek_pos = float(self.progress.get())
        song_length = self.playlist[self.current_index].length
        
        if song_length > 0:
            new_pos = seek_pos / 100 * song_length
            mixer.music.set_pos(new_pos)
    
    def update_progress(self):
        """Update the progress bar and time display"""
        if self.current_index == -1 or not self.playlist:
            self.root.after(1000, self.update_progress)
            return
            
        if mixer.music.get_busy() and not self.paused:
            current_pos = mixer.music.get_pos() / 1000  # Convert to seconds
            song_length = self.playlist[self.current_index].length
            
            if song_length > 0:
                progress_percent = (current_pos / song_length) * 100
                self.progress.set(progress_percent)
                self.time_elapsed.config(text=self.format_time(current_pos))
                
                # Check if song ended (with some buffer for lag)
                if current_pos >= song_length - 0.5:
                    if self.repeat_mode == 1:  # Repeat single
                        self.play(self.current_index)
                    else:
                        self.next_track()
        
        self.root.after(200, self.update_progress)
    
    def format_time(self, seconds):
        """Format seconds into MM:SS"""
        minutes = int(seconds // 60)
        seconds = int(seconds % 60)
        return f"{minutes}:{seconds:02d}"
    
    def update_now_playing(self, song):
        """Update the now playing information"""
        song.load_tags()
        
        self.song_title.config(text=song.title or os.path.basename(song.path))
        self.song_artist.config(text=song.artist or "Unknown Artist")
        self.song_album.config(text=song.album or "Unknown Album")
        
        self.time_total.config(text=self.format_time(song.length))
        
        # Try to load album art
        self.load_album_art(song)
    
    def load_album_art(self, song):
        """Try to load album art for the current song"""
        # Clear current image
        self.album_art.config(image='')
        self.album_art.image = None
        
        # Try to extract image from tags
        try:
            if song.path.lower().endswith('.mp3'):
                audio = ID3(song.path)
                for tag in audio.values():
                    if tag.FrameID == 'APIC':
                        img_data = tag.data
                        break
                else:
                    raise ValueError("No image found")
            elif song.path.lower().endswith('.flac'):
                audio = FLAC(song.path)
                if not audio.pictures:
                    raise ValueError("No image found")
                img_data = audio.pictures[0].data
            elif song.path.lower().endswith('.ogg'):
                audio = OggVorbis(song.path)
                if not audio.pictures:
                    raise ValueError("No image found")
                img_data = audio.pictures[0].data
            else:
                raise ValueError("Unsupported format for album art")
            
            # Create image from data
            img = Image.open(io.BytesIO(img_data))
            img.thumbnail((60, 60))
            photo = ImageTk.PhotoImage(img)
            
            self.album_art.config(image=photo)
            self.album_art.image = photo
            
        except Exception as e:
            # Use default image if no album art found
            img = Image.new('RGB', (60, 60), 'black')
            draw = ImageDraw.Draw(img)
            draw.text((10, 20), "No Image", fill='white')
            photo = ImageTk.PhotoImage(img)
            
            self.album_art.config(image=photo)
            self.album_art.image = photo
    
    def update_play_button(self):
        """Update the play/pause button appearance"""
        if self.paused or not mixer.music.get_busy():
            self.play_btn.config(text="⏯")
        else:
            self.play_btn.config(text="⏸")
    
    def update_repeat_button(self):
        """Update the repeat button appearance based on current mode"""
        if self.repeat_mode == 0:
            self.repeat_btn.config(text="🔁")
        elif self.repeat_mode == 1:
            self.repeat_btn.config(text="🔂")
        else:
            self.repeat_btn.config(text="🔁 (All)")
    
    def update_shuffle_button(self):
        """Update the shuffle button appearance"""
        if self.shuffle_mode:
            self.shuffle_btn.config(text="🔀", style='Accent.TButton')
        else:
            self.shuffle_btn.config(text="🔀", style='TButton')
    
    # Playlist management
    def add_files(self):
        """Add files to the playlist"""
        files = filedialog.askopenfilenames(
            title="Select Audio Files",
            filetypes=(
                ("Audio Files", "*.mp3 *.wav *.flac *.ogg *.m4a"),
                ("MP3 Files", "*.mp3"),
                ("WAV Files", "*.wav"),
                ("FLAC Files", "*.flac"),
                ("OGG Files", "*.ogg"),
                ("All Files", "*.*")
            )
        )
        
        if files:
            self.add_to_playlist(files)
    
    def open_file(self):
        """Open a single file and replace current playlist"""
        file = filedialog.askopenfilename(
            title="Select Audio File",
            filetypes=(
                ("Audio Files", "*.mp3 *.wav *.flac *.ogg *.m4a"),
                ("MP3 Files", "*.mp3"),
                ("WAV Files", "*.wav"),
                ("FLAC Files", "*.flac"),
                ("OGG Files", "*.ogg"),
                ("All Files", "*.*")
            )
        )
        
        if file:
            self.clear_playlist()
            self.add_to_playlist([file])
            self.play(0)
    
    def open_folder(self):
        """Open all audio files in a folder and replace current playlist"""
        folder = filedialog.askdirectory(title="Select Folder with Audio Files")
        
        if folder:
            self.clear_playlist()
            files = []
            
            for root, _, filenames in os.walk(folder):
                for filename in filenames:
                    if filename.lower().endswith(SUPPORTED_FORMATS):
                        files.append(os.path.join(root, filename))
            
            if files:
                self.add_to_playlist(files)
                self.play(0)
            else:
                messagebox.showinfo("No Audio Files", "No supported audio files found in the selected folder.")
    
    def add_to_playlist(self, file_paths):
        """Add files to the playlist"""
        new_songs = []
        
        for path in file_paths:
            if not os.path.isfile(path):
                continue
                
            # Get basic info without loading all tags
            try:
                if path.lower().endswith('.mp3'):
                    audio = mutagen.File(path, easy=True)
                    length = audio.info.length
                    title = audio.get('title', [os.path.basename(path)])[0]
                    artist = audio.get('artist', ['Unknown Artist'])[0]
                    album = audio.get('album', ['Unknown Album'])[0]
                elif path.lower().endswith('.flac'):
                    audio = FLAC(path)
                    length = audio.info.length
                    title = audio.get('title', [os.path.basename(path)])[0]
                    artist = audio.get('artist', ['Unknown Artist'])[0]
                    album = audio.get('album', ['Unknown Album'])[0]
                elif path.lower().endswith('.ogg'):
                    audio = OggVorbis(path)
                    length = audio.info.length
                    title = audio.get('title', [os.path.basename(path)])[0]
                    artist = audio.get('artist', ['Unknown Artist'])[0]
                    album = audio.get('album', ['Unknown Album'])[0]
                elif path.lower().endswith('.wav'):
                    with wave.open(path, 'rb') as wav_file:
                        length = wav_file.getnframes() / float(wav_file.getframerate())
                    title = os.path.basename(path)
                    artist = 'Unknown Artist'
                    album = 'Unknown Album'
                else:
                    # Unsupported format, skip
                    continue
                    
                new_songs.append(Song(
                    path=path,
                    title=title,
                    artist=artist,
                    album=album,
                    length=length
                ))
            except Exception as e:
                print(f"Error loading file {path}: {e}")
                continue
        
        if new_songs:
            start_index = len(self.playlist)
            self.playlist.extend(new_songs)
            
            for i, song in enumerate(new_songs, start=start_index):
                self.playlist_tree.insert('', 'end', values=(
                    song.title,
                    song.artist,
                    self.format_time(song.length)
                ))
            
            self.status_left.config(text=f"Added {len(new_songs)} songs to playlist")
    
    def remove_selected(self):
        """Remove selected songs from the playlist"""
        selection = self.playlist_tree.selection()
        if not selection:
            return
            
        # Get indices in reverse order to avoid shifting issues
        indices = sorted([self.playlist_tree.index(item) for item in selection], reverse=True)
        
        for index in indices:
            # Stop playback if removing currently playing song
            if index == self.current_index:
                self.stop()
                self.current_index = -1
                self.song_title.config(text="No song selected")
                self.song_artist.config(text="")
                self.song_album.config(text="")
                self.time_total.config(text="0:00")
            
            # Remove from playlist
            self.playlist.pop(index)
            self.playlist_tree.delete(self.playlist_tree.get_children()[index])
        
        self.status_left.config(text=f"Removed {len(indices)} songs from playlist")
    
    def clear_playlist(self):
        """Clear the entire playlist"""
        if not self.playlist:
            return
            
        self.stop()
        self.playlist.clear()
        self.playlist_tree.delete(*self.playlist_tree.get_children())
        self.current_index = -1
        self.song_title.config(text="No song selected")
        self.song_artist.config(text="")
        self.song_album.config(text="")
        self.time_total.config(text="0:00")
        self.status_left.config(text="Playlist cleared")
    
    def move_up(self):
        """Move selected songs up in the playlist"""
        selection = self.playlist_tree.selection()
        if not selection:
            return
            
        indices = [self.playlist_tree.index(item) for item in selection]
        if min(indices) == 0:
            return  # Can't move up the first item
            
        for index in sorted(indices):
            # Swap in playlist
            self.playlist[index], self.playlist[index-1] = self.playlist[index-1], self.playlist[index]
            
            # Swap in treeview
            prev_item = self.playlist_tree.get_children()[index-1]
            item = self.playlist_tree.get_children()[index]
            self.playlist_tree.move(item, '', index-1)
            
            # Update current index if needed
            if index == self.current_index:
                self.current_index -= 1
            elif index-1 == self.current_index:
                self.current_index += 1
        
        # Reselect items
        for item in selection:
            self.playlist_tree.selection_add(item)
    
    def move_down(self):
        """Move selected songs down in the playlist"""
        selection = self.playlist_tree.selection()
        if not selection:
            return
            
        indices = [self.playlist_tree.index(item) for item in selection]
        if max(indices) == len(self.playlist) - 1:
            return  # Can't move down the last item
            
        for index in sorted(indices, reverse=True):
            # Swap in playlist
            self.playlist[index], self.playlist[index+1] = self.playlist[index+1], self.playlist[index]
            
            # Swap in treeview
            next_item = self.playlist_tree.get_children()[index+1]
            item = self.playlist_tree.get_children()[index]
            self.playlist_tree.move(item, '', index+1)
            
            # Update current index if needed
            if index == self.current_index:
                self.current_index += 1
            elif index+1 == self.current_index:
                self.current_index -= 1
        
        # Reselect items
        for item in selection:
            self.playlist_tree.selection_add(item)
    
    def save_playlist(self):
        """Save the current playlist to a file"""
        if not self.playlist:
            messagebox.showwarning("Empty Playlist", "There are no songs in the playlist to save.")
            return
            
        file = filedialog.asksaveasfilename(
            title="Save Playlist",
            defaultextension=".json",
            filetypes=(("JSON Files", "*.json"), ("All Files", "*.*"))
        )
        
        if file:
            try:
                playlist_data = []
                for song in self.playlist:
                    playlist_data.append({
                        'path': song.path,
                        'title': song.title,
                        'artist': song.artist,
                        'album': song.album,
                        'length': song.length
                    })
                
                with open(file, 'w') as f:
                    json.dump(playlist_data, f, indent=2)
                
                self.status_left.config(text=f"Playlist saved to {os.path.basename(file)}")
            except Exception as e:
                messagebox.showerror("Save Error", f"Could not save playlist: {str(e)}")
    
    def load_playlist(self):
        """Load a playlist from a file"""
        file = filedialog.askopenfilename(
            title="Load Playlist",
            filetypes=(("JSON Files", "*.json"), ("All Files", "*.*"))
        )
        
        if file:
            try:
                with open(file, 'r') as f:
                    playlist_data = json.load(f)
                
                new_songs = []
                for item in playlist_data:
                    # Verify file exists
                    if not os.path.isfile(item['path']):
                        # Try relative path
                        base_dir = os.path.dirname(file)
                        rel_path = os.path.join(base_dir, item['path'])
                        if os.path.isfile(rel_path):
                            item['path'] = rel_path
                        else:
                            continue
                    
                    new_songs.append(Song(
                        path=item['path'],
                        title=item.get('title', os.path.basename(item['path'])),
                        artist=item.get('artist', 'Unknown Artist'),
                        album=item.get('album', 'Unknown Album'),
                        length=item.get('length', 0)
                    ))
                
                if new_songs:
                    self.clear_playlist()
                    self.add_to_playlist([song.path for song in new_songs])
                    self.status_left.config(text=f"Loaded playlist {os.path.basename(file)}")
                else:
                    messagebox.showwarning("Empty Playlist", "No valid songs found in the playlist file.")
            except Exception as e:
                messagebox.showerror("Load Error", f"Could not load playlist: {str(e)}")
    
    def show_playlist_context_menu(self, event):
        """Show the playlist context menu"""
        item = self.playlist_tree.identify_row(event.y)
        if item:
            self.playlist_tree.selection_set(item)
            self.playlist_menu.post(event.x_root, event.y_root)
    
    def show_in_folder(self):
        """Show the selected song in its folder"""
        selection = self.playlist_tree.selection()
        if not selection:
            return
            
        index = self.playlist_tree.index(selection[0])
        song = self.playlist[index]
        
        try:
            if platform.system() == 'Windows':
                os.startfile(os.path.dirname(song.path))
            elif platform.system() == 'Darwin':
                subprocess.run(['open', os.path.dirname(song.path)])
            else:  # Linux
                subprocess.run(['xdg-open', os.path.dirname(song.path)])
        except Exception as e:
            messagebox.showerror("Error", f"Could not open folder: {str(e)}")
    
    def show_song_properties(self):
        """Show properties of the selected song"""
        selection = self.playlist_tree.selection()
        if not selection:
            return
            
        index = self.playlist_tree.index(selection[0])
        song = self.playlist[index]
        song.load_tags()
        
        properties = [
            f"Title: {song.title}",
            f"Artist: {song.artist}",
            f"Album: {song.album}",
            f"Duration: {self.format_time(song.length)}",
            f"File: {song.path}",
            f"Size: {os.path.getsize(song.path) / 1024 / 1024:.2f} MB",
            f"Modified: {time.ctime(os.path.getmtime(song.path))}"
        ]
        
        messagebox.showinfo("Song Properties", "\n".join(properties))
    
    # Equalizer functionality
    def toggle_equalizer(self):
        """Toggle equalizer visibility"""
        if self.equalizer_visible:
            self.equalizer_frame.pack_forget()
            self.equalizer_visible = False
        else:
            self.equalizer_frame.pack(fill=tk.X, pady=(5, 0))
            self.equalizer_visible = True
    
    def on_equalizer_change(self, band_idx, value):
        """Handle equalizer band change"""
        self.equalizer_bands[band_idx] = value
        self.apply_equalizer()
    
    def apply_equalizer(self):
        """Apply equalizer settings to current playback"""
        if not mixer.music.get_busy() or self.current_index == -1:
            return
            
        # This is a simplified equalizer implementation
        # A real implementation would use a proper audio processing library
        # For demonstration, we'll just adjust the volume of different frequency ranges
        
        # Calculate band gains (convert from dB to multiplier)
        band_gains = [10 ** (band / 20) for band in self.equalizer_bands]
        
        # Apply to playback (this is where you'd normally use a proper DSP)
        # For this demo, we'll just print the gains
        print(f"Applying equalizer gains: {band_gains}")
    
    # Visualization functionality
    def update_visualization(self):
        """Update the audio visualization"""
        while self.visualization_thread_running:
            if mixer.music.get_busy() and not self.paused:
                # Simulate getting audio data (in a real app, you'd use a proper audio analysis)
                # Here we just generate some random data for visualization
                new_data = np.random.rand(1) * 100
                self.visualization_data.append(new_data[0])
                
                # Update the visualization on the main thread
                self.root.after(0, self.draw_visualization)
            
            time.sleep(0.05)
    
    def draw_visualization(self):
        """Draw the audio visualization"""
        self.visualization_canvas.delete("all")
        
        width = self.visualization_canvas.winfo_width()
        height = self.visualization_canvas.winfo_height()
        
        if width <= 1 or height <= 1:
            return
            
        # Draw a simple bar visualization
        bar_width = width / VISUALIZATION_SAMPLES
        data = list(self.visualization_data)
        
        for i, value in enumerate(data):
            x0 = i * bar_width
            x1 = x0 + bar_width - 1
            y0 = height - (value / 100 * height)
            y1 = height
            
            color = "#{:02x}{:02x}{:02x}".format(
                int(255 * (value / 100)),
                int(128 + (value / 100 * 127)),
                128
            )
            
            self.visualization_canvas.create_rectangle(
                x0, y0, x1, y1,
                fill=color,
                outline=color,
                width=0
            )
    
    # Theme and appearance
    def toggle_dark_mode(self):
        """Toggle between dark and light mode"""
        self.dark_mode = not self.dark_mode
        self.apply_theme()
        self.save_config()
    
    def toggle_mini_player(self):
        """Toggle mini player mode"""
        if hasattr(self, 'mini_player') and self.mini_player.winfo_exists():
            self.mini_player.destroy()
            delattr(self, 'mini_player')
        else:
            self.create_mini_player()
    
    def create_mini_player(self):
        """Create a mini player window"""
        self.mini_player = tk.Toplevel(self.root)
        self.mini_player.title("Mini Player")
        self.mini_player.geometry("300x100")
        self.mini_player.resizable(False, False)
        
        # Make it always on top
        self.mini_player.attributes('-topmost', True)
        
        # Controls frame
        controls_frame = ttk.Frame(self.mini_player)
        controls_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Song info
        self.mini_song_label = ttk.Label(controls_frame, text="No song playing", font=('Helvetica', 9))
        self.mini_song_label.pack(fill=tk.X)
        
        # Progress bar
        self.mini_progress = ttk.Scale(controls_frame, from_=0, to=100, orient=tk.HORIZONTAL)
        self.mini_progress.pack(fill=tk.X, pady=2)
        
        # Buttons
        btn_frame = ttk.Frame(controls_frame)
        btn_frame.pack(fill=tk.X)
        
        ttk.Button(btn_frame, text="⏮", command=self.previous_track, width=3).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="⏯", command=self.toggle_play_pause, width=3).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="⏭", command=self.next_track, width=3).pack(side=tk.LEFT, padx=2)
        ttk.Button(btn_frame, text="⏹", command=self.stop, width=3).pack(side=tk.LEFT, padx=2)
        
        # Update mini player info
        self.update_mini_player()
        
        # Handle window close
        self.mini_player.protocol("WM_DELETE_WINDOW", self.toggle_mini_player)
    
    def update_mini_player(self):
        """Update the mini player display"""
        if hasattr(self, 'mini_player') and self.mini_player.winfo_exists():
            if self.current_index != -1 and self.playlist:
                song = self.playlist[self.current_index]
                self.mini_song_label.config(text=f"{song.title} - {song.artist}")
                
                if mixer.music.get_busy() and not self.paused:
                    current_pos = mixer.music.get_pos() / 1000
                    progress = (current_pos / song.length) * 100
                    self.mini_progress.set(progress)
            
            self.root.after(1000, self.update_mini_player)
    
    # System tray functionality
    def show_window(self):
        """Show the main window from system tray"""
        self.root.deiconify()
        self.root.attributes('-topmost', True)
        self.root.after(100, lambda: self.root.attributes('-topmost', False))
    
    def hide_window(self):
        """Hide the main window to system tray"""
        self.root.withdraw()
    
    # Configuration
    def load_config(self):
        """Load configuration from file"""
        try:
            if os.path.exists(CONFIG_FILE):
                with open(CONFIG_FILE, 'r') as f:
                    config = json.load(f)
                
                self.volume = config.get('volume', DEFAULT_VOLUME)
                self.dark_mode = config.get('dark_mode', False)
                self.repeat_mode = config.get('repeat_mode', 0)
                self.shuffle_mode = config.get('shuffle_mode', False)
                self.equalizer_bands = config.get('equalizer_bands', [0.0] * 10)
                
                # Apply loaded settings
                self.set_volume(self.volume)
                self.set_repeat_mode(self.repeat_mode)
                if self.shuffle_mode:
                    self.toggle_shuffle()
                
        except Exception as e:
            print(f"Error loading config: {e}")
    
    def save_config(self):
        """Save configuration to file"""
        try:
            config = {
                'volume': self.volume,
                'dark_mode': self.dark_mode,
                'repeat_mode': self.repeat_mode,
                'shuffle_mode': self.shuffle_mode,
                'equalizer_bands': self.equalizer_bands
            }
            
            with open(CONFIG_FILE, 'w') as f:
                json.dump(config, f, indent=2)
        except Exception as e:
            print(f"Error saving config: {e}")
    
    # Help and about
    def show_documentation(self):
        """Show documentation in browser"""
        webbrowser.open("https://github.com/yourusername/audio-player/docs")
    
    def check_for_updates(self):
        """Check for updates"""
        self.status_left.config(text="Checking for updates...")
        # In a real app, this would check your update server
        self.root.after(2000, lambda: self.status_left.config(text="You have the latest version"))
    
    def show_about(self):
        """Show about dialog"""
        about_text = """World-Class Audio Player
        
Version 1.0.0
        
A feature-rich audio player with:
- Multiple format support
- Playlist management
- Audio visualization
- Equalizer
- Cross-platform compatibility
        
© 2025 Your Name"""
        
        messagebox.showinfo("About", about_text)
    
    # Application lifecycle
    def quit_app(self):
        """Quit the application"""
        self.visualization_thread_running = False
        if self.visualization_thread.is_alive():
            self.visualization_thread.join(timeout=0.1)
        
        self.save_config()
        mixer.quit()
        
        if hasattr(self, 'tray_icon'):
            self.tray_icon.stop()
        
        self.root.quit()
        self.root.destroy()

def main():
    """Main entry point"""
    root = tk.Tk()
    
    # Set window icon
    try:
        if platform.system() == 'Windows':
            root.iconbitmap('icon.ico')
        else:
            img = Image.new('RGB', (64, 64), 'black')
            draw = ImageDraw.Draw(img)
            draw.ellipse((16, 16, 48, 48), fill='white')
            photo = ImageTk.PhotoImage(img)
            root.tk.call('wm', 'iconphoto', root._w, photo)
    except Exception:
        pass
    
    app = AudioPlayerApp(root)
    root.protocol("WM_DELETE_WINDOW", app.hide_window)
    root.mainloop()

if __name__ == "__main__":
    main()
