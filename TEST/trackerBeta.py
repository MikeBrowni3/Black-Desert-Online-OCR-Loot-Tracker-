import json
import os
import threading
import queue
import customtkinter as ctk
from mss import MSS
from PIL import Image, ImageOps, ImageFilter
import re
import time
from difflib import get_close_matches
import ctypes
import csv
import numpy as np
from rapidocr_onnxruntime import RapidOCR
import tkinter.font as tkfont
import requests
from io import BytesIO
import webbrowser
import sys

# ================== PORTABLE PATH LOGIC ==================
# This ensures the app finds its data folder whether running as a script or a frozen EXE
if getattr(sys, 'frozen', False):
    # If running as an EXE (PyInstaller)
    APPLICATION_PATH = os.path.dirname(sys.executable)
else:
    # If running as a standard Python script
    APPLICATION_PATH = os.path.dirname(os.path.abspath(__file__))

DATA_FOLDER = os.path.join(APPLICATION_PATH, "BDO_Data")
CONFIG_FILE = os.path.join(DATA_FOLDER, "scanner_config.json")
ITEM_DB_FILE = os.path.join(DATA_FOLDER, "local_items.json")
LOCATIONS_FILE = os.path.join(DATA_FOLDER, "locations.json")
EXPORT_FILE = os.path.join(DATA_FOLDER, "bdo-loot-data.json")
RAPID_EXPORT_FILE = os.path.join(DATA_FOLDER, "bdo-loot-data-RapidOCR.json")
HISTORY_FILE = os.path.join(DATA_FOLDER, "grind-history.csv")
HISTORY_JS_FILE = os.path.join(DATA_FOLDER, "grind-history.js")

if not os.path.exists(DATA_FOLDER):
    os.makedirs(DATA_FOLDER)

# WinAPI Constants
GWL_EXSTYLE = -20
WS_EX_LAYERED = 0x80000
WS_EX_TRANSPARENT = 0x20
WS_EX_TOPMOST = 0x8
WS_EX_TOOLWINDOW = 0x80
WS_EX_NOACTIVATE = 0x08000000

# Virtual Key Mapping for common bindable keys
VK_MAP = {
    "F1": 0x70, "F2": 0x71, "F3": 0x72, "F4": 0x73, "F5": 0x74, "F6": 0x75,
    "F7": 0x76, "F8": 0x77, "F9": 0x78, "F10": 0x79, "F11": 0x7A, "F12": 0x7B,
    "HOME": 0x24, "END": 0x23, "INSERT": 0x2D, "DELETE": 0x2E, "PAGE_UP": 0x21, "PAGE_DOWN": 0x22,
    "NUM_0": 0x60, "NUM_1": 0x61, "NUM_2": 0x62, "NUM_3": 0x63, "NUM_4": 0x64, "NUM_5": 0x65
}

class LootTrackerApp(ctk.CTk):

    def __init__(self):
        super().__init__()

        self.title("BDO Loot Tracker")
        self.geometry("340x650")
        self.configure(fg_color="#000000")

        self.update_queue = queue.Queue()
        self.current_zone = "SEARCHING..."
        
        config = self.load_config()
        self.scan_region = config
        self.current_font_family = config.get("font", "Georama")
        self.current_class = config.get("class", "Select Class")
        self.transparency_val = config.get("transparency", 0.9)
        self.current_hotkey_str = config.get("hotkey", "F10")
        self.current_hotkey_code = VK_MAP.get(self.current_hotkey_str, 0x79)

        self.session_running = False
        self.is_click_through = False

        self.start_time = 0
        self.loot_table = {}
        self.rapid_loot_table = {}
        self.total_silver_value = 0
        self.rapid_item_timestamps = {}
        
        self.loot_rows = {} 
        self.icon_cache = {}

        self.item_db = self.load_json(ITEM_DB_FILE)
        self.locations_db = self.load_json(LOCATIONS_FILE)

        self.active_pool = []
        self.available_fonts = sorted([f for f in tkfont.families() if not f.startswith("@")])

        self.setup_widgets()
        self.set_font(self.current_font_family)
        self.class_dropdown.set(self.current_class)
        self.hotkey_dropdown.set(self.current_hotkey_str)
        
        self.attributes("-alpha", self.transparency_val)
        self.after(500, self.init_window_styles)

        threading.Thread(target=self.hotkey_check_loop, daemon=True).start()
        self.check_queue()

    def log_error(self, context, error):
        print(f"[ERROR] {context}: {error}")

    def init_window_styles(self):
        try:
            self.hwnd = ctypes.windll.user32.FindWindowW(None, "BDO Loot Tracker")
            if self.hwnd:
                style = (WS_EX_LAYERED | WS_EX_TOPMOST | WS_EX_TOOLWINDOW)
                ctypes.windll.user32.SetWindowLongW(self.hwnd, GWL_EXSTYLE, style)
                self.attributes("-topmost", True)
        except Exception as e:
            self.log_error("init_window_styles", e)

    def load_json(self, path):
        try:
            if os.path.exists(path):
                with open(path, 'r', encoding='utf-8') as f:
                    return json.load(f)
        except Exception as e:
            self.log_error(f"load_json ({path})", e)
        return {}

    def load_config(self):
        config = self.load_json(CONFIG_FILE)
        defaults = {
            "top": 800, "left": 2000, "width": 500, "height": 250, 
            "font": "Georama", "class": "Select Class", "transparency": 0.9,
            "hotkey": "F10"
        }
        if not config: return defaults
        for key, val in defaults.items():
            if key not in config: config[key] = val
        return config

    def save_config(self):
        config_data = {
            "top": self.scan_region.get("top", 800),
            "left": self.scan_region.get("left", 2000),
            "width": self.scan_region.get("width", 500),
            "height": self.scan_region.get("height", 250),
            "font": self.current_font_family,
            "class": self.current_class,
            "transparency": self.transparency_val,
            "hotkey": self.current_hotkey_str
        }
        try:
            with open(CONFIG_FILE, "w", encoding='utf-8') as f:
                json.dump(config_data, f, indent=4)
        except Exception as e: self.log_error("save_config", e)

    def set_font(self, selected_font):
        self.current_font_family = selected_font
        self.save_config()
        self.zone_label.configure(font=(self.current_font_family, 14, "bold"))
        self.timer_label.configure(font=(self.current_font_family, 28, "bold"))
        self.silver_label.configure(font=(self.current_font_family, 22, "bold"))
        self.silver_hr_label.configure(font=(self.current_font_family, 16, "bold"))
        self.trash_hr_label.configure(font=(self.current_font_family, 16, "bold"))

    def set_transparency(self, value):
        self.transparency_val = float(value)
        self.attributes("-alpha", self.transparency_val)
        self.transparency_label.configure(text=f"Transparency: {int(self.transparency_val * 100)}%")
        self.save_config()

    def set_hotkey(self, selected_key):
        self.current_hotkey_str = selected_key
        self.current_hotkey_code = VK_MAP.get(selected_key, 0x79)
        status_text = "ON" if self.is_click_through else "OFF"
        color = "#e74c3c" if self.is_click_through else "#34495e"
        self.click_btn.configure(text=f"{self.current_hotkey_str}: CLICK-THRU {status_text}", fg_color=color)
        self.save_config()

    def setup_widgets(self):
        self.tabview = ctk.CTkTabview(self, segmented_button_fg_color="#1a1a1a", segmented_button_selected_color="#3498db")
        self.tabview.pack(padx=10, pady=10, fill="both", expand=True)
        self.tabview.add("Tracker")
        self.tabview.add("Settings")

        # --- TRACKER TAB ---
        tracker_tab = self.tabview.tab("Tracker")
        tracker_tab.configure(fg_color="#000000")

        self.header_frame = ctk.CTkFrame(tracker_tab, fg_color="transparent")
        self.header_frame.pack(fill="x", pady=(5, 0))

        self.zone_label = ctk.CTkLabel(self.header_frame, text=self.current_zone.upper(), text_color="#3498db")
        self.zone_label.pack(side="left", padx=5)

        self.row_frame = ctk.CTkFrame(tracker_tab, fg_color="transparent")
        self.row_frame.pack(fill="x", pady=10)

        self.timer_label = ctk.CTkLabel(self.row_frame, text="00:00:00", text_color="#ffffff")
        self.timer_label.pack(side="left", padx=5)

        self.silver_container = ctk.CTkFrame(self.row_frame, fg_color="transparent")
        self.silver_container.pack(side="right", padx=5)

        ctk.CTkLabel(self.silver_container, text="TOTAL SILVER", font=("Georama", 10), text_color="#00ff88").pack(anchor="e")
        self.silver_label = ctk.CTkLabel(self.silver_container, text="0", text_color="#ffffff")
        self.silver_label.pack(anchor="e")

        self.stats_grid = ctk.CTkFrame(tracker_tab, fg_color="transparent")
        self.stats_grid.pack(fill="x", pady=5)
        self.stats_grid.columnconfigure((0, 1), weight=1)

        self.s_hr_box = ctk.CTkFrame(self.stats_grid, fg_color="#1a1a1a", corner_radius=2)
        self.s_hr_box.grid(row=0, column=0, padx=5, sticky="nsew")
        ctk.CTkLabel(self.s_hr_box, text="SILVER / HR", font=("Georama", 10), text_color="#00ff88").pack(pady=(5,0))
        self.silver_hr_label = ctk.CTkLabel(self.s_hr_box, text="0")
        self.silver_hr_label.pack(pady=(0,5))

        self.t_hr_box = ctk.CTkFrame(self.stats_grid, fg_color="#1a1a1a", corner_radius=2)
        self.t_hr_box.grid(row=0, column=1, padx=5, sticky="nsew")
        ctk.CTkLabel(self.t_hr_box, text="TRASH / HR", font=("Georama", 10), text_color="#00ff88").pack(pady=(5,0))
        self.trash_hr_label = ctk.CTkLabel(self.t_hr_box, text="0")
        self.trash_hr_label.pack(pady=(0,5))

        self.btn_frame = ctk.CTkFrame(tracker_tab, fg_color="transparent")
        self.btn_frame.pack(fill="x", pady=10)
        self.start_btn = ctk.CTkButton(self.btn_frame, text="START", fg_color="#27ae60", height=32, command=self.start_session)
        self.start_btn.pack(side="left", padx=5, expand=True)
        self.stop_btn = ctk.CTkButton(self.btn_frame, text="STOP", fg_color="#c0392b", height=32, command=self.stop_session)
        self.stop_btn.pack(side="left", padx=5, expand=True)

        self.click_btn = ctk.CTkButton(tracker_tab, text=f"{self.current_hotkey_str}: CLICK-THRU OFF", fg_color="#34495e", height=32, command=self.toggle_click_through)
        self.click_btn.pack(fill="x", padx=5, pady=5)

        self.loot_scroll_frame = ctk.CTkFrame(tracker_tab, fg_color="transparent", corner_radius=0)
        self.loot_scroll_frame.pack(pady=5, fill="both", expand=True)

        # --- SETTINGS TAB ---
        settings_tab = self.tabview.tab("Settings")
        
        ctk.CTkLabel(settings_tab, text="Character Class:").pack(pady=(10,0))
        self.class_dropdown = ctk.CTkComboBox(settings_tab, values=["Warrior", "Ranger", "Sorceress", "Berserker", "Tamer", "Musa", "Maehwa", "Valkyrie", "Kunoichi", "Ninja", "Wizard", "Witch", "Dark Knight", "Striker", "Mystic", "Lahn", "Archer", "Shai", "Guardian", "Hashashin", "Nova", "Sage", "Corsair", "Drakania", "Woosa", "Maegu", "Scholar", "Dosa", "Deadeye"], command=self.set_class, width=200)
        self.class_dropdown.pack(pady=5)

        ctk.CTkLabel(settings_tab, text="Click-thru Hotkey:").pack(pady=(10,0))
        self.hotkey_dropdown = ctk.CTkComboBox(settings_tab, values=list(VK_MAP.keys()), command=self.set_hotkey, width=200)
        self.hotkey_dropdown.pack(pady=5)

        ctk.CTkLabel(settings_tab, text="UI Font:").pack(pady=(10,0))
        self.font_dropdown = ctk.CTkComboBox(settings_tab, values=self.available_fonts, command=self.set_font, width=200)
        self.font_dropdown.set(self.current_font_family)
        self.font_dropdown.pack(pady=5)

        self.transparency_label = ctk.CTkLabel(settings_tab, text=f"Transparency: {int(self.transparency_val * 100)}%")
        self.transparency_label.pack(pady=(10, 0))
        self.trans_slider = ctk.CTkSlider(settings_tab, from_=0.1, to=1.0, command=self.set_transparency)
        self.trans_slider.set(self.transparency_val)
        self.trans_slider.pack(pady=5)

        ctk.CTkButton(settings_tab, text="RE-CONFIGURE SCAN AREA", fg_color="#8e44ad", command=self.toggle_selector).pack(pady=20)
        self.rapid_preview = ctk.CTkLabel(settings_tab, text="", fg_color="black", width=200, height=80)
        self.rapid_preview.pack()

        # --- CLICKABLE TWITCH LINK ---
        link_label = ctk.CTkLabel(
            settings_tab, 
            text="made by : https://www.twitch.tv/brownie_", 
            text_color="#3498db", 
            cursor="hand2"
        )
        link_label.pack(side="bottom", pady=20)
        link_label.bind("<Button-1>", lambda e: webbrowser.open("https://www.twitch.tv/brownie_"))

    def check_queue(self):
        while not self.update_queue.empty():
            task, data = self.update_queue.get()
            if task == "toggle_click": self.toggle_click_through()
            elif task == "preview": self.rapid_preview.configure(image=data[1])
            elif task == "ui_refresh":
                # Update header/stat labels
                self.silver_label.configure(text=f"{self.total_silver_value:,}")
                elapsed = max(1, time.time() - self.start_time)
                s_hr = int((self.total_silver_value / elapsed) * 3600)
                total_trash = sum(qty for item, qty in self.loot_table.items() if self.item_db.get(item, {}).get("category") == "Trash")
                t_hr = int((total_trash / elapsed) * 3600)
                self.silver_hr_label.configure(text=f"{s_hr:,}")
                self.trash_hr_label.configure(text=f"{t_hr:,}")
                self.zone_label.configure(text=f"{self.current_zone.upper()} • {self.current_class.upper()}")
                
                # Update or create loot rows
                sorted_items = sorted(self.loot_table.items(), key=lambda x: x[1], reverse=True)
                for item_name, qty in sorted_items:
                    if item_name in self.loot_rows:
                        # Update existing row
                        row_frame = self.loot_rows[item_name]
                        row_frame.qty_label.configure(text=f"x{qty:,}")
                        # Move to current position in sort order
                        row_frame.pack_forget()
                        row_frame.pack(fill="x", pady=2)
                    else:
                        # Create new row
                        row = ctk.CTkFrame(self.loot_scroll_frame, fg_color="transparent")
                        row.pack(fill="x", pady=2)
                        
                        icon_url = self.item_db.get(item_name, {}).get("icon", "")
                        if icon_url:
                            if icon_url not in self.icon_cache:
                                try:
                                    response = requests.get(icon_url, timeout=2)
                                    if response.status_code == 200:
                                        img_data = Image.open(BytesIO(response.content))
                                        self.icon_cache[icon_url] = ctk.CTkImage(light_image=img_data, dark_image=img_data, size=(24, 24))
                                except: pass
                            if icon_url in self.icon_cache:
                                ctk.CTkLabel(row, image=self.icon_cache[icon_url], text="").pack(side="left", padx=(5, 5))

                        ctk.CTkLabel(row, text=item_name.title(), font=(self.current_font_family, 13), text_color="#bdc3c7", anchor="w").pack(side="left", expand=True, fill="x")
                        
                        # Store reference to qty label for future updates
                        row.qty_label = ctk.CTkLabel(row, text=f"x{qty:,}", font=(self.current_font_family, 13, "bold"), text_color="#00ff88")
                        row.qty_label.pack(side="right", padx=5)
                        
                        self.loot_rows[item_name] = row

        self.after(100, self.check_queue)

    def hotkey_check_loop(self):
        state_hotkey = 0
        while True:
            new_state = ctypes.windll.user32.GetAsyncKeyState(self.current_hotkey_code)
            if new_state & 0x8000 and not state_hotkey:
                self.update_queue.put(("toggle_click", None))
            state_hotkey = new_state & 0x8000
            time.sleep(0.05)

    def update_loop(self):
        try: rapid_engine = RapidOCR()
        except: rapid_engine = None
        with MSS() as sct:
            while self.session_running:
                try:
                    sct_img = sct.grab(self.scan_region)
                    raw_img = Image.frombytes("RGB", sct_img.size, sct_img.bgra, "raw", "BGRX")
                    w, h = raw_img.size
                    bottom_crop = raw_img.crop((0, int(h * 0.70), w, h))
                    rapid_base = bottom_crop.resize((w * 2, int(h * 0.6)), Image.Resampling.LANCZOS).convert("RGB")
                    p2 = rapid_base.copy()
                    p2.thumbnail((200, 80))
                    img2 = ctk.CTkImage(light_image=p2, size=p2.size)
                    self.update_queue.put(("preview", (None, img2)))
                    rapid_text = ""
                    if rapid_engine:
                        res, _ = rapid_engine(np.array(rapid_base))
                        if res: rapid_text = "\n".join([str(l[1]).strip().lower() for l in res if float(l[2]) >= 0.45])
                    now = time.time()
                    updated = False
                    for line in [l.strip() for l in rapid_text.split('\n') if len(l.strip()) > 3]:
                        clean = re.sub(r'[^a-z\s-]', '', re.sub(r'[x\s]?\d+', '', line)).strip()
                        if len(clean) < 3: continue
                        match = get_close_matches(clean, self.active_pool if self.active_pool else list(self.item_db.keys()), n=1, cutoff=0.55)
                        if match:
                            item = match[0]
                            if (now - self.rapid_item_timestamps.get(item, 0)) > 0.85:
                                self.detect_zone(item)
                                qty = 1
                                nums = re.findall(r'(\d+)', line)
                                if nums: qty = int(nums[-1].replace(',', ''))
                                self.rapid_loot_table[item] = (self.rapid_loot_table.get(item, 0) + qty)
                                self.rapid_item_timestamps[item] = now
                                updated = True
                    if updated:
                        self.update_queue.put(("ui_refresh", None))
                        self.save_loot_data()
                except Exception as e: self.log_error("update_loop", e)
                time.sleep(0.4)

    def toggle_click_through(self):
        try:
            self.is_click_through = not self.is_click_through
            style = (WS_EX_LAYERED | WS_EX_TOPMOST | WS_EX_TOOLWINDOW)
            if self.is_click_through:
                new_style = (style | WS_EX_TRANSPARENT | WS_EX_NOACTIVATE)
                self.click_btn.configure(text=f"{self.current_hotkey_str}: CLICK-THRU ON", fg_color="#e74c3c")
                self.attributes("-alpha", self.transparency_val)
            else:
                new_style = style
                self.click_btn.configure(text=f"{self.current_hotkey_str}: CLICK-THRU OFF", fg_color="#34495e")
                self.attributes("-alpha", 1.0)
            ctypes.windll.user32.SetWindowLongW(self.hwnd, GWL_EXSTYLE, new_style)
        except Exception as e: self.log_error("toggle_click_through", e)

    def start_session(self):
        self.session_running = True
        self.start_time = time.time()
        self.rapid_loot_table = {}
        # Clear existing rows from previous session
        for row in self.loot_rows.values():
            row.destroy()
        self.loot_rows = {}
        threading.Thread(target=self.update_loop, daemon=True).start()
        self.tick_timer()

    def tick_timer(self):
        if self.session_running:
            elapsed = int(time.time() - self.start_time)
            self.timer_label.configure(text=time.strftime("%H:%M:%S", time.gmtime(elapsed)))
            self.save_loot_data()
            self.update_queue.put(("ui_refresh", None))
            self.after(1000, self.tick_timer)

    def stop_session(self):
        self.session_running = False
        self.save_loot_data()
        self.log_to_history()

    def save_loot_data(self):
        try:
            self.loot_table = self.rapid_loot_table.copy()
            self.total_silver_value = sum(qty * self.item_db.get(item, {}).get("price", 0) for item, qty in self.loot_table.items())
            elapsed = max(1, time.time() - self.start_time)
            s_hr = int((self.total_silver_value / elapsed) * 3600)
            total_trash = sum(qty for item, qty in self.loot_table.items() if self.item_db.get(item, {}).get("category") == "Trash")
            t_hr = int((total_trash / elapsed) * 3600)
            items_with_icons = {item: {"count": qty, "icon": self.item_db.get(item, {}).get("icon", "")} for item, qty in self.loot_table.items()}
            base = {"class": self.current_class, "location": self.current_zone, "start_timestamp": self.start_time, "session_duration": self.timer_label.cget("text"), "total_silver": self.total_silver_value, "silver_per_hr": s_hr, "trash_per_hr": t_hr, "session_active": self.session_running, "timestamp": int(time.time()), "items": items_with_icons}
            with open(EXPORT_FILE, "w", encoding='utf-8') as f: json.dump(base, f, indent=4)
        except Exception as e: self.log_error("save_loot_data", e)

    def log_to_history(self):
        """Modified to output structured CSV with headers and readable loot summaries."""
        try:
            # Sync data state
            self.loot_table = self.rapid_loot_table.copy()
            total_silver = sum(qty * self.item_db.get(item, {}).get("price", 0) for item, qty in self.loot_table.items())
            elapsed = max(1, time.time() - self.start_time)
            s_hr = int((total_silver / elapsed) * 3600)
            total_trash = sum(qty for item, qty in self.loot_table.items() if self.item_db.get(item, {}).get("category") == "Trash")
            t_hr = int((total_trash / elapsed) * 3600)
            
            # Map details including ICON URL for the web history dashboard
            details = {
                item: {
                    "qty": qty, 
                    "price": self.item_db.get(item, {}).get("price", 0),
                    "icon": self.item_db.get(item, {}).get("icon", "")
                } for item, qty in self.loot_table.items()
            }

            # Create a human-readable summary for easy reading in Excel/CSV
            loot_summary = ", ".join([f"{item} (x{qty})" for item, qty in self.loot_table.items()])
            
            # Check if file exists/is empty to determine if headers are needed
            file_exists = os.path.exists(HISTORY_FILE) and os.path.getsize(HISTORY_FILE) > 0
            
            # Save to CSV as a structured table
            with open(HISTORY_FILE, 'a', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                # Write header if starting a new file
                if not file_exists:
                    writer.writerow([
                        "Timestamp", "Class", "Location", "Duration", 
                        "Total Silver", "Silver/Hr", "Trash/Hr", "Loot Summary", "Raw Data"
                    ])
                
                writer.writerow([
                    time.strftime("%Y-%m-%d %H:%M:%S"), 
                    self.current_class, 
                    self.current_zone, 
                    self.timer_label.cget("text"), 
                    total_silver, 
                    s_hr, 
                    t_hr, 
                    loot_summary,
                    json.dumps(details)
                ])
            
            # Sync to JS history file (Updated to handle skipping headers in the CSV source)
            history_list = []
            if os.path.exists(HISTORY_FILE):
                with open(HISTORY_FILE, 'r', encoding='utf-8') as f:
                    reader = csv.reader(f)
                    for row in reader:
                        # Skip empty rows or header row
                        if not row or row[0] == "Timestamp": continue
                        try:
                            # Use row indices relative to the new table structure
                            history_list.append({
                                "timestamp": row[0],
                                "class": row[1],
                                "location": row[2],
                                "duration": row[3],
                                "total_silver": int(row[4]),
                                "silver_hr": int(row[5]),
                                "trash_hr": int(row[6]),
                                "details": json.loads(row[-1])
                            })
                        except (ValueError, json.JSONDecodeError, IndexError):
                            continue
            
            with open(HISTORY_JS_FILE, "w", encoding='utf-8') as f:
                f.write(f"const grindHistory = {json.dumps(history_list, indent=4)};")
                
        except Exception as e: self.log_error("log_to_history", e)

    def set_class(self, selected_class):
        self.current_class = selected_class
        self.save_config()
        self.update_queue.put(("ui_refresh", None))

    def toggle_selector(self):
        self.selector = ctk.CTkToplevel(self)
        self.selector.attributes("-alpha", 0.3, "-topmost", True)
        self.selector.geometry(f"{self.scan_region['width']}x{self.scan_region['height']}+{self.scan_region['left']}+{self.scan_region['top']}")
        ctk.CTkButton(self.selector, text="LOCK AREA", command=self.lock_region).pack(expand=True)

    def lock_region(self):
        self.scan_region = {"top": self.selector.winfo_y(), "left": self.selector.winfo_x(), "width": self.selector.winfo_width(), "height": self.selector.winfo_height()}
        self.save_config()
        self.selector.destroy()

    def detect_zone(self, item_name):
        for zone, info in self.locations_db.items():
            if item_name in [s.lower() for s in info.get("signatures", [])]:
                if self.current_zone != zone:
                    self.current_zone = zone
                    self.active_pool = [n for n, d in self.item_db.items() if d.get("location") == zone or d.get("location") == "Global"]
                    return True
        return False

if __name__ == "__main__":
    app = LootTrackerApp()
    app.mainloop()