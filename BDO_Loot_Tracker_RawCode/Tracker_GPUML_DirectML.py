import json
import os
import threading
import queue
import customtkinter as ctk
from PIL import Image, ImageOps, ImageFilter
import re
import time
from difflib import get_close_matches
import ctypes
import csv
import numpy as np
import cv2
import dxcam
import onnxruntime as ort
from concurrent.futures import ThreadPoolExecutor
from rapidocr_onnxruntime import RapidOCR
import tkinter.font as tkfont
import requests
from io import BytesIO
import webbrowser
import sys
import urllib.request
import datetime
from datetime import timezone
import pygame
import textdistance

# ML Dependencies (optional - will use mock if not available)
try:
    import torch
    import torchvision
    import torchvision.transforms as transforms
    ML_AVAILABLE = True
except ImportError:
    ML_AVAILABLE = False
    print("[WARNING] ML dependencies not found. Using mock classifier. Install torch/torchvision for full ML support.")

# ================== PORTABLE PATH LOGIC ==================
if getattr(sys, 'frozen', False):
    APPLICATION_PATH = os.path.dirname(sys.executable)
else:
    APPLICATION_PATH = os.path.dirname(os.path.abspath(__file__))

DATA_FOLDER = os.path.join(APPLICATION_PATH, "BDO_Data")
CONFIG_FILE = os.path.join(DATA_FOLDER, "scanner_config.json")
ITEM_DB_FILE = os.path.join(DATA_FOLDER, "local_items.json")
LOCATIONS_FILE = os.path.join(DATA_FOLDER, "locations.json")
CLASSES_FILE = os.path.join(DATA_FOLDER, "Classes.json")
EXPORT_FILE = os.path.join(DATA_FOLDER, "bdo-loot-data.json")
GARMOTH_EXPORT_FILE = os.path.join(DATA_FOLDER, "garmoth-loot-data.json")
RAPID_EXPORT_FILE = os.path.join(DATA_FOLDER, "bdo-loot-data-RapidOCR.json")
HISTORY_FILE = os.path.join(DATA_FOLDER, "grind-history.csv")
HISTORY_JS_FILE = os.path.join(DATA_FOLDER, "grind-history.js")
SOUNDS_FOLDER = os.path.join(DATA_FOLDER, "sounds", "boss_timer")
BOSS_TIMES_FILE = os.path.join(DATA_FOLDER, "boss_times.json")
VIDEOS_FILE = os.path.join(DATA_FOLDER, "videos.json")
DROPS_ICONS_FOLDER = os.path.join(DATA_FOLDER, "drop_icons")
TOLERANCE_CONFIG_FILE = os.path.join(DATA_FOLDER, "tolerance_config.json")

SHEET_CSV_URL = "https://docs.google.com/spreadsheets/d/e/2PACX-1vTSfa7xSRb-YGF9SNlsWNqhuKs4C-XaYWz4yt2fZKOeWzw1xGESL7ifUmV8OjL-7hiFl9MckOWAXM_c/pub?gid=0&single=true&output=csv"

if not os.path.exists(DATA_FOLDER):
    os.makedirs(DATA_FOLDER)

if not os.path.exists(SOUNDS_FOLDER):
    os.makedirs(SOUNDS_FOLDER)

# Create local item icon cache folder
if not os.path.exists(DROPS_ICONS_FOLDER):
    os.makedirs(DROPS_ICONS_FOLDER)

# Initialize pygame mixer for sound playback
try:
    pygame.mixer.init()
except Exception as e:
    print(f"[WARNING] Failed to initialize pygame mixer: {e}")

# WinAPI Constants
GWL_EXSTYLE = -20
WS_EX_LAYERED = 0x80000
WS_EX_TRANSPARENT = 0x20
WS_EX_TOPMOST = 0x8
WS_EX_TOOLWINDOW = 0x80
WS_EX_NOACTIVATE = 0x08000000

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
        self.geometry("380x750")
        self.configure(fg_color="#000000")

        self.update_queue = queue.Queue()
        self.current_zone = "SEARCHING..."
        
        config = self.load_config()
        self.scan_region = config
        self.current_font_family = config.get("font", "Georama")
        self.current_class = config.get("class", "Select Class")
        self.current_class_id = config.get("class_id", 0)
        self.current_spec = config.get("spec", 0)
        self.transparency_val = config.get("transparency", 0.9)
        self.current_hotkey_str = config.get("hotkey", "F10")
        self.current_hotkey_code = VK_MAP.get(self.current_hotkey_str, 0x79)
        self.garmoth_api_key = config.get("garmoth_api_key", "")
        self.boss_region = config.get("boss_region", "EU")
        self.sound_volume = config.get("sound_volume", 0.5)
        self.sound_notifications = config.get("sound_notifications", {
            "30min": False, "15min": False, "10min": False, "5min": False, "3min": False, "1min": False, "spawn": False
        })

        self.session_running = False
        self.is_click_through = False

        self.start_time = 0
        self.loot_table = {}
        self.rapid_loot_table = {}
        self.total_silver_value = 0
        self.active_tracks = [] 
        
        self.loot_rows = {} 
        self.icon_cache = {}

        # Load Database and ensure lowercase keys for matching
        self.item_db = self.load_json(ITEM_DB_FILE)
        self.locations_db = self.load_json(LOCATIONS_FILE)
        self.classes_db = self.load_json(CLASSES_FILE)

        # Auto-correct class_id and spec based on selected class
        for class_key, class_data in self.classes_db.items():
            if class_data["description"] == self.current_class:
                self.current_class_id = class_data["id"]
                self.current_spec = class_data["spec"]
                self.save_config()
                break

        # New internal indexes
        self.items_by_name = {}
        self.items_by_location = {}
        self.build_indexes()

        self.active_pool = []

        # ================= PERFORMANCE =================
        self.last_frame_gray = None
        self.last_loot_boxes = []
        self.last_ocr_time = 0
        self.frame_skip_counter = 0
        self.consecutive_filter_failures = 0

        # OCR worker thread
        self.ocr_executor = ThreadPoolExecutor(max_workers=1)
        self.ocr_future = None

        # Frame differencing threshold
        self.motion_threshold = 0.5

        # Cache loot row regions
        self.cached_row_regions = []

        # Template matching
        self.template_cache = {}
        self.template_threshold = 0.88
        self.icon_size = (32, 32)

        # Temporal confidence tracking
        self.temporal_cache = {}
        self.temporal_required_hits = 1

        # Load item-specific tolerances from config file
        self.load_tolerance_config()

        # Multi-scale template matching
        self.template_scales = [28, 32, 36]

        # Hybrid OCR/ML Configuration
        self.ml_confidence_threshold = 0.70  # Use ML if OCR confidence below this
        self.ml_classifier = None
        self.use_ml_fallback = True

        # OCR cooldown
        self.ocr_cooldown = 0.30

        self.load_item_templates()
        
        # Initialize ML classifier
        if self.use_ml_fallback:
            try:
                self.ml_classifier = self.MLIconClassifier(DROPS_ICONS_FOLDER, self.item_db)
                print("[ML] Classifier initialized successfully")
            except Exception as e:
                print(f"[WARNING] ML classifier init failed: {e}")
                self.ml_classifier = None
        
        self.available_fonts = sorted([f for f in tkfont.families() if not f.startswith("@")])

        self.setup_widgets()
        self.set_font(self.current_font_family)
        self.class_dropdown.set(self.current_class)
        self.hotkey_dropdown.set(self.current_hotkey_str)
        
        self.attributes("-alpha", self.transparency_val)
        self.after(500, self.init_window_styles)

        threading.Thread(target=self.hotkey_check_loop, daemon=True).start()
        self.check_queue()

    def safe_int(self, value, default=0):
        try:
            value = str(value).replace(",", "").strip()
            if value == "":
                return default
            return int(value)
        except:
            return default


    def build_indexes(self):
        self.items_by_name = {}
        self.items_by_location = {}

        for uid, data in self.item_db.items():

            # BACKWARD COMPATIBILITY
            if isinstance(data, dict):
                item_name = str(data.get("name", uid)).strip().lower()
            else:
                item_name = str(uid).strip().lower()
                data = {}

            if not item_name:
                continue

            if item_name not in self.items_by_name:
                self.items_by_name[item_name] = []

            self.items_by_name[item_name].append(uid)

            location_str = str(data.get("location", ""))

            for loc in location_str.split(","):
                loc = loc.strip().lower()

                if not loc:
                    continue

                if loc not in self.items_by_location:
                    self.items_by_location[loc] = []

                if item_name not in self.items_by_location[loc]:
                    self.items_by_location[loc].append(item_name)

    def sync_database(self):
        def run_sync():
            self.update_queue.put(("sync_status", "Syncing..."))
            try:
                response = urllib.request.urlopen(SHEET_CSV_URL)
                lines = [line.decode('utf-8') for line in response.readlines()]
                reader = csv.DictReader(lines)

                new_items = {}
                new_locs = {}

                for row in reader:
                    name = row.get("item name", "").strip().lower()
                    if not name:
                        continue

                    item_id = row.get("id", "").strip()
                    sub_key = self.safe_int(row.get("sub_key", 0))

                    market_price = self.safe_int(row.get("price", 0))
                    vendor_price = self.safe_int(row.get("vendor price", 0))
                    price = market_price if market_price > 0 else vendor_price

                    category = row.get("category", "").strip()
                    location_val = row.get("location", "").strip()
                    icon_url = row.get("item icon", "").strip()
                    garmoth_id = self.safe_int(row.get("garmoth_id", 0))

                    # UNIQUE INTERNAL KEY
                    unique_key = f"{item_id}_{sub_key}_{location_val.lower().replace(' ', '_')}"

                    new_items[unique_key] = {
                        "name": name,
                        "id": item_id,
                        "sub_key": sub_key,
                        "price": price,
                        "category": category,
                        "location": location_val,
                        "icon": icon_url
                    }

                    if category.lower() == "trash":
                        loc_list = [l.strip() for l in location_val.split(",")]

                        for loc in loc_list:
                            if not loc:
                                continue

                            if loc not in new_locs:
                                new_locs[loc] = {
                                    "garmoth_id": garmoth_id,
                                    "signatures": [],
                                    "description": f"Grind Zone: {loc}"
                                }

                            if garmoth_id > 0:
                                new_locs[loc]["garmoth_id"] = garmoth_id

                            if name not in new_locs[loc]["signatures"]:
                                new_locs[loc]["signatures"].append(name)

                with open(ITEM_DB_FILE, 'w', encoding='utf-8') as f: 
                    json.dump(new_items, f, indent=4)
                with open(LOCATIONS_FILE, 'w', encoding='utf-8') as f: 
                    json.dump(new_locs, f, indent=4)
                
                self.item_db = new_items
                self.locations_db = new_locs
                self.build_indexes()

                self.update_queue.put(("sync_status", f"Success: {len(new_items)} database rows synced"))
            except Exception as e:
                self.update_queue.put(("sync_status", "Sync Failed!"))
                self.log_error("sync_database", e)

        threading.Thread(target=run_sync, daemon=True).start()

    def save_garmoth_api_key(self):
        try:
            self.garmoth_api_key = self.garmoth_api_entry.get().strip()
            self.save_config()
            self.update_queue.put(("sync_status", "API Key Saved!"))
        except Exception as e:
            self.log_error("save_garmoth_api_key", e)

    def reset_garmoth_button(self):
        self.garmoth_btn.configure(state="normal", text="UPLOAD TO GARMOTH", fg_color="#f39c12")
        self.garmoth_progress.stop()
        self.garmoth_progress.set(0)
        self.garmoth_progress.pack_forget()

    def upload_to_garmoth(self):
        try:
            self.garmoth_api_key = self.garmoth_api_entry.get().strip()
            self.save_config()
            
            if not self.garmoth_api_key:
                self.update_queue.put(("sync_status", "Error: No API Key"))
                return

            if not os.path.exists(GARMOTH_EXPORT_FILE):
                self.update_queue.put(("sync_status", "No Data Found"))
                return

            self.garmoth_progress.pack(fill="x", padx=10, pady=(0, 5), before=self.loot_scroll_frame)
            self.garmoth_btn.configure(state="disabled", text="UPLOADING...")
            self.garmoth_progress.start()

            with open(GARMOTH_EXPORT_FILE, 'r', encoding='utf-8') as f:
                payload = json.load(f)

            headers = {
                "apiKey": self.garmoth_api_key, 
                "Content-Type": "application/json"
            }
            url = "https://api.garmoth.com/api/external/grind-tracker/sessions/create"
            
            def perform_request():
                try:
                    response = requests.post(url, json=payload, headers=headers, timeout=20)
                    if response.status_code in [200, 201]:
                        self.update_queue.put(("sync_status", "Upload Success!"))
                    else:
                        self.update_queue.put(("sync_status", f"Failed: {response.status_code}"))
                except Exception as e:
                    self.update_queue.put(("sync_status", "Upload Error"))
                    self.log_error("upload_request", e)

            threading.Thread(target=perform_request, daemon=True).start()
        except Exception as e:
            self.log_error("upload_to_garmoth", e)

    def save_garmoth_json(self):
        try:
            elapsed_seconds = max(1, time.time() - self.start_time)
            minutes = max(1, int(elapsed_seconds / 60))
            total_silver = int(self.total_silver_value)
            hourly = int((total_silver / max(1, elapsed_seconds)) * 3600)
            
            drops = {}
            for item_name, qty in self.rapid_loot_table.items():
                item_info = {}

                if item_name in self.items_by_name:
                    first_uid = self.items_by_name[item_name][0]
                    item_info = self.item_db.get(first_uid, {})
                main_key = item_info.get("id")
                sub_key = item_info.get("sub_key", 0)
                if main_key:
                    drops[f"{str(main_key).replace(',', '')}_{sub_key}"] = int(qty)

            zone_data = self.locations_db.get(self.current_zone, {})
            payload = {
                "Class_id": int(self.current_class_id),
                "spec": int(self.current_spec),
                "grindspot_id": int(zone_data.get("garmoth_id", 0)),
                "minutes": int(minutes),
                "hourly": int(hourly),
                "total": int(total_silver),
                "global": False,
                "drops": drops
            }
            with open(GARMOTH_EXPORT_FILE, 'w', encoding='utf-8') as f:
                json.dump(payload, f, indent=4)
        except Exception as e:
            self.log_error("save_garmoth_json", e)

    def log_error(self, context, error):
        print(f"[ERROR] {context}: {error}")

    def download_icon_to_local(self, icon_url, item_id):
        """Download icon from URL and save to drop_icons folder as PNG using Item ID"""
        try:
         #   print(f"[DEBUG] download_icon_to_local called - URL: {icon_url}, ID: {item_id}")
            
            if not icon_url or not item_id:
         #       print(f"[DEBUG] Missing icon_url or item_id")
                return False

            # Ensure icon folder exists
            os.makedirs(DROPS_ICONS_FOLDER, exist_ok=True)

            # Always save as PNG
            item_id = str(item_id).replace(",", "").strip()
            local_icon_path = os.path.join(DROPS_ICONS_FOLDER, f"{item_id}.png")
         #   print(f"[DEBUG] Target path: {local_icon_path}")

            # Skip if already exists
            if os.path.exists(local_icon_path):
         #       print(f"[DEBUG] Icon already exists, skipping")
                return True

            # Download image with proper headers to avoid 403
         #   print(f"[DEBUG] Downloading from URL...")
            headers = {
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
                "Referer": "https://garmoth.com/",
                "Accept": "image/webp,image/apng,image/*,*/*;q=0.8",
                "Accept-Language": "en-US,en;q=0.9",
                "Accept-Encoding": "gzip, deflate, br",
                "Connection": "keep-alive",
                "Sec-Fetch-Dest": "image",
                "Sec-Fetch-Mode": "no-cors",
                "Sec-Fetch-Site": "cross-site"
            }
            response = requests.get(icon_url, headers=headers, timeout=10)
         #   print(f"[DEBUG] Response status: {response.status_code}")

            if response.status_code == 200:
                # Convert WEBP/other formats to PNG
                img_data = Image.open(BytesIO(response.content)).convert("RGBA")

                # Resize to consistent icon size
                img_data = img_data.resize((24, 24), Image.Resampling.LANCZOS)

                # Save as PNG
                img_data.save(local_icon_path, "PNG")

                print(f"[INFO] Downloaded and converted icon for item {item_id} to {local_icon_path}")

                return True
            else:
                print(f"[ERROR] Failed to download icon, status code: {response.status_code}")

        except Exception as e:
            self.log_error("download_icon", e)
            print(f"[ERROR] Exception in download_icon_to_local: {e}")

        return False

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

    def generate_tolerance_config(self):
        """Auto-generate tolerance_config.json from local_items.json based on category"""
        try:
            if os.path.exists(TOLERANCE_CONFIG_FILE):
                return  # Already exists
            
            tolerance_config = {
                "_category_defaults": {
                    "trash": (25, 35),  # Loose for common trash items
                    "General": (15, 25),  # Medium for general items
                    "rare": (12, 18),  # Tight for rare items
                    "default": (12, 18)  # Fallback
                },
                "_manual_overrides": {}
            }
            
            # Generate item-specific tolerances based on category
            for uid, data in self.item_db.items():
                if isinstance(data, dict):
                    item_name = data.get("name", "").lower()
                    category = data.get("category", "").lower()
                    
                    if not item_name:
                        continue
                    
                    # Use category-based default
                    if category in tolerance_config["_category_defaults"]:
                        tolerance_config[item_name] = tolerance_config["_category_defaults"][category]
                    else:
                        tolerance_config[item_name] = tolerance_config["_category_defaults"]["rare"]
            
            # Save the config
            with open(TOLERANCE_CONFIG_FILE, 'w', encoding='utf-8') as f:
                json.dump(tolerance_config, f, indent=4)
            
            print(f"[INFO] Generated tolerance_config.json with {len(tolerance_config)} items")
            
        except Exception as e:
            self.log_error("generate_tolerance_config", e)

    def load_tolerance_config(self):
        """Load tolerance config from file, generate if missing"""
        try:
            if not os.path.exists(TOLERANCE_CONFIG_FILE):
                self.generate_tolerance_config()
            
            with open(TOLERANCE_CONFIG_FILE, 'r', encoding='utf-8') as f:
                config = json.load(f)
            
            # Extract manual overrides if they exist
            manual_overrides = config.get("_manual_overrides", {})
            
            # Build tolerance dict, manual overrides take precedence
            self.item_tolerances = {}
            for item_name, tolerance in config.items():
                if not item_name.startswith("_"):
                    self.item_tolerances[item_name] = tuple(tolerance)
            
            # Apply manual overrides
            for item_name, tolerance in manual_overrides.items():
                self.item_tolerances[item_name] = tuple(tolerance)
            
            # Set default fallback
            if "default" not in self.item_tolerances:
                self.item_tolerances["default"] = (20, 30)
            
            print(f"[INFO] Loaded {len(self.item_tolerances)} item tolerances")
            
        except Exception as e:
            self.log_error("load_tolerance_config", e)
            # Fallback to hardcoded defaults
            self.item_tolerances = {"default": (20, 30)}

    def correct_spelling(self, ocr_text, max_distance=2):
        """Find closest matching item name using Levenshtein distance"""
        ocr_text = ocr_text.lower().strip()
        
        # Fast path: exact match
        if ocr_text in self.items_by_name:
            return ocr_text
        
        # Find closest match within edit distance
        best_match = None
        best_distance = max_distance
        
        for item_name in self.items_by_name.keys():
            distance = textdistance.levenshtein(ocr_text, item_name)
            if distance < best_distance:
                best_distance = distance
                best_match = item_name
        
        return best_match if best_match else ocr_text

    class MLIconClassifier:
        """ONNX-based ML classifier for drop icon recognition using MobileNetV3"""
        def __init__(self, drop_icons_folder, item_db):
            self.drop_icons_folder = drop_icons_folder
            self.item_db = item_db
            self.model = None
            self.idx_to_class = {}
            self.id_to_name = {}
            self.image_size = 64
            self._load_icon_mapping()
            self._load_class_mapping()
            
            if ML_AVAILABLE:
                self._init_model()
            else:
                print("[ML] Using mock classifier (template-based fallback)")
        
        def _load_icon_mapping(self):
            """Map icon filenames to item names from database"""
            for uid, data in self.item_db.items():
                if isinstance(data, dict):
                    item_id = str(data.get("id", "")).replace(",", "").strip()
                    item_name = data.get("name", "").lower()
                    if item_id and item_name:
                        self.id_to_name[item_id] = item_name
        
        def _load_class_mapping(self):
            """Load class mapping from training"""
            class_mapping_path = os.path.join(DATA_FOLDER, "class_mapping.json")
            if os.path.exists(class_mapping_path):
                with open(class_mapping_path, 'r') as f:
                    mapping = json.load(f)
                    self.idx_to_class = {int(k): v for k, v in mapping['idx_to_class'].items()}
                print(f"[ML] Loaded {len(self.idx_to_class)} class mappings")
            else:
                print("[ML] class_mapping.json not found, ML inference disabled")
        
        def _init_model(self):
            """Initialize ONNX model for inference"""
            onnx_path = os.path.join(DATA_FOLDER, "icon_classifier.onnx")
            if os.path.exists(onnx_path):
                try:
                    # Check available providers
                    available = ort.get_available_providers()
                    print(f"[ML] Available ONNX providers: {available}")
                    
                    # Build provider list with GPU priority
                    providers = []
                    if 'DmlExecutionProvider' in available:
                        providers.append('DmlExecutionProvider')
                    if 'CUDAExecutionProvider' in available:
                        providers.append('CUDAExecutionProvider')
                    providers.append('CPUExecutionProvider')
                    
                    print(f"[ML] Using providers: {providers}")
                    self.model = ort.InferenceSession(onnx_path, providers=providers)
                    print("[ML] Loaded ONNX model successfully")
                except Exception as e:
                    print(f"[ML] Failed to load ONNX model: {e}")
                    self.model = None
            else:
                print(f"[ML] ONNX model not found at {onnx_path}")
                self.model = None
        
        def _preprocess_image(self, icon_region):
            """Preprocess icon region for model input"""
            try:
                # Convert grayscale to RGB if needed
                if len(icon_region.shape) == 2:
                    icon_region = cv2.cvtColor(icon_region, cv2.COLOR_GRAY2RGB)
                elif icon_region.shape[2] == 4:
                    icon_region = cv2.cvtColor(icon_region, cv2.COLOR_RGBA2RGB)
                
                # Resize to model input size
                icon_region = cv2.resize(icon_region, (self.image_size, self.image_size))
                
                # Convert to float32 and normalize
                icon_region = icon_region.astype(np.float32) / 255.0
                # ImageNet normalization
                mean = np.array([0.485, 0.456, 0.406])
                std = np.array([0.229, 0.224, 0.225])
                icon_region = (icon_region - mean) / std
                
                # Transpose to CHW format and add batch dimension
                icon_region = np.transpose(icon_region, (2, 0, 1))
                icon_region = np.expand_dims(icon_region, axis=0)
                
                return icon_region.astype(np.float32)
            except Exception as e:
                print(f"[ML] Preprocessing error: {e}")
                return None
        
        def classify(self, icon_region):
            """
            Classify icon region using ML or fallback
            Returns: (item_name, confidence_score)
            """
            if self.model is None or not self.idx_to_class:
                # Fallback: use template matching with drop_icons
                return self._template_fallback(icon_region)
            
            try:
                # Preprocess image
                input_tensor = self._preprocess_image(icon_region)
                if input_tensor is None:
                    return self._template_fallback(icon_region)
                
                # Run inference
                outputs = self.model.run(None, {'input': input_tensor})
                logits = outputs[0][0]
                
                # Apply softmax to get probabilities
                exp_logits = np.exp(logits - np.max(logits))
                probs = exp_logits / exp_logits.sum()
                
                # Get top prediction
                top_class_idx = np.argmax(probs)
                confidence = float(probs[top_class_idx])
                
                # Map to item name
                item_name = self.idx_to_class.get(top_class_idx)
                
                if item_name and confidence > 0.50:
                    return item_name, confidence
                else:
                    # Low confidence, try template fallback
                    return self._template_fallback(icon_region)
                    
            except Exception as e:
                print(f"[ML] Inference error: {e}")
                return self._template_fallback(icon_region)
        
        def _template_fallback(self, icon_region):
            """Fallback to template matching using drop_icons folder"""
            try:
                best_match = None
                best_score = 0.0
                
                # Convert to grayscale for template matching
                if len(icon_region.shape) == 3:
                    icon_region_gray = cv2.cvtColor(icon_region, cv2.COLOR_RGB2GRAY)
                else:
                    icon_region_gray = icon_region
                
                # Try to match against local icons
                for icon_file in os.listdir(self.drop_icons_folder):
                    if not icon_file.endswith('.png'):
                        continue
                    
                    icon_path = os.path.join(self.drop_icons_folder, icon_file)
                    template = cv2.imread(icon_path, cv2.IMREAD_GRAYSCALE)
                    
                    if template is None:
                        continue
                    
                    # Resize to match
                    if icon_region_gray.shape != template.shape:
                        template = cv2.resize(template, (icon_region_gray.shape[1], icon_region_gray.shape[0]))
                    
                    result = cv2.matchTemplate(icon_region_gray, template, cv2.TM_CCOEFF_NORMED)
                    score = float(result.max())
                    
                    if score > best_score:
                        best_score = score
                        item_id = icon_file.replace('.png', '')
                        best_match = self.id_to_name.get(item_id)
                
                if best_score > 0.75:  # Threshold for template fallback
                    return best_match, best_score
                
                return None, 0.0
            except Exception as e:
                print(f"[ML] Template fallback error: {e}")
                return None, 0.0
    
    def extract_icon_region(self, frame, box_coords):
        """Extract icon region from frame using OCR bounding box"""
        try:
            x1, y1 = int(box_coords[0][0]), int(box_coords[0][1])
            x2, y2 = int(box_coords[2][0]), int(box_coords[2][1])
            
            # Extract region to the left of text (where icon typically is)
            icon_width = min(40, x1)  # Max 40px width
            icon_height = y2 - y1
            
            if icon_width <= 0 or icon_height <= 0:
                return None
            
            icon_region = frame[max(0, y1):min(frame.shape[0], y2), 
                               max(0, x1 - icon_width):x1]
            
            if icon_region.size == 0:
                return None
            
            # Keep RGB for ML model (preprocessing will handle conversion)
            return icon_region
        except Exception as e:
            print(f"[ML] Icon extraction error: {e}")
            return None

    def load_config(self):
        config = self.load_json(CONFIG_FILE)
        defaults = {
            "top": 800, "left": 2000, "width": 500, "height": 250, 
            "font": "Georama", "class": "Select Class", "class_id": 0, "spec": 0, "transparency": 0.9,
            "hotkey": "F10",
            "garmoth_api_key": ""
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
            "class_id": self.current_class_id,
            "spec": self.current_spec,
            "transparency": self.transparency_val,
            "hotkey": self.current_hotkey_str,
            "garmoth_api_key": self.garmoth_api_key,
            "boss_region": self.boss_region,
            "sound_volume": self.sound_volume,
            "sound_notifications": self.sound_notifications
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
        
        # Update main buttons
        if hasattr(self, 'start_btn'):
            self.start_btn.configure(font=(self.current_font_family, 12, "bold"))
        if hasattr(self, 'stop_btn'):
            self.stop_btn.configure(font=(self.current_font_family, 12, "bold"))
        if hasattr(self, 'click_btn'):
            self.click_btn.configure(font=(self.current_font_family, 12, "bold"))
        if hasattr(self, 'garmoth_btn'):
            self.garmoth_btn.configure(font=(self.current_font_family, 12, "bold"))
        if hasattr(self, 'save_api_btn'):
            self.save_api_btn.configure(font=(self.current_font_family, 12, "bold"))
        if hasattr(self, 'sync_btn'):
            self.sync_btn.configure(font=(self.current_font_family, 12, "bold"))
        
        # Update all loot rows with new font
        for item_name, row in self.loot_rows.items():
            for child in row.winfo_children():
                if isinstance(child, ctk.CTkLabel):
                    current_font = child.cget("font")
                    if isinstance(current_font, tuple) and len(current_font) >= 2:
                        child.configure(font=(self.current_font_family, current_font[1]) + (current_font[2:] if len(current_font) > 2 else ()))

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

    def set_boss_region(self, selected_region):
        self.boss_region = selected_region
        self.save_config()
        self.setup_boss_timer()

    def toggle_sound_notification(self, key):
        self.sound_notifications[key] = not self.sound_notifications.get(key, False)
        self.save_config()

    def set_sound_volume(self, value):
        self.sound_volume = float(value)
        volume_label = self.volume_slider.master.winfo_children()[2]  # Get the volume label
        volume_label.configure(text=f"Volume: {int(self.sound_volume * 100)}%")
        self.save_config()

    def test_boss_sound(self):
        """Test play the boss spawn sound"""
        try:
            test_sound_file = os.path.join(SOUNDS_FOLDER, "spawn.mp3")
            if os.path.exists(test_sound_file):
                pygame.mixer.music.load(test_sound_file)
                pygame.mixer.music.set_volume(self.sound_volume)
                pygame.mixer.music.play()
            else:
                print(f"[ERROR] Sound file not found: {test_sound_file}")
        except Exception as e:
            print(f"[ERROR] Failed to play test sound: {e}")

    def add_mousewheel_to_dropdown(self, dropdown):
        """Mousewheel not supported for customtkinter dropdowns - use arrow keys instead"""
        pass

    def setup_widgets(self):
        self.tabview = ctk.CTkTabview(self, segmented_button_fg_color="#1a1a1a", segmented_button_selected_color="#3498db")
        self.tabview.pack(padx=10, pady=10, fill="both", expand=True)
        self.tabview.add("Tracker")
        self.tabview.add("Guides")
        self.tabview.add("Boss Timer")
        self.tabview.add("Settings")

        tracker_tab = self.tabview.tab("Tracker")
        tracker_tab.configure(fg_color="#000000")

        self.header_frame = ctk.CTkFrame(tracker_tab, fg_color="transparent")
        self.header_frame.pack(fill="x", pady=(5, 0))

        # Left container for location and class name
        self.left_header = ctk.CTkFrame(self.header_frame, fg_color="transparent")
        self.left_header.pack(side="left", padx=5)

        self.zone_label = ctk.CTkLabel(self.left_header, text=self.current_zone.upper(), text_color="#3498db", anchor="center", font=(self.current_font_family, 17, "bold"))
        self.zone_label.pack(fill="x", pady=(0, 2))

        self.class_name_label = ctk.CTkLabel(self.left_header, text=self.current_class.upper(), text_color="#ffffff", anchor="center", font=(self.current_font_family, 17, "bold"))
        self.class_name_label.pack(fill="x")

        # Class icon to the right of class name
        self.class_icon_label = ctk.CTkLabel(self.header_frame, text="", width=100, height=100)
        self.class_icon_label.pack(side="right", padx=5)
        self.update_class_icon()

        self.row_frame = ctk.CTkFrame(tracker_tab, fg_color="transparent")
        self.row_frame.pack(fill="x", pady=10)

        self.timer_container = ctk.CTkFrame(self.row_frame, fg_color="transparent")
        self.timer_container.pack(side="left", padx=5)

        ctk.CTkLabel(self.timer_container, text="TIME", font=(self.current_font_family, 12), text_color="#00ff88").pack(anchor="w")
        self.timer_label = ctk.CTkLabel(self.timer_container, text="00:00:00", text_color="#ffffff")
        self.timer_label.pack(anchor="w")

        self.silver_container = ctk.CTkFrame(self.row_frame, fg_color="transparent")
        self.silver_container.pack(side="right", padx=5)

        ctk.CTkLabel(self.silver_container, text="TOTAL SILVER", font=(self.current_font_family, 12), text_color="#00ff88").pack(anchor="e")
        self.silver_label = ctk.CTkLabel(self.silver_container, text="0", text_color="#ffffff")
        self.silver_label.pack(anchor="e")

        self.stats_grid = ctk.CTkFrame(tracker_tab, fg_color="transparent")
        self.stats_grid.pack(fill="x", pady=5)
        self.stats_grid.columnconfigure((0, 1), weight=1)

        self.s_hr_box = ctk.CTkFrame(self.stats_grid, fg_color="#1a1a1a", corner_radius=2)
        self.s_hr_box.grid(row=0, column=0, padx=5, sticky="nsew")
        ctk.CTkLabel(self.s_hr_box, text="SILVER / HR", font=(self.current_font_family, 10), text_color="#00ff88").pack(pady=(5,0))
        self.silver_hr_label = ctk.CTkLabel(self.s_hr_box, text="0")
        self.silver_hr_label.pack(pady=(0,5))

        self.t_hr_box = ctk.CTkFrame(self.stats_grid, fg_color="#1a1a1a", corner_radius=2)
        self.t_hr_box.grid(row=0, column=1, padx=5, sticky="nsew")
        ctk.CTkLabel(self.t_hr_box, text="TRASH / HR", font=(self.current_font_family, 10), text_color="#00ff88").pack(pady=(5,0))
        self.trash_hr_label = ctk.CTkLabel(self.t_hr_box, text="0")
        self.trash_hr_label.pack(pady=(0,5))

        self.btn_frame = ctk.CTkFrame(tracker_tab, fg_color="transparent")
        self.btn_frame.pack(fill="x", pady=10)
        self.start_btn = ctk.CTkButton(self.btn_frame, text="START/RESET", fg_color="#27ae60", height=32, font=(self.current_font_family, 12, "bold"), command=self.start_session)
        self.start_btn.pack(side="left", padx=5, expand=True)
        self.stop_btn = ctk.CTkButton(self.btn_frame, text="STOP", fg_color="#c0392b", height=32, font=(self.current_font_family, 12, "bold"), command=self.stop_session)
        self.stop_btn.pack(side="left", padx=5, expand=True)

        self.click_btn = ctk.CTkButton(tracker_tab, text=f"{self.current_hotkey_str}: CLICK-THRU OFF", fg_color="#34495e", height=32, font=(self.current_font_family, 12, "bold"), command=self.toggle_click_through)
        self.click_btn.pack(fill="x", padx=5, pady=5)

        self.garmoth_btn = ctk.CTkButton(tracker_tab, text="UPLOAD TO GARMOTH", fg_color="#f39c12", height=32, font=(self.current_font_family, 12, "bold"), command=self.upload_to_garmoth)
        self.garmoth_btn.pack(fill="x", padx=5, pady=5)

        self.garmoth_progress = ctk.CTkProgressBar(tracker_tab, orientation="horizontal", height=8, progress_color="#3498db")
        self.garmoth_progress.set(0)

        self.loot_scroll_frame = ctk.CTkFrame(tracker_tab, fg_color="transparent", corner_radius=0)
        self.loot_scroll_frame.pack(pady=5, fill="both", expand=True)

        guides_tab = self.tabview.tab("Guides")
        guides_tab.configure(fg_color="#000000")

        # Load videos from JSON
        videos_config = self.load_json(VIDEOS_FILE)
        videos_list = videos_config.get("videos", [])

        # Display each video
        for video_data in videos_list:
            video_id = video_data.get("id", "")
            video_title = video_data.get("title", "Video Guide")
            start_time = video_data.get("start_time", "")
            
            if not video_id:
                continue

            # Video preview section
            video_frame = ctk.CTkFrame(guides_tab, fg_color="#1a1a1a", corner_radius=10)
            video_frame.pack(pady=10, padx=10, fill="x")

            video_url = f"https://www.youtube.com/watch?v={video_id}"
            if start_time:
                video_url += f"&t={start_time}s"

            try:
                thumbnail_url = f"https://img.youtube.com/vi/{video_id}/maxresdefault.jpg"
                response = requests.get(thumbnail_url, timeout=5)
                if response.status_code == 200:
                    img_data = Image.open(BytesIO(response.content))
                    img_data = img_data.resize((320, 180), Image.Resampling.LANCZOS)
                    video_thumbnail = ctk.CTkImage(light_image=img_data, dark_image=img_data, size=(320, 180))
                    
                    video_button = ctk.CTkButton(video_frame, image=video_thumbnail, text="", fg_color="transparent", 
                                               hover_color="#3498db", cursor="hand2", font=(self.current_font_family, 12), command=lambda url=video_url: webbrowser.open(url))
                    video_button.pack(pady=10)
                else:
                    # Fallback to high quality if maxres not available
                    thumbnail_url = f"https://img.youtube.com/vi/{video_id}/hqdefault.jpg"
                    response = requests.get(thumbnail_url, timeout=5)
                    if response.status_code == 200:
                        img_data = Image.open(BytesIO(response.content))
                        img_data = img_data.resize((320, 180), Image.Resampling.LANCZOS)
                        video_thumbnail = ctk.CTkImage(light_image=img_data, dark_image=img_data, size=(320, 180))
                        
                        video_button = ctk.CTkButton(video_frame, image=video_thumbnail, text="", fg_color="transparent", 
                                                   hover_color="#3498db", cursor="hand2", font=(self.current_font_family, 12), command=lambda url=video_url: webbrowser.open(url))
                        video_button.pack(pady=10)
            except:
                # Fallback to text link if image loading fails
                video_link = ctk.CTkLabel(video_frame, text=f"▶ {video_title}", font=(self.current_font_family, 14, "bold"), 
                                         text_color="#3498db", cursor="hand2")
                video_link.pack(pady=15)
                video_link.bind("<Button-1>", lambda e, url=video_url: webbrowser.open(url))

            ctk.CTkLabel(video_frame, text=f"Click to watch {video_title}", font=(self.current_font_family, 10), text_color="#bdc3c7").pack(pady=(0, 10))

        # Add clickable link at the bottom
        guides_link_frame = ctk.CTkFrame(guides_tab, fg_color="#1a1a1a", corner_radius=10)
        guides_link_frame.pack(pady=10, padx=10, fill="x")
        
        guides_link_btn = ctk.CTkButton(guides_link_frame, text="Ultimate Site for BDO Guides", 
                                       fg_color="#9b59b6", hover_color="#8e44ad", height=35,
                                       font=(self.current_font_family, 12, "bold"),
                                       command=lambda: webbrowser.open("https://garmoth.com/guides"))
        guides_link_btn.pack(pady=10, padx=10, fill="x")
        
        # Add class guides button
        class_guides_frame = ctk.CTkFrame(guides_tab, fg_color="#1a1a1a", corner_radius=10)
        class_guides_frame.pack(pady=10, padx=10, fill="x")
        
        class_guides_btn = ctk.CTkButton(class_guides_frame, text="Ultimate Site for Class Guides", 
                                         fg_color="#3498db", hover_color="#2980b9", height=35,
                                         font=(self.current_font_family, 12, "bold"),
                                         command=lambda: webbrowser.open("https://www.blackdesertfoundry.com/category/all-guides/class-guides/"))
        class_guides_btn.pack(pady=10, padx=10, fill="x")

        boss_timer_tab = self.tabview.tab("Boss Timer")
        boss_timer_tab.configure(fg_color="#000000")
        
        # Region selector
        region_frame = ctk.CTkFrame(boss_timer_tab, fg_color="#1a1a1a", corner_radius=5)
        region_frame.pack(fill="x", padx=10, pady=5)
        
        ctk.CTkLabel(region_frame, text="Region:", font=(self.current_font_family, 12), text_color="#bdc3c7").pack(side="left", padx=10)
        self.region_dropdown = ctk.CTkComboBox(region_frame, values=["EU", "NA", "SEA", "JP", "KR", "MENA", "SA", "RU"], command=self.set_boss_region, width=100)
        self.region_dropdown.set(self.boss_region)
        self.region_dropdown.pack(side="left", padx=10)
        
        self.boss_scroll_frame = ctk.CTkScrollableFrame(boss_timer_tab, fg_color="transparent", corner_radius=0, scrollbar_button_color="#000000", scrollbar_button_hover_color="#000000", scrollbar_fg_color="#000000")
        self.boss_scroll_frame.pack(fill="both", expand=True, padx=10, pady=5)
        
        # Sound notifications frame
        sound_frame = ctk.CTkFrame(boss_timer_tab, fg_color="#1a1a1a", corner_radius=5)
        sound_frame.pack(fill="x", padx=10, pady=5)
        
        ctk.CTkLabel(sound_frame, text="Sound Notifications:", font=(self.current_font_family, 12, "bold"), text_color="#3498db").pack(pady=(5, 0))
        
        self.sound_checkboxes = {}
        sound_options = [("30 min", "30min"), ("15 min", "15min"), ("10 min", "10min"), ("5 min", "5min"), ("3 min", "3min"), ("1 min", "1min"), ("On Spawn", "spawn")]
        
        checkbox_frame = ctk.CTkFrame(sound_frame, fg_color="transparent")
        checkbox_frame.pack(pady=5)
        
        for i, (label, key) in enumerate(sound_options):
            if i % 2 == 0:
                row_frame = ctk.CTkFrame(checkbox_frame, fg_color="transparent")
                row_frame.pack(fill="x", pady=2)
            
            checkbox = ctk.CTkCheckBox(row_frame, text=label, command=lambda k=key: self.toggle_sound_notification(k))
            checkbox.select() if self.sound_notifications.get(key, False) else checkbox.deselect()
            checkbox.pack(side="left", padx=5)
            self.sound_checkboxes[key] = checkbox
        
        # Volume slider
        volume_label = ctk.CTkLabel(sound_frame, text=f"Volume: {int(self.sound_volume * 100)}%", font=(self.current_font_family, 10), text_color="#bdc3c7")
        volume_label.pack(pady=(5, 0))
        self.volume_slider = ctk.CTkSlider(sound_frame, from_=0.0, to=1.0, command=self.set_sound_volume)
        self.volume_slider.set(self.sound_volume)
        self.volume_slider.pack(pady=(0, 5), padx=10, fill="x")
        
        # Test sound button
        test_sound_btn = ctk.CTkButton(sound_frame, text="🔊 TEST SOUND", fg_color="#9b59b6", height=28, font=(self.current_font_family, 11, "bold"), command=self.test_boss_sound)
        test_sound_btn.pack(pady=(5, 10), padx=10, fill="x")
        
        self.boss_labels = {}
        self.setup_boss_timer()

        settings_tab = self.tabview.tab("Settings")
        
        ctk.CTkLabel(settings_tab, text="Character Class:").pack(pady=(10,0))
        class_descriptions = [class_data["description"] for class_data in self.classes_db.values()]
        self.class_dropdown = ctk.CTkComboBox(settings_tab, values=class_descriptions, command=self.set_class, width=200)
        self.class_dropdown.pack(pady=5)
        self.add_mousewheel_to_dropdown(self.class_dropdown)

        ctk.CTkLabel(settings_tab, text="Click-thru Hotkey:").pack(pady=(10,0))
        self.hotkey_dropdown = ctk.CTkComboBox(settings_tab, values=list(VK_MAP.keys()), command=self.set_hotkey, width=200)
        self.hotkey_dropdown.pack(pady=5)
        self.add_mousewheel_to_dropdown(self.hotkey_dropdown)

        ctk.CTkLabel(settings_tab, text="UI Font:").pack(pady=(10,0))
        self.font_dropdown = ctk.CTkComboBox(settings_tab, values=self.available_fonts, command=self.set_font, width=200)
        self.font_dropdown.set(self.current_font_family)
        self.font_dropdown.pack(pady=5)

        ctk.CTkLabel(settings_tab, text="Garmoth API Key:").pack(pady=(10,0))
        self.garmoth_api_entry = ctk.CTkEntry(settings_tab, width=260, show="*")
        self.garmoth_api_entry.pack(pady=5)
        self.garmoth_api_entry.insert(0, self.garmoth_api_key)

        self.save_api_btn = ctk.CTkButton(settings_tab, text="SAVE API KEY", fg_color="#8e44ad", font=(self.current_font_family, 12, "bold"), command=self.save_garmoth_api_key)
        self.save_api_btn.pack(pady=(0,10))

        self.sync_btn = ctk.CTkButton(settings_tab, text="SYNC DATABASE", fg_color="#2980b9", font=(self.current_font_family, 12, "bold"), command=self.sync_database)
        self.sync_btn.pack(pady=(10,0))
        self.sync_status_label = ctk.CTkLabel(settings_tab, text="", font=(self.current_font_family, 10))
        self.sync_status_label.pack()

        self.transparency_label = ctk.CTkLabel(settings_tab, text=f"Transparency: {int(self.transparency_val * 100)}%")
        self.transparency_label.pack(pady=(10, 0))
        self.trans_slider = ctk.CTkSlider(settings_tab, from_=0.1, to=1.0, command=self.set_transparency)
        self.trans_slider.set(self.transparency_val)
        self.trans_slider.pack(pady=5)

        ctk.CTkButton(settings_tab, text="RE-CONFIGURE SCAN AREA", fg_color="#8e44ad", font=(self.current_font_family, 12, "bold"), command=self.toggle_selector).pack(pady=20)
        
        ctk.CTkButton(settings_tab, text="SNAP TO 357x315 (LOG SIZE + BUFFER)", fg_color="#d35400", font=(self.current_font_family, 12, "bold"), command=self.snap_to_standard_size).pack(pady=(0, 10))
        
        setup_link_frame = ctk.CTkFrame(settings_tab, fg_color="#1a1a1a", corner_radius=10)
        setup_link_frame.pack(pady=10, padx=10, fill="x")
        
        setup_link_btn = ctk.CTkButton(setup_link_frame, text="How To Setup Loot Tracker", 
                                       fg_color="#9b59b6", hover_color="#8e44ad", height=35,
                                       font=(self.current_font_family, 12, "bold"),
                                       command=lambda: webbrowser.open("https://www.youtube.com/watch?v=xQOaEX3zQXI"))
        setup_link_btn.pack(pady=10, padx=10, fill="x")

        link_label = ctk.CTkLabel(settings_tab, text="made by : https://www.twitch.tv/brownie_", text_color="#3498db", cursor="hand2")
        link_label.pack(pady=(10, 5))
        link_label.bind("<Button-1>", lambda e: webbrowser.open("https://www.twitch.tv/brownie_"))

        self.rapid_preview = ctk.CTkLabel(settings_tab, text="", fg_color="black", width=300, height=250)
        self.rapid_preview.pack(pady=10)

    def check_queue(self):
        while not self.update_queue.empty():
            task, data = self.update_queue.get()
            if task == "toggle_click": self.toggle_click_through()
            elif task == "preview":
                # data[0] = image dimensions (height, width), data[1] = image
                dims = data[0]
                img = data[1]
                self.rapid_preview.configure(image=img)
                # Update label text with dimensions to detect cropping
                self.rapid_preview.configure(text=f"OCR Input: {dims[1]}x{dims[0]}")
            elif task == "sync_status": 
                self.sync_status_label.configure(text=data)
                
                if "Upload Success" in data:
                    self.garmoth_progress.stop()
                    self.garmoth_progress.set(1)
                    self.garmoth_btn.configure(text="UPLOAD COMPLETE", fg_color="#2ecc71")
                    self.after(3000, self.reset_garmoth_button)
                elif "Failed" in data or "Error" in data or "No Data" in data:
                    self.reset_garmoth_button()

            elif task == "ui_refresh":
                self.silver_label.configure(text=f"{self.total_silver_value:,}")
                elapsed = max(1, time.time() - self.start_time)
                s_hr = int((self.total_silver_value / elapsed) * 3600)
                total_trash = sum(qty for item, qty in self.rapid_loot_table.items() if self.get_item_data(item).get("category", "").lower() == "trash")
                t_hr = int((total_trash / elapsed) * 3600)
                self.silver_hr_label.configure(text=f"{s_hr:,}")
                self.trash_hr_label.configure(text=f"{t_hr:,}")
                self.zone_label.configure(text=f"{self.current_zone.upper()}")
                self.class_name_label.configure(text=f"{self.current_class.upper()}")
                
                sorted_items = sorted(self.rapid_loot_table.items(), key=lambda x: x[1], reverse=True)
                for item_name, qty in sorted_items:
                    if item_name in self.loot_rows:
                        row_frame = self.loot_rows[item_name]
                        row_frame.qty_label.configure(text=f"x{qty:,}")
                        row_frame.pack_forget()
                        row_frame.pack(fill="x", pady=2)
                    else:
                        row = ctk.CTkFrame(self.loot_scroll_frame, fg_color="transparent")
                        row.pack(fill="x", pady=2)
                        item_data = self.get_item_data(item_name)
                        icon_url = item_data.get("icon", "")
                        item_id = item_data.get("id", "")

                   #     print(f"[DEBUG] Processing item: {item_name}, ID from DB: {item_id}, URL: {icon_url}")

                        if not icon_url:
                            pass
                        #    print(f"[DEBUG] Missing icon URL for item: {item_name}")
                        if icon_url and icon_url not in self.icon_cache:
                            try:
                                # Try to load from local drops_icons folder using Item ID
                                if item_id:
                                    local_icon_path = os.path.join(DROPS_ICONS_FOLDER, f"{item_id}.png")
                                    if os.path.exists(local_icon_path):
                                #        print(f"[DEBUG] Loading local icon: {local_icon_path}")
                                        img_data = Image.open(local_icon_path).convert("RGBA")
                                        img_data = img_data.resize((24, 24), Image.Resampling.LANCZOS)
                                        self.icon_cache[icon_url] = ctk.CTkImage(
                                            light_image=img_data,
                                            dark_image=img_data,
                                            size=(24, 24)
                                        )
                                    else:
                                        # Download missing icon to local folder
                                        self.download_icon_to_local(icon_url, item_id)
                                        # Try loading again after download
                                        if os.path.exists(local_icon_path):
                                #            print(f"[DEBUG] Downloaded and loading icon: {local_icon_path}")
                                            img_data = Image.open(local_icon_path).convert("RGBA")
                                            img_data = img_data.resize((24, 24), Image.Resampling.LANCZOS)
                                            self.icon_cache[icon_url] = ctk.CTkImage(
                                                light_image=img_data,
                                                dark_image=img_data,
                                                size=(24, 24)
                                            )
                                # Fallback to online fetch if still not in cache
                                if icon_url not in self.icon_cache:
                                    try:
                                        response = requests.get(icon_url, timeout=2)
                                        if response.status_code == 200:
                                #            print(f"[DEBUG] Fetching online icon for: {item_name}")
                                            img_data = Image.open(BytesIO(response.content)).convert("RGBA")
                                            img_data = img_data.resize((24, 24), Image.Resampling.LANCZOS)
                                            self.icon_cache[icon_url] = ctk.CTkImage(
                                                light_image=img_data,
                                                dark_image=img_data,
                                                size=(24, 24)
                                            )
                                    except:
                                        pass
                            except Exception as e:
                                self.log_error("icon_load", e)
                        if icon_url in self.icon_cache:
                            row.icon_label = ctk.CTkLabel(row, image=self.icon_cache[icon_url], text="")
                            row.icon_label.pack(side="left", padx=(5, 5))
                            row.icon_label.image = self.icon_cache[icon_url]
                        ctk.CTkLabel(row, text=item_name.title(), font=(self.current_font_family, 13), text_color="#bdc3c7", anchor="w").pack(side="left", expand=True, fill="x")
                        row.qty_label = ctk.CTkLabel(row, text=f"x{qty:,}", font=(self.current_font_family, 13, "bold"), text_color="#00ff88")
                        row.qty_label.pack(side="right", padx=5)
                        self.loot_rows[item_name] = row
        self.after(500, self.check_queue)

    def hotkey_check_loop(self):
        state_hotkey = 0
        while True:
            new_state = ctypes.windll.user32.GetAsyncKeyState(self.current_hotkey_code)
            if new_state & 0x8000 and not state_hotkey:
                self.update_queue.put(("toggle_click", None))
            state_hotkey = new_state & 0x8000
            time.sleep(0.20)

    def update_loop(self):
        try:
            # =============================================
            # GPU ONNX Runtime Providers
            # =============================================
            available_providers = ort.get_available_providers()

            use_dml = "DmlExecutionProvider" in available_providers
            use_cuda = "CUDAExecutionProvider" in available_providers

            # Build provider list for ONNX Runtime
            providers = []
            if use_dml:
                providers.append('DmlExecutionProvider')
            if use_cuda:
                providers.append('CUDAExecutionProvider')
            providers.append('CPUExecutionProvider')  # Always add CPU as fallback

            print(f"[Tracker] Available providers: {available_providers}")
            print(f"[Tracker] Using providers: {providers}")

            try:
                rapid_engine = RapidOCR(providers=providers)
                self.gpu_provider = "DirectML" if use_dml else "CUDA" if use_cuda else "CPU"
                print(f"[Tracker] OCR Provider: {self.gpu_provider}")
            except Exception as e:
                print(f"[WARNING] OCR initialization failed: {e}")
                rapid_engine = None
                self.gpu_provider = "Failed"
        except: rapid_engine = None
        
        frame_count = 0
        self.last_save_time = time.time()
        
        # Cache for faster OCR name matching
        item_cache = {}
        
        # Initialize dxcam for ultra-low-latency capture
        camera = None
        last_region = None
        
        try:
            while self.session_running:
                try:
                    frame_count += 1
                    
                    # -------------------------------------------------
                    # Recreate camera if scan region changed
                    # -------------------------------------------------
                    current_region = (
                        self.scan_region["left"],
                        self.scan_region["top"],
                        self.scan_region["left"] + self.scan_region["width"],
                        self.scan_region["top"] + self.scan_region["height"]
                    )
                    if last_region != current_region or camera is None:
                        if camera is not None:
                            camera.release()
                        camera = dxcam.create(region=current_region, output_color="BGR")
                        last_region = current_region
                        print(f"[INFO] Camera recreated for new region: {current_region}")
                    
                    # -------------------------------------------------
                    # Capture Screen Region with DXCAM
                    # -------------------------------------------------
                    frame = camera.grab()
                    if frame is None:
                        time.sleep(0.01)
                        continue
                    
                    # Convert BGR numpy array to RGB PIL Image
                    raw_img = Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))
                    
                    # Larger bottom border to prevent text cutoff at bottom
                    raw_img = ImageOps.expand(raw_img, border=(0, 0, 0, 30), fill="black")
                    
                    # -------------------------------------------------
                    # Image Processing
                    # -------------------------------------------------
                    enhanced = ImageOps.grayscale(raw_img)
                    
                    # Lower threshold slightly for better rare item detection
                    enhanced = enhanced.point(lambda p: 255 if p > 150 else 0)
                    
                    # Smaller upscale = MUCH lower CPU usage
                    w, h = enhanced.size
                    rapid_base = enhanced.resize((int(w * 2), int(h * 2)), Image.Resampling.BILINEAR).convert("RGB")
                    
                    # Convert to numpy once
                    rapid_np = np.array(rapid_base)

                    # =============================================
                    # FRAME DIFFERENCING
                    # =============================================
                    gray_np = cv2.cvtColor(rapid_np, cv2.COLOR_RGB2GRAY)

                    # Morphology preprocessing
                    gray_np = self.preprocess_for_ocr(gray_np)

                    # Fallback: bypass filters after 10 consecutive failures
                    bypass_filters = self.consecutive_filter_failures >= 10

                    if not bypass_filters and not self.has_frame_changed(gray_np):
                      #  print(f"[DEBUG] Frame differencing: no change detected (threshold: {self.motion_threshold})")
                        self.consecutive_filter_failures += 1
                        time.sleep(0.05)
                        continue

                    # =============================================
                    # DETECT LOOT ROWS
                    # =============================================
                    if not bypass_filters:
                        loot_rows = self.detect_loot_rows(gray_np)

                        if not loot_rows:
                          #  print(f"[DEBUG] No loot rows detected")
                            self.consecutive_filter_failures += 1
                            time.sleep(0.05)
                            continue
                    else:
                      #  print(f"[FALLBACK] Bypassing loot row detection (failures: {self.consecutive_filter_failures})")
                        loot_rows = [(0, 0, rapid_np.shape[1], rapid_np.shape[0])]  # Use full image

                    # =============================================
                    # NEW ROW FILTERING
                    # =============================================
                    if not bypass_filters:
                        new_rows = []

                        for row in loot_rows:
                            if row not in self.cached_row_regions:
                                new_rows.append(row)

                        self.cached_row_regions = loot_rows

                        if not new_rows:
                        #    print(f"[DEBUG] No new rows (all cached)")
                            self.consecutive_filter_failures += 1
                            continue
                    else:
                      #  print(f"[FALLBACK] Bypassing row filtering")
                        new_rows = loot_rows

                    # =============================================
                    # OCR COOLDOWN
                    # =============================================
                    current_time = time.time()

                    # Skip cooldown check in fallback mode to ensure OCR runs
                    if not bypass_filters and current_time - self.last_ocr_time < self.ocr_cooldown:
                     #   print(f"[DEBUG] OCR cooldown: {current_time - self.last_ocr_time:.3f}s < {self.ocr_cooldown}s")
                        self.consecutive_filter_failures += 1
                        continue

                    self.last_ocr_time = current_time

                    # -------------------------------------------------
                    # OCR ONLY Every 3 Frames
                    # -------------------------------------------------
                    # Skip frame check in fallback mode to ensure OCR runs
                    if not bypass_filters and frame_count % 5 != 0:
                     #   print(f"[DEBUG] Frame skip: {frame_count} % 3 != 0")
                        time.sleep(0.25)
                        continue

                    # -------------------------------------------------
                    # Preview Refresh - Show EXACTLY what OCR sees (1:1)
                    # -------------------------------------------------
                    # Convert gray_np (actual OCR input) back to PIL Image for display
                    # NO thumbnail resize - show actual aspect ratio to detect cropping
                    ocr_input_pil = Image.fromarray(gray_np)
                    # Resize to fit window while preserving aspect ratio
                    w, h = ocr_input_pil.size
                    scale = min(300 / w, 250 / h)
                    new_w, new_h = int(w * scale), int(h * scale)
                    ocr_input_resized = ocr_input_pil.resize((new_w, new_h), Image.Resampling.NEAREST)
                    img2 = ctk.CTkImage(light_image=ocr_input_resized, size=ocr_input_resized.size)
                    # Pass dimensions to detect cropping
                    self.update_queue.put(("preview", (gray_np.shape, img2)))

                    # Debug: Check if we reach OCR submission point
                   # print(f"[DEBUG] Reached OCR submission point (rapid_engine: {rapid_engine is not None})")

                    if rapid_engine:
                     #   print(f"[DEBUG] Running OCR (frame: {frame_count})")
                        # Use synchronous OCR like Tracker.py for reliability
                        res, _ = rapid_engine(rapid_np)
                     #   print(f"[DEBUG] OCR result: {len(res) if res else 0} detections")
                        if res:
                            # Reset failure counter on successful OCR
                            self.consecutive_filter_failures = 0
                            now = time.time()
                            updated = False
                            
                            # Remove stale tracking entries
                            self.active_tracks = [t for t in self.active_tracks if now - t['last_time'] < 3.0]
                            
                            search_pool = self.active_pool if self.active_pool else list(self.items_by_name.keys())
                            
                            for box_data in res:
                                try:
                                    box_coords = box_data[0]
                                    line = str(box_data[1]).strip().lower()
                                    score = float(box_data[2])
                                    
                                    # Lower confidence threshold improves misses
                                    if score < 0.50:
                                        continue
                                    
                                    # -------------------------------------------------
                                    # HYBRID: Use ML fallback for low-confidence OCR
                                    # -------------------------------------------------
                                    use_ml_fallback = False
                                    item = None
                                    
                                    if score < self.ml_confidence_threshold and self.ml_classifier:
                                        # Try ML classification on icon region
                                        icon_region = self.extract_icon_region(rapid_np, box_coords)
                                        if icon_region is not None:
                                            ml_item, ml_score = self.ml_classifier.classify(icon_region)
                                            if ml_item and ml_score > score:
                                                item = ml_item
                                                use_ml_fallback = True
                                                print(f"[ML] Fallback used: OCR={score:.2f} -> ML={ml_score:.2f} for {item}")
                                    
                                    if not use_ml_fallback:
                                        if len(line) < 3:
                                            continue
                                    
                                    y_center = sum(p[1] for p in box_coords) / 4
                                    x_center = sum(p[0] for p in box_coords) / 4
                                    
                                    # -------------------------------------------------
                                    # Quantity Detection
                                    # -------------------------------------------------
                                    qty_match = re.findall(r'(\d+)', line)
                                    
                                    if not use_ml_fallback:
                                        clean_name = re.sub(r'[^a-z\s-]', '', re.sub(r'[x\s]?\d+', '', line)).strip()
                                        
                                        if not clean_name:
                                            continue
                                        
                                        # -------------------------------------------------
                                        # Cached Match Lookup
                                        # -------------------------------------------------
                                        item = item_cache.get(clean_name)
                                        
                                        if not item:
                                            # Try spell correction first
                                            corrected = self.correct_spelling(clean_name)
                                            if corrected in self.items_by_name:
                                                item = corrected
                                                item_cache[clean_name] = item
                                            else:
                                                # Fallback to fuzzy matching
                                                name_len = len(clean_name)
                                                cutoff = 0.75 if name_len < 10 else 0.70
                                                match = get_close_matches(clean_name, search_pool, n=1, cutoff=cutoff)
                                                
                                                if match:
                                                    item = match[0]
                                                    item_cache[clean_name] = item
                                                else:
                                                    continue
                                    else:
                                        # ML fallback already set item, cache it
                                        if item:
                                            item_cache[f"ml_{item}"] = item
                                    
                                    qty = 1
                                    if qty_match:
                                        try: qty = int(qty_match[-1].replace(',', ''))
                                        except: pass
                                    elif self.get_item_data(item).get("category", "").lower() == "trash":
                                        qty = 1
                                    
                                    # -------------------------------------------------
                                    # Duplicate Detection with X/Y Tracking
                                    # -------------------------------------------------
                                    is_duplicate = False
                                    item_lower = item.lower()
                                    y_tol, x_tol = self.item_tolerances.get(item_lower, self.item_tolerances["default"])
                                    
                                    for track in self.active_tracks:
                                        if track['name'] == item and track['qty'] == qty:
                                            # Item-specific tolerance
                                            if -y_tol < (y_center - track['last_y']) < y_tol and -x_tol < (x_center - track.get('last_x', x_center)) < x_tol:
                                                track['last_y'] = y_center
                                                track['last_x'] = x_center
                                                track['last_time'] = now
                                                is_duplicate = True
                                                break
                                    
                                    if not is_duplicate:
                                        self.detect_zone(item)
                                        self.rapid_loot_table[item] = self.rapid_loot_table.get(item, 0) + qty
                                        self.active_tracks.append({'name': item, 'qty': qty, 'last_y': y_center, 'last_x': x_center, 'last_time': now})
                                        updated = True
                                except Exception as e:
                                    self.log_error("ocr_processing", e)
                                    continue
                            
                            if updated:
                                self.update_queue.put(("ui_refresh", None))
                                # Reduce disk write frequency
                                if now - self.last_save_time > 5.0:
                                    self.save_loot_data()
                                    self.last_save_time = now
                except Exception as e: self.log_error("update_loop", e)
                time.sleep(0.25)
        finally:
            # Release dxcam camera
            if camera:
                camera.release()


    def has_frame_changed(self, current_gray):
        try:
            if self.last_frame_gray is None:
                self.last_frame_gray = current_gray
                return True

            diff = cv2.absdiff(self.last_frame_gray, current_gray)
            mean_diff = np.mean(diff)

            self.last_frame_gray = current_gray

            return mean_diff > self.motion_threshold

        except Exception as e:
            self.log_error("has_frame_changed", e)
            return True

    def detect_loot_rows(self, binary_img):
        try:
            contours, _ = cv2.findContours(
                binary_img,
                cv2.RETR_EXTERNAL,
                cv2.CHAIN_APPROX_SIMPLE
            )

            rows = []

            for cnt in contours:
                x, y, w, h = cv2.boundingRect(cnt)

                # Relaxed constraints: w < 50 or h < 8 or h > 100
                if w < 50 or h < 8:
                    continue

                if h > 100:
                    continue

                rows.append((x, y, w, h))

            rows.sort(key=lambda r: r[1])

            return rows

        except Exception as e:
            self.log_error("detect_loot_rows", e)
            return []

    def process_ocr_async(self, rapid_engine, image_array):
        try:
            result, _ = rapid_engine(image_array)
            return result
        except Exception as e:
            self.log_error("process_ocr_async", e)
            return []


    def load_item_templates(self):
        try:
            template_dir = os.path.join(os.getcwd(), "item_templates")

            if not os.path.exists(template_dir):
                return

            for file in os.listdir(template_dir):
                if not file.lower().endswith(".png"):
                    continue

                path = os.path.join(template_dir, file)

                img = cv2.imread(path, cv2.IMREAD_UNCHANGED)

                if img is None:
                    continue

                img = cv2.resize(img, self.icon_size)

                item_name = os.path.splitext(file)[0].lower()

                self.template_cache[item_name] = img

        except Exception as e:
            self.log_error("load_item_templates", e)

    def template_match_item(self, icon_region):
        try:
            if icon_region is None:
                return None, 0.0

            best_name = None
            best_score = 0.0

            for scale in self.template_scales:
                scaled_region = cv2.resize(icon_region, (scale, scale))

                for item_name, template in self.template_cache.items():
                    scaled_template = cv2.resize(template, (scale, scale))

                    result = cv2.matchTemplate(
                        scaled_region,
                        scaled_template,
                        cv2.TM_CCOEFF_NORMED
                    )

                    score = float(result.max())

                    if score > best_score:
                        best_score = score
                        best_name = item_name

            if best_score >= self.template_threshold:
                return best_name, best_score

            return None, best_score

        except Exception as e:
            self.log_error("template_match_item", e)
            return None, 0.0


    def preprocess_for_ocr(self, gray_np):
        try:
            _, thresh = cv2.threshold(
                gray_np,
                150,
                255,
                cv2.THRESH_BINARY
            )

            kernel = np.ones((2, 2), np.uint8)

            dilated = cv2.dilate(thresh, kernel, iterations=1)
            processed = cv2.erode(dilated, kernel, iterations=1)

            return processed

        except Exception as e:
            self.log_error("preprocess_for_ocr", e)
            return gray_np

    def temporal_validate(self, item_name):
        try:
            now = time.time()

            if item_name not in self.temporal_cache:
                self.temporal_cache[item_name] = {
                    "hits": 1,
                    "last_seen": now
                }
                return False

            self.temporal_cache[item_name]["hits"] += 1
            self.temporal_cache[item_name]["last_seen"] = now

            return (
                self.temporal_cache[item_name]["hits"]
                >= self.temporal_required_hits
            )

        except Exception as e:
            self.log_error("temporal_validate", e)
            return True

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
        self.current_zone = "SEARCHING..."
        self.zone_label.configure(text=self.current_zone.upper())
        self.rapid_loot_table = {}
        self.loot_table = {}
        self.total_silver_value = 0
        self.active_tracks = []
        self.active_pool = []

        # ================= PERFORMANCE =================
        self.last_frame_gray = None
        self.last_loot_boxes = []
        self.last_ocr_time = 0
        self.frame_skip_counter = 0
        self.consecutive_filter_failures = 0

        # OCR worker thread
        self.ocr_executor = ThreadPoolExecutor(max_workers=1)
        self.ocr_future = None

        # Frame differencing threshold
        self.motion_threshold = 0.5

        # Cache loot row regions
        self.cached_row_regions = []

        # Template matching
        self.template_cache = {}
        self.template_threshold = 0.88
        self.icon_size = (32, 32)

        # Temporal confidence tracking
        self.temporal_cache = {}
        self.temporal_required_hits = 2

        # Load item-specific tolerances from config file
        self.load_tolerance_config()

        # Multi-scale template matching
        self.template_scales = [28, 32, 36]



        # OCR cooldown
        self.ocr_cooldown = 0.20

        self.load_item_templates()
        for row in self.loot_rows.values():
            row.destroy()
        self.loot_rows = {}
        self.silver_label.configure(text="0")
        self.silver_hr_label.configure(text="0")
        self.trash_hr_label.configure(text="0")
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
        self.save_garmoth_json()
        self.save_loot_data()
        self.log_to_history()

    def save_loot_data(self):
        try:
            self.loot_table = self.rapid_loot_table.copy()
            self.total_silver_value = sum(qty * self.get_item_data(item).get("price", 0) for item, qty in self.loot_table.items())
            elapsed = max(1, time.time() - self.start_time)
            s_hr = int((self.total_silver_value / elapsed) * 3600)
            total_trash = sum(qty for item, qty in self.loot_table.items() if self.get_item_data(item).get("category", "").lower() == "trash")
            t_hr = int((total_trash / elapsed) * 3600)
            items_with_icons = {}
            for item, qty in self.loot_table.items():
                item_data = self.get_item_data(item)
                item_id = item_data.get("id", "")
                # Use local icon path if available, otherwise use online URL
                if item_id and os.path.exists(os.path.join(DROPS_ICONS_FOLDER, f"{item_id}.png")):
                    icon_path = f"drop_icons/{item_id}.png"
                else:
                    icon_path = item_data.get("icon", "")
                items_with_icons[item] = {"count": qty, "icon": icon_path}
            class_icon_path = ""
            for class_key, class_data in self.classes_db.items():
                if class_data["description"] == self.current_class:
                    class_icon_path = class_data.get("icon", "")
                    break
            base = {"class": self.current_class, "class_icon": class_icon_path, "location": self.current_zone, "start_timestamp": self.start_time, "session_duration": self.timer_label.cget("text"), "total_silver": self.total_silver_value, "silver_per_hr": s_hr, "trash_per_hr": t_hr, "session_active": self.session_running, "timestamp": int(time.time()), "items": items_with_icons}
            with open(EXPORT_FILE, "w", encoding='utf-8') as f: json.dump(base, f, indent=4)
        except Exception as e: self.log_error("save_loot_data", e)

    def log_to_history(self):
        try:
            self.loot_table = self.rapid_loot_table.copy()
            total_silver = sum(qty * self.get_item_data(item).get("price", 0) for item, qty in self.loot_table.items())
            elapsed = max(1, time.time() - self.start_time)
            s_hr = int((total_silver / elapsed) * 3600)
            total_trash = sum(qty for item, qty in self.loot_table.items() if self.get_item_data(item).get("category", "").lower() == "trash")
            t_hr = int((total_trash / elapsed) * 3600)
            details = {}
            for item, qty in self.loot_table.items():
                item_data = self.get_item_data(item)
                item_id = item_data.get("id", "")
                # Use local icon path if available, otherwise use online URL
                if item_id and os.path.exists(os.path.join(DROPS_ICONS_FOLDER, f"{item_id}.png")):
                    icon_path = f"drop_icons/{item_id}.png"
                else:
                    icon_path = item_data.get("icon", "")
                details[item] = {"qty": qty, "price": item_data.get("price", 0), "icon": icon_path}
            loot_summary = ", ".join([f"{item} (x{qty})" for item, qty in self.loot_table.items()])
            class_icon_path = ""
            for class_key, class_data in self.classes_db.items():
                if class_data["description"] == self.current_class:
                    class_icon_path = class_data.get("icon", "")
                    break
            file_exists = os.path.exists(HISTORY_FILE) and os.path.getsize(HISTORY_FILE) > 0
            with open(HISTORY_FILE, 'a', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                if not file_exists:
                    writer.writerow(["Timestamp", "Class", "Class Icon", "Location", "Duration", "Total Silver", "Silver/Hr", "Trash/Hr", "Loot Summary", "Raw Data"])
                writer.writerow([time.strftime("%Y-%m-%d %H:%M:%S"), self.current_class, class_icon_path, self.current_zone, self.timer_label.cget("text"), total_silver, s_hr, t_hr, loot_summary, json.dumps(details)])
            
            history_list = []
            if os.path.exists(HISTORY_FILE):
                with open(HISTORY_FILE, 'r', encoding='utf-8') as f:
                    reader = csv.reader(f)
                    for row in reader:
                        if not row or row[0] == "Timestamp": continue
                        try:
                            history_list.append({"timestamp": row[0], "class": row[1], "class_icon": row[2], "location": row[3], "duration": row[4], "total_silver": int(row[5]), "silver_hr": int(row[6]), "trash_hr": int(row[7]), "details": json.loads(row[-1])})
                        except: continue
            with open(HISTORY_JS_FILE, "w", encoding='utf-8') as f:
                f.write(f"const grindHistory = {json.dumps(history_list, indent=4)};")
        except Exception as e: self.log_error("log_to_history", e)

    def set_class(self, selected_class):
        self.current_class = selected_class
        # Find the class data by description
        for class_key, class_data in self.classes_db.items():
            if class_data["description"] == selected_class:
                self.current_class_id = class_data["id"]
                self.current_spec = class_data["spec"]
                break
        self.save_config()
        self.update_class_icon()
        self.update_queue.put(("ui_refresh", None))

    def update_class_icon(self):
        icon_path = ""
        for class_key, class_data in self.classes_db.items():
            if class_data["description"] == self.current_class:
                icon_path = class_data.get("icon", "")
                break
        if icon_path and os.path.exists(os.path.join(DATA_FOLDER, icon_path)):
            try:
                img = Image.open(os.path.join(DATA_FOLDER, icon_path))
                img = img.resize((100, 100), Image.Resampling.LANCZOS)
                ctk_img = ctk.CTkImage(light_image=img, dark_image=img, size=(100, 100))
                self.class_icon_label.configure(image=ctk_img, text="")
            except Exception as e:
                self.log_error("update_class_icon", e)
                self.class_icon_label.configure(image="", text="")
        else:
            self.class_icon_label.configure(image="", text="")


    def get_item_data(self, item_name):
        item_name = item_name.lower()
        if item_name in self.items_by_name:
            uid = self.items_by_name[item_name][0]
            return self.item_db.get(uid, {})
        if item_name in self.item_db:
            return self.item_db.get(item_name, {})
        return {}

    def toggle_selector(self):
        self.selector = ctk.CTkToplevel(self)
        self.selector.title("Scan Area Selector")
        self.selector.attributes("-alpha", 0.6, "-topmost", True) 
        self.selector.configure(fg_color="#3498db") 
        self.selector.geometry(f"{self.scan_region['width']}x{self.scan_region['height']}+{self.scan_region['left']}+{self.scan_region['top']}")
        ctk.CTkLabel(self.selector, text="DRAG & RESIZE OVER LOOT FEED", text_color="white", font=(self.current_font_family, 12, "bold")).pack(pady=10)
        ctk.CTkButton(self.selector, text="LOCK AREA", fg_color="#2ecc71", font=(self.current_font_family, 12, "bold"), command=self.lock_region).pack(expand=True)

    def lock_region(self):
        self.scan_region = {"top": self.selector.winfo_y(), "left": self.selector.winfo_x(), "width": self.selector.winfo_width(), "height": self.selector.winfo_height()}
        self.save_config()
        self.selector.destroy()

    def setup_boss_timer(self):
        # Load boss times from JSON file
        region_boss_data = self.load_json(BOSS_TIMES_FILE)
        
        # Get current day of week (using local time)
        current_day = datetime.datetime.now().strftime("%A")
        
        # Get today's schedule for the selected region
        if region_boss_data and self.boss_region in region_boss_data:
            self.boss_data = region_boss_data[self.boss_region].get(current_day, [])
        else:
            self.boss_data = []
        
    #    print(f"[DEBUG] Region: {self.boss_region}, Day: {current_day}, Boss entries: {len(self.boss_data)}")
        
        # Sort boss entries by spawn time
        now = datetime.datetime.now()
        def get_spawn_time(entry):
            spawn_dt = datetime.datetime.strptime(now.strftime("%Y-%m-%d") + " " + entry["time"], "%Y-%m-%d %H:%M")
            if spawn_dt < now:
                spawn_dt += datetime.timedelta(days=1)
            return spawn_dt
        
        self.boss_data.sort(key=get_spawn_time)
        
        # Clear existing labels
        for widget in self.boss_scroll_frame.winfo_children():
            widget.destroy()
        self.boss_labels = {}
        
        for boss_entry in self.boss_data:
            boss_frame = ctk.CTkFrame(self.boss_scroll_frame, fg_color="#1a1a1a", corner_radius=5)
            boss_frame.pack(fill="x", pady=3)
            
            # Display boss names on the left (green)
            boss_names = ", ".join(boss_entry["bosses"])
        #    print(f"[DEBUG] Time: {boss_entry['time']}, Bosses: {boss_names}")
            name_label = ctk.CTkLabel(boss_frame, text=boss_names, font=(self.current_font_family, 12, "bold"), text_color="#00ff88", anchor="w")
            name_label.pack(side="left", padx=10, pady=5)
            
            # Display time on the right (gray)
            time_label = ctk.CTkLabel(boss_frame, text=boss_entry["time"], font=(self.current_font_family, 11), text_color="#bdc3c7", anchor="e")
            time_label.pack(side="right", padx=10, pady=5)
            
            # Store label for updates (use time as key)
            self.boss_labels[boss_entry["time"]] = time_label
        
        self.update_boss_timer()

    def update_boss_timer(self):
        now = datetime.datetime.now()
        current_time = now.strftime("%H:%M")
        
        # Track which bosses are spawning soon for sound notifications
        self.boss_spawn_times = {}
        
        for slot in self.boss_data:
            spawn_time = slot["time"]
            # Parse spawn time using today's date (local time)
            spawn_dt = datetime.datetime.strptime(now.strftime("%Y-%m-%d") + " " + spawn_time, "%Y-%m-%d %H:%M")
            
            # If spawn time has passed today, show it for tomorrow
            if spawn_dt < now:
                spawn_dt += datetime.timedelta(days=1)
            
            diff = (spawn_dt - now).total_seconds()
            
            # Store spawn time for each boss in this slot
            for boss_name in slot["bosses"]:
                self.boss_spawn_times[boss_name] = diff
            
            # Update the label with countdown
            hours = int(diff // 3600)
            minutes = int((diff % 3600) // 60)
            seconds = int(diff % 60)
            if hours > 0:
                time_str = f"{hours}h {minutes}m {seconds}s"
            else:
                time_str = f"{minutes}m {seconds}s"
            self.boss_labels[spawn_time].configure(text=time_str)
        
        # Check for sound notifications
        self.check_sound_notifications()
        
        # Export boss timer data for OBS
        self.export_boss_timer_json()
        
        self.after(1000, self.update_boss_timer)
    
    def export_boss_timer_json(self):
        """Export current boss timer data to JSON for OBS overlay"""
        try:
            if not hasattr(self, 'boss_spawn_times'):
                return
            
            # Find the next boss to spawn
            next_boss = None
            next_time = None
            min_seconds = float('inf')
            
            for boss_name, seconds in self.boss_spawn_times.items():
                if seconds < min_seconds:
                    min_seconds = seconds
                    next_boss = boss_name
                    next_time = seconds
            
            if next_boss is None:
                return
            
            # Calculate countdown string
            hours = int(min_seconds // 3600)
            minutes = int((min_seconds % 3600) // 60)
            seconds = int(min_seconds % 60)
            if hours > 0:
                countdown = f"{hours}h {minutes}m {seconds}s"
            else:
                countdown = f"{minutes}m {seconds}s"
            
            # Create export data
            export_data = {
                "next_boss": next_boss,
                "countdown": countdown,
                "seconds_remaining": int(min_seconds),
                "region": self.boss_region,
                "last_updated": datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            }
            
            # Export to JSON file
            boss_timer_export_file = os.path.join(DATA_FOLDER, "bosstimer.json")
            with open(boss_timer_export_file, 'w', encoding='utf-8') as f:
                json.dump(export_data, f, indent=4)
        except Exception as e:
            self.log_error("export_boss_timer_json", e)

    def check_sound_notifications(self):
        """Check if any boss spawn times match the configured sound notification intervals"""
        if not hasattr(self, 'boss_spawn_times'):
            return
            
        notification_times = {
            "30min": 30 * 60,
            "15min": 15 * 60,
            "10min": 10 * 60,
            "5min": 5 * 60,
            "3min": 3 * 60,
            "1min": 1 * 60,
            "spawn": 0
        }
        
        current_minute = int(time.time())
        
        for boss_name, seconds_until_spawn in self.boss_spawn_times.items():
            for notification_key, threshold_seconds in notification_times.items():
                if self.sound_notifications.get(notification_key, False):
                    # Check if we're within the notification window (within 1 second of the threshold)
                    if abs(seconds_until_spawn - threshold_seconds) < 1:
                        # Play sound only once per notification per boss
                        notification_key_full = f"{boss_name}_{notification_key}"
                        if not hasattr(self, '_last_notifications'):
                            self._last_notifications = {}
                        
                        if notification_key_full not in self._last_notifications or (current_minute - self._last_notifications[notification_key_full]) >= 60:
                            try:
                                self.play_boss_sound(notification_key)
                                self._last_notifications[notification_key_full] = current_minute
                            except Exception as e:
                                self.log_error("sound_notification", e)
    
    def play_boss_sound(self, notification_key):
        """Play custom sound file for boss notification"""
        # Map notification keys to actual file names
        file_map = {
            "30min": "30",
            "15min": "15",
            "10min": "10",
            "5min": "5",
            "3min": "3",
            "1min": "1",
            "spawn": "spawn"
        }
        
        filename = file_map.get(notification_key, notification_key)
        sound_file = os.path.join(SOUNDS_FOLDER, f"{filename}.mp3")
        
        # Try .mp3 first, then .wav if mp3 doesn't exist
        if not os.path.exists(sound_file):
            sound_file = os.path.join(SOUNDS_FOLDER, f"{filename}.wav")
        
        if os.path.exists(sound_file):
            try:
                pygame.mixer.music.load(sound_file)
                pygame.mixer.music.set_volume(self.sound_volume)
                pygame.mixer.music.play()
            except Exception as e:
                self.log_error("play_boss_sound", e)
              #  print(f"[ERROR] Failed to play sound file: {sound_file}")
        else:
            print(f"[WARNING] Sound file not found: {sound_file}")

    def snap_to_standard_size(self):
        self.scan_region["width"] = 357
        self.scan_region["height"] = 315
        self.save_config()
        self.update_queue.put(("sync_status", "Dimensions set to 357x315"))
        if hasattr(self, 'selector') and self.selector.winfo_exists():
            self.selector.geometry(f"357x315+{self.selector.winfo_x()}+{self.selector.winfo_y()}")

    def detect_zone(self, item_name):
        item_name = item_name.lower()
        for zone, info in self.locations_db.items():
            sigs = [s.lower() for s in info.get("signatures", [])]
            if item_name in sigs:
                if self.current_zone != zone:
                    self.current_zone = zone
                    pool = set()
                    zone_items = self.items_by_location.get(zone.lower(), [])
                    for item in zone_items:
                        pool.add(item.lower())
                    global_items = self.items_by_location.get("global", [])
                    for item in global_items:
                        pool.add(item.lower())
                    self.active_pool = list(pool)
                return True
        return False

if __name__ == "__main__":
    app = LootTrackerApp()
    app.mainloop()