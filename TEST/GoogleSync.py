import json
import os
import urllib.request
import csv
import sys

# --- CONFIG ---
SHEET_CSV_URL = "https://docs.google.com/spreadsheets/d/e/2PACX-1vT0-ltwF8Sm_wDzYtOm6NFrJTq2JunlUnpDRJCY5iprLXXcE0_SOq1calIm8XWXvOaiwG9vQIdWv3v3/pub?gid=2130357199&single=true&output=csv"

# ================== PORTABLE PATH LOGIC ==================
if getattr(sys, 'frozen', False):
    APPLICATION_PATH = os.path.dirname(sys.executable)
else:
    APPLICATION_PATH = os.path.dirname(os.path.abspath(__file__))

DATA_FOLDER = os.path.join(APPLICATION_PATH, "BDO_Data")
ITEM_FILE = os.path.join(DATA_FOLDER, "local_items.json")
LOC_FILE = os.path.join(DATA_FOLDER, "locations.json")

def sync_from_sheet():
    print("--- Starting Master Sync: Google Sheets -> Local JSON ---")
    print(f"Target Folder: {DATA_FOLDER}")
    
    try:
        response = urllib.request.urlopen(SHEET_CSV_URL)
        lines = [line.decode('utf-8') for line in response.readlines()]
        
        reader = csv.reader(lines)
        header = next(reader) 
        
        new_items = {}
        new_locs = {}

        for cols in reader:
            if len(cols) < 7: continue
            
            name = cols[0].strip().lower()
            item_id = cols[1].strip()
            
            m_price = cols[2].strip().replace(',', '')
            v_price = cols[3].strip().replace(',', '')
            
            try:
                price = int(m_price) if m_price and m_price != '0' else int(v_price or 0)
            except ValueError:
                price = 0
                
            category = cols[4].strip()
            location_val = cols[5].strip()
            icon_url = cols[6].strip()

            new_items[name] = {
                "id": item_id,
                "price": price,
                "category": category,
                "location": location_val,
                "icon": icon_url
            }

            if category.lower() == "trash":
                loc_list = [l.strip() for l in location_val.split(',')]
                for loc in loc_list:
                    if loc not in new_locs:
                        new_locs[loc] = {
                            "signatures": [], 
                            "description": f"Grind Zone: {loc}"
                        }
                    if name not in new_locs[loc]["signatures"]:
                        new_locs[loc]["signatures"].append(name)

        os.makedirs(DATA_FOLDER, exist_ok=True)
        
        with open(ITEM_FILE, 'w', encoding='utf-8') as f:
            json.dump(new_items, f, indent=4)
        
        with open(LOC_FILE, 'w', encoding='utf-8') as f:
            json.dump(new_locs, f, indent=4)

        print(f"SUCCESS: Synced {len(new_items)} items.")
        print(f"Locations defined: {list(new_locs.keys())}")

    except Exception as e:
        print(f"FAILED: Error processing sheet. {e}")

    input("\nPress Enter to close...")

if __name__ == "__main__":
    sync_from_sheet()