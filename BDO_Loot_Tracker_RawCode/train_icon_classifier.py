"""
MobileNetV3 Training Script for BDO Drop Icon Classifier
Trains on drop_icons folder and exports to ONNX format
"""
import os
import json
import torch
import torch.nn as nn
import torch.optim as optim
from torch.utils.data import Dataset, DataLoader
from torchvision import models, transforms
from PIL import Image
import cv2
import numpy as np
import requests
from io import BytesIO
import time

# ================== CONFIGURATION ==================
DATA_FOLDER = "BDO_Data"
DROPS_ICONS_FOLDER = os.path.join(DATA_FOLDER, "drop_icons")
ITEM_DB_FILE = os.path.join(DATA_FOLDER, "local_items.json")
MODEL_OUTPUT_PATH = os.path.join(DATA_FOLDER, "icon_classifier.pth")
ONNX_OUTPUT_PATH = os.path.join(DATA_FOLDER, "icon_classifier.onnx")

# Training parameters
BATCH_SIZE = 16
EPOCHS = 20
LEARNING_RATE = 0.001
IMAGE_SIZE = 64  # Input size for MobileNetV3

# ================== ICON DOWNLOADER ==================
def download_new_icons():
    """Download icons for new items only (doesn't overwrite existing files)"""
    print("=" * 60)
    print("Downloading New Icons")
    print("=" * 60)
    
    # Create output directory if it doesn't exist
    os.makedirs(DROPS_ICONS_FOLDER, exist_ok=True)
    
    # Read the JSON file
    with open(ITEM_DB_FILE, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    # Headers to mimic browser request
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'
    }
    
    # Track processed IDs to avoid duplicates
    processed_ids = set()
    new_downloads = 0
    skipped = 0
    errors = 0
    
    # Iterate through each item
    for key, item in data.items():
        item_id = item.get('id')
        icon_url = item.get('icon')
        
        if not item_id or not icon_url:
            continue
        
        # Skip if we've already processed this ID
        if item_id in processed_ids:
            continue
        
        processed_ids.add(item_id)
        
        # Check if file already exists
        output_path = os.path.join(DROPS_ICONS_FOLDER, f"{item_id}.png")
        if os.path.exists(output_path):
            skipped += 1
            continue
        
        try:
            # Download the image with headers
            response = requests.get(icon_url, headers=headers, timeout=10)
            response.raise_for_status()
            
            # Open the image from bytes
            img = Image.open(BytesIO(response.content))
            
            # Convert to RGB if necessary (for RGBA images)
            if img.mode in ('RGBA', 'LA', 'P'):
                img = img.convert('RGB')
            
            # Save as PNG with the ID as filename
            img.save(output_path, 'PNG')
            
            new_downloads += 1
            print(f"   Downloaded: {item_id}.png")
            
            # Small delay to avoid rate limiting
            time.sleep(0.1)
            
        except Exception as e:
            errors += 1
            print(f"   Error processing {item_id}: {e}")
    
    print(f"\n[Icon Downloader] New downloads: {new_downloads}, Skipped existing: {skipped}, Errors: {errors}")
    print(f"[Icon Downloader] Total icons in folder: {len(os.listdir(DROPS_ICONS_FOLDER))}")
    print()

# ================== DATASET LOADER ==================
class IconDataset(Dataset):
    def __init__(self, drop_icons_folder, item_db, transform=None):
        self.drop_icons_folder = drop_icons_folder
        self.item_db = item_db
        self.transform = transform
        self.samples = []
        self.class_to_idx = {}
        self.idx_to_class = {}
        
        # Build mapping from icon IDs to class indices
        self._build_dataset()
    
    def _build_dataset(self):
        """Map icon files to class indices"""
        class_idx = 0
        
        for uid, data in self.item_db.items():
            if isinstance(data, dict):
                item_id = str(data.get("id", "")).replace(",", "").strip()
                item_name = data.get("name", "").lower()
                
                if item_id and item_name:
                    icon_path = os.path.join(self.drop_icons_folder, f"{item_id}.png")
                    
                    if os.path.exists(icon_path):
                        # Assign class index if not already assigned
                        if item_name not in self.class_to_idx:
                            self.class_to_idx[item_name] = class_idx
                            self.idx_to_class[class_idx] = item_name
                            class_idx += 1
                        
                        self.samples.append({
                            'path': icon_path,
                            'label': self.class_to_idx[item_name],
                            'item_name': item_name
                        })
        
        print(f"[Dataset] Loaded {len(self.samples)} samples across {len(self.class_to_idx)} classes")
    
    def __len__(self):
        return len(self.samples)
    
    def __getitem__(self, idx):
        sample = self.samples[idx]
        
        # Load image
        image = Image.open(sample['path']).convert('RGB')
        
        if self.transform:
            image = self.transform(image)
        
        return image, sample['label']

# ================== TRAINING ==================
def train_model():
    print("=" * 60)
    print("MobileNetV3 Icon Classifier Training")
    print("=" * 60)
    
    # Load item database
    print("\n[1/5] Loading item database...")
    with open(ITEM_DB_FILE, 'r', encoding='utf-8') as f:
        item_db = json.load(f)
    
    # Data augmentation and normalization
    train_transform = transforms.Compose([
        transforms.Resize((IMAGE_SIZE, IMAGE_SIZE)),
        transforms.RandomHorizontalFlip(),
        transforms.RandomRotation(10),
        transforms.ColorJitter(brightness=0.2, contrast=0.2),
        transforms.ToTensor(),
        transforms.Normalize([0.485, 0.456, 0.406], [0.229, 0.224, 0.225])
    ])
    
    # Create dataset
    print("[2/5] Creating dataset...")
    dataset = IconDataset(DROPS_ICONS_FOLDER, item_db, transform=train_transform)
    
    if len(dataset) == 0:
        print("[ERROR] No training data found! Ensure drop_icons folder has PNG files.")
        return
    
    # Split into train/validation (80/20)
    train_size = int(0.8 * len(dataset))
    val_size = len(dataset) - train_size
    train_dataset, val_dataset = torch.utils.data.random_split(dataset, [train_size, val_size])
    
    train_loader = DataLoader(train_dataset, batch_size=BATCH_SIZE, shuffle=True)
    val_loader = DataLoader(val_dataset, batch_size=BATCH_SIZE, shuffle=False)
    
    num_classes = len(dataset.class_to_idx)
    print(f"   Classes: {num_classes}")
    print(f"   Train samples: {train_size}")
    print(f"   Val samples: {val_size}")
    
    # Save class mapping for inference
    class_mapping = {
        'class_to_idx': dataset.class_to_idx,
        'idx_to_class': dataset.idx_to_class
    }
    with open(os.path.join(DATA_FOLDER, "class_mapping.json"), 'w') as f:
        json.dump(class_mapping, f, indent=4)
    print(f"   Saved class mapping to class_mapping.json")
    
    # Load MobileNetV3 Small
    print("[3/5] Initializing MobileNetV3-Small...")
    model = models.mobilenet_v3_small(pretrained=True)
    
    # Modify classifier for our number of classes
    model.classifier[3] = nn.Linear(model.classifier[3].in_features, num_classes)
    
    # Move to GPU if available
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model = model.to(device)
    print(f"   Using device: {device}")
    
    # Loss and optimizer
    criterion = nn.CrossEntropyLoss()
    optimizer = optim.Adam(model.parameters(), lr=LEARNING_RATE)
    
    # Training loop
    print("[4/5] Training...")
    best_val_acc = 0.0
    
    for epoch in range(EPOCHS):
        model.train()
        train_loss = 0.0
        train_correct = 0
        train_total = 0
        
        for images, labels in train_loader:
            images, labels = images.to(device), labels.to(device)
            
            optimizer.zero_grad()
            outputs = model(images)
            loss = criterion(outputs, labels)
            loss.backward()
            optimizer.step()
            
            train_loss += loss.item()
            _, predicted = outputs.max(1)
            train_total += labels.size(0)
            train_correct += predicted.eq(labels).sum().item()
        
        # Validation
        model.eval()
        val_loss = 0.0
        val_correct = 0
        val_total = 0
        
        with torch.no_grad():
            for images, labels in val_loader:
                images, labels = images.to(device), labels.to(device)
                outputs = model(images)
                loss = criterion(outputs, labels)
                
                val_loss += loss.item()
                _, predicted = outputs.max(1)
                val_total += labels.size(0)
                val_correct += predicted.eq(labels).sum().item()
        
        train_acc = 100. * train_correct / train_total
        val_acc = 100. * val_correct / val_total
        
        print(f"   Epoch {epoch+1}/{EPOCHS} - "
              f"Train Loss: {train_loss/len(train_loader):.4f}, Acc: {train_acc:.2f}% | "
              f"Val Loss: {val_loss/len(val_loader):.4f}, Acc: {val_acc:.2f}%")
        
        # Save best model
        if val_acc > best_val_acc:
            best_val_acc = val_acc
            torch.save(model.state_dict(), MODEL_OUTPUT_PATH)
            print(f"   Saved best model (val_acc: {val_acc:.2f}%)")
    
    # Load best model for export
    print("[5/5] Exporting to ONNX...")
    model.load_state_dict(torch.load(MODEL_OUTPUT_PATH))
    model.eval()
    
    # Create dummy input
    dummy_input = torch.randn(1, 3, IMAGE_SIZE, IMAGE_SIZE).to(device)
    
    # Export to ONNX
    torch.onnx.export(
        model,
        dummy_input,
        ONNX_OUTPUT_PATH,
        export_params=True,
        opset_version=11,
        input_names=['input'],
        output_names=['output'],
        dynamic_axes={
            'input': {0: 'batch_size'},
            'output': {0: 'batch_size'}
        }
    )
    
    print(f"   Saved PyTorch model to {MODEL_OUTPUT_PATH}")
    print(f"   Saved ONNX model to {ONNX_OUTPUT_PATH}")
    print("\n" + "=" * 60)
    print("Training complete!")
    print("=" * 60)

if __name__ == "__main__":
    # Download new icons first
    download_new_icons()
    # Then train the model
    train_model()
