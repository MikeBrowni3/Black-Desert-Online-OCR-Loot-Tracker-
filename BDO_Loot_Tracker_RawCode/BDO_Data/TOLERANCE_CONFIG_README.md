# Tolerance Config Guide

## Purpose
This file controls duplicate detection tolerances for the BDO Loot Tracker. Adjust these values to improve tracking accuracy without changing code.

## Tolerance Format
`[y_tolerance, x_tolerance]` - Maximum pixel distance in Y and X directions to consider an item a duplicate.

## How It Works
When an item is detected, the tracker checks if a similar item was recently detected within these pixel distances. If yes, it's considered a duplicate and not counted again.

## Category Defaults
- **trash**: `[25, 35]` - Loose tolerance for common trash items that appear frequently and may shift position
- **General**: `[15, 25]` - Medium tolerance for general items like black stones
- **rare**: `[12, 18]` - Tight tolerance for rare items to prevent false positives
- **default**: `[12, 18]` - Fallback for items without a category

## Accuracy Tuning Guide

### Overcounting Issue
If you track MORE than you actually loot, **TIGHTEN** the tolerance (reduce numbers). This prevents false duplicates from being counted as separate items.

### Undercounting Issue
If you track LESS than you actually loot, **LOOSEN** the tolerance (increase numbers). This allows more variation in item position before being considered a duplicate.

### Perfect Accuracy
When tracked count matches looted count, the tolerance is optimal for that item.

## Manual Overrides
Use the `_manual_overrides` section to fine-tune specific items. Overrides take precedence over auto-generated values.

```json
"_manual_overrides": {
    "ancient spirit dust": [10, 15],
    "black stone": [12, 18]
}
```

## Testing Workflow
1. Grind for 5-10 minutes and record tracked vs looted counts
2. Identify items with accuracy issues (overcounting or undercounting)
3. For overcounting items: Add to `_manual_overrides` with TIGHTER tolerance (smaller numbers)
4. For undercounting items: Add to `_manual_overrides` with LOOSER tolerance (larger numbers)
5. Test again and iterate until accuracy is 95%+ for all items
6. Share your optimized `_manual_overrides` with the community

## Machine Learning Integration
**Suggested Approach**: Use accuracy data (tracked vs looted) to train a model that predicts optimal tolerances based on item properties (category, price, drop rate, name length, etc.)

**Input Features**: item_category, item_price, drop_frequency, name_complexity, icon_similarity_score

**Output Target**: optimal_y_tolerance, optimal_x_tolerance

**Training Data**: Collect grinding sessions with known ground truth (actual looted counts) to train the model

## Community Collaboration
- Share optimized tolerances: Post your `_manual_overrides` section to forums/discord with your accuracy results
- Regional differences: Note that optimal tolerances may vary by screen resolution, UI scale, and game client version
- Version control: Keep backups of working tolerance configs before experimenting

## Important Notes
- **Item names**: All item names must be lowercase to match the tracker's internal format
- **Tolerance ranges**: Recommended range: y_tolerance [8-40], x_tolerance [12-50]. Values outside this range may cause issues
- **Special cases**: Items with very similar names or icons may need tighter tolerances to prevent misidentification
- **Resolution scaling**: Higher screen resolutions may require proportionally larger tolerances
