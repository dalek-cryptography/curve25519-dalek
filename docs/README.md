# Dalek-Lite Verification Website

This directory contains the static website for tracking Verus verification progress of the curve25519-dalek library.

## Structure

```
docs/
├── index.html          # Main website page
├── styles.css          # Styling
├── script.js           # Interactive features
├── outputs/            # Generated plot images
│   ├── overall_progress.png
│   ├── progress_over_time.png
│   ├── verification_funnel.png
│   └── ... (other plots)
└── README.md          # This file
```

## Viewing Locally

To view the website locally:

```bash
cd docs
python -m http.server 8000
# Open http://localhost:8000 in your browser
```

Or use any other static file server.

## Updating the Website

The website displays auto-generated plots from the verification analysis. To update:

```bash
# From the repo root
./scripts/update_website.py
```

This will:
1. Run the Verus analysis on all tracked functions
2. Generate snapshot plots (current state)
3. Generate temporal plots (progress over time)
4. Copy all plots to `docs/outputs/`

## Deploying to GitHub Pages

1. **Enable GitHub Pages** in your repository settings:
   - Go to Settings > Pages
   - Source: Deploy from a branch
   - Branch: `main` (or your default branch)
   - Folder: `/docs`
   - Click Save

2. **Commit and push** the docs directory:
   ```bash
   git add docs/
   git commit -m "Update verification website"
   git push
   ```

3. **Access your site** at:
   ```
   https://beneficial-ai-foundation.github.io/dalek-lite/
   ```
   (Or your organization/username URL)

## Automatic Updates

You can set up a GitHub Action to automatically update the website on every push:

```yaml
# .github/workflows/update-website.yml
name: Update Website

on:
  push:
    branches: [ main ]
  schedule:
    - cron: '0 0 * * *'  # Daily at midnight

jobs:
  update:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Install Rust
        uses: actions-rust-lang/setup-rust-toolchain@v1
      - name: Install Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.11'
      - name: Install uv
        run: pip install uv
      - name: Update website
        run: ./scripts/update_website.py
      - name: Commit changes
        run: |
          git config user.name "GitHub Actions"
          git config user.email "actions@github.com"
          git add docs/outputs/
          git diff --quiet && git diff --staged --quiet || git commit -m "Auto-update website plots"
          git push
```

## Customization

- **Update stats**: Edit the numbers in `index.html` (currently hardcoded, could be made dynamic)
- **Change styling**: Modify `styles.css`
- **Add interactivity**: Extend `script.js`
- **Add sections**: Edit `index.html` structure

## Features

- 📊 **8 different visualizations** of verification progress
- 📈 **Temporal tracking** showing progress over time
- 🎨 **Modern, responsive design** that works on all devices
- 🔄 **Auto-updating charts** from git history
- 📱 **Mobile-friendly** navigation and layout
- 🌙 **Professional styling** with smooth animations

## Technologies Used

- Pure HTML/CSS/JavaScript (no frameworks needed)
- Google Fonts (Inter)
- Responsive CSS Grid and Flexbox
- Intersection Observer API for animations
- Python scripts for data generation

