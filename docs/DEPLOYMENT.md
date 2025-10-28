# Website Deployment Guide

## Quick Start

The website is now ready to deploy! Here's what we've created:

### ✨ Features

- **8 Interactive Visualizations** showing verification progress
- **Responsive Design** that works on all devices
- **Automatic Data Updates** from git history
- **Modern UI** with smooth animations
- **Complete Documentation** of the project

### 📁 Structure

```
docs/
├── index.html              # Main website
├── styles.css              # Styling
├── script.js               # Interactive features
├── _config.yml            # GitHub Pages config
├── outputs/               # Auto-generated charts
│   ├── progress_over_time.png
│   ├── verification_funnel.png
│   ├── overall_progress.png
│   ├── verus_breakdown.png
│   ├── absolute_counts_over_time.png
│   ├── module_breakdown.png
│   ├── verification_velocity.png
│   └── comparison_pie.png
└── README.md              # Documentation
```

## View Locally

The website is currently running at:
```
http://localhost:8000
```

To restart the server:
```bash
cd docs
python3 -m http.server 8000
```

## Deploy to GitHub Pages

### Step 1: Enable GitHub Pages

1. Go to your repository on GitHub
2. Navigate to **Settings** → **Pages**
3. Under "Source":
   - Branch: `main` (or your default branch)
   - Folder: `/docs`
4. Click **Save**

### Step 2: Commit and Push

```bash
# Add all website files
git add docs/

# Commit
git commit -m "Add verification progress website"

# Push to GitHub
git push origin main
```

### Step 3: Access Your Site

Your website will be available at:
```
https://beneficial-ai-foundation.github.io/dalek-lite/
```

GitHub Pages typically takes 1-2 minutes to build and deploy.

## Update the Website

Whenever you want to update the charts with latest data:

```bash
# From repo root
./scripts/update_website.py

# Commit and push
git add docs/outputs/
git commit -m "Update verification progress charts"
git push
```

## Automate Updates with GitHub Actions

Create `.github/workflows/update-website.yml`:

```yaml
name: Update Website

on:
  push:
    branches: [ main ]
    paths:
      - 'curve25519-dalek/src/**'
      - 'outputs/curve25519_functions.csv'
  schedule:
    # Run daily at 00:00 UTC
    - cron: '0 0 * * *'

jobs:
  update-website:
    runs-on: ubuntu-latest
    
    steps:
      - name: Checkout repository
        uses: actions/checkout@v4
        with:
          fetch-depth: 0  # Full history for temporal analysis
      
      - name: Set up Python
        uses: actions/setup-python@v5
        with:
          python-version: '3.11'
      
      - name: Install uv
        run: pip install uv
      
      - name: Update website
        run: ./scripts/update_website.py
      
      - name: Commit and push if changed
        run: |
          git config user.name "github-actions[bot]"
          git config user.email "github-actions[bot]@users.noreply.github.com"
          git add docs/outputs/
          if git diff --staged --quiet; then
            echo "No changes to commit"
          else
            git commit -m "Auto-update website charts [skip ci]"
            git push
          fi
```

This will automatically update your website whenever:
- You push changes to the source code
- The CSV file is updated
- Once per day (to catch any manual commits)

## Customization

### Update Statistics

Edit the hero section in `index.html`:

```html
<div class="stat-card">
    <div class="stat-number">257</div>  <!-- Update this -->
    <div class="stat-label">Total Functions</div>
</div>
```

You can make this dynamic by parsing the CSV with JavaScript if desired.

### Change Colors

Edit CSS variables in `styles.css`:

```css
:root {
    --primary-color: #2563eb;      /* Change primary color */
    --secondary-color: #10b981;    /* Change accent color */
    /* ... */
}
```

### Add Content

The website is organized into sections with IDs:
- `#home` - Hero section
- `#progress` - Charts and visualizations
- `#about` - Project information
- `#trust` - Trust model explanation

Add new sections by following the existing structure.

## Troubleshooting

### Charts not showing?

Make sure the images are in `docs/outputs/` and paths in HTML are correct:
```html
<img src="outputs/filename.png" alt="...">
```

### GitHub Pages not updating?

1. Check the Actions tab for build errors
2. Ensure GitHub Pages is enabled in Settings
3. Wait 1-2 minutes after pushing
4. Clear your browser cache

### Styling looks broken?

Check that `styles.css` is in the same directory as `index.html` and linked correctly:
```html
<link rel="stylesheet" href="styles.css">
```

## Next Steps

- [ ] Enable GitHub Pages in repository settings
- [ ] Push the docs directory to GitHub
- [ ] Verify the site works at the GitHub Pages URL
- [ ] Set up the GitHub Action for automatic updates
- [ ] Share the URL with your team!

## Support

For issues or questions:
- Open an issue on GitHub
- Check the [GitHub Pages documentation](https://docs.github.com/en/pages)
- Review the [README.md](README.md) in this directory

