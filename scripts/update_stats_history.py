#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# dependencies = [
#   "beartype",
#   "gitpython",
# ]
# ///
"""
Update verification stats history.

This script:
1. Fetches existing stats_history.jsonl (from file or URL)
2. Regenerates missing history from git commits if needed
3. Appends current commit stats
4. Writes updated stats_history.jsonl

Format: JSON Lines (one JSON object per line)
{
  "commit": "abc123...",
  "date": "2025-11-11T12:00:00",
  "total": 213,
  "specs": 50,
  "specs_external": 5,
  "proofs": 30
}
"""

import argparse
import csv
import io
import json
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List

from beartype import beartype
from git import Repo


def get_csv_column_names(first_row: dict) -> tuple[str, str]:
    """
    Get the correct column names for spec and proof columns.
    Supports both old (has_spec_verus) and new (has_spec) column names.

    Returns:
        tuple: (spec_column_name, proof_column_name)
    """
    spec_col = "has_spec" if "has_spec" in first_row else "has_spec_verus"
    proof_col = "has_proof" if "has_proof" in first_row else "has_proof_verus"
    return spec_col, proof_col


@beartype
def read_existing_history(history_file: Path) -> List[Dict]:
    """Read existing stats history from JSONL file."""
    if not history_file.exists():
        return []

    history = []
    with open(history_file, "r", encoding="utf-8") as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if line:
                try:
                    history.append(json.loads(line))
                except json.JSONDecodeError as e:
                    print(f"Warning: Skipping malformed JSON at line {line_num}: {e}")
                    continue
    return history


@beartype
def get_current_stats(csv_file: Path) -> Dict[str, int]:
    """Extract stats from current CSV file."""
    if not csv_file.exists():
        raise FileNotFoundError(f"CSV file not found: {csv_file}")

    with open(csv_file, "r", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        rows = list(reader)

    if not rows:
        return {
            "total": 0,
            "specs": 0,
            "specs_external": 0,
            "proofs": 0,
        }

    total = len(rows)
    specs_full = 0
    specs_external = 0
    proofs = 0

    # Support both old and new column names for backward compatibility
    spec_col, proof_col = get_csv_column_names(rows[0])

    for row in rows:
        spec_val = row.get(spec_col, "").strip()
        if spec_val == "yes":
            specs_full += 1
        elif spec_val == "ext":
            specs_external += 1

        if row.get(proof_col, "").strip() == "yes":
            proofs += 1

    return {
        "total": total,
        "specs": specs_full,
        "specs_external": specs_external,
        "proofs": proofs,
    }


@beartype
def analyze_csv_at_commit(
    repo: Repo, commit_hash: str, csv_path: str
) -> Dict[str, int] | None:
    """
    Analyze CSV at a specific commit by retrieving it from git history.
    Returns None if the CSV doesn't exist at that commit.
    """
    try:
        commit = repo.commit(commit_hash)

        # Try to get CSV from git history (old commits)
        try:
            csv_blob = commit.tree / csv_path
            csv_content = csv_blob.data_stream.read().decode("utf-8")
        except KeyError:
            # CSV not in git, skip this commit
            return None

        # Parse CSV
        lines = csv_content.strip().split("\n")
        if len(lines) < 2:
            return None

        reader = csv.DictReader(io.StringIO(csv_content))
        rows = list(reader)

        if not rows:
            return None

        total = len(rows)

        # Support both old and new column names
        spec_col, proof_col = get_csv_column_names(rows[0])

        specs_full = 0
        specs_external = 0
        proofs = 0

        for row in rows:
            spec_val = row.get(spec_col, "").strip()
            if spec_val == "yes":
                specs_full += 1
            elif spec_val == "ext":
                specs_external += 1

            if row.get(proof_col, "").strip() == "yes":
                proofs += 1

        return {
            "total": total,
            "specs": specs_full,
            "specs_external": specs_external,
            "proofs": proofs,
        }

    except Exception as e:
        print(f"  Warning: Could not analyze commit {commit_hash[:8]}: {e}")
        return None


@beartype
def fill_missing_history(
    repo_path: Path,
    existing_history: List[Dict],
    csv_path: str = "outputs/curve25519_functions.csv",
    since_date: str | None = None,
    max_commits: int = 1000,
) -> List[Dict]:
    """
    Fill in missing history by analyzing git commits.
    Only processes commits not already in history.

    Args:
        csv_path: Relative path to CSV file in git history
    """
    repo = Repo(repo_path)

    # Get existing commit hashes
    existing_commits = {entry["commit"] for entry in existing_history}

    # Get commit history
    print(f"Scanning git history (max {max_commits} commits)...")
    try:
        commits = list(repo.iter_commits("main", max_count=max_commits))
    except Exception:
        commits = list(repo.iter_commits(max_count=max_commits))

    new_entries = []
    processed = 0

    for commit in commits:
        commit_hash = commit.hexsha
        commit_date = datetime.fromtimestamp(commit.committed_date, tz=timezone.utc)

        # Filter by date if specified
        if since_date:
            since = datetime.strptime(since_date, "%Y-%m-%d").replace(
                tzinfo=timezone.utc
            )
            if commit_date < since:
                break

        # Skip if already in history
        if commit_hash in existing_commits:
            continue

        processed += 1
        if processed % 10 == 0:
            print(f"  Processed {processed} new commits...")

        # Try to analyze CSV at this commit
        stats = analyze_csv_at_commit(repo, commit_hash, csv_path)

        if stats:
            new_entries.append(
                {
                    "commit": commit_hash,
                    "date": commit_date.isoformat(),
                    "total": stats["total"],
                    "specs": stats["specs"],
                    "specs_external": stats["specs_external"],
                    "proofs": stats["proofs"],
                }
            )

    print(f"Found {len(new_entries)} new commits with data")
    return new_entries


@beartype
def write_history(history: List[Dict], output_file: Path) -> None:
    """Write stats history to JSONL file."""
    # Sort by date
    history_sorted = sorted(history, key=lambda x: x["date"])

    output_file.parent.mkdir(parents=True, exist_ok=True)

    with open(output_file, "w", encoding="utf-8") as f:
        for entry in history_sorted:
            f.write(json.dumps(entry) + "\n")

    print(f"Wrote {len(history_sorted)} entries to {output_file}")


@beartype
def main():
    parser = argparse.ArgumentParser(description="Update verification stats history")
    parser.add_argument(
        "--csv",
        type=Path,
        default=Path("outputs/curve25519_functions.csv"),
        help="Path to current CSV file",
    )
    parser.add_argument(
        "--history",
        type=Path,
        default=Path("outputs/stats_history.jsonl"),
        help="Path to stats history file",
    )
    parser.add_argument(
        "--fetch-url",
        type=str,
        help="URL to fetch existing history from (e.g., deployed website)",
    )
    parser.add_argument(
        "--fill-missing",
        action="store_true",
        help="Fill missing history from git commits",
    )
    parser.add_argument(
        "--since",
        type=str,
        help="Only process commits since this date (YYYY-MM-DD)",
    )
    parser.add_argument(
        "--max-commits",
        type=int,
        default=1000,
        help="Maximum number of commits to scan when filling history",
    )

    args = parser.parse_args()

    repo_path = Path.cwd()

    # Step 1: Read existing history
    existing_history = []

    if args.fetch_url:
        print(f"Fetching history from {args.fetch_url}...")
        try:
            with urllib.request.urlopen(args.fetch_url, timeout=10) as response:
                content = response.read().decode("utf-8")
                for line_num, line in enumerate(content.strip().split("\n"), 1):
                    if line:
                        try:
                            existing_history.append(json.loads(line))
                        except json.JSONDecodeError as e:
                            print(
                                f"  Warning: Skipping malformed JSON at line {line_num}: {e}"
                            )
                            continue
            print(f"  Fetched {len(existing_history)} existing entries")
        except Exception as e:
            print(f"  Warning: Could not fetch from URL: {e}")
            print("  Falling back to local file...")

    # Fallback to local file
    if not existing_history and args.history.exists():
        existing_history = read_existing_history(args.history)
        print(f"Read {len(existing_history)} entries from local file")

    # Step 2: Fill missing history from git if requested
    if args.fill_missing:
        # Convert CSV path to relative path for git history lookup
        csv_relative_path = str(
            args.csv.relative_to(repo_path) if args.csv.is_absolute() else args.csv
        )
        new_entries = fill_missing_history(
            repo_path, existing_history, csv_relative_path, args.since, args.max_commits
        )
        existing_history.extend(new_entries)

    # Step 3: Add current commit
    try:
        repo = Repo(repo_path)
        current_commit = repo.head.commit
        current_hash = current_commit.hexsha
        current_date = datetime.fromtimestamp(
            current_commit.committed_date, tz=timezone.utc
        )

        # Check if current commit already in history
        if not any(e["commit"] == current_hash for e in existing_history):
            print(f"Adding current commit {current_hash[:8]}...")
            current_stats = get_current_stats(args.csv)

            existing_history.append(
                {
                    "commit": current_hash,
                    "date": current_date.isoformat(),
                    "total": current_stats["total"],
                    "specs": current_stats["specs"],
                    "specs_external": current_stats["specs_external"],
                    "proofs": current_stats["proofs"],
                }
            )
            print(f"  Stats: {current_stats}")
        else:
            print(f"Current commit {current_hash[:8]} already in history")

    except Exception as e:
        print(f"Warning: Could not add current commit: {e}")

    # Step 4: Write updated history
    write_history(existing_history, args.history)

    print("\nSummary:")
    print(f"  Total entries: {len(existing_history)}")
    if existing_history:
        dates = [e["date"] for e in existing_history]
        print(f"  Date range: {min(dates)} to {max(dates)}")


if __name__ == "__main__":
    main()
