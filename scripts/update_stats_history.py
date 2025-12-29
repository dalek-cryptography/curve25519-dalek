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
import logging
import ssl
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List

from beartype import beartype
from git import Repo
from git.exc import GitCommandError

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format="%(message)s",
)
logger = logging.getLogger(__name__)

# Default validation thresholds (can be overridden via CLI)
DEFAULT_MIN_EXPECTED_ENTRIES = 100  # Minimum entries we expect in history
DEFAULT_MAX_GAP_DAYS = 14  # Maximum days between entries before flagging as corrupted


@beartype
def validate_fetched_history(
    history: List[Dict],
    local_history: List[Dict],
    min_entries: int = DEFAULT_MIN_EXPECTED_ENTRIES,
    max_gap_days: int = DEFAULT_MAX_GAP_DAYS,
) -> bool:
    """
    Validate fetched history to detect corruption or data loss.

    Returns True if history looks valid, False if it appears corrupted.
    """
    if not history:
        logger.error("  Validation FAILED: Empty history")
        return False

    # Check minimum entries
    if len(history) < min_entries:
        logger.info(
            f"  Validation WARNING: Only {len(history)} entries (expected >= {min_entries})"
        )
        # Don't fail yet, check other criteria

    # Sort by parsed datetime
    sorted_history = sorted(history, key=lambda x: datetime.fromisoformat(x["date"]))

    # Check for big gaps in dates
    gaps_found = []
    for i in range(1, len(sorted_history)):
        prev_date = datetime.fromisoformat(sorted_history[i - 1]["date"])
        curr_date = datetime.fromisoformat(sorted_history[i]["date"])
        gap_days = (curr_date - prev_date).days
        if gap_days > max_gap_days:
            gaps_found.append(
                (
                    sorted_history[i - 1]["date"][:10],
                    sorted_history[i]["date"][:10],
                    gap_days,
                )
            )

    if gaps_found:
        logger.info(
            f"  Validation WARNING: Found {len(gaps_found)} gap(s) > {max_gap_days} days:"
        )
        for start, end, days in gaps_found[:3]:  # Show first 3
            logger.warning(f"    {start} -> {end} ({days} days)")

    # Check if local history has more entries (indicates data loss in fetched)
    if local_history and len(local_history) > len(history):
        logger.info(
            f"  Validation WARNING: Local history has more entries ({len(local_history)}) than fetched ({len(history)})"
        )
        # This is a strong indicator of data loss
        return False

    # Check if fetched history is missing recent dates that local has
    if local_history:
        local_dates = {e["date"][:10] for e in local_history}
        fetched_dates = {e["date"][:10] for e in history}
        missing_dates = local_dates - fetched_dates
        if len(missing_dates) > 5:  # More than 5 dates missing
            logger.warning(
                f"  Fetched history missing {len(missing_dates)} dates present in local"
            )
            return False

    # If we have significant gaps but local history is smaller or empty,
    # we might still want to use fetched (it's better than nothing)
    if gaps_found and len(gaps_found) > 2:
        logger.error("  Validation FAILED: Too many gaps in fetched history")
        return False

    logger.info(f"  Validation PASSED: {len(history)} entries, data looks consistent")
    return True


@beartype
def merge_histories(local: List[Dict], fetched: List[Dict]) -> List[Dict]:
    """
    Merge local and fetched histories, keeping all unique entries.
    This ensures we don't lose data from either source.
    """
    seen_commits = set()
    merged = []

    # Add all entries, deduplicating by commit hash
    for entry in local + fetched:
        commit = entry["commit"]
        if commit not in seen_commits:
            seen_commits.add(commit)
            merged.append(entry)

    # Sort by parsed datetime
    merged.sort(key=lambda x: datetime.fromisoformat(x["date"]))
    return merged


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
                    logger.warning(f" Skipping malformed JSON at line {line_num}: {e}")
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
        logger.warning(f"   Could not analyze commit {commit_hash[:8]}: {e}")
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
    logger.info(f"Scanning git history (max {max_commits} commits)...")
    try:
        commits = list(repo.iter_commits("main", max_count=max_commits))
    except GitCommandError:
        # "main" branch doesn't exist, try current branch
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
            logger.info(f"  Processed {processed} new commits...")

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

    logger.info(f"Found {len(new_entries)} new commits with data")
    return new_entries


@beartype
def write_history(history: List[Dict], output_file: Path) -> None:
    """Write stats history to JSONL file."""
    # Sort by parsed datetime
    history_sorted = sorted(history, key=lambda x: datetime.fromisoformat(x["date"]))

    output_file.parent.mkdir(parents=True, exist_ok=True)

    with open(output_file, "w", encoding="utf-8") as f:
        for entry in history_sorted:
            f.write(json.dumps(entry) + "\n")

    logger.info(f"Wrote {len(history_sorted)} entries to {output_file}")


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
    parser.add_argument(
        "--min-entries",
        type=int,
        default=DEFAULT_MIN_EXPECTED_ENTRIES,
        help=f"Minimum expected history entries for validation to pass (default: {DEFAULT_MIN_EXPECTED_ENTRIES})",
    )
    parser.add_argument(
        "--max-gap-days",
        type=int,
        default=DEFAULT_MAX_GAP_DAYS,
        help=f"Maximum allowed gap in days between entries before flagging as corrupted (default: {DEFAULT_MAX_GAP_DAYS})",
    )

    args = parser.parse_args()

    repo_path = Path.cwd()

    # Step 1: Read existing history
    existing_history = []
    local_history = []

    # Always read local file first (for validation comparison)
    if args.history.exists():
        local_history = read_existing_history(args.history)
        logger.info(f"Read {len(local_history)} entries from local file")

    if args.fetch_url:
        logger.info(f"Fetching history from {args.fetch_url}...")
        fetched_history = []
        try:
            # Create SSL context (some environments need this)
            ssl_context = ssl.create_default_context()
            with urllib.request.urlopen(
                args.fetch_url, timeout=10, context=ssl_context
            ) as response:
                content = response.read().decode("utf-8")
                for line_num, line in enumerate(content.strip().splitlines(), 1):
                    if line:
                        try:
                            fetched_history.append(json.loads(line))
                        except json.JSONDecodeError as e:
                            logger.warning(
                                f"  Skipping malformed JSON at line {line_num}: {e}"
                            )
                            continue
            logger.info(f"  Fetched {len(fetched_history)} entries from URL")

            # Validate fetched history
            if validate_fetched_history(
                fetched_history, local_history, args.min_entries, args.max_gap_days
            ):
                existing_history = fetched_history
            else:
                logger.warning(
                    "  Fetched history failed validation, merging with local file..."
                )
                # Merge both histories to avoid losing data from either source
                existing_history = merge_histories(local_history, fetched_history)
                logger.info(f"  Merged history: {len(existing_history)} entries")

        except Exception as e:
            logger.warning(f"  Could not fetch from URL: {e}")
            logger.info("  Falling back to local file...")
            existing_history = local_history
    else:
        # No fetch URL, use local file
        existing_history = local_history

    # Step 2: Fill missing history from git if requested
    if args.fill_missing:
        # Convert CSV path to relative path for git history lookup
        try:
            csv_relative_path = str(
                args.csv.relative_to(repo_path) if args.csv.is_absolute() else args.csv
            )
        except ValueError:
            # CSV is outside repo - can't look it up in git history
            logger.warning(
                f"CSV path {args.csv} is outside repository, skipping git history fill"
            )
            csv_relative_path = None

        if csv_relative_path:
            new_entries = fill_missing_history(
                repo_path,
                existing_history,
                csv_relative_path,
                args.since,
                args.max_commits,
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
            logger.info(f"Adding current commit {current_hash[:8]}...")
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
            logger.info(f"  Stats: {current_stats}")
        else:
            logger.info(f"Current commit {current_hash[:8]} already in history")

    except Exception as e:
        logger.warning(f" Could not add current commit: {e}")

    # Step 4: Write updated history
    write_history(existing_history, args.history)

    logger.info("\nSummary:")
    logger.info(f"  Total entries: {len(existing_history)}")
    if existing_history:
        parsed_dates = [datetime.fromisoformat(e["date"]) for e in existing_history]
        logger.info(
            f"  Date range: {min(parsed_dates).isoformat()} to {max(parsed_dates).isoformat()}"
        )


if __name__ == "__main__":
    main()
