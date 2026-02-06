#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/link_skills.sh [--codex] [--claude]

Creates symlinks from your global skill directories back into this repository.
This lets you edit the repo-scoped skills and have the changes immediately
reflected in your local Codex/Claude installs.

Examples:
  scripts/link_skills.sh --codex
  scripts/link_skills.sh --claude
  scripts/link_skills.sh --codex --claude

Notes:
  - This script is never run automatically by builds or tests.
  - If a target path exists and is not a symlink, it is moved aside to a
    timestamped *.bak.* backup before the symlink is created.
EOF
}

want_codex=0
want_claude=0

for arg in "$@"; do
  case "$arg" in
    --codex) want_codex=1 ;;
    --claude) want_claude=1 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown arg: $arg" >&2; usage >&2; exit 2 ;;
  esac
done

if [[ "$want_codex" -eq 0 && "$want_claude" -eq 0 ]]; then
  echo "Pick at least one of --codex or --claude" >&2
  usage >&2
  exit 2
fi

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd -- "${script_dir}/.." && pwd)"

backup_if_needed() {
  local target="$1"
  if [[ -e "$target" && ! -L "$target" ]]; then
    local ts
    ts="$(date +"%Y%m%d-%H%M%S")"
    mv "$target" "${target}.bak.${ts}"
  fi
}

link_one() {
  local target="$1"
  local source="$2"

  mkdir -p "$(dirname -- "$target")"
  backup_if_needed "$target"
  ln -sfn "$source" "$target"
  echo "linked: $target -> $source"
}

if [[ "$want_codex" -eq 1 ]]; then
  link_one "${HOME}/.codex/skills/verus-proof-helper" "${repo_root}/.codex/skills/verus-proof-helper"
fi

if [[ "$want_claude" -eq 1 ]]; then
  link_one "${HOME}/.claude/skills/verus-proof-helper" "${repo_root}/.claude/skills/verus-proof-helper"
fi
