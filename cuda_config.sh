#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SPPARK_DIR="${ROOT_DIR}/sppark"
REMOTE_URL="https://github.com/zz-sol/sppark.git"
REMOTE_BRANCH="ed25519-cuda"
BLST_DIR="${SPPARK_DIR}/blst"
BLST_REMOTE_URL="https://github.com/supranational/blst.git"

if [[ -d "${SPPARK_DIR}/.git" ]]; then
  echo "Updating sppark in ${SPPARK_DIR}"
  git -C "${SPPARK_DIR}" remote set-url origin "${REMOTE_URL}" >/dev/null 2>&1 || true
  git -C "${SPPARK_DIR}" fetch origin
  git -C "${SPPARK_DIR}" checkout "${REMOTE_BRANCH}"
  git -C "${SPPARK_DIR}" pull --ff-only origin "${REMOTE_BRANCH}"
elif [[ -d "${SPPARK_DIR}" ]]; then
  ts="$(date +%Y%m%d_%H%M%S)"
  backup="${SPPARK_DIR}.backup.${ts}"
  echo "Existing sppark directory found. Moving to ${backup}"
  mv "${SPPARK_DIR}" "${backup}"
  git clone --branch "${REMOTE_BRANCH}" --depth 1 "${REMOTE_URL}" "${SPPARK_DIR}"
else
  git clone --branch "${REMOTE_BRANCH}" --depth 1 "${REMOTE_URL}" "${SPPARK_DIR}"
fi

if [[ -d "${BLST_DIR}/.git" ]]; then
  echo "Updating blst in ${BLST_DIR}"
  git -C "${BLST_DIR}" remote set-url origin "${BLST_REMOTE_URL}" >/dev/null 2>&1 || true
  git -C "${BLST_DIR}" fetch origin
  git -C "${BLST_DIR}" pull --ff-only
elif [[ -d "${BLST_DIR}" ]]; then
  ts="$(date +%Y%m%d_%H%M%S)"
  backup="${BLST_DIR}.backup.${ts}"
  echo "Existing blst directory found. Moving to ${backup}"
  mv "${BLST_DIR}" "${backup}"
  git clone --depth 1 "${BLST_REMOTE_URL}" "${BLST_DIR}"
else
  git clone --depth 1 "${BLST_REMOTE_URL}" "${BLST_DIR}"
fi

if [[ ! -f "${BLST_DIR}/build.sh" ]]; then
  echo "Expected blst build.sh at ${BLST_DIR}/build.sh but it is missing."
  exit 1
fi

echo "sppark ready at ${SPPARK_DIR}"
