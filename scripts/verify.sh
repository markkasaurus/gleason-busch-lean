#!/usr/bin/env bash

set -euo pipefail

repo_root="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT

build_log="$tmpdir/build.log"
axioms_log="$tmpdir/axioms.log"

cd "$repo_root"

echo "[1/4] Building the repository"
lake build 2>&1 | tee "$build_log"
if grep -nE "warning:|error:" "$build_log" >/dev/null; then
  echo
  echo "Build output contains warnings or errors:"
  grep -nE "warning:|error:" "$build_log"
  exit 1
fi

echo
echo "[2/4] Checking axiom dependencies"
lake env lean Verification/Axioms.lean 2>&1 | tee "$axioms_log"
if grep -n "sorryAx" "$axioms_log" >/dev/null; then
  echo
  echo "Unexpected sorryAx dependency found:"
  grep -n "sorryAx" "$axioms_log"
  exit 1
fi
if grep "depends on axioms:" "$axioms_log" | grep -vF "depends on axioms: [propext, Classical.choice, Quot.sound]" >/dev/null; then
  echo
  echo "Unexpected axiom dependency found:"
  grep "depends on axioms:" "$axioms_log" | grep -vF "depends on axioms: [propext, Classical.choice, Quot.sound]"
  exit 1
fi

echo
echo "[3/4] Scanning for placeholders"
if grep -RInE "\\b(sorry|admit)\\b" --include="*.lean" --exclude-dir=".lake" --exclude-dir="build" --exclude-dir=".git" . >/dev/null; then
  echo
  echo "Unexpected placeholder token found:"
  grep -RInE "\\b(sorry|admit)\\b" --include="*.lean" --exclude-dir=".lake" --exclude-dir="build" --exclude-dir=".git" .
  exit 1
fi

echo
echo "[4/4] Scanning for custom declaration escape hatches"
if grep -RInE "^[[:space:]]*(axiom|postulate|unsafe|opaque)\\b" --include="*.lean" --exclude-dir=".lake" --exclude-dir="build" --exclude-dir=".git" . >/dev/null; then
  echo
  echo "Unexpected declaration form found:"
  grep -RInE "^[[:space:]]*(axiom|postulate|unsafe|opaque)\\b" --include="*.lean" --exclude-dir=".lake" --exclude-dir="build" --exclude-dir=".git" .
  exit 1
fi

echo
echo "Verification completed successfully."
