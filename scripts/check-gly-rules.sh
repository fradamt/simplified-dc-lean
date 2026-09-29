#!/usr/bin/env bash
# Check (i), BUILD §7.3: the GLY §F rules whose enforcement is a grep or a
# mechanical scan. The rules, their scopes and their baselines
# (scripts/baselines/check-gly-rules-<rule>.txt) are in
# scripts/check-gly-rules.py; this driver runs every rule.
# F-7 and F-10 compare with the base commit GLY_BASE (default 7ac5b0c).
# Usage: bash scripts/check-gly-rules.sh [--rule F-n]... [--list-legacy] [--write-baseline]
# Exit 0: no failing finding; 1: a failing finding; 2: an input error.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/check-gly-rules.py "$@"
