#!/usr/bin/env bash
# Run at G-F0a. Override all three paths when testing the helper.
set -euo pipefail
cd "$(dirname "$0")/.."
manifest=docs/FGSA-API.md
frozen=docs/FGSA-API-frozen.md
frozen_sha=scripts/fgsa-manifest-frozen.sha256
usage() {
  echo "usage: bash scripts/fgsa-freeze.sh [--manifest <path>] [--frozen <path>] [--frozen-sha <path>]" >&2
}
while [ $# -gt 0 ]; do
  case "$1" in
    --manifest|--frozen|--frozen-sha)
      [ $# -ge 2 ] || { usage; exit 2; }
      case "$1" in
        --manifest) manifest=$2 ;;
        --frozen) frozen=$2 ;;
        --frozen-sha) frozen_sha=$2 ;;
      esac
      shift 2 ;;
    *) usage; exit 2 ;;
  esac
done
lake env lean --run scripts/V2Manifest.lean --scope fgsa --write --manifest "$manifest"
cp "$manifest" "$frozen"
python3 - "$frozen" "$frozen_sha" <<'PY'
import hashlib
import pathlib
import sys

digest = hashlib.sha256(pathlib.Path(sys.argv[1]).read_bytes()).hexdigest()
pathlib.Path(sys.argv[2]).write_text(digest + "\n")
PY
echo "FGSA frozen: $frozen; SHA-256: $frozen_sha"
