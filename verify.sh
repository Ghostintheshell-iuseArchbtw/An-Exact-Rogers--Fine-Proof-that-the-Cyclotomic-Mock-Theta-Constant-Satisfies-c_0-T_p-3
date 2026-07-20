#!/usr/bin/env bash
set -euo pipefail

command -v rg >/dev/null 2>&1 || {
  echo "Error: ripgrep (rg) is required for source verification."
  exit 127
}

lake build

if rg -n '\b(sorry|admit|axiom|sorryAx|native_decide)\b' \
  --glob '*.lean' \
  --glob '!Audit.lean' \
  .; then
  echo "Forbidden placeholder, custom axiom, or native_decide found."
  exit 1
fi

lake env lean Audit.lean
