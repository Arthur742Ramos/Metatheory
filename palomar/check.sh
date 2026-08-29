#!/usr/bin/env bash
set -euo pipefail

PALOMAR_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$PALOMAR_DIR"

lake build
lake env lean --src-deps Challenge.lean
lake env lean --src-deps Solution.lean
lake env lean --src-deps Checks.lean
lake env lean Challenge.lean
lake env lean Solution.lean
lake env lean Checks.lean

if rg -n '^import[[:space:]]+Metatheory($|\.)' --glob '*.lean' .; then
  echo "Palomar sources import the parent Metatheory project"
  exit 1
fi

if rg -n '\bsorry\b|\badmit\b' PalomarCommon.lean Solution.lean Checks.lean; then
  echo "production Palomar sources contain a placeholder"
  exit 1
fi

if rg -n '^[[:space:]]*(axiom|constant)\b' PalomarCommon.lean Solution.lean Checks.lean; then
  echo "production Palomar sources contain an axiom or constant declaration"
  exit 1
fi
