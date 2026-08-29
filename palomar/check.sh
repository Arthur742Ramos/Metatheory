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

if rg -n '^import[[:space:]]+(Palomar|Metatheory)' Challenge.lean; then
  echo "Challenge imports project-local source"
  exit 1
fi

challenge_deps="$(lake env lean --src-deps Challenge.lean)"
if printf '%s\n' "$challenge_deps" | rg -q '/palomar/'; then
  echo "Challenge source closure contains project-local source"
  exit 1
fi

production_sources=(PalomarCommon.lean PalomarProof.lean Solution.lean Checks.lean)

if rg -n '\bsorry\b|\badmit\b|Lean\.ofReduceBool|\bnative_decide\b' "${production_sources[@]}"; then
  echo "production Palomar sources contain a placeholder"
  exit 1
fi

if rg -n '^[[:space:]]*(axiom|constant)\b' "${production_sources[@]}"; then
  echo "production Palomar sources contain an axiom or constant declaration"
  exit 1
fi
