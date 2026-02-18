#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

lake build

if grep -R -n -w sorry --include='*.lean' --exclude-dir='.lake' .; then
  echo "Found forbidden placeholder: sorry"
  exit 1
fi

if grep -R -n -w admit --include='*.lean' --exclude-dir='.lake' .; then
  echo "Found forbidden placeholder: admit"
  exit 1
fi

if grep -R -n -E '^[[:space:]]*(axiom|constant)\b' --include='*.lean' --exclude-dir='.lake' .; then
  echo "Found forbidden declaration: axiom/constant"
  exit 1
fi

echo "OK"
