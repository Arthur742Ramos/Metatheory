#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MAX_FAMILY_N="${1:-20}"
MAX_EXTERNAL_FAMILY_N="${2:-100}"

lake build
scripts/regenerate-decreasing-diagrams-artifacts.sh "$MAX_FAMILY_N" "$MAX_EXTERNAL_FAMILY_N"

mkdir -p artifacts/decreasing-diagrams/wpte-2026

cp artifacts/decreasing-diagrams/external/stats.csv \
  artifacts/decreasing-diagrams/wpte-2026/external-benchmarks-stats.csv
cp artifacts/decreasing-diagrams/external-family/stats.csv \
  artifacts/decreasing-diagrams/wpte-2026/external-family-stats-"$MAX_EXTERNAL_FAMILY_N".csv
cp artifacts/decreasing-diagrams/external-family/roundtrip.csv \
  artifacts/decreasing-diagrams/wpte-2026/external-family-roundtrip-"$MAX_EXTERNAL_FAMILY_N".csv

./.lake/build/bin/ddcert stats-external-family "$MAX_EXTERNAL_FAMILY_N" \
  > artifacts/decreasing-diagrams/wpte-2026/external-family-"$MAX_EXTERNAL_FAMILY_N".txt

echo "WPTE 2026 prep bundle refreshed under artifacts/decreasing-diagrams/wpte-2026"
