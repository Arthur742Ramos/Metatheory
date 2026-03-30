#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

MAX_FAMILY_N="${1:-20}"
MAX_EXTERNAL_FAMILY_N="${2:-20}"

lake build Metatheory ddcert

mkdir -p artifacts/decreasing-diagrams
mkdir -p artifacts/decreasing-diagrams/external
mkdir -p artifacts/decreasing-diagrams/external-family
mkdir -p artifacts/decreasing-diagrams/external-family-negative

./.lake/build/bin/ddcert export-bundle artifacts/decreasing-diagrams "$MAX_FAMILY_N"
./.lake/build/bin/ddcert export-external-bundle artifacts/decreasing-diagrams
./.lake/build/bin/ddcert export-external-family-bundle artifacts/decreasing-diagrams/external-family "$MAX_EXTERNAL_FAMILY_N"
./.lake/build/bin/ddcert export-external-family-negative-bundle artifacts/decreasing-diagrams/external-family-negative

./.lake/build/bin/ddcert stats-range "$MAX_FAMILY_N" > artifacts/decreasing-diagrams/family-stats.csv
./.lake/build/bin/ddcert stats-external-benchmarks > artifacts/decreasing-diagrams/external/stats.csv
./.lake/build/bin/ddcert stats-external-family-range "$MAX_EXTERNAL_FAMILY_N" > artifacts/decreasing-diagrams/external-family/stats.csv
./.lake/build/bin/ddcert roundtrip-external-family-range "$MAX_EXTERNAL_FAMILY_N" > artifacts/decreasing-diagrams/external-family/roundtrip.csv

while IFS= read -r benchmark; do
  ./.lake/build/bin/ddcert check-external \
    artifacts/decreasing-diagrams/external/"$benchmark".json
  ./.lake/build/bin/ddcert check-external-raw \
    artifacts/decreasing-diagrams/external/"$benchmark".raw.json
done < <(./.lake/build/bin/ddcert list-external-benchmarks)

./.lake/build/bin/ddcert check-external artifacts/decreasing-diagrams/external-family/family-"$MAX_EXTERNAL_FAMILY_N".json
./.lake/build/bin/ddcert check-external-raw artifacts/decreasing-diagrams/external-family/family-"$MAX_EXTERNAL_FAMILY_N".raw.json

expect_reject() {
  local cmd="$1"
  local artifact="$2"
  if ./.lake/build/bin/ddcert "$cmd" "$artifact"; then
    echo "expected rejection for $artifact" >&2
    exit 1
  fi
}

expect_reject check-external-raw artifacts/decreasing-diagrams/external-family-negative/family-5-missing-loop-self.raw.json
expect_reject check-external artifacts/decreasing-diagrams/external-family-negative/family-5-extra-trivial.json
expect_reject check-external artifacts/decreasing-diagrams/external-family-negative/family-5-symmetric-duplicate.json
expect_reject check-external artifacts/decreasing-diagrams/external-family-negative/family-5-missing-peak.json
expect_reject check-external artifacts/decreasing-diagrams/external-family-negative/family-5-bad-valley.json

echo "decreasing-diagrams artifacts regenerated"
