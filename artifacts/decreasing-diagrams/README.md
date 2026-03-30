# Decreasing-Diagrams Artifacts

This directory contains the exported certificate artifacts and benchmark summaries used for the decreasing-diagrams certificate work.

## Layout

- `example.json`: the small built-in example artifact.
- `family-*.json`: the typed internal benchmark family exported by `lake exe ddcert export-bundle`.
- `family-stats.csv`: CSV summary for the internal benchmark family.
- `external/`: hand-written self-contained external benchmarks and their CSV summary.
- `negative/`: malformed or intentionally invalid external artifacts that the checker must reject.
- `external-family/`: generated self-contained external family artifacts, both raw (`family-*.raw.json`) and compressed (`family-*.json`), plus `stats.csv` and `roundtrip.csv`.
- `external-family-negative/`: generated invalid external family artifacts that target missing coverage, bad valleys, and canonical-compression failures.
- `WPTE2026.md`: repo-side checklist and command guide for the certificates-focused workshop submission track.
- `wpte-2026/`: copied evaluation outputs produced by `scripts/prepare-wpte-2026.sh`.

## Regeneration

Run:

```bash
scripts/regenerate-decreasing-diagrams-artifacts.sh
```

Optional arguments:

```bash
scripts/regenerate-decreasing-diagrams-artifacts.sh <max-family-n> <max-external-family-n>
```

The script rebuilds `Metatheory` and `ddcert`, exports the artifact bundles, refreshes the CSV summaries, and smoke-checks representative external artifacts.

For the larger workshop-prep bundle, run:

```bash
scripts/prepare-wpte-2026.sh <max-family-n> <max-external-family-n>
```

## Checker Entry Points

Examples:

```bash
lake exe ddcert check-external artifacts/decreasing-diagrams/external/fan3.json
lake exe ddcert check-external-raw artifacts/decreasing-diagrams/external-family/family-20.raw.json
lake exe ddcert stats-external-benchmarks
lake exe ddcert stats-external-family-range 20
lake exe ddcert roundtrip-external-family-range 20
```
