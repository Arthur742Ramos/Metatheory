# WPTE 2026 Submission Outline

## Candidate Titles

- Self-Contained Decreasing-Diagram Certificates with Canonical Compression
- Certified Checking of Self-Contained Confluence Artifacts for Decreasing Diagrams
- Lean-Checked Self-Contained Certificates for Decreasing-Diagram Confluence Proofs

## Core Claim

We present a Lean-checked certificate format for finite decreasing-diagram confluence proofs in which the artifact itself describes the entire labeled rewrite system, the checker derives confluence directly for that embedded relation, and a deterministic canonical compression layer removes trivial peaks and symmetric duplicates without changing the certified result. The resulting story is backed by positive and negative benchmark corpora plus a generated external family that scales through `n = 100`, where compression reduces `707` raw certificates to `101` compressed certificates (`85%` reduction) and shrinks the JSON artifact from `115757` bytes to `34500` bytes (`70%` reduction).

## Contribution Bullets

- A self-contained external certificate interface: exported artifacts enumerate both steps and decreasing-diagram certificates, so the checked object is the whole finite rewriting problem rather than a certificate interpreted against a separate trusted relation.
- A canonical compressed format for external certificates: the strengthened checker accepts only non-trivial canonically oriented peaks, and the raw-to-compressed roundtrip is deterministic across the generated family (`0..100` all `ok` in `external-family/roundtrip.csv`).
- A negative regression suite that exercises the exact failure modes a certificates paper should care about: malformed JSON, missing peak coverage, bad valleys, extra trivial certificates, and symmetric duplicates that violate the canonical compression invariant.
- A reproducible evaluation path with Lean theorems, CLI commands, exported artifacts, CSV summaries, and scripts that regenerate both the benchmark corpus and the workshop-facing bundle from the repository state.

## Benchmark Table

| Case | Suite | Steps | Raw certs | Compressed certs | Cert reduction | Raw bytes | Compressed bytes | JSON reduction | Raw check (us) | Compressed check (us) |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `fan3` | hand-written external | 7 | 13 | 3 | 76% | 1905 | 655 | 65% | 66 | 30 |
| `fan4` | hand-written external | 9 | 21 | 6 | 71% | 3009 | 1119 | 62% | 108 | 54 |
| `staggered` | hand-written external | 6 | 8 | 1 | 87% | 1233 | 363 | 70% | 41 | 15 |
| `shortcut` | hand-written external | 4 | 6 | 1 | 83% | 899 | 284 | 68% | 28 | 10 |
| `zigzag` | hand-written external | 8 | 10 | 1 | 90% | 1569 | 443 | 71% | 54 | 20 |
| `funnel` | hand-written external | 10 | 16 | 3 | 81% | 2445 | 793 | 67% | 90 | 40 |
| `double-peak` | hand-written external | 9 | 13 | 2 | 84% | 1953 | 591 | 69% | 66 | 27 |
| `family-0` | generated external family | 5 | 7 | 1 | 85% | 1065 | 323 | 69% | 35 | 13 |
| `family-5` | generated external family | 30 | 42 | 6 | 85% | 6465 | 1902 | 70% | 273 | 123 |
| `family-20` | generated external family | 105 | 147 | 21 | 85% | 23055 | 6792 | 70% | 1763 | 970 |
| `family-50` | generated external family | 255 | 357 | 51 | 85% | 57357 | 17000 | 70% | 8258 | 5034 |
| `family-100` | generated external family | 505 | 707 | 101 | 85% | 115757 | 34500 | 70% | 29501 | 18766 |

Interpretation: the generated family gives a simple scaling law instead of a pile of unrelated examples, while the hand-written suite now covers larger fans, shortcut valleys, longer asymmetric joins, mixed three-way peaks, and multiple independent peaks. The evaluation takeaway is that canonical compression is not only smaller but also faster to check on every measured instance.

## Negative-Regression Table

| Artifact | Family | Failure mode | Expected outcome |
| --- | --- | --- | --- |
| `negative/fan3-missing-loop-self.raw.json` | hand-written raw | missing trivial self-peak certificate for the loop step | checker rejects |
| `negative/fan3-extra-trivial.json` | hand-written compressed | extra trivial certificate violates canonical compressed form | checker rejects |
| `negative/fan3-missing-peak.json` | hand-written compressed | incomplete peak coverage | checker rejects |
| `negative/staggered-bad-valley.json` | hand-written compressed | valley path does not witness a valid join | checker rejects |
| `negative/malformed.json` | parser regression | malformed JSON input | parser fails |
| `external-family-negative/family-5-missing-loop-self.raw.json` | generated raw | missing loop self-peak in the generated family | checker rejects |
| `external-family-negative/family-5-extra-trivial.json` | generated compressed | extra trivial certificate after compression | checker rejects |
| `external-family-negative/family-5-symmetric-duplicate.json` | generated compressed | symmetric duplicate survives compression, violating canonical orientation | checker rejects |
| `external-family-negative/family-5-missing-peak.json` | generated compressed | one canonical peak certificate removed | checker rejects |
| `external-family-negative/family-5-bad-valley.json` | generated compressed | invalid valley endpoint in a generated family peak | checker rejects |

This table is useful because it shows that the checker is not just proving confluence for positive examples; it is also enforcing the representation invariants that make the compressed artifact format a real technical contribution.

## Reproducibility Paragraph

The current repo can regenerate the complete certificates artifact story from source. Running `scripts/prepare-wpte-2026.sh 20 100` performs a full `lake build`, refreshes the hand-written and generated decreasing-diagrams artifacts, regenerates benchmark CSVs, validates the raw-to-canonical roundtrip for the external family through `n = 100`, checks the largest positive generated artifact (`family-100` raw and compressed), confirms that all generated family-negative artifacts are rejected, and copies the resulting evaluation files into `artifacts/decreasing-diagrams/wpte-2026/`. The main outputs for the submission are `external-benchmarks-stats.csv`, `external-family-stats-100.csv`, `external-family-roundtrip-100.csv`, and `external-family-100.txt`.

## Suggested 10-Page Shape

1. Introduction: confluence certificates should be portable artifacts, not proofs tied to a hidden trusted relation.
2. Certificate format: raw self-contained artifacts and their Lean checker.
3. Canonical compression: trivial-peak elimination, symmetric-duplicate elimination, and deterministic roundtripping.
4. Soundness story: successful checking implies confluence of the embedded labeled relation.
5. Evaluation: hand-written benchmarks, generated family scaling, and negative regressions.
6. Reproducibility and lessons: scripts, artifacts, and what this buys over ad hoc encodings.
