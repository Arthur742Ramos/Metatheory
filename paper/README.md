# ITP 2026 Short Paper: A Lean 4 Toolbox for First-Order Term Rewriting

## Paper Details

**Title:** A Lean 4 Toolbox for First-Order Term Rewriting: Critical Pairs, Newman Confluence, and Completion Orderings

**Submission type:** Short paper (6 pages)

**Conference:** ITP 2026 (17th International Conference on Interactive Theorem Proving), July 26-29, 2026, Lisbon, Portugal

## Building the Paper

### Prerequisites

1. Download the LIPIcs style files from:
   https://submission.dagstuhl.de/series/details/LIPIcs#author

2. Extract `lipics-v2021.cls` and related files to this directory.

### Compilation

```bash
pdflatex itp2026-trs.tex
bibtex itp2026-trs
pdflatex itp2026-trs.tex
pdflatex itp2026-trs.tex
```

## Building the Artifact

The accompanying Lean 4 library can be built with:

```bash
cd ..
lake update
lake build
```

### Key Modules

| Module | Description |
|--------|-------------|
| `Metatheory.TRS.FirstOrder.Syntax` | First-order terms, substitutions |
| `Metatheory.TRS.FirstOrder.Positions` | Positions, subterms, replacement |
| `Metatheory.TRS.FirstOrder.Rules` | Rewrite rules and steps |
| `Metatheory.TRS.FirstOrder.Unification` | Robinson unification |
| `Metatheory.TRS.FirstOrder.CriticalPairs` | Critical pair construction |
| `Metatheory.TRS.FirstOrder.Confluence` | Critical pair theorem, Knuth-Bendix |
| `Metatheory.TRS.FirstOrder.Ordering` | Weight/matrix orderings |
| `Metatheory.TRS.FirstOrder.LPO` | Lexicographic path ordering |
| `Metatheory.TRS.FirstOrder.Examples` | Worked examples |
| `Metatheory.Rewriting.Newman` | Newman's lemma (abstract) |
| `Metatheory.Rewriting.Basic` | Abstract rewriting definitions |

### Main Theorems

1. **Critical Pair Theorem** (`FirstOrder/Confluence.lean:201`):
   ```lean
   theorem localConfluent_of_criticalPairsJoinable :
       CriticalPairsJoinable rules → LocalConfluent rules
   ```

2. **Newman's Lemma** (`Rewriting/Newman.lean:150`):
   ```lean
   theorem confluent_of_terminating_localConfluent :
       Terminating r → LocalConfluent r → Confluent r
   ```

3. **Knuth-Bendix Confluence** (`FirstOrder/Confluence.lean:337`):
   ```lean
   theorem confluent_of_terminating_criticalPairsJoinable :
       Terminating rules → CriticalPairsJoinable rules → Confluent rules
   ```

4. **Termination via Ordering** (`FirstOrder/Confluence.lean:318`):
   ```lean
   theorem terminating_of_ordering :
       (∀ r, rules r → ord.lt r.rhs r.lhs) → Terminating rules
   ```

## File Counts

The first-order TRS development comprises approximately 5,000 lines across 19 modules:
- `FirstOrder/*.lean`: ~4,500 lines
- `Rewriting/*.lean`: ~1,500 lines (shared with other developments)

## Important Dates (ITP 2026)

- Abstract deadline: February 12, 2026 (AOE)
- Paper submission: February 19, 2026 (AOE)
- Author notification: April 26, 2026
- Camera-ready: May 24, 2026
- Conference: July 26-29, 2026
