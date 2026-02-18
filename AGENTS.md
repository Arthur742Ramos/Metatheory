# Codex Workflow for Metatheory

Contribute to this Metatheory (Lean 4) repo using the Codex CLI workflow: make focused edits, run lake build, and never leave sorry proofs.

## Non-negotiables

- `sorry` is not acceptable anywhere in `Metatheory/`.
- Prefer small, reviewable changes over large refactors.
- Keep edits consistent with existing Lean style and naming.

## How to Work in This Repo

### 1. Orient

- Identify the relevant layer under `Metatheory/`:
  - `Rewriting/` - Generic abstract rewriting system framework
  - `Lambda/` - Lambda calculus Church-Rosser theorem
  - `CL/` - Combinatory Logic Church-Rosser theorem
  - `TRS/` - Simple expression rewriting
  - `StringRewriting/` - String rewriting
  - `STLC/` - Simply typed lambda calculus
- Find similar theorems/lemmas nearby and mirror their proof style.

### 2. Implement

- Update Lean code with the smallest change that fixes the issue or adds the feature.
- If a proof gets stuck, extract helper lemmas instead of introducing ad-hoc rewrites.

### 3. Validate

Run:
```bash
lake build
```

Ensure there are no `sorry` placeholders, no new build errors, and no build warnings.

### 4. Report

Summarize what changed and which command(s) you ran.

## Useful Commands

```bash
lake build    # Build the project
lake clean    # Clean build artifacts
```

## Additional Context

See `CLAUDE.md` for full project documentation, including:
- Project structure and layers
- Key theorems and proof techniques
- Code style conventions
- References and citations
