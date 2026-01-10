---
name: aristotle
description: Run Aristotle automated theorem prover on Lean files to fill sorry placeholders. Use when you have a file with sorries that needs automated proof search. Handles API setup and result verification.
---

# Aristotle Automated Theorem Prover

This skill runs [Aristotle](https://aristotle.harmonic.fun) to automatically fill `sorry` placeholders in Lean 4 files.

## Important: Version Compatibility Warning

**This project uses Lean 4.14.0, but Aristotle runs on Lean 4.24.0.**

This version mismatch may cause issues:
- Syntax differences between Lean versions
- Tactic availability differences
- Type inference changes

Consider upgrading the toolchain if you need Aristotle support, or use Aristotle's output as a guide rather than direct copy-paste.

## Quick Usage

```
/aristotle path/to/file.lean
```

## Project Policy Note

This repository has a **"No Sorrys Allowed"** policy. Aristotle is useful for:
1. Development workflow (fill sorries before committing)
2. Exploring proof strategies
3. Verifying that automated provers can handle certain goals

## Workflow

When the user invokes `/aristotle`, follow these steps:

### Step 1: Validate the Target File

1. **Check file exists**: Verify the specified `.lean` file exists
2. **Check for sorries**: Grep for `sorry` in the file - if none, inform user
3. **Warn about version mismatch**: Remind user about Lean 4.14.0 vs 4.24.0

```bash
grep -n "sorry" "path/to/file.lean"
```

### Step 2: Run Aristotle

```bash
export ARISTOTLE_API_KEY='arstl_hCSoWHQ4OwTccQbXeuRXOHF-UqIH8RtVMUjS2B_vIpI'
uvx --from aristotlelib aristotle.exe prove-from-file "path/to/file.lean" \
  --output-file "path/to/file_aristotle.lean"
```

**Important**: The command may take several minutes. Aristotle queues jobs and polls for completion.

### Step 3: Report Results

After Aristotle completes, read the output file header to see what was proved:

```lean
/-
This file was edited by Aristotle.
...
The following was proved by Aristotle:
- theorem foo : ...
- theorem bar : ...
-/
```

Report to user:
- Number of theorems attempted
- Number successfully proved
- Any that failed or were skipped
- Version compatibility warnings if tactics don't exist in 4.14.0

### Step 4: Adapt Output for Lean 4.14.0

If Aristotle produces tactics that don't exist in Lean 4.14.0:

| Aristotle Output | Lean 4.14.0 Equivalent |
|------------------|------------------------|
| `grind` | May not exist - try `simp`, `omega`, or manual proof |
| `exact?` | `exact?` should work (Mathlib tactic) |
| `omega` | Should work |
| `decide` | Should work |

### Step 5: Verify Output

Try building with the project's Lean version:

```bash
lake build ModuleName
```

## Command Variations

### Basic Usage
```
/aristotle Metatheory/Lambda/NewLemma.lean
```

### With Custom Output
```
/aristotle Metatheory/Lambda/NewLemma.lean --output NewLemma_proved.lean
```

## Interpreting Aristotle Output

### Success Indicators

```lean
/-
The following was proved by Aristotle:
- theorem my_theorem : ...
-/
```

### Common Proof Tactics

| Tactic | Meaning | 4.14.0 Compatible? |
|--------|---------|-------------------|
| `exact?` | Found matching lemma | Yes (Mathlib) |
| `grind` | Automation | Maybe not |
| `simp` | Simplification | Yes |
| `rfl` | Reflexivity | Yes |
| `omega` | Linear arithmetic | Yes |
| `decide` | Decidable proposition | Yes |

### Failure Indicators

```lean
/- Aristotle failed to load this code into its environment. -/
```
**Cause**: Version incompatibility or syntax issues.

## Environment Setup

The API key should be set in `~/.bashrc`:
```bash
export ARISTOTLE_API_KEY='arstl_hCSoWHQ4OwTccQbXeuRXOHF-UqIH8RtVMUjS2B_vIpI'
```

## Project-Specific Modules

### Modules That Should Work Well

| Module | Description |
|--------|-------------|
| `Rewriting/Basic.lean` | Core ARS definitions |
| `Rewriting/Diamond.lean` | Diamond property proofs |
| `Rewriting/Newman.lean` | Newman's lemma |
| `Lambda/Term.lean` | De Bruijn terms |
| `TRS/Syntax.lean` | Expression syntax |

### Complex Modules

| Module | Notes |
|--------|-------|
| `Lambda/Complete.lean` | Complex substitution lemmas |
| `STLC/Normalization.lean` | Logical relations proofs |

## Troubleshooting

| Issue | Solution |
|-------|----------|
| Version mismatch errors | Manually adapt tactics for 4.14.0 |
| `grind` not found | Replace with `simp` or manual proof |
| API key error | Check `ARISTOTLE_API_KEY` is set |
| Timeout | Use `--no-wait`, check dashboard later |

## Example Session

User: `/aristotle Metatheory/Lambda/NewLemma.lean`

Claude:
1. Reads file, finds 2 sorries
2. Warns about Lean 4.14.0 vs 4.24.0 compatibility
3. Runs Aristotle (waits ~3-5 minutes)
4. Reports: "Aristotle proved 2/2 theorems"
5. Notes: "Output uses `grind` tactic - may need adaptation"
6. Offers to help adapt proofs for Lean 4.14.0
