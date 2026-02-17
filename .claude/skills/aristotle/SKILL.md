---
name: aristotle
description: Run Aristotle automated theorem prover on Lean files to fill sorry placeholders. Use when you have a file with sorries that needs automated proof search. Handles API setup and result verification.
---

# Aristotle Automated Theorem Prover

This skill runs [Aristotle](https://aristotle.harmonic.fun) to automatically fill `sorry` placeholders in Lean 4 files.

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

```bash
grep -n "sorry" "path/to/file.lean"
```

### Step 2: Run Aristotle

```bash
export ARISTOTLE_API_KEY='arstl_hCSoWHQ4OwTccQbXeuRXOHF-UqIH8RtVMUjS2B_vIpI'
uvx --from aristotlelib aristotle.exe prove-from-file "path/to/file.lean" \
  --output-file "path/to/file_aristotle.lean"
```

**IMPORTANT - Long Processing Times**:
- Aristotle can take **30+ minutes** for complex proofs (e.g., substitution lemmas, normalization proofs)
- **DO NOT kill the process prematurely** - let it run to completion
- Run the command in the background with `run_in_background: true`
- Periodically check progress by reading the output file
- Progress may stay at low percentages (1-10%) for extended periods while Aristotle searches for proofs
- Only consider it failed if it returns an error status, not just because it's taking a long time

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

### Step 4: Verify Output

Try building to verify the proofs compile:

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

| Tactic | Meaning |
|--------|---------|
| `exact?` | Found matching lemma (build to see suggestion) |
| `grind` | Automation solved it |
| `simp` | Simplification |
| `rfl` | Reflexivity |
| `omega` | Linear arithmetic |
| `decide` | Decidable proposition |

### Failure Indicators

```lean
/- Aristotle failed to load this code into its environment. -/
```
**Cause**: Syntax issues or import problems.

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
| API key error | Check `ARISTOTLE_API_KEY` is set |
| Timeout | Use `--no-wait`, check dashboard later |
| `exact?` in output | Run `lake build` to see suggestions |

## Example Session

User: `/aristotle Metatheory/Lambda/NewLemma.lean`

Claude:
1. Reads file, finds 2 sorries
2. Runs Aristotle (waits ~3-5 minutes)
3. Reports: "Aristotle proved 2/2 theorems"
4. Offers: "Want me to verify the output compiles?"
5. Builds, reports success
