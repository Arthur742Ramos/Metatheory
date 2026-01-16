---
name: sorry-checker
description: Check that no sorry placeholders exist in the codebase. Use after making changes or when asked to verify proof completeness.
---

# Verify No Sorry

This skill checks that the codebase contains no `sorry` placeholders, which is a critical requirement for this project.

## Quick Check

Run this command to find any sorries:

```bash
grep -r "sorry" Metatheory/ --include="*.lean"
```

Expected output: No matches (empty output).

## Full Verification

Build the project to verify all proofs compile:

```bash
lake build
```

A successful build with no warnings about `sorry` confirms the codebase is complete.

## What to Do If Sorries Are Found

### Option 1: Complete the Proof Manually

Look at similar proofs nearby and mirror their style.

### Option 2: Use Aristotle

For difficult proofs, use the `aristotle` skill to get automated proof suggestions.

### Option 3: Extract Helper Lemmas

If a proof is stuck, break it into smaller pieces:

```lean
-- Instead of one complex proof
theorem big_theorem : ... := by
  sorry

-- Extract helpers
lemma helper1 : ... := by
  ...

lemma helper2 : ... := by
  ...

theorem big_theorem : ... := by
  apply helper1
  apply helper2
```

## Project Policy

**`sorry` is NEVER acceptable in commits to this codebase.**

All theorems must be fully proven before merging.
