# Verify Build

Build the project and verify everything compiles correctly with no errors.

## Instructions

1. **Run the build**
```bash
lake build
```

2. **Check for issues**:
   - Compilation errors
   - Warnings
   - Deprecation notices
   - Sorry placeholders (should be NONE)

3. **Report results**:

### If successful:
```
Build successful!

Summary:
- All modules compiled
- No errors
- No sorries detected
```

### If failed:
```
Build FAILED

Errors:
1. [File:Line] Error message
   Context: ...
   Suggested fix: ...

Warnings:
1. [File:Line] Warning message
```

4. **For each error**, provide:
   - The exact error message
   - The relevant code context
   - A suggested fix based on Lean 4 patterns in this codebase

## Common Issues and Fixes

### Type mismatch
- Check if `Nat` vs `Int` coercion is needed (especially in shift operations)
- Verify universe levels match

### Termination proof failed
- Add explicit `termination_by` clause
- Use `decreasing_by` for complex measures

### Tactic failed
- Check if `simp` needs explicit lemmas: `simp only [lemma1, lemma2]`
- Use `omega` for arithmetic goals
- Try `exact` instead of `apply` for precise matching

### Missing imports
- Add necessary imports at file top
- Check `Metatheory.lean` for the full import structure
