# Add Lemma

Add a new lemma to the codebase following the project's style conventions.

## Arguments
- $ARGUMENTS: Description of the lemma to add, including file location if known

## Instructions

1. **Understand the request**: Parse the lemma description from: $ARGUMENTS

2. **Determine placement**:
   - Which module should contain this lemma?
   - What lemmas does it depend on?
   - What lemmas will use it?

3. **Write the lemma** following conventions:

### Documentation
```lean
/-- Brief description of what the lemma states.

    Longer explanation if needed, including:
    - Mathematical intuition
    - Use cases
    - Related lemmas

    References:
    - [Citation if applicable] -/
```

### Naming Conventions
- Use snake_case
- Start with the main subject: `star_trans`, `subst_shift_cancel`
- Use standard suffixes: `_of_`, `_iff_`, `_comm`, `_assoc`

### Proof Style
- Prefer tactic proofs for complex results
- Use term mode for simple definitions
- Structure proofs with comments for long proofs:
  ```lean
  theorem foo : ... := by
    -- Step 1: Establish base case
    ...
    -- Step 2: Induction on M
    induction M with
    | var n => ...
    | app M N ih_M ih_N => ...
    | lam M ih => ...
  ```

4. **Complete the proof**: NO sorries allowed

5. **Verify**: Run `lake build` to ensure it compiles

6. **Consider adding tests**: Add `#check` statements to verify types

## Template

```lean
/-- Description of the lemma.

    Additional context about usage and significance. -/
theorem lemma_name {α : Type*} (params : ...) : conclusion := by
  -- Proof structure explanation
  <proof>
```

## Checklist
- [ ] Docstring with description
- [ ] Proper type signatures
- [ ] Complete proof (no sorry)
- [ ] Follows naming conventions
- [ ] Placed in appropriate module
- [ ] Builds successfully
