# Check for Sorries

Scan the codebase for any `sorry` placeholders and report them. This codebase has a strict NO SORRY policy.

## Instructions

1. Search all `.lean` files for:
   - `sorry` keyword
   - `admit` keyword
   - `axiom`/`constant` declarations

2. For each finding, report:
   - File path and line number
   - The theorem/definition containing the sorry
   - Context about what needs to be proven

3. If sorries are found, suggest approaches to complete the proofs based on:
   - Similar completed proofs in the codebase
   - Standard techniques (induction, well-founded recursion, case analysis)
   - Referenced literature

4. Run `lake build` to verify the project compiles

## Expected Output

If clean:
```
All proofs complete. No sorries found in the codebase.
Build successful.
```

If sorries found:
```
Found incomplete proofs:

1. File: Metatheory/Example/Foo.lean:42
   Theorem: example_theorem
   Context: Needs induction on term structure

   Suggested approach: Follow pattern from Lambda/Term.lean:shift_zero

[Additional findings...]
```
