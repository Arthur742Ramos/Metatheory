# Explain Theorem

Provide a detailed explanation of a theorem in this codebase, including proof strategy and mathematical context.

## Arguments
- $ARGUMENTS: Theorem name or description (e.g., "Newman's lemma", "strong_normalization", "subst_subst_gen")

## Instructions

1. **Find the theorem**: Search for the theorem by name in the codebase

2. **Provide explanation** covering:

### Mathematical Context
- What does this theorem state in plain language?
- Why is it important in PL foundations / term rewriting?
- Historical context and original sources

### Proof Strategy
- What technique is used? (induction, well-founded recursion, logical relations, etc.)
- What are the key lemmas it depends on?
- What is the overall proof structure?

### Code Walkthrough
- Explain the Lean 4 proof tactics used
- Highlight tricky parts
- Explain any non-obvious steps

### Connections
- How does this theorem relate to others in the codebase?
- What theorems depend on it?
- Are there alternative proof approaches?

3. **Format output** as educational material suitable for someone learning PL theory

## Example Output Format

```
## Theorem: confluence_of_diamond

### Statement
If a relation r has the diamond property (one-step divergence closes in one step),
then r is confluent (multi-step divergence closes in multi-step).

### Mathematical Significance
This is a cornerstone result in term rewriting theory. It provides the standard
approach for proving Church-Rosser for untyped lambda calculus via parallel
reduction (Takahashi 1995).

### Proof Strategy
1. First prove the "strip lemma": diamond allows pushing a step through a path
2. Use strip lemma to prove semi-confluence
3. Apply the equivalence: semi-confluence ⟺ confluence

### Key Dependencies
- `strip`: The strip lemma (Rewriting/Diamond.lean:71)
- `SemiConfluent.toConfluent`: Semi-conf implies conf (Rewriting/Basic.lean:242)

### Code Explanation
[Line-by-line explanation of the proof...]
```
