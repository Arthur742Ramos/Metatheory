# Critical Pair Analysis

Perform critical pair analysis for a term rewriting system to check local confluence.

## Arguments
- $ARGUMENTS: The rewriting system to analyze (file path or description)

## Instructions

1. **Extract rewriting rules** from: $ARGUMENTS

2. **Identify critical pairs**

A critical pair occurs when:
- Two rules can apply to the same term
- Their left-hand sides overlap

### Types of Overlaps

**Type 1: Same position overlap**
Both rules apply at the root of the same term.
Example: `x + 0 → x` and `0 + x → x` overlap on `0 + 0`

**Type 2: Nested overlap**
One rule's LHS is a subterm of another's.
Example: If `f(g(x)) → h(x)` and `g(a) → b`, then `f(g(a))` has nested overlap.

**Type 3: Congruence overlap**
Same rule applied at different positions.
Example: `(0 + 1) + (0 + 2)` with rule `0 + x → x`

3. **For each critical pair**, check joinability

Given term `t` with rules `l₁ → r₁` and `l₂ → r₂` both applicable:
- Apply rule 1: `t → t₁`
- Apply rule 2: `t → t₂`
- Find `t'` such that `t₁ →* t'` and `t₂ →* t'`

4. **Generate Lean proof**

```lean
/-- Local confluence by critical pair analysis -/
theorem local_confluent (e e₁ e₂ : Expr) (h1 : e ⟶ e₁) (h2 : e ⟶ e₂) :
    Rewriting.Joinable Step e₁ e₂ :=
  match h1, h2 with
  -- Same rule: trivially joinable
  | Rule.foo _, Rule.foo _ => ⟨_, MultiStep.refl _, MultiStep.refl _⟩

  -- Different rules at same position: join at common form
  | Rule.foo _, Rule.bar _ => ⟨common, path1, path2⟩

  -- Base rule vs congruence
  | Rule.foo _, Rule.congL h => ⟨_, ..., ...⟩

  -- Congruence at different positions (parallel)
  | Rule.congL h1, Rule.congR h2 =>
    ⟨_, MultiStep.single (Rule.congR h2), MultiStep.single (Rule.congL h1)⟩

  -- Congruence at same position (recursive)
  | Rule.congL h1, Rule.congL h2 =>
    let ⟨e', h1', h2'⟩ := local_confluent _ _ _ h1 h2
    ⟨..., MultiStep.congL h1', MultiStep.congL h2'⟩
termination_by structural h1
```

5. **Verify completeness**

Ensure ALL critical pairs are covered:
- [ ] Same rule twice
- [ ] Each pair of different rules
- [ ] Rule vs each congruence position
- [ ] Congruence vs congruence (same and different positions)

## Example: TRS Critical Pairs

For rules `x + 0 → x`, `0 + x → x`, `x * 1 → x`, `1 * x → x`, `x * 0 → 0`, `0 * x → 0`:

Critical pairs include:
1. `0 + 0`: Both add rules apply → both reduce to `0` ✓
2. `1 * 1`: Both mul-one rules apply → both reduce to `1` ✓
3. `0 * 1`: mul-zero and mul-one overlap → `0 * 1 → 0` and `0 * 1 → 0` ✓
4. `1 * 0`: mul-one and mul-zero overlap → `1 * 0 → 0` and `1 * 0 → 0` ✓

See `Metatheory/TRS/Confluence.lean:85-150` for complete implementation.

## Output Format

```
Critical Pair Analysis for: <System Name>

Rules:
1. l₁ → r₁
2. l₂ → r₂
...

Critical Pairs Found:

Pair 1: Rules 1,2 overlap on term T
  - T →₁ T₁
  - T →₂ T₂
  - Joinable: T₁ →* T' ←* T₂ where T' = ...

[Continue for all pairs...]

Conclusion: All critical pairs joinable → Locally confluent
```
