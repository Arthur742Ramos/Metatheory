# De Bruijn Helper

Assist with de Bruijn index manipulation lemmas - shifting, substitution, and their interactions.

## Arguments
- $ARGUMENTS: Description of the de Bruijn lemma needed or problem encountered

## Instructions

1. **Identify the lemma type** from: $ARGUMENTS

### Common De Bruijn Lemmas

#### Shift Lemmas
- `shift_zero`: shift 0 c M = M
- `shift_shift`: shift d₁ c (shift d₂ c M) = shift (d₁+d₂) c M
- `shift_shift_comm`: Shift commutation at different cutoffs
- `shift_shift_succ`: shift 1 (c+1) (shift 1 c M) = shift 2 c M

#### Substitution Lemmas
- `subst_var_eq`: subst j N (var j) = N
- `subst_var_ne`: subst j N (var n) when n ≠ j
- `subst_shift_cancel`: subst c N (shift 1 c M) = M

#### Key Interaction Lemmas
- `shift_subst`: shift d c (M[N]) = (shift d (c+1) M)[shift d c N]
- `subst_subst_gen`: (subst (j+1) (shift1 N) M)[subst j N L] = subst j N (M[L])

2. **Proof strategies** for de Bruijn lemmas:

### Induction on Term Structure
Most de Bruijn lemmas use:
```lean
induction M generalizing <params> with
| var n =>
  -- Case analysis on n vs cutoff/substitution index
  by_cases h : n < c
  · -- Below cutoff: variable unchanged
  · -- Above cutoff: adjust index
| app M N ih_M ih_N =>
  simp only [shift, subst]
  rw [ih_M, ih_N]
| lam M ih =>
  simp only [shift, subst]
  congr 1
  -- Key: cutoff/index increases by 1 under binder
  -- May need auxiliary lemmas about shifted arguments
```

### Key Proof Patterns

**Pattern 1: Variable case splitting**
```lean
by_cases h : n = j
· -- n = j: substitution fires
  simp only [h, ite_true]
· by_cases h' : n > j
  · -- n > j: index decreases
  · -- n < j: unchanged
```

**Pattern 2: Using omega for index arithmetic**
```lean
have h1 : n + 1 ≠ j := by omega
have h2 : n + 1 > j := by omega
```

**Pattern 3: Int.toNat handling**
```lean
have eq1 : Int.toNat (↑n + ↑d) = n + d := by
  simp only [← Int.ofNat_add, Int.toNat_ofNat]
```

3. **Generate the lemma** with complete proof

4. **Verify** with `lake build`

## Reference: Lambda/Term.lean

The de Bruijn infrastructure is in `Metatheory/Lambda/Term.lean`. Key lemmas:
- Lines 94-106: `shift_zero`
- Lines 123-145: `shift_shift`
- Lines 152-176: `shift_shift_succ`
- Lines 272-297: `subst_shift_cancel`
- Lines 328-415: `shift_subst_at` (generalized shift-substitution)
- Lines 578-705: `subst_subst_gen_full` (THE key lemma, ~90 lines)

## Debugging Tips

1. **Unfold definitions**: Use `simp only [shift, subst]` to see structure
2. **Check Int vs Nat**: Shift uses Int for the amount, be careful with coercions
3. **Print intermediate goals**: Use `trace` or break into smaller lemmas
4. **Compare with existing**: Look at similar lemmas in Term.lean
