# Strong Normalization

Guide for proving strong normalization (termination) for typed lambda calculi.

## Arguments
- $ARGUMENTS: The type system to prove SN for, or specific question about SN proofs

## Instructions

1. **Understand the type system** from: $ARGUMENTS

2. **Choose proof technique**:

### Logical Relations (Tait's Method)
Best for: STLC, System T, simple type systems

Key steps:
1. Define `Reducible A M` (reducibility predicate indexed by type)
2. Prove CR properties (CR1, CR2, CR3)
3. Prove fundamental lemma
4. Conclude SN

### Candidates of Reducibility (Girard's Method)
Best for: System F, polymorphic systems

Key steps:
1. Define reducibility candidates (sets with closure properties)
2. Interpret types as candidates
3. Prove adequacy lemma
4. Conclude SN

3. **Implementation for Logical Relations**

### Step 1: Define Reducibility
```lean
def Reducible : Ty → Term → Prop
  | Ty.base _, M => SN M
  | Ty.arr A B, M => ∀ N, Reducible A N → Reducible B (app M N)
```

### Step 2: CR Properties

**CR1**: Reducible implies SN
```lean
theorem cr1_reducible_sn (A : Ty) (M : Term) (h : Reducible A M) : SN M
```

**CR2**: Reducibility closed under reduction
```lean
theorem cr2_reducible_red (A : Ty) :
    ∀ M N, Reducible A M → BetaStep M N → Reducible A N
```

**CR3**: Neutral terms with reducible reducts are reducible
```lean
theorem cr3_neutral (A : Ty) (M : Term)
    (h_red : ∀ N, BetaStep M N → Reducible A N)
    (h_neut : IsNeutral M) : Reducible A M
```

### Step 3: Key Lemma for Lambda Case
```lean
theorem reducible_app_lam : ∀ (B : Ty) (M N : Term),
    SN M → SN N →
    Reducible B (subst0 N M) →
    (∀ M', BetaStep M M' → Reducible B (subst0 N M')) →
    (∀ N', BetaStep N N' → Reducible B (subst0 N' M)) →
    Reducible B (app (lam M) N)
```

This is THE hard lemma. Prove by nested well-founded induction on SN M and SN N.

### Step 4: Fundamental Lemma
```lean
theorem fundamental_lemma : ∀ {Γ : Context} {M : Term} {A : Ty} {σ : Nat → Term},
    HasType Γ M A →
    ReducibleSubst Γ σ →
    Reducible A (applySubst σ M)
```

### Step 5: Strong Normalization
```lean
theorem strong_normalization {Γ : Context} {M : Term} {A : Ty}
    (h : HasType Γ M A) : SN M := by
  have hσ : ReducibleSubst Γ idSubst := fun n B _ => var_reducible n B
  have hred : Reducible A (applySubst idSubst M) := fundamental_lemma h hσ
  rw [applySubst_id] at hred
  exact cr1_reducible_sn A M hred
```

## Reference Implementation

See `Metatheory/STLC/Normalization.lean` for the complete proof (~1200 lines).

Key sections:
- Lines 35-52: SN definition and basic properties
- Lines 278-288: Reducible definition
- Lines 300-427: CR properties (mutual proof)
- Lines 444-552: reducible_app_lam (the hard lemma)
- Lines 1078-1170: fundamental_lemma
- Lines 1184-1195: strong_normalization

## Checklist

- [ ] SN definition (as Acc)
- [ ] Reducible predicate
- [ ] CR1 (reducible → SN)
- [ ] CR2 (closed under reduction)
- [ ] CR3 (neutral + reducible reducts → reducible)
- [ ] Substitution infrastructure
- [ ] reducible_app_lam lemma
- [ ] fundamental_lemma
- [ ] strong_normalization theorem
- [ ] All proofs complete
