# Add Typed System

Create a new typed lambda calculus variant with typing rules, subject reduction, and potentially strong normalization.

## Arguments
- $ARGUMENTS: Description of the type system (e.g., "System T", "PCF", "System F")

## Instructions

1. **Analyze the request**: Determine the type system from: $ARGUMENTS

2. **Create directory structure**: `Metatheory/<Name>/`
   - `Types.lean` - Type syntax
   - `Terms.lean` - Term syntax (or re-export from Lambda)
   - `Typing.lean` - Typing rules and subject reduction
   - `Normalization.lean` - Strong normalization (if applicable)

3. **Implement Types**

```lean
/-
# <Name> - Types

Type syntax for <Name>.
-/

namespace Metatheory.<Name>

/-- Type syntax -/
inductive Ty : Type where
  | base : String → Ty          -- Base types
  | arr : Ty → Ty → Ty          -- Function types
  -- Add other type constructors as needed
  deriving Repr, DecidableEq

notation:50 A " ⇒ " B => Ty.arr A B

end Metatheory.<Name>
```

4. **Implement Typing Rules**

```lean
/-- Typing context -/
def Context := List Ty

/-- Typing judgment: Γ ⊢ M : A -/
inductive HasType : Context → Term → Ty → Prop where
  | var : Γ.get? n = some A → HasType Γ (var n) A
  | app : HasType Γ M (A ⇒ B) → HasType Γ N A → HasType Γ (app M N) B
  | lam : HasType (A :: Γ) M B → HasType Γ (lam M) (A ⇒ B)
  -- Add rules for other term formers
```

5. **Prove Subject Reduction**

```lean
/-- Type preservation under reduction -/
theorem subject_reduction : HasType Γ M A → BetaStep M N → HasType Γ N A := by
  intro htype hstep
  induction hstep generalizing Γ A with
  | beta M' N' =>
    -- Key case: (λM)N → M[N]
    -- Need substitution lemma
    ...
  | appL hstep ih => ...
  | appR hstep ih => ...
  | lam hstep ih => ...
```

Key lemma needed:
```lean
/-- Substitution preserves typing -/
theorem substitution_lemma :
    HasType (A :: Γ) M B → HasType Γ N A → HasType Γ (subst0 N M) B
```

6. **Prove Progress** (for closed terms)

```lean
/-- Values: canonical forms -/
def IsValue : Term → Prop
  | lam _ => True
  | _ => False

/-- Closed well-typed terms are values or can step -/
theorem progress : HasType [] M A → IsValue M ∨ ∃ N, BetaStep M N
```

7. **Strong Normalization** (if type system guarantees it)

Follow the pattern in `/strong-normalization` command:
- Define reducibility predicate
- Prove CR properties
- Prove fundamental lemma
- Conclude SN

## Systems Where SN Holds
- STLC (simple types)
- System T (Gödel's T)
- System F (polymorphic, requires candidates)

## Systems Where SN Fails
- Untyped lambda calculus
- PCF with fixpoint
- System F with impredicativity issues

## Checklist

- [ ] Type syntax with notation
- [ ] Typing rules
- [ ] Context operations (lookup, extension)
- [ ] Substitution lemma
- [ ] Subject reduction theorem
- [ ] Progress theorem
- [ ] Strong normalization (if applicable)
- [ ] Update `Metatheory.lean` imports
- [ ] All proofs complete
- [ ] Build passes
