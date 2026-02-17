/-
# Combinatory Logic - Reduction

This module defines one-step and multi-step weak reduction for CL.

## Reduction Rules

- **K-reduction**: Kxy → x
- **S-reduction**: Sxyz → xz(yz)

Plus congruence rules for reducing inside applications.

## References

- Hindley & Seldin, "Lambda-Calculus and Combinators" (2008)
- Barendregt, "The Lambda Calculus" (1984), Chapter 7
-/

import Metatheory.CL.Syntax
import Metatheory.Rewriting.Basic

namespace Metatheory.CL

open Term

/-! ## One-Step Weak Reduction -/

/-- One-step weak reduction for Combinatory Logic.

    The two basic contractions are:
    - K M N → M
    - S M N P → (M P) (N P)

    Plus congruence rules for reducing inside applications. -/
inductive WeakStep : Term → Term → Prop where
  | k_red : ∀ (M N : Term), WeakStep (K ⬝ M ⬝ N) M
  | s_red : ∀ (M N P : Term), WeakStep (S ⬝ M ⬝ N ⬝ P) ((M ⬝ P) ⬝ (N ⬝ P))
  | appL : ∀ {M M' N : Term}, WeakStep M M' → WeakStep (M ⬝ N) (M' ⬝ N)
  | appR : ∀ {M N N' : Term}, WeakStep N N' → WeakStep (M ⬝ N) (M ⬝ N')

/-- Notation for one-step reduction -/
scoped infix:50 " ⟶ " => WeakStep

/-! ## Multi-Step Reduction -/

/-- Multi-step weak reduction (reflexive-transitive closure) -/
abbrev MultiStep : Term → Term → Prop := Rewriting.Star WeakStep

/-- Notation for multi-step reduction -/
scoped infix:50 " ⟶* " => MultiStep

namespace MultiStep

/-- Reflexivity -/
theorem refl (M : Term) : M ⟶* M := Rewriting.Star.refl M

/-- Single step implies multi-step -/
theorem single {M N : Term} (h : M ⟶ N) : M ⟶* N := Rewriting.Star.single h

/-- Transitivity -/
theorem trans {M N P : Term} (h1 : M ⟶* N) (h2 : N ⟶* P) : M ⟶* P :=
  Rewriting.Star.trans h1 h2

/-- Head step -/
theorem head {M N P : Term} (h1 : M ⟶ N) (h2 : N ⟶* P) : M ⟶* P :=
  Rewriting.Star.head h1 h2

/-- Tail step -/
theorem tail {M N P : Term} (h1 : M ⟶* N) (h2 : N ⟶ P) : M ⟶* P :=
  Rewriting.Star.tail h1 h2

/-- Left congruence for multi-step -/
theorem appL {M M' N : Term} (h : M ⟶* M') : (M ⬝ N) ⟶* (M' ⬝ N) := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact tail ih (WeakStep.appL hstep)

/-- Right congruence for multi-step -/
theorem appR {M N N' : Term} (h : N ⟶* N') : (M ⬝ N) ⟶* (M ⬝ N') := by
  induction h with
  | refl => exact refl _
  | tail _ hstep ih => exact tail ih (WeakStep.appR hstep)

/-- Full congruence: if M ⟶* M' and N ⟶* N' then M·N ⟶* M'·N' -/
theorem app {M M' N N' : Term} (hM : M ⟶* M') (hN : N ⟶* N') :
    (M ⬝ N) ⟶* (M' ⬝ N') :=
  trans (appL hM) (appR hN)

end MultiStep

/-! ## Combinator Identities -/

/-- The I combinator is the identity: I x →* x.
    Proof: SKKx → Kx(Kx) → x -/
theorem I_identity (x : Term) : (I ⬝ x) ⟶* x := by
  -- I = SKK, so I x = SKK x
  unfold I
  -- SKK x → Kx (Kx) by s_red
  apply MultiStep.head (WeakStep.s_red K K x)
  -- Kx (Kx) → x by k_red
  apply MultiStep.single (WeakStep.k_red x (K ⬝ x))

/-- The K combinator projects to its first argument: K x y →* x.
    This is immediate from the reduction rule. -/
theorem K_identity (x y : Term) : (K ⬝ x ⬝ y) ⟶* x :=
  MultiStep.single (WeakStep.k_red x y)

/-- The S combinator distributes: S x y z →* (x z) (y z).
    This is immediate from the reduction rule. -/
theorem S_identity (x y z : Term) : (S ⬝ x ⬝ y ⬝ z) ⟶* ((x ⬝ z) ⬝ (y ⬝ z)) :=
  MultiStep.single (WeakStep.s_red x y z)

/-- The B combinator composes functions: B f g x →* f (g x).
    Proof: S(KS)K f g x → (KS f) g x (K f g x)
         → S g (K f g x) → S g f x → ... -/
theorem B_identity (f g x : Term) : (B ⬝ f ⬝ g ⬝ x) ⟶* (f ⬝ (g ⬝ x)) := by
  -- B = S(KS)K, so B f g x = S(KS)K f g x
  unfold B
  -- S(KS)K f g x → ((KS) f g) (K f g) x
  -- First: S(KS)K f → (KS f) (K f)
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.appL (WeakStep.s_red (K ⬝ S) K f))
  -- Now we have ((KS f) (K f)) g x
  -- KS f → S
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.appL (WeakStep.appL (WeakStep.k_red S f)))
  -- Now we have (S (K f)) g x
  -- S (K f) g x → ((K f) x) (g x)
  apply MultiStep.head
  · exact WeakStep.s_red (K ⬝ f) g x
  -- Now we have ((K f) x) (g x)
  -- (K f) x → f
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.k_red f x)
  -- Now we have f (g x)
  exact MultiStep.refl _

/-- The W combinator duplicates: W x y →* x y y.
    Proof: SS(SK)xy → Sx(SKx)y → xy(SKxy) → xy(Ky(xy)) → xyy -/
theorem W_identity (x y : Term) : (W ⬝ x ⬝ y) ⟶* (x ⬝ y ⬝ y) := by
  -- W = SS(SK), so W x y = SS(SK) x y
  unfold W
  -- SS(SK) x → Sx(SKx) by s_red
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.s_red S (S ⬝ K) x)
  -- Sx(SKx) y → xy(SKxy) by s_red
  apply MultiStep.head
  · exact WeakStep.s_red x (S ⬝ K ⬝ x) y
  -- SKxy → Ky(xy) by s_red
  apply MultiStep.head
  · exact WeakStep.appR (WeakStep.s_red K x y)
  -- Ky(xy) → y by k_red
  apply MultiStep.head
  · exact WeakStep.appR (WeakStep.k_red y (x ⬝ y))
  exact MultiStep.refl _

/-- The C combinator flips arguments: C x y z →* x z y.
    C = S(S(KB)S)(KK), proof uses B reduction internally. -/
theorem C_identity (x y z : Term) : (C ⬝ x ⬝ y ⬝ z) ⟶* (x ⬝ z ⬝ y) := by
  -- C = S(S(KB)S)(KK) where B = S(KS)K
  unfold C B
  -- S(S(K(S(KS)K))S)(KK) x y z
  -- Step 1: S(S(KB)S)(KK) x → (S(KB)S x) ((KK) x)
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.appL (WeakStep.s_red (S ⬝ (K ⬝ (S ⬝ (K ⬝ S) ⬝ K)) ⬝ S) (K ⬝ K) x))
  -- Step 2: (KK) x → K
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.appL (WeakStep.appR (WeakStep.k_red K x)))
  -- Now: (S(KB)S x) K y z
  -- Step 3: S(KB)S x → (KB x) (S x)
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.appL (WeakStep.appL (WeakStep.s_red (K ⬝ (S ⬝ (K ⬝ S) ⬝ K)) S x)))
  -- Step 4: KB x → B (via K-red)
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.appL (WeakStep.appL (WeakStep.appL (WeakStep.k_red (S ⬝ (K ⬝ S) ⬝ K) x))))
  -- Now: (B (Sx)) K y z = S(KS)K (Sx) K y z
  -- Step 5: S(KS)K (Sx) → (KS (Sx)) (K (Sx))
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.appL (WeakStep.appL (WeakStep.s_red (K ⬝ S) K (S ⬝ x))))
  -- Step 6: KS (Sx) → S
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.appL (WeakStep.appL (WeakStep.appL (WeakStep.k_red S (S ⬝ x)))))
  -- Now: (S (K(Sx))) K y z
  -- Step 7: S (K(Sx)) K y → (K(Sx) y) (K y)
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.s_red (K ⬝ (S ⬝ x)) K y)
  -- Step 8: K(Sx) y → Sx
  apply MultiStep.head
  · exact WeakStep.appL (WeakStep.appL (WeakStep.k_red (S ⬝ x) y))
  -- Now: (Sx (Ky)) z
  -- Step 9: Sx (Ky) z → (x z) ((Ky) z)
  apply MultiStep.head
  · exact WeakStep.s_red x (K ⬝ y) z
  -- Step 10: (Ky) z → y
  apply MultiStep.head
  · exact WeakStep.appR (WeakStep.k_red y z)
  -- Now: (x z) y = x z y
  exact MultiStep.refl _

end Metatheory.CL
