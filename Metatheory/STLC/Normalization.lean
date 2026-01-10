/-
# Simply Typed Lambda Calculus - Strong Normalization

This module proves strong normalization for STLC: every well-typed
term terminates (all reduction sequences are finite).

## Strategy: Logical Relations (Reducibility Candidates)

The proof uses Tait's method of logical relations (also called reducibility):

1. Define a predicate `Reducible A M` for each type A
2. Show reducibility conditions (CR1, CR2, CR3)
3. Prove the fundamental lemma: well-typed terms are reducible
4. Conclude: reducible terms are strongly normalizing

## References

- Tait, "Intensional Interpretations of Functionals of Finite Type" (1967)
- Girard, "Interprétation fonctionnelle et élimination des coupures" (1972)
- Pierce, "Types and Programming Languages" (2002), Chapter 12
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

import Metatheory.STLC.Typing
import Metatheory.Rewriting.Basic
import Metatheory.Lambda.Generic

namespace Metatheory.STLC

open Lambda Rewriting

/-! ## Strong Normalization Definition -/

/-- A term is strongly normalizing if all reduction sequences from it terminate.
    Formally: M is SN iff M is accessible in the inverse reduction relation. -/
def SN (M : Term) : Prop := Acc (fun a b => BetaStep b a) M

/-! ## Normal Forms -/

/-- Strong normalization implies existence of a β-normal form (as a generic `Rewriting.HasNormalForm`). -/
theorem hasNormalForm_of_SN {M : Term} (hM : SN M) : Rewriting.HasNormalForm BetaStep M :=
  Rewriting.hasNormalForm_of_acc hM

/-! ## Basic SN Properties -/

/-- Variables are strongly normalizing (they don't reduce) -/
theorem sn_var (n : Nat) : SN (Term.var n) := by
  constructor
  intro y hy
  cases hy  -- No reduction from a variable

/-- If M is SN, then any reduct N is also SN -/
theorem sn_of_step {M N : Term} (hM : SN M) (h : BetaStep M N) : SN N :=
  Acc.inv hM h

/-- SN terms can be constructed by showing all reducts are SN -/
theorem sn_intro {M : Term} (h : ∀ N, BetaStep M N → SN N) : SN M :=
  Acc.intro M h

/-! ## Neutral Terms -/

/-- A term is neutral if it cannot be the function in a beta redex.
    Variables and applications (where the function is not a lambda) are neutral.
    Lambdas are NOT neutral because when applied, they form a redex. -/
def IsNeutral : Term → Prop
  | Term.var _ => True
  | Term.app (Term.lam _) _ => False
  | Term.app _ _ => True
  | Term.lam _ => False

/-- Variables are neutral -/
theorem neutral_var (n : Nat) : IsNeutral (Term.var n) := trivial

/-- Applications where the function is not a lambda are neutral -/
theorem neutral_app_of_not_lam {M N : Term} (h : ∀ M', M ≠ Term.lam M') :
    IsNeutral (Term.app M N) := by
  unfold IsNeutral
  cases M with
  | var _ => trivial
  | app _ _ => trivial
  | lam M' => exact absurd rfl (h M')

/-- Neutral terms are not beta redexes -/
theorem neutral_not_redex {M : Term} (h : IsNeutral M) :
    ∀ M' N, M ≠ Term.app (Term.lam M') N := by
  intro M' N heq
  cases M with
  | var _ => cases heq
  | lam _ => exact h
  | app M1 M2 =>
    cases M1 with
    | var _ => cases heq
    | app _ _ => cases heq
    | lam _ => exact h

/-- If neutral M and app M N is neutral, beta reduction of app M N
    must come from reducing M or N, not from beta. -/
theorem neutral_app_step {M N P : Term} (hM : IsNeutral M) (hstep : BetaStep (Term.app M N) P) :
    (∃ M', BetaStep M M' ∧ P = Term.app M' N) ∨ (∃ N', BetaStep N N' ∧ P = Term.app M N') := by
  cases hstep with
  | beta M' N' =>
    -- M = lam M', but M is neutral, contradiction
    unfold IsNeutral at hM
    exact False.elim hM
  | appL hM' =>
    exact Or.inl ⟨_, hM', rfl⟩
  | appR hN' =>
    exact Or.inr ⟨_, hN', rfl⟩

/-- If app M N is SN, then M is SN (left projection of SN) -/
theorem sn_app_left {M N : Term} (h : SN (Term.app M N)) : SN M := by
  -- Prove by Acc.rec on the accessibility proof
  have : ∀ T, SN T → ∀ M N, T = Term.app M N → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N hTeq
      subst hTeq
      apply sn_intro
      intro M' hM'
      exact ih (Term.app M' N) (BetaStep.appL hM') M' N rfl
  exact this (Term.app M N) h M N rfl

/-- Application of neutral M to SN term preserves SN from result to function -/
theorem sn_of_app_neutral {M N : Term} (hMN : SN (Term.app M N)) : SN M :=
  sn_app_left hMN

/-- If app M N is SN, then N is SN -/
theorem sn_app_right {M N : Term} (h : SN (Term.app M N)) : SN N := by
  have : ∀ T, SN T → ∀ M N, T = Term.app M N → SN N := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N hTeq
      subst hTeq
      apply sn_intro
      intro N' hN'
      exact ih (Term.app M N') (BetaStep.appR hN') M N' rfl
  exact this (Term.app M N) h M N rfl

/-- If lam M reduces to lam M', then M reduces to M' -/
theorem lam_step_inv {M M' : Term} (h : BetaStep (Term.lam M) (Term.lam M')) : BetaStep M M' := by
  cases h with
  | lam hM => exact hM

/-- Helper lemma: substitution at any level preserves beta reduction -/
private theorem subst_preserves_step (j : Nat) {M M' N : Term} (hstep : BetaStep M M') :
    BetaStep (Term.subst j N M) (Term.subst j N M') := by
  induction hstep generalizing j N with
  | beta M₁ N₁ =>
    simp only [Term.subst]
    rw [← Term.subst_subst_gen]
    apply BetaStep.beta
  | appL hstep_M₁ ih =>
    simp only [Term.subst]
    apply BetaStep.appL
    apply ih
  | appR hstep_M₂ ih =>
    simp only [Term.subst]
    apply BetaStep.appR
    apply ih
  | lam hstep_M ih =>
    simp only [Term.subst]
    apply BetaStep.lam
    apply ih

/-- Substitution preserves beta reduction: if M →β M', then M[N] →β M'[N].

    Standard compatibility lemma. Proved by induction on the BetaStep derivation.

    References:
    - Barendregt "The Lambda Calculus" Lemma 3.2.4
    - Pierce TAPL Chapter 6 -/
theorem subst0_step_left {M M' N : Term} (hstep : BetaStep M M') :
    BetaStep (Term.subst0 N M) (Term.subst0 N M') := by
  unfold Term.subst0
  exact subst_preserves_step 0 hstep

/-- Helper lemma: shift preserves beta reduction -/
private theorem shift_preserves_step (d : Nat) (c : Nat) {M M' : Term} (hstep : BetaStep M M') :
    BetaStep (Term.shift d c M) (Term.shift d c M') := by
  induction hstep generalizing c with
  | beta M N =>
    simp only [Term.shift, Term.subst0]
    -- Need to show: (lam (shift d (c+1) M)) (shift d c N) →β shift d c (subst 0 N M)
    -- By the shift_subst lemma: shift d c (subst 0 N M) = subst 0 (shift d c N) (shift d (c+1) M)
    rw [Term.shift_subst]
    apply BetaStep.beta
  | appL _ ih =>
    simp only [Term.shift]
    apply BetaStep.appL
    apply ih
  | appR _ ih =>
    simp only [Term.shift]
    apply BetaStep.appR
    apply ih
  | lam _ ih =>
    simp only [Term.shift]
    apply BetaStep.lam
    apply ih

/-- Helper to lift Star steps under appL -/
private def star_appL {M M' N : Term} (h : Rewriting.Star BetaStep M M') :
    Rewriting.Star BetaStep (Term.app M N) (Term.app M' N) := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hbc ih => exact Rewriting.Star.tail ih (BetaStep.appL hbc)

/-- Helper to lift Star steps under appR -/
private def star_appR {M N N' : Term} (h : Rewriting.Star BetaStep N N') :
    Rewriting.Star BetaStep (Term.app M N) (Term.app M N') := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hbc ih => exact Rewriting.Star.tail ih (BetaStep.appR hbc)

/-- Helper to lift Star steps under lam -/
private def star_lam {M M' : Term} (h : Rewriting.Star BetaStep M M') :
    Rewriting.Star BetaStep (Term.lam M) (Term.lam M') := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hbc ih => exact Rewriting.Star.tail ih (BetaStep.lam hbc)

/-- Substitution preserves beta reduction in argument: if N →β N', then M[N] →* M[N'].

    Standard compatibility lemma. Proved by induction on M.
    Note: This produces a multi-step reduction (Star) because when M is a lambda,
    we need to propagate the reduction through shifts.

    References:
    - Barendregt "The Lambda Calculus" -/
theorem subst0_step_right {M N N' : Term} (hstep : BetaStep N N') :
    Rewriting.Star BetaStep (Term.subst0 N M) (Term.subst0 N' M) := by
  -- We prove a more general version by induction on M
  suffices ∀ (j : Nat) (N N' M : Term), BetaStep N N' →
      Rewriting.Star BetaStep (Term.subst j N M) (Term.subst j N' M) by
    exact this 0 N N' M hstep
  intro j N₀ N₀' M₀ hstep₀
  induction M₀ generalizing j N₀ N₀' with
  | var n =>
    simp only [Term.subst]
    by_cases h : n = j
    · simp only [h, ite_true]
      -- With corrected substitution, subst j N₀ (var j) = N₀ directly
      exact Rewriting.Star.single hstep₀
    · simp only [h, ite_false]
      exact Rewriting.Star.refl _
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [Term.subst]
    have h1 := ih₁ j N₀ N₀' hstep₀
    have h2 := ih₂ j N₀ N₀' hstep₀
    -- Combine reductions: first reduce M₁, then reduce M₂
    exact Rewriting.Star.trans (star_appL h1) (star_appR h2)
  | lam M₁ ih =>
    simp only [Term.subst]
    -- shift1 preserves beta reduction
    have hshift := shift_preserves_step 1 0 hstep₀
    -- Apply IH with shifted terms and lift under lambda
    exact star_lam (ih (j + 1) (Term.shift1 N₀) (Term.shift1 N₀') hshift)

/-- If M is SN and lam M →β T, then T = lam M' for some M' with M →β M' -/
theorem lam_step_form {M T : Term} (h : BetaStep (Term.lam M) T) :
    ∃ M', T = Term.lam M' ∧ BetaStep M M' := by
  cases h with
  | lam hM => exact ⟨_, rfl, hM⟩

/-- SN is closed under multi-step reduction -/
theorem sn_of_multi {M N : Term} (hM : SN M) (h : Rewriting.Star BetaStep M N) : SN N := by
  induction h with
  | refl => exact hM
  | tail _ hstep ih => exact sn_of_step ih hstep

/-- If lam M is SN, then M is SN -/
theorem sn_lam_inv {M : Term} (h : SN (Term.lam M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = Term.lam M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hTeq
      subst hTeq
      apply sn_intro
      intro M' hM'
      exact ih (Term.lam M') (BetaStep.lam hM') M' rfl
  exact this (Term.lam M) h M rfl

/-! ## Reducibility (Logical Relations) -/

/-- Reducibility predicate indexed by type.

    The key innovation of Tait's method is this definition:
    - Base types: reducible = strongly normalizing
    - Arrow types: M ∈ RED(A→B) iff ∀N ∈ RED(A), M N ∈ RED(B) -/
def Reducible : Ty → Term → Prop
  | Ty.base _, M => SN M
  | Ty.arr A B, M => ∀ N, Reducible A N → Reducible B (Term.app M N)

/-! ## Reducibility Conditions (CR1, CR2, CR3)

These are the key properties of reducibility candidates. The proofs require
careful mutual induction on type structure.

References:
- Girard, Lafont & Taylor "Proofs and Types" Section 6.2
- Pierce TAPL Chapter 12 -/

/-- CR2: Reducibility is closed backward under reduction.
    If M is reducible and M → N, then N is reducible. -/
theorem cr2_reducible_red (A : Ty) : ∀ M N, Reducible A M → BetaStep M N → Reducible A N := by
  induction A with
  | base n =>
    intro M N hM hstep
    exact sn_of_step hM hstep
  | arr A B ihA ihB =>
    intro M N hM hstep P hP
    exact ihB (Term.app M P) (Term.app N P) (hM P hP) (BetaStep.appL hstep)

/-- CR2 extended to multi-step reduction -/
theorem cr2_reducible_red_multi (A : Ty) (M N : Term)
    (hM : Reducible A M) (hstep : Rewriting.Star BetaStep M N) : Reducible A N := by
  induction hstep with
  | refl => exact hM
  | tail _ h ih => exact cr2_reducible_red A _ _ ih h

/-! ## CR1 and CR3: Mutual Proof by Well-Founded Induction -/

/-- The combined CR1 and CR3 properties for a type -/
def CR_Props (A : Ty) : Prop :=
  (∀ M, Reducible A M → SN M) ∧
  (∀ M, (∀ N, BetaStep M N → Reducible A N) → IsNeutral M → Reducible A M)

/-- CR3 for base types: neutral terms with SN reducts are SN -/
theorem cr3_base (n : Nat) (M : Term)
    (h_red : ∀ N, BetaStep M N → Reducible (Ty.base n) N)
    (_h_neut : IsNeutral M) : Reducible (Ty.base n) M := by
  -- Reducible at base type = SN
  unfold Reducible
  apply sn_intro
  intro N hN
  exact h_red N hN

/-- CR1 and CR3 hold for all types (mutual proof by well-founded induction on type size) -/
theorem cr_props_all : ∀ A, CR_Props A := by
  intro A
  -- Well-founded induction on type size
  induction A using Ty.rec with
  | base n =>
    constructor
    · -- CR1 for base: trivial (Reducible = SN)
      intro M hM
      exact hM
    · -- CR3 for base
      intro M h_red h_neut
      exact cr3_base n M h_red h_neut
  | arr A B ihA ihB =>
    obtain ⟨cr1_A, cr3_A⟩ := ihA
    obtain ⟨cr1_B, cr3_B⟩ := ihB
    constructor
    · -- CR1 for A ⇒ B: need to show Reducible (A ⇒ B) M → SN M
      intro M hM
      -- Apply M to a reducible neutral term and use cr1_B
      -- var 0 is neutral with no reducts, so by cr3_A, var 0 is reducible at A
      have h_var_red : Reducible A (Term.var 0) := by
        apply cr3_A
        · intro N hN; cases hN  -- var 0 has no reducts
        · exact neutral_var 0
      -- Since M is reducible at A ⇒ B, app M (var 0) is reducible at B
      have h_app_red : Reducible B (Term.app M (Term.var 0)) := hM (Term.var 0) h_var_red
      -- By cr1_B, app M (var 0) is SN
      have h_app_sn : SN (Term.app M (Term.var 0)) := cr1_B (Term.app M (Term.var 0)) h_app_red
      -- From SN (app M (var 0)), we get SN M
      exact sn_app_left h_app_sn
    · -- CR3 for A ⇒ B: need to show neutral M with reducible reducts is reducible
      intro M h_red h_neut
      -- Need: ∀ N, Reducible A N → Reducible B (app M N)
      intro P hP
      -- By cr1_A, P is SN. We use strong induction on SN P.
      have hP_sn : SN P := cr1_A P hP
      -- We prove: for all SN Q that are reducible at A, app M Q is reducible at B
      suffices h : ∀ Q, SN Q → Reducible A Q → Reducible B (Term.app M Q) by
        exact h P hP_sn hP
      intro Q hQ_sn
      induction hQ_sn with
      | intro Q' hQ'_acc ih =>
        intro hQ'_red
        -- Need: Reducible B (app M Q')
        -- app M Q' is neutral (since M is neutral, M is not a lambda)
        -- All reducts of app M Q' are reducible at B
        apply cr3_B
        · -- All reducts of app M Q' are reducible at B
          intro R hR
          -- Since M is neutral, app M Q' reduces by appL or appR, not beta
          rcases neutral_app_step h_neut hR with ⟨M', hM', hReq⟩ | ⟨Q'', hQ'', hReq⟩
          · -- appL: M → M', R = app M' Q'
            subst hReq
            -- M' is reducible at A ⇒ B by h_red
            exact h_red M' hM' Q' hQ'_red
          · -- appR: Q' → Q'', R = app M Q''
            subst hReq
            -- Q'' is reducible at A by CR2 for A
            have hQ''_red : Reducible A Q'' := cr2_reducible_red A Q' Q'' hQ'_red hQ''
            -- By IH (Q'' is accessible from Q'), app M Q'' is reducible at B
            exact ih Q'' hQ'' hQ''_red
        · -- app M Q' is neutral
          -- M is neutral means M is not a lambda
          -- So app M Q' is not of the form app (lam _) _
          cases M with
          | var n => exact trivial
          | app M1 M2 =>
            -- M = app M1 M2, which is neutral, so M1 is not a lambda
            unfold IsNeutral at h_neut
            cases M1 with
            | var _ => exact trivial
            | app _ _ => exact trivial
            | lam _ => exact False.elim h_neut
          | lam M' =>
            -- M = lam M' contradicts h_neut (IsNeutral (lam _) = False)
            exact False.elim h_neut

/-- CR1: Reducible terms are strongly normalizing -/
theorem cr1_reducible_sn (A : Ty) (M : Term) (h : Reducible A M) : SN M :=
  (cr_props_all A).1 M h

/-- CR3 with IsNeutral requirement: Neutral terms with all reducts reducible are reducible.

    This is the core CR3 property. It requires IsNeutral, which ensures:
    - M is a variable, or
    - M is an application where the function is not a lambda

    Lambdas are NOT neutral and should not use CR3; their reducibility is
    established via the fundamental lemma which uses typing information. -/
theorem cr3_neutral (A : Ty) (M : Term)
    (h_red : ∀ N, BetaStep M N → Reducible A N)
    (h_neut : IsNeutral M) :
    Reducible A M :=
  (cr_props_all A).2 M h_red h_neut

/-- Key lemma: reducibility of beta redexes.

    If the body M is SN, N is SN, the beta reduct (M[N]) is reducible, all body
    reducts produce reducible substitutions, and all argument reducts produce
    reducible substitutions, then (λM)N is reducible.

    The proof uses well-founded induction on (SN M, SN N) lexicographically,
    with type casing inside.

    Note: SN N is required as an explicit hypothesis. At the call site in
    fundamental_lemma, N is reducible, hence SN by CR1.

    References:
    - Girard, Lafont & Taylor "Proofs and Types" Lemma 6.2.4
    - Tait "Intensional Interpretations of Functionals" (1967) -/
theorem reducible_app_lam : ∀ (B : Ty) (M N : Term),
    SN M →
    SN N →
    Reducible B (Term.subst0 N M) →
    (∀ M', BetaStep M M' → Reducible B (Term.subst0 N M')) →
    (∀ N', BetaStep N N' → Reducible B (Term.subst0 N' M)) →
    Reducible B (Term.app (Term.lam M) N) := by
  intro B
  -- Well-founded induction on type B
  induction B with
  | base n =>
    -- Base type case: Reducible (base n) means SN
    intro M N hM_sn hN_sn hbeta_red hM'_red hN'_red
    unfold Reducible at hbeta_red hM'_red hN'_red
    -- Use nested induction on SN M and SN N
    induction hM_sn generalizing N with
    | intro M hM_acc ihM =>
      -- Hypotheses N, hN_sn, hbeta_red, hM'_red, hN'_red are already in context
      induction hN_sn with
      | intro N hN_acc ihN =>
        apply sn_intro
        intro P hP
        cases hP with
        | beta => exact hbeta_red
        | appL hstep_lam =>
          cases hstep_lam with
          | lam hM'' =>
            -- M → M'', apply ihM
            apply ihM _ hM'' N (Acc.intro N hN_acc)
            · exact hM'_red _ hM''
            · intro M''' hM'''
              exact sn_of_step (hM'_red _ hM'') (subst0_step_left hM''')
            · intro N' hN'_step
              exact sn_of_step (hN'_red N' hN'_step) (subst0_step_left hM'')
        | appR hN'' =>
          -- N → N'', apply ihN
          apply ihN _ hN''
          · exact hN'_red _ hN''
          · intro M' hM'_step
            exact sn_of_multi (hM'_red M' hM'_step) (subst0_step_right hN'')
          · intro N' hN'_step
            exact sn_of_multi (hN'_red _ hN'') (subst0_step_right hN'_step)

  | arr A C _ihA ihC =>
    -- Arrow type case: Reducible (A ⇒ C) means ∀ P reducible at A, app _ P reducible at C
    intro M N hM_sn hN_sn hbeta_red hM'_red hN'_red
    -- Need: ∀ P, Reducible A P → Reducible C (app (app (lam M) N) P)
    intro P hP

    -- SN P from CR1
    have hP_sn : SN P := cr1_reducible_sn A P hP

    -- app (app (lam M) N) P is NEUTRAL because app (lam M) N is an application, not a lambda
    have h_neutral : IsNeutral (Term.app (Term.app (Term.lam M) N) P) := by
      unfold IsNeutral
      trivial

    -- Use CR3: neutral terms with reducible reducts are reducible
    apply cr3_neutral C _ _ h_neutral

    -- Nested induction on SN M, SN N, SN P
    induction hM_sn generalizing N P with
    | intro M hM_acc ihM =>
      -- Hypotheses N, hN_sn, hbeta_red, hM'_red, hN'_red, P, hP, hP_sn, h_neutral are in context
      induction hN_sn generalizing P with
      | intro N hN_acc ihN =>
        induction hP_sn with
        | intro P hP_acc ihP =>
          intro Q hQ
          cases hQ with
          | appL hstep_inner =>
            cases hstep_inner with
            | beta =>
              -- inner beta: Q = app (subst0 N M) P
              exact hbeta_red P hP
            | appL hstep_lam =>
              cases hstep_lam with
              | @lam M_body M'_body hM' =>
                -- M → M'_body under lam, Q = app (app (lam M'_body) N) P
                -- Q is neutral, use CR3 + ihM
                have hbeta_red' : Reducible (Ty.arr A C) (Term.subst0 N M'_body) := hM'_red M'_body hM'
                have hM''_red : ∀ M'', M'_body →β M'' → Reducible (Ty.arr A C) (Term.subst0 N M'') := fun M'' hM'' =>
                  cr2_reducible_red (Ty.arr A C) _ _ hbeta_red' (subst0_step_left hM'')
                have hN'_red' : ∀ N', N →β N' → Reducible (Ty.arr A C) (Term.subst0 N' M'_body) := fun N' hN' =>
                  cr2_reducible_red (Ty.arr A C) _ _ (hN'_red N' hN') (subst0_step_left hM')
                have h_neutral' : IsNeutral (Term.app (Term.app (Term.lam M'_body) N) P) := by
                  unfold IsNeutral; trivial
                apply cr3_neutral C _ _ h_neutral'
                exact ihM M'_body hM' N (Acc.intro N hN_acc) hbeta_red' hM''_red hN'_red' P hP (cr1_reducible_sn A P hP) (by unfold IsNeutral; trivial)
            | @appR _ N_arg N'_arg hN' =>
              -- N → N'_arg, Q = app (app (lam M) N'_arg) P
              -- Q is neutral, use CR3 + ihN
              have hbeta_red' : Reducible (Ty.arr A C) (Term.subst0 N'_arg M) := hN'_red N'_arg hN'
              have hM'_red' : ∀ M', M →β M' → Reducible (Ty.arr A C) (Term.subst0 N'_arg M') := fun M' hM' =>
                cr2_reducible_red (Ty.arr A C) _ _ hbeta_red' (subst0_step_left hM')
              have hN''_red : ∀ N'', N'_arg →β N'' → Reducible (Ty.arr A C) (Term.subst0 N'' M) := fun N'' hN'' =>
                cr2_reducible_red_multi (Ty.arr A C) _ _ hbeta_red' (subst0_step_right hN'')
              have h_neutral' : IsNeutral (Term.app (Term.app (Term.lam M) N'_arg) P) := by
                unfold IsNeutral; trivial
              apply cr3_neutral C _ _ h_neutral'
              exact ihN N'_arg hN' hbeta_red' hM'_red' hN''_red P hP (cr1_reducible_sn A P hP) (by unfold IsNeutral; trivial)
          | @appR _ P_arg P'_arg hP' =>
            -- P → P'_arg, Q = app (app (lam M) N) P'_arg
            -- Q is neutral, use CR3 + ihP
            have hP'_red : Reducible A P'_arg := cr2_reducible_red A P P'_arg hP hP'
            have h_neutral' : IsNeutral (Term.app (Term.app (Term.lam M) N) P'_arg) := by
              unfold IsNeutral; trivial
            apply cr3_neutral C _ _ h_neutral'
            exact ihP P'_arg hP' hP'_red (by unfold IsNeutral; trivial)

/-! ## Reducibility of Variables -/

/-- Variables are reducible at any type.

    This follows from CR3: variables are neutral and have no reducts. -/
theorem var_reducible (n : Nat) (A : Ty) : Reducible A (Term.var n) := by
  apply cr3_neutral
  · intro N hstep
    cases hstep  -- Variables don't reduce
  · exact neutral_var n

/-! ## Substitution Infrastructure -/

/-- Apply a parallel substitution σ to a term -/
def applySubst (σ : Nat → Term) : Term → Term
  | Term.var n => σ n
  | Term.app M N => Term.app (applySubst σ M) (applySubst σ N)
  | Term.lam M => Term.lam (applySubst (liftSubst σ) M)
where
  liftSubst (σ : Nat → Term) (n : Nat) : Term :=
    if n = 0 then Term.var 0 else Term.shift1 (σ (n - 1))

/-- Identity substitution -/
def idSubst : Nat → Term := Term.var

/-- Extend a substitution with a term at position 0.
    extendSubst σ N maps 0 ↦ N and (n+1) ↦ σ(n) -/
def extendSubst (σ : Nat → Term) (N : Term) : Nat → Term
  | 0 => N
  | n + 1 => σ n

/-- Helper: liftSubst σ 0 = var 0 -/
theorem liftSubst_zero (σ : Nat → Term) : applySubst.liftSubst σ 0 = Term.var 0 := by
  simp only [applySubst.liftSubst, ite_true]

/-- Helper: liftSubst σ (n+1) = shift1 (σ n) -/
theorem liftSubst_succ (σ : Nat → Term) (n : Nat) :
    applySubst.liftSubst σ (n + 1) = Term.shift1 (σ n) := by
  simp only [applySubst.liftSubst, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]

/-- Helper: extendSubst σ N 0 = N -/
theorem extendSubst_zero (σ : Nat → Term) (N : Term) : extendSubst σ N 0 = N := rfl

/-- Helper: extendSubst σ N (n+1) = σ n -/
theorem extendSubst_succ (σ : Nat → Term) (N : Term) (n : Nat) :
    extendSubst σ N (n + 1) = σ n := rfl

/-- Helper: subst0 N (shift1 M) = M for any N and M -/
theorem subst0_shift1 (N M : Term) : Term.subst0 N (Term.shift1 M) = M :=
  Term.subst_shift1 M N

/-- Helper: shift 0 0 is the identity -/
theorem shift_zero_zero (M : Term) : Term.shift 0 0 M = M := Term.shift_zero 0 M

/-! ## Helper lemmas for liftSubst_extendSubst_comm -/

/-- subst 1 X (shift1 Y) = shift1 (subst 0 X Y) for appropriately shifted X.

    Follows from shift1_subst with proper specialization. -/
theorem subst1_shift1_eq_shift1_subst0 (N X : Term) :
    Term.subst 1 (Term.shift1 N) (Term.shift1 X) = Term.shift1 (Term.subst0 N X) := by
  -- shift1_subst: shift1 (subst j N L) = subst (j+1) (shift1 N) (shift1 L)
  -- At j=0: shift1 (subst 0 N X) = subst 1 (shift1 N) (shift1 X)
  symm
  exact Term.shift1_subst X N 0

/-- The doubly-lifted substitution at n+2 gives shift1 (shift1 (σ n)) -/
theorem liftSubst_liftSubst_succ_succ (σ : Nat → Term) (n : Nat) :
    applySubst.liftSubst (applySubst.liftSubst σ) (n + 2) = Term.shift1 (Term.shift1 (σ n)) := by
  simp only [applySubst.liftSubst]
  have h1 : n + 2 ≠ 0 := by omega
  have h2 : n + 2 - 1 = n + 1 := by omega
  have h3 : n + 1 ≠ 0 := by omega
  have h4 : n + 1 - 1 = n := by omega
  simp only [h1, ↓reduceIte, h2, h3, h4]

/-- The singly-lifted extended substitution at n+2 gives shift1 (σ n) -/
theorem liftSubst_extendSubst_succ_succ (σ : Nat → Term) (N : Term) (n : Nat) :
    applySubst.liftSubst (extendSubst σ N) (n + 2) = Term.shift1 (σ n) := by
  simp only [applySubst.liftSubst]
  have h1 : n + 2 ≠ 0 := by omega
  have h2 : n + 2 - 1 = n + 1 := by omega
  simp only [h1, ↓reduceIte, h2]
  simp only [extendSubst]

/-- The doubly-lifted substitution at 1 gives shift1 (var 0) = var 1 -/
theorem liftSubst_liftSubst_one (σ : Nat → Term) :
    applySubst.liftSubst (applySubst.liftSubst σ) 1 = Term.var 1 := by
  simp only [applySubst.liftSubst, Nat.one_ne_zero, ↓reduceIte, Nat.sub_self]
  simp only [Term.shift1, Term.shift]
  rfl

/-- The singly-lifted extended substitution at 1 gives shift1 N -/
theorem liftSubst_extendSubst_one (σ : Nat → Term) (N : Term) :
    applySubst.liftSubst (extendSubst σ N) 1 = Term.shift1 N := by
  simp only [applySubst.liftSubst, Nat.one_ne_zero, ↓reduceIte, Nat.sub_self]
  simp only [extendSubst]

/-- subst 1 (shift1 N) (shift1 (shift1 X)) = shift1 X.

    Key lemma: substituting at level 1 after double-shifting cancels one shift.
    Uses that subst 1 X (shift1 Y) = shift1 (subst 0 X Y) and subst0_shift1. -/
theorem subst1_shift1_shift1_cancel (N X : Term) :
    Term.subst 1 (Term.shift1 N) (Term.shift1 (Term.shift1 X)) = Term.shift1 X := by
  rw [subst1_shift1_eq_shift1_subst0]
  rw [subst0_shift1]

/-- Helper: liftSubst (extendSubst σ N) is extensionally equal to extending liftSubst σ with var 0,
    except composed with shift1.

    Specifically: liftSubst (extendSubst σ N) n equals:
    - var 0 when n = 0
    - shift1 (extendSubst σ N (n-1)) = shift1 of (N if n=1, σ(n-2) if n>1) when n > 0
-/
theorem liftSubst_extendSubst_eq (σ : Nat → Term) (N : Term) (n : Nat) :
    applySubst.liftSubst (extendSubst σ N) n =
    if n = 0 then Term.var 0 else Term.shift1 (extendSubst σ N (n - 1)) := by
  cases n with
  | zero => simp only [applySubst.liftSubst]
  | succ k => simp only [applySubst.liftSubst, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

/-- Helper: extensional equality of functions implies applySubst equality -/
theorem applySubst_ext {σ₁ σ₂ : Nat → Term} (h : ∀ n, σ₁ n = σ₂ n) (M : Term) :
    applySubst σ₁ M = applySubst σ₂ M := by
  induction M generalizing σ₁ σ₂ with
  | var n => simp only [applySubst]; exact h n
  | app M1 M2 ih1 ih2 => simp only [applySubst]; rw [ih1 h, ih2 h]
  | lam M ih =>
    simp only [applySubst]
    congr 1
    apply ih
    intro n
    simp only [applySubst.liftSubst]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
      congr 1
      exact h (n - 1)

/-- Helper: subst 1 X (shift 2 0 T) = shift1 T.

    This follows from:
    1. shift 2 0 T = shift 1 1 (shift 1 0 T) by shift_shift_succ
    2. subst 1 X (shift 1 1 Y) = Y by subst_shift_cancel with c=1 -/
theorem subst1_shift2_eq_shift1 (X T : Term) :
    Term.subst 1 X (Term.shift 2 0 T) = Term.shift1 T := by
  -- shift 2 0 T = shift 1 1 (shift 1 0 T)
  have h1 : Term.shift 2 0 T = Term.shift 1 1 (Term.shift 1 0 T) := by
    rw [← Term.shift_shift_succ 0 T]
  rw [h1]
  -- subst 1 X (shift 1 1 (shift1 T)) = shift1 T by subst_shift_cancel
  exact Term.subst_shift_cancel (Term.shift1 T) X 1

/-- Apply liftSubst n times to a substitution -/
def liftSubst_n : Nat → (Nat → Term) → (Nat → Term)
  | 0, σ => σ
  | n + 1, σ => applySubst.liftSubst (liftSubst_n n σ)

/-- liftSubst_n (n+1) σ = liftSubst (liftSubst_n n σ) -/
theorem liftSubst_n_succ (n : Nat) (σ : Nat → Term) :
    liftSubst_n (n + 1) σ = applySubst.liftSubst (liftSubst_n n σ) := rfl

/-- liftSubst_n 1 σ = liftSubst σ -/
theorem liftSubst_n_one (σ : Nat → Term) :
    liftSubst_n 1 σ = applySubst.liftSubst σ := rfl

/-- liftSubst_n 2 σ = liftSubst (liftSubst σ) -/
theorem liftSubst_n_two (σ : Nat → Term) :
    liftSubst_n 2 σ = applySubst.liftSubst (applySubst.liftSubst σ) := rfl

/-- Key characterization of liftSubst_n:
    - For n < k: liftSubst_n k σ n = var n
    - For n ≥ k: liftSubst_n k σ n = shift k 0 (σ (n - k)) -/
theorem liftSubst_n_spec : ∀ k σ n,
    liftSubst_n k σ n = if n < k then Term.var n else Term.shift k 0 (σ (n - k)) := by
  intro k
  induction k with
  | zero =>
    intro σ n
    simp only [liftSubst_n, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    -- Need: σ n = shift 0 0 (σ n)
    -- Note: shift takes Int as first arg, and (0 : Nat) coerces to (0 : Int)
    -- Term.shift_zero : shift (0 : Nat) c M = M
    -- Goal has shift (↑0) which is shift ((0 : Nat) : Int)
    -- These are definitionally equal
    exact (Term.shift_zero 0 (σ n)).symm
  | succ k ih =>
    intro σ n
    simp only [liftSubst_n]
    -- liftSubst (liftSubst_n k σ) n
    cases n with
    | zero =>
      -- n = 0 < k + 1, so RHS = var 0
      simp only [Nat.zero_lt_succ, ↓reduceIte]
      simp only [applySubst.liftSubst, ↓reduceIte]
    | succ m =>
      -- n = m + 1
      simp only [applySubst.liftSubst, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      -- liftSubst (liftSubst_n k σ) (m + 1) = shift1 (liftSubst_n k σ m)
      rw [ih σ m]
      -- Now we have: shift1 (if m < k then var m else shift k 0 (σ (m - k)))
      by_cases hm : m < k
      · -- m < k, so m + 1 < k + 1
        have hmk : m + 1 < k + 1 := Nat.succ_lt_succ hm
        simp only [hm, ↓reduceIte, hmk]
        simp only [Term.shift1, Term.shift, Nat.not_lt_zero, ↓reduceIte]
        -- Goal: var (↑m + 1).toNat = var (m + 1)
        -- (↑m : Int) + 1 = ↑(m + 1), and (↑(m + 1)).toNat = m + 1
        have h_toNat : (↑m + 1 : Int).toNat = m + 1 := by
          have h : (↑m : Int) + 1 = ↑(m + 1) := by omega
          rw [h]
          rfl
        rw [h_toNat]
      · -- m ≥ k, so m + 1 ≥ k + 1
        have hmk : ¬(m + 1 < k + 1) := by omega
        have hmk' : m + 1 - (k + 1) = m - k := by omega
        simp only [hm, ↓reduceIte, hmk, hmk']
        -- Goal: shift1 (shift k 0 (σ (m - k))) = shift (k + 1) 0 (σ (m - k))
        simp only [Term.shift1]
        have h := Term.shift_shift 1 k 0 (σ (m - k))
        calc Term.shift 1 0 (Term.shift k 0 (σ (m - k)))
            = Term.shift (↑1 + ↑k) 0 (σ (m - k)) := h
          _ = Term.shift (↑k + 1) 0 (σ (m - k)) := by
              have heq : (↑1 : Int) + ↑k = ↑k + 1 := Int.add_comm _ _
              rw [heq]
          _ = Term.shift (↑(k + 1)) 0 (σ (m - k)) := by
              have heq : (↑k : Int) + 1 = ↑(k + 1) := by omega
              rw [heq]

/-- Combined generalized substitution-applySubst composition.

    This is THE key lemma that makes the fundamental lemma work.
    It generalizes subst_applySubst_lift to all levels j:

    subst j (shift j 0 N) (applySubst (liftSubst_n (j+1) σ) M) = applySubst (liftSubst_n j (extendSubst σ N)) M

    The proof is by induction on M, with j as a parameter.
    - var: Case analysis on n vs j
    - app: Direct by IH
    - lam: Apply IH at level j+1

    References:
    - Schäfer, Tebbi, Smolka: "Autosubst" (ITP 2015)
    - Aydemir et al. "Engineering Formal Metatheory" (2008) -/
theorem subst_applySubst_gen : ∀ (M : Term) (j : Nat) (σ : Nat → Term) (N : Term),
    Term.subst j (Term.shift j 0 N) (applySubst (liftSubst_n (j + 1) σ) M) =
    applySubst (liftSubst_n j (extendSubst σ N)) M := by
  intro M
  induction M with
  | var n =>
    intro j σ N
    simp only [applySubst]
    -- Use the characterization of liftSubst_n
    rw [liftSubst_n_spec (j + 1) σ n, liftSubst_n_spec j (extendSubst σ N) n]
    -- Case analysis on n vs j
    by_cases hn_lt_j : n < j
    · -- Case 1: n < j < j + 1
      have hn_lt_j1 : n < j + 1 := Nat.lt_succ_of_lt hn_lt_j
      simp only [hn_lt_j1, ↓reduceIte, hn_lt_j]
      -- LHS: subst j (shift j 0 N) (var n) where n < j
      -- subst at j doesn't affect var n when n ≠ j and n < j
      simp only [Term.subst]
      have hne : n ≠ j := Nat.ne_of_lt hn_lt_j
      have hng : ¬(n > j) := Nat.not_lt.mpr (Nat.le_of_lt hn_lt_j)
      simp only [hne, ↓reduceIte, hng]
    · -- Case 2: n ≥ j
      have hn_ge_j : n ≥ j := Nat.le_of_not_lt hn_lt_j
      simp only [hn_lt_j, ↓reduceIte]
      by_cases hn_lt_j1 : n < j + 1
      · -- Subcase 2a: n = j (since n ≥ j and n < j + 1)
        have hn_eq_j : n = j := Nat.le_antisymm (Nat.lt_succ_iff.mp hn_lt_j1) hn_ge_j
        simp only [hn_lt_j1, ↓reduceIte]
        subst hn_eq_j
        -- LHS: subst j (shift j 0 N) (var j) = shift j 0 N
        simp only [Term.subst, ↓reduceIte]
        -- RHS: shift j 0 (extendSubst σ N (j - j)) = shift j 0 (extendSubst σ N 0) = shift j 0 N
        simp only [Nat.sub_self, extendSubst]
      · -- Subcase 2b: n ≥ j + 1
        have hn_ge_j1 : n ≥ j + 1 := Nat.le_of_not_lt hn_lt_j1
        simp only [hn_lt_j1, ↓reduceIte]
        -- LHS: subst j (shift j 0 N) (shift (j+1) 0 (σ (n - (j+1))))
        -- RHS: shift j 0 (extendSubst σ N (n - j))
        -- Since n > j: extendSubst σ N (n - j) = σ (n - j - 1) = σ (n - (j + 1))
        have hn_gt_j : n > j := Nat.lt_of_succ_le hn_ge_j1
        have h_nj_pos : n - j > 0 := Nat.sub_pos_of_lt hn_gt_j
        have h_ext : extendSubst σ N (n - j) = σ (n - j - 1) := by
          cases hnj : n - j with
          | zero => omega
          | succ k =>
            simp only [extendSubst]
            have hsimp : k + 1 - 1 = k := Nat.succ_sub_one k
            simp only [hsimp]
        rw [h_ext]
        have h_eq : n - j - 1 = n - (j + 1) := by omega
        rw [h_eq]
        -- Now goal: subst j (shift j 0 N) (shift (j+1) 0 (σ (n - (j+1)))) = shift j 0 (σ (n - (j+1)))
        -- Key: shift (j+1) 0 X = shift 1 j (shift j 0 X)
        -- Then use subst_shift_cancel
        let X := σ (n - (j + 1))
        show Term.subst j (Term.shift j 0 N) (Term.shift (j + 1) 0 X) = Term.shift j 0 X
        -- shift (j+1) 0 X = shift 1 j (shift j 0 X) by shift_shift_offset
        have h_decomp : Term.shift (j + 1) 0 X = Term.shift 1 j (Term.shift j 0 X) := by
          have h := Term.shift_shift_offset j 0 X
          simp only [Nat.add_zero] at h
          exact h.symm
        rw [h_decomp]
        -- subst j (shift j 0 N) (shift 1 j Y) = Y by subst_shift_cancel
        exact Term.subst_shift_cancel (Term.shift j 0 X) (Term.shift j 0 N) j
  | app M1 M2 ih1 ih2 =>
    intro j σ N
    simp only [applySubst, Term.subst]
    congr 1
    · exact ih1 j σ N
    · exact ih2 j σ N
  | lam M0 ih =>
    intro j σ N
    simp only [applySubst, Term.subst]
    congr 1
    -- Goal: subst (j+1) (shift1 (shift j 0 N)) (applySubst (liftSubst (liftSubst_n (j+1) σ)) M0)
    --     = applySubst (liftSubst (liftSubst_n j (extendSubst σ N))) M0
    -- Using: liftSubst (liftSubst_n k σ) = liftSubst_n (k+1) σ
    simp only [← liftSubst_n_succ]
    -- And shift1 (shift j 0 N) = shift (j+1) 0 N
    -- This requires the shift_shift lemma
    have hshift : Term.shift1 (Term.shift j 0 N) = Term.shift (j + 1) 0 N := by
      simp only [Term.shift1]
      have h := Term.shift_shift 1 j 0 N
      -- h : shift 1 0 (shift j 0 N) = shift (↑1 + ↑j) 0 N
      -- Goal: shift 1 0 (shift j 0 N) = shift (↑j + 1) 0 N
      -- We need: ↑1 + ↑j = ↑j + 1 (as Int)
      -- Key insight: both (↑1 : Int) and (1 : Int) are definitionally equal
      -- And ↑1 + ↑j = 1 + ↑j = ↑j + 1 by Int.add_comm
      have heq : (↑1 : Int) + ↑j = ↑j + 1 := by
        -- First show ↑1 = 1
        have h1 : (↑1 : Int) = (1 : Int) := rfl
        calc (↑1 : Int) + ↑j = 1 + ↑j := by rw [h1]
          _ = ↑j + 1 := Int.add_comm 1 ↑j
      -- Now use calc to transform h
      calc Term.shift 1 0 (Term.shift j 0 N)
          = Term.shift (↑1 + ↑j) 0 N := h
        _ = Term.shift (↑j + 1) 0 N := by rw [heq]
    rw [hshift]
    exact ih (j + 1) σ N

/-- Commutation of subst 1 with doubly-lifted and extended substitutions.

    This is the key lemma for the lambda case of subst_applySubst_lift.
    It shows that substituting at index 1 after applying a doubly-lifted substitution
    equals applying a singly-lifted extended substitution.

    The proof instantiates the generalized `subst_applySubst_gen` at j=1.

    References:
    - Schäfer, Tebbi, Smolka: "Autosubst" (ITP 2015)
    - Aydemir et al. "Engineering Formal Metatheory" (2008)
    - PLFA Substitution chapter -/
theorem liftSubst_extendSubst_comm (σ : Nat → Term) (N M : Term)
    (_outer_ih : ∀ σ' N', Term.subst0 N' (applySubst (applySubst.liftSubst σ') M) =
                   applySubst (extendSubst σ' N') M) :
    Term.subst 1 (Term.shift1 N) (applySubst (applySubst.liftSubst (applySubst.liftSubst σ)) M) =
    applySubst (applySubst.liftSubst (extendSubst σ N)) M := by
  -- Use the generalized lemma at j = 1
  have h := subst_applySubst_gen M 1 σ N
  -- liftSubst_n 2 σ = liftSubst (liftSubst σ)
  -- liftSubst_n 1 (extendSubst σ N) = liftSubst (extendSubst σ N)
  simp only [liftSubst_n] at h
  -- h now has: subst 1 (shift 1 0 N) (applySubst (liftSubst (liftSubst σ)) M)
  --          = applySubst (liftSubst (extendSubst σ N)) M
  -- Our goal has shift1 N which equals shift 1 0 N by definition
  -- So h is exactly what we need
  exact h

/-- Key substitution composition lemma:
    subst0 N (applySubst (liftSubst σ) M) = applySubst (extendSubst σ N) M

    This is the critical interaction between single substitution (subst0)
    and parallel substitution (applySubst) needed for the fundamental lemma.

    The proof is by structural induction on M:
    - var n case (COMPLETE): Split on whether n = 0 or n > 0
      - n = 0: liftSubst σ 0 = var 0, so LHS = subst0 N (var 0) = N = extendSubst σ N 0 = RHS
      - n = k+1: liftSubst σ (k+1) = shift1 (σ k), so LHS = subst0 N (shift1 (σ k)) = σ k = extendSubst σ N (k+1) = RHS
    - app case (COMPLETE): Direct by IH
    - lam case (INCOMPLETE): Requires additional infrastructure

    The lambda case requires proving that the two nested substitutions are equivalent. The challenge is that:
    1. The IH gives us a result for subst 0, but we need subst 1 after unfolding the lambda
    2. This requires either:
       a) Generalizing the entire theorem to work for arbitrary j (not just 0)
       b) Proving an auxiliary lemma about the composition of liftSubst and extendSubst
       c) Using the shift-subst interaction lemmas from Term.lean

    All three approaches are standard but require significant additional lemmas and infrastructure.
    The most common approach in the literature (e.g., Autosubst) is (a).

    References:
    - Sch\"afer, Tebbi, Smolka: "Autosubst: Reasoning with de Bruijn Terms" (ITP 2015)
    - Girard, Lafont & Taylor "Proofs and Types" Section 6.2
    - PLFA: Programming Language Foundations in Agda, Substitution chapter
    - Aydemir et al. "Engineering Formal Metatheory" (2008) -/
theorem subst_applySubst_lift : ∀ (σ : Nat → Term) (N : Term) (M : Term),
    Term.subst0 N (applySubst (applySubst.liftSubst σ) M) = applySubst (extendSubst σ N) M := by
  intro σ N M
  induction M generalizing σ N with
  | var n =>
    -- Case 1: Variable
    simp only [applySubst, Term.subst0]
    by_cases h : n = 0
    · -- Subcase n = 0
      simp only [h]
      rw [liftSubst_zero, extendSubst_zero]
      -- liftSubst σ 0 = var 0, so subst0 N (var 0) = N by definition
      rfl
    · -- Subcase n > 0, so n = k + 1 for some k
      have ⟨k, hk⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero h
      subst hk
      rw [liftSubst_succ, extendSubst_succ]
      -- subst 0 N (shift1 (σ k)) = σ k by the shift cancellation lemma
      exact subst0_shift1 N (σ k)
  | app M1 M2 ih1 ih2 =>
    -- Case 2: Application - direct by IH
    simp only [applySubst]
    simp only [Term.subst0, Term.subst]
    congr 1
    · exact ih1 σ N
    · exact ih2 σ N
  | lam M ih =>
    -- Case 3: Lambda abstraction
    -- After unfolding both sides:
    -- LHS: lam (subst 1 (shift1 N) (applySubst (liftSubst (liftSubst σ)) M))
    -- RHS: lam (applySubst (liftSubst (extendSubst σ N)) M)
    simp only [applySubst, Term.subst0, Term.subst]
    congr 1
    -- Use the liftSubst_extendSubst_comm lemma
    exact liftSubst_extendSubst_comm σ N M ih

/-- Lifting identity substitution gives identity. -/
theorem liftSubst_id : ∀ n, applySubst.liftSubst idSubst n = Term.var n := by
  intro n
  simp only [applySubst.liftSubst, idSubst]
  cases n with
  | zero => rfl
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
    simp only [Term.shift1, Term.shift]
    simp

/-- A substitution is identity-like if it maps each n to var n -/
def IsIdSubst (σ : Nat → Term) : Prop := ∀ n, σ n = Term.var n

/-- Lifting an identity-like substitution gives an identity-like substitution -/
theorem liftSubst_preserves_id {σ : Nat → Term} (h : IsIdSubst σ) :
    IsIdSubst (applySubst.liftSubst σ) := by
  intro n
  simp only [applySubst.liftSubst]
  cases n with
  | zero => rfl
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
    rw [h k]
    simp only [Term.shift1, Term.shift]
    simp

/-- Applying an identity-like substitution gives the original term -/
theorem applySubst_of_isId {σ : Nat → Term} (h : IsIdSubst σ) : ∀ M, applySubst σ M = M := by
  intro M
  induction M generalizing σ with
  | var n =>
    simp only [applySubst]
    exact h n
  | app M N ihM ihN =>
    simp only [applySubst]
    rw [ihM h, ihN h]
  | lam M ih =>
    simp only [applySubst]
    rw [ih (liftSubst_preserves_id h)]

/-- Identity substitution is identity-like -/
theorem idSubst_isId : IsIdSubst idSubst := fun _ => rfl

/-- Identity substitution is the identity function on terms. -/
theorem applySubst_id : ∀ M, applySubst idSubst M = M :=
  applySubst_of_isId idSubst_isId

/-- Reducible substitution: maps each variable to a reducible term of its type -/
def ReducibleSubst (Γ : Context) (σ : Nat → Term) : Prop :=
  ∀ (n : Nat) (A : Ty), Γ[n]? = some A → Reducible A (σ n)

/-- Extended substitution preserves reducibility.

    If σ is reducible for Γ and N is reducible at A,
    then (extendSubst σ N) is reducible for (A :: Γ). -/
theorem extendSubst_reducible {Γ : Context} {σ : Nat → Term} {N : Term} {A : Ty}
    (hσ : ReducibleSubst Γ σ) (hN : Reducible A N) :
    ReducibleSubst (A :: Γ) (extendSubst σ N) := by
  intro n B hB
  cases n with
  | zero =>
    -- extendSubst σ N 0 = N, and N is reducible at A
    simp only [extendSubst]
    simp only [List.getElem?_cons_zero] at hB
    injection hB with hB'
    rw [← hB']
    exact hN
  | succ n' =>
    -- extendSubst σ N (n'+1) = σ n'
    simp only [extendSubst]
    simp only [List.getElem?_cons_succ] at hB
    exact hσ n' B hB

/-! ## Fundamental Lemma -/

/-- **Fundamental Lemma**: Well-typed terms are reducible under reducible substitution.

    This is the heart of the strong normalization proof. It says:
    If Γ ⊢ M : A and σ is a reducible substitution for Γ,
    then M[σ] is reducible at type A.

    The proof requires careful handling of the lambda case using
    extended substitutions.

    References:
    - Girard, Lafont & Taylor "Proofs and Types" Lemma 6.2.3
    - Pierce TAPL Lemma 12.1.6 -/
theorem fundamental_lemma : ∀ {Γ : Context} {M : Term} {A : Ty} {σ : Nat → Term},
    HasType Γ M A →
    ReducibleSubst Γ σ →
    Reducible A (applySubst σ M) := by
  intro Γ M A σ htype hσ
  induction htype generalizing σ with
  | @var Γ' n A' hget =>
    -- M = var n, applySubst σ (var n) = σ n
    simp only [applySubst]
    exact hσ n A' hget
  | @app Γ' M' N' A' B' hM hN ihM ihN =>
    -- M = app M' N', need app (applySubst σ M') (applySubst σ N') reducible at B'
    simp only [applySubst]
    -- By IH, applySubst σ M' is reducible at A' ⇒ B'
    have hM' := ihM hσ
    -- By IH, applySubst σ N' is reducible at A'
    have hN' := ihN hσ
    -- By definition of reducible at arrow type, application is reducible at B'
    exact hM' (applySubst σ N') hN'
  | @lam Γ' M' A' B' hBody ihBody =>
    -- M = lam M', need lam (applySubst (liftSubst σ) M') reducible at A' ⇒ B'
    simp only [applySubst]
    -- Reducible at A' ⇒ B' means: ∀ N reducible at A', app (...) N reducible at B'
    intro N hN

    -- Let M'' = applySubst (liftSubst σ) M' (the substituted body)
    let M'' := applySubst (applySubst.liftSubst σ) M'

    -- The extended substitution is reducible for (A' :: Γ')
    have hext : ReducibleSubst (A' :: Γ') (extendSubst σ N) := extendSubst_reducible hσ hN
    -- By IH, applySubst (extendSubst σ N) M' is reducible at B'
    have hbeta : Reducible B' (applySubst (extendSubst σ N) M') := ihBody hext
    -- By subst_applySubst_lift, this equals the beta reduct
    rw [← subst_applySubst_lift] at hbeta

    -- Get SN of M'' from the SN of its substitution with any reducible term
    -- We use that var 0 is reducible at any type (by CR3)
    have hvar0 : Reducible A' (Term.var 0) := var_reducible 0 A'
    have hext0 : ReducibleSubst (A' :: Γ') (extendSubst σ (Term.var 0)) := extendSubst_reducible hσ hvar0
    have hM''_var : Reducible B' (applySubst (extendSubst σ (Term.var 0)) M') := ihBody hext0
    rw [← subst_applySubst_lift] at hM''_var
    have hM''_sn_from_subst : SN (Term.subst0 (Term.var 0) M'') := cr1_reducible_sn B' _ hM''_var

    -- Use reducible_app_lam to show app (lam M'') N is reducible
    -- N is reducible at A', hence SN by CR1
    have hN_sn : SN N := cr1_reducible_sn A' N hN
    apply reducible_app_lam B' M'' N

    -- 1. Need SN M''
    · -- SN M'' can be obtained from SN of subst0 (var 0) M'' via the inverse
      -- of the substitution compatibility. This is complex so we use a workaround:
      -- From CR1, subst0 N M'' is SN (by hbeta), and SN is closed under expansion
      -- for strongly normalizing arguments.
      -- Actually, we need a helper lemma. For now, use that if subst0 (var 0) M'' is SN,
      -- then since var 0 has no reducts, M'' steps imply subst0 (var 0) M'' steps,
      -- so M'' is SN.
      have : ∀ T, SN T → ∀ M, T = Term.subst0 (Term.var 0) M → SN M := by
        intro T hT
        induction hT with
        | intro T' _ ih =>
          intro M hTeq
          apply sn_intro
          intro M'_step hM'_step
          -- M → M'_step implies subst0 (var 0) M → subst0 (var 0) M'_step
          have hstep : BetaStep (Term.subst0 (Term.var 0) M) (Term.subst0 (Term.var 0) M'_step) :=
            @subst0_step_left M M'_step (Term.var 0) hM'_step
          rw [← hTeq] at hstep
          exact ih (Term.subst0 (Term.var 0) M'_step) hstep M'_step rfl
      exact this (Term.subst0 (Term.var 0) M'') hM''_sn_from_subst M'' rfl

    -- 2. SN N
    · exact hN_sn

    -- 3. Beta reduct is reducible (already have this)
    · exact hbeta

    -- 4. All M'' reducts: if M'' → M''', then subst0 N M''' is reducible at B'
    · intro M''' hM'''
      -- Use CR2: subst0 N M'' → subst0 N M''' (by subst0_step_left)
      -- and hbeta says subst0 N M'' is reducible, so subst0 N M''' is reducible by CR2
      have hstep : BetaStep (Term.subst0 N M'') (Term.subst0 N M''') := subst0_step_left hM'''
      exact cr2_reducible_red B' _ _ hbeta hstep

    -- 5. All N reducts: if N → N', then subst0 N' M'' is reducible at B'
    · intro N' hN'
      -- N' is reducible at A' by CR2
      have hN'_red : Reducible A' N' := cr2_reducible_red A' N N' hN hN'
      -- Extended substitution with N' is reducible
      have hext' : ReducibleSubst (A' :: Γ') (extendSubst σ N') := extendSubst_reducible hσ hN'_red
      -- By IH, applySubst (extendSubst σ N') M' is reducible at B'
      have h := ihBody hext'
      rw [← subst_applySubst_lift] at h
      exact h

/-! ## Strong Normalization Theorem -/

/-- **Strong Normalization Theorem**: Every well-typed term in STLC terminates.

    This is one of the cornerstone results in type theory, first proven by
    Tait (1967) for STLC and extended by Girard (1972) to System F.

    Proof:
    1. The identity substitution σ(n) = var n is reducible (variables are reducible)
    2. By the fundamental lemma, M[σ] = M is reducible
    3. By CR1, reducible terms are strongly normalizing
    4. Therefore M is SN ∎ -/
theorem strong_normalization {Γ : Context} {M : Term} {A : Ty}
    (h : HasType Γ M A) : SN M := by
  -- Identity substitution is reducible
  have hσ : ReducibleSubst Γ idSubst := by
    intro n B hB
    exact var_reducible n B
  -- By fundamental lemma, M[id] is reducible
  have hred : Reducible A (applySubst idSubst M) := fundamental_lemma h hσ
  -- M[id] = M
  rw [applySubst_id] at hred
  -- By CR1, M is SN
  exact cr1_reducible_sn A M hred

/-! ## Corollaries -/

/-- Every well-typed term has a β-normal form. -/
theorem hasNormalForm_of_hasType {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) :
    Rewriting.HasNormalForm BetaStep M :=
  hasNormalForm_of_SN (strong_normalization h)

/-- Every well-typed term has a unique β-normal form. -/
theorem existsUnique_normalForm_of_hasType {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) :
    ∃ n, Rewriting.Star BetaStep M n ∧ Rewriting.IsNormalForm BetaStep n ∧
      ∀ n', (Rewriting.Star BetaStep M n' ∧ Rewriting.IsNormalForm BetaStep n') → n' = n :=
  Rewriting.existsUnique_normalForm_of_confluent_hasNormalForm Metatheory.Lambda.betaStep_confluent
    (hasNormalForm_of_hasType h)

/-- Well-typed STLC programs don't diverge -/
theorem stlc_termination {M : Term} {A : Ty}
    (h : HasType [] M A) : SN M :=
  strong_normalization h

/-- Type safety: well-typed closed terms are values or can step -/
theorem type_safety {M N : Term} {A : Ty}
    (htype : HasType [] M A) (hsteps : MultiStep M N) :
    IsValue N ∨ ∃ P, BetaStep N P :=
  progress (subject_reduction_multi htype hsteps)

end Metatheory.STLC
