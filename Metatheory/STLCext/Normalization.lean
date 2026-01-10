/-
# Simply Typed Lambda Calculus with Products and Sums - Strong Normalization

This module proves strong normalization for the extended STLC with products and sums:
every well-typed term terminates (all reduction sequences are finite).

## Strategy: Logical Relations (Reducibility Candidates)

The proof extends Tait's method of logical relations to products and sums:

1. Define a predicate `Reducible A M` for each type A
2. Show reducibility conditions (CR1, CR2, CR3)
3. Prove the fundamental lemma: well-typed terms are reducible
4. Conclude: reducible terms are strongly normalizing

## References

- Tait, "Intensional Interpretations of Functionals of Finite Type" (1967)
- Girard, "Interprétation fonctionnelle et élimination des coupures" (1972)
- Pierce, "Types and Programming Languages" (2002), Chapters 11-12
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

import Metatheory.STLCext.Typing
import Metatheory.Rewriting.Basic

namespace Metatheory.STLCext

/-! ## Strong Normalization Definition -/

/-- A term is strongly normalizing if all reduction sequences from it terminate. -/
def SN (M : Term) : Prop := Acc (fun a b => Step b a) M

/-! ## Normal Forms -/

/-- Strong normalization implies existence of a normal form (as a generic `Rewriting.HasNormalForm`). -/
theorem hasNormalForm_of_SN {M : Term} (hM : SN M) : Rewriting.HasNormalForm Step M :=
  Rewriting.hasNormalForm_of_acc hM

/-! ## Basic SN Properties -/

theorem sn_var (n : Nat) : SN (Term.var n) := Acc.intro _ (fun _ h => nomatch h)

theorem sn_of_step {M N : Term} (hM : SN M) (h : Step M N) : SN N := Acc.inv hM h

theorem sn_intro {M : Term} (h : ∀ N, Step M N → SN N) : SN M := Acc.intro M h

theorem sn_of_multi {M N : Term} (hM : SN M) (h : MultiStep M N) : SN N := by
  induction h with
  | refl => exact hM
  | step hstep _ ih => exact ih (sn_of_step hM hstep)

/-! ## Multi-step reduction for injections -/

/-- If inl M steps, it must step to inl M' for some M' with M →₁ M' -/
theorem step_inl_inv {M Q : Term} (h : Step (Term.inl M) Q) :
    ∃ M', Q = Term.inl M' ∧ Step M M' := by
  cases h with
  | inl hM => exact ⟨_, rfl, hM⟩

/-- If inr M steps, it must step to inr M' for some M' with M →₁ M' -/
theorem step_inr_inv {M Q : Term} (h : Step (Term.inr M) Q) :
    ∃ M', Q = Term.inr M' ∧ Step M M' := by
  cases h with
  | inr hM => exact ⟨_, rfl, hM⟩

/-- Multi-step reduction under inl: if inl M ⟶* inl V then M ⟶* V -/
theorem multiStep_inl_inv {M V : Term} (h : MultiStep (Term.inl M) (Term.inl V)) :
    MultiStep M V := by
  have : ∀ P Q, MultiStep P Q → ∀ M V, P = Term.inl M → Q = Term.inl V → MultiStep M V := by
    intro P Q hPQ
    induction hPQ with
    | refl =>
      intro M V hP hQ
      rw [hP] at hQ
      injection hQ with hQ'
      rw [← hQ']
      exact MultiStep.refl M
    | step hstep _ ih =>
      intro M V hP hQ
      subst hP
      obtain ⟨M', hM'eq, hM'step⟩ := step_inl_inv hstep
      subst hM'eq
      exact MultiStep.step hM'step (ih M' V rfl hQ)
  exact this (Term.inl M) (Term.inl V) h M V rfl rfl

/-- Multi-step reduction under inr: if inr M ⟶* inr V then M ⟶* V -/
theorem multiStep_inr_inv {M V : Term} (h : MultiStep (Term.inr M) (Term.inr V)) :
    MultiStep M V := by
  have : ∀ P Q, MultiStep P Q → ∀ M V, P = Term.inr M → Q = Term.inr V → MultiStep M V := by
    intro P Q hPQ
    induction hPQ with
    | refl =>
      intro M V hP hQ
      rw [hP] at hQ
      injection hQ with hQ'
      rw [← hQ']
      exact MultiStep.refl M
    | step hstep _ ih =>
      intro M V hP hQ
      subst hP
      obtain ⟨M', hM'eq, hM'step⟩ := step_inr_inv hstep
      subst hM'eq
      exact MultiStep.step hM'step (ih M' V rfl hQ)
  exact this (Term.inr M) (Term.inr V) h M V rfl rfl

/-- inl M cannot reduce to inr V -/
theorem multiStep_inl_not_inr {M V : Term} (h : MultiStep (Term.inl M) (Term.inr V)) : False := by
  have : ∀ P Q, MultiStep P Q → ∀ M V, P = Term.inl M → Q = Term.inr V → False := by
    intro P Q hPQ
    induction hPQ with
    | refl =>
      intro M V hP hQ
      rw [hP] at hQ
      cases hQ
    | step hstep _ ih =>
      intro M V hP hQ
      subst hP
      obtain ⟨M', hM'eq, _⟩ := step_inl_inv hstep
      subst hM'eq
      exact ih M' V rfl hQ
  exact this (Term.inl M) (Term.inr V) h M V rfl rfl

/-- inr M cannot reduce to inl V -/
theorem multiStep_inr_not_inl {M V : Term} (h : MultiStep (Term.inr M) (Term.inl V)) : False := by
  have : ∀ P Q, MultiStep P Q → ∀ M V, P = Term.inr M → Q = Term.inl V → False := by
    intro P Q hPQ
    induction hPQ with
    | refl =>
      intro M V hP hQ
      rw [hP] at hQ
      cases hQ
    | step hstep _ ih =>
      intro M V hP hQ
      subst hP
      obtain ⟨M', hM'eq, _⟩ := step_inr_inv hstep
      subst hM'eq
      exact ih M' V rfl hQ
  exact this (Term.inr M) (Term.inl V) h M V rfl rfl

/-! ## Neutral Terms -/

def IsNeutral : Term → Prop
  | Term.var _ => True
  | Term.app (Term.lam _) _ => False
  | Term.app _ _ => True
  | Term.lam _ => False
  | Term.pair _ _ => False
  | Term.fst (Term.pair _ _) => False
  | Term.fst _ => True
  | Term.snd (Term.pair _ _) => False
  | Term.snd _ => True
  | Term.inl _ => False
  | Term.inr _ => False
  | Term.case (Term.inl _) _ _ => False
  | Term.case (Term.inr _) _ _ => False
  | Term.case _ _ _ => True
  | Term.unit => False

theorem neutral_var (n : Nat) : IsNeutral (Term.var n) := trivial

/-! ## SN Projections -/

theorem sn_app_left {M N : Term} (h : SN (Term.app M N)) : SN M := by
  have : ∀ T, SN T → ∀ M N, T = Term.app M N → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N hTeq
      subst hTeq
      exact sn_intro fun M' hM' => ih (Term.app M' N) (Step.appL hM') M' N rfl
  exact this (Term.app M N) h M N rfl

theorem sn_app_right {M N : Term} (h : SN (Term.app M N)) : SN N := by
  have : ∀ T, SN T → ∀ M N, T = Term.app M N → SN N := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N hTeq
      subst hTeq
      exact sn_intro fun N' hN' => ih (Term.app M N') (Step.appR hN') M N' rfl
  exact this (Term.app M N) h M N rfl

theorem sn_fst_inv {M : Term} (h : SN (Term.fst M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = Term.fst M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hTeq
      subst hTeq
      exact sn_intro fun M' hM' => ih (Term.fst M') (Step.fst hM') M' rfl
  exact this (Term.fst M) h M rfl

theorem sn_snd_inv {M : Term} (h : SN (Term.snd M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = Term.snd M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hTeq
      subst hTeq
      exact sn_intro fun M' hM' => ih (Term.snd M') (Step.snd hM') M' rfl
  exact this (Term.snd M) h M rfl

theorem sn_lam_inv {M : Term} (h : SN (Term.lam M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = Term.lam M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hTeq
      subst hTeq
      exact sn_intro fun M' hM' => ih (Term.lam M') (Step.lam hM') M' rfl
  exact this (Term.lam M) h M rfl

theorem sn_pair_left {M N : Term} (h : SN (Term.pair M N)) : SN M := by
  have : ∀ T, SN T → ∀ M N, T = Term.pair M N → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N hTeq
      subst hTeq
      exact sn_intro fun M' hM' => ih (Term.pair M' N) (Step.pairL hM') M' N rfl
  exact this (Term.pair M N) h M N rfl

theorem sn_pair_right {M N : Term} (h : SN (Term.pair M N)) : SN N := by
  have : ∀ T, SN T → ∀ M N, T = Term.pair M N → SN N := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N hTeq
      subst hTeq
      exact sn_intro fun N' hN' => ih (Term.pair M N') (Step.pairR hN') M N' rfl
  exact this (Term.pair M N) h M N rfl

theorem sn_inl_inv {M : Term} (h : SN (Term.inl M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = Term.inl M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hTeq
      subst hTeq
      exact sn_intro fun M' hM' => ih (Term.inl M') (Step.inl hM') M' rfl
  exact this (Term.inl M) h M rfl

theorem sn_inr_inv {M : Term} (h : SN (Term.inr M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = Term.inr M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hTeq
      subst hTeq
      exact sn_intro fun M' hM' => ih (Term.inr M') (Step.inr hM') M' rfl
  exact this (Term.inr M) h M rfl

theorem sn_case_scrut {M N₁ N₂ : Term} (h : SN (Term.case M N₁ N₂)) : SN M := by
  have : ∀ T, SN T → ∀ M N₁ N₂, T = Term.case M N₁ N₂ → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N₁ N₂ hTeq
      subst hTeq
      exact sn_intro fun M' hM' => ih (Term.case M' N₁ N₂) (Step.caseS hM') M' N₁ N₂ rfl
  exact this (Term.case M N₁ N₂) h M N₁ N₂ rfl

theorem sn_case_left {M N₁ N₂ : Term} (h : SN (Term.case M N₁ N₂)) : SN N₁ := by
  have : ∀ T, SN T → ∀ M N₁ N₂, T = Term.case M N₁ N₂ → SN N₁ := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N₁ N₂ hTeq
      subst hTeq
      exact sn_intro fun N₁' hN₁' => ih (Term.case M N₁' N₂) (Step.caseL hN₁') M N₁' N₂ rfl
  exact this (Term.case M N₁ N₂) h M N₁ N₂ rfl

theorem sn_case_right {M N₁ N₂ : Term} (h : SN (Term.case M N₁ N₂)) : SN N₂ := by
  have : ∀ T, SN T → ∀ M N₁ N₂, T = Term.case M N₁ N₂ → SN N₂ := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M N₁ N₂ hTeq
      subst hTeq
      exact sn_intro fun N₂' hN₂' => ih (Term.case M N₁ N₂') (Step.caseR hN₂') M N₁ N₂' rfl
  exact this (Term.case M N₁ N₂) h M N₁ N₂ rfl

/-! ## SN Term Constructors -/

/-- If M is SN, then lam M is SN -/
theorem sn_lam {M : Term} (hM : SN M) : SN (Term.lam M) := by
  induction hM with
  | intro M' _ ih =>
    exact sn_intro fun T hT => by
      cases hT with
      | lam hM'' => exact ih _ hM''

/-- If M and N are SN, then pair M N is SN -/
theorem sn_pair {M N : Term} (hM : SN M) (hN : SN N) : SN (Term.pair M N) := by
  induction hM generalizing N with
  | intro M' hM'_acc ihM =>
    induction hN with
    | intro N' hN'_acc ihN =>
      exact sn_intro fun T hT => by
        cases hT with
        | pairL hM'' =>
          have hN'_sn : SN N' := Acc.intro N' hN'_acc
          exact ihM _ hM'' hN'_sn
        | pairR hN'' => exact ihN _ hN''

/-- If M is SN, then inl M is SN -/
theorem sn_inl {M : Term} (hM : SN M) : SN (Term.inl M) := by
  induction hM with
  | intro M' _ ih =>
    exact sn_intro fun T hT => by
      cases hT with
      | inl hM'' => exact ih _ hM''

/-- If M is SN, then inr M is SN -/
theorem sn_inr {M : Term} (hM : SN M) : SN (Term.inr M) := by
  induction hM with
  | intro M' _ ih =>
    exact sn_intro fun T hT => by
      cases hT with
      | inr hM'' => exact ih _ hM''

/-! ## Reducibility (Logical Relations) -/

/-- Reducibility predicate indexed by type.
    For sum types, we track content reducibility via multi-step reduction to injections. -/
def Reducible : Ty → Term → Prop
  | Ty.base _, M => SN M
  | Ty.arr A B, M => ∀ N, Reducible A N → Reducible B (Term.app M N)
  | Ty.prod A B, M => Reducible A (Term.fst M) ∧ Reducible B (Term.snd M)
  | Ty.sum A B, M => SN M ∧
      (∀ V, MultiStep M (Term.inl V) → Reducible A V) ∧
      (∀ V, MultiStep M (Term.inr V) → Reducible B V)
  | Ty.unit, M => SN M

/-! ## CR2: Reducibility is closed backward under reduction -/

theorem cr2_reducible_red (A : Ty) : ∀ M N, Reducible A M → Step M N → Reducible A N := by
  induction A with
  | base n => intro M N hM hstep; unfold Reducible at hM ⊢; exact sn_of_step hM hstep
  | arr A B ihA ihB =>
    intro M N hM hstep P hP
    unfold Reducible at hM
    exact ihB (Term.app M P) (Term.app N P) (hM P hP) (Step.appL hstep)
  | prod A B ihA ihB =>
    intro M N hM hstep
    unfold Reducible at hM ⊢
    exact ⟨ihA _ _ hM.1 (Step.fst hstep), ihB _ _ hM.2 (Step.snd hstep)⟩
  | sum A B ihA ihB =>
    intro M N hM hstep
    unfold Reducible at hM ⊢
    obtain ⟨hM_sn, hM_inl, hM_inr⟩ := hM
    refine ⟨sn_of_step hM_sn hstep, ?_, ?_⟩
    · intro V hNred
      -- If N →* inl V, then M →* inl V (by prepending the step M → N)
      exact hM_inl V (MultiStep.step hstep hNred)
    · intro V hNred
      -- If N →* inr V, then M →* inr V (by prepending the step M → N)
      exact hM_inr V (MultiStep.step hstep hNred)
  | unit => intro M N hM hstep; unfold Reducible at hM ⊢; exact sn_of_step hM hstep

theorem cr2_reducible_red_multi (A : Ty) (M N : Term)
    (hM : Reducible A M) (hstep : MultiStep M N) : Reducible A N := by
  induction hstep with
  | refl => exact hM
  | step h _ ih => exact ih (cr2_reducible_red A _ _ hM h)

/-! ## CR1 and CR3: Main Properties -/

def CR_Props (A : Ty) : Prop :=
  (∀ M, Reducible A M → SN M) ∧
  (∀ M, (∀ N, Step M N → Reducible A N) → IsNeutral M → Reducible A M)

theorem cr_props_all : ∀ A, CR_Props A := by
  intro A
  induction A using Ty.rec with
  | base n =>
    constructor
    · intro M hM; unfold Reducible at hM; exact hM
    · intro M h_red _; unfold Reducible; exact sn_intro fun N hN => by
        have h := h_red N hN; unfold Reducible at h; exact h
  | arr A B ihA ihB =>
    obtain ⟨cr1_A, cr3_A⟩ := ihA
    obtain ⟨cr1_B, cr3_B⟩ := ihB
    constructor
    · intro M hM
      have h_var_red : Reducible A (Term.var 0) := cr3_A _ (fun N hN => nomatch hN) (neutral_var 0)
      unfold Reducible at hM
      exact sn_app_left (cr1_B _ (hM (Term.var 0) h_var_red))
    · intro M h_red h_neut
      unfold Reducible
      intro P hP
      have hP_sn : SN P := cr1_A P hP
      suffices h : ∀ Q, SN Q → Reducible A Q → Reducible B (Term.app M Q) by
        exact h P hP_sn hP
      intro Q hQ_sn
      induction hQ_sn with
      | intro Q' hQ'_acc ih =>
        intro hQ'_red
        apply cr3_B
        · intro R hR
          cases hR with
          | beta => exact False.elim h_neut
          | appL hstep => unfold Reducible at h_red; exact h_red _ hstep Q' hQ'_red
          | appR hQ'' => exact ih _ hQ'' (cr2_reducible_red A Q' _ hQ'_red hQ'')
        · cases M with
          | var _ => exact trivial
          | lam _ => exact False.elim h_neut
          | app M1 M2 =>
            unfold IsNeutral at h_neut
            cases M1 with
            | var _ => exact trivial
            | app _ _ => exact trivial
            | lam _ => exact False.elim h_neut
            | _ => exact trivial
          | _ => exact trivial
  | prod A B ihA ihB =>
    obtain ⟨cr1_A, cr3_A⟩ := ihA
    obtain ⟨cr1_B, cr3_B⟩ := ihB
    constructor
    · intro M hM
      unfold Reducible at hM
      exact sn_fst_inv (cr1_A _ hM.1)
    · intro M h_red h_neut
      unfold Reducible
      constructor
      · apply cr3_A
        · intro N hN
          cases hN with
          | fstPair => exact False.elim h_neut
          | fst hM' => have hM'_red := h_red _ hM'; unfold Reducible at hM'_red; exact hM'_red.1
        · cases M with
          | var _ => exact trivial
          | pair _ _ => exact False.elim h_neut
          | _ => exact trivial
      · apply cr3_B
        · intro N hN
          cases hN with
          | sndPair => exact False.elim h_neut
          | snd hM' => have hM'_red := h_red _ hM'; unfold Reducible at hM'_red; exact hM'_red.2
        · cases M with
          | var _ => exact trivial
          | pair _ _ => exact False.elim h_neut
          | _ => exact trivial
  | sum A B ihA ihB =>
    constructor
    · intro M hM; unfold Reducible at hM; exact hM.1
    · intro M h_red h_neut; unfold Reducible
      refine ⟨sn_intro fun N hN => ?_, ?_, ?_⟩
      · have hN_red := h_red N hN; unfold Reducible at hN_red; exact hN_red.1
      · intro V hMred
        -- M →* inl V with M neutral. Can't be refl (inl not neutral), so M → M' →* inl V
        cases hMred with
        | refl => unfold IsNeutral at h_neut; exact False.elim h_neut
        | step hstep hM'red =>
          have hM'_red := h_red _ hstep
          unfold Reducible at hM'_red
          exact hM'_red.2.1 V hM'red
      · intro V hMred
        cases hMred with
        | refl => unfold IsNeutral at h_neut; exact False.elim h_neut
        | step hstep hM'red =>
          have hM'_red := h_red _ hstep
          unfold Reducible at hM'_red
          exact hM'_red.2.2 V hM'red
  | unit =>
    constructor
    · intro M hM; unfold Reducible at hM; exact hM
    · intro M h_red _; unfold Reducible; exact sn_intro fun N hN => by
        have h := h_red N hN; unfold Reducible at h; exact h

theorem cr1_reducible_sn (A : Ty) (M : Term) (h : Reducible A M) : SN M :=
  (cr_props_all A).1 M h

theorem cr3_neutral (A : Ty) (M : Term) (h_red : ∀ N, Step M N → Reducible A N) (h_neut : IsNeutral M) :
    Reducible A M :=
  (cr_props_all A).2 M h_red h_neut

theorem var_reducible (n : Nat) (A : Ty) : Reducible A (Term.var n) :=
  cr3_neutral A _ (fun _ hstep => nomatch hstep) (neutral_var n)

/-! ## Reducibility of Applications with Lambdas -/

/-- Key lemma: (λM)N is reducible when M[N] is reducible -/
theorem reducible_app_lam : ∀ (B : Ty) (M N : Term),
    SN M → SN N →
    Reducible B (Term.subst0 N M) →
    (∀ M', Step M M' → Reducible B (Term.subst0 N M')) →
    (∀ N', Step N N' → Reducible B (Term.subst0 N' M)) →
    Reducible B (Term.app (Term.lam M) N) := by
  intro B
  induction B with
  | base n =>
    intro M N hM_sn hN_sn hbeta_red hM'_red hN'_red
    unfold Reducible at hbeta_red hM'_red hN'_red
    induction hM_sn generalizing N with
    | intro M hM_acc ihM =>
      induction hN_sn with
      | intro N hN_acc ihN =>
        apply sn_intro
        intro P hP
        cases hP with
        | beta => exact hbeta_red
        | appL hstep_lam =>
          cases hstep_lam with
          | lam hM'' =>
            apply ihM _ hM'' N (Acc.intro N hN_acc)
            · exact hM'_red _ hM''
            · intro M''' hM'''; exact sn_of_step (hM'_red _ hM'') (subst0_step_left hM''')
            · intro N' hN'_step; exact sn_of_step (hN'_red N' hN'_step) (subst0_step_left hM'')
        | appR hN'' =>
          apply ihN _ hN''
          · exact hN'_red _ hN''
          · intro M' hM'_step; exact sn_of_multi (hM'_red M' hM'_step) (subst0_step_right hN'')
          · intro N' hN'_step; exact sn_of_multi (hN'_red _ hN'') (subst0_step_right hN'_step)

  | arr A C _ihA ihC =>
    intro M N hM_sn hN_sn hbeta_red hM'_red hN'_red
    intro P hP
    have hP_sn : SN P := cr1_reducible_sn A P hP
    have h_neutral : IsNeutral (Term.app (Term.app (Term.lam M) N) P) := by unfold IsNeutral; trivial
    apply cr3_neutral C _ _ h_neutral
    induction hM_sn generalizing N P with
    | intro M hM_acc ihM =>
      induction hN_sn generalizing P with
      | intro N hN_acc ihN =>
        induction hP_sn with
        | intro P hP_acc ihP =>
          intro Q hQ
          cases hQ with
          | appL hstep_inner =>
            cases hstep_inner with
            | beta =>
              unfold Reducible at hbeta_red
              exact hbeta_red P hP
            | appL hstep_lam =>
              cases hstep_lam with
              | @lam M_body M'_body hM' =>
                have hbeta_red' : Reducible (Ty.arr A C) (Term.subst0 N M'_body) := hM'_red M'_body hM'
                have hM''_red : ∀ M'', Step M'_body M'' → Reducible (Ty.arr A C) (Term.subst0 N M'') :=
                  fun M'' hM'' => cr2_reducible_red (Ty.arr A C) _ _ hbeta_red' (subst0_step_left hM'')
                have hN'_red' : ∀ N', Step N N' → Reducible (Ty.arr A C) (Term.subst0 N' M'_body) :=
                  fun N' hN' => cr2_reducible_red (Ty.arr A C) _ _ (hN'_red N' hN') (subst0_step_left hM')
                have h_neutral' : IsNeutral (Term.app (Term.app (Term.lam M'_body) N) P) := by unfold IsNeutral; trivial
                apply cr3_neutral C _ _ h_neutral'
                exact ihM M'_body hM' N (Acc.intro N hN_acc) hbeta_red' hM''_red hN'_red' P hP (cr1_reducible_sn A P hP) (by unfold IsNeutral; trivial)
            | @appR _ N_arg N'_arg hN' =>
              have hbeta_red' : Reducible (Ty.arr A C) (Term.subst0 N'_arg M) := hN'_red N'_arg hN'
              have hM'_red' : ∀ M', Step M M' → Reducible (Ty.arr A C) (Term.subst0 N'_arg M') :=
                fun M' hM' => cr2_reducible_red (Ty.arr A C) _ _ hbeta_red' (subst0_step_left hM')
              have hN''_red : ∀ N'', Step N'_arg N'' → Reducible (Ty.arr A C) (Term.subst0 N'' M) :=
                fun N'' hN'' => cr2_reducible_red_multi (Ty.arr A C) _ _ hbeta_red' (subst0_step_right hN'')
              have h_neutral' : IsNeutral (Term.app (Term.app (Term.lam M) N'_arg) P) := by unfold IsNeutral; trivial
              apply cr3_neutral C _ _ h_neutral'
              exact ihN N'_arg hN' hbeta_red' hM'_red' hN''_red P hP (cr1_reducible_sn A P hP) (by unfold IsNeutral; trivial)
          | @appR _ P_arg P'_arg hP' =>
            have hP'_red : Reducible A P'_arg := cr2_reducible_red A P P'_arg hP hP'
            have h_neutral' : IsNeutral (Term.app (Term.app (Term.lam M) N) P'_arg) := by unfold IsNeutral; trivial
            apply cr3_neutral C _ _ h_neutral'
            exact ihP P'_arg hP' hP'_red (by unfold IsNeutral; trivial)

  | prod A C ihA ihC =>
    intro M N hM_sn hN_sn hbeta_red hM'_red hN'_red
    unfold Reducible at hbeta_red hM'_red hN'_red ⊢
    constructor
    · -- fst (app (lam M) N) is reducible at A
      have h_neutral : IsNeutral (Term.fst (Term.app (Term.lam M) N)) := by unfold IsNeutral; trivial
      apply cr3_neutral A _ _ h_neutral
      induction hM_sn generalizing N with
      | intro Mb hMb_acc ihMb =>
        induction hN_sn with
        | intro Nb hNb_acc ihNb =>
          intro Q hQ
          cases hQ with
          | fst hApp =>
            cases hApp with
            | beta => exact hbeta_red.1
            | appL hLam =>
              cases hLam with
              | @lam _ Mb' hMb' =>
                have hbeta_red' := hM'_red _ hMb'
                have hMb''_red : ∀ M'', Step Mb' M'' → Reducible (Ty.prod A C) (Term.subst0 Nb M'') :=
                  fun M'' hM'' => cr2_reducible_red (Ty.prod A C) _ _ hbeta_red' (subst0_step_left hM'')
                have hNb'_red : ∀ N', Step Nb N' → Reducible (Ty.prod A C) (Term.subst0 N' Mb') :=
                  fun N' hN' => cr2_reducible_red (Ty.prod A C) _ _ (hN'_red N' hN') (subst0_step_left hMb')
                have h_neutral' : IsNeutral (Term.fst (Term.app (Term.lam Mb') Nb)) := by unfold IsNeutral; trivial
                apply cr3_neutral A _ _ h_neutral'
                exact ihMb _ hMb' Nb (Acc.intro Nb hNb_acc) hbeta_red' hMb''_red hNb'_red h_neutral'
            | @appR _ _ Nb' hNb' =>
              have hbeta_red' := hN'_red _ hNb'
              have hMb'_red : ∀ M', Step Mb M' → Reducible (Ty.prod A C) (Term.subst0 Nb' M') :=
                fun M' hM' => cr2_reducible_red (Ty.prod A C) _ _ hbeta_red' (subst0_step_left hM')
              have hNb''_red : ∀ N'', Step Nb' N'' → Reducible (Ty.prod A C) (Term.subst0 N'' Mb) :=
                fun N'' hN'' => cr2_reducible_red_multi (Ty.prod A C) _ _ hbeta_red' (subst0_step_right hN'')
              have h_neutral' : IsNeutral (Term.fst (Term.app (Term.lam Mb) Nb')) := by unfold IsNeutral; trivial
              apply cr3_neutral A _ _ h_neutral'
              exact ihNb _ hNb' hbeta_red' hMb'_red hNb''_red h_neutral'
    · -- snd (app (lam M) N) is reducible at C
      have h_neutral : IsNeutral (Term.snd (Term.app (Term.lam M) N)) := by unfold IsNeutral; trivial
      apply cr3_neutral C _ _ h_neutral
      induction hM_sn generalizing N with
      | intro Mb hMb_acc ihMb =>
        induction hN_sn with
        | intro Nb hNb_acc ihNb =>
          intro Q hQ
          cases hQ with
          | snd hApp =>
            cases hApp with
            | beta => exact hbeta_red.2
            | appL hLam =>
              cases hLam with
              | @lam _ Mb' hMb' =>
                have hbeta_red' := hM'_red _ hMb'
                have hMb''_red : ∀ M'', Step Mb' M'' → Reducible (Ty.prod A C) (Term.subst0 Nb M'') :=
                  fun M'' hM'' => cr2_reducible_red (Ty.prod A C) _ _ hbeta_red' (subst0_step_left hM'')
                have hNb'_red : ∀ N', Step Nb N' → Reducible (Ty.prod A C) (Term.subst0 N' Mb') :=
                  fun N' hN' => cr2_reducible_red (Ty.prod A C) _ _ (hN'_red N' hN') (subst0_step_left hMb')
                have h_neutral' : IsNeutral (Term.snd (Term.app (Term.lam Mb') Nb)) := by unfold IsNeutral; trivial
                apply cr3_neutral C _ _ h_neutral'
                exact ihMb _ hMb' Nb (Acc.intro Nb hNb_acc) hbeta_red' hMb''_red hNb'_red h_neutral'
            | @appR _ _ Nb' hNb' =>
              have hbeta_red' := hN'_red _ hNb'
              have hMb'_red : ∀ M', Step Mb M' → Reducible (Ty.prod A C) (Term.subst0 Nb' M') :=
                fun M' hM' => cr2_reducible_red (Ty.prod A C) _ _ hbeta_red' (subst0_step_left hM')
              have hNb''_red : ∀ N'', Step Nb' N'' → Reducible (Ty.prod A C) (Term.subst0 N'' Mb) :=
                fun N'' hN'' => cr2_reducible_red_multi (Ty.prod A C) _ _ hbeta_red' (subst0_step_right hN'')
              have h_neutral' : IsNeutral (Term.snd (Term.app (Term.lam Mb) Nb')) := by unfold IsNeutral; trivial
              apply cr3_neutral C _ _ h_neutral'
              exact ihNb _ hNb' hbeta_red' hMb'_red hNb''_red h_neutral'

  | sum A C ihA ihC =>
    intro M N hM_sn hN_sn hbeta_red hM'_red hN'_red
    unfold Reducible at hbeta_red hM'_red hN'_red ⊢
    -- Don't destructure hbeta_red - keep it as triple for IH generalization
    refine ⟨?sn, ?inl_case, ?inr_case⟩
    -- For inl/inr cases, we use nested SN induction to trace the multi-step path
    case inl_case =>
      -- Prove: ∀ V, app (lam M) N →* inl V → Reducible A V
      -- IH returns the same type: ∀ V, app (lam Ms') Ns →* inl V → Reducible A V
      induction hM_sn generalizing N with
      | intro Ms hMs_acc ihMs =>
        induction hN_sn with
        | intro Ns hNs_acc ihNs =>
          intro V hVred
          -- app (lam Ms) Ns →* inl V must be at least one step (structural difference)
          cases hVred with
          | step hstep hrest =>
            cases hstep with
            | beta => exact hbeta_red.2.1 V hrest
            | appL hstep_lam =>
              cases hstep_lam with
              | @lam _ Ms' hMsStep =>
                have hMs'_red := hM'_red Ms' hMsStep
                have hMs''_red : ∀ M'', Step Ms' M'' → Reducible (Ty.sum A C) (Term.subst0 Ns M'') :=
                  fun M'' hM'' => cr2_reducible_red (Ty.sum A C) _ _ hMs'_red (subst0_step_left hM'')
                have hNs'_red' : ∀ N', Step Ns N' → Reducible (Ty.sum A C) (Term.subst0 N' Ms') :=
                  fun N' hN' => cr2_reducible_red (Ty.sum A C) _ _ (hN'_red N' hN') (subst0_step_left hMsStep)
                exact ihMs Ms' hMsStep Ns (Acc.intro Ns hNs_acc) hMs'_red hMs''_red hNs'_red' V hrest
            | @appR _ _ Ns' hNsStep =>
              have hNs'_red := hN'_red Ns' hNsStep
              have hMs'_red' : ∀ M', Step Ms M' → Reducible (Ty.sum A C) (Term.subst0 Ns' M') :=
                fun M' hM' => cr2_reducible_red (Ty.sum A C) _ _ hNs'_red (subst0_step_left hM')
              have hNs''_red : ∀ N'', Step Ns' N'' → Reducible (Ty.sum A C) (Term.subst0 N'' Ms) :=
                fun N'' hN'' => cr2_reducible_red_multi (Ty.sum A C) _ _ hNs'_red (subst0_step_right hN'')
              exact ihNs Ns' hNsStep hNs'_red hMs'_red' hNs''_red V hrest
    case inr_case =>
      -- Similar to inl_case, for inr
      -- IH returns: ∀ V, app (lam Ms') Ns →* inr V → Reducible C V
      induction hM_sn generalizing N with
      | intro Ms hMs_acc ihMs =>
        induction hN_sn with
        | intro Ns hNs_acc ihNs =>
          intro V hVred
          cases hVred with
          | step hstep hrest =>
            cases hstep with
            | beta => exact hbeta_red.2.2 V hrest
            | appL hstep_lam =>
              cases hstep_lam with
              | @lam _ Ms' hMsStep =>
                have hMs'_red := hM'_red Ms' hMsStep
                have hMs''_red : ∀ M'', Step Ms' M'' → Reducible (Ty.sum A C) (Term.subst0 Ns M'') :=
                  fun M'' hM'' => cr2_reducible_red (Ty.sum A C) _ _ hMs'_red (subst0_step_left hM'')
                have hNs'_red' : ∀ N', Step Ns N' → Reducible (Ty.sum A C) (Term.subst0 N' Ms') :=
                  fun N' hN' => cr2_reducible_red (Ty.sum A C) _ _ (hN'_red N' hN') (subst0_step_left hMsStep)
                exact ihMs Ms' hMsStep Ns (Acc.intro Ns hNs_acc) hMs'_red hMs''_red hNs'_red' V hrest
            | @appR _ _ Ns' hNsStep =>
              have hNs'_red := hN'_red Ns' hNsStep
              have hMs'_red' : ∀ M', Step Ms M' → Reducible (Ty.sum A C) (Term.subst0 Ns' M') :=
                fun M' hM' => cr2_reducible_red (Ty.sum A C) _ _ hNs'_red (subst0_step_left hM')
              have hNs''_red : ∀ N'', Step Ns' N'' → Reducible (Ty.sum A C) (Term.subst0 N'' Ms) :=
                fun N'' hN'' => cr2_reducible_red_multi (Ty.sum A C) _ _ hNs'_red (subst0_step_right hN'')
              exact ihNs Ns' hNsStep hNs'_red hMs'_red' hNs''_red V hrest
    case sn =>
      -- IH returns: SN (app (lam Ms') Ns)
      induction hM_sn generalizing N with
      | intro Ms hMs_acc ihMs =>
        induction hN_sn with
        | intro Ns hNs_acc ihNs =>
          apply sn_intro
          intro P hP
          cases hP with
          | beta => exact hbeta_red.1
          | appL hstep_lam =>
            cases hstep_lam with
            | @lam _ Ms' hMsStep =>
              have hMs'_red := hM'_red _ hMsStep
              have hMs''_red : ∀ M'', Step Ms' M'' → Reducible (Ty.sum A C) (Term.subst0 Ns M'') :=
                fun M'' hM'' => cr2_reducible_red (Ty.sum A C) _ _ hMs'_red (subst0_step_left hM'')
              have hNs'_red' : ∀ N', Step Ns N' → Reducible (Ty.sum A C) (Term.subst0 N' Ms') :=
                fun N' hN' => cr2_reducible_red (Ty.sum A C) _ _ (hN'_red N' hN') (subst0_step_left hMsStep)
              exact ihMs _ hMsStep Ns (Acc.intro Ns hNs_acc) hMs'_red hMs''_red hNs'_red'
          | @appR _ _ Ns' hNsStep =>
            have hNs'_red := hN'_red _ hNsStep
            have hMs'_red' : ∀ M', Step Ms M' → Reducible (Ty.sum A C) (Term.subst0 Ns' M') :=
              fun M' hM' => cr2_reducible_red (Ty.sum A C) _ _ hNs'_red (subst0_step_left hM')
            have hNs''_red : ∀ N'', Step Ns' N'' → Reducible (Ty.sum A C) (Term.subst0 N'' Ms) :=
              fun N'' hN'' => cr2_reducible_red_multi (Ty.sum A C) _ _ hNs'_red (subst0_step_right hN'')
            exact ihNs _ hNsStep hNs'_red hMs'_red' hNs''_red

  | unit =>
    intro M N hM_sn hN_sn hbeta_red hM'_red hN'_red
    unfold Reducible at hbeta_red hM'_red hN'_red
    induction hM_sn generalizing N with
    | intro M hM_acc ihM =>
      induction hN_sn with
      | intro N hN_acc ihN =>
        apply sn_intro
        intro P hP
        cases hP with
        | beta => exact hbeta_red
        | appL hstep_lam =>
          cases hstep_lam with
          | lam hM'' =>
            apply ihM _ hM'' N (Acc.intro N hN_acc)
            · exact hM'_red _ hM''
            · intro M''' hM'''; exact sn_of_step (hM'_red _ hM'') (subst0_step_left hM''')
            · intro N' hN'_step; exact sn_of_step (hN'_red N' hN'_step) (subst0_step_left hM'')
        | appR hN'' =>
          apply ihN _ hN''
          · exact hN'_red _ hN''
          · intro M' hM'_step; exact sn_of_multi (hM'_red M' hM'_step) (subst0_step_right hN'')
          · intro N' hN'_step; exact sn_of_multi (hN'_red _ hN'') (subst0_step_right hN'_step)

/-! ## Reducibility of Pairs -/

/-- Helper: fst (pair M N) is reducible at A when M and N are SN and M is reducible -/
theorem reducible_fst_pair (A : Ty) (_B : Ty) (M N : Term)
    (hM_red : Reducible A M) (hN_sn : SN N) : Reducible A (Term.fst (Term.pair M N)) := by
  -- fst (pair M N) is NOT neutral (it's a fstPair redex), so we can't use CR3 directly.
  -- Instead, prove by induction on type A FIRST (outside), then SN induction inside each case.
  have hM_sn := cr1_reducible_sn A M hM_red
  -- Induct on type FIRST to avoid complex IH interactions from nested generalizing
  induction A using Ty.rec generalizing M N with
  | base a =>
    -- Reducible (base a) = SN. Show SN (fst (pair M N)) by showing all reducts are SN.
    induction hM_sn generalizing N with
    | intro M hM_acc ihM =>
      induction hN_sn with
      | intro N hN_acc ihN =>
        apply sn_intro
        intro Q hQ
        cases hQ with
        | fstPair => exact hM_red
        | fst hP =>
          cases hP with
          | @pairL _ M' _ hM' =>
            have hM'_red := cr2_reducible_red (Ty.base a) M _ hM_red hM'
            exact ihM M' hM' N hM'_red (Acc.intro N hN_acc)
          | pairR hN' =>
            exact ihN _ hN'
  | arr A' B' ihA' ihB' =>
    -- Reducible (arr A' B') M = ∀ P, Reducible A' P → Reducible B' (app M P)
    unfold Reducible
    intro P hP
    -- Show Reducible B' (app (fst (pair M N)) P)
    -- app (fst (pair M N)) P IS neutral (head is fst, not lam)
    have hP_sn := cr1_reducible_sn A' P hP
    apply (cr_props_all B').2  -- CR3
    · -- Prove all reducts are reducible
      -- We need nested SN induction on M, N, and P
      induction hM_sn generalizing N P with
      | intro M hM_acc ihM =>
        induction hN_sn generalizing P with
        | intro N hN_acc ihN =>
          induction hP_sn with
          | intro P hP_acc ihP =>
            intro Q hQ
            cases hQ with
            | appL hstep =>
              cases hstep with
              | fstPair =>
                -- app (fst (pair M N)) P → app M P via fstPair
                unfold Reducible at hM_red
                exact hM_red P hP
              | fst hP' =>
                cases hP' with
                | @pairL _ M' _ hM' =>
                  have hM'_red := cr2_reducible_red (Ty.arr A' B') M _ hM_red hM'
                  -- Use ihM (SN recursion on M) to get CR3 argument
                  apply cr3_neutral B' (Term.app (Term.fst (Term.pair M' N)) P)
                  · exact ihM M' hM' N hM'_red (Acc.intro N hN_acc) P hP (Acc.intro P hP_acc)
                  · unfold IsNeutral; trivial
                | @pairR _ _ N' hN' =>
                  -- Use ihN (SN recursion on N)
                  apply cr3_neutral B' (Term.app (Term.fst (Term.pair M N')) P)
                  · exact ihN N' hN' P hP (Acc.intro P hP_acc)
                  · unfold IsNeutral; trivial
            | @appR _ _ P' hP' =>
              have hP'_red := cr2_reducible_red A' P _ hP hP'
              apply cr3_neutral B' (Term.app (Term.fst (Term.pair M N)) P')
              · exact ihP P' hP' hP'_red
              · unfold IsNeutral; trivial
    · unfold IsNeutral; trivial
  | prod A' B' ihA' ihB' =>
    -- Reducible (prod A' B') M = Reducible A' (fst M) ∧ Reducible B' (snd M)
    -- Goal: Reducible (prod A' B') (fst (pair M N))
    --     = Reducible A' (fst (fst (pair M N))) ∧ Reducible B' (snd (fst (pair M N)))
    -- Have: hM_red : Reducible A' (fst M) ∧ Reducible B' (snd M)
    -- Key: fst (fst (pair M N)) →₁ fst M, and snd (fst (pair M N)) →₁ snd M
    -- Use CR3 on each component - fst/snd of fst(...) is "neutral enough"
    unfold Reducible
    unfold Reducible at hM_red
    constructor
    · -- Reducible A' (fst (fst (pair M N)))
      -- fst (fst (pair M N)) is neutral (head is fst, not pair)
      -- All reducts: fst M (via inner fstPair), fst (fst (pair M' N)), fst (fst (pair M N'))
      induction hM_sn generalizing N with
      | intro M hM_acc ihM =>
        induction hN_sn with
        | intro N hN_acc ihN =>
          apply cr3_neutral A' (Term.fst (Term.fst (Term.pair M N)))
          · intro Q hQ
            -- hQ : fst (fst (pair M N)) →₁ Q
            -- fstPair can't apply because fst (pair M N) is not a pair
            cases hQ with
            | fst hP =>
              -- hP : fst (pair M N) →₁ P for some P, and Q = fst P
              cases hP with
              | fstPair =>
                -- Q = fst M, need Reducible A' (fst M) = hM_red.1
                exact hM_red.1
              | fst hInner =>
                -- hInner : pair M N →₁ P', Q = fst (fst P')
                cases hInner with
                | @pairL _ M' _ hM' =>
                  -- ihM returns a function expecting Reducible (prod A' B') M'
                  have hM'_red := cr2_reducible_red (Ty.prod A' B') M _ ⟨hM_red.1, hM_red.2⟩ hM'
                  unfold Reducible at hM'_red
                  exact ihM M' hM' N (Acc.intro N hN_acc) hM'_red
                | pairR hN' =>
                  exact ihN _ hN'
          · unfold IsNeutral; trivial
    · -- Reducible B' (snd (fst (pair M N)))
      -- Same approach
      induction hM_sn generalizing N with
      | intro M hM_acc ihM =>
        induction hN_sn with
        | intro N hN_acc ihN =>
          apply cr3_neutral B' (Term.snd (Term.fst (Term.pair M N)))
          · intro Q hQ
            -- hQ : snd (fst (pair M N)) →₁ Q
            -- sndPair can't apply because fst (pair M N) is not a pair
            cases hQ with
            | snd hP =>
              -- hP : fst (pair M N) →₁ P
              cases hP with
              | fstPair =>
                -- Q = snd M
                exact hM_red.2
              | fst hInner =>
                cases hInner with
                | @pairL _ M' _ hM' =>
                  have hM'_red := cr2_reducible_red (Ty.prod A' B') M _ ⟨hM_red.1, hM_red.2⟩ hM'
                  unfold Reducible at hM'_red
                  exact ihM M' hM' N (Acc.intro N hN_acc) hM'_red
                | pairR hN' =>
                  exact ihN _ hN'
          · unfold IsNeutral; trivial
  | sum A' B' ihA' ihB' =>
    -- Reducible (sum A' B') M = SN M ∧ (∀ V, M →* inl V → Reducible A' V) ∧ (∀ V, M →* inr V → Reducible B' V)
    unfold Reducible
    unfold Reducible at hM_red
    refine ⟨?_, ?_, ?_⟩
    · -- SN (fst (pair M N))
      induction hM_sn generalizing N with
      | intro M hM_acc ihM =>
        induction hN_sn with
        | intro N hN_acc ihN =>
          apply sn_intro
          intro Q hQ
          cases hQ with
          | fstPair => exact hM_red.1
          | fst hP =>
            cases hP with
            | pairL hM' =>
              -- ihM returns a function expecting Reducible (sum A' B') M'
              have hM'_red := cr2_reducible_red (Ty.sum A' B') M _ ⟨hM_red.1, hM_red.2.1, hM_red.2.2⟩ hM'
              exact ihM _ hM' N (Acc.intro N hN_acc) hM'_red
            | pairR hN' =>
              exact ihN _ hN'
    · -- ∀ V, fst (pair M N) →* inl V → Reducible A' V
      intro V hVred
      -- fst (pair M N) cannot equal inl V (different head constructors), so must step first
      induction hM_sn generalizing N V with
      | intro M hM_acc ihM =>
        induction hN_sn generalizing V with
        | intro N hN_acc ihN =>
          -- refl case is impossible: fst (pair M N) ≠ inl V
          cases hVred with
          | step hstep hrest =>
            cases hstep with
            | fstPair => exact hM_red.2.1 V hrest
            | fst hP =>
              cases hP with
              | pairL hM' =>
                have hM'_red := cr2_reducible_red (Ty.sum A' B') M _ ⟨hM_red.1, hM_red.2.1, hM_red.2.2⟩ hM'
                exact ihM _ hM' N (Acc.intro N hN_acc) hM'_red V hrest
              | pairR hN' =>
                exact ihN _ hN' V hrest
    · -- ∀ V, fst (pair M N) →* inr V → Reducible B' V
      intro V hVred
      induction hM_sn generalizing N V with
      | intro M hM_acc ihM =>
        induction hN_sn generalizing V with
        | intro N hN_acc ihN =>
          cases hVred with
          | step hstep hrest =>
            cases hstep with
            | fstPair => exact hM_red.2.2 V hrest
            | fst hP =>
              cases hP with
              | pairL hM' =>
                have hM'_red := cr2_reducible_red (Ty.sum A' B') M _ ⟨hM_red.1, hM_red.2.1, hM_red.2.2⟩ hM'
                exact ihM _ hM' N (Acc.intro N hN_acc) hM'_red V hrest
              | pairR hN' =>
                exact ihN _ hN' V hrest
  | unit =>
    -- Reducible unit = SN. Show SN (fst (pair M N)) by showing all reducts are SN.
    induction hM_sn generalizing N with
    | intro M hM_acc ihM =>
      induction hN_sn with
      | intro N hN_acc ihN =>
        apply sn_intro
        intro Q hQ
        cases hQ with
        | fstPair => exact hM_red
        | fst hP =>
          cases hP with
          | @pairL _ M' _ hM' =>
            have hM'_red := cr2_reducible_red Ty.unit M _ hM_red hM'
            exact ihM M' hM' N hM'_red (Acc.intro N hN_acc)
          | pairR hN' =>
            exact ihN _ hN'

/-- Helper: snd (pair M N) is reducible at B when M and N are SN and N is reducible -/
theorem reducible_snd_pair (_A : Ty) (B : Ty) (M N : Term)
    (hM_sn : SN M) (hN_red : Reducible B N) : Reducible B (Term.snd (Term.pair M N)) := by
  -- Similar to reducible_fst_pair, but for snd
  -- Induct on type FIRST (outside), then SN induction inside each case
  have hN_sn := cr1_reducible_sn B N hN_red
  induction B using Ty.rec generalizing M N with
  | base b =>
    -- Reducible (base b) = SN. Show SN (snd (pair M N)) by showing all reducts are SN.
    induction hM_sn generalizing N with
    | intro M hM_acc ihM =>
      induction hN_sn with
      | intro N hN_acc ihN =>
        apply sn_intro
        intro Q hQ
        cases hQ with
        | sndPair => exact hN_red
        | snd hP =>
          cases hP with
          | pairL hM' =>
            -- ihM : ∀ M', M →₁ M' → ∀ N, SN N → Reducible (base b) N → SN (snd (pair M' N))
            exact ihM _ hM' N (Acc.intro N hN_acc) hN_red
          | pairR hN' =>
            have hN'_red := cr2_reducible_red (Ty.base b) N _ hN_red hN'
            exact ihN _ hN' hN'_red
  | arr A' B' ihA' ihB' =>
    -- Reducible (arr A' B') N = ∀ P, Reducible A' P → Reducible B' (app N P)
    unfold Reducible
    intro P hP
    have hP_sn := cr1_reducible_sn A' P hP
    apply (cr_props_all B').2
    · -- Prove all reducts are reducible
      induction hM_sn generalizing N P with
      | intro M hM_acc ihM =>
        induction hN_sn generalizing P with
        | intro N hN_acc ihN =>
          induction hP_sn with
          | intro P hP_acc ihP =>
            intro Q hQ
            cases hQ with
            | appL hstep =>
              cases hstep with
              | sndPair =>
                unfold Reducible at hN_red
                exact hN_red P hP
              | snd hP' =>
                cases hP' with
                | pairL hM' =>
                  -- ihM returns CR3-style, apply CR3 to get Reducible
                  have hN_sn' : SN N := Acc.intro N hN_acc
                  have hP_sn' : SN P := Acc.intro P hP_acc
                  apply (cr_props_all B').2
                  · exact ihM _ hM' N hN_red hN_sn' P hP hP_sn'
                  · unfold IsNeutral; trivial
                | pairR hN' =>
                  have hP_sn' : SN P := Acc.intro P hP_acc
                  have hN'_red := cr2_reducible_red (Ty.arr A' B') N _ hN_red hN'
                  apply (cr_props_all B').2
                  · exact ihN _ hN' hN'_red P hP hP_sn'
                  · unfold IsNeutral; trivial
            | appR hP' =>
              have hP'_red := cr2_reducible_red A' P _ hP hP'
              -- ihP returns CR3-style, need to apply CR3 to get final result
              apply (cr_props_all B').2
              · exact ihP _ hP' hP'_red
              · unfold IsNeutral; trivial
    · unfold IsNeutral; trivial
  | prod A' B' ihA' ihB' =>
    -- Goal: Reducible (prod A' B') (snd (pair M N))
    --     = Reducible A' (fst (snd (pair M N))) ∧ Reducible B' (snd (snd (pair M N)))
    -- hN_red : Reducible A' (fst N) ∧ Reducible B' (snd N)
    -- Key: fst (snd (pair M N)) →* fst N via sndPair, similarly for snd
    unfold Reducible
    unfold Reducible at hN_red
    constructor
    · -- Reducible A' (fst (snd (pair M N)))
      -- fst (snd (pair M N)) is neutral, use CR3
      induction hM_sn generalizing N with
      | intro M hM_acc ihM =>
        induction hN_sn with
        | intro N hN_acc ihN =>
          apply cr3_neutral A' (Term.fst (Term.snd (Term.pair M N)))
          · intro Q hQ
            cases hQ with
            | fst hP =>
              cases hP with
              | sndPair => exact hN_red.1
              | snd hInner =>
                cases hInner with
                | @pairL _ M' _ hM' =>
                  exact ihM M' hM' N (Acc.intro N hN_acc) hN_red
                | pairR hN' =>
                  have hN'_red := cr2_reducible_red (Ty.prod A' B') N _ ⟨hN_red.1, hN_red.2⟩ hN'
                  unfold Reducible at hN'_red
                  exact ihN _ hN' hN'_red
          · unfold IsNeutral; trivial
    · -- Reducible B' (snd (snd (pair M N)))
      induction hM_sn generalizing N with
      | intro M hM_acc ihM =>
        induction hN_sn with
        | intro N hN_acc ihN =>
          apply cr3_neutral B' (Term.snd (Term.snd (Term.pair M N)))
          · intro Q hQ
            cases hQ with
            | snd hP =>
              cases hP with
              | sndPair => exact hN_red.2
              | snd hInner =>
                cases hInner with
                | @pairL _ M' _ hM' =>
                  exact ihM M' hM' N (Acc.intro N hN_acc) hN_red
                | pairR hN' =>
                  have hN'_red := cr2_reducible_red (Ty.prod A' B') N _ ⟨hN_red.1, hN_red.2⟩ hN'
                  unfold Reducible at hN'_red
                  exact ihN _ hN' hN'_red
          · unfold IsNeutral; trivial
  | sum A' B' ihA' ihB' =>
    -- Reducible (sum A' B') N = SN N ∧ (∀ V, N →* inl V → Reducible A' V) ∧ (∀ V, N →* inr V → Reducible B' V)
    unfold Reducible
    unfold Reducible at hN_red
    refine ⟨?_, ?_, ?_⟩
    · -- SN (snd (pair M N))
      induction hM_sn generalizing N with
      | intro M hM_acc ihM =>
        induction hN_sn with
        | intro N hN_acc ihN =>
          apply sn_intro
          intro Q hQ
          cases hQ with
          | sndPair => exact hN_red.1
          | snd hP =>
            cases hP with
            | pairL hM' =>
              -- ihM : ∀ M', M →₁ M' → ∀ N, SN N → Reducible (sum A' B') N → SN (snd (pair M' N))
              have hN_red' : Reducible (Ty.sum A' B') N := ⟨hN_red.1, hN_red.2.1, hN_red.2.2⟩
              exact ihM _ hM' N (Acc.intro N hN_acc) hN_red'
            | pairR hN' =>
              have hN'_red := cr2_reducible_red (Ty.sum A' B') N _ ⟨hN_red.1, hN_red.2.1, hN_red.2.2⟩ hN'
              exact ihN _ hN' hN'_red
    · -- ∀ V, snd (pair M N) →* inl V → Reducible A' V
      intro V hVred
      -- snd (pair M N) cannot equal inl V, so must step first
      induction hM_sn generalizing N V with
      | intro M hM_acc ihM =>
        induction hN_sn generalizing V with
        | intro N hN_acc ihN =>
          cases hVred with
          | step hstep hrest =>
            cases hstep with
            | sndPair => exact hN_red.2.1 V hrest
            | snd hP =>
              cases hP with
              | pairL hM' =>
                have hN_red' : Reducible (Ty.sum A' B') N := ⟨hN_red.1, hN_red.2.1, hN_red.2.2⟩
                exact ihM _ hM' N (Acc.intro N hN_acc) hN_red' V hrest
              | pairR hN' =>
                have hN'_red := cr2_reducible_red (Ty.sum A' B') N _ ⟨hN_red.1, hN_red.2.1, hN_red.2.2⟩ hN'
                exact ihN _ hN' hN'_red V hrest
    · -- ∀ V, snd (pair M N) →* inr V → Reducible B' V
      intro V hVred
      induction hM_sn generalizing N V with
      | intro M hM_acc ihM =>
        induction hN_sn generalizing V with
        | intro N hN_acc ihN =>
          cases hVred with
          | step hstep hrest =>
            cases hstep with
            | sndPair => exact hN_red.2.2 V hrest
            | snd hP =>
              cases hP with
              | pairL hM' =>
                have hN_red' : Reducible (Ty.sum A' B') N := ⟨hN_red.1, hN_red.2.1, hN_red.2.2⟩
                exact ihM _ hM' N (Acc.intro N hN_acc) hN_red' V hrest
              | pairR hN' =>
                have hN'_red := cr2_reducible_red (Ty.sum A' B') N _ ⟨hN_red.1, hN_red.2.1, hN_red.2.2⟩ hN'
                exact ihN _ hN' hN'_red V hrest
  | unit =>
    -- Reducible unit = SN. Show SN (snd (pair M N)) by showing all reducts are SN.
    induction hM_sn generalizing N with
    | intro M hM_acc ihM =>
      induction hN_sn with
      | intro N hN_acc ihN =>
        apply sn_intro
        intro Q hQ
        cases hQ with
        | sndPair => exact hN_red
        | snd hP =>
          cases hP with
          | pairL hM' =>
            exact ihM _ hM' N (Acc.intro N hN_acc) hN_red
          | pairR hN' =>
            have hN'_red := cr2_reducible_red Ty.unit N _ hN_red hN'
            exact ihN _ hN' hN'_red

/-- Pairs are reducible if components are reducible -/
theorem reducible_pair {A B : Ty} {M N : Term}
    (hM : Reducible A M) (hN : Reducible B N) : Reducible (Ty.prod A B) (Term.pair M N) := by
  unfold Reducible
  constructor
  · exact reducible_fst_pair A B M N hM (cr1_reducible_sn B N hN)
  · exact reducible_snd_pair A B M N (cr1_reducible_sn A M hM) hN

/-! ## Reducibility of Case Expressions -/

/-- Key lemma: case M N₁ N₂ is reducible when branches are appropriately reducible -/
theorem reducible_case (C' A' B' : Ty) (M N₁ N₂ : Term)
    (hM_sn : SN M) (hN₁_sn : SN N₁) (hN₂_sn : SN N₂)
    (hM_inl : ∀ V, M ⟶* Term.inl V → Reducible A' V)
    (hM_inr : ∀ V, M ⟶* Term.inr V → Reducible B' V)
    (hInlRed : ∀ V, M ⟶* Term.inl V → Reducible C' (Term.subst0 V N₁))
    (hInrRed : ∀ V, M ⟶* Term.inr V → Reducible C' (Term.subst0 V N₂)) :
    Reducible C' (Term.case M N₁ N₂) := by
  -- Helper for SN (used for base types and sum type's SN component)
  have sn_case_helper : ∀ (M : Term) (N₁ N₂ : Term),
      SN M → SN N₁ → SN N₂ →
      (∀ V, M ⟶* Term.inl V → Reducible A' V) →
      (∀ V, M ⟶* Term.inr V → Reducible B' V) →
      (∀ V, M ⟶* Term.inl V → Reducible C' (Term.subst0 V N₁)) →
      (∀ V, M ⟶* Term.inr V → Reducible C' (Term.subst0 V N₂)) →
      SN (Term.case M N₁ N₂) := by
    intro M N₁ N₂ hM_sn hN₁_sn hN₂_sn hM_inl' hM_inr' hInlRed hInrRed
    induction hM_sn generalizing N₁ N₂ with
    | intro M hM_acc ihM =>
      induction hN₁_sn generalizing N₂ with
      | intro N₁ hN₁_acc ihN₁ =>
        induction hN₂_sn with
        | intro N₂ hN₂_acc ihN₂ =>
          apply sn_intro
          intro T hT
          cases hT with
          | @caseInl V _ _ =>
            have hMred : Term.inl V ⟶* Term.inl V := MultiStep.refl _
            exact cr1_reducible_sn C' _ (hInlRed V hMred)
          | @caseInr V _ _ =>
            have hMred : Term.inr V ⟶* Term.inr V := MultiStep.refl _
            exact cr1_reducible_sn C' _ (hInrRed V hMred)
          | caseS hM' =>
            apply ihM _ hM' N₁ N₂ (Acc.intro N₁ hN₁_acc) (Acc.intro N₂ hN₂_acc)
            · intro V hM'red; exact hM_inl' V (MultiStep.step hM' hM'red)
            · intro V hM'red; exact hM_inr' V (MultiStep.step hM' hM'red)
            · intro V hM'red; exact hInlRed V (MultiStep.step hM' hM'red)
            · intro V hM'red; exact hInrRed V (MultiStep.step hM' hM'red)
          | caseL hN₁' =>
            apply ihN₁ _ hN₁' N₂ (Acc.intro N₂ hN₂_acc)
            · intro V hMred; exact cr2_reducible_red C' _ _ (hInlRed V hMred) (subst0_step_left hN₁')
            · exact hInrRed
          | caseR hN₂' =>
            apply ihN₂ _ hN₂'
            intro V hMred; exact cr2_reducible_red C' _ _ (hInrRed V hMred) (subst0_step_left hN₂')
  -- Now prove Reducible C' by case analysis on C'
  -- Note: We use `cases` instead of `induction` to avoid capturing type IHs in nested SN inductions
  cases C' with
  | base n =>
    unfold Reducible
    exact sn_case_helper M N₁ N₂ hM_sn hN₁_sn hN₂_sn hM_inl hM_inr hInlRed hInrRed
  | arr C1 C2 =>
    -- Reducible (C1 → C2) M = ∀ P, Reducible C1 P → Reducible C2 (app M P)
    -- app (case M N₁ N₂) P is ALWAYS neutral
    unfold Reducible
    intro P hP
    have hP_sn := cr1_reducible_sn C1 P hP
    have h_neutral : IsNeutral (Term.app (Term.case M N₁ N₂) P) := by unfold IsNeutral; trivial
    apply cr3_neutral C2 _ _ h_neutral
    -- Nested SN induction to show all reducts are reducible
    induction hM_sn generalizing N₁ N₂ P with
    | intro Ms hMs_acc ihMs =>
      induction hN₁_sn generalizing N₂ P with
      | intro N1s hN1s_acc ihN1s =>
        induction hN₂_sn generalizing P with
        | intro N2s hN2s_acc ihN2s =>
          induction hP_sn with
          | intro Ps hPs_acc ihPs =>
            intro Q hQ
            cases hQ with
            | appL hCase =>
              cases hCase with
              | @caseInl V _ _ =>
                have hMred : Term.inl V ⟶* Term.inl V := MultiStep.refl _
                have hSubstRed := hInlRed V hMred
                unfold Reducible at hSubstRed
                exact hSubstRed Ps hP
              | @caseInr V _ _ =>
                have hMred : Term.inr V ⟶* Term.inr V := MultiStep.refl _
                have hSubstRed := hInrRed V hMred
                unfold Reducible at hSubstRed
                exact hSubstRed Ps hP
              | @caseS _ Ms' _ _ hMs' =>
                have h_neutral' : IsNeutral (Term.app (Term.case Ms' N1s N2s) Ps) := by unfold IsNeutral; trivial
                apply cr3_neutral C2 _ _ h_neutral'
                have hInlRed' : ∀ V, Ms' ⟶* Term.inl V → Reducible (Ty.arr C1 C2) (Term.subst0 V N1s) := by
                  intro V hred
                  have h := hInlRed V (MultiStep.step hMs' hred)
                  unfold Reducible; unfold Reducible at h
                  exact h
                have hInrRed' : ∀ V, Ms' ⟶* Term.inr V → Reducible (Ty.arr C1 C2) (Term.subst0 V N2s) := by
                  intro V hred
                  have h := hInrRed V (MultiStep.step hMs' hred)
                  unfold Reducible; unfold Reducible at h
                  exact h
                have hM_inl' : ∀ V, Ms' ⟶* Term.inl V → Reducible A' V := fun V hred => hM_inl V (MultiStep.step hMs' hred)
                have hM_inr' : ∀ V, Ms' ⟶* Term.inr V → Reducible B' V := fun V hred => hM_inr V (MultiStep.step hMs' hred)
                exact ihMs Ms' hMs' N1s N2s (Acc.intro N1s hN1s_acc) (Acc.intro N2s hN2s_acc) hM_inl' hM_inr' hInlRed' hInrRed' Ps hP (Acc.intro Ps hPs_acc) h_neutral'
              | @caseL _ _ N1s' _ hN1s' =>
                have h_neutral' : IsNeutral (Term.app (Term.case Ms N1s' N2s) Ps) := by unfold IsNeutral; trivial
                apply cr3_neutral C2 _ _ h_neutral'
                have hInlRed' : ∀ V, Ms ⟶* Term.inl V → Reducible (Ty.arr C1 C2) (Term.subst0 V N1s') := by
                  intro V hred
                  have h := hInlRed V hred
                  have h' := cr2_reducible_red (Ty.arr C1 C2) _ _ h (subst0_step_left hN1s')
                  unfold Reducible; unfold Reducible at h'
                  exact h'
                exact ihN1s N1s' hN1s' N2s (Acc.intro N2s hN2s_acc) hInlRed' hInrRed Ps hP (Acc.intro Ps hPs_acc) h_neutral'
              | @caseR _ _ _ N2s' hN2s' =>
                have h_neutral' : IsNeutral (Term.app (Term.case Ms N1s N2s') Ps) := by unfold IsNeutral; trivial
                apply cr3_neutral C2 _ _ h_neutral'
                have hInrRed' : ∀ V, Ms ⟶* Term.inr V → Reducible (Ty.arr C1 C2) (Term.subst0 V N2s') := by
                  intro V hred
                  have h := hInrRed V hred
                  have h' := cr2_reducible_red (Ty.arr C1 C2) _ _ h (subst0_step_left hN2s')
                  unfold Reducible; unfold Reducible at h'
                  exact h'
                exact ihN2s N2s' hN2s' hInrRed' Ps hP (Acc.intro Ps hPs_acc) h_neutral'
            | @appR _ _ Ps' hPs' =>
              have hPs'_red := cr2_reducible_red C1 _ _ hP hPs'
              have h_neutral' : IsNeutral (Term.app (Term.case Ms N1s N2s) Ps') := by unfold IsNeutral; trivial
              apply cr3_neutral C2 _ _ h_neutral'
              exact ihPs Ps' hPs' hPs'_red h_neutral'
  | prod C1 C2 =>
    -- Reducible (C1 × C2) M = Reducible C1 (fst M) ∧ Reducible C2 (snd M)
    unfold Reducible
    constructor
    · -- Reducible C1 (fst (case M N₁ N₂))
      have h_neutral : IsNeutral (Term.fst (Term.case M N₁ N₂)) := by unfold IsNeutral; trivial
      apply cr3_neutral C1 _ _ h_neutral
      induction hM_sn generalizing N₁ N₂ with
      | intro Ms hMs_acc ihMs =>
        induction hN₁_sn generalizing N₂ with
        | intro N1s hN1s_acc ihN1s =>
          induction hN₂_sn with
          | intro N2s hN2s_acc ihN2s =>
            intro Q hQ
            cases hQ with
            | fst hCase =>
              cases hCase with
              | @caseInl V _ _ =>
                have hMred : Term.inl V ⟶* Term.inl V := MultiStep.refl _
                have hSubstRed := hInlRed V hMred
                unfold Reducible at hSubstRed
                exact hSubstRed.1
              | @caseInr V _ _ =>
                have hMred : Term.inr V ⟶* Term.inr V := MultiStep.refl _
                have hSubstRed := hInrRed V hMred
                unfold Reducible at hSubstRed
                exact hSubstRed.1
              | @caseS _ Ms' _ _ hMs' =>
                have h_neutral' : IsNeutral (Term.fst (Term.case Ms' N1s N2s)) := by unfold IsNeutral; trivial
                apply cr3_neutral C1 _ _ h_neutral'
                have hInlRed' : ∀ V, Ms' ⟶* Term.inl V → Reducible (Ty.prod C1 C2) (Term.subst0 V N1s) := by
                  intro V hred
                  have h := hInlRed V (MultiStep.step hMs' hred)
                  unfold Reducible; unfold Reducible at h; exact h
                have hInrRed' : ∀ V, Ms' ⟶* Term.inr V → Reducible (Ty.prod C1 C2) (Term.subst0 V N2s) := by
                  intro V hred
                  have h := hInrRed V (MultiStep.step hMs' hred)
                  unfold Reducible; unfold Reducible at h; exact h
                have hM_inl' : ∀ V, Ms' ⟶* Term.inl V → Reducible A' V := fun V hred => hM_inl V (MultiStep.step hMs' hred)
                have hM_inr' : ∀ V, Ms' ⟶* Term.inr V → Reducible B' V := fun V hred => hM_inr V (MultiStep.step hMs' hred)
                exact ihMs Ms' hMs' N1s N2s (Acc.intro N1s hN1s_acc) (Acc.intro N2s hN2s_acc) hM_inl' hM_inr' hInlRed' hInrRed' h_neutral'
              | @caseL _ _ N1s' _ hN1s' =>
                have h_neutral' : IsNeutral (Term.fst (Term.case Ms N1s' N2s)) := by unfold IsNeutral; trivial
                apply cr3_neutral C1 _ _ h_neutral'
                have hInlRed' : ∀ V, Ms ⟶* Term.inl V → Reducible (Ty.prod C1 C2) (Term.subst0 V N1s') := by
                  intro V hred
                  have h := hInlRed V hred
                  have h' := cr2_reducible_red (Ty.prod C1 C2) _ _ h (subst0_step_left hN1s')
                  unfold Reducible; unfold Reducible at h'; exact h'
                exact ihN1s N1s' hN1s' N2s (Acc.intro N2s hN2s_acc) hInlRed' hInrRed h_neutral'
              | @caseR _ _ _ N2s' hN2s' =>
                have h_neutral' : IsNeutral (Term.fst (Term.case Ms N1s N2s')) := by unfold IsNeutral; trivial
                apply cr3_neutral C1 _ _ h_neutral'
                have hInrRed' : ∀ V, Ms ⟶* Term.inr V → Reducible (Ty.prod C1 C2) (Term.subst0 V N2s') := by
                  intro V hred
                  have h := hInrRed V hred
                  have h' := cr2_reducible_red (Ty.prod C1 C2) _ _ h (subst0_step_left hN2s')
                  unfold Reducible; unfold Reducible at h'; exact h'
                exact ihN2s N2s' hN2s' hInrRed' h_neutral'
    · -- Reducible C2 (snd (case M N₁ N₂))
      have h_neutral : IsNeutral (Term.snd (Term.case M N₁ N₂)) := by unfold IsNeutral; trivial
      apply cr3_neutral C2 _ _ h_neutral
      induction hM_sn generalizing N₁ N₂ with
      | intro Ms hMs_acc ihMs =>
        induction hN₁_sn generalizing N₂ with
        | intro N1s hN1s_acc ihN1s =>
          induction hN₂_sn with
          | intro N2s hN2s_acc ihN2s =>
            intro Q hQ
            cases hQ with
            | snd hCase =>
              cases hCase with
              | @caseInl V _ _ =>
                have hMred : Term.inl V ⟶* Term.inl V := MultiStep.refl _
                have hSubstRed := hInlRed V hMred
                unfold Reducible at hSubstRed
                exact hSubstRed.2
              | @caseInr V _ _ =>
                have hMred : Term.inr V ⟶* Term.inr V := MultiStep.refl _
                have hSubstRed := hInrRed V hMred
                unfold Reducible at hSubstRed
                exact hSubstRed.2
              | @caseS _ Ms' _ _ hMs' =>
                have h_neutral' : IsNeutral (Term.snd (Term.case Ms' N1s N2s)) := by unfold IsNeutral; trivial
                apply cr3_neutral C2 _ _ h_neutral'
                have hInlRed' : ∀ V, Ms' ⟶* Term.inl V → Reducible (Ty.prod C1 C2) (Term.subst0 V N1s) := by
                  intro V hred
                  have h := hInlRed V (MultiStep.step hMs' hred)
                  unfold Reducible; unfold Reducible at h; exact h
                have hInrRed' : ∀ V, Ms' ⟶* Term.inr V → Reducible (Ty.prod C1 C2) (Term.subst0 V N2s) := by
                  intro V hred
                  have h := hInrRed V (MultiStep.step hMs' hred)
                  unfold Reducible; unfold Reducible at h; exact h
                have hM_inl' : ∀ V, Ms' ⟶* Term.inl V → Reducible A' V := fun V hred => hM_inl V (MultiStep.step hMs' hred)
                have hM_inr' : ∀ V, Ms' ⟶* Term.inr V → Reducible B' V := fun V hred => hM_inr V (MultiStep.step hMs' hred)
                exact ihMs Ms' hMs' N1s N2s (Acc.intro N1s hN1s_acc) (Acc.intro N2s hN2s_acc) hM_inl' hM_inr' hInlRed' hInrRed' h_neutral'
              | @caseL _ _ N1s' _ hN1s' =>
                have h_neutral' : IsNeutral (Term.snd (Term.case Ms N1s' N2s)) := by unfold IsNeutral; trivial
                apply cr3_neutral C2 _ _ h_neutral'
                have hInlRed' : ∀ V, Ms ⟶* Term.inl V → Reducible (Ty.prod C1 C2) (Term.subst0 V N1s') := by
                  intro V hred
                  have h := hInlRed V hred
                  have h' := cr2_reducible_red (Ty.prod C1 C2) _ _ h (subst0_step_left hN1s')
                  unfold Reducible; unfold Reducible at h'; exact h'
                exact ihN1s N1s' hN1s' N2s (Acc.intro N2s hN2s_acc) hInlRed' hInrRed h_neutral'
              | @caseR _ _ _ N2s' hN2s' =>
                have h_neutral' : IsNeutral (Term.snd (Term.case Ms N1s N2s')) := by unfold IsNeutral; trivial
                apply cr3_neutral C2 _ _ h_neutral'
                have hInrRed' : ∀ V, Ms ⟶* Term.inr V → Reducible (Ty.prod C1 C2) (Term.subst0 V N2s') := by
                  intro V hred
                  have h := hInrRed V hred
                  have h' := cr2_reducible_red (Ty.prod C1 C2) _ _ h (subst0_step_left hN2s')
                  unfold Reducible; unfold Reducible at h'; exact h'
                exact ihN2s N2s' hN2s' hInrRed' h_neutral'
  | sum C1 C2 =>
    -- Reducible (C1 ⊕ C2) M = SN M ∧ (∀ V, M ⟶* inl V → Reducible C1 V) ∧ (∀ V, M ⟶* inr V → Reducible C2 V)
    unfold Reducible
    refine ⟨?_, ?_, ?_⟩
    · -- SN (case M N₁ N₂)
      exact sn_case_helper M N₁ N₂ hM_sn hN₁_sn hN₂_sn hM_inl hM_inr hInlRed hInrRed
    · -- ∀ V, (case M N₁ N₂) ⟶* inl V → Reducible C1 V
      intro V hCaseRed
      induction hM_sn generalizing N₁ N₂ V with
      | intro Ms hMs_acc ihMs =>
        induction hN₁_sn generalizing N₂ V with
        | intro N1s hN1s_acc ihN1s =>
          induction hN₂_sn generalizing V with
          | intro N2s hN2s_acc ihN2s =>
            cases hCaseRed with
            | step hstep hrest =>
              cases hstep with
              | @caseInl W _ _ =>
                have hMred : Term.inl W ⟶* Term.inl W := MultiStep.refl _
                have hSubstRed := hInlRed W hMred
                unfold Reducible at hSubstRed
                exact hSubstRed.2.1 V hrest
              | @caseInr W _ _ =>
                have hMred : Term.inr W ⟶* Term.inr W := MultiStep.refl _
                have hSubstRed := hInrRed W hMred
                unfold Reducible at hSubstRed
                exact hSubstRed.2.1 V hrest
              | @caseS _ Ms' _ _ hMs' =>
                have hInlRed' : ∀ W, Ms' ⟶* Term.inl W → Reducible (Ty.sum C1 C2) (Term.subst0 W N1s) := by
                  intro W hred
                  have h := hInlRed W (MultiStep.step hMs' hred)
                  unfold Reducible; unfold Reducible at h; exact h
                have hInrRed' : ∀ W, Ms' ⟶* Term.inr W → Reducible (Ty.sum C1 C2) (Term.subst0 W N2s) := by
                  intro W hred
                  have h := hInrRed W (MultiStep.step hMs' hred)
                  unfold Reducible; unfold Reducible at h; exact h
                have hM_inl' : ∀ W, Ms' ⟶* Term.inl W → Reducible A' W := fun W hred => hM_inl W (MultiStep.step hMs' hred)
                have hM_inr' : ∀ W, Ms' ⟶* Term.inr W → Reducible B' W := fun W hred => hM_inr W (MultiStep.step hMs' hred)
                exact ihMs Ms' hMs' N1s N2s (Acc.intro N1s hN1s_acc) (Acc.intro N2s hN2s_acc) hM_inl' hM_inr' hInlRed' hInrRed' V hrest
              | @caseL _ _ N1s' _ hN1s' =>
                have hInlRed' : ∀ W, Ms ⟶* Term.inl W → Reducible (Ty.sum C1 C2) (Term.subst0 W N1s') := by
                  intro W hred
                  have h := hInlRed W hred
                  have h' := cr2_reducible_red (Ty.sum C1 C2) _ _ h (subst0_step_left hN1s')
                  unfold Reducible; unfold Reducible at h'; exact h'
                exact ihN1s N1s' hN1s' N2s (Acc.intro N2s hN2s_acc) hInlRed' hInrRed V hrest
              | @caseR _ _ _ N2s' hN2s' =>
                have hInrRed' : ∀ W, Ms ⟶* Term.inr W → Reducible (Ty.sum C1 C2) (Term.subst0 W N2s') := by
                  intro W hred
                  have h := hInrRed W hred
                  have h' := cr2_reducible_red (Ty.sum C1 C2) _ _ h (subst0_step_left hN2s')
                  unfold Reducible; unfold Reducible at h'; exact h'
                exact ihN2s N2s' hN2s' hInrRed' V hrest
    · -- ∀ V, (case M N₁ N₂) ⟶* inr V → Reducible C2 V
      intro V hCaseRed
      induction hM_sn generalizing N₁ N₂ V with
      | intro Ms hMs_acc ihMs =>
        induction hN₁_sn generalizing N₂ V with
        | intro N1s hN1s_acc ihN1s =>
          induction hN₂_sn generalizing V with
          | intro N2s hN2s_acc ihN2s =>
            cases hCaseRed with
            | step hstep hrest =>
              cases hstep with
              | @caseInl W _ _ =>
                have hMred : Term.inl W ⟶* Term.inl W := MultiStep.refl _
                have hSubstRed := hInlRed W hMred
                unfold Reducible at hSubstRed
                exact hSubstRed.2.2 V hrest
              | @caseInr W _ _ =>
                have hMred : Term.inr W ⟶* Term.inr W := MultiStep.refl _
                have hSubstRed := hInrRed W hMred
                unfold Reducible at hSubstRed
                exact hSubstRed.2.2 V hrest
              | @caseS _ Ms' _ _ hMs' =>
                have hInlRed' : ∀ W, Ms' ⟶* Term.inl W → Reducible (Ty.sum C1 C2) (Term.subst0 W N1s) := by
                  intro W hred
                  have h := hInlRed W (MultiStep.step hMs' hred)
                  unfold Reducible; unfold Reducible at h; exact h
                have hInrRed' : ∀ W, Ms' ⟶* Term.inr W → Reducible (Ty.sum C1 C2) (Term.subst0 W N2s) := by
                  intro W hred
                  have h := hInrRed W (MultiStep.step hMs' hred)
                  unfold Reducible; unfold Reducible at h; exact h
                have hM_inl' : ∀ W, Ms' ⟶* Term.inl W → Reducible A' W := fun W hred => hM_inl W (MultiStep.step hMs' hred)
                have hM_inr' : ∀ W, Ms' ⟶* Term.inr W → Reducible B' W := fun W hred => hM_inr W (MultiStep.step hMs' hred)
                exact ihMs Ms' hMs' N1s N2s (Acc.intro N1s hN1s_acc) (Acc.intro N2s hN2s_acc) hM_inl' hM_inr' hInlRed' hInrRed' V hrest
              | @caseL _ _ N1s' _ hN1s' =>
                have hInlRed' : ∀ W, Ms ⟶* Term.inl W → Reducible (Ty.sum C1 C2) (Term.subst0 W N1s') := by
                  intro W hred
                  have h := hInlRed W hred
                  have h' := cr2_reducible_red (Ty.sum C1 C2) _ _ h (subst0_step_left hN1s')
                  unfold Reducible; unfold Reducible at h'; exact h'
                exact ihN1s N1s' hN1s' N2s (Acc.intro N2s hN2s_acc) hInlRed' hInrRed V hrest
              | @caseR _ _ _ N2s' hN2s' =>
                have hInrRed' : ∀ W, Ms ⟶* Term.inr W → Reducible (Ty.sum C1 C2) (Term.subst0 W N2s') := by
                  intro W hred
                  have h := hInrRed W hred
                  have h' := cr2_reducible_red (Ty.sum C1 C2) _ _ h (subst0_step_left hN2s')
                  unfold Reducible; unfold Reducible at h'; exact h'
                exact ihN2s N2s' hN2s' hInrRed' V hrest
  | unit =>
    -- Reducible unit = SN
    unfold Reducible
    exact sn_case_helper M N₁ N₂ hM_sn hN₁_sn hN₂_sn hM_inl hM_inr hInlRed hInrRed

/-! ## Substitution Infrastructure -/

def applySubst (σ : Nat → Term) : Term → Term
  | Term.var n => σ n
  | Term.lam M => Term.lam (applySubst (liftSubst σ) M)
  | Term.app M N => Term.app (applySubst σ M) (applySubst σ N)
  | Term.pair M N => Term.pair (applySubst σ M) (applySubst σ N)
  | Term.fst M => Term.fst (applySubst σ M)
  | Term.snd M => Term.snd (applySubst σ M)
  | Term.inl M => Term.inl (applySubst σ M)
  | Term.inr M => Term.inr (applySubst σ M)
  | Term.case M N₁ N₂ => Term.case (applySubst σ M) (applySubst (liftSubst σ) N₁) (applySubst (liftSubst σ) N₂)
  | Term.unit => Term.unit
where
  liftSubst (σ : Nat → Term) (n : Nat) : Term :=
    if n = 0 then Term.var 0 else Term.shift1 (σ (n - 1))

def idSubst : Nat → Term := Term.var

def extendSubst (σ : Nat → Term) (N : Term) : Nat → Term
  | 0 => N
  | n + 1 => σ n

def ReducibleSubst (Γ : Context) (σ : Nat → Term) : Prop :=
  ∀ n A, Γ[n]? = some A → Reducible A (σ n)

def IsIdSubst (σ : Nat → Term) : Prop := ∀ n, σ n = Term.var n

theorem liftSubst_preserves_id {σ : Nat → Term} (h : IsIdSubst σ) :
    IsIdSubst (applySubst.liftSubst σ) := by
  intro n
  simp only [applySubst.liftSubst]
  cases n with
  | zero => rfl
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
    rw [h k]
    simp only [Term.shift1, Term.shift]; simp

theorem applySubst_of_isId {σ : Nat → Term} (h : IsIdSubst σ) : ∀ M, applySubst σ M = M := by
  intro M
  induction M generalizing σ with
  | var n => simp only [applySubst]; exact h n
  | lam M ih => simp only [applySubst]; rw [ih (liftSubst_preserves_id h)]
  | app M N ihM ihN => simp only [applySubst]; rw [ihM h, ihN h]
  | pair M N ihM ihN => simp only [applySubst]; rw [ihM h, ihN h]
  | fst M ih => simp only [applySubst]; rw [ih h]
  | snd M ih => simp only [applySubst]; rw [ih h]
  | inl M ih => simp only [applySubst]; rw [ih h]
  | inr M ih => simp only [applySubst]; rw [ih h]
  | case M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp only [applySubst]; rw [ihM h, ihN₁ (liftSubst_preserves_id h), ihN₂ (liftSubst_preserves_id h)]
  | unit => simp only [applySubst]

theorem idSubst_isId : IsIdSubst idSubst := fun _ => rfl

theorem applySubst_id : ∀ M, applySubst idSubst M = M := applySubst_of_isId idSubst_isId

/-! ## Substitution Composition Lemmas -/

def liftSubst_n : Nat → (Nat → Term) → (Nat → Term)
  | 0, σ => σ
  | n + 1, σ => applySubst.liftSubst (liftSubst_n n σ)

theorem liftSubst_n_spec : ∀ k σ n,
    liftSubst_n k σ n = if n < k then Term.var n else Term.shift k 0 (σ (n - k)) := by
  intro k
  induction k with
  | zero =>
    intro σ n
    simp only [liftSubst_n, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
    exact (Term.shift_zero 0 (σ n)).symm
  | succ k ih =>
    intro σ n
    simp only [liftSubst_n]
    cases n with
    | zero => simp only [Nat.zero_lt_succ, ↓reduceIte, applySubst.liftSubst, ↓reduceIte]
    | succ m =>
      simp only [applySubst.liftSubst, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [ih σ m]
      by_cases hm : m < k
      · simp only [hm, ↓reduceIte, Nat.succ_lt_succ hm]
        simp only [Term.shift1, Term.shift, Nat.not_lt_zero, ↓reduceIte]
        have h_toNat : (↑m + 1 : Int).toNat = m + 1 := by omega
        rw [h_toNat]
      · have hmk : ¬(m + 1 < k + 1) := by omega
        have hmk' : m + 1 - (k + 1) = m - k := by omega
        simp only [hm, ↓reduceIte, hmk, hmk']
        simp only [Term.shift1]
        have h := Term.shift_shift 1 k 0 (σ (m - k))
        calc Term.shift 1 0 (Term.shift k 0 (σ (m - k)))
            = Term.shift (↑1 + ↑k) 0 (σ (m - k)) := h
          _ = Term.shift (↑(k + 1)) 0 (σ (m - k)) := by
              have heq : (↑1 : Int) + ↑k = ↑(k + 1) := by omega
              rw [heq]

/-- Helper: shift 1 c X = shift 1 (j+c) X when X = shift j c M (all vars in X >= c are shifted) -/
theorem shift_shifted_eq_gen (M : Term) (j c : Nat) :
    Term.shift 1 c (Term.shift j c M) = Term.shift 1 (j + c) (Term.shift j c M) := by
  induction M generalizing j c with
  | var n =>
    simp only [Term.shift]
    by_cases h1 : n < c
    · -- n < c, inner shift doesn't change n
      simp only [h1, ↓reduceIte, Term.shift]
      have h2 : n < j + c := Nat.lt_add_left j h1
      simp only [h2, ↓reduceIte]
    · -- n >= c, inner shift gives n + j
      have h1' : ¬(n < c) := h1
      simp only [h1', ↓reduceIte, Term.shift]
      -- After inner shift, variable is ((n : Int) + (j : Int)).toNat = n + j
      have h_toNat_eq : ((n : Int) + (j : Int)).toNat = n + j := by omega
      have h_nlt_c : ¬(((n : Int) + (j : Int)).toNat < c) := by rw [h_toNat_eq]; omega
      have h_nlt_jc : ¬(((n : Int) + (j : Int)).toNat < j + c) := by rw [h_toNat_eq]; omega
      simp only [h_nlt_c, h_nlt_jc, ↓reduceIte]
  | lam M ih =>
    simp only [Term.shift]
    congr 1
    have h : j + c + 1 = j + (c + 1) := by omega
    rw [h]
    exact ih j (c + 1)
  | app M1 M2 ih1 ih2 =>
    simp only [Term.shift]
    congr 1
    · exact ih1 j c
    · exact ih2 j c
  | pair M1 M2 ih1 ih2 =>
    simp only [Term.shift]
    congr 1
    · exact ih1 j c
    · exact ih2 j c
  | fst M ih =>
    simp only [Term.shift]; congr 1; exact ih j c
  | snd M ih =>
    simp only [Term.shift]; congr 1; exact ih j c
  | inl M ih =>
    simp only [Term.shift]; congr 1; exact ih j c
  | inr M ih =>
    simp only [Term.shift]; congr 1; exact ih j c
  | case M N1 N2 ihM ihN1 ihN2 =>
    simp only [Term.shift]
    congr 1
    · exact ihM j c
    · have h : j + c + 1 = j + (c + 1) := by omega
      rw [h]
      exact ihN1 j (c + 1)
    · have h : j + c + 1 = j + (c + 1) := by omega
      rw [h]
      exact ihN2 j (c + 1)
  | unit =>
    simp only [Term.shift]

/-- Corollary: shift 1 0 X = shift 1 j X when X = shift j 0 M -/
theorem shift_shifted_eq (M : Term) (j : Nat) :
    Term.shift 1 0 (Term.shift j 0 M) = Term.shift 1 j (Term.shift j 0 M) := by
  have h := shift_shifted_eq_gen M j 0
  simp only [Nat.add_zero] at h
  exact h

/-- Key lemma relating single substitution with parallel substitution -/
theorem subst_applySubst_gen : ∀ (M : Term) (j : Nat) (σ : Nat → Term) (N : Term),
    Term.subst j (Term.shift j 0 N) (applySubst (liftSubst_n (j + 1) σ) M) =
    applySubst (liftSubst_n j (extendSubst σ N)) M := by
  intro M
  induction M with
  | var n =>
    intro j σ N
    simp only [applySubst]
    rw [liftSubst_n_spec (j + 1) σ n, liftSubst_n_spec j (extendSubst σ N) n]
    by_cases hn_lt_j : n < j
    · have hn_lt_j1 : n < j + 1 := Nat.lt_succ_of_lt hn_lt_j
      simp only [hn_lt_j1, ↓reduceIte, hn_lt_j, Term.subst]
      have hne : n ≠ j := Nat.ne_of_lt hn_lt_j
      have hng : ¬(n > j) := Nat.not_lt.mpr (Nat.le_of_lt hn_lt_j)
      simp only [hne, ↓reduceIte, hng]
    · have hn_ge_j : n ≥ j := Nat.le_of_not_lt hn_lt_j
      simp only [hn_lt_j, ↓reduceIte]
      by_cases hn_lt_j1 : n < j + 1
      · have hn_eq_j : n = j := Nat.le_antisymm (Nat.lt_succ_iff.mp hn_lt_j1) hn_ge_j
        simp only [hn_lt_j1, ↓reduceIte]
        subst hn_eq_j
        simp only [Term.subst, ↓reduceIte, Nat.sub_self, extendSubst]
      · have hn_ge_j1 : n ≥ j + 1 := Nat.le_of_not_lt hn_lt_j1
        simp only [hn_lt_j1, ↓reduceIte]
        have hn_gt_j : n > j := Nat.lt_of_succ_le hn_ge_j1
        have h_nj_pos : n - j > 0 := Nat.sub_pos_of_lt hn_gt_j
        have h_ext : extendSubst σ N (n - j) = σ (n - j - 1) := by
          cases hnj : n - j with
          | zero => omega
          | succ k => simp only [extendSubst, Nat.succ_sub_one]
        rw [h_ext]
        have h_eq : n - j - 1 = n - (j + 1) := by omega
        rw [h_eq]
        -- Show: subst j (shift j 0 N) (shift (j+1) 0 (σ (n-(j+1)))) = shift j 0 (σ (n-(j+1)))
        -- Key: shift (j+1) 0 M = shift 1 j (shift j 0 M), then use subst_shift_cancel
        have h_shift_split : Term.shift (↑(j + 1) : Int) 0 (σ (n - (j + 1))) = Term.shift 1 j (Term.shift (↑j : Int) 0 (σ (n - (j + 1)))) := by
          -- First: shift (j+1) 0 M = shift 1 0 (shift j 0 M) by shift_shift
          have h1 := Term.shift_shift 1 j 0 (σ (n - (j + 1)))
          -- h1 : shift 1 0 (shift j 0 M) = shift (1+j) 0 M
          -- Second: shift 1 0 (shift j 0 M) = shift 1 j (shift j 0 M) by shift_shifted_eq
          have h2 := shift_shifted_eq (σ (n - (j + 1))) j
          -- h2 : shift 1 0 (shift j 0 M) = shift 1 j (shift j 0 M)
          have heq : (1 : Nat) + j = j + 1 := Nat.add_comm 1 j
          calc Term.shift (↑(j + 1) : Int) 0 (σ (n - (j + 1)))
              = Term.shift (↑(1 + j)) 0 (σ (n - (j + 1))) := by rw [heq]
            _ = Term.shift 1 0 (Term.shift (↑j) 0 (σ (n - (j + 1)))) := h1.symm
            _ = Term.shift 1 j (Term.shift (↑j) 0 (σ (n - (j + 1)))) := h2
        rw [h_shift_split]
        exact Term.subst_shift_cancel (Term.shift (↑j : Int) 0 (σ (n - (j + 1)))) (Term.shift (↑j : Int) 0 N) j
  | lam M0 ih =>
    intro j σ N
    simp only [applySubst, Term.subst]
    congr 1
    have hshift : Term.shift1 (Term.shift j 0 N) = Term.shift (j + 1) 0 N := by
      simp only [Term.shift1]
      have h := Term.shift_shift 1 j 0 N
      have heq : (↑1 : Int) + ↑j = ↑(j + 1) := by omega
      calc Term.shift 1 0 (Term.shift j 0 N)
          = Term.shift (↑1 + ↑j) 0 N := h
        _ = Term.shift (↑(j + 1)) 0 N := by rw [heq]
    rw [hshift]
    have hlift : liftSubst_n (j + 1 + 1) σ = applySubst.liftSubst (liftSubst_n (j + 1) σ) := rfl
    have hlift' : liftSubst_n (j + 1) (extendSubst σ N) = applySubst.liftSubst (liftSubst_n j (extendSubst σ N)) := rfl
    rw [← hlift, ← hlift']
    exact ih (j + 1) σ N
  | app M1 M2 ih1 ih2 =>
    intro j σ N
    simp only [applySubst, Term.subst]
    congr 1
    · exact ih1 j σ N
    · exact ih2 j σ N
  | pair M1 M2 ih1 ih2 =>
    intro j σ N
    simp only [applySubst, Term.subst]
    congr 1
    · exact ih1 j σ N
    · exact ih2 j σ N
  | fst M ih =>
    intro j σ N
    simp only [applySubst, Term.subst]
    congr 1
    exact ih j σ N
  | snd M ih =>
    intro j σ N
    simp only [applySubst, Term.subst]
    congr 1
    exact ih j σ N
  | inl M ih =>
    intro j σ N
    simp only [applySubst, Term.subst]
    congr 1
    exact ih j σ N
  | inr M ih =>
    intro j σ N
    simp only [applySubst, Term.subst]
    congr 1
    exact ih j σ N
  | case M N1 N2 ihM ihN1 ihN2 =>
    intro j σ N
    simp only [applySubst, Term.subst]
    have hshift : Term.shift1 (Term.shift j 0 N) = Term.shift (j + 1) 0 N := by
      simp only [Term.shift1]
      have h := Term.shift_shift 1 j 0 N
      have heq : (↑1 : Int) + ↑j = ↑(j + 1) := by omega
      calc Term.shift 1 0 (Term.shift j 0 N)
          = Term.shift (↑1 + ↑j) 0 N := h
        _ = Term.shift (↑(j + 1)) 0 N := by rw [heq]
    congr 1
    · exact ihM j σ N
    · rw [hshift]
      have hlift : liftSubst_n (j + 1 + 1) σ = applySubst.liftSubst (liftSubst_n (j + 1) σ) := rfl
      have hlift' : liftSubst_n (j + 1) (extendSubst σ N) = applySubst.liftSubst (liftSubst_n j (extendSubst σ N)) := rfl
      rw [← hlift, ← hlift']
      exact ihN1 (j + 1) σ N
    · rw [hshift]
      have hlift : liftSubst_n (j + 1 + 1) σ = applySubst.liftSubst (liftSubst_n (j + 1) σ) := rfl
      have hlift' : liftSubst_n (j + 1) (extendSubst σ N) = applySubst.liftSubst (liftSubst_n j (extendSubst σ N)) := rfl
      rw [← hlift, ← hlift']
      exact ihN2 (j + 1) σ N
  | unit =>
    intro j σ N
    simp only [applySubst, Term.subst]

theorem subst_applySubst_lift : ∀ (σ : Nat → Term) (N : Term) (M : Term),
    Term.subst0 N (applySubst (applySubst.liftSubst σ) M) = applySubst (extendSubst σ N) M := by
  intro σ N M
  unfold Term.subst0
  have h := subst_applySubst_gen M 0 σ N
  simp only [liftSubst_n] at h
  -- Term.shift (↑0) 0 N = Term.shift 0 0 N since (↑0 : Int) = 0
  have hcast : (↑(0 : Nat) : Int) = 0 := rfl
  simp only [hcast, Term.shift_zero] at h
  exact h

theorem extendSubst_reducible {Γ : Context} {σ : Nat → Term} {N : Term} {A : Ty}
    (hσ : ReducibleSubst Γ σ) (hN : Reducible A N) :
    ReducibleSubst (A :: Γ) (extendSubst σ N) := by
  intro n B hB
  cases n with
  | zero =>
    simp only [extendSubst, List.getElem?_cons_zero] at hB ⊢
    injection hB with hB'; rw [← hB']; exact hN
  | succ n' =>
    simp only [extendSubst, List.getElem?_cons_succ] at hB ⊢
    exact hσ n' B hB

/-! ## Fundamental Lemma -/

/-- Helper to get SN from reducible under subst -/
theorem sn_from_subst_var {M : Term} (h : SN (Term.subst0 (Term.var 0) M)) : SN M := by
  have : ∀ T, SN T → ∀ M, T = Term.subst0 (Term.var 0) M → SN M := by
    intro T hT
    induction hT with
    | intro T' _ ih =>
      intro M hTeq
      apply sn_intro
      intro M'_step hM'_step
      have hstep : Step (Term.subst0 (Term.var 0) M) (Term.subst0 (Term.var 0) M'_step) :=
        @subst0_step_left M M'_step (Term.var 0) hM'_step
      rw [← hTeq] at hstep
      exact ih (Term.subst0 (Term.var 0) M'_step) hstep M'_step rfl
  exact this (Term.subst0 (Term.var 0) M) h M rfl

theorem fundamental_lemma : ∀ {Γ : Context} {M : Term} {A : Ty} {σ : Nat → Term},
    HasType Γ M A → ReducibleSubst Γ σ → Reducible A (applySubst σ M) := by
  intro Γ M A σ htype hσ
  induction htype generalizing σ with
  | @var Γ' n A' hget =>
    simp only [applySubst]
    exact hσ n A' (by simp_all)
  | @app Γ' M' N' A' B' hM hN ihM ihN =>
    simp only [applySubst]
    exact ihM hσ (applySubst σ N') (ihN hσ)
  | @lam Γ' M' A' B' hBody ihBody =>
    simp only [applySubst]
    intro N hN
    let M'' := applySubst (applySubst.liftSubst σ) M'
    have hext : ReducibleSubst (A' :: Γ') (extendSubst σ N) := extendSubst_reducible hσ hN
    have hbeta : Reducible B' (applySubst (extendSubst σ N) M') := ihBody hext
    rw [← subst_applySubst_lift] at hbeta
    have hvar0 : Reducible A' (Term.var 0) := var_reducible 0 A'
    have hext0 : ReducibleSubst (A' :: Γ') (extendSubst σ (Term.var 0)) := extendSubst_reducible hσ hvar0
    have hM''_var : Reducible B' (applySubst (extendSubst σ (Term.var 0)) M') := ihBody hext0
    rw [← subst_applySubst_lift] at hM''_var
    have hM''_sn_from_subst : SN (Term.subst0 (Term.var 0) M'') := cr1_reducible_sn B' _ hM''_var
    have hN_sn : SN N := cr1_reducible_sn A' N hN
    apply reducible_app_lam B' M'' N
    · exact sn_from_subst_var hM''_sn_from_subst
    · exact hN_sn
    · exact hbeta
    · intro M''' hM'''
      exact cr2_reducible_red B' _ _ hbeta (subst0_step_left hM''')
    · intro N' hN'
      have hN'_red : Reducible A' N' := cr2_reducible_red A' N N' hN hN'
      have hext' : ReducibleSubst (A' :: Γ') (extendSubst σ N') := extendSubst_reducible hσ hN'_red
      have h := ihBody hext'
      rw [← subst_applySubst_lift] at h
      exact h
  | @pair Γ' M' N' A' B' hM hN ihM ihN =>
    simp only [applySubst]
    exact reducible_pair (ihM hσ) (ihN hσ)
  | @fst Γ' M' A' B' hM ihM =>
    simp only [applySubst]
    have h := ihM hσ
    unfold Reducible at h
    exact h.1
  | @snd Γ' M' A' B' hM ihM =>
    simp only [applySubst]
    have h := ihM hσ
    unfold Reducible at h
    exact h.2
  | @inl Γ' M' A' B' hM ihM =>
    simp only [applySubst]
    unfold Reducible
    refine ⟨sn_inl (cr1_reducible_sn A' _ (ihM hσ)), ?_, ?_⟩
    · intro V hVeq
      -- hVeq : (applySubst σ M').inl ⟶* Term.inl V
      have hMV := multiStep_inl_inv hVeq
      exact cr2_reducible_red_multi A' (applySubst σ M') V (ihM hσ) hMV
    · intro V hVeq
      -- hVeq : (applySubst σ M').inl ⟶* Term.inr V - impossible
      exact False.elim (multiStep_inl_not_inr hVeq)
  | @inr Γ' M' A' B' hN ihN =>
    simp only [applySubst]
    unfold Reducible
    refine ⟨sn_inr (cr1_reducible_sn B' _ (ihN hσ)), ?_, ?_⟩
    · intro V hVeq
      -- hVeq : (applySubst σ M').inr ⟶* Term.inl V - impossible
      exact False.elim (multiStep_inr_not_inl hVeq)
    · intro V hVeq
      -- hVeq : (applySubst σ M').inr ⟶* Term.inr V
      have hMV := multiStep_inr_inv hVeq
      exact cr2_reducible_red_multi B' (applySubst σ M') V (ihN hσ) hMV
  | @case Γ' M' N₁' N₂' A' B' C' hM hN₁ hN₂ ihM ihN₁ ihN₂ =>
    simp only [applySubst]
    have hM_red := ihM hσ
    unfold Reducible at hM_red
    have hM_sn := hM_red.1
    have hM_inl := hM_red.2.1
    have hM_inr := hM_red.2.2
    have hN₁_sn : SN (applySubst (applySubst.liftSubst σ) N₁') := by
      have hvar0 : Reducible A' (Term.var 0) := var_reducible 0 A'
      have hext0 := extendSubst_reducible hσ hvar0
      have h := ihN₁ hext0
      have hsn := cr1_reducible_sn C' _ h
      rw [← subst_applySubst_lift] at hsn
      exact sn_from_subst_var hsn
    have hN₂_sn : SN (applySubst (applySubst.liftSubst σ) N₂') := by
      have hvar0 : Reducible B' (Term.var 0) := var_reducible 0 B'
      have hext0 := extendSubst_reducible hσ hvar0
      have h := ihN₂ hext0
      have hsn := cr1_reducible_sn C' _ h
      rw [← subst_applySubst_lift] at hsn
      exact sn_from_subst_var hsn
    -- Helper to get Reducible C' (subst0 V N₁) when M ⟶* inl V
    have hInlRed : ∀ V, (applySubst σ M') ⟶* Term.inl V →
        Reducible C' (Term.subst0 V (applySubst (applySubst.liftSubst σ) N₁')) := by
      intro V hMeq
      have hV_red : Reducible A' V := hM_inl V hMeq
      have hext := extendSubst_reducible hσ hV_red
      have h := ihN₁ hext
      rw [← subst_applySubst_lift] at h
      exact h
    -- Helper to get Reducible C' (subst0 V N₂) when M ⟶* inr V
    have hInrRed : ∀ V, (applySubst σ M') ⟶* Term.inr V →
        Reducible C' (Term.subst0 V (applySubst (applySubst.liftSubst σ) N₂')) := by
      intro V hMeq
      have hV_red : Reducible B' V := hM_inr V hMeq
      have hext := extendSubst_reducible hσ hV_red
      have h := ihN₂ hext
      rw [← subst_applySubst_lift] at h
      exact h
    -- Use the reducible_case theorem
    exact reducible_case C' A' B' _ _ _ hM_sn hN₁_sn hN₂_sn hM_inl hM_inr hInlRed hInrRed
  | @unit Γ' =>
    simp only [applySubst]
    unfold Reducible
    -- unit term is SN (doesn't reduce)
    exact sn_intro (fun _ h => nomatch h)

/-! ## Strong Normalization Theorem -/

/-- **Strong Normalization Theorem**: Every well-typed term in extended STLC terminates. -/
theorem strong_normalization {Γ : Context} {M : Term} {A : Ty}
    (h : HasType Γ M A) : SN M := by
  have hσ : ReducibleSubst Γ idSubst := fun n B hB => var_reducible n B
  have hred : Reducible A (applySubst idSubst M) := fundamental_lemma h hσ
  rw [applySubst_id] at hred
  exact cr1_reducible_sn A M hred

/-! ## Corollaries -/

theorem hasNormalForm_of_hasType {Γ : Context} {M : Term} {A : Ty} (h : HasType Γ M A) :
    Rewriting.HasNormalForm Step M :=
  hasNormalForm_of_SN (strong_normalization h)

theorem stlcext_termination {M : Term} {A : Ty} (h : HasType [] M A) : SN M :=
  strong_normalization h

theorem type_safety {M N : Term} {A : Ty}
    (htype : HasType [] M A) (hsteps : MultiStep M N) :
    IsValue N ∨ ∃ P, Step N P :=
  progress (subject_reduction_multi htype hsteps)

end Metatheory.STLCext
