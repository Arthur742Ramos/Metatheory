import Metatheory.STLCextBool.Reduction

/-!
# Parallel Reduction for STLC with Booleans

Parallel reduction contracts multiple redexes simultaneously, enabling
the diamond property proof for confluence.
-/

namespace Metatheory.STLCextBool

open Term

/-! ## Parallel Reduction -/

/-- Parallel reduction for STLC with booleans. -/
inductive ParRed : Term → Term → Prop where
  | var : ∀ n, ParRed (var n) (var n)
  | lam : ∀ {M M'}, ParRed M M' → ParRed (lam M) (lam M')
  | app : ∀ {M M' N N'}, ParRed M M' → ParRed N N' → ParRed (app M N) (app M' N')
  | ttrue : ParRed ttrue ttrue
  | tfalse : ParRed tfalse tfalse
  | ite : ∀ {M M' N₁ N₁' N₂ N₂'},
      ParRed M M' → ParRed N₁ N₁' → ParRed N₂ N₂' →
      ParRed (ite M N₁ N₂) (ite M' N₁' N₂')
  | beta : ∀ {M M' N N'}, ParRed M M' → ParRed N N' →
      ParRed (app (lam M) N) (M'[N'])
  | iteTrue : ∀ {N₁ N₁' N₂ N₂'}, ParRed N₁ N₁' → ParRed N₂ N₂' →
      ParRed (ite ttrue N₁ N₂) N₁'
  | iteFalse : ∀ {N₁ N₁' N₂ N₂'}, ParRed N₁ N₁' → ParRed N₂ N₂' →
      ParRed (ite tfalse N₁ N₂) N₂'

/-- Notation for parallel reduction. -/
scoped infix:50 " ⇒ " => ParRed

namespace ParRed

/-! ## Reflexivity -/

/-- Parallel reduction is reflexive. -/
theorem refl (M : Term) : M ⇒ M := by
  induction M with
  | var n => exact ParRed.var n
  | lam M ih => exact ParRed.lam ih
  | app M N ihM ihN => exact ParRed.app ihM ihN
  | ttrue => exact ParRed.ttrue
  | tfalse => exact ParRed.tfalse
  | ite M N₁ N₂ ihM ihN₁ ihN₂ => exact ParRed.ite ihM ihN₁ ihN₂

/-! ## Relationship to Single-Step -/

/-- Single-step reduction implies parallel reduction. -/
theorem of_step {M N : Term} (h : Step M N) : M ⇒ N := by
  induction h with
  | beta M N =>
    exact ParRed.beta (refl M) (refl N)
  | iteTrue N₁ N₂ =>
    exact ParRed.iteTrue (refl N₁) (refl N₂)
  | iteFalse N₁ N₂ =>
    exact ParRed.iteFalse (refl N₁) (refl N₂)
  | appL hstep ih =>
    exact ParRed.app ih (refl _)
  | appR hstep ih =>
    exact ParRed.app (refl _) ih
  | lamStep hstep ih =>
    exact ParRed.lam ih
  | iteC hstep ih =>
    exact ParRed.ite ih (refl _) (refl _)
  | iteT hstep ih =>
    exact ParRed.ite (refl _) ih (refl _)
  | iteF hstep ih =>
    exact ParRed.ite (refl _) (refl _) ih

/-! ## Relationship to Multi-Step -/

/-- Parallel reduction implies multi-step reduction. -/
theorem toMulti {M N : Term} (h : M ⇒ N) : M ⟶* N := by
  induction h with
  | var n => exact MultiStep.refl _
  | lam _ ih => exact MultiStep.lam ih
  | app _ _ ihM ihN =>
    exact MultiStep.trans (MultiStep.appL ihM) (MultiStep.appR ihN)
  | ttrue => exact MultiStep.refl _
  | tfalse => exact MultiStep.refl _
  | ite _ _ _ ihM ihN₁ ihN₂ =>
    exact MultiStep.trans (MultiStep.iteC ihM)
      (MultiStep.trans (MultiStep.iteT ihN₁) (MultiStep.iteF ihN₂))
  | @beta M M' N N' _ _ ihM ihN =>
    have h1 : Term.app (Term.lam M) N ⟶* Term.app (Term.lam M') N' :=
      MultiStep.trans (MultiStep.appL (MultiStep.lam ihM)) (MultiStep.appR ihN)
    have h2 : Term.app (Term.lam M') N' ⟶* M'[N'] := MultiStep.single (Step.beta M' N')
    exact MultiStep.trans h1 h2
  | @iteTrue N₁ N₁' N₂ N₂' _ _ ihN₁ ihN₂ =>
    have h1 : Term.ite Term.ttrue N₁ N₂ ⟶* Term.ite Term.ttrue N₁' N₂' :=
      MultiStep.trans (MultiStep.iteT ihN₁) (MultiStep.iteF ihN₂)
    have h2 : Term.ite Term.ttrue N₁' N₂' ⟶* N₁' :=
      MultiStep.single (Step.iteTrue N₁' N₂')
    exact MultiStep.trans h1 h2
  | @iteFalse N₁ N₁' N₂ N₂' _ _ ihN₁ ihN₂ =>
    have h1 : Term.ite Term.tfalse N₁ N₂ ⟶* Term.ite Term.tfalse N₁' N₂' :=
      MultiStep.trans (MultiStep.iteT ihN₁) (MultiStep.iteF ihN₂)
    have h2 : Term.ite Term.tfalse N₁' N₂' ⟶* N₂' :=
      MultiStep.single (Step.iteFalse N₁' N₂')
    exact MultiStep.trans h1 h2

/-! ## Auxiliary Substitution Lemmas -/

/-- Shifting preserves parallel reduction. -/
theorem shift {M M' : Term} (d : Nat) (c : Nat) (h : M ⇒ M') :
    Term.shift d c M ⇒ Term.shift d c M' := by
  induction h generalizing c with
  | var n =>
    simp only [Term.shift]
    split <;> exact ParRed.var _
  | lam _ ih =>
    simp only [Term.shift]
    exact ParRed.lam (ih (c + 1))
  | app _ _ ihM ihN =>
    simp only [Term.shift]
    exact ParRed.app (ihM c) (ihN c)
  | ttrue =>
    simp [Term.shift]
    exact ParRed.ttrue
  | tfalse =>
    simp [Term.shift]
    exact ParRed.tfalse
  | ite _ _ _ ihM ihN₁ ihN₂ =>
    simp [Term.shift]
    exact ParRed.ite (ihM c) (ihN₁ c) (ihN₂ c)
  | beta _ _ ihM ihN =>
    simp [Term.shift]
    rw [Term.shift_subst]
    exact ParRed.beta (ihM (c + 1)) (ihN c)
  | iteTrue _ _ ihN₁ ihN₂ =>
    simp [Term.shift]
    exact ParRed.iteTrue (ihN₁ c) (ihN₂ c)
  | iteFalse _ _ ihN₁ ihN₂ =>
    simp [Term.shift]
    exact ParRed.iteFalse (ihN₁ c) (ihN₂ c)

/-- Parallel reduction is preserved under substitution. -/
theorem subst_gen {M M' : Term} (j : Nat) {N N' : Term}
    (hM : M ⇒ M') (hN : N ⇒ N') :
    Term.subst j N M ⇒ Term.subst j N' M' := by
  induction hM generalizing j N N' with
  | var n =>
    simp only [Term.subst]
    split
    · exact hN
    · split <;> exact ParRed.var _
  | lam hM ih =>
    simp only [Term.subst]
    apply ParRed.lam
    have hshift : Term.shift1 N ⇒ Term.shift1 N' := shift 1 0 hN
    exact ih (j + 1) hshift
  | app hM hN ihM ihN =>
    simp only [Term.subst]
    exact ParRed.app (ihM j hN) (ihN j hN)
  | ttrue =>
    simp [Term.subst]
    exact ParRed.ttrue
  | tfalse =>
    simp [Term.subst]
    exact ParRed.tfalse
  | ite hM hN₁ hN₂ ihM ihN₁ ihN₂ =>
    simp [Term.subst]
    exact ParRed.ite (ihM j hN) (ihN₁ j hN) (ihN₂ j hN)
  | @beta M0 M0' N0 N0' hM0 hN0 ihM ihN =>
    simp [Term.subst]
    have h1 := ihM (j + 1) (shift 1 0 hN)
    have h2 := ihN j hN
    have h_eq : (Term.subst (j + 1) (Term.shift 1 0 N') M0')[Term.subst j N' N0'] =
        Term.subst j N' (M0'[N0']) := by
      simpa [Term.shift1] using (Term.subst_subst_gen M0' N' N0' j)
    have h_beta := ParRed.beta h1 h2
    simpa [h_eq, Term.shift1, Term.subst0] using h_beta
  | iteTrue hN₁ hN₂ ihN₁ ihN₂ =>
    simp [Term.subst]
    exact ParRed.iteTrue (ihN₁ j hN) (ihN₂ j hN)
  | iteFalse hN₁ hN₂ ihN₁ ihN₂ =>
    simp [Term.subst]
    exact ParRed.iteFalse (ihN₁ j hN) (ihN₂ j hN)

/-- Parallel reduction is preserved under substitution at 0. -/
theorem subst {M M' N N' : Term} (hM : M ⇒ M') (hN : N ⇒ N') :
    M[N] ⇒ M'[N'] :=
  subst_gen 0 hM hN

end ParRed

end Metatheory.STLCextBool
