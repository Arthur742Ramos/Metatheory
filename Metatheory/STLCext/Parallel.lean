import Metatheory.STLCext.Reduction

/-!
# Parallel Reduction for Extended STLC

This module defines parallel reduction for STLC with products and sums,
used to prove Church-Rosser via the diamond property.

## Parallel Reduction

Parallel reduction contracts multiple redexes simultaneously:
- Variables reduce to themselves
- Constructors reduce component-wise
- Beta, fst/snd, and case redexes can fire directly

## References

- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
- Pierce, "Types and Programming Languages" (2002), Chapters 11-12
-/

namespace Metatheory.STLCext

open Term

/-! ## Parallel Reduction -/

/-- Parallel reduction for extended STLC. -/
inductive ParRed : Term → Term → Prop where
  | var : ∀ n, ParRed (var n) (var n)
  | lam : ∀ {M M'}, ParRed M M' → ParRed (lam M) (lam M')
  | app : ∀ {M M' N N'}, ParRed M M' → ParRed N N' → ParRed (app M N) (app M' N')
  | pair : ∀ {M M' N N'}, ParRed M M' → ParRed N N' → ParRed (pair M N) (pair M' N')
  | fst : ∀ {M M'}, ParRed M M' → ParRed (fst M) (fst M')
  | snd : ∀ {M M'}, ParRed M M' → ParRed (snd M) (snd M')
  | inl : ∀ {M M'}, ParRed M M' → ParRed (inl M) (inl M')
  | inr : ∀ {M M'}, ParRed M M' → ParRed (inr M) (inr M')
  | case : ∀ {M M' N₁ N₁' N₂ N₂'},
      ParRed M M' → ParRed N₁ N₁' → ParRed N₂ N₂' →
      ParRed (case M N₁ N₂) (case M' N₁' N₂')
  | beta : ∀ {M M' N N'}, ParRed M M' → ParRed N N' →
      ParRed (app (lam M) N) (M'[N'])
  | fstPair : ∀ {M M' N N'}, ParRed M M' → ParRed N N' →
      ParRed (fst (pair M N)) M'
  | sndPair : ∀ {M M' N N'}, ParRed M M' → ParRed N N' →
      ParRed (snd (pair M N)) N'
  | caseInl : ∀ {V V' N₁ N₁' N₂ N₂'}, ParRed V V' → ParRed N₁ N₁' → ParRed N₂ N₂' →
      ParRed (case (inl V) N₁ N₂) (N₁'[V'])
  | caseInr : ∀ {V V' N₁ N₁' N₂ N₂'}, ParRed V V' → ParRed N₁ N₁' → ParRed N₂ N₂' →
      ParRed (case (inr V) N₁ N₂) (N₂'[V'])
  | unit : ParRed unit unit

/-- Notation for parallel reduction. -/
scoped infix:50 " ⇒ " => ParRed

namespace ParRed

/-- Parallel reduction is reflexive. -/
theorem refl (M : Term) : M ⇒ M := by
  induction M with
  | var n => exact ParRed.var n
  | lam M ih => exact ParRed.lam ih
  | app M N ihM ihN => exact ParRed.app ihM ihN
  | pair M N ihM ihN => exact ParRed.pair ihM ihN
  | fst M ih => exact ParRed.fst ih
  | snd M ih => exact ParRed.snd ih
  | inl M ih => exact ParRed.inl ih
  | inr M ih => exact ParRed.inr ih
  | case M N₁ N₂ ihM ihN₁ ihN₂ => exact ParRed.case ihM ihN₁ ihN₂
  | unit => exact ParRed.unit

/-- Single-step reduction implies parallel reduction. -/
theorem of_step {M N : Term} (h : Step M N) : M ⇒ N := by
  induction h with
  | beta M N =>
    exact ParRed.beta (refl M) (refl N)
  | fstPair M N =>
    exact ParRed.fstPair (refl M) (refl N)
  | sndPair M N =>
    exact ParRed.sndPair (refl M) (refl N)
  | caseInl V N₁ N₂ =>
    exact ParRed.caseInl (refl V) (refl N₁) (refl N₂)
  | caseInr V N₁ N₂ =>
    exact ParRed.caseInr (refl V) (refl N₁) (refl N₂)
  | appL hstep ih =>
    exact ParRed.app ih (refl _)
  | appR hstep ih =>
    exact ParRed.app (refl _) ih
  | lam hstep ih =>
    exact ParRed.lam ih
  | pairL hstep ih =>
    exact ParRed.pair ih (refl _)
  | pairR hstep ih =>
    exact ParRed.pair (refl _) ih
  | fst hstep ih =>
    exact ParRed.fst ih
  | snd hstep ih =>
    exact ParRed.snd ih
  | inl hstep ih =>
    exact ParRed.inl ih
  | inr hstep ih =>
    exact ParRed.inr ih
  | caseS hstep ih =>
    exact ParRed.case ih (refl _) (refl _)
  | caseL hstep ih =>
    exact ParRed.case (refl _) ih (refl _)
  | caseR hstep ih =>
    exact ParRed.case (refl _) (refl _) ih

/-- Parallel reduction implies multi-step reduction. -/
theorem toMulti {M N : Term} (h : M ⇒ N) : M ⟶* N := by
  induction h with
  | var n => exact MultiStep.refl _
  | lam _ ih => exact MultiStep.lam ih
  | app _ _ ihM ihN => exact MultiStep.trans (MultiStep.appL ihM) (MultiStep.appR ihN)
  | pair _ _ ihM ihN => exact MultiStep.trans (MultiStep.pairL ihM) (MultiStep.pairR ihN)
  | fst _ ih => exact MultiStep.fst ih
  | snd _ ih => exact MultiStep.snd ih
  | inl _ ih => exact MultiStep.inl ih
  | inr _ ih => exact MultiStep.inr ih
  | case _ _ _ ihM ihN₁ ihN₂ =>
    exact MultiStep.trans (MultiStep.caseS ihM)
      (MultiStep.trans (MultiStep.caseL ihN₁) (MultiStep.caseR ihN₂))
  | @beta M M' N N' _ _ ihM ihN =>
    have h1 : Term.app (Term.lam M) N ⟶* Term.app (Term.lam M') N' :=
      MultiStep.trans (MultiStep.appL (MultiStep.lam ihM)) (MultiStep.appR ihN)
    have h2 : Term.app (Term.lam M') N' ⟶* M'[N'] := MultiStep.single (Step.beta M' N')
    exact MultiStep.trans h1 h2
  | @fstPair M M' N N' _ _ ihM ihN =>
    have h1 : Term.fst (Term.pair M N) ⟶* Term.fst (Term.pair M' N') :=
      MultiStep.fst (MultiStep.trans (MultiStep.pairL ihM) (MultiStep.pairR ihN))
    have h2 : Term.fst (Term.pair M' N') ⟶* M' := MultiStep.single (Step.fstPair M' N')
    exact MultiStep.trans h1 h2
  | @sndPair M M' N N' _ _ ihM ihN =>
    have h1 : Term.snd (Term.pair M N) ⟶* Term.snd (Term.pair M' N') :=
      MultiStep.snd (MultiStep.trans (MultiStep.pairL ihM) (MultiStep.pairR ihN))
    have h2 : Term.snd (Term.pair M' N') ⟶* N' := MultiStep.single (Step.sndPair M' N')
    exact MultiStep.trans h1 h2
  | @caseInl V V' N₁ N₁' N₂ N₂' _ _ _ ihV ihN₁ ihN₂ =>
    have h1 : Term.case (Term.inl V) N₁ N₂ ⟶* Term.case (Term.inl V') N₁' N₂' :=
      MultiStep.trans (MultiStep.caseS (MultiStep.inl ihV))
        (MultiStep.trans (MultiStep.caseL ihN₁) (MultiStep.caseR ihN₂))
    have h2 : Term.case (Term.inl V') N₁' N₂' ⟶* N₁'[V'] :=
      MultiStep.single (Step.caseInl V' N₁' N₂')
    exact MultiStep.trans h1 h2
  | @caseInr V V' N₁ N₁' N₂ N₂' _ _ _ ihV ihN₁ ihN₂ =>
    have h1 : Term.case (Term.inr V) N₁ N₂ ⟶* Term.case (Term.inr V') N₁' N₂' :=
      MultiStep.trans (MultiStep.caseS (MultiStep.inr ihV))
        (MultiStep.trans (MultiStep.caseL ihN₁) (MultiStep.caseR ihN₂))
    have h2 : Term.case (Term.inr V') N₁' N₂' ⟶* N₂'[V'] :=
      MultiStep.single (Step.caseInr V' N₁' N₂')
    exact MultiStep.trans h1 h2
  | unit => exact MultiStep.refl _

/-- Parallel reduction is preserved under shifting. -/
theorem shift {M M' : Term} (d : Nat) (c : Nat) (h : M ⇒ M') :
    Term.shift d c M ⇒ Term.shift d c M' := by
  induction h generalizing c with
  | var n =>
    simp [Term.shift]
    split <;> exact ParRed.var _
  | lam _ ih =>
    simp [Term.shift]
    exact ParRed.lam (ih (c + 1))
  | app _ _ ihM ihN =>
    simp [Term.shift]
    exact ParRed.app (ihM c) (ihN c)
  | pair _ _ ihM ihN =>
    simp [Term.shift]
    exact ParRed.pair (ihM c) (ihN c)
  | fst _ ih =>
    simp [Term.shift]
    exact ParRed.fst (ih c)
  | snd _ ih =>
    simp [Term.shift]
    exact ParRed.snd (ih c)
  | inl _ ih =>
    simp [Term.shift]
    exact ParRed.inl (ih c)
  | inr _ ih =>
    simp [Term.shift]
    exact ParRed.inr (ih c)
  | case _ _ _ ihM ihN₁ ihN₂ =>
    simp [Term.shift]
    exact ParRed.case (ihM c) (ihN₁ (c + 1)) (ihN₂ (c + 1))
  | beta _ _ ihM ihN =>
    simp [Term.shift]
    rw [Term.shift_subst]
    exact ParRed.beta (ihM (c + 1)) (ihN c)
  | fstPair _ _ ihM ihN =>
    simp [Term.shift]
    exact ParRed.fstPair (ihM c) (ihN c)
  | sndPair _ _ ihM ihN =>
    simp [Term.shift]
    exact ParRed.sndPair (ihM c) (ihN c)
  | caseInl _ _ _ ihV ihN₁ ihN₂ =>
    simp [Term.shift]
    rw [Term.shift_subst]
    exact ParRed.caseInl (ihV c) (ihN₁ (c + 1)) (ihN₂ (c + 1))
  | caseInr _ _ _ ihV ihN₁ ihN₂ =>
    simp [Term.shift]
    rw [Term.shift_subst]
    exact ParRed.caseInr (ihV c) (ihN₁ (c + 1)) (ihN₂ (c + 1))
  | unit =>
    simp [Term.shift]
    exact ParRed.unit

/-- Parallel reduction is preserved under substitution. -/
theorem subst_gen {M M' : Term} (j : Nat) {N N' : Term}
    (hM : M ⇒ M') (hN : N ⇒ N') :
    Term.subst j N M ⇒ Term.subst j N' M' := by
  induction hM generalizing j N N' with
  | var n =>
    simp [Term.subst]
    split
    · exact hN
    · split <;> exact ParRed.var _
  | lam hM ih =>
    simp [Term.subst]
    apply ParRed.lam
    have hshift : Term.shift1 N ⇒ Term.shift1 N' := shift 1 0 hN
    exact ih (j + 1) hshift
  | app hM hN ihM ihN =>
    simp [Term.subst]
    exact ParRed.app (ihM j hN) (ihN j hN)
  | pair hM hN ihM ihN =>
    simp [Term.subst]
    exact ParRed.pair (ihM j hN) (ihN j hN)
  | fst hM ih =>
    simp [Term.subst]
    exact ParRed.fst (ih j hN)
  | snd hM ih =>
    simp [Term.subst]
    exact ParRed.snd (ih j hN)
  | inl hM ih =>
    simp [Term.subst]
    exact ParRed.inl (ih j hN)
  | inr hM ih =>
    simp [Term.subst]
    exact ParRed.inr (ih j hN)
  | case hM hN₁ hN₂ ihM ihN₁ ihN₂ =>
    simp [Term.subst]
    exact ParRed.case (ihM j hN) (ihN₁ (j + 1) (shift 1 0 hN)) (ihN₂ (j + 1) (shift 1 0 hN))
  | @beta M0 M0' N0 N0' hM0 hN0 ihM ihN =>
    simp [Term.subst]
    have h1 := ihM (j + 1) (shift 1 0 hN)
    have h2 := ihN j hN
    have h_eq : (Term.subst (j + 1) (Term.shift 1 0 N') M0')[Term.subst j N' N0'] =
        Term.subst j N' (M0'[N0']) := by
      simpa [Term.shift1] using (Term.subst_subst_gen M0' N' N0' j)
    have h_beta := ParRed.beta h1 h2
    simpa [h_eq, Term.shift1, Term.subst0] using h_beta
  | fstPair hM hN ihM ihN =>
    simp [Term.subst]
    exact ParRed.fstPair (ihM j hN) (ihN j hN)
  | sndPair hM hN ihM ihN =>
    simp [Term.subst]
    exact ParRed.sndPair (ihM j hN) (ihN j hN)
  | @caseInl V V' N₁ N₁' N₂ N₂' hV hN₁ hN₂ ihV ihN₁ ihN₂ =>
    simp [Term.subst]
    have hV' := ihV j hN
    have hN₁' := ihN₁ (j + 1) (shift 1 0 hN)
    have hN₂' := ihN₂ (j + 1) (shift 1 0 hN)
    have h_eq : (Term.subst (j + 1) (Term.shift 1 0 N') N₁')[Term.subst j N' V'] =
        Term.subst j N' (N₁'[V']) :=
      Term.subst_subst_gen N₁' N' V' j
    have hcase := ParRed.caseInl hV' hN₁' hN₂'
    simpa [h_eq] using hcase
  | @caseInr V V' N₁ N₁' N₂ N₂' hV hN₁ hN₂ ihV ihN₁ ihN₂ =>
    simp [Term.subst]
    have hV' := ihV j hN
    have hN₁' := ihN₁ (j + 1) (shift 1 0 hN)
    have hN₂' := ihN₂ (j + 1) (shift 1 0 hN)
    have h_eq : (Term.subst (j + 1) (Term.shift 1 0 N') N₂')[Term.subst j N' V'] =
        Term.subst j N' (N₂'[V']) :=
      Term.subst_subst_gen N₂' N' V' j
    have hcase := ParRed.caseInr hV' hN₁' hN₂'
    simpa [h_eq] using hcase
  | unit =>
    simp [Term.subst]
    exact ParRed.unit

/-- Parallel reduction is preserved under substitution at 0. -/
theorem subst {M M' N N' : Term} (hM : M ⇒ M') (hN : N ⇒ N') :
    M[N] ⇒ M'[N'] :=
  subst_gen 0 hM hN

end ParRed

end Metatheory.STLCext
