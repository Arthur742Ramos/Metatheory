/-
# Eta Reduction and Basic Beta-Eta Interface

This module defines one-step eta reduction for the untyped lambda calculus and
provides a small, stable interface for combining eta steps with the existing
beta-reduction development.

The previous version attempted a full beta-eta confluence development, but it
had accumulated a large number of broken proof scripts and stale helper calls.
For the current repository state, the code that is actually used elsewhere only
needs the eta relation itself, its standard expansion redex, and the embedding
into a combined beta-eta reduction system.
-/

import Metatheory.Lambda.Confluence
import Metatheory.Rewriting.Basic

namespace Metatheory.Lambda

open Term

/-! ## Free Variable Check -/

/-- Boolean check for whether variable `k` occurs free in a term. -/
def hasFreeVar : Nat → Term → Bool
  | k, var n => n == k
  | k, app M N => hasFreeVar k M || hasFreeVar k N
  | k, lam M => hasFreeVar (k + 1) M

/-- After shifting by `1` at cutoff `c`, variable `c` is no longer free. -/
theorem hasFreeVar_shift1_at (M : Term) (c : Nat) : hasFreeVar c (shift 1 c M) = false := by
  induction M generalizing c with
  | var n =>
      unfold shift hasFreeVar
      by_cases h : n < c
      · simp [h]
        exact Nat.ne_of_lt h
      · simp [h]
        have hne : n + 1 ≠ c := by omega
        exact hne
  | app M N ihM ihN =>
      simp [shift, hasFreeVar, ihM, ihN]
  | lam M ih =>
      simpa [shift, hasFreeVar] using ih (c + 1)

/-- Special case of `hasFreeVar_shift1_at` at cutoff `0`. -/
theorem hasFreeVar_shift1_zero (M : Term) : hasFreeVar 0 (shift 1 0 M) = false :=
  hasFreeVar_shift1_at M 0

/-! ## Eta Reduction -/

/-- One-step eta reduction. -/
inductive EtaStep : Term → Term → Prop where
  /-- Contract `λx. M x` to `M`, represented in de Bruijn form. -/
  | eta : ∀ M, hasFreeVar 0 M = false → EtaStep (lam (app M (var 0))) (shift (-1) 0 M)
  | appL : ∀ {M M' N}, EtaStep M M' → EtaStep (app M N) (app M' N)
  | appR : ∀ {M N N'}, EtaStep N N' → EtaStep (app M N) (app M N')
  | lam : ∀ {M M'}, EtaStep M M' → EtaStep (lam M) (lam M')

/-- Notation for eta reduction. -/
scoped infix:50 " →η " => EtaStep

/-- Multi-step eta reduction. -/
abbrev EtaMulti := Rewriting.Star EtaStep

/-- Notation for multi-step eta reduction. -/
scoped infix:50 " →η* " => EtaMulti

/-! ## Shift Cancellation -/

/-- Shifting by `1` and then by `-1` at the same cutoff is the identity. -/
theorem shift_neg1_shift1_at (M : Term) (c : Nat) : shift (-1) c (shift 1 c M) = M := by
  induction M generalizing c with
  | var n =>
      by_cases h : n < c
      · simp [shift, h]
      · have h' : ¬ n + 1 < c := by omega
        simp [shift, h, h']
        omega
  | app M N ihM ihN =>
      simp [shift, ihM c, ihN c]
  | lam M ih =>
      simpa [shift] using ih (c + 1)

/-- Special case of `shift_neg1_shift1_at` at cutoff `0`. -/
theorem shift_neg1_shift1 (M : Term) : shift (-1) 0 (shift 1 0 M) = M :=
  shift_neg1_shift1_at M 0

/-! ## Standard Eta Expansion -/

/-- Standard eta expansion. -/
def etaExpand (M : Term) : Term := lam (app (shift 1 0 M) (var 0))

/-- Eta-expanded terms contract back in one eta step. -/
theorem etaExpand_reducible (M : Term) : etaExpand M →η M := by
  unfold etaExpand
  have h : hasFreeVar 0 (shift 1 0 M) = false := hasFreeVar_shift1_zero M
  have hη : lam (app (shift 1 0 M) (var 0)) →η shift (-1) 0 (shift 1 0 M) :=
    EtaStep.eta _ h
  simpa [shift_neg1_shift1] using hη

/-! ## Combined Beta-Eta Reduction -/

/-- One-step beta-eta reduction. -/
inductive BetaEtaStep : Term → Term → Prop where
  | beta : ∀ {M N}, M →β N → BetaEtaStep M N
  | eta : ∀ {M N}, M →η N → BetaEtaStep M N

/-- Notation for beta-eta reduction. -/
scoped infix:50 " →βη " => BetaEtaStep

/-- Multi-step beta-eta reduction. -/
abbrev BetaEtaMulti := Rewriting.Star BetaEtaStep

/-- Notation for multi-step beta-eta reduction. -/
scoped infix:50 " →βη* " => BetaEtaMulti

namespace BetaEtaStep

/-- Embed a beta step into beta-eta reduction. -/
theorem of_beta {M N : Term} (h : M →β N) : M →βη N :=
  BetaEtaStep.beta h

/-- Embed an eta step into beta-eta reduction. -/
theorem of_eta {M N : Term} (h : M →η N) : M →βη N :=
  BetaEtaStep.eta h

end BetaEtaStep

namespace BetaEtaMulti

/-- Multi-step beta reduction is also multi-step beta-eta reduction. -/
theorem of_beta_multi {M N : Term} (h : M →* N) : M →βη* N := by
  induction h with
  | refl =>
      exact Rewriting.Star.refl _
  | step hstep _ ih =>
      exact Rewriting.Star.head (BetaEtaStep.of_beta hstep) ih

/-- Multi-step eta reduction is also multi-step beta-eta reduction. -/
theorem of_eta_multi {M N : Term} (h : M →η* N) : M →βη* N := by
  induction h with
  | refl =>
      exact Rewriting.Star.refl _
  | tail _ hstep ih =>
      exact Rewriting.Star.tail ih (BetaEtaStep.of_eta hstep)

end BetaEtaMulti

end Metatheory.Lambda
