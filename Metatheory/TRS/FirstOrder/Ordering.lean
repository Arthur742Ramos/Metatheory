/-
# Orderings for First-Order TRSs

Provides lightweight, substitution-closed orderings useful for termination
and Knuth-Bendix completion certificates.
-/

import Metatheory.TRS.FirstOrder.Confluence
import Metatheory.TRS.FirstOrder.Positions

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Weight Ordering (KBO-style) -/

/-- Symbol and variable weights. -/
structure Weighting (sig : Signature) where
  w0 : Nat
  wf : sig.Sym → Nat

/-- Weighted size of a term. -/
def weight {sig : Signature} (w : Weighting sig) : Term sig → Nat
  | var _ => w.w0
  | app f args => w.wf f + Term.finSum (fun i => weight w (args i))

/-- Replacing a subterm with a heavier one increases total weight. -/
theorem weight_replace_lt {sig : Signature} (w : Weighting sig)
    {t u v t' t'' : Term sig} {p : Pos}
    (hrep1 : Term.replace t p u = some t')
    (hrep2 : Term.replace t p v = some t'')
    (h : weight w u < weight w v) :
    weight w t' < weight w t'' := by
  induction p generalizing t u v t' t'' with
  | nil =>
      have ht' : t' = u := by
        simpa [Term.replace] using hrep1
      have ht'' : t'' = v := by
        simpa [Term.replace] using hrep2
      subst ht' ht''
      simpa using h
  | cons i ps ih =>
      cases t with
      | var x =>
          simp [Term.replace] at hrep1
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            cases hrep1' : Term.replace (args ⟨i, hi⟩) ps u with
            | none =>
                simp [Term.replace, hi, hrep1'] at hrep1
            | some t1 =>
              cases hrep2' : Term.replace (args ⟨i, hi⟩) ps v with
              | none =>
                  simp [Term.replace, hi, hrep2'] at hrep2
              | some t2 =>
                  have ht' : t' =
                      app f (fun j => if _ : j = ⟨i, hi⟩ then t1 else args j) := by
                    simpa [Term.replace, hi, hrep1'] using hrep1
                  have ht'' : t'' =
                      app f (fun j => if _ : j = ⟨i, hi⟩ then t2 else args j) := by
                    simpa [Term.replace, hi, hrep2'] using hrep2
                  subst ht' ht''
                  have hwt : weight w t1 < weight w t2 := ih hrep1' hrep2' h
                  have hsum :
                      Term.finSum (fun j => weight w (if _ : j = ⟨i, hi⟩ then t1 else args j)) <
                      Term.finSum (fun j => weight w (if _ : j = ⟨i, hi⟩ then t2 else args j)) := by
                    refine Term.finSum_lt_of_lt (i := ⟨i, hi⟩) ?_ ?_
                    · simpa using hwt
                    · intro j hj
                      by_cases hji : j = ⟨i, hi⟩
                      · exact (hj hji).elim
                      · simp [hji]
                  have : w.wf f +
                      Term.finSum (fun j => weight w (if _ : j = ⟨i, hi⟩ then t1 else args j)) <
                      w.wf f +
                      Term.finSum (fun j => weight w (if _ : j = ⟨i, hi⟩ then t2 else args j)) :=
                    Nat.add_lt_add_left hsum (w.wf f)
                  simpa [weight] using this
          ·
            simp [Term.replace, hi] at hrep1

/-- Stable weight ordering: weight decreases under all substitutions. -/
def stableWeightLt {sig : Signature} (w : Weighting sig) (s t : Term sig) : Prop :=
  ∀ sub : Subst sig, weight w (Term.subst sub s) < weight w (Term.subst sub t)

theorem stableWeightLt_wf {sig : Signature} (w : Weighting sig) :
    WellFounded (stableWeightLt (sig := sig) w) := by
  apply Subrelation.wf
  · intro a b h
    have h' := h Term.idSubst
    simpa [stableWeightLt, Term.subst_id] using h'
  · exact InvImage.wf (weight w) Nat.lt_wfRel.wf

theorem stableWeightLt_trans {sig : Signature} (w : Weighting sig) :
    Transitive (stableWeightLt (sig := sig) w) := by
  intro a b c hab hbc sub
  exact Nat.lt_trans (hab sub) (hbc sub)

theorem stableWeightLt_subst {sig : Signature} (w : Weighting sig) {sub : Subst sig} {s t : Term sig} :
    stableWeightLt (sig := sig) w s t →
      stableWeightLt (sig := sig) w (Term.subst sub s) (Term.subst sub t) := by
  intro h sub'
  have := h (Term.compSubst sub' sub)
  simpa [Term.subst_comp] using this

theorem stableWeightLt_replace {sig : Signature} (w : Weighting sig)
    {t : Term sig} {p : Pos} {u v t' t'' : Term sig}
    (h : stableWeightLt (sig := sig) w u v)
    (hrep1 : Term.replace t p u = some t')
    (hrep2 : Term.replace t p v = some t'') :
    stableWeightLt (sig := sig) w t' t'' := by
  intro sub
  have hrep1' := Term.replace_subst (sub := sub) (t := t) (p := p) (u := u) (t' := t') hrep1
  have hrep2' := Term.replace_subst (sub := sub) (t := t) (p := p) (u := v) (t' := t'') hrep2
  have hsize : weight w (Term.subst sub u) < weight w (Term.subst sub v) := h sub
  simpa using weight_replace_lt (w := w) (t := Term.subst sub t)
    (p := p) (u := Term.subst sub u) (v := Term.subst sub v)
    (t' := Term.subst sub t') (t'' := Term.subst sub t'') hrep1' hrep2' hsize

/-- Weight ordering packaged as a reduction ordering (KBO-style). -/
def kboOrdering (sig : Signature) (w : Weighting sig) : ReductionOrdering sig :=
  { lt := stableWeightLt w
    wf := stableWeightLt_wf w
    trans := stableWeightLt_trans w
    subst_closed := stableWeightLt_subst w
    replace_closed := by
      intro t p u v t' t'' h hrep1 hrep2
      exact stableWeightLt_replace (w := w) (t := t) (p := p) (u := u) (v := v) (t' := t') (t'' := t'') h hrep1 hrep2 }

/-- Termination from a KBO-style ordering. -/
theorem terminating_of_kbo {sig : Signature} {rules : RuleSet sig} (w : Weighting sig)
    (hord : ∀ r, rules r → stableWeightLt (sig := sig) w r.rhs r.lhs) :
    Terminating rules :=
  terminating_of_ordering (ord := kboOrdering sig w) hord

/-! ## LPO Ordering -/

-- LPO ordering is defined in `LPO.lean`, but its well-foundedness and
-- context-closure are not proven here.

end Metatheory.TRS.FirstOrder
