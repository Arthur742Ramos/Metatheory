/-
# Lexicographic Path Ordering (LPO)

A proper implementation of the Lexicographic Path Ordering with precedence.
LPO is a simplification ordering used for proving termination of TRSs.
-/

import Metatheory.TRS.FirstOrder.Confluence
import Mathlib.Logic.Relation
import Mathlib.Data.List.Shortlex

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Precedence -/

/-- A precedence is a strict partial order on symbols. -/
structure Precedence (sig : Signature) where
  /-- The strict ordering relation on symbols. -/
  lt : sig.Sym → sig.Sym → Prop
  /-- The ordering is irreflexive. -/
  irrefl : ∀ f, ¬ lt f f
  /-- The ordering is transitive. -/
  trans : ∀ f g h, lt f g → lt g h → lt f h
  /-- The ordering is well-founded. -/
  wf : WellFounded lt

/-! ## LPO Definition -/

/-- Lexicographic Path Ordering on terms.
    s >_lpo t if one of the following holds:
    1. s = f(s₁,...,sₙ) and sᵢ = t for some i (subterm equality)
    2. s = f(s₁,...,sₙ) and sᵢ >_lpo t for some i (subterm strict)
    3. s = f(s₁,...,sₘ) and t = g(t₁,...,tₙ) with f > g and s >_lpo tⱼ for all j
    4. s = f(s₁,...,sₘ) and t = f(t₁,...,tₙ) with lexicographic comparison
       and s >_lpo tⱼ for all j
-/
inductive LPO {sig : Signature} (prec : Precedence sig) : Term sig → Term sig → Prop where
  | subEq : ∀ {f : sig.Sym} {args : Fin (sig.arity f) → Term sig} {i : Fin (sig.arity f)},
      LPO prec (Term.app f args) (args i)
  | subLt : ∀ {f : sig.Sym} {args : Fin (sig.arity f) → Term sig} {t : Term sig} {i : Fin (sig.arity f)},
      LPO prec (args i) t →
      LPO prec (Term.app f args) t
  | precGt : ∀ {f g : sig.Sym} {args : Fin (sig.arity f) → Term sig} {args' : Fin (sig.arity g) → Term sig},
      prec.lt g f →
      (∀ j, LPO prec (Term.app f args) (args' j)) →
      LPO prec (Term.app f args) (Term.app g args')
  | lexEq : ∀ {f : sig.Sym} {args args' : Fin (sig.arity f) → Term sig} {k : Fin (sig.arity f)},
      (∀ i, i < k → args i = args' i) →
      LPO prec (args k) (args' k) →
      (∀ j, LPO prec (Term.app f args) (args' j)) →
      LPO prec (Term.app f args) (Term.app f args')

/-- LPO is greater-than-or-equal. -/
def LPOge {sig : Signature} (prec : Precedence sig) (s t : Term sig) : Prop :=
  s = t ∨ LPO prec s t

theorem lpo_mono {sig : Signature} {prec prec' : Precedence sig}
    (hprec : ∀ f g, prec.lt f g → prec'.lt f g) :
    ∀ {s t : Term sig}, LPO prec s t → LPO prec' s t := by
  intro s t h
  induction h with
  | subEq => exact LPO.subEq
  | subLt h ih => exact LPO.subLt ih
  | precGt hlt hall ih =>
      exact LPO.precGt (hprec _ _ hlt) (by intro j; exact ih j)
  | lexEq hprefix hlt hall ih =>
      exact LPO.lexEq hprefix (ih hlt) (by intro j; exact ih (hall j))

/-! ## Basic LPO Properties -/

/-- Variables are not LPO-greater than anything. -/
theorem lpo_var_not_gt {sig : Signature} (prec : Precedence sig) (x : Nat) (t : Term sig) :
    ¬ LPO prec (Term.var x) t := by
  intro h
  cases h

/-- If s > t via subEq, then t is an argument of s. -/
theorem lpo_subEq_arg {sig : Signature} (prec : Precedence sig)
    {f : sig.Sym} {args : Fin (sig.arity f) → Term sig} {i : Fin (sig.arity f)} :
    LPO prec (Term.app f args) (args i) := LPO.subEq

/-! ## Stable LPO -/

/-- LPO is closed under substitution. -/
theorem lpo_subst {sig : Signature} (prec : Precedence sig)
    {sub : Subst sig} {s t : Term sig} :
    LPO prec s t → LPO prec (Term.subst sub s) (Term.subst sub t) := by
  intro h
  induction h with
  | subEq =>
      exact LPO.subEq
  | subLt h ih =>
      exact LPO.subLt ih
  | precGt hlt hall ih =>
      exact LPO.precGt hlt (by intro j; exact ih j)
  | lexEq hprefix hlt hall ih =>
      exact LPO.lexEq hprefix (ih hlt) (by intro j; exact ih (hall j))

/-- Stable LPO: holds under all substitutions. -/
def StableLPO {sig : Signature} (prec : Precedence sig) (s t : Term sig) : Prop :=
  ∀ sub : Subst sig, LPO prec (Term.subst sub s) (Term.subst sub t)

/-- LPO implies stable LPO. -/
theorem stableLPO_of_lpo {sig : Signature} (prec : Precedence sig) {s t : Term sig} :
    LPO prec s t → StableLPO prec s t := by
  intro h sub
  exact lpo_subst prec (sub := sub) h

/-- Stable LPO implies LPO (at the identity substitution). -/
theorem lpo_of_stableLPO {sig : Signature} (prec : Precedence sig) {s t : Term sig} :
    StableLPO prec s t → LPO prec s t := by
  intro h
  exact h Term.idSubst

/-- Stable LPO is equivalent to LPO. -/
theorem stableLPO_iff {sig : Signature} (prec : Precedence sig) {s t : Term sig} :
    StableLPO prec s t ↔ LPO prec s t := by
  constructor
  · exact lpo_of_stableLPO prec
  · exact stableLPO_of_lpo prec

/-- Stable LPO is closed under substitution by definition. -/
theorem stableLPO_subst {sig : Signature} (prec : Precedence sig)
    {sub : Subst sig} {s t : Term sig}
    (h : StableLPO prec s t) :
    StableLPO prec (Term.subst sub s) (Term.subst sub t) := by
  intro sub'
  have := h (Term.compSubst sub' sub)
  simpa [Term.subst_comp] using this

/-! ## Context Closure -/

theorem lpo_replace {sig : Signature} (prec : Precedence sig)
    {t u v t' t'' : Term sig} {p : Pos} :
    LPO prec u v →
    Term.replace t p u = some t' →
    Term.replace t p v = some t'' →
    LPO prec t' t'' := by
  intro hlt hrep_u hrep_v
  induction p generalizing t t' t'' with
  | nil =>
      have ht' : t' = u := by
        simpa [Term.replace] using hrep_u.symm
      have ht'' : t'' = v := by
        simpa [Term.replace] using hrep_v.symm
      subst ht' ht''
      exact hlt
  | cons i ps ih =>
      cases t with
      | var x =>
          simp [Term.replace] at hrep_u
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            cases hrep_u' : Term.replace (args ⟨i, hi⟩) ps u with
            | none =>
                simp [Term.replace, hi, hrep_u'] at hrep_u
            | some u' =>
                have ht' : t' =
                    Term.app f (fun j => if _ : j = ⟨i, hi⟩ then u' else args j) := by
                  simpa [Term.replace, hi, hrep_u'] using hrep_u.symm
                cases hrep_v' : Term.replace (args ⟨i, hi⟩) ps v with
                | none =>
                    simp [Term.replace, hi, hrep_v'] at hrep_v
                | some v' =>
                    have ht'' : t'' =
                        Term.app f (fun j => if _ : j = ⟨i, hi⟩ then v' else args j) := by
                      simpa [Term.replace, hi, hrep_v'] using hrep_v.symm
                    subst ht' ht''
                    set idx : Fin (sig.arity f) := ⟨i, hi⟩
                    set args1 : Fin (sig.arity f) → Term sig :=
                      fun j => if _ : j = idx then u' else args j
                    set args2 : Fin (sig.arity f) → Term sig :=
                      fun j => if _ : j = idx then v' else args j
                    have hlt' : LPO prec u' v' :=
                      ih (t := args idx) (t' := u') (t'' := v') hlt hrep_u' hrep_v'
                    have hprefix : ∀ j, j < idx → args1 j = args2 j := by
                      intro j hj
                      have hjne : j ≠ idx := ne_of_lt hj
                      simp [args1, args2, hjne]
                    have hall : ∀ j, LPO prec (Term.app f args1) (args2 j) := by
                      intro j
                      by_cases hj : j = idx
                      · subst hj
                        have hlt'' : LPO prec (args1 idx) (args2 idx) := by
                          simpa [args1, args2] using hlt'
                        exact LPO.subLt (f := f) (args := args1) (i := idx) hlt''
                      ·
                        have hsub : LPO prec (Term.app f args1) (args1 j) := LPO.subEq
                        simpa [args1, args2, hj] using hsub
                    exact LPO.lexEq (f := f) (args := args1) (args' := args2) (k := idx)
                      hprefix hlt' hall
          ·
            simp [Term.replace, hi] at hrep_u

theorem stableLPO_replace {sig : Signature} (prec : Precedence sig)
    {t u v t' t'' : Term sig} {p : Pos} :
    StableLPO prec u v →
    Term.replace t p u = some t' →
    Term.replace t p v = some t'' →
    StableLPO prec t' t'' := by
  intro hlt hrep_u hrep_v sub
  have hrep_u' := Term.replace_subst (sub := sub) (t := t) (p := p) (u := u) (t' := t') hrep_u
  have hrep_v' := Term.replace_subst (sub := sub) (t := t) (p := p) (u := v) (t' := t'') hrep_v
  exact lpo_replace prec (hlt sub) hrep_u' hrep_v'

/-! ## Transitive Closure -/

/-- Transitive closure of stable LPO (mathlib `Relation.TransGen`). -/
def StableLPOplus {sig : Signature} (prec : Precedence sig) : Term sig → Term sig → Prop :=
  Relation.TransGen (StableLPO prec)

/-- Stable LPO is closed under a single step. -/
theorem stableLPOplus_single {sig : Signature} (prec : Precedence sig) {s t : Term sig} :
    StableLPO prec s t → StableLPOplus prec s t :=
  Relation.TransGen.single

theorem stableLPOplus_trans {sig : Signature} (prec : Precedence sig) :
    Transitive (StableLPOplus prec) := by
  intro a b c hab hbc
  exact Relation.TransGen.trans hab hbc

theorem stableLPOplus_wf {sig : Signature} (prec : Precedence sig) :
    WellFounded (StableLPOplus prec) := by
  exact (stableLPO_wf prec).transGen

theorem stableLPOplus_subst {sig : Signature} (prec : Precedence sig)
    {sub : Subst sig} {s t : Term sig} :
    StableLPOplus prec s t →
      StableLPOplus prec (Term.subst sub s) (Term.subst sub t) := by
  intro h
  refine Relation.TransGen.lift (f := fun u => Term.subst sub u) ?_ h
  intro a b hab
  exact stableLPO_subst prec (sub := sub) hab

theorem stableLPOplus_replace {sig : Signature} (prec : Precedence sig)
    {t : Term sig} {p : Pos} {u v t' t'' : Term sig} :
    StableLPOplus prec u v →
    Term.replace t p u = some t' →
    Term.replace t p v = some t'' →
    StableLPOplus prec t' t'' := by
  intro h hrep_u hrep_v
  induction h generalizing t' t'' with
  | single hstep =>
      exact Relation.TransGen.single (stableLPO_replace prec hstep hrep_u hrep_v)
  | tail (b := b) h hstep ih =>
      obtain ⟨t1, hrep_b⟩ :=
        Term.replace_defined_of_replace (t := t) (p := p) (u := u) (t' := t') hrep_u b
      have ih' : StableLPOplus prec t' t1 := ih hrep_u hrep_b
      have hstep' : StableLPO prec t1 t'' := stableLPO_replace prec hstep hrep_b hrep_v
      exact Relation.TransGen.tail ih' hstep'

/-! ## Well-Foundedness -/

private def LPOList {sig : Signature} (prec : Precedence sig) : List (Term sig) → List (Term sig) → Prop :=
  List.Shortlex (LPO prec)

private def lpoMeasure {sig : Signature} (prec : Precedence sig) : Term sig → Ordinal
  | Term.var _ => 0
  | Term.app f args =>
      let recArg : Fin (sig.arity f) → Ordinal := fun i => lpoMeasure prec (args i)
      let m := ⨆ i : Fin (sig.arity f), recArg i
      Ordinal.omega0 * (IsWellFounded.rank (α := sig.Sym) prec.lt f) + m + 1

private theorem lpoMeasure_subterm {sig : Signature} (prec : Precedence sig)
    {f : sig.Sym} {args : Fin (sig.arity f) → Term sig} {i : Fin (sig.arity f)} :
    lpoMeasure prec (args i) < lpoMeasure prec (Term.app f args) := by
  have hle : lpoMeasure prec (args i) ≤ ⨆ j : Fin (sig.arity f), lpoMeasure prec (args j) :=
    Ordinal.le_iSup (fun j : Fin (sig.arity f) => lpoMeasure prec (args j)) i
  have hlt : lpoMeasure prec (args i) <
      Ordinal.omega0 * (IsWellFounded.rank (α := sig.Sym) prec.lt f) +
        (⨆ j : Fin (sig.arity f), lpoMeasure prec (args j)) + 1 := by
    exact (Ordinal.lt_succ_of_le (Ordinal.le_add_left _ _ |>.trans hle))
  simpa [lpoMeasure] using hlt

private theorem lpoMeasure_prec {sig : Signature} (prec : Precedence sig)
    {f g : sig.Sym} {args : Fin (sig.arity f) → Term sig} {args' : Fin (sig.arity g) → Term sig}
    (hfg : prec.lt g f) :
    lpoMeasure prec (Term.app g args') < lpoMeasure prec (Term.app f args) := by
  have hrank : IsWellFounded.rank (α := sig.Sym) prec.lt g <
      IsWellFounded.rank (α := sig.Sym) prec.lt f :=
    IsWellFounded.rank_lt_of_rel hfg
  have hmul :
      Ordinal.omega0 * IsWellFounded.rank (α := sig.Sym) prec.lt g <
      Ordinal.omega0 * IsWellFounded.rank (α := sig.Sym) prec.lt f := by
    exact (Ordinal.mul_lt_mul_iff_left (a0 := Ordinal.omega0_pos)).2 hrank
  have hlt :
      Ordinal.omega0 * IsWellFounded.rank (α := sig.Sym) prec.lt g +
          (⨆ i : Fin (sig.arity g), lpoMeasure prec (args' i)) + 1 <
      Ordinal.omega0 * IsWellFounded.rank (α := sig.Sym) prec.lt f :=
    (Ordinal.add_lt_add_iff_left _).2 <| (Ordinal.lt_succ_iff).2 <| by
      exact (Ordinal.lt_of_lt_of_le hmul (Ordinal.le_add_right _ _))
  have hlt' :
      Ordinal.omega0 * IsWellFounded.rank (α := sig.Sym) prec.lt g +
          (⨆ i : Fin (sig.arity g), lpoMeasure prec (args' i)) + 1 <
      Ordinal.omega0 * IsWellFounded.rank (α := sig.Sym) prec.lt f +
          (⨆ i : Fin (sig.arity f), lpoMeasure prec (args i)) + 1 :=
    lt_of_lt_of_le hlt (Ordinal.le_add_right _ _)
  simpa [lpoMeasure] using hlt'

private theorem lpoMeasure_lex {sig : Signature} (prec : Precedence sig)
    {f : sig.Sym} {args args' : Fin (sig.arity f) → Term sig} {k : Fin (sig.arity f)}
    (hprefix : ∀ i, i < k → args i = args' i)
    (hk : lpoMeasure prec (args' k) < lpoMeasure prec (args k)) :
    lpoMeasure prec (Term.app f args') < lpoMeasure prec (Term.app f args) := by
  have hsup : ⨆ i : Fin (sig.arity f), lpoMeasure prec (args' i) <
      ⨆ i : Fin (sig.arity f), lpoMeasure prec (args i) := by
    refine (Ordinal.lt_iSup_iff).2 ?_
    refine ⟨k, ?_⟩
    exact hk.trans_le (Ordinal.le_iSup (fun i : Fin (sig.arity f) => lpoMeasure prec (args i)) k)
  have hlt :
      Ordinal.omega0 * IsWellFounded.rank (α := sig.Sym) prec.lt f +
          (⨆ i : Fin (sig.arity f), lpoMeasure prec (args' i)) + 1 <
      Ordinal.omega0 * IsWellFounded.rank (α := sig.Sym) prec.lt f +
          (⨆ i : Fin (sig.arity f), lpoMeasure prec (args i)) + 1 := by
    exact (Ordinal.add_lt_add_iff_left _).2 <| (Ordinal.add_lt_add_iff_left _).2 hsup
  simpa [lpoMeasure] using hlt

theorem lpo_wf {sig : Signature} (prec : Precedence sig) : WellFounded (LPO prec) := by
  refine Subrelation.wf ?_ ?_
  · intro s t h
    induction h with
    | subEq =>
        exact lpoMeasure_subterm prec
    | subLt h ih =>
        exact (lpoMeasure_subterm prec).trans ih
    | precGt hlt _ =>
        exact lpoMeasure_prec prec hlt
    | lexEq hprefix hk _ =>
        have hk' : lpoMeasure prec (args' k) < lpoMeasure prec (args k) := by
          exact (ih hk)
        exact lpoMeasure_lex prec hprefix hk'
  · exact InvImage.wf (lpoMeasure prec) Ordinal.lt_wf

theorem stableLPO_wf {sig : Signature} (prec : Precedence sig) :
    WellFounded (StableLPO prec) := by
  refine Subrelation.wf ?_ ?_
  · intro s t h
    have h' : LPO prec s t := h Term.idSubst
    exact (lpo_wf prec).apply _ h'
  · exact lpo_wf prec

/-! ## LPO Examples -/

/-- Example precedence: total order on symbols by some encoding. -/
def totalPrecedence (sig : Signature) [LinearOrder sig.Sym] : Precedence sig where
  lt := (· < ·)
  irrefl := lt_irrefl
  trans := fun _ _ _ => lt_trans
  wf := IsWellFounded.wf (r := (· < ·))

end Metatheory.TRS.FirstOrder
