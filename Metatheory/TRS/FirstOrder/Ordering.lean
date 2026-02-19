/-
# Orderings for First-Order TRSs

Provides lightweight, substitution-closed orderings useful for termination
and Knuth-Bendix completion certificates.
-/

import Metatheory.TRS.FirstOrder.Confluence
import Metatheory.TRS.FirstOrder.Positions
import Metatheory.TRS.FirstOrder.LPO

namespace Metatheory.TRS.FirstOrder

/- TODO: Fix Mathlib dependency (Prod.Lex, Prod.Basic, etc.)

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

/-! ## Argument Filtering -/

/-- Argument filtering: keep a list of argument positions. -/
structure ArgFilter (sig : Signature) where
  keep : ∀ f, Option (Fin (sig.arity f))

/-- Identity filtering (keeps all arguments). -/
def ArgFilter.id (sig : Signature) : ArgFilter sig :=
  { keep := fun _ => none }

def filterTerm {sig : Signature} (af : ArgFilter sig) : Term sig → Term sig
  | var x => Term.var x
  | app f args =>
      match af.keep f with
      | none => Term.app f (fun i => filterTerm af (args i))
      | some i => filterTerm af (args i)

def filterPos {sig : Signature} (af : ArgFilter sig) : Term sig → Pos → Option Pos
  | t, [] => some []
  | Term.var _, _ :: _ => none
  | Term.app f args, i :: ps =>
      match af.keep f with
      | none =>
          if h : i < sig.arity f then
            match filterPos af (args ⟨i, h⟩) ps with
            | none => none
            | some q => some (i :: q)
          else none
      | some j =>
          if h : i = j.val then
            filterPos af (args j) ps
          else none

theorem filterPos_replace {sig : Signature} (af : ArgFilter sig) :
    ∀ {t p u t' q},
      Term.replace t p u = some t' →
      filterPos af t p = some q →
      Term.replace (filterTerm af t) q (filterTerm af u) = some (filterTerm af t') := by
  intro t p u t' q hrep hpos
  induction p generalizing t u t' q with
  | nil =>
      have ht' : t' = u := by
        simpa [Term.replace] using hrep
      have hq : q = [] := by
        simpa [filterPos] using hpos
      subst ht' hq
      simp [Term.replace]
  | cons i ps ih =>
      cases t with
      | var x =>
          simp [Term.replace] at hrep
      | app f args =>
          cases hkeep : af.keep f with
          | none =>
              by_cases hi : i < sig.arity f
              ·
                cases hrep1 : Term.replace (args ⟨i, hi⟩) ps u with
                | none =>
                    simp [Term.replace, hi, hrep1] at hrep
                | some t1 =>
                    have ht' : t' =
                        Term.app f (fun j => if _ : j = ⟨i, hi⟩ then t1 else args j) := by
                      simpa [Term.replace, hi, hrep1] using hrep
                    cases hpf : filterPos af (args ⟨i, hi⟩) ps with
                    | none =>
                        simp [filterPos, hkeep, hi, hpf] at hpos
                    | some q' =>
                        have hq : q = i :: q' := by
                          simpa [filterPos, hkeep, hi, hpf] using hpos
                        subst hq
                        have ih' :=
                          ih (t := args ⟨i, hi⟩) (u := u) (t' := t1) (q := q') hrep1 hpf
                        have hfilter_t' : filterTerm af t' =
                            Term.app f (fun j =>
                              if _ : j = ⟨i, hi⟩ then filterTerm af t1 else filterTerm af (args j)) := by
                          subst ht'
                          simp [filterTerm, hkeep]
                          funext j
                          by_cases hji : j = ⟨i, hi⟩ <;> simp [hji]
                        have hrep' :
                            Term.replace
                              (Term.app f (fun j => filterTerm af (args j)))
                              (i :: q') (filterTerm af u) =
                                some (Term.app f (fun j =>
                                  if _ : j = ⟨i, hi⟩ then filterTerm af t1 else filterTerm af (args j))) := by
                          simp [Term.replace, hi, ih']
                        simpa [filterTerm, hkeep, hfilter_t'] using hrep'
              ·
                simp [Term.replace, hi] at hrep
          | some j =>
              by_cases hji : i = j.val
              ·
                have hi : i < sig.arity f := by
                  simpa [hji] using j.isLt
                have hidx : (⟨i, hi⟩ : Fin (sig.arity f)) = j := by
                  ext
                  exact hji
                have hpos' : filterPos af (args j) ps = some q := by
                  simpa [filterPos, hkeep, hji] using hpos
                cases hrep1 : Term.replace (args j) ps u with
                | none =>
                    have hrep' : Term.replace (args ⟨i, hi⟩) ps u = none := by
                      simpa [hidx] using hrep1
                    simp [Term.replace, hi, hrep'] at hrep
                | some t1 =>
                    have hrep' : Term.replace (args ⟨i, hi⟩) ps u = some t1 := by
                      simpa [hidx] using hrep1
                    have ht' : t' =
                        Term.app f (fun j => if _ : j = ⟨i, hi⟩ then t1 else args j) := by
                      simpa [Term.replace, hi, hrep'] using hrep
                    have ih' := ih (t := args j) (u := u) (t' := t1) (q := q) hrep1 hpos'
                    have hfilter_t' : filterTerm af t' = filterTerm af t1 := by
                      subst ht'
                      simp [filterTerm, hkeep, hji]
                    simpa [filterTerm, hkeep, hji, hfilter_t'] using ih'
              ·
                simp [filterPos, hkeep, hji] at hpos
theorem filterTerm_id {sig : Signature} (t : Term sig) :
    filterTerm (ArgFilter.id sig) t = t := by
  induction t with
  | var x => rfl
  | app f args ih =>
      simp [filterTerm, ArgFilter.id]
      apply congrArg (fun args' => Term.app f args')
      funext i
      exact ih i

theorem filterTerm_subst {sig : Signature} (af : ArgFilter sig) (sub : Subst sig) :
    ∀ t, filterTerm af (Term.subst sub t) =
      Term.subst sub (filterTerm af t) := by
  intro t
  induction t with
  | var x =>
      simp [filterTerm, Term.subst]
  | app f args ih =>
      cases hkeep : af.keep f with
      | none =>
          simp [filterTerm, Term.subst, hkeep, ih]
      | some i =>
          simp [filterTerm, Term.subst, hkeep, ih]

/-- Filtered ordering induced by a base reduction ordering. -/
def filteredLt {sig : Signature} (ord : ReductionOrdering sig) (af : ArgFilter sig)
    (s t : Term sig) : Prop :=
  ord.lt (filterTerm af s) (filterTerm af t)

theorem filteredLt_wf {sig : Signature} (ord : ReductionOrdering sig) (af : ArgFilter sig) :
    WellFounded (filteredLt (sig := sig) ord af) := by
  exact InvImage.wf (filterTerm af) ord.wf

theorem filteredLt_trans {sig : Signature} (ord : ReductionOrdering sig) (af : ArgFilter sig) :
    Transitive (filteredLt (sig := sig) ord af) := by
  intro a b c hab hbc
  exact ord.trans hab hbc

theorem filteredLt_subst {sig : Signature} (ord : ReductionOrdering sig) (af : ArgFilter sig)
    {sub : Subst sig} {s t : Term sig} :
    filteredLt ord af s t →
      filteredLt ord af (Term.subst sub s) (Term.subst sub t) := by
  intro h
  have h' := ord.subst_closed (s := filterTerm af s) (t := filterTerm af t) h
  simpa [filteredLt, filterTerm_subst] using h'

theorem filteredLt_id {sig : Signature} (ord : ReductionOrdering sig) (s t : Term sig) :
    filteredLt ord (ArgFilter.id sig) s t ↔ ord.lt s t := by
  simp [filteredLt, filterTerm_id, ArgFilter.id]

/-! ## Linear Polynomial Interpretation -/

/-- Linear polynomial interpretation with positive coefficients. -/
structure LinearWeighting (sig : Signature) where
  w0 : Nat
  wf : sig.Sym → Nat
  coeff : ∀ f, Fin (sig.arity f) → Nat
  coeff_pos : ∀ f i, 0 < coeff f i

/-- Linear polynomial weight of a term. -/
def linearWeight {sig : Signature} (w : LinearWeighting sig) : Term sig → Nat
  | var _ => w.w0
  | app f args => w.wf f + Term.finSum (fun i => w.coeff f i * linearWeight w (args i))

/-- Replacing a subterm with a heavier one increases the linear weight. -/
theorem linearWeight_replace_lt {sig : Signature} (w : LinearWeighting sig)
    {t u v t' t'' : Term sig} {p : Pos}
    (hrep1 : Term.replace t p u = some t')
    (hrep2 : Term.replace t p v = some t'')
    (h : linearWeight w u < linearWeight w v) :
    linearWeight w t' < linearWeight w t'' := by
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
                  set idx : Fin (sig.arity f) := ⟨i, hi⟩
                  set args1 : Fin (sig.arity f) → Term sig :=
                    fun j => if _ : j = idx then t1 else args j
                  set args2 : Fin (sig.arity f) → Term sig :=
                    fun j => if _ : j = idx then t2 else args j
                  have hwt : linearWeight w t1 < linearWeight w t2 :=
                    ih hrep1' hrep2' h
                  have hmul :
                      w.coeff f idx * linearWeight w t1 < w.coeff f idx * linearWeight w t2 := by
                    exact Nat.mul_lt_mul_of_pos_left hwt (w.coeff_pos f idx)
                  have hsum :
                      Term.finSum (fun j => w.coeff f j * linearWeight w (args1 j)) <
                      Term.finSum (fun j => w.coeff f j * linearWeight w (args2 j)) := by
                    refine Term.finSum_lt_of_lt (i := idx) ?_ ?_
                    · simpa [args1, args2] using hmul
                    · intro j hj
                      by_cases hji : j = idx
                      · exact (hj hji).elim
                      · simp [args1, args2, hji]
                  have : w.wf f +
                      Term.finSum (fun j => w.coeff f j * linearWeight w (args1 j)) <
                      w.wf f +
                      Term.finSum (fun j => w.coeff f j * linearWeight w (args2 j)) :=
                    Nat.add_lt_add_left hsum (w.wf f)
                  simpa [linearWeight] using this
          ·
            simp [Term.replace, hi] at hrep1

/-- Stable linear weight ordering. -/
def stableLinearWeightLt {sig : Signature} (w : LinearWeighting sig) (s t : Term sig) : Prop :=
  ∀ sub : Subst sig, linearWeight w (Term.subst sub s) < linearWeight w (Term.subst sub t)

theorem stableLinearWeightLt_wf {sig : Signature} (w : LinearWeighting sig) :
    WellFounded (stableLinearWeightLt (sig := sig) w) := by
  apply Subrelation.wf
  · intro a b h
    have h' := h Term.idSubst
    simpa [stableLinearWeightLt, Term.subst_id] using h'
  · exact InvImage.wf (linearWeight w) Nat.lt_wfRel.wf

theorem stableLinearWeightLt_trans {sig : Signature} (w : LinearWeighting sig) :
    Transitive (stableLinearWeightLt (sig := sig) w) := by
  intro a b c hab hbc sub
  exact Nat.lt_trans (hab sub) (hbc sub)

theorem stableLinearWeightLt_subst {sig : Signature} (w : LinearWeighting sig)
    {sub : Subst sig} {s t : Term sig} :
    stableLinearWeightLt (sig := sig) w s t →
      stableLinearWeightLt (sig := sig) w (Term.subst sub s) (Term.subst sub t) := by
  intro h sub'
  have := h (Term.compSubst sub' sub)
  simpa [Term.subst_comp] using this

theorem stableLinearWeightLt_replace {sig : Signature} (w : LinearWeighting sig)
    {t : Term sig} {p : Pos} {u v t' t'' : Term sig}
    (h : stableLinearWeightLt (sig := sig) w u v)
    (hrep1 : Term.replace t p u = some t')
    (hrep2 : Term.replace t p v = some t'') :
    stableLinearWeightLt (sig := sig) w t' t'' := by
  intro sub
  have hrep1' := Term.replace_subst (sub := sub) (t := t) (p := p) (u := u) (t' := t') hrep1
  have hrep2' := Term.replace_subst (sub := sub) (t := t) (p := p) (u := v) (t' := t'') hrep2
  have hsize : linearWeight w (Term.subst sub u) < linearWeight w (Term.subst sub v) := h sub
  simpa using linearWeight_replace_lt (w := w) (t := Term.subst sub t)
    (p := p) (u := Term.subst sub u) (v := Term.subst sub v)
    (t' := Term.subst sub t') (t'' := Term.subst sub t'') hrep1' hrep2' hsize

/-- Linear polynomial interpretation packaged as a reduction ordering. -/
def linearOrdering (sig : Signature) (w : LinearWeighting sig) : ReductionOrdering sig :=
  { lt := stableLinearWeightLt w
    wf := stableLinearWeightLt_wf w
    trans := stableLinearWeightLt_trans w
    subst_closed := stableLinearWeightLt_subst w
    replace_closed := by
      intro t p u v t' t'' h hrep1 hrep2
      exact stableLinearWeightLt_replace (w := w) (t := t) (p := p) (u := u) (v := v)
        (t' := t') (t'' := t'') h hrep1 hrep2 }

/-- Termination from a linear polynomial interpretation. -/
theorem terminating_of_linear {sig : Signature} {rules : RuleSet sig} (w : LinearWeighting sig)
    (hord : ∀ r, rules r → stableLinearWeightLt (sig := sig) w r.rhs r.lhs) :
    Terminating rules :=
  terminating_of_ordering (ord := linearOrdering sig w) hord

/-! ## 2x2 Matrix Interpretation -/

abbrev Vec2 := Nat × Nat

def vec2Add (v w : Vec2) : Vec2 := (v.1 + w.1, v.2 + w.2)

def vec2Sum {n : Nat} (f : Fin n → Vec2) : Vec2 :=
  (Term.finSum (fun i => (f i).1), Term.finSum (fun i => (f i).2))

def vec2Lt (v w : Vec2) : Prop := Prod.Lex (· < ·) (· < ·) v w

theorem vec2Lt_add_left {u v w : Vec2} (h : vec2Lt v w) :
    vec2Lt (vec2Add u v) (vec2Add u w) := by
  rcases (Prod.lex_def).1 h with hlt | ⟨hEq, hlt⟩
  · exact (Prod.lex_def).2 (Or.inl (Nat.add_lt_add_left hlt u.1))
  · refine (Prod.lex_def).2 (Or.inr ?_)
    refine ⟨by simpa [vec2Add, hEq], Nat.add_lt_add_left hlt u.2⟩

theorem vec2Sum_lt_of_lt {n : Nat} {f g : Fin n → Vec2} (i : Fin n)
    (h : vec2Lt (f i) (g i)) (hrest : ∀ j, j ≠ i → f j = g j) :
    vec2Lt (vec2Sum f) (vec2Sum g) := by
  rcases (Prod.lex_def).1 h with hlt | ⟨hEq, hlt⟩
  ·
    have hsum1 :
        Term.finSum (fun j => (f j).1) < Term.finSum (fun j => (g j).1) := by
      refine Term.finSum_lt_of_lt (i := i) ?_ ?_
      · exact hlt
      · intro j hj
        have h' := hrest j hj
        simpa [h'] using rfl
    exact (Prod.lex_def).2 (Or.inl hsum1)
  ·
    have hfun1 : (fun j => (f j).1) = fun j => (g j).1 := by
      funext j
      by_cases hji : j = i
      · subst hji
        simpa [hEq]
      · have h' := hrest j hji
        simpa [h'] using rfl
    have hsum1 :
        Term.finSum (fun j => (f j).1) = Term.finSum (fun j => (g j).1) := by
      simpa [hfun1]
    have hsum2 :
        Term.finSum (fun j => (f j).2) < Term.finSum (fun j => (g j).2) := by
      refine Term.finSum_lt_of_lt (i := i) ?_ ?_
      · exact hlt
      · intro j hj
        have h' := hrest j hj
        simpa [h'] using rfl
    exact (Prod.lex_def).2 (Or.inr ⟨hsum1, hsum2⟩)

structure Mat2Lower where
  a11 : Nat
  a21 : Nat
  a22 : Nat
  a11_pos : 0 < a11
  a22_pos : 0 < a22

def matMul (M : Mat2Lower) (v : Vec2) : Vec2 :=
  (M.a11 * v.1, M.a21 * v.1 + M.a22 * v.2)

theorem matMul_lt_of_lt (M : Mat2Lower) {v w : Vec2} (h : vec2Lt v w) :
    vec2Lt (matMul M v) (matMul M w) := by
  rcases (Prod.lex_def).1 h with hlt | ⟨hEq, hlt⟩
  ·
    have hmul : M.a11 * v.1 < M.a11 * w.1 :=
      Nat.mul_lt_mul_of_pos_left hlt M.a11_pos
    exact (Prod.lex_def).2 (Or.inl hmul)
  ·
    have hmul : M.a22 * v.2 < M.a22 * w.2 :=
      Nat.mul_lt_mul_of_pos_left hlt M.a22_pos
    have hEq' : M.a11 * v.1 = M.a11 * w.1 := by
      simpa [hEq]
    have hlt' : M.a21 * v.1 + M.a22 * v.2 < M.a21 * v.1 + M.a22 * w.2 :=
      Nat.add_lt_add_left hmul (M.a21 * v.1)
    refine (Prod.lex_def).2 (Or.inr ⟨?_, hlt'⟩)
    exact hEq'

structure MatrixInterpretation (sig : Signature) where
  w0 : Vec2
  wf : sig.Sym → Vec2
  mat : ∀ f, Fin (sig.arity f) → Mat2Lower

def matrixWeight {sig : Signature} (w : MatrixInterpretation sig) : Term sig → Vec2
  | var _ => w.w0
  | app f args =>
      vec2Add (w.wf f)
        (vec2Sum (fun i => matMul (w.mat f i) (matrixWeight w (args i))))

theorem matrixWeight_replace_lt {sig : Signature} (w : MatrixInterpretation sig)
    {t u v t' t'' : Term sig} {p : Pos}
    (hrep1 : Term.replace t p u = some t')
    (hrep2 : Term.replace t p v = some t'')
    (h : vec2Lt (matrixWeight w u) (matrixWeight w v)) :
    vec2Lt (matrixWeight w t') (matrixWeight w t'') := by
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
                  set idx : Fin (sig.arity f) := ⟨i, hi⟩
                  set args1 : Fin (sig.arity f) → Term sig :=
                    fun j => if _ : j = idx then t1 else args j
                  set args2 : Fin (sig.arity f) → Term sig :=
                    fun j => if _ : j = idx then t2 else args j
                  have hwt : vec2Lt (matrixWeight w t1) (matrixWeight w t2) :=
                    ih hrep1' hrep2' h
                  have hmul :
                      vec2Lt (matMul (w.mat f idx) (matrixWeight w t1))
                        (matMul (w.mat f idx) (matrixWeight w t2)) :=
                    matMul_lt_of_lt (w.mat f idx) hwt
                  have hsum :
                      vec2Lt
                        (vec2Sum (fun j =>
                          matMul (w.mat f j) (matrixWeight w (args1 j))))
                        (vec2Sum (fun j =>
                          matMul (w.mat f j) (matrixWeight w (args2 j)))) := by
                    refine vec2Sum_lt_of_lt (i := idx) ?_ ?_
                    · simpa [args1, args2] using hmul
                    · intro j hj
                      by_cases hji : j = idx
                      · exact (hj hji).elim
                      · simp [args1, args2, hji]
                  have hsum' :
                      vec2Lt
                        (vec2Add (w.wf f)
                          (vec2Sum (fun j =>
                            matMul (w.mat f j) (matrixWeight w (args1 j)))))
                        (vec2Add (w.wf f)
                          (vec2Sum (fun j =>
                            matMul (w.mat f j) (matrixWeight w (args2 j))))) :=
                    vec2Lt_add_left hsum
                  simpa [matrixWeight] using hsum'
          ·
            simp [Term.replace, hi] at hrep1

def stableMatrixLt {sig : Signature} (w : MatrixInterpretation sig) (s t : Term sig) : Prop :=
  ∀ sub : Subst sig, vec2Lt (matrixWeight w (Term.subst sub s))
    (matrixWeight w (Term.subst sub t))

theorem vec2Lt_wf : WellFounded vec2Lt := by
  simpa [vec2Lt] using
    (WellFounded.prod_lex (ha := Nat.lt_wfRel.wf) (hb := Nat.lt_wfRel.wf))

theorem stableMatrixLt_wf {sig : Signature} (w : MatrixInterpretation sig) :
    WellFounded (stableMatrixLt (sig := sig) w) := by
  apply Subrelation.wf
  · intro a b h
    have h' := h Term.idSubst
    simpa [stableMatrixLt, Term.subst_id] using h'
  · exact InvImage.wf (matrixWeight w) vec2Lt_wf

theorem stableMatrixLt_trans {sig : Signature} (w : MatrixInterpretation sig) :
    Transitive (stableMatrixLt (sig := sig) w) := by
  intro a b c hab hbc sub
  exact Prod.Lex.trans (hab sub) (hbc sub)

theorem stableMatrixLt_subst {sig : Signature} (w : MatrixInterpretation sig)
    {sub : Subst sig} {s t : Term sig} :
    stableMatrixLt (sig := sig) w s t →
      stableMatrixLt (sig := sig) w (Term.subst sub s) (Term.subst sub t) := by
  intro h sub'
  have := h (Term.compSubst sub' sub)
  simpa [Term.subst_comp] using this

theorem stableMatrixLt_replace {sig : Signature} (w : MatrixInterpretation sig)
    {t : Term sig} {p : Pos} {u v t' t'' : Term sig}
    (h : stableMatrixLt (sig := sig) w u v)
    (hrep1 : Term.replace t p u = some t')
    (hrep2 : Term.replace t p v = some t'') :
    stableMatrixLt (sig := sig) w t' t'' := by
  intro sub
  have hrep1' := Term.replace_subst (sub := sub) (t := t) (p := p) (u := u) (t' := t') hrep1
  have hrep2' := Term.replace_subst (sub := sub) (t := t) (p := p) (u := v) (t' := t'') hrep2
  have hsize : vec2Lt (matrixWeight w (Term.subst sub u))
      (matrixWeight w (Term.subst sub v)) := h sub
  simpa using matrixWeight_replace_lt (w := w) (t := Term.subst sub t)
    (p := p) (u := Term.subst sub u) (v := Term.subst sub v)
    (t' := Term.subst sub t') (t'' := Term.subst sub t'') hrep1' hrep2' hsize

def matrixOrdering (sig : Signature) (w : MatrixInterpretation sig) : ReductionOrdering sig :=
  { lt := stableMatrixLt w
    wf := stableMatrixLt_wf w
    trans := stableMatrixLt_trans w
    subst_closed := stableMatrixLt_subst w
    replace_closed := by
      intro t p u v t' t'' h hrep1 hrep2
      exact stableMatrixLt_replace (w := w) (t := t) (p := p) (u := u) (v := v)
        (t' := t') (t'' := t'') h hrep1 hrep2 }

theorem terminating_of_matrix {sig : Signature} {rules : RuleSet sig} (w : MatrixInterpretation sig)
    (hord : ∀ r, rules r → stableMatrixLt (sig := sig) w r.rhs r.lhs) :
    Terminating rules :=
  terminating_of_ordering (ord := matrixOrdering sig w) hord

/-! ## LPO Ordering -/

/-- LPO ordering packaged as a reduction ordering (via transitive closure). -/
def lpoOrdering (sig : Signature) (prec : Precedence sig) : ReductionOrdering sig :=
  { lt := StableLPOplus prec
    wf := stableLPOplus_wf prec
    trans := stableLPOplus_trans prec
    subst_closed := stableLPOplus_subst prec
    replace_closed := by
      intro t p u v t' t'' h hrep1 hrep2
      exact stableLPOplus_replace prec h hrep1 hrep2 }

/-- Termination from an LPO ordering. -/
theorem terminating_of_lpo {sig : Signature} {rules : RuleSet sig} (prec : Precedence sig)
    (hord : ∀ r, rules r → StableLPOplus prec r.rhs r.lhs) :
    Terminating rules :=
  terminating_of_ordering (ord := lpoOrdering sig prec) hord

theorem terminating_of_lpo_single {sig : Signature} {rules : RuleSet sig} (prec : Precedence sig)
    (hord : ∀ r, rules r → LPO prec r.rhs r.lhs) :
    Terminating rules := by
  apply terminating_of_lpo (prec := prec)
  intro r hr
  exact StableLPOplus.single (stableLPO_of_lpo prec (hord r hr))

end Metatheory.TRS.FirstOrder

-/

end Metatheory.TRS.FirstOrder
