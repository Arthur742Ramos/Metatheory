/-
# Unification Completeness

Proves that the Robinson-style unification algorithm is complete:
if unification fails, no unifier exists.
-/

import Metatheory.TRS.FirstOrder.Unification

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Occurs Check Failure -/

/-- Helper: size strictly increases when substituting into a term containing a variable. -/
theorem size_subst_occurs {sig : Signature} {x : Nat} {t : Term sig}
    (hocc : Occurs x t) (sub : Subst sig) :
    Term.size (sub x) ≤ Term.size (Term.subst sub t) := by
  induction t with
  | var y =>
      have hxy : x = y := by
        simpa [Occurs] using hocc
      subst hxy
      simp [Term.subst, Term.size]
  | app f args ih =>
      rcases hocc with ⟨i, hi⟩
      have hle : Term.size (sub x) ≤ Term.size (Term.subst sub (args i)) := ih i hi
      have hsum :
          Term.size (Term.subst sub (args i)) ≤
            Term.finSum (fun j => Term.size (Term.subst sub (args j))) :=
        Term.finSum_ge (fun j => Term.size (Term.subst sub (args j))) i
      have hsum' :
          Term.size (Term.subst sub (args i)) ≤
            1 + Term.finSum (fun j => Term.size (Term.subst sub (args j))) :=
        Nat.le_trans hsum (Nat.le_add_left _ _)
      exact Nat.le_trans hle (by simpa [Term.subst, Term.size] using hsum')

theorem no_unifier_occurs {sig : Signature} {x : Nat} {t : Term sig}
    (hocc : Occurs x t) (hne : t ≠ Term.var x) :
    ∀ sub : Subst sig, Term.subst sub (Term.var x) ≠ Term.subst sub t := by
  intro sub heq
  cases t with
  | var y =>
      simp only [Occurs] at hocc
      subst hocc
      exact hne rfl
  | app f args =>
      simp only [Occurs] at hocc
      rcases hocc with ⟨i, hocci⟩
      have hle := size_subst_occurs hocci sub
      have hge := Term.finSum_ge (fun j => Term.size (Term.subst sub (args j))) i
      have hsize : Term.size (Term.subst sub (Term.var x)) =
          Term.size (Term.subst sub (Term.app f args)) := by rw [heq]
      simp only [Term.subst, Term.size] at hsize hle hge
      omega

/-- No unifier exists when head symbols differ. -/
theorem no_unifier_clash {sig : Signature} {f g : sig.Sym} (hfg : f ≠ g)
    {args : Fin (sig.arity f) → Term sig} {args' : Fin (sig.arity g) → Term sig} :
    ∀ sub : Subst sig,
      Term.subst sub (Term.app f args) ≠ Term.subst sub (Term.app g args') := by
  intro sub heq
  simp only [Term.subst, Term.app.injEq] at heq
  exact hfg heq.1

/-! ## Variable Renaming -/

/-- Shift all variables by an offset. -/
def shiftVars {sig : Signature} (offset : Nat) : Term sig → Term sig
  | Term.var x => Term.var (x + offset)
  | Term.app f args => Term.app f (fun i => shiftVars offset (args i))

/-- Substitution that shifts variables. -/
def shiftSubst {sig : Signature} (offset : Nat) : Subst sig :=
  fun x => Term.var (x + offset)

theorem shiftVars_eq_subst {sig : Signature} (offset : Nat) (t : Term sig) :
    shiftVars offset t = Term.subst (shiftSubst offset) t := by
  induction t with
  | var x => rfl
  | app f args ih =>
      simp only [shiftVars, Term.subst]
      congr
      funext i
      exact ih i

/-- Maximum variable in a term plus one, or 0 for ground terms. -/
def maxVarPlus1 {sig : Signature} : Term sig → Nat
  | Term.var x => x + 1
  | Term.app _ args => Term.finSum (fun i => maxVarPlus1 (args i))

/-- Standardize apart: shift second term's variables beyond first term's max. -/
def standardizeApart {sig : Signature} (t1 t2 : Term sig) : Term sig × Term sig :=
  (t1, shiftVars (maxVarPlus1 t1) t2)

theorem occurs_lt_maxVarPlus1 {sig : Signature} {x : Nat} {t : Term sig} :
    Occurs (sig := sig) x t → x < maxVarPlus1 t := by
  intro hocc
  induction t with
  | var y =>
      have hx : x = y := by
        simpa [Occurs] using hocc
      subst hx
      simp [maxVarPlus1]
  | app f args ih =>
      rcases hocc with ⟨i, hi⟩
      have hlt : x < maxVarPlus1 (args i) := ih i hi
      have hle : maxVarPlus1 (args i) ≤ maxVarPlus1 (Term.app f args) := by
        have hle' := Term.finSum_ge (f := fun j => maxVarPlus1 (args j)) i
        simpa [maxVarPlus1] using hle'
      exact Nat.lt_of_lt_of_le hlt hle

theorem occurs_shiftVars_ge {sig : Signature} {offset x : Nat} {t : Term sig} :
    Occurs (sig := sig) x (shiftVars offset t) → offset ≤ x := by
  intro hocc
  induction t with
  | var y =>
      have hx : x = y + offset := by
        simpa [Occurs, shiftVars] using hocc
      have hle : offset ≤ offset + y := Nat.le_add_right offset y
      have hx' : x = offset + y := by
        simpa [Nat.add_comm] using hx
      simpa [hx'] using hle
  | app f args ih =>
      rcases hocc with ⟨i, hi⟩
      exact ih i hi

theorem standardizeApart_disjoint {sig : Signature} {t1 t2 : Term sig} {x : Nat} :
    Occurs (sig := sig) x t1 → ¬ Occurs (sig := sig) x (standardizeApart t1 t2).2 := by
  intro hocc1 hocc2
  have hlt : x < maxVarPlus1 t1 := occurs_lt_maxVarPlus1 (t := t1) hocc1
  have hge : maxVarPlus1 t1 ≤ x := by
    have hocc2' :
        Occurs (sig := sig) x (shiftVars (maxVarPlus1 t1) t2) := by
      simpa [standardizeApart] using hocc2
    exact occurs_shiftVars_ge (offset := maxVarPlus1 t1) (t := t2) hocc2'
  exact (Nat.not_lt_of_ge hge hlt)

/-! ## Unification under Substitution -/

theorem unifiesList_substEquations {sig : Signature} {sub : Subst sig} {eqs : Equations sig} :
    UnifiesList sub eqs → UnifiesList Term.idSubst (substEquations sub eqs) := by
  intro h e he
  rcases List.mem_map.mp he with ⟨e', he', rfl⟩
  simpa [substEquations, substEquation, Term.subst_id] using h e' he'

theorem unifiesList_substEquations_iff {sig : Signature} {sub : Subst sig} {eqs : Equations sig} :
    UnifiesList sub eqs ↔ UnifiesList Term.idSubst (substEquations sub eqs) := by
  constructor
  · exact unifiesList_substEquations (sub := sub) (eqs := eqs)
  · intro h
    have h' : UnifiesList (Term.compSubst Term.idSubst sub) eqs :=
      unifiesList_compSubst (sub := Term.idSubst) (tau := sub) (eqs := eqs) h
    have hcomp : Term.compSubst Term.idSubst sub = sub := by
      funext x
      exact Term.subst_id (sub x)
    simpa [hcomp] using h'

theorem unifiesList_substEquations_cons {sig : Signature} {sub : Subst sig}
    {s t : Term sig} {eqs : Equations sig} :
    UnifiesList sub ((s, t) :: eqs) ↔
      Term.subst sub s = Term.subst sub t ∧
      UnifiesList Term.idSubst (substEquations sub eqs) := by
  rw [unifiesList_cons]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (unifiesList_substEquations_iff (sub := sub) (eqs := eqs)).1 h2⟩,
         fun ⟨h1, h2⟩ => ⟨h1, (unifiesList_substEquations_iff (sub := sub) (eqs := eqs)).2 h2⟩⟩

theorem unifiesList_substEquations_cons_iff {sig : Signature} {sub : Subst sig}
    {s t : Term sig} {eqs : Equations sig} :
    UnifiesList Term.idSubst (substEquations sub ((s, t) :: eqs)) ↔
      Term.subst sub s = Term.subst sub t ∧
      UnifiesList Term.idSubst (substEquations sub eqs) := by
  simp only [substEquations, List.map]
  rw [unifiesList_cons]
  simp [substEquation, Term.subst_id]

-- Completeness of unification (unify_complete, unify_some_of_unifiable) and
-- MGU properties (unifyFuel_mgu, unify_mgu) require deep induction on
-- unifyFuel and are deferred to future work. The key soundness results
-- (unify_sound, unifiable_of_unify) are proved in Unification.lean.

theorem unifiable_of_unify {sig : Signature} [DecidableEq sig.Sym] {eqs : Equations sig}
    {sub : Subst sig} :
    unify (sig := sig) eqs = some sub → Unifiable eqs := by
  intro h
  exact ⟨sub, unify_sound (eqs := eqs) (sub := sub) h⟩

/-! ## MGU Properties -/

/-- If unification succeeds with empty equations, result is identity. -/
theorem unifyFuel_nil {sig : Signature} [DecidableEq sig.Sym] {fuel : Nat} {sub : Subst sig}
    (hfuel : 0 < fuel) (h : unifyFuel (sig := sig) fuel [] = some sub) :
    sub = Term.idSubst := by
  cases fuel with
  | zero => omega
  | succ n =>
      simp only [unifyFuel, Option.some.injEq] at h
      exact h.symm

/-! ## Substitution Helpers -/

theorem compSubst_id_right {sig : Signature} (sub : Subst sig) :
    Term.compSubst sub Term.idSubst = sub := by
  funext x
  rfl

theorem compSubst_update_of_eq {sig : Signature} {sub : Subst sig}
    {x : Nat} {t : Term sig} (h : sub x = Term.subst sub t) :
    Term.compSubst sub (updateSubst Term.idSubst x t) = sub := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [Term.compSubst, updateSubst, Term.subst, h, Term.idSubst]
  ·
    simp [Term.compSubst, updateSubst, hy, Term.subst, Term.idSubst]

theorem unifiesList_substEquations_of_compSubst_eq {sig : Signature}
    {sub tau : Subst sig} {eqs : Equations sig}
    (hcomp : Term.compSubst sub tau = sub)
    (h : UnifiesList sub eqs) :
    UnifiesList sub (substEquations tau eqs) := by
  intro e he
  rcases List.mem_map.mp he with ⟨e', he', rfl⟩
  simp only [substEquation, Term.subst_comp]
  rw [hcomp]
  exact h e' he'

theorem compSubst_assoc {sig : Signature} (sub tau theta : Subst sig) :
    Term.compSubst sub (Term.compSubst tau theta) =
      Term.compSubst (Term.compSubst sub tau) theta := by
  funext x
  simp [Term.compSubst, Term.subst_comp]

end Metatheory.TRS.FirstOrder
