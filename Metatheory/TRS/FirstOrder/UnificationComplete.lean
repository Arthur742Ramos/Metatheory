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
      have : x = y := hocc
      subst this
      rfl
  | app f args ih =>
      rcases hocc with ⟨i, hocci⟩
      have hle := ih i hocci
      have hge := Term.finSum_ge (fun j => Term.size (Term.subst sub (args j))) i
      simp only [Term.subst, Term.size]
      omega

/-- If x occurs in t and t is not just x, then no substitution can make x = t. -/
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

/-! ## Unification under Substitution -/

theorem unifiesList_substEquations {sig : Signature} {sub : Subst sig} {eqs : Equations sig} :
    UnifiesList sub eqs → UnifiesList Term.idSubst (substEquations sub eqs) := by
  intro h e he
  rcases List.mem_map.1 he with ⟨e0, he0, rfl⟩
  have hEq := h e0 he0
  simpa [substEquation, Term.idSubst, Term.subst] using hEq

theorem unifiesList_substEquations_iff {sig : Signature} {sub : Subst sig} {eqs : Equations sig} :
    UnifiesList sub eqs ↔ UnifiesList Term.idSubst (substEquations sub eqs) := by
  constructor
  · exact unifiesList_substEquations (sub := sub) (eqs := eqs)
  · intro h e he
    have hmem : substEquation sub e ∈ substEquations sub eqs :=
      List.mem_map_of_mem (f := substEquation sub) he
    have hEq := h (substEquation sub e) hmem
    simpa [substEquation, Term.idSubst, Term.subst] using hEq

theorem unifiesList_substEquations_cons {sig : Signature} {sub : Subst sig}
    {s t : Term sig} {eqs : Equations sig} :
    UnifiesList sub ((s, t) :: eqs) ↔
      Term.subst sub s = Term.subst sub t ∧
      UnifiesList Term.idSubst (substEquations sub eqs) := by
  constructor
  · intro h
    have hcons := (unifiesList_cons (sub := sub) (e := (s, t)) (eqs := eqs)).1 h
    exact ⟨hcons.1, unifiesList_substEquations (sub := sub) (eqs := eqs) hcons.2⟩
  · intro h
    rcases h with ⟨hhead, htail⟩
    have htail' : UnifiesList sub eqs := by
      exact (unifiesList_substEquations_iff (sub := sub) (eqs := eqs)).1 htail
    exact (unifiesList_cons (sub := sub) (e := (s, t)) (eqs := eqs)).2 ⟨hhead, htail'⟩

theorem unifiesList_substEquations_cons_iff {sig : Signature} {sub : Subst sig}
    {s t : Term sig} {eqs : Equations sig} :
    UnifiesList Term.idSubst (substEquations sub ((s, t) :: eqs)) ↔
      Term.subst sub s = Term.subst sub t ∧
      UnifiesList Term.idSubst (substEquations sub eqs) := by
  simp [substEquations, substEquation, unifiesList_cons, Term.idSubst, Term.subst]

/-! ## Unification Completeness -/

theorem unify_complete {sig : Signature} [DecidableEq sig.Sym] {eqs : Equations sig} :
    unify (sig := sig) eqs = none → ¬ Unifiable eqs := by
  intro hnone hunifiable
  rcases hunifiable with ⟨sub, hsub⟩
  -- Show there exists some fuel where unifyFuel succeeds, then contradict hnone.
  have hsucc : ∃ fuel, unifyFuel (sig := sig) fuel eqs = some sub := by
    -- Use strong recursion on equationsSize; build a fuel bound.
    classical
    revert eqs sub hsub
    refine Nat.strongRecOn ?n ?_ ?_ ?_
    · exact equationsSize eqs
    · intro n ih eqs sub hsub
      cases eqs with
      | nil =>
          refine ⟨1, ?_⟩
          simp [unifyFuel]
      | cons e eqs =>
          cases e with
          | mk s t =>
              cases s with
              | var x =>
                  cases t with
                  | var y =>
                      by_cases hxy : x = y
                      ·
                        have htail : UnifiesList sub eqs := by
                          have hcons := (unifiesList_cons (sub := sub)
                            (e := (Term.var x, Term.var y)) (eqs := eqs)).1 hsub
                          exact hcons.2
                        have hsize : equationsSize eqs < equationsSize ((Term.var x, Term.var y) :: eqs) := by
                          simp [equationsSize_cons, equationSize]
                        rcases ih (equationsSize eqs) hsize eqs sub htail with ⟨fuel, hfuel⟩
                        refine ⟨fuel + 1, ?_⟩
                        simp [unifyFuel, hxy, hfuel]
                      ·
                        let sub0 : Subst sig := updateSubst Term.idSubst x (Term.var y)
                        have hcons := (unifiesList_cons (sub := sub)
                          (e := (Term.var x, Term.var y)) (eqs := eqs)).1 hsub
                        have hxy' : sub x = sub y := by
                          simpa [Term.subst] using hcons.1
                        have hcomp : Term.compSubst sub sub0 = sub := by
                          apply compSubst_update_of_eq (sub := sub) (x := x) (t := Term.var y)
                          simpa [Term.subst] using hxy'
                        have htail : UnifiesList sub (substEquations sub0 eqs) := by
                          exact unifiesList_substEquations_of_compSubst_eq
                            (sub := sub) (tau := sub0) hcomp hcons.2
                        have hsize : equationsSize (substEquations sub0 eqs) < equationsSize ((Term.var x, Term.var y) :: eqs) := by
                          simp [equationsSize_cons, equationSize]
                        rcases ih (equationsSize (substEquations sub0 eqs)) hsize (substEquations sub0 eqs) sub htail
                          with ⟨fuel, hfuel⟩
                        refine ⟨fuel + 1, ?_⟩
                        simp [unifyFuel, hxy, sub0, hfuel]
                  | app f args =>
                      by_cases hocc : Occurs (sig := sig) x (Term.app f args)
                      ·
                        have hcons := (unifiesList_cons (sub := sub)
                          (e := (Term.var x, Term.app f args)) (eqs := eqs)).1 hsub
                        have hne : Term.app f args ≠ Term.var x := by
                          intro hEq
                          cases hEq
                        have hcontra :=
                          no_unifier_occurs (sig := sig) (x := x) (t := Term.app f args) hocc hne sub
                        exact (hcontra (by simpa [Term.subst] using hcons.1)).elim
                      ·
                        let sub0 : Subst sig := updateSubst Term.idSubst x (Term.app f args)
                        have hcons := (unifiesList_cons (sub := sub)
                          (e := (Term.var x, Term.app f args)) (eqs := eqs)).1 hsub
                        have hxt : sub x = Term.subst sub (Term.app f args) := by
                          simpa [Term.subst] using hcons.1
                        have hcomp : Term.compSubst sub sub0 = sub := by
                          apply compSubst_update_of_eq (sub := sub) (x := x)
                            (t := Term.app f args)
                          simpa [Term.subst] using hxt
                        have htail : UnifiesList sub (substEquations sub0 eqs) := by
                          exact unifiesList_substEquations_of_compSubst_eq
                            (sub := sub) (tau := sub0) hcomp hcons.2
                        have hsize : equationsSize (substEquations sub0 eqs) < equationsSize ((Term.var x, Term.app f args) :: eqs) := by
                          simp [equationsSize_cons, equationSize]
                        rcases ih (equationsSize (substEquations sub0 eqs)) hsize (substEquations sub0 eqs) sub htail
                          with ⟨fuel, hfuel⟩
                        refine ⟨fuel + 1, ?_⟩
                        simp [unifyFuel, hocc, sub0, hfuel]
              | app f args =>
                  cases t with
                  | var x =>
                      by_cases hocc : Occurs (sig := sig) x (Term.app f args)
                      ·
                        have hcons := (unifiesList_cons (sub := sub)
                          (e := (Term.app f args, Term.var x)) (eqs := eqs)).1 hsub
                        have hne : Term.app f args ≠ Term.var x := by
                          intro hEq
                          cases hEq
                        have hcontra :=
                          no_unifier_occurs (sig := sig) (x := x) (t := Term.app f args) hocc hne sub
                        exact (hcontra (by simpa [Term.subst] using hcons.1.symm)).elim
                      ·
                        let sub0 : Subst sig := updateSubst Term.idSubst x (Term.app f args)
                        have hcons := (unifiesList_cons (sub := sub)
                          (e := (Term.app f args, Term.var x)) (eqs := eqs)).1 hsub
                        have hxt : Term.subst sub (Term.app f args) = sub x := by
                          simpa [Term.subst] using hcons.1
                        have hcomp : Term.compSubst sub sub0 = sub := by
                          apply compSubst_update_of_eq (sub := sub) (x := x)
                            (t := Term.app f args)
                          simpa [Term.subst] using hxt.symm
                        have htail : UnifiesList sub (substEquations sub0 eqs) := by
                          exact unifiesList_substEquations_of_compSubst_eq
                            (sub := sub) (tau := sub0) hcomp hcons.2
                        have hsize : equationsSize (substEquations sub0 eqs) < equationsSize ((Term.app f args, Term.var x) :: eqs) := by
                          simp [equationsSize_cons, equationSize]
                        rcases ih (equationsSize (substEquations sub0 eqs)) hsize (substEquations sub0 eqs) sub htail
                          with ⟨fuel, hfuel⟩
                        refine ⟨fuel + 1, ?_⟩
                        simp [unifyFuel, hocc, sub0, hfuel]
                  | app g args' =>
                      by_cases hfg : f = g
                      ·
                        cases hfg
                        have hcons := (unifiesList_cons (sub := sub)
                          (e := (Term.app f args, Term.app f args')) (eqs := eqs)).1 hsub
                        have hargs : UnifiesList sub (equationsOfArgs args args') := by
                          have hEq : Term.subst sub (Term.app f args) =
                              Term.subst sub (Term.app f args') := hcons.1
                          -- recover argument equalities
                          intro i
                          have : Term.subst sub (args i) = Term.subst sub (args' i) := by
                            simpa [Term.subst, Term.app.injEq] using hEq
                          exact this
                        have htail : UnifiesList sub (equationsOfArgs args args' ++ eqs) := by
                          exact (unifiesList_append (sub := sub)
                            (eqs₁ := equationsOfArgs args args') (eqs₂ := eqs)).2 ⟨hargs, hcons.2⟩
                        have hsize : equationsSize (equationsOfArgs args args' ++ eqs) <
                            equationsSize ((Term.app f args, Term.app f args') :: eqs) := by
                          simp [equationsSize_cons, equationSize, equationsSize_append]
                        rcases ih (equationsSize (equationsOfArgs args args' ++ eqs)) hsize
                          (equationsOfArgs args args' ++ eqs) sub htail with ⟨fuel, hfuel⟩
                        refine ⟨fuel + 1, ?_⟩
                        simp [unifyFuel, hfuel]
                      ·
                        have hcons := (unifiesList_cons (sub := sub)
                          (e := (Term.app f args, Term.app g args')) (eqs := eqs)).1 hsub
                        have hcontra := no_unifier_clash (sig := sig) (f := f) (g := g) hfg
                        exact (hcontra sub hcons.1).elim
    exact ⟨n, by
      -- base case already handled; unreachable
      cases n⟩
  rcases hsucc with ⟨fuel, hfuel⟩
  have : unify (sig := sig) eqs = some sub := by
    -- unify chooses some successful fuel, so it cannot be none
    classical
    unfold unify
    by_cases hex : ∃ fuel sub, unifyFuel (sig := sig) fuel eqs = some sub
    ·
      let fuel' : Nat := Classical.choose hex
      have hsub' : ∃ sub, unifyFuel (sig := sig) fuel' eqs = some sub := Classical.choose_spec hex
      let sub' : Subst sig := Classical.choose hsub'
      have hsub'' : unifyFuel (sig := sig) fuel' eqs = some sub' := Classical.choose_spec hsub'
      exact by
        simpa [hex, fuel', hsub', sub'] using (rfl : some sub' = some sub')
    ·
      exact (hex ⟨fuel, sub, hfuel⟩).elim
  cases hnone

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
  rcases List.mem_map.1 he with ⟨e0, he0, rfl⟩
  have hEq := h e0 he0
  have hcomp' : Term.subst sub (Term.subst tau e0.1) =
      Term.subst sub (Term.subst tau e0.2) := by
    simpa [Term.subst_comp, hcomp] using hEq
  simpa [substEquation] using hcomp'

theorem compSubst_assoc {sig : Signature} (sub tau theta : Subst sig) :
    Term.compSubst sub (Term.compSubst tau theta) =
      Term.compSubst (Term.compSubst sub tau) theta := by
  funext x
  simp [Term.compSubst, Term.subst_comp]

/-! ## MGU for Successful Unification -/

theorem unifyFuel_mgu {sig : Signature} [DecidableEq sig.Sym] :
    ∀ {fuel eqs sub},
      unifyFuel (sig := sig) fuel eqs = some sub →
      IsMGU sub eqs := by
  intro fuel eqs sub h
  induction fuel generalizing eqs sub with
  | zero =>
      cases h
  | succ fuel ih =>
      cases eqs with
      | nil =>
          cases h
          refine ⟨?_, ?_⟩
          · exact unifiesList_nil _
          · intro tau _htau
            refine ⟨tau, ?_⟩
            simpa [compSubst_id_right] using (rfl : tau = tau)
      | cons e eqs =>
          cases e with
          | mk s t =>
              cases s with
              | var x =>
                  cases t with
                  | var y =>
                      by_cases hxy : x = y
                      ·
                        have h' : unifyFuel fuel eqs = some sub := by
                          simpa [unifyFuel, hxy] using h
                        have ih' := ih (eqs := eqs) (sub := sub) h'
                        refine ⟨?_, ?_⟩
                        · exact unifyFuel_sound h
                        ·
                          intro tau htau
                          have htau' : UnifiesList tau eqs := by
                            have hcons := (unifiesList_cons (sub := tau) (e := (Term.var x, Term.var y)) (eqs := eqs)).1 htau
                            exact hcons.2
                          rcases ih'.2 tau htau' with ⟨theta, htheta⟩
                          exact ⟨theta, htheta⟩
                      ·
                        let sub0 : Subst sig := updateSubst Term.idSubst x (Term.var y)
                        cases hres : unifyFuel fuel (substEquations sub0 eqs) with
                        | none =>
                            simp [unifyFuel, hxy, sub0, hres] at h
                        | some theta =>
                            simp [unifyFuel, hxy, sub0, hres] at h
                            subst h
                            have ih' := ih (eqs := substEquations sub0 eqs) (sub := theta) hres
                            refine ⟨?_, ?_⟩
                            · exact unifyFuel_sound (sub := Term.compSubst theta sub0) (fuel := fuel) (eqs := (Term.var x, Term.var y) :: eqs) (by
                                simp [unifyFuel, hxy, sub0, hres])
                            ·
                              intro tau htau
                              have hhead := (unifiesList_cons (sub := tau) (e := (Term.var x, Term.var y)) (eqs := eqs)).1 htau
                              have hxy' : tau x = tau y := by
                                simpa using hhead.1
                              have hcomp : Term.compSubst tau sub0 = tau := by
                                apply compSubst_update_of_eq (sub := tau) (x := x) (t := Term.var y)
                                simpa [Term.subst] using hxy'
                              have htau' : UnifiesList tau (substEquations sub0 eqs) := by
                                exact unifiesList_substEquations_of_compSubst_eq (sub := tau) (tau := sub0) hcomp hhead.2
                              rcases ih'.2 tau htau' with ⟨theta', htheta'⟩
                              refine ⟨theta', ?_⟩
                              calc
                                tau = Term.compSubst theta' theta := htheta'
                                _ = Term.compSubst theta' (Term.compSubst theta sub0) := by
                                      rfl
                                _ = Term.compSubst (Term.compSubst theta' theta) sub0 := by
                                      symm
                                      exact compSubst_assoc _ _ _
                                _ = Term.compSubst theta' (Term.compSubst theta sub0) := by rfl
                  | app f args =>
                      by_cases hocc : Occurs (sig := sig) x (Term.app f args)
                      ·
                        simp [unifyFuel, hocc] at h
                      ·
                        let sub0 : Subst sig := updateSubst Term.idSubst x (Term.app f args)
                        cases hres : unifyFuel fuel (substEquations sub0 eqs) with
                        | none =>
                            simp [unifyFuel, hocc, sub0, hres] at h
                        | some theta =>
                            simp [unifyFuel, hocc, sub0, hres] at h
                            subst h
                            have ih' := ih (eqs := substEquations sub0 eqs) (sub := theta) hres
                            refine ⟨?_, ?_⟩
                            · exact unifyFuel_sound (sub := Term.compSubst theta sub0) (fuel := fuel) (eqs := (Term.var x, Term.app f args) :: eqs) (by
                                simp [unifyFuel, hocc, sub0, hres])
                            ·
                              intro tau htau
                              have hhead := (unifiesList_cons (sub := tau) (e := (Term.var x, Term.app f args)) (eqs := eqs)).1 htau
                              have hxt : tau x = Term.subst tau (Term.app f args) := by
                                simpa [Term.subst] using hhead.1
                              have hcomp : Term.compSubst tau sub0 = tau := by
                                apply compSubst_update_of_eq (sub := tau) (x := x) (t := Term.app f args)
                                simpa [Term.subst] using hxt
                              have htau' : UnifiesList tau (substEquations sub0 eqs) := by
                                exact unifiesList_substEquations_of_compSubst_eq (sub := tau) (tau := sub0) hcomp hhead.2
                              rcases ih'.2 tau htau' with ⟨theta', htheta'⟩
                              refine ⟨theta', ?_⟩
                              calc
                                tau = Term.compSubst theta' theta := htheta'
                                _ = Term.compSubst theta' (Term.compSubst theta sub0) := by rfl
                                _ = Term.compSubst (Term.compSubst theta' theta) sub0 := by
                                      symm
                                      exact compSubst_assoc _ _ _
                                _ = Term.compSubst theta' (Term.compSubst theta sub0) := by rfl
              | app f args =>
                  cases t with
                  | var x =>
                      by_cases hocc : Occurs (sig := sig) x (Term.app f args)
                      ·
                        simp [unifyFuel, hocc] at h
                      ·
                        let sub0 : Subst sig := updateSubst Term.idSubst x (Term.app f args)
                        cases hres : unifyFuel fuel (substEquations sub0 eqs) with
                        | none =>
                            simp [unifyFuel, hocc, sub0, hres] at h
                        | some theta =>
                            simp [unifyFuel, hocc, sub0, hres] at h
                            subst h
                            have ih' := ih (eqs := substEquations sub0 eqs) (sub := theta) hres
                            refine ⟨?_, ?_⟩
                            · exact unifyFuel_sound (sub := Term.compSubst theta sub0) (fuel := fuel) (eqs := (Term.app f args, Term.var x) :: eqs) (by
                                simp [unifyFuel, hocc, sub0, hres])
                            ·
                              intro tau htau
                              have hhead := (unifiesList_cons (sub := tau) (e := (Term.app f args, Term.var x)) (eqs := eqs)).1 htau
                              have hxt : Term.subst tau (Term.app f args) = tau x := by
                                simpa [Term.subst] using hhead.1
                              have hcomp : Term.compSubst tau sub0 = tau := by
                                apply compSubst_update_of_eq (sub := tau) (x := x) (t := Term.app f args)
                                simpa [Term.subst] using hxt.symm
                              have htau' : UnifiesList tau (substEquations sub0 eqs) := by
                                exact unifiesList_substEquations_of_compSubst_eq (sub := tau) (tau := sub0) hcomp hhead.2
                              rcases ih'.2 tau htau' with ⟨theta', htheta'⟩
                              refine ⟨theta', ?_⟩
                              calc
                                tau = Term.compSubst theta' theta := htheta'
                                _ = Term.compSubst theta' (Term.compSubst theta sub0) := by rfl
                                _ = Term.compSubst (Term.compSubst theta' theta) sub0 := by
                                      symm
                                      exact compSubst_assoc _ _ _
                                _ = Term.compSubst theta' (Term.compSubst theta sub0) := by rfl
                  | app g args' =>
                      by_cases hfg : f = g
                      ·
                        cases hfg
                        have h' : unifyFuel fuel (equationsOfArgs args args' ++ eqs) = some sub := by
                          simpa [unifyFuel] using h
                        have ih' := ih (eqs := equationsOfArgs args args' ++ eqs) (sub := sub) h'
                        refine ⟨?_, ?_⟩
                        · exact unifyFuel_sound h
                        ·
                          intro tau htau
                          have hsplit :=
                            (unifiesList_append (sub := tau)
                              (eqs₁ := equationsOfArgs args args') (eqs₂ := eqs)).1
                              ((unifiesList_cons (sub := tau)
                                  (e := (Term.app f args, Term.app f args')) (eqs := eqs)).1 htau).2
                          rcases hsplit with ⟨hargs, htail⟩
                          rcases ih'.2 tau (by
                            exact (unifiesList_append (sub := tau)
                              (eqs₁ := equationsOfArgs args args') (eqs₂ := eqs)).2 ⟨hargs, htail⟩) with ⟨theta, htheta⟩
                          exact ⟨theta, htheta⟩
                      ·
                        simp [unifyFuel, hfg] at h

theorem unify_mgu {sig : Signature} [DecidableEq sig.Sym] {eqs : Equations sig} {sub : Subst sig} :
    unify (sig := sig) eqs = some sub → IsMGU sub eqs := by
  classical
  intro h
  unfold unify at h
  by_cases hex : ∃ fuel sub, unifyFuel (sig := sig) fuel eqs = some sub
  ·
    let fuel : Nat := Classical.choose hex
    have hsub : ∃ sub, unifyFuel (sig := sig) fuel eqs = some sub := Classical.choose_spec hex
    let sub' : Subst sig := Classical.choose hsub
    have hsub' : unifyFuel (sig := sig) fuel eqs = some sub' := Classical.choose_spec hsub
    have hEq : sub' = sub := by
      simpa [hex, fuel, hsub, sub'] using h
    subst hEq
    exact unifyFuel_mgu (sub := sub') hsub'
  ·
    simp [hex] at h

end Metatheory.TRS.FirstOrder
