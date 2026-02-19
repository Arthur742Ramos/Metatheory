/-
# Unification Basics for First-Order Terms

Defines unifiers, most general unifiers, and basic occurs/check utilities.
-/

import Metatheory.TRS.FirstOrder.Syntax

namespace Metatheory.TRS.FirstOrder

open Term

/-- An equation between terms. -/
abbrev Equation (sig : Signature) := Term sig × Term sig

/-- A list of equations. -/
abbrev Equations (sig : Signature) := List (Equation sig)

/-- A substitution unifies a list of equations. -/
def UnifiesList {sig : Signature} (sub : Subst sig) (eqs : Equations sig) : Prop :=
  ∀ e ∈ eqs, Term.subst sub e.1 = Term.subst sub e.2

/-- A list of equations is unifiable if it has a unifier. -/
def Unifiable {sig : Signature} (eqs : Equations sig) : Prop :=
  ∃ sub, UnifiesList sub eqs

/-- Most general unifier: any unifier factors through it by composition. -/
def IsMGU {sig : Signature} (sub : Subst sig) (eqs : Equations sig) : Prop :=
  UnifiesList sub eqs ∧
  ∀ tau, UnifiesList tau eqs -> ∃ theta, tau = Term.compSubst theta sub

/-- Occurs check: variable occurs in term. -/
def Occurs {sig : Signature} (x : Nat) : Term sig -> Prop
  | Term.var y => x = y
  | Term.app _ args => ∃ i, Occurs x (args i)

theorem occurs_var {sig : Signature} (x y : Nat) :
    Occurs (sig := sig) x (Term.var y) ↔ x = y := by
  rfl

theorem occurs_app {sig : Signature} (x : Nat) (f : sig.Sym)
    (args : Fin (sig.arity f) -> Term sig) :
    Occurs (sig := sig) x (Term.app f args) ↔ ∃ i, Occurs x (args i) := by
  rfl

/-- Update a substitution at a single variable. -/
def updateSubst {sig : Signature} (sub : Subst sig) (x : Nat) (t : Term sig) : Subst sig :=
  fun y => if y = x then t else sub y

@[simp] theorem updateSubst_same {sig : Signature} (sub : Subst sig) (x : Nat) (t : Term sig) :
    updateSubst sub x t x = t := by
  simp [updateSubst]

@[simp] theorem updateSubst_ne {sig : Signature} (sub : Subst sig) {x y : Nat} (t : Term sig)
    (h : y ≠ x) : updateSubst sub x t y = sub y := by
  simp [updateSubst, h]

/-! ## Equation Utilities -/

/-- Apply a substitution to one equation. -/
def substEquation {sig : Signature} (sub : Subst sig) (e : Equation sig) : Equation sig :=
  (Term.subst sub e.1, Term.subst sub e.2)

/-- Apply a substitution to a list of equations. -/
def substEquations {sig : Signature} (sub : Subst sig) (eqs : Equations sig) : Equations sig :=
  eqs.map (substEquation sub)

/-- Size of one equation. -/
def equationSize {sig : Signature} (e : Equation sig) : Nat :=
  Term.size e.1 + Term.size e.2

/-- Total size of a list of equations. -/
def equationsSize {sig : Signature} (eqs : Equations sig) : Nat :=
  eqs.foldl (fun n e => n + equationSize e) 0

def equationsBudget {sig : Signature} (eqs : Equations sig) : Nat :=
  equationsSize eqs + eqs.length + 1

@[simp] theorem equationsSize_nil {sig : Signature} :
    equationsSize (sig := sig) [] = 0 := by
  rfl

@[simp] theorem equationsSize_cons {sig : Signature} (e : Equation sig) (eqs : Equations sig) :
    equationsSize (e :: eqs) = equationSize e + equationsSize eqs := by
  unfold equationsSize
  simp [List.foldl]
  have hfoldl :
      ∀ (a b : Nat) (eqs : Equations sig),
        List.foldl (fun n e => n + equationSize e) (a + b) eqs =
          a + List.foldl (fun n e => n + equationSize e) b eqs := by
    intro a b eqs
    induction eqs generalizing a b with
    | nil =>
        simp
    | cons e' eqs ih =>
        simp [List.foldl, Nat.add_assoc, ih]
  simpa [Nat.add_zero] using (hfoldl (a := equationSize e) (b := 0) (eqs := eqs))

theorem equationsSize_append {sig : Signature} (eqs₁ eqs₂ : Equations sig) :
    equationsSize (eqs₁ ++ eqs₂) = equationsSize eqs₁ + equationsSize eqs₂ := by
  induction eqs₁ with
  | nil =>
      simp [equationsSize]
  | cons e eqs ih =>
      simp [equationsSize_cons, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

@[simp] theorem unifiesList_nil {sig : Signature} (sub : Subst sig) :
    UnifiesList sub [] := by
  simp [UnifiesList]

theorem unifiesList_cons {sig : Signature} (sub : Subst sig)
    (e : Equation sig) (eqs : Equations sig) :
    UnifiesList sub (e :: eqs) ↔
      Term.subst sub e.1 = Term.subst sub e.2 ∧ UnifiesList sub eqs := by
  constructor
  · intro h
    refine ⟨h e (by simp), ?_⟩
    intro e' he'
    exact h e' (by simp [he'])
  · rintro ⟨hhead, htail⟩ e' he'
    have : e' = e ∨ e' ∈ eqs := by
      simpa using he'
    cases this with
    | inl hEq =>
        subst hEq
        exact hhead
    | inr hmem =>
        exact htail e' hmem

theorem unifiesList_append {sig : Signature} (sub : Subst sig)
    (eqs₁ eqs₂ : Equations sig) :
    UnifiesList sub (eqs₁ ++ eqs₂) ↔
      UnifiesList sub eqs₁ ∧ UnifiesList sub eqs₂ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro e he
      exact h e (by simp [he])
    · intro e he
      exact h e (by simp [he])
  · rintro ⟨h₁, h₂⟩ e he
    rcases List.mem_append.mp he with hmem | hmem
    · exact h₁ e hmem
    · exact h₂ e hmem

theorem unifiesList_compSubst {sig : Signature} {sub tau : Subst sig} {eqs : Equations sig}
    (h : UnifiesList sub (substEquations tau eqs)) :
    UnifiesList (Term.compSubst sub tau) eqs := by
  intro e he
  have hmem : substEquation tau e ∈ substEquations tau eqs :=
    List.mem_map_of_mem (f := substEquation tau) he
  have hEq := h (substEquation tau e) hmem
  simpa [substEquation, Term.subst_comp] using hEq

/-! ## Occurs Check -/

/-- Decide existence over a finite index. -/
def decExistsFin : ∀ {n} (p : Fin n → Prop) [DecidablePred p], Decidable (∃ i, p i)
  | 0, _, _ => isFalse (by
      intro h
      rcases h with ⟨i, _⟩
      exact Fin.elim0 i)
  | n + 1, p, _ =>
      if h0 : p 0 then
        isTrue ⟨0, h0⟩
      else
        by
          haveI : DecidablePred (fun i => p (Fin.succ i)) := fun i => inferInstance
          cases decExistsFin (p := fun i => p (Fin.succ i)) with
          | isTrue h =>
              exact isTrue (by
                rcases h with ⟨i, hi⟩
                exact ⟨Fin.succ i, hi⟩)
          | isFalse h =>
              exact isFalse (by
                intro h'
                rcases h' with ⟨i, hi⟩
                cases i using Fin.cases with
                | zero => exact h0 hi
                | succ i => exact h ⟨i, hi⟩)

noncomputable instance occursDecidable {sig : Signature} (x : Nat) :
    DecidablePred (Occurs (sig := sig) x) := by
  intro t
  induction t with
  | var y =>
      simpa [Occurs] using (decEq x y)
  | app f args ih =>
      haveI : DecidablePred (fun i => Occurs (sig := sig) x (args i)) := fun i => ih i
      simpa [Occurs] using
        (decExistsFin (p := fun i => Occurs (sig := sig) x (args i)))

theorem subst_updateSubst_notOccurs {sig : Signature} {x : Nat} {t u : Term sig}
    (h : ¬ Occurs (sig := sig) x t) :
    Term.subst (updateSubst Term.idSubst x u) t = t := by
  induction t with
  | var y =>
      have hyx : y ≠ x := by
        simpa [Occurs, eq_comm] using h
      simp [Term.subst, updateSubst, hyx, Term.idSubst]
  | app f args ih =>
      have hargs : ∀ i, ¬ Occurs (sig := sig) x (args i) := by
        intro i hi
        exact h ⟨i, hi⟩
      apply congrArg (fun args' => Term.app f args')
      funext i
      exact ih i (hargs i)

/-! ## Argument Equations -/

/-- Equations pairing each argument position. -/
def equationsOfArgs {sig : Signature} :
    ∀ {n}, (Fin n → Term sig) → (Fin n → Term sig) → Equations sig
  | 0, _, _ => []
  | n + 1, args, args' =>
      (args 0, args' 0) ::
        equationsOfArgs (fun i => args (Fin.succ i)) (fun i => args' (Fin.succ i))

theorem unifiesList_equationsOfArgs {sig : Signature} {sub : Subst sig} :
    ∀ {n} {args args' : Fin n → Term sig},
      UnifiesList sub (equationsOfArgs args args') →
      ∀ i, Term.subst sub (args i) = Term.subst sub (args' i)
  | 0, _, _, _, i => (Fin.elim0 i)
  | n + 1, args, args', h, i => by
      have h' :
          Term.subst sub (args 0) = Term.subst sub (args' 0) ∧
          UnifiesList sub
            (equationsOfArgs (fun j => args (Fin.succ j))
              (fun j => args' (Fin.succ j))) := by
        simpa [equationsOfArgs, unifiesList_cons] using h
      cases i using Fin.cases with
      | zero => exact h'.1
      | succ i =>
          exact unifiesList_equationsOfArgs (n := n)
            (args := fun j => args (Fin.succ j))
            (args' := fun j => args' (Fin.succ j)) h'.2 i

theorem unifies_app_of_args {sig : Signature} {sub : Subst sig} {f : sig.Sym}
    {args args' : Fin (sig.arity f) → Term sig}
    (h : UnifiesList sub (equationsOfArgs args args')) :
    Term.subst sub (Term.app f args) = Term.subst sub (Term.app f args') := by
  apply congrArg (fun args'' => Term.app f args'')
  funext i
  exact unifiesList_equationsOfArgs (args := args) (args' := args') h i

/-! ## Unification Algorithm -/

/-- Fuel-bounded unification algorithm (Robinson-style). -/
noncomputable def unifyFuel {sig : Signature} [DecidableEq sig.Sym] :
    Nat → Equations sig → Option (Subst sig)
  | 0, _ => none
  | fuel + 1, [] => some Term.idSubst
  | fuel + 1, (s, t) :: eqs =>
      match s, t with
      | Term.var x, Term.var y =>
          if hxy : x = y then
            unifyFuel fuel eqs
          else
            let sub : Subst sig := updateSubst Term.idSubst x (Term.var y)
            match unifyFuel fuel (substEquations sub eqs) with
            | none => none
            | some theta => some (Term.compSubst theta sub)
      | Term.var x, _ =>
          if hocc : Occurs (sig := sig) x t then
            none
          else
            let sub : Subst sig := updateSubst Term.idSubst x t
            match unifyFuel fuel (substEquations sub eqs) with
            | none => none
            | some theta => some (Term.compSubst theta sub)
      | _, Term.var x =>
          if hocc : Occurs (sig := sig) x s then
            none
          else
            let sub : Subst sig := updateSubst Term.idSubst x s
            match unifyFuel fuel (substEquations sub eqs) with
            | none => none
            | some theta => some (Term.compSubst theta sub)
      | Term.app f args, Term.app g args' =>
          if hfg : f = g then
            (by
              cases hfg
              exact unifyFuel fuel (equationsOfArgs args args' ++ eqs))
          else
            none

/-- Default fuel based on total equation size. -/
noncomputable def unify {sig : Signature} [DecidableEq sig.Sym] (eqs : Equations sig) :
    Option (Subst sig) := by
  classical
  by_cases h : ∃ fuel sub, unifyFuel (sig := sig) fuel eqs = some sub
  ·
    let fuel : Nat := Classical.choose h
    have hsub : ∃ sub, unifyFuel (sig := sig) fuel eqs = some sub := Classical.choose_spec h
    exact some (Classical.choose hsub)
  ·
    exact none

/-- Executable unification with a size-based fuel bound. -/
noncomputable def unifyBounded {sig : Signature} [DecidableEq sig.Sym] (eqs : Equations sig) :
    Option (Subst sig) :=
  unifyFuel (sig := sig) (equationsBudget eqs) eqs

theorem unifyFuel_sound {sig : Signature} [DecidableEq sig.Sym] :
    ∀ {fuel eqs sub},
      unifyFuel (sig := sig) fuel eqs = some sub →
      UnifiesList sub eqs := by
  intro fuel eqs sub h
  induction fuel generalizing eqs sub with
  | zero =>
      cases h
  | succ fuel ih =>
      cases eqs with
      | nil =>
          cases h
          simp [UnifiesList]
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
                        have htail : UnifiesList sub eqs :=
                          ih (eqs := eqs) (sub := sub) h'
                        refine (unifiesList_cons (sub := sub) (e := (Term.var x, Term.var y)) (eqs := eqs)).2 ?_
                        have hhead : Term.subst sub (Term.var x) = Term.subst sub (Term.var y) := by
                          simpa [hxy]
                        exact ⟨hhead, htail⟩
                      ·
                        let sub0 : Subst sig := updateSubst Term.idSubst x (Term.var y)
                        cases hres : unifyFuel fuel (substEquations sub0 eqs) with
                        | none =>
                            simp [unifyFuel, hxy, sub0, hres] at h
                        | some theta =>
                            simp [unifyFuel, hxy, sub0, hres] at h
                            subst h
                            have htail : UnifiesList theta (substEquations sub0 eqs) :=
                              ih (eqs := substEquations sub0 eqs) (sub := theta) hres
                            have htail' : UnifiesList (Term.compSubst theta sub0) eqs :=
                              unifiesList_compSubst (sub := theta) (tau := sub0) htail
                            have hyx : y ≠ x := by exact Ne.symm hxy
                            have hhead :
                                Term.subst (Term.compSubst theta sub0) (Term.var x) =
                                  Term.subst (Term.compSubst theta sub0) (Term.var y) := by
                              simp [Term.subst, Term.compSubst, sub0, updateSubst_same, updateSubst_ne, hyx, Term.idSubst]
                            exact (unifiesList_cons (sub := Term.compSubst theta sub0)
                              (e := (Term.var x, Term.var y)) (eqs := eqs)).2 ⟨hhead, htail'⟩
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
                            have htail : UnifiesList theta (substEquations sub0 eqs) :=
                              ih (eqs := substEquations sub0 eqs) (sub := theta) hres
                            have htail' : UnifiesList (Term.compSubst theta sub0) eqs :=
                              unifiesList_compSubst (sub := theta) (tau := sub0) htail
                            have hsub0 : Term.subst sub0 (Term.app f args) = Term.app f args :=
                              subst_updateSubst_notOccurs (x := x) (t := Term.app f args)
                                (u := Term.app f args) hocc
                            have hhead :
                                Term.subst (Term.compSubst theta sub0) (Term.var x) =
                                  Term.subst (Term.compSubst theta sub0) (Term.app f args) := by
                              calc
                                Term.subst (Term.compSubst theta sub0) (Term.var x)
                                    = Term.subst theta (Term.app f args) := by
                                        simp [Term.subst, Term.compSubst, sub0, updateSubst_same]
                                _ = Term.subst theta (Term.subst sub0 (Term.app f args)) := by
                                      simpa [hsub0]
                                _ = Term.subst (Term.compSubst theta sub0) (Term.app f args) := by
                                      symm
                                      simpa [Term.subst_comp]
                            exact (unifiesList_cons (sub := Term.compSubst theta sub0)
                              (e := (Term.var x, Term.app f args)) (eqs := eqs)).2 ⟨hhead, htail'⟩
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
                            have htail : UnifiesList theta (substEquations sub0 eqs) :=
                              ih (eqs := substEquations sub0 eqs) (sub := theta) hres
                            have htail' : UnifiesList (Term.compSubst theta sub0) eqs :=
                              unifiesList_compSubst (sub := theta) (tau := sub0) htail
                            have hsub0 : Term.subst sub0 (Term.app f args) = Term.app f args :=
                              subst_updateSubst_notOccurs (x := x) (t := Term.app f args)
                                (u := Term.app f args) hocc
                            have hhead :
                                Term.subst (Term.compSubst theta sub0) (Term.app f args) =
                                  Term.subst (Term.compSubst theta sub0) (Term.var x) := by
                              calc
                                Term.subst (Term.compSubst theta sub0) (Term.app f args)
                                    = Term.subst theta (Term.subst sub0 (Term.app f args)) := by
                                        simp [Term.subst_comp]
                                _ = Term.subst theta (Term.app f args) := by
                                      simp [hsub0]
                                _ = Term.subst (Term.compSubst theta sub0) (Term.var x) := by
                                      simp [Term.subst, Term.compSubst, sub0, updateSubst_same]
                            exact (unifiesList_cons (sub := Term.compSubst theta sub0)
                              (e := (Term.app f args, Term.var x)) (eqs := eqs)).2 ⟨hhead, htail'⟩
                  | app g args' =>
                      by_cases hfg : f = g
                      ·
                        cases hfg
                        have h' : unifyFuel fuel (equationsOfArgs args args' ++ eqs) = some sub := by
                          simpa [unifyFuel] using h
                        have h' := ih (eqs := equationsOfArgs args args' ++ eqs) (sub := sub) h'
                        have hsplit :=
                          (unifiesList_append (sub := sub)
                            (eqs₁ := equationsOfArgs args args') (eqs₂ := eqs)).1 h'
                        rcases hsplit with ⟨hargs, htail⟩
                        have hhead :
                            Term.subst sub (Term.app f args) =
                              Term.subst sub (Term.app f args') := by
                          simpa using (unifies_app_of_args (f := f) (args := args) (args' := args') hargs)
                        exact (unifiesList_cons (sub := sub)
                          (e := (Term.app f args, Term.app f args')) (eqs := eqs)).2 ⟨hhead, htail⟩
                      ·
                        simp [unifyFuel, hfg] at h

theorem unify_sound {sig : Signature} [DecidableEq sig.Sym] {eqs : Equations sig} {sub : Subst sig} :
    unify (sig := sig) eqs = some sub → UnifiesList sub eqs := by
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
    exact unifyFuel_sound (sub := sub') hsub'
  ·
    simp [hex] at h

theorem unifyBounded_sound {sig : Signature} [DecidableEq sig.Sym]
    {eqs : Equations sig} {sub : Subst sig} :
    unifyBounded (sig := sig) eqs = some sub → UnifiesList sub eqs := by
  intro h
  have h' : unifyFuel (sig := sig) (equationsBudget eqs) eqs = some sub := by
    simpa [unifyBounded] using h
  exact unifyFuel_sound (fuel := equationsBudget eqs) (eqs := eqs) (sub := sub) h'

end Metatheory.TRS.FirstOrder
