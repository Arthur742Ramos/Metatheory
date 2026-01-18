/-
# Positions and Replacement for First-Order Terms

This module defines positions, subterm selection, and replacement for
first-order terms. These are foundational for critical pairs and completion.
-/

import Metatheory.TRS.FirstOrder.Syntax

namespace Metatheory.TRS.FirstOrder

/-! ## Positions -/

/-- Positions are paths of child indices. -/
abbrev Pos := List Nat

/-! ## Prefix Order on Positions -/

/-- Prefix relation on positions. -/
def PosPrefix (p q : Pos) : Prop := ∃ r, q = p ++ r

@[simp] theorem posPrefix_refl (p : Pos) : PosPrefix p p := by
  refine ⟨[], by simp⟩

theorem posPrefix_trans {p q r : Pos} :
    PosPrefix p q -> PosPrefix q r -> PosPrefix p r := by
  intro hp hq
  rcases hp with ⟨s, rfl⟩
  rcases hq with ⟨t, rfl⟩
  refine ⟨s ++ t, by simp [List.append_assoc]⟩

namespace Term

variable {sig : Signature}

/-- Retrieve the subterm at a position (if valid). -/
def subterm : Term sig -> Pos -> Option (Term sig)
  | t, [] => some t
  | var _, _ :: _ => none
  | app f args, i :: ps =>
    if h : i < sig.arity f then
      subterm (args ⟨i, h⟩) ps
    else
      none

theorem subterm_append {t u : Term sig} {p q : Pos} :
    subterm t p = some u -> subterm t (p ++ q) = subterm u q := by
  intro hsub
  induction p generalizing t u with
  | nil =>
      have ht : t = u := by
        simpa [subterm] using hsub
      subst ht
      simp [subterm]
  | cons i ps ih =>
      cases t with
      | var x =>
          simp [subterm] at hsub
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            have hsub' : subterm (args ⟨i, hi⟩) ps = some u := by
              simpa [subterm, hi] using hsub
            have ih' := ih (t := args ⟨i, hi⟩) (u := u) hsub'
            simpa [subterm, hi] using ih'
          ·
            simp [subterm, hi] at hsub

/-- Replace the subterm at a position (if valid). -/
def replace : Term sig -> Pos -> Term sig -> Option (Term sig)
  | _, [], u => some u
  | var _, _ :: _, _ => none
  | app f args, i :: ps, u =>
    if h : i < sig.arity f then
      let idx : Fin (sig.arity f) := ⟨i, h⟩
      match replace (args idx) ps u with
      | none => none
      | some t' =>
        let args' : Fin (sig.arity f) -> Term sig :=
          fun j => if _ : j = idx then t' else args j
        some (app f args')
    else
      none

@[simp] theorem subterm_root (t : Term sig) : subterm t [] = some t := by
  cases t <;> rfl

@[simp] theorem replace_root (t u : Term sig) : replace t [] u = some u := by
  cases t <;> rfl

@[simp] theorem subterm_var_cons (x : Nat) (i : Nat) (p : Pos) :
    subterm (var (sig := sig) x) (i :: p) = none := by
  rfl

@[simp] theorem replace_var_cons (x : Nat) (i : Nat) (p : Pos) (u : Term sig) :
    replace (var (sig := sig) x) (i :: p) u = none := by
  rfl

theorem subterm_replace {t u t' : Term sig} {p : Pos} :
    replace t p u = some t' -> subterm t' p = some u := by
  intro hrep
  induction p generalizing t t' with
  | nil =>
      have ht' : t' = u := by
        simpa [replace] using hrep.symm
      subst ht'
      simp [subterm]
  | cons i ps ih =>
      cases t with
      | var x =>
          simp [replace] at hrep
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            cases hrep' : replace (args ⟨i, hi⟩) ps u with
            | none =>
                simp [replace, hi, hrep'] at hrep
            | some t1 =>
                have ht' : t' =
                    app f (fun j => if _ : j = ⟨i, hi⟩ then t1 else args j) := by
                  simpa [replace, hi, hrep'] using hrep.symm
                subst ht'
                have ih' := ih (t := args ⟨i, hi⟩) (t' := t1) hrep'
                simpa [subterm, hi, ih']
          ·
            simp [replace, hi] at hrep

theorem subterm_subst (sub : Subst sig) :
    ∀ {t : Term sig} {p : Pos} {u : Term sig},
      subterm t p = some u ->
      subterm (Term.subst sub t) p = some (Term.subst sub u) := by
  intro t p
  induction p generalizing t with
  | nil =>
      intro u h
      have ht : t = u := by
        simpa [subterm] using h
      subst ht
      simp
  | cons i ps ih =>
      intro u h
      cases t with
      | var x =>
          cases (by simpa [subterm] using h : False)
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            have hsub : subterm (args ⟨i, hi⟩) ps = some u := by
              simpa [subterm, hi] using h
            have ih' := ih (t := args ⟨i, hi⟩) (u := u) hsub
            simp [subterm, Term.subst, hi, ih']
          ·
            simp [subterm, hi] at h

-- subterm_subst_inv and subterm_subst_iff are not needed in this development.


theorem replace_subst (sub : Subst sig) :
    ∀ {t : Term sig} {p : Pos} {u t' : Term sig},
      replace t p u = some t' ->
      replace (Term.subst sub t) p (Term.subst sub u) = some (Term.subst sub t') := by
  intro t p
  induction p generalizing t with
  | nil =>
      intro u t' h
      have ht' : t' = u := by
        simpa [replace] using h.symm
      subst ht'
      simp [replace, Term.subst]
  | cons i ps ih =>
      intro u t' h
      cases t with
      | var x =>
          simp [replace] at h
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            cases hrep : replace (args ⟨i, hi⟩) ps u with
            | none =>
                simp [replace, hi, hrep] at h
            | some t1 =>
              have ht' : t' =
                  app f (fun j => if _ : j = ⟨i, hi⟩ then t1 else args j) := by
                simpa [replace, hi, hrep] using h.symm
              subst ht'
              have ih' := ih (t := args ⟨i, hi⟩) (u := u) (t' := t1) hrep
              exact by
                have hfun :
                    (fun j => if _ : j = ⟨i, hi⟩ then Term.subst sub t1 else Term.subst sub (args j)) =
                      fun j => Term.subst sub (if _ : j = ⟨i, hi⟩ then t1 else args j) := by
                  funext j
                  by_cases hji : j = ⟨i, hi⟩ <;> simp [hji, Term.subst]
                simpa [replace, Term.subst, hi, hrep, ih', hfun]
          ·
            simp [replace, hi] at h

theorem replace_defined_of_replace {t u t' : Term sig} {p : Pos} :
    replace t p u = some t' -> ∀ v, ∃ t'', replace t p v = some t'' := by
  intro hrep v
  induction p generalizing t t' with
  | nil =>
      exact ⟨v, by simp [replace]⟩
  | cons i ps ih =>
      cases t with
      | var x =>
          simp [replace] at hrep
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            cases hrep' : replace (args ⟨i, hi⟩) ps u with
            | none =>
                simp [replace, hi, hrep'] at hrep
            | some t1 =>
                rcases ih (t := args ⟨i, hi⟩) (t' := t1) hrep' with ⟨t1', hrep_v⟩
                refine ⟨app f (fun j => if _ : j = ⟨i, hi⟩ then t1' else args j), ?_⟩
                simp [replace, hi, hrep_v]
          ·
            simp [replace, hi] at hrep

theorem replace_override {t u v t1 t2 : Term sig} {p : Pos} :
    replace t p u = some t1 ->
    replace t p v = some t2 ->
    replace t1 p v = some t2 := by
  intro hrep1 hrep2
  induction p generalizing t t1 t2 with
  | nil =>
      have ht1 : t1 = u := by
        simpa [replace] using hrep1.symm
      have ht2 : t2 = v := by
        simpa [replace] using hrep2.symm
      subst ht1 ht2
      simp [replace]
  | cons i ps ih =>
      cases t with
      | var x =>
          simp [replace] at hrep1
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            cases hrep1' : replace (args ⟨i, hi⟩) ps u with
            | none =>
                simp [replace, hi, hrep1'] at hrep1
            | some t1' =>
                have ht1 : t1 =
                    app f (fun j => if _ : j = ⟨i, hi⟩ then t1' else args j) := by
                  simpa [replace, hi, hrep1'] using hrep1.symm
                cases hrep2' : replace (args ⟨i, hi⟩) ps v with
                | none =>
                    simp [replace, hi, hrep2'] at hrep2
                | some t2' =>
                    have ht2 : t2 =
                        app f (fun j => if _ : j = ⟨i, hi⟩ then t2' else args j) := by
                      simpa [replace, hi, hrep2'] using hrep2.symm
                    subst ht1 ht2
                    have ih' := ih (t := args ⟨i, hi⟩) (t1 := t1') (t2 := t2') hrep1' hrep2'
                    have hfun :
                        (fun j => if j = ⟨i, hi⟩ then t2' else if j = ⟨i, hi⟩ then t1' else args j) =
                          fun j => if j = ⟨i, hi⟩ then t2' else args j := by
                      funext j
                      by_cases hji : j = ⟨i, hi⟩ <;> simp [hji]
                    simpa [replace, hi, hrep1', hrep2', ih', hfun]
          ·
            simp [replace, hi] at hrep1

theorem replace_append {t u u' t' : Term sig} {p q : Pos} {v : Term sig} :
    subterm t p = some u ->
    replace u q v = some u' ->
    replace t p u' = some t' ->
    replace t (p ++ q) v = some t' := by
  intro hsub hrep_inner hrep_outer
  induction p generalizing t u u' t' with
  | nil =>
      have hu : u = t := by
        simpa [subterm] using hsub.symm
      subst hu
      have ht' : t' = u' := by
        simpa [replace] using hrep_outer.symm
      subst ht'
      simpa using hrep_inner
  | cons i ps ih =>
      cases t with
      | var x =>
          simp [subterm] at hsub
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            have hsub' : subterm (args ⟨i, hi⟩) ps = some u := by
              simpa [subterm, hi] using hsub
            cases hrep_outer' : replace (args ⟨i, hi⟩) ps u' with
            | none =>
                simp [replace, hi, hrep_outer'] at hrep_outer
            | some t1 =>
                have ht' : t' =
                    app f (fun j => if _ : j = ⟨i, hi⟩ then t1 else args j) := by
                  simpa [replace, hi, hrep_outer'] using hrep_outer.symm
                subst ht'
                have ih' := ih (t := args ⟨i, hi⟩) (u := u) (u' := u') (t' := t1)
                  hsub' hrep_inner hrep_outer'
                simpa [replace, hi, ih'] using ih'
          ·
            simp [subterm, hi] at hsub

theorem replace_append_inv {t u t' : Term sig} {p q : Pos} {v : Term sig} :
    subterm t p = some u ->
    replace t (p ++ q) v = some t' ->
    ∃ u', replace u q v = some u' ∧ replace t p u' = some t' := by
  intro hsub hrep
  induction p generalizing t u t' with
  | nil =>
      have hu : u = t := by
        simpa [subterm] using hsub.symm
      subst hu
      refine ⟨t', ?_, ?_⟩
      · simpa using hrep
      · simpa [replace]
  | cons i ps ih =>
      cases t with
      | var x =>
          simp [subterm] at hsub
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            have hsub' : subterm (args ⟨i, hi⟩) ps = some u := by
              simpa [subterm, hi] using hsub
            cases hrep' : replace (args ⟨i, hi⟩) (ps ++ q) v with
            | none =>
                simp [replace, hi, hrep'] at hrep
            | some t1 =>
                have ht' : t' =
                    app f (fun j => if _ : j = ⟨i, hi⟩ then t1 else args j) := by
                  simpa [replace, hi, hrep'] using hrep.symm
                subst ht'
                rcases ih (t := args ⟨i, hi⟩) (u := u) (t' := t1) hsub' hrep'
                  with ⟨u', hrep_inner, hrep_outer⟩
                refine ⟨u', hrep_inner, ?_⟩
                simpa [replace, hi, hrep_outer]
          ·
            simp [subterm, hi] at hsub

theorem replace_self {t u : Term sig} {p : Pos} :
    subterm t p = some u ->
    replace t p u = some t := by
  intro hsub
  induction p generalizing t u with
  | nil =>
      have hu : u = t := by
        simpa [subterm] using hsub.symm
      subst hu
      simp [replace]
  | cons i ps ih =>
      cases t with
      | var x =>
        simp [subterm] at hsub
      | app f args =>
        by_cases hi : i < sig.arity f
        ·
          have hsub' : subterm (args ⟨i, hi⟩) ps = some u := by
            simpa [subterm, hi] using hsub
          have hrep' := ih (t := args ⟨i, hi⟩) (u := u) hsub'
          have hfun : (fun j => if _ : j = ⟨i, hi⟩ then args ⟨i, hi⟩ else args j) = args := by
            funext j
            by_cases hji : j = ⟨i, hi⟩ <;> simp [hji]
          exact by
            simpa [replace, hi, hrep', hfun]
        ·
          simp [subterm, hi] at hsub

/-- Proper subterms are strictly smaller in size. -/
theorem size_subterm_lt {t u : Term sig} {p : Pos} :
    subterm t p = some u → p ≠ [] → size u < size t := by
  intro hsub hpos
  induction p generalizing t u with
  | nil =>
      exact (hpos rfl).elim
  | cons i ps ih =>
      cases t with
      | var x =>
          simp [subterm] at hsub
      | app f args =>
          by_cases hi : i < sig.arity f
          ·
            have hsub' : subterm (args ⟨i, hi⟩) ps = some u := by
              simpa [subterm, hi] using hsub
            have hlt_arg : size (args ⟨i, hi⟩) < size (app f args) := by
              have hle := finSum_ge (f := fun j => size (args j)) (i := ⟨i, hi⟩)
              have hlt : size (args ⟨i, hi⟩) < finSum (fun j => size (args j)) + 1 :=
                Nat.lt_succ_of_le hle
              simpa [size, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
            by_cases hps : ps = []
            ·
              have hu : u = args ⟨i, hi⟩ := by
                simpa [subterm, hps] using hsub'.symm
              subst hu
              exact hlt_arg
            ·
              have hlt_sub := ih (t := args ⟨i, hi⟩) (u := u) hsub' hps
              exact Nat.lt_trans hlt_sub hlt_arg
          ·
            simp [subterm, hi] at hsub

/-- Replacing a subterm with a larger one increases size. -/
theorem size_replace_lt {t u v t' t'' : Term sig} {p : Pos}
    (hrep1 : replace t p u = some t')
    (hrep2 : replace t p v = some t'')
    (h : size u < size v) :
    size t' < size t'' := by
  induction p generalizing t u v t' t'' with
  | nil =>
    have ht' : t' = u := by
      simpa [replace] using hrep1.symm
    have ht'' : t'' = v := by
      simpa [replace] using hrep2.symm
    subst ht' ht''
    simpa using h
  | cons i ps ih =>
    cases t with
    | var x =>
      simp [replace] at hrep1
    | app f args =>
      by_cases hi : i < sig.arity f
      ·
        cases hrep1' : replace (args ⟨i, hi⟩) ps u with
        | none =>
          simp [replace, hi, hrep1'] at hrep1
        | some t1 =>
          cases hrep2' : replace (args ⟨i, hi⟩) ps v with
          | none =>
            simp [replace, hi, hrep2'] at hrep2
          | some t2 =>
            have ht' : t' =
                app f (fun j => if _ : j = ⟨i, hi⟩ then t1 else args j) := by
              simpa [replace, hi, hrep1'] using hrep1.symm
            have ht'' : t'' =
                app f (fun j => if _ : j = ⟨i, hi⟩ then t2 else args j) := by
              simpa [replace, hi, hrep2'] using hrep2.symm
            subst ht' ht''
            have hsize : size t1 < size t2 := ih hrep1' hrep2' h
            have hsum :
                finSum (fun j => size (if _ : j = ⟨i, hi⟩ then t1 else args j)) <
                finSum (fun j => size (if _ : j = ⟨i, hi⟩ then t2 else args j)) := by
              refine finSum_lt_of_lt (i := ⟨i, hi⟩) ?_ ?_
              · simpa using hsize
              · intro j hj
                by_cases hji : j = ⟨i, hi⟩
                · exact (hj hji).elim
                · simp [hji]
            have : 1 + finSum (fun j => size (if _ : j = ⟨i, hi⟩ then t1 else args j)) <
                1 + finSum (fun j => size (if _ : j = ⟨i, hi⟩ then t2 else args j)) :=
              Nat.add_lt_add_left hsum 1
            simpa [size] using this
      ·
        simp [replace, hi] at hrep1

/-- Subterm stays the same if the replacement position is disjoint. -/
theorem subterm_replace_of_disjoint {t u t' : Term sig} {p q : Pos} :
    replace t p u = some t' ->
    ¬ PosPrefix p q ->
    ¬ PosPrefix q p ->
    subterm t' q = subterm t q := by
  intro hrep hnotpq hnotqp
  induction p generalizing t u t' q with
  | nil =>
      have : PosPrefix [] q := ⟨q, by simp⟩
      exact (False.elim (hnotpq this))
  | cons i ps ih =>
      cases q with
      | nil =>
          have : PosPrefix [] (i :: ps) := ⟨i :: ps, by simp⟩
          exact (False.elim (hnotqp this))
      | cons j qs =>
          cases t with
          | var x =>
              simp [replace] at hrep
          | app f args =>
              by_cases hi : i < sig.arity f
              ·
                cases hrep' : replace (args ⟨i, hi⟩) ps u with
                | none =>
                    simp [replace, hi, hrep'] at hrep
                | some t1 =>
                    have ht' : t' =
                        app f (fun k => if _ : k = ⟨i, hi⟩ then t1 else args k) := by
                      simpa [replace, hi, hrep'] using hrep.symm
                    subst ht'
                    by_cases hij : i = j
                    ·
                      subst hij
                      have hnotpq' : ¬ PosPrefix ps qs := by
                        intro h
                        apply hnotpq
                        rcases h with ⟨r, rfl⟩
                        exact ⟨r, by simp [List.append_assoc]⟩
                      have hnotqp' : ¬ PosPrefix qs ps := by
                        intro h
                        apply hnotqp
                        rcases h with ⟨r, rfl⟩
                        exact ⟨r, by simp [List.append_assoc]⟩
                      have ih' := ih (t := args ⟨i, hi⟩) (u := u) (t' := t1) (q := qs)
                        hrep' hnotpq' hnotqp'
                      simpa [subterm, hi] using ih'
                    ·
                      by_cases hj : j < sig.arity f
                      ·
                        have hne : (⟨j, hj⟩ : Fin (sig.arity f)) ≠ ⟨i, hi⟩ := by
                          intro h
                          have hval := congrArg Fin.val h
                          exact hij hval.symm
                        simp [subterm, hi, hj, hne]
                      ·
                        simp [subterm, hi, hj]
              ·
                simp [replace, hi] at hrep

theorem replace_comm_of_disjoint {t u v t1 t2 : Term sig} {p q : Pos} :
    replace t p u = some t1 ->
    replace t q v = some t2 ->
    ¬ PosPrefix p q ->
    ¬ PosPrefix q p ->
    ∃ t', replace t1 q v = some t' ∧ replace t2 p u = some t' := by
  intro hrep1 hrep2 hnotpq hnotqp
  induction p generalizing t u v t1 t2 q with
  | nil =>
      have : PosPrefix [] q := ⟨q, by simp⟩
      exact (False.elim (hnotpq this))
  | cons i ps ih =>
      cases q with
      | nil =>
          have : PosPrefix [] (i :: ps) := ⟨i :: ps, by simp⟩
          exact (False.elim (hnotqp this))
      | cons j qs =>
          cases t with
          | var x =>
              simp [replace] at hrep1
          | app f args =>
              by_cases hi : i < sig.arity f
              ·
                cases hrep1' : replace (args ⟨i, hi⟩) ps u with
                | none =>
                    simp [replace, hi, hrep1'] at hrep1
                | some t1' =>
                    have ht1 : t1 =
                        app f (fun k => if _ : k = ⟨i, hi⟩ then t1' else args k) := by
                      simpa [replace, hi, hrep1'] using hrep1.symm
                    by_cases hj : j < sig.arity f
                    ·
                      cases hrep2' : replace (args ⟨j, hj⟩) qs v with
                      | none =>
                          simp [replace, hj, hrep2'] at hrep2
                      | some t2' =>
                          have ht2 : t2 =
                              app f (fun k => if _ : k = ⟨j, hj⟩ then t2' else args k) := by
                            simpa [replace, hj, hrep2'] using hrep2.symm
                          by_cases hij : i = j
                          ·
                            subst hij
                            have hnotpq' : ¬ PosPrefix ps qs := by
                              intro h
                              apply hnotpq
                              rcases h with ⟨r, rfl⟩
                              exact ⟨r, by simp [List.append_assoc]⟩
                            have hnotqp' : ¬ PosPrefix qs ps := by
                              intro h
                              apply hnotqp
                              rcases h with ⟨r, rfl⟩
                              exact ⟨r, by simp [List.append_assoc]⟩
                            have ih' := ih (t := args ⟨i, hi⟩) (u := u) (v := v)
                              (t1 := t1') (t2 := t2') (q := qs)
                              hrep1' hrep2' hnotpq' hnotqp'
                            rcases ih' with ⟨t', hrep1'', hrep2''⟩
                            refine ⟨app f (fun k => if _ : k = ⟨i, hi⟩ then t' else args k), ?_, ?_⟩
                            ·
                              subst ht1
                              have hfun :
                                  (fun k =>
                                      if _ : k = ⟨i, hi⟩ then t'
                                      else if _ : k = ⟨i, hi⟩ then t1' else args k) =
                                    fun k => if _ : k = ⟨i, hi⟩ then t' else args k := by
                                funext k
                                by_cases hk : k = ⟨i, hi⟩ <;> simp [hk]
                              simpa [replace, hi, hrep1'', hfun]
                            ·
                              subst ht2
                              have hfun :
                                  (fun k =>
                                      if _ : k = ⟨i, hi⟩ then t'
                                      else if _ : k = ⟨i, hi⟩ then t2' else args k) =
                                    fun k => if _ : k = ⟨i, hi⟩ then t' else args k := by
                                funext k
                                by_cases hk : k = ⟨i, hi⟩ <;> simp [hk]
                              simpa [replace, hi, hrep2'', hfun]
                          ·
                            have hne : (⟨j, hj⟩ : Fin (sig.arity f)) ≠ ⟨i, hi⟩ := by
                              intro h
                              apply hij
                              exact (congrArg Fin.val h).symm
                            have hne' : (⟨i, hi⟩ : Fin (sig.arity f)) ≠ ⟨j, hj⟩ := by
                              intro h
                              apply hij
                              exact congrArg Fin.val h
                            have hji : j ≠ i := by
                              exact Ne.symm hij
                            refine ⟨
                              app f (fun k =>
                                if _ : k = ⟨i, hi⟩ then t1' else if _ : k = ⟨j, hj⟩ then t2' else args k),
                              ?_, ?_⟩
                            ·
                              subst ht1
                              have hfun :
                                  (fun k =>
                                      if _ : k = ⟨j, hj⟩ then t2'
                                      else if _ : k = ⟨i, hi⟩ then t1' else args k) =
                                    fun k =>
                                      if _ : k = ⟨i, hi⟩ then t1'
                                      else if _ : k = ⟨j, hj⟩ then t2' else args k := by
                                funext k
                                by_cases hki : k = ⟨i, hi⟩
                                · subst hki; simp [hne, hne', hij, hji]
                                · by_cases hkj : k = ⟨j, hj⟩
                                  · subst hkj; simp [hki, hne', hij, hji]
                                  · simp [hki, hkj, hij, hji]
                              simpa [replace, hj, hrep2', hfun, hne, hij, hji]
                            ·
                              subst ht2
                              have hfun :
                                  (fun k =>
                                      if _ : k = ⟨i, hi⟩ then t1'
                                      else if _ : k = ⟨j, hj⟩ then t2' else args k) =
                                    fun k =>
                                      if _ : k = ⟨j, hj⟩ then t2'
                                      else if _ : k = ⟨i, hi⟩ then t1' else args k := by
                                funext k
                                by_cases hkj : k = ⟨j, hj⟩
                                · subst hkj; simp [hne', hij, hji]
                                · by_cases hki : k = ⟨i, hi⟩
                                  · subst hki; simp [hkj, hne, hij, hji]
                                  · simp [hki, hkj, hij, hji]
                              simpa [replace, hi, hrep1', hfun, hne', hij, hji]
                    ·
                      simp [replace, hj] at hrep2
              ·
                simp [replace, hi] at hrep1

-- (reserved for future use)

end Term

end Metatheory.TRS.FirstOrder
