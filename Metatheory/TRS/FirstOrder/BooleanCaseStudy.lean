 /-
 # First-Order TRS Case Study: Boolean Fragment

 This module provides a small non-ground TRS example with two rules:
 - `not(not(x)) -> x`
 - `and(x,x) -> x`
 -/

import Metatheory.TRS.FirstOrder.Confluence

namespace Metatheory.TRS.FirstOrder

/- TODO: Fix Mathlib dependency (Fin.cons, List.Shortlex, etc.)

open Term

-- Reduce simp overhead by using `simp only` with explicit lemma sets
attribute [local simp] Overlap mkCriticalPair

/-! ## Signature and Terms -/

/-- Symbols for a Boolean signature. -/
inductive BoolSym : Type
  | and
  | not

/-- Arity of the Boolean symbols. -/
def boolArity : BoolSym -> Nat
  | .and => 2
  | .not => 1

/-- Boolean signature with unary `not` and binary `and`. -/
def boolSig : Signature :=
  { Sym := BoolSym, arity := boolArity }

/-- Unary constructor `not`. -/
def notTerm (t : Term boolSig) : Term boolSig :=
  Term.app BoolSym.not (fun _ => t)

/-- Binary constructor `and`. -/
def andTerm (s t : Term boolSig) : Term boolSig :=
  Term.app BoolSym.and (Fin.cons s (fun _ => t))

/-- Variable `x`. -/
def xTerm : Term boolSig := Term.var 0

/-! ## Simplifications -/

@[simp] lemma subterm_not (t : Term boolSig) :
    Term.subterm (notTerm t) [0] = some t := by
  simp [notTerm, Term.subterm, boolSig, boolArity]

@[simp] lemma replace_not (t u : Term boolSig) :
    Term.replace (notTerm t) [0] u = some (notTerm u) := by
  simp [notTerm, Term.replace, boolSig, boolArity]
  ext j
  cases j using Fin.cases with
  | zero => simp
  | succ j => exact (Fin.elim0 j)

@[simp] lemma subterm_and_left (s t : Term boolSig) :
    Term.subterm (andTerm s t) [0] = some s := by
  simp [andTerm, Term.subterm, boolSig, boolArity]

@[simp] lemma subterm_and_right (s t : Term boolSig) :
    Term.subterm (andTerm s t) [1] = some t := by
  simp [andTerm, Term.subterm, boolSig, boolArity]

@[simp] lemma replace_and_left (s t u : Term boolSig) :
    Term.replace (andTerm s t) [0] u = some (andTerm u t) := by
  simp [andTerm, Term.replace, boolSig, boolArity]
  ext j
  cases j using Fin.cases with
  | zero => simp
  | succ j =>
      cases j using Fin.cases with
      | zero => simp
      | succ j => exact (Fin.elim0 j)

@[simp] lemma replace_and_right (s t u : Term boolSig) :
    Term.replace (andTerm s t) [1] u = some (andTerm s u) := by
  simp [andTerm, Term.replace, boolSig, boolArity]
  ext j
  cases j using Fin.cases with
  | zero => simp
  | succ j =>
      cases j using Fin.cases with
      | zero => simp
      | succ j => exact (Fin.elim0 j)

@[simp] lemma subst_xTerm (sub : Subst boolSig) :
    Term.subst sub xTerm = sub 0 := by
  rfl

@[simp] lemma subst_notTerm (sub : Subst boolSig) (t : Term boolSig) :
    Term.subst sub (notTerm t) = notTerm (Term.subst sub t) := by
  rfl

@[simp] lemma subst_andTerm (sub : Subst boolSig) (s t : Term boolSig) :
    Term.subst sub (andTerm s t) =
      andTerm (Term.subst sub s) (Term.subst sub t) := by
  dsimp [andTerm, Term.subst]
  congr
  funext i
  cases i using Fin.cases <;> rfl

@[simp] lemma size_notTerm (t : Term boolSig) :
    Term.size (notTerm t) = 1 + Term.size t := by
  simp [notTerm, Term.size, Term.finSum, boolSig, boolArity]

@[simp] lemma size_andTerm (s t : Term boolSig) :
    Term.size (andTerm s t) = 1 + Term.size s + Term.size t := by
  simp [andTerm, Term.size, Term.finSum, boolSig, boolArity, Nat.add_assoc, Nat.add_comm]

/-! ## Rules -/

/-- Rule `not(not(x)) -> x`. -/
def rule_not_not : Rule boolSig :=
  { lhs := notTerm (notTerm xTerm), rhs := xTerm }

/-- Rule `and(x,x) -> x`. -/
def rule_and_idem : Rule boolSig :=
  { lhs := andTerm xTerm xTerm, rhs := xTerm }

/-- Rule set containing the Boolean rules. -/
def rules : RuleSet boolSig :=
  fun r => r = rule_not_not ∨ r = rule_and_idem

@[simp] lemma rules_not_not : rules rule_not_not := by
  simp [rules]

@[simp] lemma rules_and_idem : rules rule_and_idem := by
  simp [rules]

/-! ## Ordering Proofs -/

theorem rule_not_not_oriented :
    stableSizeLt (sig := boolSig) rule_not_not.rhs rule_not_not.lhs := by
  intro sub
  have h : Term.size (sub 0) < Term.size (sub 0) + 2 := by
    exact Nat.lt_add_of_pos_right (n := Term.size (sub 0)) (k := 2) (by decide)
  have hcalc : Term.size (Term.subst sub rule_not_not.lhs) = 1 + (1 + Term.size (sub 0)) := by
    simp [rule_not_not, Term.subst, subst_xTerm, size_notTerm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hcalc' : Term.size (Term.subst sub rule_not_not.lhs) = Term.size (sub 0) + 2 := by
    calc
      Term.size (Term.subst sub rule_not_not.lhs)
          = 1 + (1 + Term.size (sub 0)) := hcalc
      _ = Term.size (sub 0) + 2 := by
        omega
  have hcalc'' : Term.size (Term.subst sub rule_not_not.rhs) = Term.size (sub 0) := by
    simp [rule_not_not, Term.subst, subst_xTerm]
  simpa [hcalc', hcalc''] using h

theorem rule_and_idem_oriented :
    stableSizeLt (sig := boolSig) rule_and_idem.rhs rule_and_idem.lhs := by
  intro sub
  have h : Term.size (sub 0) < Term.size (sub 0) + (Term.size (sub 0) + 1) := by
    have hpos : 0 < Term.size (sub 0) + 1 := Nat.succ_pos _
    exact Nat.lt_add_of_pos_right (n := Term.size (sub 0)) (k := Term.size (sub 0) + 1) hpos
  simpa [rule_and_idem, Term.subst, subst_xTerm, size_andTerm, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using h

theorem rules_oriented :
    ∀ r, rules r → stableSizeLt (sig := boolSig) r.rhs r.lhs := by
  intro r hr
  rcases hr with rfl | rfl
  · exact rule_not_not_oriented
  · exact rule_and_idem_oriented

/-! ## Critical Pairs -/

lemma joinable_of_eq {s t : Term boolSig} (h : s = t) :
    Rewriting.Joinable (Step rules) s t := by
  subst h
  exact Rewriting.Joinable.refl (Step rules) _

lemma step_not_not (t : Term boolSig) :
    Step rules (notTerm (notTerm t)) t := by
  have hstep := step_of_rule rule_not_not rules_not_not (fun _ => t)
  simpa [rule_not_not, notTerm, Term.subst] using hstep

lemma step_and_idem (t : Term boolSig) :
    Step rules (andTerm t t) t := by
  have hstep := step_of_rule rule_and_idem rules_and_idem (fun _ => t)
  simpa [rule_and_idem, Term.subst, subst_xTerm, subst_andTerm] using hstep

lemma step_and_right_not_not (t : Term boolSig) :
    Step rules (andTerm t (notTerm (notTerm t))) (andTerm t t) := by
  refine ⟨rule_not_not, rules_not_not, [1], (fun _ => t), ?_, ?_⟩
  · simp [rule_not_not, Term.subst, subst_xTerm]
  · simp [rule_not_not, Term.subst, subst_xTerm]

lemma step_and_left_not_not (t : Term boolSig) :
    Step rules (andTerm (notTerm (notTerm t)) t) (andTerm t t) := by
  refine ⟨rule_not_not, rules_not_not, [0], (fun _ => t), ?_, ?_⟩
  · simp [rule_not_not, Term.subst, subst_xTerm]
  · simp [rule_not_not, Term.subst, subst_xTerm]

lemma step_and_right_and_idem (t : Term boolSig) :
    Step rules (andTerm t (andTerm t t)) (andTerm t t) := by
  refine ⟨rule_and_idem, rules_and_idem, [1], (fun _ => t), ?_, ?_⟩
  · simp [rule_and_idem, Term.subst, subst_xTerm]
  · simp [rule_and_idem, Term.subst, subst_xTerm]

lemma step_and_left_and_idem (t : Term boolSig) :
    Step rules (andTerm (andTerm t t) t) (andTerm t t) := by
  refine ⟨rule_and_idem, rules_and_idem, [0], (fun _ => t), ?_, ?_⟩
  · simp [rule_and_idem, Term.subst, subst_xTerm]
  · simp [rule_and_idem, Term.subst, subst_xTerm]

lemma joinable_and_not (t : Term boolSig) :
    Rewriting.Joinable (Step rules) (andTerm t t) (notTerm (notTerm t)) := by
  refine ⟨t, Rewriting.Star.single (step_and_idem t), Rewriting.Star.single (step_not_not t)⟩

lemma joinable_and_not_right (t : Term boolSig) :
    Rewriting.Joinable (Step rules) (andTerm t (notTerm (notTerm t))) (notTerm (notTerm t)) := by
  refine ⟨t, ?_, Rewriting.Star.single (step_not_not t)⟩
  exact Rewriting.Star.tail (Rewriting.Star.single (step_and_right_not_not t)) (step_and_idem t)

lemma joinable_and_not_left (t : Term boolSig) :
    Rewriting.Joinable (Step rules) (andTerm (notTerm (notTerm t)) t) (notTerm (notTerm t)) := by
  refine ⟨t, ?_, Rewriting.Star.single (step_not_not t)⟩
  exact Rewriting.Star.tail (Rewriting.Star.single (step_and_left_not_not t)) (step_and_idem t)

lemma joinable_and_nested_right (t : Term boolSig) :
    Rewriting.Joinable (Step rules) (andTerm t (andTerm t t)) (andTerm t t) := by
  refine ⟨t, ?_, Rewriting.Star.single (step_and_idem t)⟩
  exact Rewriting.Star.tail (Rewriting.Star.single (step_and_right_and_idem t)) (step_and_idem t)

lemma joinable_and_nested_left (t : Term boolSig) :
    Rewriting.Joinable (Step rules) (andTerm (andTerm t t) t) (andTerm t t) := by
  refine ⟨t, ?_, Rewriting.Star.single (step_and_idem t)⟩
  exact Rewriting.Star.tail (Rewriting.Star.single (step_and_left_and_idem t)) (step_and_idem t)

lemma joinable_and_context_right {s t s' : Term boolSig} {q : Pos}
    (hsub : Term.subterm s q = some (andTerm t t))
    (hrep : Term.replace s q t = some s') :
    Rewriting.Joinable (Step rules) s (andTerm s' s) := by
  have hstep : Step rules s s' := by
    refine ⟨rule_and_idem, rules_and_idem, q, (fun _ => t), ?_, ?_⟩
    · simpa [rule_and_idem, Term.subst] using hsub
    · simpa [rule_and_idem, Term.subst] using hrep
  have hsub_outer : Term.subterm (andTerm s' s) [1] = some s := by
    simp [subterm_and_right]
  have hsub_ctx : Term.subterm (andTerm s' s) ([1] ++ q) = some (andTerm t t) := by
    have hsub_append :=
      Term.subterm_append (t := andTerm s' s) (p := [1]) (q := q) (u := s) hsub_outer
    simpa [hsub_append] using hsub
  have hrep_outer : Term.replace (andTerm s' s) [1] s' = some (andTerm s' s') := by
    simp [replace_and_right]
  have hrep_ctx : Term.replace (andTerm s' s) ([1] ++ q) t = some (andTerm s' s') := by
    exact Term.replace_append (t := andTerm s' s) (u := s) (u' := s')
      (t' := andTerm s' s') (p := [1]) (q := q) (v := t) hsub_outer hrep hrep_outer
  have hstep_ctx : Step rules (andTerm s' s) (andTerm s' s') := by
    refine ⟨rule_and_idem, rules_and_idem, [1] ++ q, (fun _ => t), ?_, ?_⟩
    · simpa [rule_and_idem, Term.subst] using hsub_ctx
    · simpa [rule_and_idem, Term.subst] using hrep_ctx
  have hstep_root : Step rules (andTerm s' s') s' := step_and_idem s'
  refine ⟨s', Rewriting.Star.single hstep, ?_⟩
  exact Rewriting.Star.tail (Rewriting.Star.single hstep_ctx) hstep_root

lemma joinable_and_context_left {s t s' : Term boolSig} {q : Pos}
    (hsub : Term.subterm s q = some (andTerm t t))
    (hrep : Term.replace s q t = some s') :
    Rewriting.Joinable (Step rules) s (andTerm s s') := by
  have hstep : Step rules s s' := by
    refine ⟨rule_and_idem, rules_and_idem, q, (fun _ => t), ?_, ?_⟩
    · simpa [rule_and_idem, Term.subst] using hsub
    · simpa [rule_and_idem, Term.subst] using hrep
  have hsub_outer : Term.subterm (andTerm s s') [0] = some s := by
    simp [subterm_and_left]
  have hsub_ctx : Term.subterm (andTerm s s') ([0] ++ q) = some (andTerm t t) := by
    have hsub_append :=
      Term.subterm_append (t := andTerm s s') (p := [0]) (q := q) (u := s) hsub_outer
    simpa [hsub_append] using hsub
  have hrep_outer : Term.replace (andTerm s s') [0] s' = some (andTerm s' s') := by
    simp [replace_and_left]
  have hrep_ctx : Term.replace (andTerm s s') ([0] ++ q) t = some (andTerm s' s') := by
    exact Term.replace_append (t := andTerm s s') (u := s) (u' := s')
      (t' := andTerm s' s') (p := [0]) (q := q) (v := t) hsub_outer hrep hrep_outer
  have hstep_ctx : Step rules (andTerm s s') (andTerm s' s') := by
    refine ⟨rule_and_idem, rules_and_idem, [0] ++ q, (fun _ => t), ?_, ?_⟩
    · simpa [rule_and_idem, Term.subst] using hsub_ctx
    · simpa [rule_and_idem, Term.subst] using hrep_ctx
  have hstep_root : Step rules (andTerm s' s') s' := step_and_idem s'
  refine ⟨s', Rewriting.Star.single hstep, ?_⟩
  exact Rewriting.Star.tail (Rewriting.Star.single hstep_ctx) hstep_root

theorem rules_criticalPairsJoinable : CriticalPairsJoinable rules := by
  intro cp hcp
  rcases hcp with ⟨r1, r2, p, sub1, sub2, hr1, hr2, hover, hmk⟩
  rcases hr1 with rfl | rfl <;> rcases hr2 with rfl | rfl
  ·
    cases p with
    | nil =>
        have hoverEq : Term.subst sub1 rule_not_not.lhs = Term.subst sub2 rule_not_not.lhs := by
          simpa [Overlap] using hover
        have hsub := congrArg (fun t => Term.subterm t [0]) hoverEq
        have hvars : sub1 0 = sub2 0 := by
          have hsub' : (fun _ : Fin 1 => sub1 0) = fun _ : Fin 1 => sub2 0 := by
            simpa [rule_not_not, notTerm, Term.subst, Term.subterm, boolSig, boolArity, subst_xTerm] using hsub
          simpa using congrArg (fun f => f 0) hsub'
        simp [rule_not_not, mkCriticalPair] at hmk
        cases hmk
        exact joinable_of_eq (by simpa [Term.subst, hvars])
    | cons i ps =>
        cases i with
        | zero =>
            cases ps with
            | nil =>
                have hsub : sub1 0 = notTerm (sub2 0) := by
                  have hfun :
                      (fun _ : Fin 1 => sub1 0) = fun _ : Fin 1 => notTerm (sub2 0) := by
                    simpa [Overlap, rule_not_not, notTerm, Term.subst, Term.subterm, boolSig, boolArity, subst_xTerm]
                      using hover
                  simpa using congrArg (fun f => f 0) hfun
                simp [rule_not_not, mkCriticalPair] at hmk
                cases hmk
                exact joinable_of_eq (by simpa [hsub, notTerm, Term.subst])
            | cons j qs =>
                cases j with
                | zero =>
                    cases qs with
                    | nil =>
                        have hsub : sub1 0 = notTerm (notTerm (sub2 0)) := by
                          simpa [Overlap, rule_not_not, notTerm, Term.subst, Term.subterm, boolSig, boolArity,
                            subst_xTerm, subst_notTerm] using hover
                        simp [rule_not_not, mkCriticalPair] at hmk
                        cases hmk
                        exact joinable_of_eq (by simpa [hsub, notTerm, Term.subst])
                    | cons k ks =>
                        simp [Overlap, rule_not_not, notTerm, Term.subterm, Term.subst, boolSig, boolArity] at hover
                        cases hover
                | succ j =>
                    simp [Overlap, rule_not_not, notTerm, Term.subterm, Term.subst, boolSig, boolArity] at hover
                    cases hover
        | succ i =>
            simp [Overlap, rule_not_not, notTerm, Term.subterm, Term.subst, boolSig, boolArity] at hover
            cases hover
  ·
    cases p with
    | nil =>
        simp [Overlap, rule_not_not, rule_and_idem, notTerm, andTerm, Term.subterm, Term.subst, boolSig, boolArity] at hover
        cases hover
    | cons i ps =>
        cases i with
        | zero =>
            cases ps with
            | nil =>
                simp [Overlap, rule_not_not, rule_and_idem, notTerm, andTerm, Term.subterm, Term.subst, boolSig, boolArity] at hover
                cases hover
            | cons j qs =>
                cases j with
                | zero =>
                    cases qs with
                    | nil =>
                        have hsub : sub1 0 = andTerm (sub2 0) (sub2 0) := by
                          simpa [Overlap, rule_not_not, rule_and_idem, notTerm, andTerm, Term.subst,
                            Term.subterm, boolSig, boolArity, subst_andTerm, subst_xTerm] using hover
                        simp [rule_not_not, rule_and_idem, mkCriticalPair] at hmk
                        cases hmk
                        simpa [hsub, notTerm, andTerm, Term.subst] using
                          (joinable_and_not (t := sub2 0))
                    | cons k ks =>
                        simp [Overlap, rule_not_not, rule_and_idem, notTerm, andTerm, Term.subterm, Term.subst,
                          boolSig, boolArity] at hover
                        cases hover
                | succ j =>
                    simp [Overlap, rule_not_not, rule_and_idem, notTerm, andTerm, Term.subterm, Term.subst,
                      boolSig, boolArity] at hover
                    cases hover
        | succ i =>
            simp [Overlap, rule_not_not, rule_and_idem, notTerm, andTerm, Term.subterm, Term.subst, boolSig, boolArity] at hover
            cases hover
  ·
    cases p with
    | nil =>
        simp [Overlap, rule_and_idem, rule_not_not, notTerm, andTerm, Term.subterm, Term.subst, boolSig, boolArity,
          subst_andTerm, subst_xTerm] at hover
        cases hover
    | cons i ps =>
        cases ps with
        | nil =>
            cases i with
            | zero =>
                have hsub : sub1 0 = notTerm (notTerm (sub2 0)) := by
                  simpa [Overlap, rule_not_not, rule_and_idem, notTerm, andTerm, Term.subst,
                    Term.subterm, boolSig, boolArity, subst_andTerm, subst_xTerm] using hover
                simp [rule_not_not, rule_and_idem, mkCriticalPair] at hmk
                cases hmk
                have hjoin := joinable_and_not_right (t := sub2 0)
                simpa [hsub, notTerm, andTerm, Term.subst] using (Rewriting.Joinable.symm hjoin)
            | succ i =>
                cases i with
                | zero =>
                    have hsub : sub1 0 = notTerm (notTerm (sub2 0)) := by
                      simpa [Overlap, rule_not_not, rule_and_idem, notTerm, andTerm, Term.subst,
                        Term.subterm, boolSig, boolArity, subst_andTerm, subst_xTerm] using hover
                    simp [rule_not_not, rule_and_idem, mkCriticalPair] at hmk
                    cases hmk
                    have hjoin := joinable_and_not_left (t := sub2 0)
                    simpa [hsub, notTerm, andTerm, Term.subst] using (Rewriting.Joinable.symm hjoin)
                | succ i =>
                    simp [Overlap, rule_not_not, rule_and_idem, notTerm, andTerm, Term.subterm, Term.subst,
                      boolSig, boolArity, subst_andTerm, subst_xTerm] at hover
                    cases hover
        | cons j qs =>
            simp [Overlap, rule_not_not, rule_and_idem, notTerm, andTerm, Term.subterm, Term.subst,
              boolSig, boolArity, subst_andTerm, subst_xTerm] at hover
            cases hover
  ·
    cases p with
    | nil =>
        have hoverEq : Term.subst sub1 rule_and_idem.lhs = Term.subst sub2 rule_and_idem.lhs := by
          simpa [Overlap] using hover
        have hsub := congrArg (fun t => Term.subterm t [0]) hoverEq
        have hvars : sub1 0 = sub2 0 := by
          have hsub' : (fun _ : Fin 1 => sub1 0) = fun _ : Fin 1 => sub2 0 := by
            simpa [rule_and_idem, andTerm, Term.subst, Term.subterm, boolSig, boolArity, subst_xTerm] using hsub
          simpa using congrArg (fun f => f 0) hsub'
        simp [rule_and_idem, mkCriticalPair] at hmk
        cases hmk
        exact joinable_of_eq (by simpa [Term.subst, hvars])
    | cons i ps =>
        cases ps with
        | nil =>
            cases i with
            | zero =>
                have hsub : sub1 0 = andTerm (sub2 0) (sub2 0) := by
                  simpa [Overlap, rule_and_idem, andTerm, Term.subst, Term.subterm, boolSig, boolArity, subst_xTerm,
                    subst_andTerm] using hover
                simp [rule_and_idem, mkCriticalPair] at hmk
                cases hmk
                have hjoin := joinable_and_nested_right (t := sub2 0)
                simpa [hsub, andTerm, Term.subst] using (Rewriting.Joinable.symm hjoin)
            | succ i =>
                cases i with
                | zero =>
                    have hsub : sub1 0 = andTerm (sub2 0) (sub2 0) := by
                      simpa [Overlap, rule_and_idem, andTerm, Term.subst, Term.subterm, boolSig, boolArity, subst_xTerm,
                        subst_andTerm] using hover
                    simp [rule_and_idem, mkCriticalPair] at hmk
                    cases hmk
                    have hjoin := joinable_and_nested_left (t := sub2 0)
                    simpa [hsub, andTerm, Term.subst] using (Rewriting.Joinable.symm hjoin)
                | succ i =>
                    have : False := by
                      simpa [Overlap, rule_and_idem, andTerm, Term.subterm, Term.subst, boolSig, boolArity, subst_xTerm,
                        subst_andTerm] using hover
                    exact this.elim
        | cons j qs =>
            cases i with
            | zero =>
                have hsub : Term.subterm (sub1 0) (j :: qs) =
                    some (andTerm (sub2 0) (sub2 0)) := by
                  simpa [Overlap, rule_and_idem, andTerm, Term.subterm, Term.subst, boolSig, boolArity, subst_xTerm,
                    subst_andTerm] using hover
                cases hrep : Term.replace (andTerm (sub1 0) (sub1 0)) (0 :: j :: qs) (sub2 0) with
                | none =>
                    simp [mkCriticalPair, rule_and_idem, andTerm, Term.subst] at hmk
                | some u =>
                    have hmk' := hmk
                    simp [mkCriticalPair, rule_and_idem, andTerm, Term.subst] at hmk'
                    cases hmk'
                    have hsub_root :
                        Term.subterm (andTerm (sub1 0) (sub1 0)) [0] = some (sub1 0) := by
                      simp [subterm_and_left]
                    rcases Term.replace_append_inv
                      (t := andTerm (sub1 0) (sub1 0)) (u := sub1 0) (p := [0]) (q := j :: qs)
                      (v := sub2 0) hsub_root hrep with ⟨s', hrep_inner, hrep_outer⟩
                    have hu : u = andTerm s' (sub1 0) := by
                      simpa [replace_and_left] using hrep_outer.symm
                    subst hu
                    exact joinable_and_context_right (s := sub1 0) (t := sub2 0)
                      (s' := s') (q := j :: qs) hsub hrep_inner
            | succ i =>
                cases i with
                | zero =>
                    have hsub : Term.subterm (sub1 0) (j :: qs) =
                        some (andTerm (sub2 0) (sub2 0)) := by
                      simpa [Overlap, rule_and_idem, andTerm, Term.subterm, Term.subst, boolSig, boolArity, subst_xTerm,
                        subst_andTerm] using hover
                    cases hrep : Term.replace (andTerm (sub1 0) (sub1 0)) (1 :: j :: qs) (sub2 0) with
                    | none =>
                        simp [mkCriticalPair, rule_and_idem, andTerm, Term.subst] at hmk
                    | some u =>
                        have hmk' := hmk
                        simp [mkCriticalPair, rule_and_idem, andTerm, Term.subst] at hmk'
                        cases hmk'
                        have hsub_root :
                            Term.subterm (andTerm (sub1 0) (sub1 0)) [1] = some (sub1 0) := by
                          simp [subterm_and_right]
                        rcases Term.replace_append_inv
                          (t := andTerm (sub1 0) (sub1 0)) (u := sub1 0) (p := [1]) (q := j :: qs)
                          (v := sub2 0) hsub_root hrep with ⟨s', hrep_inner, hrep_outer⟩
                        have hu : u = andTerm (sub1 0) s' := by
                          simpa [replace_and_right] using hrep_outer.symm
                        subst hu
                        exact joinable_and_context_left (s := sub1 0) (t := sub2 0)
                          (s' := s') (q := j :: qs) hsub hrep_inner
                | succ i =>
                    have : False := by
                      simpa [Overlap, rule_and_idem, andTerm, Term.subterm, Term.subst, boolSig, boolArity, subst_xTerm,
                        subst_andTerm] using hover
                    exact this.elim

/-! ## Knuth-Bendix Certificate -/

theorem boolean_knuthBendixComplete :
    KnuthBendixComplete (rules := rules) (stableSizeOrdering boolSig) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases hr with rfl | rfl <;> simp [rule_not_not, rule_and_idem, notTerm, andTerm, NonVarLHS, NonVar, IsVar]
  · exact rules_oriented
  · exact rules_criticalPairsJoinable

theorem boolean_confluent : Confluent rules :=
  confluent_of_knuthBendixComplete boolean_knuthBendixComplete

end Metatheory.TRS.FirstOrder

-/

end Metatheory.TRS.FirstOrder
