/-
# First-Order TRS Examples

A tiny ground TRS example with a Knuth-Bendix completion certificate.
-/

import Metatheory.TRS.FirstOrder.Confluence
import Metatheory.TRS.FirstOrder.Ordering

namespace Metatheory.TRS.FirstOrder

/-! ## Signature and Terms -/

/-- Symbols for a tiny ground signature. -/
inductive ExampleSym : Type
  | a
  | b
  | f

/-- Arity of the example symbols. -/
def exampleArity : ExampleSym -> Nat
  | .a => 0
  | .b => 0
  | .f => 1

/-- Example signature with constants `a`, `b` and unary `f`. -/
def exampleSig : Signature :=
  { Sym := ExampleSym, arity := exampleArity }

/-- Constant term `a`. -/
def aTerm : Term exampleSig :=
  Term.app ExampleSym.a (fun i => i.elim0)

/-- Constant term `b`. -/
def bTerm : Term exampleSig :=
  Term.app ExampleSym.b (fun i => i.elim0)

/-- Unary constructor `f`. -/
def fTerm (t : Term exampleSig) : Term exampleSig :=
  Term.app ExampleSym.f (fun _ => t)

/-! ## Rules -/

/-- Rule `f(a) → b`. -/
def rule1 : Rule exampleSig :=
  { lhs := fTerm aTerm, rhs := bTerm }

/-- Rule `f(b) → a`. -/
def rule2 : Rule exampleSig :=
  { lhs := fTerm bTerm, rhs := aTerm }

/-- Rule set containing the two example rules. -/
def rules : RuleSet exampleSig :=
  fun r => r = rule1 ∨ r = rule2

/-! ## Ordering Lemmas -/

/-- `b` is strictly smaller than `f(a)` in the stable size ordering. -/
theorem rule1_oriented :
    stableSizeLt (sig := exampleSig) rule1.rhs rule1.lhs := by
  intro sub
  simp [rule1, fTerm, aTerm, bTerm, Term.size, Term.subst, Term.finSum, exampleArity]

/-- `a` is strictly smaller than `f(b)` in the stable size ordering. -/
theorem rule2_oriented :
    stableSizeLt (sig := exampleSig) rule2.rhs rule2.lhs := by
  intro sub
  simp [rule2, fTerm, aTerm, bTerm, Term.size, Term.subst, Term.finSum, exampleArity]

/-- Orientation proof for all rules using the stable size ordering. -/
theorem rules_oriented :
    ∀ r, rules r → stableSizeLt (sig := exampleSig) r.rhs r.lhs := by
  intro r hr
  rcases hr with rfl | rfl
  · exact rule1_oriented
  · exact rule2_oriented

/-! ## Critical Pairs -/

/-- The example rules have trivially joinable critical pairs. -/
theorem rules_criticalPairsJoinable : CriticalPairsJoinable rules := by
  intro cp hcp
  rcases hcp with ⟨r1, r2, p, sub1, sub2, hr1, hr2, hover, hmk⟩
  rcases hr1 with rfl | rfl <;> rcases hr2 with rfl | rfl
  all_goals
    have hsub : Term.subterm (Term.subst sub1 r1.lhs) p = some (Term.subst sub2 r2.lhs) := hover
    have hoverEq : Term.subst sub1 r1.lhs = Term.subst sub2 r2.lhs := by
      simpa using hsub
    cases p with
    | nil =>
        simp [rule1, rule2, mkCriticalPair] at hmk
        cases hmk
        exact Rewriting.Joinable.refl (Step rules) _
    | cons i ps =>
        simp [rule1, rule2, fTerm, aTerm, bTerm, Term.subterm, exampleArity] at hsub

/-! ## Knuth-Bendix Certificate -/

/-- Knuth-Bendix completion certificate for the example system. -/
theorem example_knuthBendixComplete :
    KnuthBendixComplete (rules := rules) (stableSizeOrdering exampleSig) := by
  refine ⟨?_, ?_⟩
  · exact rules_oriented
  · exact rules_criticalPairsJoinable

/-- The example TRS is confluent. -/
theorem example_confluent : Confluent rules :=
  confluent_of_knuthBendixComplete example_knuthBendixComplete

end Metatheory.TRS.FirstOrder

/-! ## KBO Example -/

namespace Metatheory.TRS.FirstOrder

open Term

/-! ### Signature and Terms -/

inductive KboSym : Type
  | f
  | g

def kboArity : KboSym -> Nat
  | .f => 1
  | .g => 1

def kboSig : Signature :=
  { Sym := KboSym, arity := kboArity }

def fKbo (t : Term kboSig) : Term kboSig :=
  Term.app KboSym.f (fun _ => t)

def gKbo (t : Term kboSig) : Term kboSig :=
  Term.app KboSym.g (fun _ => t)

def xKbo : Term kboSig :=
  Term.var 0

@[simp] lemma subterm_fKbo (t : Term kboSig) :
    Term.subterm (fKbo t) [0] = some t := by
  simp [fKbo, Term.subterm, kboArity]

@[simp] lemma subterm_gKbo (t : Term kboSig) :
    Term.subterm (gKbo t) [0] = some t := by
  simp [gKbo, Term.subterm, kboArity]

@[simp] lemma replace_fKbo (t u : Term kboSig) :
    Term.replace (fKbo t) [0] u = some (fKbo u) := by
  simp [fKbo, Term.replace, kboArity]

@[simp] lemma replace_gKbo (t u : Term kboSig) :
    Term.replace (gKbo t) [0] u = some (gKbo u) := by
  simp [gKbo, Term.replace, kboArity]

/-! ### Rules -/

def kboRule1 : Rule kboSig :=
  { lhs := fKbo xKbo, rhs := gKbo xKbo }

def kboRule2 : Rule kboSig :=
  { lhs := gKbo xKbo, rhs := xKbo }

def kboRules : RuleSet kboSig :=
  fun r => r = kboRule1 ∨ r = kboRule2

@[simp] lemma kbo_rules_rule1 : kboRules kboRule1 := by
  simp [kboRules]

@[simp] lemma kbo_rules_rule2 : kboRules kboRule2 := by
  simp [kboRules]

/-! ### KBO Ordering -/

def kboWeights : Weighting kboSig :=
  { w0 := 1
    wf := fun
      | .f => 2
      | .g => 1 }

@[simp] lemma weight_fKbo (t : Term kboSig) :
    weight kboWeights (fKbo t) = kboWeights.wf KboSym.f + weight kboWeights t := by
  simp [weight, fKbo, kboArity, Term.finSum, kboWeights]

@[simp] lemma weight_gKbo (t : Term kboSig) :
    weight kboWeights (gKbo t) = kboWeights.wf KboSym.g + weight kboWeights t := by
  simp [weight, gKbo, kboArity, Term.finSum, kboWeights]

theorem kbo_rule1_oriented :
    stableWeightLt (sig := kboSig) kboWeights kboRule1.rhs kboRule1.lhs := by
  intro sub
  have hfg : kboWeights.wf KboSym.g < kboWeights.wf KboSym.f := by decide
  simpa [stableWeightLt, kboRule1, Term.subst] using
    (Nat.add_lt_add_right hfg (weight kboWeights (sub 0)))

theorem kbo_rule2_oriented :
    stableWeightLt (sig := kboSig) kboWeights kboRule2.rhs kboRule2.lhs := by
  intro sub
  have hpos : 0 < kboWeights.wf KboSym.g := by decide
  simpa [stableWeightLt, kboRule2, Term.subst] using
    (Nat.lt_add_of_pos_left (weight kboWeights (sub 0)) hpos)

theorem kbo_rules_oriented :
    ∀ r, kboRules r → stableWeightLt (sig := kboSig) kboWeights r.rhs r.lhs := by
  intro r hr
  rcases hr with rfl | rfl
  · exact kbo_rule1_oriented
  · exact kbo_rule2_oriented

/-! ### Critical Pairs -/

lemma kbo_joinable_of_eq {s t : Term kboSig} (h : s = t) :
    Rewriting.Joinable (Step kboRules) s t := by
  subst h
  exact Rewriting.Joinable.refl (Step kboRules) _

lemma joinable_gg_f (t : Term kboSig) :
    Rewriting.Joinable (Step kboRules) (gKbo (gKbo t)) (fKbo t) := by
  refine ⟨gKbo t, ?_, ?_⟩
  ·
    have hstep :=
      step_of_rule kboRule2 kbo_rules_rule2 (fun _ => gKbo t)
    have hstep' : Step kboRules (gKbo (gKbo t)) (gKbo t) := by
      simpa [kboRule2, gKbo, Term.subst] using hstep
    exact Rewriting.Star.single hstep'
  ·
    have hstep :=
      step_of_rule kboRule1 kbo_rules_rule1 (fun _ => t)
    have hstep' : Step kboRules (fKbo t) (gKbo t) := by
      simpa [kboRule1, fKbo, gKbo, Term.subst] using hstep
    exact Rewriting.Star.single hstep'

lemma joinable_gf_fg (t : Term kboSig) :
    Rewriting.Joinable (Step kboRules) (gKbo (fKbo t)) (fKbo (gKbo t)) := by
  refine ⟨gKbo t, ?_, ?_⟩
  ·
    have hstep1 :=
      step_of_rule kboRule2 kbo_rules_rule2 (fun _ => fKbo t)
    have hstep1' : Step kboRules (gKbo (fKbo t)) (fKbo t) := by
      simpa [kboRule2, gKbo, fKbo, Term.subst] using hstep1
    have hstep2 :=
      step_of_rule kboRule1 kbo_rules_rule1 (fun _ => t)
    have hstep2' : Step kboRules (fKbo t) (gKbo t) := by
      simpa [kboRule1, fKbo, gKbo, Term.subst] using hstep2
    exact Rewriting.Star.tail (Rewriting.Star.single hstep1') hstep2'
  ·
    have hstep1 :=
      step_of_rule kboRule1 kbo_rules_rule1 (fun _ => gKbo t)
    have hstep1' : Step kboRules (fKbo (gKbo t)) (gKbo (gKbo t)) := by
      simpa [kboRule1, fKbo, gKbo, Term.subst] using hstep1
    have hstep2 :=
      step_of_rule kboRule2 kbo_rules_rule2 (fun _ => gKbo t)
    have hstep2' : Step kboRules (gKbo (gKbo t)) (gKbo t) := by
      simpa [kboRule2, gKbo, Term.subst] using hstep2
    exact Rewriting.Star.tail (Rewriting.Star.single hstep1') hstep2'

theorem kbo_rules_criticalPairsJoinable : CriticalPairsJoinable kboRules := by
  intro cp hcp
  rcases hcp with ⟨r1, r2, p, sub1, sub2, hr1, hr2, hover, hmk⟩
  rcases hr1 with rfl | rfl <;> rcases hr2 with rfl | rfl
  ·
    cases p with
    | nil =>
        have hoverEq : Term.subst sub1 kboRule1.lhs = Term.subst sub2 kboRule1.lhs := by
          simpa using hover
        have hsub := congrArg (fun t => Term.subterm t [0]) hoverEq
        have hvars : sub1 0 = sub2 0 := by
          simpa [kboRule1, fKbo, Term.subst, Term.subterm, kboArity] using hsub
        simp [kboRule1, mkCriticalPair] at hmk
        cases hmk
        exact kbo_joinable_of_eq (by simpa [gKbo, Term.subst, hvars])
    | cons i ps =>
        cases ps with
        | nil =>
            cases i with
            | zero =>
                have hsub : sub1 0 = fKbo (sub2 0) := by
                  simpa [kboRule1, fKbo, Term.subst, Term.subterm, kboArity] using hover
                simp [kboRule1, mkCriticalPair] at hmk
                cases hmk
                simpa [hsub, fKbo, gKbo, Term.subst] using
                  (joinable_gf_fg (t := sub2 0))
            | succ i =>
                simp [kboRule1, Term.subterm, kboArity] at hover
        | cons j qs =>
            simp [kboRule1, Term.subterm, kboArity] at hover
  ·
    cases p with
    | nil =>
        have hoverEq : Term.subst sub1 kboRule1.lhs = Term.subst sub2 kboRule2.lhs := by
          simpa using hover
        cases hoverEq
    | cons i ps =>
        cases ps with
        | nil =>
            cases i with
            | zero =>
                have hsub : sub1 0 = gKbo (sub2 0) := by
                  simpa [kboRule1, kboRule2, fKbo, gKbo, Term.subst, Term.subterm, kboArity] using hover
                simp [kboRule1, kboRule2, mkCriticalPair] at hmk
                cases hmk
                simpa [hsub, fKbo, gKbo, Term.subst] using
                  (joinable_gg_f (t := sub2 0))
            | succ i =>
                simp [kboRule1, kboRule2, Term.subterm, kboArity] at hover
        | cons j qs =>
            simp [kboRule1, kboRule2, Term.subterm, kboArity] at hover
  ·
    cases p with
    | nil =>
        have hoverEq : Term.subst sub1 kboRule2.lhs = Term.subst sub2 kboRule1.lhs := by
          simpa using hover
        cases hoverEq
    | cons i ps =>
        cases ps with
        | nil =>
            cases i with
            | zero =>
                have hsub : sub1 0 = fKbo (sub2 0) := by
                  simpa [kboRule1, kboRule2, fKbo, gKbo, Term.subst, Term.subterm, kboArity] using hover
                simp [kboRule1, kboRule2, mkCriticalPair] at hmk
                cases hmk
                have hjoin := joinable_gg_f (t := sub2 0)
                exact Rewriting.Joinable.symm hjoin
            | succ i =>
                simp [kboRule1, kboRule2, Term.subterm, kboArity] at hover
        | cons j qs =>
            simp [kboRule1, kboRule2, Term.subterm, kboArity] at hover
  ·
    cases p with
    | nil =>
        have hoverEq : Term.subst sub1 kboRule2.lhs = Term.subst sub2 kboRule2.lhs := by
          simpa using hover
        have hsub := congrArg (fun t => Term.subterm t [0]) hoverEq
        have hvars : sub1 0 = sub2 0 := by
          simpa [kboRule2, gKbo, Term.subst, Term.subterm, kboArity] using hsub
        simp [kboRule2, mkCriticalPair] at hmk
        cases hmk
        exact kbo_joinable_of_eq (by simpa [Term.subst, hvars])
    | cons i ps =>
        cases ps with
        | nil =>
            cases i with
            | zero =>
                have hsub : sub1 0 = gKbo (sub2 0) := by
                  simpa [kboRule2, gKbo, Term.subst, Term.subterm, kboArity] using hover
                simp [kboRule2, mkCriticalPair] at hmk
                cases hmk
                exact kbo_joinable_of_eq (by simpa [hsub, gKbo, Term.subst])
            | succ i =>
                simp [kboRule2, Term.subterm, kboArity] at hover
        | cons j qs =>
            simp [kboRule2, Term.subterm, kboArity] at hover

/-! ### Knuth-Bendix Certificate -/

theorem kbo_knuthBendixComplete :
    KnuthBendixComplete (rules := kboRules) (kboOrdering kboSig kboWeights) := by
  refine ⟨?_, ?_⟩
  ·
    intro r hr
    exact kbo_rules_oriented r hr
  ·
    exact kbo_rules_criticalPairsJoinable

theorem kbo_example_confluent : Confluent kboRules :=
  confluent_of_knuthBendixComplete kbo_knuthBendixComplete

end Metatheory.TRS.FirstOrder

/-! ## LPO Example -/

namespace Metatheory.TRS.FirstOrder

open Term

/-! ### Signature and Terms -/

inductive LpoSym : Type
  | I
  | app

def lpoArity : LpoSym -> Nat
  | .I => 0
  | .app => 2

def lpoSig : Signature :=
  { Sym := LpoSym, arity := lpoArity }

def iTerm : Term lpoSig :=
  Term.app LpoSym.I (fun i => i.elim0)

def appTerm (t u : Term lpoSig) : Term lpoSig :=
  Term.app LpoSym.app (fun
    | ⟨0, _⟩ => t
    | ⟨1, _⟩ => u)

def xTerm : Term lpoSig := Term.var 0

/-! ### Rules -/

def lpoRule : Rule lpoSig :=
  { lhs := appTerm iTerm xTerm, rhs := xTerm }

def lpoRules : RuleSet lpoSig :=
  fun r => r = lpoRule

/-! ### Precedence -/

def lpoPrec : Precedence lpoSig where
  lt := fun f g => f = LpoSym.I ∧ g = LpoSym.app
  irrefl := by
    intro f h
    rcases h with ⟨rfl, h⟩
    cases h
  trans := by
    intro f g h hfg hgh
    rcases hfg with ⟨rfl, rfl⟩
    rcases hgh with ⟨h1, h2⟩
    cases h2
  wf := by
    classical
    refine ⟨?_, ?_⟩
    · intro f
      cases f with
      | I =>
          refine Acc.intro _ ?_
          intro y hy
          cases hy with
          | _ h =>
              cases h.1
      | app =>
          refine Acc.intro _ ?_
          intro y hy
          cases hy with
          | _ h =>
              cases h.1
    · intro a b h
      rcases h with ⟨h1, h2⟩
      cases h1

/-! ### LPO Orientation -/

theorem lpoRule_oriented : LPO lpoPrec lpoRule.lhs lpoRule.rhs := by
  dsimp [lpoRule, appTerm, iTerm, xTerm]
  -- subterm property: app(I, x) > x
  have : LPO lpoPrec (appTerm iTerm xTerm) (xTerm) := by
    simpa [appTerm] using (LPO.subEq (f := LpoSym.app)
      (args := fun
        | ⟨0, _⟩ => iTerm
        | ⟨1, _⟩ => xTerm)
      (i := ⟨1, by decide⟩))
  simpa [lpoRule] using this

theorem lpo_rules_oriented :
    ∀ r, lpoRules r → LPO lpoPrec r.rhs r.lhs := by
  intro r hr
  cases hr
  simpa [lpoRule_oriented]

/-! ### Termination -/

theorem lpo_rules_terminating : Terminating lpoRules := by
  apply terminating_of_lpo_single (prec := lpoPrec)
  intro r hr
  cases hr
  simpa [lpoRule_oriented]

/-! ### Critical Pairs -/

theorem lpo_rules_criticalPairsJoinable : CriticalPairsJoinable lpoRules := by
  intro cp hcp
  rcases hcp with ⟨r1, r2, p, sub1, sub2, hr1, hr2, hover, hmk⟩
  cases hr1
  cases hr2
  cases p with
  | nil =>
      simp [lpoRule, appTerm, iTerm, xTerm, mkCriticalPair] at hmk
      cases hmk
      exact Rewriting.Joinable.refl (Step lpoRules) _
  | cons i ps =>
      cases ps with
      | nil =>
          cases i with
          | zero =>
              simp [lpoRule, appTerm, iTerm, xTerm, Term.subterm, lpoArity] at hover
          | succ i =>
              cases i with
              | zero =>
                  simp [lpoRule, appTerm, iTerm, xTerm, Term.subterm, lpoArity] at hover
              | succ i =>
                  simp [lpoRule, appTerm, iTerm, xTerm, Term.subterm, lpoArity] at hover
      | cons j qs =>
          simp [lpoRule, appTerm, iTerm, xTerm, Term.subterm, lpoArity] at hover

theorem lpo_confluent : Confluent lpoRules := by
  apply confluent_of_terminating_criticalPairsJoinable
  · exact lpo_rules_terminating
  · exact lpo_rules_criticalPairsJoinable

end Metatheory.TRS.FirstOrder
