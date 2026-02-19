/-
# First-Order TRS Examples

A tiny ground TRS example with a Knuth-Bendix completion certificate.
-/

import Metatheory.TRS.FirstOrder.Confluence
import Metatheory.TRS.FirstOrder.Ordering
import Metatheory.TRS.FirstOrder.DependencyPairs

namespace Metatheory.TRS.FirstOrder

/- TODO: Fix after Ordering/DependencyPairs are restored

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
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases hr with rfl | rfl <;> simp [rule1, rule2, fTerm, NonVarLHS, NonVar, IsVar]
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
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    rcases hr with rfl | rfl <;> simp [kboRule1, kboRule2, fKbo, gKbo, NonVarLHS, NonVar, IsVar]
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
  · intro r hr
    rcases hr with rfl
    simp [lpoRule, appTerm, NonVarLHS, NonVar, IsVar]
  · exact lpo_rules_terminating
  · exact lpo_rules_criticalPairsJoinable

end Metatheory.TRS.FirstOrder

/-! ## Matrix Interpretation Example -/

namespace Metatheory.TRS.FirstOrder

open Term

inductive MatSym : Type
  | a
  | f
  deriving DecidableEq

def matArity : MatSym -> Nat
  | .a => 0
  | .f => 1

def matSig : Signature :=
  { Sym := MatSym, arity := matArity }

def aMat : Term matSig :=
  Term.app MatSym.a (fun i => i.elim0)

def fMat (t : Term matSig) : Term matSig :=
  Term.app MatSym.f (fun _ => t)

def matRule : Rule matSig :=
  { lhs := fMat aMat, rhs := aMat }

def matRules : RuleSet matSig :=
  fun r => r = matRule

def matM : Mat2Lower :=
  { a11 := 2
    a21 := 0
    a22 := 1
    a11_pos := by decide
    a22_pos := by decide }

def matInterp : MatrixInterpretation matSig :=
  { w0 := (1, 0)
    wf := fun
      | .a => (1, 0)
      | .f => (0, 0)
    mat := by
      intro f
      cases f with
      | a =>
          intro i
          exact (i.elim0)
      | f =>
          intro _
          exact matM }

theorem matRule_oriented :
    stableMatrixLt (sig := matSig) matInterp matRule.rhs matRule.lhs := by
  intro sub
  have hlt : vec2Lt (1, 0) (2, 0) :=
    Prod.Lex.left _ _ (by decide)
  simpa [matRule, aMat, fMat, matInterp, matrixWeight, vec2Add, vec2Sum, vec2Lt, matArity,
    Term.subst, Term.finSum, matMul] using hlt

theorem matRules_oriented :
    ∀ r, matRules r → stableMatrixLt (sig := matSig) matInterp r.rhs r.lhs := by
  intro r hr
  cases hr
  exact matRule_oriented

theorem matRules_terminating : Terminating matRules :=
  terminating_of_matrix (rules := matRules) matInterp matRules_oriented

end Metatheory.TRS.FirstOrder

/-! ## Dependency Pair Example -/

namespace Metatheory.TRS.FirstOrder

open Term

inductive DpSym : Type
  | a
  | f

def dpArity : DpSym -> Nat
  | .a => 0
  | .f => 1

def dpSig : Signature :=
  { Sym := DpSym, arity := dpArity }

def aDp : Term dpSig :=
  Term.app DpSym.a (fun i => i.elim0)

def fDp (t : Term dpSig) : Term dpSig :=
  Term.app DpSym.f (fun _ => t)

def dpRule : Rule dpSig :=
  { lhs := fDp aDp, rhs := aDp }

def dpRules : RuleSet dpSig :=
  fun r => r = dpRule

def dpRuleList : RuleList dpSig := [dpRule]

def dpWeights : Weighting dpSig :=
  { w0 := 1
    wf := fun
      | .a => 1
      | .f => 2 }

theorem dp_rule_oriented :
    stableWeightLt (sig := dpSig) dpWeights dpRule.rhs dpRule.lhs := by
  intro sub
  have hpos : 0 < dpWeights.wf DpSym.f := by decide
  simpa [dpRule, fDp, aDp, stableWeightLt, Term.subst, dpArity, weight, Term.finSum] using
    (Nat.lt_add_of_pos_left (weight dpWeights (sub 0)) hpos)

theorem dp_rules_oriented :
    ∀ r, dpRules r → stableWeightLt (sig := dpSig) dpWeights r.rhs r.lhs := by
  intro r hr
  cases hr
  exact dp_rule_oriented

theorem dp_rules_terminating : Terminating dpRules :=
  terminating_of_kbo (rules := dpRules) dpWeights dp_rules_oriented

theorem dp_dependencyPairs_terminating :
    Terminating (ruleSetOfList (sig := dpSig) (dependencyPairRules (sig := dpSig) dpRuleList)) := by
  apply terminating_of_dependencyPairs_ordering (ord := kboOrdering dpSig dpWeights)
  intro r hr
  -- No dependency pairs for this rule list
  simp [dependencyPairRules, dependencyPairsOfRules, dependencyPairsOfRule, dpRuleList, dpRule,
    fDp, aDp, dpArity, rootSym, DefinedSym, DefinedTerm, ruleSetOfList] at hr

end Metatheory.TRS.FirstOrder

/-! ## Non-Confluent Example -/

namespace Metatheory.TRS.FirstOrder

open Term

inductive NcSym : Type
  | a
  | b
  | c
  deriving DecidableEq

def ncArity : NcSym -> Nat
  | .a => 0
  | .b => 0
  | .c => 0

def ncSig : Signature :=
  { Sym := NcSym, arity := ncArity }

def aNc : Term ncSig := Term.app NcSym.a (fun i => i.elim0)
def bNc : Term ncSig := Term.app NcSym.b (fun i => i.elim0)
def cNc : Term ncSig := Term.app NcSym.c (fun i => i.elim0)

@[simp] lemma subst_aNc (sub : Subst ncSig) : Term.subst sub aNc = aNc := by
  simp [aNc, Term.subst, ncArity]

@[simp] lemma subst_bNc (sub : Subst ncSig) : Term.subst sub bNc = bNc := by
  simp [bNc, Term.subst, ncArity]

@[simp] lemma subst_cNc (sub : Subst ncSig) : Term.subst sub cNc = cNc := by
  simp [cNc, Term.subst, ncArity]

def rule_ab : Rule ncSig := { lhs := aNc, rhs := bNc }
def rule_ac : Rule ncSig := { lhs := aNc, rhs := cNc }

def ncRules : RuleSet ncSig := fun r => r = rule_ab ∨ r = rule_ac

lemma step_a_b : Step ncRules aNc bNc := by
  have hr : ncRules rule_ab := by simp [ncRules]
  simpa [rule_ab] using step_of_rule (rules := ncRules) rule_ab hr Term.idSubst

lemma step_a_c : Step ncRules aNc cNc := by
  have hr : ncRules rule_ac := by simp [ncRules]
  simpa [rule_ac] using step_of_rule (rules := ncRules) rule_ac hr Term.idSubst

lemma bNc_ne_cNc : bNc ≠ cNc := by
  intro h
  cases h

lemma no_step_b (t : Term ncSig) : ¬ Step ncRules bNc t := by
  intro hstep
  rcases hstep with ⟨r, hr, p, sub, hsub, _⟩
  rcases hr with rfl | rfl
  all_goals
    cases p with
    | nil =>
        have hEq : Term.subst sub aNc = bNc := by
          simpa [bNc, Term.subterm] using hsub
        have : aNc = bNc := by simpa using hEq
        cases this
    | cons i ps =>
        simp [bNc, Term.subterm, ncArity] at hsub

lemma no_step_c (t : Term ncSig) : ¬ Step ncRules cNc t := by
  intro hstep
  rcases hstep with ⟨r, hr, p, sub, hsub, _⟩
  rcases hr with rfl | rfl
  all_goals
    cases p with
    | nil =>
        have hEq : Term.subst sub aNc = cNc := by
          simpa [cNc, Term.subterm] using hsub
        have : aNc = cNc := by simpa using hEq
        cases this
    | cons i ps =>
        simp [cNc, Term.subterm, ncArity] at hsub

lemma bNc_normal : Rewriting.IsNormalForm (Step ncRules) bNc := by
  intro t hstep
  exact (no_step_b t hstep)

lemma cNc_normal : Rewriting.IsNormalForm (Step ncRules) cNc := by
  intro t hstep
  exact (no_step_c t hstep)

theorem nc_not_confluent : ¬ Confluent ncRules := by
  intro hconf
  have hb : Rewriting.Star (Step ncRules) aNc bNc := Rewriting.Star.single step_a_b
  have hc : Rewriting.Star (Step ncRules) aNc cNc := Rewriting.Star.single step_a_c
  rcases hconf aNc bNc cNc hb hc with ⟨d, hbd, hcd⟩
  have hbEq : bNc = d := Rewriting.star_normalForm_eq hbd bNc_normal
  have hcEq : cNc = d := Rewriting.star_normalForm_eq hcd cNc_normal
  have : bNc = cNc := by simpa [hbEq, hcEq]
  exact bNc_ne_cNc this

end Metatheory.TRS.FirstOrder

/-! ## Non-Terminating Example -/

namespace Metatheory.TRS.FirstOrder

open Term

inductive NtSym : Type
  | a
  | f
  deriving DecidableEq

def ntArity : NtSym -> Nat
  | .a => 0
  | .f => 1

def ntSig : Signature :=
  { Sym := NtSym, arity := ntArity }

def aNt : Term ntSig := Term.app NtSym.a (fun i => i.elim0)
def fNt (t : Term ntSig) : Term ntSig := Term.app NtSym.f (fun _ => t)

def ntRule : Rule ntSig := { lhs := aNt, rhs := fNt aNt }

def ntRules : RuleSet ntSig := fun r => r = ntRule

lemma step_a_fa : Step ntRules aNt (fNt aNt) := by
  have hr : ntRules ntRule := by simp [ntRules]
  simpa [ntRule] using step_of_rule (rules := ntRules) ntRule hr Term.idSubst

lemma step_fa_ffa : Step ntRules (fNt aNt) (fNt (fNt aNt)) := by
  have hr : ntRules ntRule := by simp [ntRules]
  refine ⟨ntRule, hr, [0], Term.idSubst, ?_, ?_⟩
  · simp [ntRule, aNt, fNt, Term.subterm, ntArity]
  · simp [ntRule, aNt, fNt, Term.replace, ntArity]

theorem nt_loop : Rewriting.Plus (Step ntRules) aNt aNt := by
  refine Rewriting.Plus.tail (Rewriting.Plus.tail (Rewriting.Plus.single step_a_fa) step_fa_ffa) ?_
  -- close the loop via the same pattern in the leftmost position
  have hr : ntRules ntRule := by simp [ntRules]
  refine ⟨ntRule, hr, [0, 0], Term.idSubst, ?_, ?_⟩
  · simp [ntRule, aNt, fNt, Term.subterm, ntArity]
  · simp [ntRule, aNt, fNt, Term.replace, ntArity]

theorem nt_not_terminating : ¬ Terminating ntRules := by
  intro hterm
  have hloop : Rewriting.Plus (Step ntRules) aNt aNt := nt_loop
  exact (hterm.isIrrefl.irrefl aNt) hloop

end Metatheory.TRS.FirstOrder

-/

end Metatheory.TRS.FirstOrder
