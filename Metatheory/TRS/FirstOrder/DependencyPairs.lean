/-
# Dependency Pairs for First-Order TRSs

Defines dependency pairs and a basic termination criterion for the
dependency pair relation induced by a rule list.
-/

import Metatheory.TRS.FirstOrder.CriticalPairs
import Metatheory.TRS.FirstOrder.Confluence

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Root Symbols and Defined Symbols -/

def rootSym {sig : Signature} : Term sig → Option sig.Sym
  | Term.var _ => none
  | Term.app f _ => some f

@[simp] theorem rootSym_var {sig : Signature} (x : Nat) :
    rootSym (sig := sig) (Term.var x) = none := by
  rfl

@[simp] theorem rootSym_app {sig : Signature} (f : sig.Sym)
    (args : Fin (sig.arity f) → Term sig) :
    rootSym (Term.app f args) = some f := by
  rfl

def DefinedSym {sig : Signature} (rules : RuleSet sig) (f : sig.Sym) : Prop :=
  ∃ r, rules r ∧ rootSym r.lhs = some f

def DefinedTerm {sig : Signature} (rules : RuleSet sig) (t : Term sig) : Prop :=
  ∃ f, rootSym t = some f ∧ DefinedSym rules f

/-! ## Dependency Pairs -/

structure DependencyPair (sig : Signature) where
  left : Term sig
  right : Term sig

def depPairRule {sig : Signature} (dp : DependencyPair sig) : Rule sig :=
  { lhs := dp.left, rhs := dp.right }

noncomputable def dependencyPairsOfRule {sig : Signature} [DecidableEq sig.Sym]
    (rules : RuleSet sig) (r : Rule sig) : List (DependencyPair sig) := by
  classical
  exact (Term.positions (sig := sig) r.rhs).filterMap (fun p =>
    match Term.subterm r.rhs p with
    | none => none
    | some t =>
        match rootSym t with
        | none => none
        | some f =>
            if h : DefinedSym rules f then
              some ⟨r.lhs, t⟩
            else none)

noncomputable def dependencyPairsOfRules {sig : Signature} [DecidableEq sig.Sym]
    (rules : RuleList sig) : List (DependencyPair sig) :=
  rules.flatMap (dependencyPairsOfRule (rules := ruleSetOfList (sig := sig) rules))

noncomputable def dependencyPairRules {sig : Signature} [DecidableEq sig.Sym]
    (rules : RuleList sig) : RuleList sig :=
  (dependencyPairsOfRules (sig := sig) rules).map depPairRule

abbrev DPStep {sig : Signature} [DecidableEq sig.Sym] (rules : RuleList sig) :
    Term sig → Term sig → Prop :=
  Step (ruleSetOfList (sig := sig) (dependencyPairRules (sig := sig) rules))

def DPChainStep {sig : Signature} [DecidableEq sig.Sym] (rules : RuleList sig) :
    Term sig → Term sig → Prop :=
  fun s t =>
    ∃ dp, dp ∈ dependencyPairsOfRules (sig := sig) rules ∧ ∃ sub,
      s = Term.subst sub dp.left ∧
        Rewriting.Star (Step (ruleSetOfList (sig := sig) rules))
          (Term.subst sub dp.right) t

abbrev DPChain {sig : Signature} [DecidableEq sig.Sym] (rules : RuleList sig) :
    Term sig → Term sig → Prop :=
  Rewriting.Plus (DPChainStep (sig := sig) rules)

/-! ## Termination for Dependency Pairs -/

theorem terminating_of_dependencyPairs_ordering {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hord : ∀ r, r ∈ dependencyPairRules (sig := sig) rules → ord.lt r.rhs r.lhs) :
    Terminating (ruleSetOfList (sig := sig) (dependencyPairRules (sig := sig) rules)) :=
  terminating_of_ordering (ord := ord) (rules := ruleSetOfList (sig := sig) (dependencyPairRules (sig := sig) rules)) hord

theorem terminating_of_rules_and_dependencyPairs_ordering {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hrules : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (_hdeps : ∀ r, r ∈ dependencyPairRules (sig := sig) rules → ord.lt r.rhs r.lhs) :
    Terminating (ruleSetOfList (sig := sig) rules) :=
  terminating_of_ordering (ord := ord) (rules := ruleSetOfList (sig := sig) rules) hrules

/-! ## Chain-Based Termination -/

theorem star_decreasing_of_ordering {sig : Signature} {rules : RuleSet sig}
    {ord : ReductionOrdering sig}
    (hord : ∀ r, rules r → ord.lt r.rhs r.lhs) :
    ∀ {s t : Term sig},
      Rewriting.Star (Step rules) s t → s = t ∨ ord.lt t s := by
  intro s t hstar
  induction hstar with
  | refl =>
      exact Or.inl rfl
  | tail hst hstep ih =>
      have hdec : ord.lt _ _ := step_decreasing_of_ordering (ord := ord) hord hstep
      cases ih with
      | inl hEq =>
          subst hEq
          exact Or.inr hdec
      | inr hlt =>
          exact Or.inr (ord.trans hdec hlt)

theorem plus_decreasing_of_relation {sig : Signature} {r : Term sig → Term sig → Prop}
    {lt : Term sig → Term sig → Prop} (htrans : Transitive lt)
    (hdec : ∀ {s t}, r s t → lt t s) :
    ∀ {s t}, Rewriting.Plus r s t → lt t s := by
  intro s t hplus
  induction hplus with
  | single hstep =>
      exact hdec hstep
  | tail hst hstep ih =>
      exact htrans (hdec hstep) ih

theorem dpChainStep_decreasing_of_ordering {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hrules : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (hdeps : ∀ r, r ∈ dependencyPairRules (sig := sig) rules → ord.lt r.rhs r.lhs) :
    ∀ {s t}, DPChainStep (sig := sig) rules s t → ord.lt t s := by
  intro s t hchain
  rcases hchain with ⟨dp, hdp, sub, rfl, hstar⟩
  have hdp' : ord.lt dp.right dp.left := by
    have hmem : depPairRule dp ∈ dependencyPairRules (sig := sig) rules := by
      have := List.mem_map_of_mem depPairRule hdp
      simpa [dependencyPairRules] using this
    simpa [depPairRule] using hdeps (depPairRule dp) hmem
  have hlt : ord.lt (Term.subst sub dp.right) (Term.subst sub dp.left) :=
    ord.subst_closed hdp'
  have hdec_star := star_decreasing_of_ordering
    (rules := ruleSetOfList (sig := sig) rules)
    (ord := ord) (fun r hr => hrules r hr)
  cases hdec_star (s := Term.subst sub dp.right) (t := t) hstar with
  | inl hEq =>
      subst hEq
      exact hlt
  | inr hlt' =>
      exact ord.trans hlt' hlt

theorem terminating_of_dpChain_ordering {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hrules : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (hdeps : ∀ r, r ∈ dependencyPairRules (sig := sig) rules → ord.lt r.rhs r.lhs) :
    Terminating (DPChainStep (sig := sig) rules) := by
  apply Subrelation.wf
  · intro a b hplus
    exact plus_decreasing_of_relation (lt := ord.lt) (htrans := ord.trans)
      (hdec := dpChainStep_decreasing_of_ordering (rules := rules) (ord := ord) hrules hdeps) hplus
  · exact ord.wf

end Metatheory.TRS.FirstOrder
