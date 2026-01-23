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

abbrev DPChain {sig : Signature} [DecidableEq sig.Sym] (rules : RuleList sig) :
    Term sig → Term sig → Prop :=
  Rewriting.Plus (DPStep (sig := sig) rules)

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

end Metatheory.TRS.FirstOrder
