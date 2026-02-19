/-
# Knuth-Bendix Completion (Abstract)

This module provides a lightweight, abstract completion relation that
adds oriented critical pairs as rewrite rules. Soundness is delegated
to the critical-pair infrastructure.

Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import Metatheory.Rewriting.Basic
import Metatheory.TRS.FirstOrder.Confluence
import Metatheory.TRS.FirstOrder.CriticalPairs


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

namespace Metatheory.TRS.FirstOrder

open Term

/-! ## Completion Steps -/

/-- Add a rule to a rule set. -/
def addRule {sig : Signature} (rules : RuleSet sig) (r0 : Rule sig) : RuleSet sig :=
  fun r => rules r ∨ r = r0

/-- A critical pair is oriented by an ordering into a rule. -/
def Oriented {sig : Signature} (ord : ReductionOrdering sig)
    (cp : CriticalPair sig) (r : Rule sig) : Prop :=
  (r.lhs = cp.left ∧ r.rhs = cp.right ∧ ord.lt cp.right cp.left) ∨
  (r.lhs = cp.right ∧ r.rhs = cp.left ∧ ord.lt cp.left cp.right)

/-- Oriented rules satisfy the ordering direction. -/
theorem oriented_lt {sig : Signature} {ord : ReductionOrdering sig}
    {cp : CriticalPair sig} {r : Rule sig} (h : Oriented ord cp r) :
    ord.lt r.rhs r.lhs := by
  rcases h with ⟨hl, hr, hlt⟩ | ⟨hl, hr, hlt⟩
  · simpa [hl, hr] using hlt
  · simpa [hl, hr] using hlt

/-- One completion step: orient a critical pair into a new rule. -/
inductive CompletionStep {sig : Signature} (ord : ReductionOrdering sig) :
    RuleSet sig → RuleSet sig → Prop where
  | orient {rules : RuleSet sig} {cp : CriticalPair sig} {r : Rule sig} :
      CriticalPairs rules cp → Oriented ord cp r →
      CompletionStep ord rules (addRule rules r)

/-- Reflexive-transitive closure of completion steps. -/
abbrev Completion {sig : Signature} (ord : ReductionOrdering sig) :
    RuleSet sig → RuleSet sig → Prop :=
  Rewriting.Star (CompletionStep ord)

/-! ## Soundness -/

/-- If completion yields a Knuth-Bendix complete system, it is confluent. -/
theorem completion_sound {sig : Signature} {ord : ReductionOrdering sig}
    {rules rules' : RuleSet sig}
    (_hcomp : Completion ord rules rules')
    (hkb : KnuthBendixComplete (rules := rules') ord) :
    Confluent rules' := by
  exact confluent_of_knuthBendixComplete hkb

/-! ## List-based Completion -/

/-- Orient a critical pair using a reduction ordering. -/
noncomputable def orientCriticalPair {sig : Signature} (ord : ReductionOrdering sig)
    (cp : CriticalPair sig) : Option (Rule sig) := by
  classical
  by_cases h : ord.lt cp.right cp.left
  · exact some { lhs := cp.left, rhs := cp.right }
  by_cases h' : ord.lt cp.left cp.right
  · exact some { lhs := cp.right, rhs := cp.left }
  exact none

theorem orientCriticalPair_oriented {sig : Signature} {ord : ReductionOrdering sig}
    {cp : CriticalPair sig} {r : Rule sig} :
    orientCriticalPair ord cp = some r → Oriented ord cp r := by
  classical
  unfold orientCriticalPair
  by_cases h : ord.lt cp.right cp.left
  · intro hr
    simp [h] at hr
    cases hr
    exact Or.inl ⟨rfl, rfl, h⟩
  ·
    by_cases h' : ord.lt cp.left cp.right
    · intro hr
      simp [h, h'] at hr
      cases hr
      exact Or.inr ⟨rfl, rfl, h'⟩
    ·
      intro hr
      simp [h, h'] at hr

/-- Orient all critical pairs from a list. -/
noncomputable def orientCriticalPairs {sig : Signature} (ord : ReductionOrdering sig)
    (cps : List (CriticalPair sig)) : List (Rule sig) :=
  cps.filterMap (orientCriticalPair ord)

/-- One batch completion step on a finite rule list. -/
noncomputable def completionStepList {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) (rules : RuleList sig) : RuleList sig :=
  rules ++ orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules)

/-- Iterate the list-based completion step `n` times. -/
noncomputable def completionIter {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) : Nat → RuleList sig → RuleList sig
  | 0, rules => rules
  | n + 1, rules => completionIter ord n (completionStepList ord rules)

theorem mem_completionStepList {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {r : Rule sig} :
    r ∈ completionStepList ord rules →
    r ∈ rules ∨ ∃ cp, cp ∈ criticalPairsOfRules (sig := sig) rules ∧
      orientCriticalPair ord cp = some r := by
  intro hmem
  have hmem' := List.mem_append.1 hmem
  rcases hmem' with hmem' | hmem'
  · exact Or.inl hmem'
  ·
    rcases List.mem_filterMap.1 hmem' with ⟨cp, hcp, horient⟩
    exact Or.inr ⟨cp, hcp, horient⟩

theorem completionStepList_oriented {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {r : Rule sig} :
    r ∈ completionStepList ord rules →
    r ∈ rules ∨ ∃ cp, cp ∈ criticalPairsOfRules (sig := sig) rules ∧ Oriented ord cp r := by
  intro hmem
  rcases mem_completionStepList (ord := ord) (rules := rules) hmem with hmem' | hmem'
  · exact Or.inl hmem'
  ·
    rcases hmem' with ⟨cp, hcp, horient⟩
    exact Or.inr ⟨cp, hcp, orientCriticalPair_oriented horient⟩

/-! ## Fixpoint Detection -/

/-- A completion step is trivial if it adds no new rules. -/
def isFixpoint {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) (rules : RuleList sig) : Prop :=
  ∀ r, r ∈ orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules) → r ∈ rules

/-- If isFixpoint holds, completionStepList returns the same rules (up to duplicates). -/
theorem completionStepList_fixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules) :
    ∀ r, r ∈ completionStepList ord rules ↔ r ∈ rules := by
  intro r
  constructor
  · intro hmem
    rcases List.mem_append.1 hmem with hmem' | hmem'
    · exact hmem'
    · exact hfix r hmem'
  · intro hmem
    exact List.mem_append_left _ hmem

/-- Fixpoints are preserved by a completion step. -/
theorem isFixpoint_completionStepList {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules) :
    isFixpoint ord (completionStepList ord rules) := by
  intro r hr
  rcases List.mem_filterMap.1 hr with ⟨cp, hcp, horient⟩
  have hsubset : ∀ r, r ∈ completionStepList ord rules → r ∈ rules := by
    intro r hr'
    exact (completionStepList_fixpoint (ord := ord) (rules := rules) hfix r).1 hr'
  have hcp' : cp ∈ criticalPairsOfRules (sig := sig) rules :=
    criticalPairsOfRules_mono (rules := completionStepList ord rules) (rules' := rules) hsubset cp hcp
  have hr' : r ∈ orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules) :=
    List.mem_filterMap.2 ⟨cp, hcp', horient⟩
  have hrules : r ∈ rules := hfix r hr'
  exact List.mem_append.2 (Or.inl hrules)

/-- If a fixpoint is not reached, completion strictly increases the rule list length. -/
theorem completionStepList_length_lt_of_not_fixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    ¬ isFixpoint ord rules → rules.length < (completionStepList ord rules).length := by
  intro hnot
  classical
  rcases Classical.not_forall.1 hnot with ⟨r, hr⟩
  rcases Classical.not_imp.1 hr with ⟨hmem, _⟩
  have hlen :
      0 < (orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules)).length :=
    List.length_pos_of_mem hmem
  have hlt : rules.length <
      rules.length + (orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules)).length :=
    Nat.lt_add_of_pos_right hlen
  simpa [completionStepList, List.length_append] using hlt

/-- One iteration unfolds to a single completion step. -/
theorem completionIter_succ_eq_step {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} (n : Nat) (rules : RuleList sig) :
    completionIter ord (n + 1) rules =
      completionStepList ord (completionIter ord n rules) := by
  induction n generalizing rules with
  | zero =>
      simp [completionIter]
  | succ n ih =>
      calc
        completionIter ord (Nat.succ (Nat.succ n)) rules
            = completionIter ord (Nat.succ n) (completionStepList ord rules) := by
                simp [completionIter]
        _ = completionStepList ord (completionIter ord n (completionStepList ord rules)) := by
                simpa using (ih (rules := completionStepList ord rules))
        _ = completionStepList ord (completionIter ord (Nat.succ n) rules) := by
                simp [completionIter]

/-- If a step is not a fixpoint, the completion iteration strictly grows in length. -/
theorem completionIter_length_lt_succ_of_not_fixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {n : Nat} :
    ¬ isFixpoint ord (completionIter ord n rules) →
    (completionIter ord n rules).length < (completionIter ord (n + 1) rules).length := by
  intro hnot
  have hlt :=
    completionStepList_length_lt_of_not_fixpoint (ord := ord)
      (rules := completionIter ord n rules) hnot
  simpa [completionIter_succ_eq_step (ord := ord) (n := n) (rules := rules)] using hlt

/- If all earlier iterations are not fixpoints, lengths grow by at least the step count. -/
noncomputable section AristotleLemmas

/-
If a sequence of natural numbers strictly increases at each step up to n, then the n-th term is at least the 0-th term plus n.
-/
lemma nat_seq_growth_bound (f : Nat → Nat) (n : Nat) :
    (∀ m < n, f m < f (m + 1)) → f 0 + n ≤ f n := by
      introv h;
      by_contra h_contra;
      -- By definition of negation, there exists some $k$ such that $f k < f 0 + k$ and $k$ is minimal.
      obtain ⟨k, hk_min⟩ : ∃ k, 0 ≤ k ∧ k ≤ n ∧ f k < f 0 + k ∧ ∀ j, 0 ≤ j → j < k → f j ≥ f 0 + j := by
        have hk_min : ∃ k, 0 ≤ k ∧ k ≤ n ∧ f k < f 0 + k ∧ ∀ j, 0 ≤ j → j < k → f j ≥ f 0 + j := by
          have h_exists : ∃ k, 0 ≤ k ∧ k ≤ n ∧ f k < f 0 + k := by
            grind
          exact ⟨ Nat.find h_exists, Nat.find_spec h_exists |>.1, Nat.find_spec h_exists |>.2.1, Nat.find_spec h_exists |>.2.2, fun j hj₁ hj₂ => not_lt.1 fun hj₃ => Nat.find_min h_exists hj₂ ⟨ hj₁, by linarith [ Nat.find_spec h_exists |>.2.1 ], hj₃ ⟩ ⟩;
        exact hk_min;
      rcases k with ( _ | k ) <;> simp +arith +decide at *;
      linarith [ h k ( by linarith ), hk_min.2.2 k le_rfl ]

end AristotleLemmas

theorem completionIter_length_lower_bound {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    ∀ n, (∀ m < n, ¬ isFixpoint ord (completionIter ord m rules)) →
      rules.length + n ≤ (completionIter ord n rules).length := by
  intros n hn; exact (by
  convert nat_seq_growth_bound _ _ _;
  rotate_left;
  rotate_left;
  use fun m => List.length ( Metatheory.TRS.FirstOrder.completionIter ord m rules );
  · exact?;
  · rfl;
  · rfl)

theorem completionIter_fixpoint_succ {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {n : Nat} :
    isFixpoint ord (completionIter ord n rules) →
    isFixpoint ord (completionIter ord (n + 1) rules) := by
  -- By definition of `completionIter`, if `isFixpoint ord (completionIter ord n rules)` holds, then `completionIter ord (n + 1) rules` is just `completionIter ord n rules` itself.
  have h_step : completionIter ord (n + 1) rules = completionStepList ord (completionIter ord n rules) := by
    exact?
  generalize_proofs at *; (
  -- By definition of `completionStepList`, if the current set is a fixpoint, then adding more rules from the critical pairs (which are already in the rules) would still be a fixpoint.
  intros hfix
  rw [h_step]
  apply isFixpoint_completionStepList hfix)

theorem completionIter_fixpoint_of_le {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {n m : Nat} :
    n ≤ m →
    isFixpoint ord (completionIter ord n rules) →
    isFixpoint ord (completionIter ord m rules) := by
  -- By induction on $k$, we can show that if the $n$th iterate is a fixpoint, then the $(n+k)$th iterate is also a fixpoint.
  have h_ind : ∀ k, isFixpoint ord (Metatheory.TRS.FirstOrder.completionIter ord n rules) → isFixpoint ord (Metatheory.TRS.FirstOrder.completionIter ord (n + k) rules) := by
    -- By induction on $k$, we can show that if the $n$th iterate is a fixpoint, then the $(n+k)$th iterate is also a fixpoint. We'll use the fact that if the $n$th iterate is a fixpoint, then the $(n+1)$th iterate is also a fixpoint.
    have h_ind_step : ∀ n, isFixpoint ord (Metatheory.TRS.FirstOrder.completionIter ord n rules) → isFixpoint ord (Metatheory.TRS.FirstOrder.completionIter ord (n + 1) rules) := by
      -- Apply the hypothesis `h_fixpoint_step` directly.
      apply Metatheory.TRS.FirstOrder.completionIter_fixpoint_succ;
    exact fun k hk => Nat.recOn k hk fun k ih => h_ind_step _ ih |> fun h => by simpa only [ Nat.add_succ ] using h;
  generalize_proofs at *; (
  exact fun hmn h => by simpa only [ add_tsub_cancel_of_le hmn ] using h_ind ( m - n ) h;)

theorem completionIter_fixpoint_of_bounded {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {bound : Nat}
    (hbound : ∀ n, (completionIter ord n rules).length ≤ bound) :
    ∃ n ≤ bound, isFixpoint ord (completionIter ord n rules) := by
  -- By contradiction, assume there is no fixpoint.
  by_contra h_no_fixpoint;
  -- If there's no fixpoint, then the length of the rule list must strictly increase with each iteration.
  have h_length_increasing : ∀ n ≤ bound, List.length (Metatheory.TRS.FirstOrder.completionIter ord n rules) ≥ rules.length + n := by
    -- Apply the fact that if n ≤ bound, then the length is at least rules.length + n by using the hypothesis h_length_increasing.
    intros n hn
    apply Metatheory.TRS.FirstOrder.completionIter_length_lower_bound n (fun m hm => by
      grind);
  linarith [ hbound bound, h_length_increasing bound le_rfl, hbound ( bound + 1 ), List.length_pos_iff.mpr ( show rules ≠ [ ] from by rintro rfl; exact h_no_fixpoint ⟨ 0, by norm_num, by
                                                                                                              unfold Metatheory.TRS.FirstOrder.isFixpoint; aesop; ⟩ ) ]

/-! ## Universe Bounds -/

/-- A finite universe of rules closed under completion steps. -/
structure RuleUniverse (sig : Signature) [DecidableEq sig.Sym] where
  univ : RuleList sig
  closed : ∀ {ord : ReductionOrdering sig} {rules : RuleList sig},
    (∀ r, r ∈ rules → r ∈ univ) →
    ∀ r, r ∈ completionStepList ord rules → r ∈ univ

/-- Rule universe defined by a decidable predicate on rules. -/
def RuleUniverse.ofPred {sig : Signature} [DecidableEq sig.Sym]
    (p : Rule sig → Prop) [DecidablePred p] (univ : RuleList sig)
    (hmem : ∀ r, r ∈ univ ↔ p r)
    (hclosed : ∀ {ord : ReductionOrdering sig} {rules : RuleList sig},
      (∀ r, r ∈ rules → p r) →
      ∀ r, r ∈ completionStepList ord rules → p r) :
    RuleUniverse sig :=
  { univ := univ
    closed := by
      intro ord rules hsubset r hmem'
      have : p r := hclosed (ord := ord) (rules := rules) (fun r hr => (hmem r).1 (hsubset r hr)) r hmem'
      exact (hmem r).2 this }

/-- If the initial rules are in the universe, all completion iterations stay in the universe. -/
theorem completionIter_subset_universe {sig : Signature} [DecidableEq sig.Sym]
    (U : RuleUniverse sig) {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hsubset : ∀ r, r ∈ rules → r ∈ U.univ) :
    ∀ n r, r ∈ completionIter ord n rules → r ∈ U.univ := by
  intro n
  induction n generalizing rules with
  | zero =>
      intro r hmem
      simpa [completionIter] using hsubset r hmem
  | succ n ih =>
      intro r hmem
      simp only [completionIter] at hmem
      have hsubset' : ∀ r, r ∈ completionIter ord n (completionStepList ord rules) → r ∈ U.univ := by
        intro r hr
        exact ih (rules := completionStepList ord rules)
          (fun r hr => U.closed (ord := ord) (rules := rules) hsubset r hr) r hr
      exact hsubset' r hmem

/-- If each completion iteration is nodup and stays within a universe list, its length is bounded. -/
theorem completionIter_length_le_of_subset {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {univ : RuleList sig}
    (hnodup : ∀ n, (completionIter ord n rules).Nodup)
    (hsubset : ∀ n, ∀ r, r ∈ completionIter ord n rules → r ∈ univ) :
    ∀ n, (completionIter ord n rules).length ≤ univ.length := by
  intro n
  have h_subset : (Metatheory.TRS.FirstOrder.completionIter ord n rules).toFinset ⊆ univ.toFinset := by
    intro r hr
    aesop;
  have := Finset.card_le_card h_subset; rw [ List.toFinset_card_of_nodup ( hnodup n ) ] at this; exact this.trans ( List.toFinset_card_le _ ) ;

theorem completionIter_fixpoint_of_universe {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {univ : RuleList sig}
    (hnodup : ∀ n, (completionIter ord n rules).Nodup)
    (hsubset : ∀ n, ∀ r, r ∈ completionIter ord n rules → r ∈ univ) :
    ∃ n ≤ univ.length, isFixpoint ord (completionIter ord n rules) := by
  refine completionIter_fixpoint_of_bounded (ord := ord) (rules := rules)
    (bound := univ.length) ?_
  intro n
  exact completionIter_length_le_of_subset (ord := ord) (rules := rules) (univ := univ) hnodup hsubset n

/-- Completion result: either completed or ran out of fuel. -/
inductive CompletionResult (sig : Signature) where
  | complete : RuleList sig → CompletionResult sig
  | incomplete : RuleList sig → CompletionResult sig

/-- Completion with bounded iterations (fuel). -/
noncomputable def completionWithFuel {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) : Nat → RuleList sig → CompletionResult sig
  | 0, rules => CompletionResult.incomplete rules
  | n + 1, rules => by
      classical
      exact if h : isFixpoint ord rules then
        CompletionResult.complete rules
      else
        completionWithFuel ord n (completionStepList ord rules)

noncomputable section AristotleLemmas

/-
Unfolding lemma for completionWithFuel.
-/
section
open Classical

theorem completionWithFuel_succ {sig : Signature} [DecidableEq sig.Sym]
    (ord : ReductionOrdering sig) (n : Nat) (rules : RuleList sig) :
    completionWithFuel ord (n + 1) rules =
      if isFixpoint ord rules then
        CompletionResult.complete rules
      else
        completionWithFuel ord n (completionStepList ord rules) := by
          exact?

end

/-
Helper lemma: if completion succeeds on the next step, it succeeds on the current step (with more fuel).
-/
section
open Classical

theorem completionWithFuel_recurse {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {n : Nat}
    (h : ∃ res, completionWithFuel ord n (completionStepList ord rules) = CompletionResult.complete res) :
    ∃ res, completionWithFuel ord (n + 1) rules = CompletionResult.complete res := by
      by_cases h' : isFixpoint ord rules <;> simp_all +decide [ completionWithFuel_succ ]

end

/-
Decidability instance for isFixpoint using classical logic, to support if-then-else in completionWithFuel lemmas.
-/
open Metatheory.TRS.FirstOrder

noncomputable instance instDecidableIsFixpoint {sig : Signature} [DecidableEq sig.Sym] (ord : ReductionOrdering sig) (rules : RuleList sig) : Decidable (isFixpoint ord rules) := Classical.dec _

/-
Base case for completionWithFuel correctness: if already a fixpoint, 1 step of fuel is enough.
-/
theorem completionWithFuel_base {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (h : isFixpoint ord rules) :
    ∃ res, completionWithFuel ord 1 rules = CompletionResult.complete res := by
      exact ⟨ rules, by rw [ completionWithFuel_succ ] ; exact if_pos h ⟩

/-
Inductive step for completionWithFuel correctness.
-/
theorem completionWithFuel_complete_step {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {n : Nat}
    (IH : ∀ rules, isFixpoint ord (completionIter ord n rules) →
      ∃ res, completionWithFuel ord (n + 1) rules = CompletionResult.complete res) :
    ∀ rules, isFixpoint ord (completionIter ord (n + 1) rules) →
      ∃ res, completionWithFuel ord (n + 2) rules = CompletionResult.complete res := by
        exact?

end AristotleLemmas

theorem completionWithFuel_complete_of_iter_fixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    ∀ n, isFixpoint ord (completionIter ord n rules) →
      ∃ result, completionWithFuel ord (n + 1) rules = CompletionResult.complete result := by
  intro n;
  induction n <;> simp_all +decide [ completionWithFuel_succ ];
  · exact?;
  · have := @completionWithFuel_complete_step;
    intro h;
    convert this _ _ h using 1;
    rename_i n ih;
    refine' Nat.recOn n _ _ <;> simp_all +decide [ completionWithFuel_succ ];
    exact?

theorem completionWithFuel_complete_of_universe {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {univ : RuleList sig}
    (hnodup : ∀ n, (completionIter ord n rules).Nodup)
    (hsubset : ∀ n, ∀ r, r ∈ completionIter ord n rules → r ∈ univ) :
    ∃ result,
      completionWithFuel ord (univ.length + 1) rules = CompletionResult.complete result := by
  -- Apply the hypothesis `hcompletion` with `n` being the length of `univ`.
  obtain ⟨n, hn⟩ : ∃ n ≤ univ.length, isFixpoint ord (completionIter ord n rules) := by
    -- Apply the hypothesis `hfixpoint` with the given hypotheses `hsubset` and `hnodup`.
    apply completionIter_fixpoint_of_universe hnodup hsubset;
  -- By definition of `completionWithFuel`, if the steps reach a fixpoint at `n`, then `completionWithFuel` with `n + 1` iterations will return the complete result.
  have h_completion : ∀ n, isFixpoint ord (completionIter ord n rules) → ∃ result, completionWithFuel ord (n + 1) rules = CompletionResult.complete result := by
    -- By definition of `completionWithFuel`, if the steps reach a fixpoint at `n`, then `completionWithFuel` with `n + 1` iterations will return the complete result. This follows directly from the definition of `completionWithFuel`.
    intros n hn
    apply completionWithFuel_complete_of_iter_fixpoint n hn;
  have h_completion : ∀ m ≥ n, isFixpoint ord (completionIter ord m rules) := by
    exact fun m hm => completionIter_fixpoint_of_le hm hn.2;
  exact ‹∀ n, Metatheory.TRS.FirstOrder.isFixpoint ord ( Metatheory.TRS.FirstOrder.completionIter ord n rules ) → ∃ result, Metatheory.TRS.FirstOrder.completionWithFuel ord ( n + 1 ) rules = Metatheory.TRS.FirstOrder.CompletionResult.complete result› _ ( h_completion _ ( by linarith ) ) |> fun ⟨ result, hresult ⟩ => ⟨ result, hresult ⟩

noncomputable section AristotleLemmas

/-
All rules generated during completion iterations are oriented by the reduction ordering, provided the initial rules are.
-/
theorem completionIter_oriented {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hord : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs) :
    ∀ n r, r ∈ completionIter ord n rules → ord.lt r.rhs r.lhs := by
      intro n;
      induction n;
      · exact?;
      · intro r hr
        rw [completionIter_succ_eq_step] at hr;
        rename_i n ih;
        exact ( completionStepList_oriented hr ) |> Or.rec ( fun h => h |> fun h => ih r h ) fun h => h |> fun ⟨ cp, hcp₁, hcp₂ ⟩ => ( oriented_lt hcp₂ )

/-
If a rule list is a fixpoint of completion and all its critical pairs are orientable, then all critical pairs are joinable.
-/
theorem criticalPairsJoinable_of_fixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules)
    (hcomplete : ∀ cp, CriticalPairs (ruleSetOfList (sig := sig) rules) cp →
      cp ∈ criticalPairsOfRules (sig := sig) rules)
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) rules →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    CriticalPairsJoinable (ruleSetOfList (sig := sig) rules) := by
      intro cp hcp
      obtain ⟨r, hr⟩ : ∃ r : Rule sig, r ∈ rules ∧ (r.lhs = cp.left ∧ r.rhs = cp.right ∨ r.lhs = cp.right ∧ r.rhs = cp.left) := by
        obtain ⟨r, hr⟩ : ∃ r : Rule sig, r ∈ rules ∧ (r.lhs = cp.left ∧ r.rhs = cp.right ∨ r.lhs = cp.right ∧ r.rhs = cp.left) := by
          have h_bound : cp ∈ criticalPairsOfRules (sig := sig) rules := hcomplete cp hcp
          have h_or : orientCriticalPair ord cp ≠ none := by
            unfold orientCriticalPair; specialize horient cp h_bound; aesop;
          obtain ⟨r, hr⟩ : ∃ r : Rule sig, orientCriticalPair ord cp = some r := by
            exact Option.ne_none_iff_exists'.mp h_or;
          exact ⟨ r, hfix r ( by
            exact List.mem_filterMap.mpr ⟨ cp, h_bound, hr ⟩ ), by
            unfold orientCriticalPair at hr; aesop; ⟩;
        exact ⟨ r, hr ⟩;
      -- Since `r` is in `rules`, we can apply the step relation to get `Step (ruleSetOfList rules) r.lhs r.rhs`.
      have h_step : Step (ruleSetOfList rules) r.lhs r.rhs := by
        constructor;
        constructor;
        exact hr.1;
        use [];
        use Term.idSubst;
        simp +decide [ Term.subst_id ];
      cases hr.2 <;> simp_all +decide [ Metatheory.TRS.FirstOrder.Joinable ];
      · exact?;
      · constructor;
        constructor;
        constructor;
        exact .single h_step

end AristotleLemmas

theorem completionIter_confluent_of_universe {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {univ : RuleList sig}
    (hnodup : ∀ n, (completionIter ord n rules).Nodup)
    (hsubset : ∀ n, ∀ r, r ∈ completionIter ord n rules → r ∈ univ)
    (hord : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (hnvl : ∀ n, NonVarLHS (ruleSetOfList (sig := sig) (completionIter ord n rules)))
    (hcomplete : ∀ n cp, CriticalPairs (ruleSetOfList (sig := sig) (completionIter ord n rules)) cp →
      cp ∈ criticalPairsOfRules (sig := sig) (completionIter ord n rules))
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) univ →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    ∃ n, Confluent (ruleSetOfList (sig := sig) (completionIter ord n rules)) := by
  have := @Metatheory.TRS.FirstOrder.completionIter_fixpoint_of_universe;
  rename_i h;
  obtain ⟨ n, hn₁, hn₂ ⟩ := @this sig h ord rules univ hnodup hsubset;
  use n;
  apply Metatheory.TRS.FirstOrder.confluent_of_terminating_criticalPairsJoinable (hnvl n);
  · apply Metatheory.TRS.FirstOrder.terminating_of_ordering;
    apply_rules [ completionIter_oriented ];
  · apply Metatheory.TRS.FirstOrder.criticalPairsJoinable_of_fixpoint hn₂;
    · exact hcomplete n;
    · intro cp hcp;
      apply horient;
      exact?

/-! ## Completion with Fuel -/

/-- If completion succeeds, the result is a fixpoint. -/
theorem completionWithFuel_complete_isFixpoint {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result) :
    isFixpoint ord result := by
  induction fuel generalizing rules with
  | zero =>
      simp [completionWithFuel] at h
  | succ n ih =>
      classical
      by_cases hfix : isFixpoint ord rules
      · simp [completionWithFuel, hfix] at h
        cases h
        exact hfix
      · simp [completionWithFuel, hfix] at h
        exact ih h

/-- If completion runs out of fuel, the result is the `fuel`-step iteration. -/
theorem completionWithFuel_incomplete_eq_iter {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (h : completionWithFuel ord fuel rules = CompletionResult.incomplete result) :
    result = completionIter ord fuel rules := by
  have h_fuel : ∀ fuel, ∀ rules, completionWithFuel ord fuel rules = CompletionResult.incomplete result → result = completionIter ord fuel rules := by
    intros fuel rules h; induction fuel generalizing rules <;> simp_all +decide [ Metatheory.TRS.FirstOrder.completionWithFuel, Metatheory.TRS.FirstOrder.completionIter ] ;
    split_ifs at h ; tauto;
  exact h_fuel fuel rules h

theorem completionWithFuel_complete_exists_iter {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result) :
    ∃ k ≤ fuel, result = completionIter ord k rules := by
  induction fuel generalizing rules result with
  | zero =>
      simp [completionWithFuel] at h
  | succ n ih =>
      classical
      by_cases hfix : isFixpoint ord rules
      · simp [completionWithFuel, hfix] at h
        cases h
        refine ⟨0, Nat.zero_le _, ?_⟩
        simp [completionIter]
      · simp [completionWithFuel, hfix] at h
        rcases ih (rules := completionStepList ord rules) (result := result) h with ⟨k, hk, hres⟩
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
        simpa [completionIter] using hres

/-- If completion terminates, it does so at some iteration. -/
theorem completion_terminates_of_iter {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules result : RuleList sig} {fuel : Nat}
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result) :
    ∃ n, result = completionIter ord n rules := by
  rcases completionWithFuel_complete_exists_iter (ord := ord) (rules := rules) (result := result) h with
    ⟨n, _, hres⟩
  exact ⟨n, hres⟩

/-! ## Completion Correctness -/

/-- Rules only grow during completion. -/
theorem completionStepList_subset {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    ∀ r, r ∈ rules → r ∈ completionStepList ord rules := by
  intro r hmem
  exact List.mem_append_left _ hmem

/-- Iterated completion preserves subset. -/
theorem completionIter_subset {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {n : Nat} :
    ∀ r, r ∈ rules → r ∈ completionIter ord n rules := by
  induction n generalizing rules with
  | zero => simp [completionIter]
  | succ n ih =>
      intro r hmem
      simp only [completionIter]
      apply ih
      exact completionStepList_subset (r := r) hmem

/-- All rules in each completion iteration satisfy the ordering. -/
theorem completionIter_oriented {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} :
    (∀ r, r ∈ rules → ord.lt r.rhs r.lhs) →
    ∀ n r, r ∈ completionIter ord n rules → ord.lt r.rhs r.lhs := by
  intro hinit n
  induction n generalizing rules with
  | zero =>
      intro r hmem
      simpa [completionIter] using hinit r hmem
  | succ n ih =>
      intro r hmem
      simp only [completionIter] at hmem
      have hinit' : ∀ r, r ∈ completionStepList ord rules → ord.lt r.rhs r.lhs := by
        intro r hr
        rcases completionStepList_oriented (ord := ord) (rules := rules) hr with hmem' | ⟨cp, _, horient⟩
        · exact hinit r hmem'
        · exact oriented_lt horient
      exact ih (rules := completionStepList ord rules) hinit' r hmem

/-- All rules in a completed system satisfy the ordering. -/
theorem completionWithFuel_oriented {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (hinit : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result) :
    ∀ r, r ∈ result → ord.lt r.rhs r.lhs := by
  induction fuel generalizing rules with
  | zero => simp [completionWithFuel] at h
  | succ n ih =>
      classical
      simp only [completionWithFuel] at h
      split at h
      · case isTrue hfix =>
          injection h with heq
          rw [← heq]
          exact hinit
      · case isFalse hfix =>
          apply ih _ h
          intro r hmem
          rcases completionStepList_oriented (ord := ord) (rules := rules) hmem with hmem' | ⟨cp, _, horient⟩
          · exact hinit r hmem'
          · exact oriented_lt horient

/-! ## Fixpoint Soundness -/

/-- At a fixpoint, every oriented critical pair is already a rule. -/
theorem fixpoint_oriented_mem {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules)
    {cp : CriticalPair sig} {r : Rule sig}
    (hcp : cp ∈ criticalPairsOfRules (sig := sig) rules)
    (horient : orientCriticalPair ord cp = some r) :
    r ∈ rules := by
  have hmem : r ∈ orientCriticalPairs ord (criticalPairsOfRules (sig := sig) rules) := by
    exact List.mem_filterMap.2 ⟨cp, hcp, horient⟩
  exact hfix r hmem

/-- If a critical pair is orientable at a fixpoint, it is joinable by one step. -/
theorem joinable_of_fixpoint_orientable {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {cp : CriticalPair sig}
    (hfix : isFixpoint ord rules)
    (hcp : cp ∈ criticalPairsOfRules (sig := sig) rules)
    (horient : ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    Joinable (ruleSetOfList (sig := sig) rules) cp.left cp.right := by
  classical
  by_cases hgt : ord.lt cp.right cp.left
  ·
    let r : Rule sig := { lhs := cp.left, rhs := cp.right }
    have horient' : orientCriticalPair ord cp = some r := by
      simp [orientCriticalPair, hgt, r]
    have hrule : r ∈ rules := fixpoint_oriented_mem (ord := ord) (rules := rules) hfix hcp horient'
    have hstep : Step (ruleSetOfList (sig := sig) rules) cp.left cp.right := by
      have hstep' := step_of_rule (rules := ruleSetOfList (sig := sig) rules) r hrule Term.idSubst
      simpa [r, Term.subst_id] using hstep'
    exact ⟨cp.right, Rewriting.Star.single hstep, Rewriting.Star.refl _⟩
  ·
    have hlt : ord.lt cp.left cp.right := by
      cases horient with
      | inl hgt' => exact (hgt hgt').elim
      | inr hlt => exact hlt
    let r : Rule sig := { lhs := cp.right, rhs := cp.left }
    have horient' : orientCriticalPair ord cp = some r := by
      simp [orientCriticalPair, hgt, hlt, r]
    have hrule : r ∈ rules := fixpoint_oriented_mem (ord := ord) (rules := rules) hfix hcp horient'
    have hstep : Step (ruleSetOfList (sig := sig) rules) cp.right cp.left := by
      have hstep' := step_of_rule (rules := ruleSetOfList (sig := sig) rules) r hrule Term.idSubst
      simpa [r, Term.subst_id] using hstep'
    exact ⟨cp.left, Rewriting.Star.refl _, Rewriting.Star.single hstep⟩

/-- If all critical pairs are orientable and the list is complete, a fixpoint gives joinability. -/
theorem criticalPairsJoinable_of_fixpoint_orientable {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules)
    (hcomplete : ∀ cp, CriticalPairs (ruleSetOfList (sig := sig) rules) cp →
      cp ∈ criticalPairsOfRules (sig := sig) rules)
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) rules →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    CriticalPairsJoinable (ruleSetOfList (sig := sig) rules) := by
  intro cp hcp
  have hmem := hcomplete cp hcp
  have hor := horient cp hmem
  exact joinable_of_fixpoint_orientable (ord := ord) (rules := rules) hfix hmem hor

/-- Fixpoint certificates yield Knuth-Bendix completeness under orientability and completeness. -/
theorem knuthBendixComplete_of_fixpoint_orientable {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig}
    (hfix : isFixpoint ord rules)
    (hnvl : NonVarLHS (ruleSetOfList (sig := sig) rules))
    (hord : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (hcomplete : ∀ cp, CriticalPairs (ruleSetOfList (sig := sig) rules) cp →
      cp ∈ criticalPairsOfRules (sig := sig) rules)
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) rules →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    KnuthBendixComplete (ruleSetOfList (sig := sig) rules) ord := by
  refine ⟨hnvl, ?_, ?_⟩
  · intro r hr
    exact hord r hr
  · exact criticalPairsJoinable_of_fixpoint_orientable (ord := ord) (rules := rules) hfix hcomplete horient

/-- Completion yields confluence when a fixpoint is reached and all critical pairs are orientable. -/
theorem completionWithFuel_confluent_of_orientable {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {fuel : Nat} {rules result : RuleList sig}
    (hinit : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (h : completionWithFuel ord fuel rules = CompletionResult.complete result)
    (hnvl : NonVarLHS (ruleSetOfList (sig := sig) result))
    (hcomplete : ∀ cp, CriticalPairs (ruleSetOfList (sig := sig) result) cp →
      cp ∈ criticalPairsOfRules (sig := sig) result)
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) result →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    Confluent (ruleSetOfList (sig := sig) result) := by
  have hfix : isFixpoint ord result :=
    completionWithFuel_complete_isFixpoint (ord := ord) (rules := rules) (result := result) h
  have hord : ∀ r, r ∈ result → ord.lt r.rhs r.lhs :=
    completionWithFuel_oriented (ord := ord) (rules := rules) (result := result) hinit h
  have hkb := knuthBendixComplete_of_fixpoint_orientable
    (ord := ord) (rules := result) hfix hnvl hord hcomplete horient
  exact confluent_of_knuthBendixComplete hkb

theorem completionWithFuel_confluent_of_universe {sig : Signature} [DecidableEq sig.Sym]
    {ord : ReductionOrdering sig} {rules : RuleList sig} {univ : RuleList sig}
    (hnodup : ∀ n, (completionIter ord n rules).Nodup)
    (hsubset : ∀ n, ∀ r, r ∈ completionIter ord n rules → r ∈ univ)
    (hord : ∀ r, r ∈ rules → ord.lt r.rhs r.lhs)
    (hnvl : ∀ r, r ∈ univ → NonVar r.lhs)
    (hcomplete : ∀ n cp, CriticalPairs (ruleSetOfList (sig := sig) (completionIter ord n rules)) cp →
      cp ∈ criticalPairsOfRules (sig := sig) (completionIter ord n rules))
    (horient : ∀ cp, cp ∈ criticalPairsOfRules (sig := sig) univ →
      ord.lt cp.right cp.left ∨ ord.lt cp.left cp.right) :
    ∃ result,
      completionWithFuel ord (univ.length + 1) rules = CompletionResult.complete result ∧
      Confluent (ruleSetOfList (sig := sig) result) := by
  obtain ⟨result, hresult⟩ : ∃ result : Metatheory.TRS.FirstOrder.RuleList sig, Metatheory.TRS.FirstOrder.completionWithFuel ord (univ.length + 1) rules = Metatheory.TRS.FirstOrder.CompletionResult.complete result := by
    have := Metatheory.TRS.FirstOrder.completionWithFuel_complete_of_universe ( sig := sig ) ( ord := ord ) ( rules := rules ) ( hnodup := hnodup ) ( hsubset := hsubset ) ; aesop;
  refine' ⟨ result, hresult, _ ⟩;
  apply Metatheory.TRS.FirstOrder.completionWithFuel_confluent_of_orientable;
  · exact hord;
  · exact hresult;
  · intro r hr
    exact hnvl r (by
      obtain ⟨ n, hn ⟩ := completion_terminates_of_iter hresult
      exact hn ▸ hsubset n r (hn ▸ hr));
  · obtain ⟨ n, hn ⟩ := completion_terminates_of_iter hresult;
    aesop;
  · have hresult_subset : ∀ r, r ∈ result → r ∈ univ := by
      obtain ⟨ n, hn ⟩ := completion_terminates_of_iter hresult;
      exact hn ▸ hsubset n;
    intros cp hcp
    apply horient cp;
    exact?

end Metatheory.TRS.FirstOrder
