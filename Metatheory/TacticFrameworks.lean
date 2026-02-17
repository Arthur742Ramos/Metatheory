/-
  Metatheory / TacticFrameworks.lean

  Tactic Frameworks
  ===================

  Proof state = goal list, tactic = goal transformer, tactic combinators
  (then, orelse, repeat, try), focused proofs, zipper navigation,
  unification hints, auto tactics, reflection.

  All proofs are sorry-free.  Uses computational paths for proof state
  rewriting (tactic application steps as path steps).  20+ theorems.
-/

set_option linter.unusedVariables false

namespace TacticFrameworks

-- ============================================================
-- §1  Computational Paths
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _,    q => q
  | .cons s p, q => .cons s (p.trans q)

def Path.length : Path α a b → Nat
  | .nil _    => 0
  | .cons _ p => 1 + p.length

def Step.symm : Step α a b → Step α b a
  | .refl a     => .refl a
  | .rule n a b => .rule (n ++ "⁻¹") b a

def Path.symm : Path α a b → Path α b a
  | .nil a    => .nil a
  | .cons s p => p.symm.trans (.cons s.symm (.nil _))

def Path.single (s : Step α a b) : Path α a b :=
  .cons s (.nil _)

theorem path_trans_assoc (p : Path α a b) (q : Path α b c) (r : Path α c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

theorem path_length_trans (p : Path α a b) (q : Path α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [Path.trans, Path.length]
  | cons s _ ih => simp [Path.trans, Path.length, ih, Nat.add_assoc]

theorem path_trans_nil_right (p : Path α a b) :
    p.trans (.nil b) = p := by
  induction p with
  | nil _ => simp [Path.trans]
  | cons s _ ih => simp [Path.trans, ih]

-- ============================================================
-- §2  Propositions and Goals
-- ============================================================

/-- Simple propositions. -/
inductive Prop' where
  | atom  : Nat → Prop'
  | conj  : Prop' → Prop' → Prop'
  | disj  : Prop' → Prop' → Prop'
  | imp   : Prop' → Prop' → Prop'
  | neg   : Prop' → Prop'
  | top   : Prop'
  | bot   : Prop'
deriving DecidableEq, Repr

/-- A goal: hypotheses + conclusion. -/
structure Goal where
  hyps  : List Prop'
  concl : Prop'
deriving DecidableEq, Repr

/-- Proof state: list of open goals. -/
abbrev ProofState := List Goal

/-- Number of open goals. -/
def openGoals (ps : ProofState) : Nat := ps.length

/-- Theorem 1: Empty proof state has zero goals. -/
theorem empty_state_no_goals : openGoals [] = 0 := by rfl

/-- Theorem 2: Adding a goal increases count. -/
theorem add_goal_increases (g : Goal) (ps : ProofState) :
    openGoals (g :: ps) = openGoals ps + 1 := by
  simp [openGoals, List.length]

-- ============================================================
-- §3  Tactic = Goal Transformer
-- ============================================================

/-- A tactic result: either success (new subgoals) or failure. -/
inductive TacticResult where
  | success : ProofState → TacticResult
  | failure : String → TacticResult
deriving DecidableEq, Repr

/-- A tactic operates on a single goal. -/
def Tactic := Goal → TacticResult

/-- Apply tactic to first goal. -/
def applyFirst (t : Tactic) : ProofState → TacticResult
  | []      => .failure "no goals"
  | g :: gs =>
    match t g with
    | .success newGs => .success (newGs ++ gs)
    | .failure msg   => .failure msg

/-- Theorem 3: Applying to empty state fails. -/
theorem apply_empty_fails (t : Tactic) :
    applyFirst t [] = .failure "no goals" := by
  rfl

-- ============================================================
-- §4  Basic Tactics as Path Steps
-- ============================================================

/-- Proof state transitions. -/
def assumptionTac : Tactic := fun g =>
  if g.hyps.contains g.concl then .success []
  else .failure "assumption not found"

def introTac : Tactic := fun g =>
  match g.concl with
  | .imp a b => .success [{ hyps := a :: g.hyps, concl := b }]
  | _        => .failure "not an implication"

def splitTac : Tactic := fun g =>
  match g.concl with
  | .conj a b => .success [{ g with concl := a }, { g with concl := b }]
  | _         => .failure "not a conjunction"

def exactTopTac : Tactic := fun g =>
  match g.concl with
  | .top => .success []
  | _    => .failure "not top"

def exFalsoTac : Tactic := fun g =>
  if g.hyps.contains .bot then .success []
  else .failure "no bot in hyps"

/-- Theorem 4: Intro on implication produces one subgoal. -/
theorem intro_imp_one_subgoal (a b : Prop') (hyps : List Prop') :
    introTac { hyps := hyps, concl := .imp a b } =
    .success [{ hyps := a :: hyps, concl := b }] := by
  simp [introTac]

/-- Theorem 5: Split on conjunction produces two subgoals. -/
theorem split_conj_two_subgoals (a b : Prop') (hyps : List Prop') :
    splitTac { hyps := hyps, concl := .conj a b } =
    .success [{ hyps := hyps, concl := a }, { hyps := hyps, concl := b }] := by
  simp [splitTac]

/-- Theorem 6: exactTop on top succeeds with empty state. -/
theorem exact_top_closes (hyps : List Prop') :
    exactTopTac { hyps := hyps, concl := .top } = .success [] := by
  simp [exactTopTac]

-- ============================================================
-- §5  Tactic Combinators
-- ============================================================

/-- Sequential composition: apply t1 then t2 to each resulting goal. -/
def thenComb (t1 t2 : Tactic) : Tactic := fun g =>
  match t1 g with
  | .failure msg   => .failure msg
  | .success goals =>
    let results := goals.map t2
    if results.all (fun r => match r with | .success _ => true | _ => false)
    then
      let allGoals := results.foldl (fun acc r =>
        match r with | .success gs => acc ++ gs | _ => acc) []
      .success allGoals
    else .failure "then: sub-tactic failed"

/-- Try combinator: try t, on failure return original goal. -/
def tryComb (t : Tactic) : Tactic := fun g =>
  match t g with
  | .success gs => .success gs
  | .failure _  => .success [g]

/-- Orelse combinator: try t1, on failure try t2. -/
def orelseComb (t1 t2 : Tactic) : Tactic := fun g =>
  match t1 g with
  | .success gs => .success gs
  | .failure _  => t2 g

/-- Identity tactic: return goal unchanged. -/
def idTac : Tactic := fun g => .success [g]

/-- Fail tactic. -/
def failTac (msg : String) : Tactic := fun _ => .failure msg

/-- Theorem 7: Try of failing tactic preserves goal. -/
theorem try_fail_preserves (g : Goal) :
    tryComb (failTac "nope") g = .success [g] := by
  simp [tryComb, failTac]

/-- Theorem 8: Orelse with success picks first. -/
theorem orelse_first_success (g : Goal) (gs : ProofState) (t2 : Tactic)
    (t1 : Tactic) (h : t1 g = .success gs) :
    orelseComb t1 t2 g = .success gs := by
  simp [orelseComb, h]

/-- Theorem 9: Orelse with first failure falls through. -/
theorem orelse_fallthrough (g : Goal) (msg : String) (t2 : Tactic)
    (t1 : Tactic) (h : t1 g = .failure msg) :
    orelseComb t1 t2 g = t2 g := by
  simp [orelseComb, h]

/-- Theorem 10: idTac preserves the goal. -/
theorem id_tac_preserves (g : Goal) :
    idTac g = .success [g] := by
  rfl

-- ============================================================
-- §6  Focused Proofs and Zipper Navigation
-- ============================================================

/-- Zipper: focused goal with context of remaining goals. -/
structure Zipper where
  left  : List Goal    -- goals before focus
  focus : Goal         -- current goal
  right : List Goal    -- goals after focus
deriving DecidableEq, Repr

/-- Convert proof state to zipper (focus on first). -/
def toZipper : ProofState → Option Zipper
  | []      => none
  | g :: gs => some { left := [], focus := g, right := gs }

/-- Move focus right. -/
def Zipper.moveRight (z : Zipper) : Option Zipper :=
  match z.right with
  | []      => none
  | g :: gs => some { left := z.left ++ [z.focus], focus := g, right := gs }

/-- Move focus left. -/
def Zipper.moveLeft (z : Zipper) : Option Zipper :=
  match z.left.reverse with
  | []      => none
  | g :: gs => some { left := gs.reverse, focus := g, right := z.focus :: z.right }

/-- Flatten zipper back to proof state. -/
def Zipper.flatten (z : Zipper) : ProofState :=
  z.left ++ [z.focus] ++ z.right

/-- Theorem 11: Zipper of singleton focuses correctly. -/
theorem zipper_singleton (g : Goal) :
    toZipper [g] = some { left := [], focus := g, right := [] } := by
  rfl

/-- Theorem 12: Flatten of single-focus is singleton. -/
theorem flatten_singleton (g : Goal) :
    (Zipper.mk [] g []).flatten = [g] := by
  simp [Zipper.flatten]

/-- Theorem 13: MoveRight on empty right is none. -/
theorem move_right_empty (g : Goal) :
    (Zipper.mk [] g []).moveRight = none := by
  rfl

-- ============================================================
-- §7  Tactic Paths — Proof Search as Path
-- ============================================================

/-- Proof search state. -/
inductive SearchState where
  | open_   : ProofState → SearchState
  | closed  : SearchState
  | stuck   : String → SearchState
deriving DecidableEq, Repr

def tacticStep (name : String) (before after : ProofState) :
    Step SearchState (.open_ before) (.open_ after) :=
  .rule name _ _

def closeStep (ps : ProofState) :
    Step SearchState (.open_ ps) .closed :=
  .rule "qed" _ _

def stuckStep (ps : ProofState) (msg : String) :
    Step SearchState (.open_ ps) (.stuck msg) :=
  .rule "stuck" _ _

/-- Theorem 14: Two-tactic proof is 3 steps (intro, assumption, qed). -/
theorem two_tactic_proof (s0 s1 : ProofState) :
    (Path.cons (tacticStep "intro" s0 s1)
      (Path.cons (tacticStep "assumption" s1 [])
        (Path.single (closeStep [])))).length = 3 := by
  simp [Path.single, Path.length]

/-- Theorem 15: Split then close both branches is 4 steps. -/
theorem split_close_proof (s0 s1 s2 : ProofState) :
    (Path.cons (tacticStep "split" s0 s1)
      (Path.cons (tacticStep "exact-left" s1 s2)
        (Path.cons (tacticStep "exact-right" s2 [])
          (Path.single (closeStep []))))).length = 4 := by
  simp [Path.single, Path.length]

/-- Theorem 16: Stuck path is shorter than success path. -/
theorem stuck_shorter (s0 : ProofState) (msg : String) (s1 : ProofState) :
    (Path.single (stuckStep s0 msg)).length <
    (Path.cons (tacticStep "intro" s0 s1)
      (Path.single (closeStep s1))).length := by
  simp [Path.single, Path.length]

-- ============================================================
-- §8  Unification Hints
-- ============================================================

/-- Simple term for unification. -/
inductive UTerm where
  | var  : Nat → UTerm
  | app  : UTerm → UTerm → UTerm
  | con  : String → UTerm
deriving DecidableEq, Repr

/-- Substitution. -/
abbrev Subst := List (Nat × UTerm)

/-- Apply one substitution entry. -/
def UTerm.substOne (t : UTerm) (x : Nat) (s : UTerm) : UTerm :=
  match t with
  | .var n      => if n == x then s else .var n
  | .app t1 t2  => .app (t1.substOne x s) (t2.substOne x s)
  | .con c      => .con c

/-- UTerm size. -/
def UTerm.size : UTerm → Nat
  | .var _     => 1
  | .app t1 t2 => 1 + t1.size + t2.size
  | .con _     => 1

/-- Theorem 17: Variable substitution replaces correctly. -/
theorem subst_var_hit (x : Nat) (s : UTerm) :
    (UTerm.var x).substOne x s = s := by
  simp [UTerm.substOne]

/-- Theorem 18: Constant unaffected by substitution. -/
theorem subst_const (c : String) (x : Nat) (s : UTerm) :
    (UTerm.con c).substOne x s = .con c := by
  simp [UTerm.substOne]

/-- Theorem 19: UTerm size is positive. -/
theorem uterm_size_pos (t : UTerm) : t.size > 0 := by
  cases t <;> simp [UTerm.size] <;> omega

-- ============================================================
-- §9  Reflection Principle
-- ============================================================

/-- A reflected decision procedure state. -/
inductive ReflectState where
  | goal       : Prop' → ReflectState
  | normalized : Prop' → ReflectState
  | decided    : Bool → ReflectState
  | reflected  : ReflectState
deriving DecidableEq, Repr

def normalizeStep (p : Prop') (q : Prop') :
    Step ReflectState (.goal p) (.normalized q) :=
  .rule "normalize" _ _

def decideStep (p : Prop') (b : Bool) :
    Step ReflectState (.normalized p) (.decided b) :=
  .rule "decide" _ _

def reflectStep (b : Bool) :
    Step ReflectState (.decided b) .reflected :=
  .rule "reflect" _ _

/-- Theorem 20: Reflection proof is 3 steps. -/
theorem reflection_proof (p q : Prop') :
    (Path.cons (normalizeStep p q)
      (Path.cons (decideStep q true)
        (Path.single (reflectStep true)))).length = 3 := by
  simp [Path.single, Path.length]

/-- Theorem 21: Failed reflection is 2 steps to decided false. -/
theorem reflection_failure (p q : Prop') :
    (Path.cons (normalizeStep p q)
      (Path.single (decideStep q false))).length = 2 := by
  simp [Path.single, Path.length]

-- ============================================================
-- §10  Auto Tactic via Search
-- ============================================================

/-- Auto tactic depth bound. -/
def autoSearch (depth : Nat) (tactics : List Tactic) (g : Goal) : TacticResult :=
  match depth with
  | 0 => .failure "depth exhausted"
  | n + 1 =>
    let results := tactics.map (· g)
    match results.find? (fun r => match r with | .success [] => true | _ => false) with
    | some r => r
    | none =>
      match results.find? (fun r => match r with | .success _ => true | _ => false) with
      | some (.success gs) =>
        let subResults := gs.map (autoSearch n tactics)
        if subResults.all (fun r => match r with | .success [] => true | _ => false)
        then .success []
        else .failure "auto: sub-search failed"
      | _ => .failure "auto: no tactic applies"

/-- Theorem 22: Auto at depth 0 always fails. -/
theorem auto_depth_zero (tactics : List Tactic) (g : Goal) :
    autoSearch 0 tactics g = .failure "depth exhausted" := by
  rfl

/-- Theorem 23: Auto with empty tactic list fails. -/
theorem auto_no_tactics (depth : Nat) (g : Goal) :
    autoSearch (depth + 1) [] g = .failure "auto: no tactic applies" := by
  simp [autoSearch]

-- ============================================================
-- §11  Path Coherence for Tactic Framework
-- ============================================================

/-- Theorem 24: Tactic path trans is associative. -/
theorem tactic_path_assoc {a b c d : SearchState}
    (p : Path SearchState a b) (q : Path SearchState b c) (r : Path SearchState c d) :
    (p.trans q).trans r = p.trans (q.trans r) := by
  exact path_trans_assoc p q r

/-- Theorem 25: Tactic path length is additive. -/
theorem tactic_path_length_additive {a b c : SearchState}
    (p : Path SearchState a b) (q : Path SearchState b c) :
    (p.trans q).length = p.length + q.length := by
  exact path_length_trans p q

end TacticFrameworks
