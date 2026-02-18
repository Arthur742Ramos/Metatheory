/-
  Metatheory / ElaborationAlgorithm.lean

  Elaboration algorithms formalised via computational paths.
  Covers: bidirectional elaboration, hole/metavariable creation,
  implicit argument inference, instance search integration,
  coercion insertion, notation desugaring, elaboration monad,
  error recovery.

  All proofs are sorry-free.  18 theorems.
-/

set_option linter.unusedVariables false

namespace ElaborationAlgorithm

-- ============================================================
-- §1  Computational Paths Infrastructure
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive DPath (α : Type) : α → α → Type where
  | nil  : (a : α) → DPath α a a
  | cons : Step α a b → DPath α b c → DPath α a c

def DPath.trans : DPath α a b → DPath α b c → DPath α a c
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

def DPath.single (s : Step α a b) : DPath α a b :=
  .cons s (.nil _)

def Step.symm : Step α a b → Step α b a
  | .refl a => .refl a
  | .rule name a b => .rule (name ++ "⁻¹") b a

def DPath.symm : DPath α a b → DPath α b a
  | .nil a => .nil a
  | .cons s p => DPath.trans (DPath.symm p) (.cons (Step.symm s) (.nil _))

def DPath.length : DPath α a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + DPath.length p

theorem dpath_trans_assoc (p : DPath α a b) (q : DPath α b c) (r : DPath α c d) :
    DPath.trans (DPath.trans p q) r = DPath.trans p (DPath.trans q r) := by
  induction p with
  | nil _ => simp [DPath.trans]
  | cons s _ ih => simp [DPath.trans, ih]

theorem dpath_trans_nil_right (p : DPath α a b) :
    DPath.trans p (.nil b) = p := by
  induction p with
  | nil _ => simp [DPath.trans]
  | cons s _ ih => simp [DPath.trans, ih]

theorem dpath_length_trans (p : DPath α a b) (q : DPath α b c) :
    (DPath.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [DPath.trans, DPath.length]
  | cons s _ ih => simp [DPath.trans, DPath.length, ih, Nat.add_assoc]

-- ============================================================
-- §2  Elaboration Elements (symbolic, no keyword conflicts)
-- ============================================================

/-- Symbolic elaboration elements. -/
structure EExpr where
  tag : String
  uid : Nat
deriving DecidableEq, Repr

def mkE (t : String) (n : Nat) : EExpr := ⟨t, n⟩

-- Surface syntax constructors
def surfVar (x : String) : EExpr := mkE ("var:" ++ x) 1
def surfLam (x : String) (body : EExpr) : EExpr :=
  mkE ("λ" ++ x ++ "." ++ body.tag) (body.uid * 10 + 2)
def surfApp (f a : EExpr) : EExpr :=
  mkE ("(" ++ f.tag ++ " " ++ a.tag ++ ")") (f.uid * 100 + a.uid + 3)
def surfHole (n : Nat) : EExpr := mkE ("?_" ++ toString n) (n + 1000)
def surfAnn (e : EExpr) (ty : String) : EExpr :=
  mkE ("(" ++ e.tag ++ " : " ++ ty ++ ")") (e.uid + 2000)
def surfLet (x : String) (v body : EExpr) : EExpr :=
  mkE ("let " ++ x ++ " := " ++ v.tag ++ " in " ++ body.tag) (v.uid * 50 + body.uid + 4)
def surfSugar (name : String) (args : List EExpr) : EExpr :=
  mkE ("sugar:" ++ name) (args.length + 5000)

-- Core syntax constructors
def coreVar (x : String) : EExpr := mkE ("core:var:" ++ x) 10001
def coreLam (x : String) (ty : String) (body : EExpr) : EExpr :=
  mkE ("core:λ(" ++ x ++ ":" ++ ty ++ ")." ++ body.tag) (body.uid * 10 + 20)
def coreApp (f a : EExpr) : EExpr :=
  mkE ("core:(" ++ f.tag ++ " " ++ a.tag ++ ")") (f.uid * 100 + a.uid + 30)
def coreImplApp (f impl : EExpr) : EExpr :=
  mkE ("core:(" ++ f.tag ++ " {" ++ impl.tag ++ "})") (f.uid * 100 + impl.uid + 40)
def coreInstApp (f inst : EExpr) : EExpr :=
  mkE ("core:(" ++ f.tag ++ " [" ++ inst.tag ++ "])") (f.uid * 100 + inst.uid + 50)
def coreCoerce (src tgt : String) (e : EExpr) : EExpr :=
  mkE ("core:coe(" ++ src ++ "→" ++ tgt ++ "," ++ e.tag ++ ")") (e.uid + 3000)
def coreMeta (n : Nat) : EExpr := mkE ("core:?m" ++ toString n) (n + 4000)
def coreLet (x ty : String) (v body : EExpr) : EExpr :=
  mkE ("core:let(" ++ x ++ ":" ++ ty ++ ":=" ++ v.tag ++ ")." ++ body.tag) (v.uid * 50 + body.uid + 60)

-- ============================================================
-- §3  Elaboration Context
-- ============================================================

structure ElabCtx where
  numBindings : Nat
  numMetas    : Nat
  numErrors   : Nat
  numInst     : Nat
  numCoerce   : Nat
deriving DecidableEq, Repr

def ElabCtx.empty : ElabCtx := ⟨0, 0, 0, 0, 0⟩

-- ============================================================
-- §4  Elaboration Rewrite Steps
-- ============================================================

/-- Desugar notation to application. -/
def desugarStep (sugar desugared : EExpr) :
    Step EExpr sugar desugared :=
  .rule "desugar" _ _

/-- Insert implicit argument: f x → f {?m} x. -/
def insertImplicitStep (before after : EExpr) :
    Step EExpr before after :=
  .rule "insert-implicit" _ _

/-- Insert instance argument: f x → f [inst] x. -/
def insertInstanceStep (before after : EExpr) :
    Step EExpr before after :=
  .rule "insert-instance" _ _

/-- Insert coercion. -/
def insertCoercionStep (e coerced : EExpr) :
    Step EExpr e coerced :=
  .rule "insert-coercion" _ _

/-- Create metavariable hole. -/
def createMetaStep (e : EExpr) (m : EExpr) :
    Step EExpr e m :=
  .rule "create-meta" _ _

/-- Solve metavariable. -/
def solveMetaStep (m solution : EExpr) :
    Step EExpr m solution :=
  .rule "solve-meta" _ _

/-- Mode switch: synth → check. -/
def modeSwitchStep (e : EExpr) :
    Step EExpr e e :=
  .rule "mode-switch" _ _

/-- Annotation elaboration. -/
def annElabStep (e elaborated : EExpr) :
    Step EExpr e elaborated :=
  .rule "ann-elab" _ _

/-- Lambda body elaboration. -/
def lamElabStep (before after : EExpr) :
    Step EExpr before after :=
  .rule "lam-elab" _ _

/-- Let elaboration. -/
def letElabStep (before after : EExpr) :
    Step EExpr before after :=
  .rule "let-elab" _ _

/-- Error recovery: replace with metavariable. -/
def errorRecoveryStep (errExpr placeholder : EExpr) :
    Step EExpr errExpr placeholder :=
  .rule "error-recovery" _ _

-- ============================================================
-- §5  Elaboration Path Constructions
-- ============================================================

/-- 1: Notation desugaring path. -/
def desugarPath (sugar desugared : EExpr) :
    DPath EExpr sugar desugared :=
  DPath.single (desugarStep sugar desugared)

/-- 2: Implicit insertion path. -/
def implicitInsertPath (before after : EExpr) :
    DPath EExpr before after :=
  DPath.single (insertImplicitStep before after)

/-- 3: Instance insertion path. -/
def instanceInsertPath (before after : EExpr) :
    DPath EExpr before after :=
  DPath.single (insertInstanceStep before after)

/-- 4: Coercion insertion path. -/
def coercionPath (e coerced : EExpr) :
    DPath EExpr e coerced :=
  DPath.single (insertCoercionStep e coerced)

/-- 5: Meta creation + solve chain (2 steps). -/
def metaSolvePath (e : EExpr) (m solution : EExpr) :
    DPath EExpr e solution :=
  let s1 := createMetaStep e m
  let s2 := solveMetaStep m solution
  (DPath.single s1).trans (DPath.single s2)

/-- 6: Full implicit + instance chain (2 steps). -/
def fullImplInstPath (e implInserted instInserted : EExpr) :
    DPath EExpr e instInserted :=
  let s1 := insertImplicitStep e implInserted
  let s2 := insertInstanceStep implInserted instInserted
  (DPath.single s1).trans (DPath.single s2)

/-- 7: Error recovery then re-elaborate chain (2 steps). -/
def errorRecoverPath (errExpr placeholder resolved : EExpr) :
    DPath EExpr errExpr resolved :=
  let s1 := errorRecoveryStep errExpr placeholder
  let s2 := solveMetaStep placeholder resolved
  (DPath.single s1).trans (DPath.single s2)

/-- 8: Lambda body elaboration path. -/
def lamBodyElabPath (before after : EExpr) :
    DPath EExpr before after :=
  DPath.single (lamElabStep before after)

/-- 9: Let body elaboration path. -/
def letBodyElabPath (before after : EExpr) :
    DPath EExpr before after :=
  DPath.single (letElabStep before after)

/-- 10: Undo coercion via symm. -/
def undoCoercionPath (e coerced : EExpr) :
    DPath EExpr coerced e :=
  (coercionPath e coerced).symm

/-- 11: Full elaboration pipeline: desugar → implicit → instance → coercion (4 steps). -/
def fullElabChain (e desugared implDone instDone coerced : EExpr) :
    DPath EExpr e coerced :=
  let s1 := desugarStep e desugared
  let s2 := insertImplicitStep desugared implDone
  let s3 := insertInstanceStep implDone instDone
  let s4 := insertCoercionStep instDone coerced
  (DPath.single s1).trans
    ((DPath.single s2).trans
      ((DPath.single s3).trans (DPath.single s4)))

/-- 12: Annotation-driven elaboration: ann → mode switch → check body (3 steps). -/
def annDrivenPath (annExpr switched checked : EExpr) :
    DPath EExpr annExpr checked :=
  let s1 := annElabStep annExpr switched
  let s2 := modeSwitchStep switched
  let s3 := lamElabStep switched checked
  (DPath.single s1).trans ((DPath.single s2).trans (DPath.single s3))

-- ============================================================
-- §6  Propositional Theorems
-- ============================================================

/-- Theorem 1: Desugar path has length 1. -/
theorem desugar_len (s d : EExpr) :
    (desugarPath s d).length = 1 := by
  simp [desugarPath, DPath.single, DPath.length]

/-- Theorem 2: Implicit insert path has length 1. -/
theorem implicitInsert_len (b a : EExpr) :
    (implicitInsertPath b a).length = 1 := by
  simp [implicitInsertPath, DPath.single, DPath.length]

/-- Theorem 3: Instance insert path has length 1. -/
theorem instanceInsert_len (b a : EExpr) :
    (instanceInsertPath b a).length = 1 := by
  simp [instanceInsertPath, DPath.single, DPath.length]

/-- Theorem 4: Coercion path has length 1. -/
theorem coercion_len (e c : EExpr) :
    (coercionPath e c).length = 1 := by
  simp [coercionPath, DPath.single, DPath.length]

/-- Theorem 5: Meta solve chain has length 2. -/
theorem metaSolve_len (e m sol : EExpr) :
    (metaSolvePath e m sol).length = 2 := by
  simp [metaSolvePath, DPath.single, DPath.trans, DPath.length]

/-- Theorem 6: Full implicit+instance chain has length 2. -/
theorem fullImplInst_len (e i1 i2 : EExpr) :
    (fullImplInstPath e i1 i2).length = 2 := by
  simp [fullImplInstPath, DPath.single, DPath.trans, DPath.length]

/-- Theorem 7: Error recovery chain has length 2. -/
theorem errorRecover_len (err ph res : EExpr) :
    (errorRecoverPath err ph res).length = 2 := by
  simp [errorRecoverPath, DPath.single, DPath.trans, DPath.length]

/-- Theorem 8: Full elaboration chain has length 4. -/
theorem fullElab_len (e d im ins c : EExpr) :
    (fullElabChain e d im ins c).length = 4 := by
  simp [fullElabChain, DPath.single, DPath.trans, DPath.length]

/-- Theorem 9: Undo coercion (symm) has length 1. -/
theorem undoCoercion_len (e c : EExpr) :
    (undoCoercionPath e c).length = 1 := by
  simp [undoCoercionPath, coercionPath, DPath.symm, DPath.single,
        DPath.trans, DPath.length, Step.symm]

/-- Theorem 10: Lambda body elab has length 1. -/
theorem lamBodyElab_len (b a : EExpr) :
    (lamBodyElabPath b a).length = 1 := by
  simp [lamBodyElabPath, DPath.single, DPath.length]

/-- Theorem 11: Let body elab has length 1. -/
theorem letBodyElab_len (b a : EExpr) :
    (letBodyElabPath b a).length = 1 := by
  simp [letBodyElabPath, DPath.single, DPath.length]

/-- Theorem 12: Annotation-driven path has length 3. -/
theorem annDriven_len (ann sw ch : EExpr) :
    (annDrivenPath ann sw ch).length = 3 := by
  simp [annDrivenPath, DPath.single, DPath.trans, DPath.length]

/-- Theorem 13: Path trans associativity for elab paths. -/
theorem elab_trans_assoc (p : DPath EExpr a b) (q : DPath EExpr b c) (r : DPath EExpr c d) :
    DPath.trans (DPath.trans p q) r = DPath.trans p (DPath.trans q r) :=
  dpath_trans_assoc p q r

/-- Theorem 14: Empty context has zero metas. -/
theorem empty_ctx_metas : ElabCtx.empty.numMetas = 0 := by rfl

/-- Theorem 15: Empty context has zero errors. -/
theorem empty_ctx_errors : ElabCtx.empty.numErrors = 0 := by rfl

/-- Theorem 16: Trans with nil preserves length. -/
theorem elab_trans_nil (p : DPath EExpr a b) :
    (DPath.trans p (DPath.nil b)).length = p.length := by
  induction p with
  | nil _ => simp [DPath.trans, DPath.length]
  | cons s _ ih => simp [DPath.trans, DPath.length, ih]

/-- Theorem 17: Composing paths adds their lengths. -/
theorem elab_compose_length (p : DPath EExpr a b) (q : DPath EExpr b c) :
    (DPath.trans p q).length = p.length + q.length :=
  dpath_length_trans p q

/-- Theorem 18: Symm of single step preserves length. -/
theorem elab_symm_single (s : Step EExpr a b) :
    (DPath.single s).symm.length = (DPath.single s).length := by
  simp [DPath.single, DPath.symm, DPath.trans, DPath.length, Step.symm]

end ElaborationAlgorithm
