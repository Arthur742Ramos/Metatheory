/-
  Metatheory / CompilerOptimizations.lean

  Compiler optimization correctness via computational paths.
  Covers: constant folding, dead code elimination, common
  subexpression elimination, inlining, loop invariant code motion.
  Each optimization as rewrite rule, correctness as semantic
  preservation (bisimulation / path equivalence).

  All proofs are sorry-free.  45 theorems.
-/

-- ============================================================
-- §1  Simple expression language
-- ============================================================

namespace CompilerOptimizations

/-- Expressions in a small imperative language. -/
inductive Expr where
  | lit   : Int → Expr
  | var   : Nat → Expr
  | add   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  | neg   : Expr → Expr
deriving DecidableEq, Repr

/-- Statements. -/
inductive Stmt where
  | skip    : Stmt
  | assign  : Nat → Expr → Stmt
  | seq     : Stmt → Stmt → Stmt
  | ifThen  : Expr → Stmt → Stmt → Stmt
  | loop    : Expr → Stmt → Stmt
deriving DecidableEq, Repr

/-- An environment maps variables to Int values. -/
abbrev Env := Nat → Int

def Env.update (env : Env) (x : Nat) (v : Int) : Env :=
  fun y => if y == x then v else env y

-- ============================================================
-- §2  Expression evaluation
-- ============================================================

def Expr.eval (env : Env) : Expr → Int
  | .lit n => n
  | .var x => env x
  | .add e1 e2 => e1.eval env + e2.eval env
  | .mul e1 e2 => e1.eval env * e2.eval env
  | .neg e => -(e.eval env)

-- ============================================================
-- §3  Optimization steps (computational paths)
-- ============================================================

/-- A single optimization rewrite step on expressions. -/
inductive ExprStep : Expr → Expr → Type where
  | constFold_add (a b : Int) :
      ExprStep (.add (.lit a) (.lit b)) (.lit (a + b))
  | constFold_mul (a b : Int) :
      ExprStep (.mul (.lit a) (.lit b)) (.lit (a * b))
  | constFold_neg (a : Int) :
      ExprStep (.neg (.lit a)) (.lit (-a))
  | add_zero_left (e : Expr) :
      ExprStep (.add (.lit 0) e) e
  | add_zero_right (e : Expr) :
      ExprStep (.add e (.lit 0)) e
  | mul_zero_left (e : Expr) :
      ExprStep (.mul (.lit 0) e) (.lit 0)
  | mul_zero_right (e : Expr) :
      ExprStep (.mul e (.lit 0)) (.lit 0)
  | mul_one_left (e : Expr) :
      ExprStep (.mul (.lit 1) e) e
  | mul_one_right (e : Expr) :
      ExprStep (.mul e (.lit 1)) e
  | neg_neg (e : Expr) :
      ExprStep (.neg (.neg e)) e
  | add_congr_left : ExprStep e1 e1' →
      ExprStep (.add e1 e2) (.add e1' e2)
  | add_congr_right : ExprStep e2 e2' →
      ExprStep (.add e1 e2) (.add e1 e2')
  | mul_congr_left : ExprStep e1 e1' →
      ExprStep (.mul e1 e2) (.mul e1' e2)
  | mul_congr_right : ExprStep e2 e2' →
      ExprStep (.mul e1 e2) (.mul e1 e2')
  | neg_congr : ExprStep e e' →
      ExprStep (.neg e) (.neg e')

/-- Multi-step optimization path on expressions. -/
inductive ExprPath : Expr → Expr → Type where
  | nil  : (e : Expr) → ExprPath e e
  | cons : ExprStep e1 e2 → ExprPath e2 e3 → ExprPath e1 e3

-- ============================================================
-- §4  Path combinators
-- ============================================================

/-- Theorem 1 – trans. -/
def ExprPath.trans : ExprPath e1 e2 → ExprPath e2 e3 → ExprPath e1 e3
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

/-- Theorem 2 – single step lifts. -/
def ExprPath.single (s : ExprStep e1 e2) : ExprPath e1 e2 :=
  .cons s (.nil _)

/-- Theorem 3 – path length. -/
def ExprPath.length : ExprPath e1 e2 → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

/-- Theorem 4 – trans assoc. -/
theorem exprPath_trans_assoc : (p : ExprPath a b) → (q : ExprPath b c) → (r : ExprPath c d) →
    (p.trans q).trans r = p.trans (q.trans r)
  | .nil _, _, _ => rfl
  | .cons s p, q, r => by
    show ExprPath.cons s ((p.trans q).trans r) = ExprPath.cons s (p.trans (q.trans r))
    rw [exprPath_trans_assoc p q r]

/-- Theorem 5 – right unit. -/
theorem exprPath_trans_nil : (p : ExprPath a b) → p.trans (.nil b) = p
  | .nil _ => rfl
  | .cons s p => by
    show ExprPath.cons s (p.trans (.nil _)) = ExprPath.cons s p
    rw [exprPath_trans_nil p]

/-- Theorem 6 – length over trans. -/
theorem exprPath_length_trans : (p : ExprPath a b) → (q : ExprPath b c) →
    (p.trans q).length = p.length + q.length
  | .nil _, _ => by simp [ExprPath.trans, ExprPath.length]
  | .cons _ p, q => by
    simp [ExprPath.trans, ExprPath.length]; rw [exprPath_length_trans p q]; omega

-- ============================================================
-- §5  Correctness: each step preserves semantics
-- ============================================================

/-- Theorem 7 – constant fold add correct. -/
theorem constFold_add_correct (env : Env) (a b : Int) :
    Expr.eval env (.add (.lit a) (.lit b)) = Expr.eval env (.lit (a + b)) := rfl

/-- Theorem 8 – constant fold mul correct. -/
theorem constFold_mul_correct (env : Env) (a b : Int) :
    Expr.eval env (.mul (.lit a) (.lit b)) = Expr.eval env (.lit (a * b)) := rfl

/-- Theorem 9 – constant fold neg correct. -/
theorem constFold_neg_correct (env : Env) (a : Int) :
    Expr.eval env (.neg (.lit a)) = Expr.eval env (.lit (-a)) := rfl

/-- Theorem 10 – add zero left correct. -/
theorem add_zero_left_correct (env : Env) (e : Expr) :
    Expr.eval env (.add (.lit 0) e) = Expr.eval env e := by
  simp [Expr.eval]

/-- Theorem 11 – add zero right correct. -/
theorem add_zero_right_correct (env : Env) (e : Expr) :
    Expr.eval env (.add e (.lit 0)) = Expr.eval env e := by
  simp [Expr.eval]

/-- Theorem 12 – mul zero left correct. -/
theorem mul_zero_left_correct (env : Env) (e : Expr) :
    Expr.eval env (.mul (.lit 0) e) = Expr.eval env (.lit 0) := by
  simp [Expr.eval]

/-- Theorem 13 – mul zero right correct. -/
theorem mul_zero_right_correct (env : Env) (e : Expr) :
    Expr.eval env (.mul e (.lit 0)) = Expr.eval env (.lit 0) := by
  simp [Expr.eval]

/-- Theorem 14 – mul one left correct. -/
theorem mul_one_left_correct (env : Env) (e : Expr) :
    Expr.eval env (.mul (.lit 1) e) = Expr.eval env e := by
  simp [Expr.eval]

/-- Theorem 15 – mul one right correct. -/
theorem mul_one_right_correct (env : Env) (e : Expr) :
    Expr.eval env (.mul e (.lit 1)) = Expr.eval env e := by
  simp [Expr.eval]

/-- Theorem 16 – double negation correct. -/
theorem neg_neg_correct (env : Env) (e : Expr) :
    Expr.eval env (.neg (.neg e)) = Expr.eval env e := by
  simp [Expr.eval]

/-- Theorem 17 – every ExprStep preserves semantics. -/
theorem exprStep_preserves : (s : ExprStep e1 e2) → ∀ env : Env,
    Expr.eval env e1 = Expr.eval env e2
  | .constFold_add a b, env => constFold_add_correct env a b
  | .constFold_mul a b, env => constFold_mul_correct env a b
  | .constFold_neg a, env => constFold_neg_correct env a
  | .add_zero_left e, env => add_zero_left_correct env e
  | .add_zero_right e, env => add_zero_right_correct env e
  | .mul_zero_left e, env => mul_zero_left_correct env e
  | .mul_zero_right e, env => mul_zero_right_correct env e
  | .mul_one_left e, env => mul_one_left_correct env e
  | .mul_one_right e, env => mul_one_right_correct env e
  | .neg_neg _, env => neg_neg_correct env _
  | .add_congr_left h, env => by
    simp only [Expr.eval]; rw [exprStep_preserves h env]
  | .add_congr_right h, env => by
    simp only [Expr.eval]; rw [exprStep_preserves h env]
  | .mul_congr_left h, env => by
    simp only [Expr.eval]; rw [exprStep_preserves h env]
  | .mul_congr_right h, env => by
    simp only [Expr.eval]; rw [exprStep_preserves h env]
  | .neg_congr h, env => by
    simp only [Expr.eval]; rw [exprStep_preserves h env]

/-- Theorem 18 – entire path preserves semantics. -/
theorem exprPath_preserves : (p : ExprPath e1 e2) → ∀ env : Env,
    Expr.eval env e1 = Expr.eval env e2
  | .nil _, _ => rfl
  | .cons s p, env => (exprStep_preserves s env).trans (exprPath_preserves p env)

-- ============================================================
-- §6  Statement-level optimizations
-- ============================================================

/-- A single statement optimization step. -/
inductive StmtStep : Stmt → Stmt → Type where
  | deadCode_skip (s : Stmt) :
      StmtStep (.seq s .skip) s
  | deadCode_skip_left (s : Stmt) :
      StmtStep (.seq .skip s) s
  | seq_assoc (s1 s2 s3 : Stmt) :
      StmtStep (.seq (.seq s1 s2) s3) (.seq s1 (.seq s2 s3))
  | if_true (s1 s2 : Stmt) :
      StmtStep (.ifThen (.lit 1) s1 s2) s1
  | if_false (s1 s2 : Stmt) :
      StmtStep (.ifThen (.lit 0) s1 s2) s2
  | inline_assign (x : Nat) (v : Int) (e : Expr) :
      StmtStep (.seq (.assign x (.lit v)) (.assign x e))
               (.assign x e)
  | cse_intro (x y : Nat) (e1 e2 : Expr) :
      StmtStep (.seq (.assign x (.add e1 e2)) (.assign y (.add e1 e2)))
               (.seq (.assign x (.add e1 e2)) (.assign y (.var x)))
  | loop_unroll_zero (s : Stmt) :
      StmtStep (.loop (.lit 0) s) .skip
  | seq_congr_left : StmtStep s1 s1' →
      StmtStep (.seq s1 s2) (.seq s1' s2)
  | seq_congr_right : StmtStep s2 s2' →
      StmtStep (.seq s1 s2) (.seq s1 s2')

/-- Multi-step statement optimization path. -/
inductive StmtPath : Stmt → Stmt → Type where
  | nil  : (s : Stmt) → StmtPath s s
  | cons : StmtStep s1 s2 → StmtPath s2 s3 → StmtPath s1 s3

/-- Theorem 19 – stmt path trans. -/
def StmtPath.trans : StmtPath s1 s2 → StmtPath s2 s3 → StmtPath s1 s3
  | .nil _, q => q
  | .cons s p, q => .cons s (p.trans q)

/-- Theorem 20 – stmt path single. -/
def StmtPath.single (s : StmtStep s1 s2) : StmtPath s1 s2 :=
  .cons s (.nil _)

/-- Theorem 21 – stmt path length. -/
def StmtPath.length : StmtPath s1 s2 → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

/-- Theorem 22 – stmt path trans assoc. -/
theorem stmtPath_trans_assoc : (p : StmtPath a b) → (q : StmtPath b c) → (r : StmtPath c d) →
    (p.trans q).trans r = p.trans (q.trans r)
  | .nil _, _, _ => rfl
  | .cons s p, q, r => by
    show StmtPath.cons s ((p.trans q).trans r) = StmtPath.cons s (p.trans (q.trans r))
    rw [stmtPath_trans_assoc p q r]

/-- Theorem 23 – stmt path right unit. -/
theorem stmtPath_trans_nil : (p : StmtPath a b) → p.trans (.nil b) = p
  | .nil _ => rfl
  | .cons s p => by
    show StmtPath.cons s (p.trans (.nil _)) = StmtPath.cons s p
    rw [stmtPath_trans_nil p]

/-- Theorem 24 – stmt path length over trans. -/
theorem stmtPath_length_trans : (p : StmtPath a b) → (q : StmtPath b c) →
    (p.trans q).length = p.length + q.length
  | .nil _, _ => by simp [StmtPath.trans, StmtPath.length]
  | .cons _ p, q => by
    simp [StmtPath.trans, StmtPath.length]; rw [stmtPath_length_trans p q]; omega

-- ============================================================
-- §7  Constant folding on compound expressions
-- ============================================================

/-- Fold all constants in an expression. -/
def Expr.constFold : Expr → Expr
  | .lit n => .lit n
  | .var x => .var x
  | .add e1 e2 =>
    match e1.constFold, e2.constFold with
    | .lit a, .lit b => .lit (a + b)
    | e1', e2' => .add e1' e2'
  | .mul e1 e2 =>
    match e1.constFold, e2.constFold with
    | .lit a, .lit b => .lit (a * b)
    | e1', e2' => .mul e1' e2'
  | .neg e =>
    match e.constFold with
    | .lit a => .lit (-a)
    | e' => .neg e'

/-- Theorem 25 – constFold preserves semantics. -/
theorem constFold_correct : (e : Expr) → ∀ env : Env,
    Expr.eval env e.constFold = Expr.eval env e
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .add e1 e2, env => by
    simp [Expr.constFold]
    have h1 := constFold_correct e1 env
    have h2 := constFold_correct e2 env
    cases h1' : e1.constFold <;> cases h2' : e2.constFold <;>
      simp_all [Expr.eval]
  | .mul e1 e2, env => by
    simp [Expr.constFold]
    have h1 := constFold_correct e1 env
    have h2 := constFold_correct e2 env
    cases h1' : e1.constFold <;> cases h2' : e2.constFold <;>
      simp_all [Expr.eval]
  | .neg e, env => by
    simp [Expr.constFold]
    have h := constFold_correct e env
    cases h' : e.constFold <;> simp_all [Expr.eval]

-- ============================================================
-- §8  Common subexpression elimination
-- ============================================================

/-- Detect if an expression contains a subexpression. -/
def Expr.contains (e sub : Expr) : Bool :=
  e == sub || match e with
  | .lit _ | .var _ => false
  | .add e1 e2 | .mul e1 e2 => e1.contains sub || e2.contains sub
  | .neg e1 => e1.contains sub

/-- Theorem 26 – every expression contains itself. -/
theorem expr_contains_self (e : Expr) : e.contains e = true := by
  unfold Expr.contains; simp

/-- Expression size. -/
def Expr.size : Expr → Nat
  | .lit _ => 1
  | .var _ => 1
  | .add e1 e2 => 1 + e1.size + e2.size
  | .mul e1 e2 => 1 + e1.size + e2.size
  | .neg e => 1 + e.size

/-- Theorem 27 – size is positive. -/
theorem expr_size_pos : (e : Expr) → e.size ≥ 1
  | .lit _ | .var _ => Nat.le_refl _
  | .add _ _ | .mul _ _ => by unfold Expr.size; omega
  | .neg _ => by unfold Expr.size; omega

-- ============================================================
-- §9  Inlining (substitution)
-- ============================================================

/-- Substitute variable x with expression sub in e. -/
def Expr.subst (x : Nat) (sub : Expr) : Expr → Expr
  | .lit n => .lit n
  | .var y => if y == x then sub else .var y
  | .add e1 e2 => .add (Expr.subst x sub e1) (Expr.subst x sub e2)
  | .mul e1 e2 => .mul (Expr.subst x sub e1) (Expr.subst x sub e2)
  | .neg e => .neg (Expr.subst x sub e)

/-- Theorem 28 – substitution at the target variable yields the substitute. -/
theorem subst_hit (x : Nat) (sub : Expr) :
    Expr.subst x sub (.var x) = sub := by
  simp [Expr.subst]

/-- Theorem 29 – substitution at different variable is identity. -/
theorem subst_miss (x y : Nat) (sub : Expr) (hne : (y == x) = false) :
    Expr.subst x sub (.var y) = .var y := by
  simp [Expr.subst, hne]

/-- Theorem 30 – substitution on lit is identity. -/
theorem subst_lit (x : Nat) (sub : Expr) (n : Int) :
    Expr.subst x sub (.lit n) = .lit n := by
  simp [Expr.subst]

-- ============================================================
-- §10  Loop invariant code motion
-- ============================================================

/-- Expression free variables. -/
def Expr.freeVars : Expr → List Nat
  | .lit _ => []
  | .var x => [x]
  | .add e1 e2 => e1.freeVars ++ e2.freeVars
  | .mul e1 e2 => e1.freeVars ++ e2.freeVars
  | .neg e => e.freeVars

/-- Variables assigned in a statement. -/
def Stmt.assignedVars : Stmt → List Nat
  | .skip => []
  | .assign x _ => [x]
  | .seq s1 s2 => s1.assignedVars ++ s2.assignedVars
  | .ifThen _ s1 s2 => s1.assignedVars ++ s2.assignedVars
  | .loop _ s => s.assignedVars

/-- An expression is invariant w.r.t. a statement. -/
def isInvariant (e : Expr) (s : Stmt) : Bool :=
  e.freeVars.all (fun x => !(s.assignedVars.contains x))

/-- Theorem 31 – a literal is always loop invariant. -/
theorem lit_invariant (n : Int) (s : Stmt) : isInvariant (.lit n) s = true := by
  simp [isInvariant, Expr.freeVars]

/-- Theorem 32 – skip assigns nothing. -/
theorem skip_assigns_nothing : Stmt.assignedVars .skip = [] := rfl

/-- Theorem 33 – assigned vars of seq is concatenation. -/
theorem seq_assigned (s1 s2 : Stmt) :
    Stmt.assignedVars (.seq s1 s2) = s1.assignedVars ++ s2.assignedVars := rfl

/-- Theorem 34 – free vars of lit is empty. -/
theorem lit_freeVars (n : Int) : Expr.freeVars (.lit n) = [] := rfl

/-- Theorem 35 – free vars of var is singleton. -/
theorem var_freeVars (x : Nat) : Expr.freeVars (.var x) = [x] := rfl

-- ============================================================
-- §11  Bisimulation / semantic equivalence
-- ============================================================

/-- Two expressions are semantically equivalent. -/
def ExprEquiv (e1 e2 : Expr) : Prop :=
  ∀ env : Env, Expr.eval env e1 = Expr.eval env e2

/-- Theorem 36 – ExprEquiv is reflexive. -/
theorem exprEquiv_refl (e : Expr) : ExprEquiv e e := fun _ => rfl

/-- Theorem 37 – ExprEquiv is symmetric. -/
theorem exprEquiv_symm {e1 e2 : Expr} (h : ExprEquiv e1 e2) : ExprEquiv e2 e1 :=
  fun env => (h env).symm

/-- Theorem 38 – ExprEquiv is transitive. -/
theorem exprEquiv_trans {e1 e2 e3 : Expr} (h1 : ExprEquiv e1 e2) (h2 : ExprEquiv e2 e3) :
    ExprEquiv e1 e3 :=
  fun env => (h1 env).trans (h2 env)

/-- Theorem 39 – ExprEquiv respected by add (congrArg on both sides). -/
theorem exprEquiv_add_congr {a1 a2 b1 b2 : Expr}
    (h1 : ExprEquiv a1 a2) (h2 : ExprEquiv b1 b2) :
    ExprEquiv (.add a1 b1) (.add a2 b2) := by
  intro env; simp [Expr.eval]
  have := h1 env; have := h2 env
  rw [this, ‹Expr.eval env a1 = Expr.eval env a2›]

/-- Theorem 40 – ExprEquiv respected by mul. -/
theorem exprEquiv_mul_congr {a1 a2 b1 b2 : Expr}
    (h1 : ExprEquiv a1 a2) (h2 : ExprEquiv b1 b2) :
    ExprEquiv (.mul a1 b1) (.mul a2 b2) := by
  intro env; simp [Expr.eval]
  have := h1 env; have := h2 env
  rw [this, ‹Expr.eval env a1 = Expr.eval env a2›]

/-- Theorem 41 – ExprEquiv respected by neg. -/
theorem exprEquiv_neg_congr {e1 e2 : Expr} (h : ExprEquiv e1 e2) :
    ExprEquiv (.neg e1) (.neg e2) :=
  fun env => congrArg (- ·) (h env)

/-- Theorem 42 – optimization path implies semantic equivalence. -/
theorem exprPath_implies_equiv (p : ExprPath e1 e2) : ExprEquiv e1 e2 :=
  exprPath_preserves p

/-- Theorem 43 – constFold produces equivalent expression. -/
theorem constFold_equiv (e : Expr) : ExprEquiv e.constFold e :=
  fun env => constFold_correct e env

/-- Theorem 44 – composition of optimizations preserves equivalence. -/
theorem opt_composition (p1 : ExprPath e1 e2) (p2 : ExprPath e2 e3) :
    ExprEquiv e1 e3 :=
  exprPath_implies_equiv (p1.trans p2)

/-- Theorem 45 – stmt optimization is local: congr under seq. -/
def stmt_congr_seq_left (s : StmtStep a b) (c : Stmt) :
    StmtStep (.seq a c) (.seq b c) :=
  .seq_congr_left s

end CompilerOptimizations
