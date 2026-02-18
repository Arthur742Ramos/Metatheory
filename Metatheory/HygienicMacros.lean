/-
  Metatheory of Hygienic Macro Systems
-/

namespace HygienicMacros

abbrev RawName := Nat

structure Mark where
  val : Nat
deriving DecidableEq, Repr, BEq

structure MarkedId where
  name : RawName
  marks : List Mark
deriving DecidableEq, Repr, BEq

def nameEquiv (a b : MarkedId) : Prop := a.name = b.name
def fullyEquiv (a b : MarkedId) : Prop := a = b

theorem nameEquiv_refl (a : MarkedId) : nameEquiv a a := rfl
theorem nameEquiv_symm {a b : MarkedId} (h : nameEquiv a b) : nameEquiv b a := h.symm
theorem nameEquiv_trans {a b c : MarkedId} (h1 : nameEquiv a b) (h2 : nameEquiv b c) :
    nameEquiv a c := h1.trans h2

theorem fullyEquiv_implies_nameEquiv {a b : MarkedId} (h : fullyEquiv a b) :
    nameEquiv a b := by simp [fullyEquiv, nameEquiv] at *; rw [h]

theorem fullyEquiv_refl (a : MarkedId) : fullyEquiv a a := rfl
theorem fullyEquiv_symm {a b : MarkedId} (h : fullyEquiv a b) : fullyEquiv b a := h.symm

-- ============================================================
-- Expressions
-- ============================================================

inductive Expr where
  | var : MarkedId → Expr
  | lam : MarkedId → Expr → Expr
  | app : Expr → Expr → Expr
  | letE : MarkedId → Expr → Expr → Expr
  | quote : Expr → Expr
  | unquote : Expr → Expr
  | num : Nat → Expr
deriving DecidableEq, Repr, BEq

-- ============================================================
-- Mark Application (Kohlbecker's Algorithm Core)
-- ============================================================

def applyMark (m : Mark) : Expr → Expr
  | .var x => .var ⟨x.name, x.marks ++ [m]⟩
  | .lam x body => .lam ⟨x.name, x.marks ++ [m]⟩ (applyMark m body)
  | .app f a => .app (applyMark m f) (applyMark m a)
  | .letE x e body => .letE ⟨x.name, x.marks ++ [m]⟩ (applyMark m e) (applyMark m body)
  | .quote e => .quote (applyMark m e)
  | .unquote e => .unquote (applyMark m e)
  | .num n => .num n

def stripMarks : Expr → Expr
  | .var x => .var ⟨x.name, []⟩
  | .lam x body => .lam ⟨x.name, []⟩ (stripMarks body)
  | .app f a => .app (stripMarks f) (stripMarks a)
  | .letE x e body => .letE ⟨x.name, []⟩ (stripMarks e) (stripMarks body)
  | .quote e => .quote (stripMarks e)
  | .unquote e => .unquote (stripMarks e)
  | .num n => .num n

theorem stripMarks_idempotent (e : Expr) : stripMarks (stripMarks e) = stripMarks e := by
  induction e with
  | var x => simp [stripMarks]
  | lam x body ih => simp [stripMarks, ih]
  | app f a ihf iha => simp [stripMarks, ihf, iha]
  | letE x e body ihe ihb => simp [stripMarks, ihe, ihb]
  | quote e ih => simp [stripMarks, ih]
  | unquote e ih => simp [stripMarks, ih]
  | num n => simp [stripMarks]

theorem applyMark_num (m : Mark) (n : Nat) : applyMark m (.num n) = .num n := rfl
theorem applyMark_app (m : Mark) (f a : Expr) :
    applyMark m (.app f a) = .app (applyMark m f) (applyMark m a) := rfl
theorem stripMarks_app (f a : Expr) :
    stripMarks (.app f a) = .app (stripMarks f) (stripMarks a) := rfl
theorem strip_lam_decompose (x : MarkedId) (body : Expr) :
    stripMarks (.lam x body) = .lam ⟨x.name, []⟩ (stripMarks body) := rfl

-- ============================================================
-- Substitution
-- ============================================================

def subst (e : Expr) (x : MarkedId) (s : Expr) : Expr :=
  match e with
  | .var y => if y = x then s else .var y
  | .lam y body => if y = x then .lam y body else .lam y (subst body x s)
  | .app f a => .app (subst f x s) (subst a x s)
  | .letE y def_ body =>
    if y = x then .letE y (subst def_ x s) body
    else .letE y (subst def_ x s) (subst body x s)
  | .quote e => .quote (subst e x s)
  | .unquote e => .unquote (subst e x s)
  | .num n => .num n

theorem subst_num (x : MarkedId) (s : Expr) (n : Nat) :
    subst (.num n) x s = .num n := rfl

theorem subst_var_same (x : MarkedId) (s : Expr) :
    subst (.var x) x s = s := by simp [subst]

theorem subst_var_diff (x y : MarkedId) (s : Expr) (h : y ≠ x) :
    subst (.var y) x s = .var y := by simp [subst, h]

theorem subst_lam_shadow (x : MarkedId) (body s : Expr) :
    subst (.lam x body) x s = .lam x body := by simp [subst]

theorem subst_app (f a : Expr) (x : MarkedId) (s : Expr) :
    subst (.app f a) x s = .app (subst f x s) (subst a x s) := rfl

-- ============================================================
-- Free Variables
-- ============================================================

def freeVars : Expr → List MarkedId
  | .var x => [x]
  | .lam x body => (freeVars body).filter (· != x)
  | .app f a => freeVars f ++ freeVars a
  | .letE x e body => freeVars e ++ (freeVars body).filter (· != x)
  | .quote e => freeVars e
  | .unquote e => freeVars e
  | .num _ => []

def allVars : Expr → List MarkedId
  | .var x => [x]
  | .lam x body => x :: allVars body
  | .app f a => allVars f ++ allVars a
  | .letE x e body => x :: (allVars e ++ allVars body)
  | .quote e => allVars e
  | .unquote e => allVars e
  | .num _ => []

theorem freeVars_num (n : Nat) : freeVars (.num n) = [] := rfl
theorem freeVars_var (x : MarkedId) : freeVars (.var x) = [x] := rfl
theorem allVars_num (n : Nat) : allVars (.num n) = [] := rfl

-- ============================================================
-- Clean Expressions and Freshness
-- ============================================================

def isClean : Expr → Prop
  | .var x => x.marks = []
  | .lam x body => x.marks = [] ∧ isClean body
  | .app f a => isClean f ∧ isClean a
  | .letE x e body => x.marks = [] ∧ isClean e ∧ isClean body
  | .quote e => isClean e
  | .unquote e => isClean e
  | .num _ => True

theorem isClean_num (n : Nat) : isClean (.num n) := trivial

theorem isClean_var (n : RawName) : isClean (.var ⟨n, []⟩) := by simp [isClean]

theorem isClean_stripMarks (e : Expr) : isClean (stripMarks e) := by
  induction e with
  | var x => simp [stripMarks, isClean]
  | lam _ _ ih => exact ⟨rfl, ih⟩
  | app _ _ ihf iha => exact ⟨ihf, iha⟩
  | letE _ _ _ ihe ihb => exact ⟨rfl, ihe, ihb⟩
  | quote _ ih => exact ih
  | unquote _ ih => exact ih
  | num _ => trivial

def freshFor (m : Mark) (e : Expr) : Prop :=
  ∀ x ∈ allVars e, m ∉ x.marks

theorem freshFor_num (m : Mark) (n : Nat) : freshFor m (.num n) := by
  simp [freshFor, allVars]

theorem freshFor_var (m : Mark) (x : MarkedId) (h : m ∉ x.marks) :
    freshFor m (.var x) := by
  simp [freshFor, allVars]; exact h

-- ============================================================
-- Capture Avoidance
-- ============================================================

theorem mark_extends_list (x : MarkedId) (m : Mark) :
    (⟨x.name, x.marks ++ [m]⟩ : MarkedId).marks = x.marks ++ [m] := rfl

theorem mark_changes_id (x : MarkedId) (m : Mark) :
    (⟨x.name, x.marks ++ [m]⟩ : MarkedId) ≠ x := by
  intro h
  have hmarks : x.marks ++ [m] = x.marks := by
    have h2 := congrArg MarkedId.marks h; simp at h2
  have hlen : (x.marks ++ [m]).length = x.marks.length := congrArg List.length hmarks
  simp [List.length_append] at hlen

theorem capture_avoidance_var (m : Mark) (x : MarkedId) :
    (⟨x.name, x.marks ++ [m]⟩ : MarkedId) ≠ x :=
  mark_changes_id x m

theorem mark_count_increases (x : MarkedId) (m : Mark) :
    (⟨x.name, x.marks ++ [m]⟩ : MarkedId).marks.length = x.marks.length + 1 := by
  simp [List.length_append]

theorem double_mark_distinct (x : MarkedId) (m1 m2 : Mark) :
    (⟨x.name, x.marks ++ [m1, m2]⟩ : MarkedId).marks.length = x.marks.length + 2 := by
  simp [List.length_append]

theorem marked_ids_diff_marks_ne (x y : MarkedId) (h : x.marks ≠ y.marks) : x ≠ y := by
  intro heq; exact h (congrArg MarkedId.marks heq)

-- ============================================================
-- Strip-Mark Commutation
-- ============================================================

theorem strip_after_mark_var (m : Mark) (x : MarkedId) :
    stripMarks (applyMark m (.var x)) = .var ⟨x.name, []⟩ := by
  simp [applyMark, stripMarks]

theorem strip_after_mark_num (m : Mark) (n : Nat) :
    stripMarks (applyMark m (.num n)) = .num n := by
  simp [applyMark, stripMarks]

theorem strip_mark_eq_strip (m : Mark) (e : Expr) :
    stripMarks (applyMark m e) = stripMarks e := by
  induction e with
  | var x => simp [applyMark, stripMarks]
  | lam x body ih => simp [applyMark, stripMarks, ih]
  | app f a ihf iha => simp [applyMark, stripMarks, ihf, iha]
  | letE x e body ihe ihb => simp [applyMark, stripMarks, ihe, ihb]
  | quote e ih => simp [applyMark, stripMarks, ih]
  | unquote e ih => simp [applyMark, stripMarks, ih]
  | num n => simp [applyMark, stripMarks]

-- ============================================================
-- Template-Based Macros
-- ============================================================

inductive Pattern where
  | pVar : RawName → Pattern
  | pLit : Nat → Pattern
  | pApp : Pattern → Pattern → Pattern
  | pWild : Pattern
deriving DecidableEq, Repr

inductive Template where
  | tVar : RawName → Template
  | tLit : Nat → Template
  | tApp : Template → Template → Template
  | tLam : RawName → Template → Template
deriving DecidableEq, Repr

structure MacroRule where
  pattern : Pattern
  template : Template
deriving Repr

abbrev MatchEnv := List (RawName × Expr)

def matchEnvLookup (env : MatchEnv) (n : RawName) : Option Expr :=
  match env with
  | [] => none
  | (k, v) :: rest => if k = n then some v else matchEnvLookup rest n

def matchPattern : Pattern → Expr → Option MatchEnv
  | .pVar n, e => some [(n, e)]
  | .pLit n, .num m => if n = m then some [] else none
  | .pApp p1 p2, .app e1 e2 => do
    let env1 ← matchPattern p1 e1
    let env2 ← matchPattern p2 e2
    some (env1 ++ env2)
  | .pWild, _ => some []
  | _, _ => none

def instantiate (env : MatchEnv) (m : Mark) : Template → Expr
  | .tVar n =>
    match matchEnvLookup env n with
    | some e => e
    | none => .var ⟨n, [m]⟩
  | .tLit n => .num n
  | .tApp t1 t2 => .app (instantiate env m t1) (instantiate env m t2)
  | .tLam n t => .lam ⟨n, [m]⟩ (instantiate env m t)

-- ============================================================
-- Pattern Matching Properties
-- ============================================================

theorem matchPattern_wild (e : Expr) : matchPattern .pWild e = some [] := rfl
theorem matchPattern_pvar (n : RawName) (e : Expr) :
    matchPattern (.pVar n) e = some [(n, e)] := rfl

theorem matchPattern_lit_same (n : Nat) :
    matchPattern (.pLit n) (.num n) = some [] := by simp [matchPattern]

theorem matchPattern_lit_diff (n m : Nat) (h : n ≠ m) :
    matchPattern (.pLit n) (.num m) = none := by simp [matchPattern, h]

-- ============================================================
-- Instantiation Properties
-- ============================================================

theorem instantiate_lit (env : MatchEnv) (m : Mark) (n : Nat) :
    instantiate env m (.tLit n) = .num n := rfl

theorem instantiate_app (env : MatchEnv) (m : Mark) (t1 t2 : Template) :
    instantiate env m (.tApp t1 t2) =
    .app (instantiate env m t1) (instantiate env m t2) := rfl

theorem instantiate_bound_var (env : MatchEnv) (m : Mark) (n : RawName) (e : Expr)
    (h : matchEnvLookup env n = some e) :
    instantiate env m (.tVar n) = e := by simp [instantiate, h]

theorem instantiate_free_var (env : MatchEnv) (m : Mark) (n : RawName)
    (h : matchEnvLookup env n = none) :
    instantiate env m (.tVar n) = .var ⟨n, [m]⟩ := by simp [instantiate, h]

-- ============================================================
-- Macro Expansion
-- ============================================================

abbrev MacroSystem := List MacroRule

structure ExpState where
  nextMark : Nat
deriving Repr

def freshMark (st : ExpState) : Mark × ExpState :=
  (⟨st.nextMark⟩, ⟨st.nextMark + 1⟩)

def tryExpand (sys : MacroSystem) (e : Expr) (st : ExpState) : Option (Expr × ExpState) :=
  match sys with
  | [] => none
  | rule :: rest =>
    match matchPattern rule.pattern e with
    | some env =>
      let (m, st') := freshMark st
      some (instantiate env m rule.template, st')
    | none => tryExpand rest e st

theorem tryExpand_empty (e : Expr) (st : ExpState) : tryExpand [] e st = none := rfl
theorem freshMark_advances (st : ExpState) :
    (freshMark st).2.nextMark = st.nextMark + 1 := rfl

-- ============================================================
-- Scope Resolution
-- ============================================================

structure Scope where
  binder : MarkedId
  introMark : Option Mark
deriving DecidableEq, Repr

def resolveScope (scopes : List Scope) (x : MarkedId) : Option Scope :=
  scopes.find? (fun s => s.binder = x)

theorem resolveScope_deterministic (scopes : List Scope) (x : MarkedId)
    (s1 s2 : Scope)
    (h1 : resolveScope scopes x = some s1)
    (h2 : resolveScope scopes x = some s2) :
    s1 = s2 := by rw [h1] at h2; exact Option.some.inj h2

theorem resolveScope_nil (x : MarkedId) : resolveScope [] x = none := by
  simp [resolveScope, List.find?]

-- ============================================================
-- Expression Contexts
-- ============================================================

inductive ExprCtx where
  | hole : ExprCtx
  | lamCtx : MarkedId → ExprCtx → ExprCtx
  | appLCtx : ExprCtx → Expr → ExprCtx
  | appRCtx : Expr → ExprCtx → ExprCtx
deriving Repr

def plug : ExprCtx → Expr → Expr
  | .hole, e => e
  | .lamCtx x c, e => .lam x (plug c e)
  | .appLCtx c a, e => .app (plug c e) a
  | .appRCtx f c, e => .app f (plug c e)

theorem plug_hole (e : Expr) : plug .hole e = e := rfl
theorem plug_app_left (c : ExprCtx) (a e : Expr) :
    plug (.appLCtx c a) e = .app (plug c e) a := rfl
theorem plug_app_right (f : Expr) (c : ExprCtx) (e : Expr) :
    plug (.appRCtx f c) e = .app f (plug c e) := rfl
theorem plug_lam (x : MarkedId) (c : ExprCtx) (e : Expr) :
    plug (.lamCtx x c) e = .lam x (plug c e) := rfl

-- ============================================================
-- Alpha Equivalence
-- ============================================================

def alphaEquiv : List (MarkedId × MarkedId) → Expr → Expr → Prop
  | ctx, .var x, .var y =>
    (x, y) ∈ ctx ∨ (x = y ∧ ∀ p ∈ ctx, p.1 ≠ x ∧ p.2 ≠ y)
  | ctx, .lam x b1, .lam y b2 => alphaEquiv ((x, y) :: ctx) b1 b2
  | ctx, .app f1 a1, .app f2 a2 => alphaEquiv ctx f1 f2 ∧ alphaEquiv ctx a1 a2
  | _, .num n, .num m => n = m
  | ctx, .quote e1, .quote e2 => alphaEquiv ctx e1 e2
  | ctx, .unquote e1, .unquote e2 => alphaEquiv ctx e1 e2
  | _, _, _ => False

def alphaEq (e1 e2 : Expr) : Prop := alphaEquiv [] e1 e2

theorem alphaEquiv_num (ctx : List (MarkedId × MarkedId)) (n : Nat) :
    alphaEquiv ctx (.num n) (.num n) := by simp [alphaEquiv]

theorem alphaEq_num (n : Nat) : alphaEq (.num n) (.num n) := alphaEquiv_num [] n

theorem alphaEq_refl_var (x : MarkedId) : alphaEq (.var x) (.var x) := by
  simp [alphaEq, alphaEquiv]

theorem alphaEquiv_app (ctx : List (MarkedId × MarkedId)) (f1 a1 f2 a2 : Expr)
    (hf : alphaEquiv ctx f1 f2) (ha : alphaEquiv ctx a1 a2) :
    alphaEquiv ctx (.app f1 a1) (.app f2 a2) := ⟨hf, ha⟩

-- ============================================================
-- Marks Monotonicity
-- ============================================================

def marksMonotone (ms : List Mark) : Prop :=
  ∀ i j : Fin ms.length, i.val < j.val → (ms.get i).val < (ms.get j).val

theorem marksMonotone_nil : marksMonotone [] := by
  intro i; exact Fin.elim0 i

theorem marksMonotone_singleton (m : Mark) : marksMonotone [m] := by
  intro i j hij
  have hi := i.isLt; have hj := j.isLt
  -- [m] has length 1, so i.val < j.val < 1 is impossible
  simp only [List.length_cons, List.length_nil] at hi hj
  omega

-- ============================================================
-- matchEnvLookup properties
-- ============================================================

theorem matchEnvLookup_nil (n : RawName) : matchEnvLookup [] n = none := rfl

theorem matchEnvLookup_hit (n : RawName) (e : Expr) (rest : MatchEnv) :
    matchEnvLookup ((n, e) :: rest) n = some e := by simp [matchEnvLookup]

theorem matchEnvLookup_miss (k n : RawName) (e : Expr) (rest : MatchEnv) (h : k ≠ n) :
    matchEnvLookup ((k, e) :: rest) n = matchEnvLookup rest n := by
  simp [matchEnvLookup, h]

end HygienicMacros
