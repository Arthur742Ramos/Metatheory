/-
  Syntax Transformers and Procedural Macros
-/

namespace SyntaxTransformers

-- ============================================================
-- Abstract Syntax Trees
-- ============================================================

inductive AST where
  | bvar : Nat → AST
  | fvar : Nat → AST
  | abs : AST → AST
  | app : AST → AST → AST
  | lit : Nat → AST
  | node2 : Nat → AST → AST → AST
  | node1 : Nat → AST → AST
  | node0 : Nat → AST
deriving DecidableEq, Repr

def AST.size : AST → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .abs body => 1 + body.size
  | .app f a => 1 + f.size + a.size
  | .lit _ => 1
  | .node2 _ a b => 1 + a.size + b.size
  | .node1 _ a => 1 + a.size
  | .node0 _ => 1

theorem ast_size_pos (t : AST) : t.size > 0 := by
  cases t <;> simp [AST.size] <;> omega

-- ============================================================
-- Syntax Transformers
-- ============================================================

structure Transformer where
  name : String
  apply : AST → Option AST

def Transformer.matches_ (t : Transformer) (input : AST) : Prop :=
  (t.apply input).isSome

def Transformer.total_ (t : Transformer) : Prop :=
  ∀ input, t.matches_ input

def Transformer.idempotent_ (t : Transformer) : Prop :=
  ∀ input, match t.apply input with
    | some output => t.apply output = some output
    | none => True

-- ============================================================
-- Transformer Combinators
-- ============================================================

def idTransformer : Transformer := ⟨"id", fun x => some x⟩
def failTransformer : Transformer := ⟨"fail", fun _ => none⟩
def constTransformer (output : AST) : Transformer := ⟨"const", fun _ => some output⟩

def composeTransformer (t1 t2 : Transformer) : Transformer :=
  ⟨t1.name ++ " >> " ++ t2.name,
   fun x => match t1.apply x with
     | some y => t2.apply y
     | none => none⟩

def choiceTransformer (t1 t2 : Transformer) : Transformer :=
  ⟨t1.name ++ " | " ++ t2.name,
   fun x => match t1.apply x with
     | some y => some y
     | none => t2.apply x⟩

infixl:60 " >=> " => composeTransformer
infixl:50 " <|> " => choiceTransformer

-- ============================================================
-- Algebraic Laws
-- ============================================================

theorem id_left_unit (t : Transformer) (input : AST) :
    (idTransformer >=> t).apply input = t.apply input := by
  simp [composeTransformer, idTransformer]

theorem id_right_unit (t : Transformer) (input : AST) :
    (t >=> idTransformer).apply input = t.apply input := by
  simp [composeTransformer, idTransformer]
  cases t.apply input <;> simp

theorem fail_left_zero (t : Transformer) (input : AST) :
    (failTransformer >=> t).apply input = none := by
  simp [composeTransformer, failTransformer]

theorem fail_right_zero (t : Transformer) (input : AST) :
    (t >=> failTransformer).apply input = none := by
  simp [composeTransformer, failTransformer]
  cases t.apply input <;> simp

theorem compose_assoc (t1 t2 t3 : Transformer) (input : AST) :
    ((t1 >=> t2) >=> t3).apply input = (t1 >=> (t2 >=> t3)).apply input := by
  simp [composeTransformer]
  cases t1.apply input <;> simp

theorem choice_left_id (t : Transformer) (input : AST) :
    (failTransformer <|> t).apply input = t.apply input := by
  simp [choiceTransformer, failTransformer]

theorem choice_right_id (t : Transformer) (input : AST) :
    (t <|> failTransformer).apply input = t.apply input := by
  simp [choiceTransformer, failTransformer]
  cases t.apply input <;> simp

theorem choice_left_bias (t1 t2 : Transformer) (input : AST) (v : AST)
    (h : t1.apply input = some v) :
    (t1 <|> t2).apply input = some v := by
  simp [choiceTransformer, h]

-- ============================================================
-- Identity and Failure Properties
-- ============================================================

theorem id_total : idTransformer.total_ := by
  intro input; simp [Transformer.total_, Transformer.matches_, idTransformer, Option.isSome]

theorem id_idempotent : idTransformer.idempotent_ := by
  intro input; simp [Transformer.idempotent_, idTransformer]

theorem fail_not_total : ¬failTransformer.total_ := by
  intro h; have := h (.lit 0)
  simp [Transformer.matches_, failTransformer, Option.isSome] at this

theorem const_total (output : AST) : (constTransformer output).total_ := by
  intro input; simp [Transformer.matches_, constTransformer, Option.isSome]

theorem const_idempotent (output : AST) : (constTransformer output).idempotent_ := by
  intro input; simp [Transformer.idempotent_, constTransformer]

theorem const_compose_const (a b : AST) (input : AST) :
    (constTransformer a >=> constTransformer b).apply input = some b := by
  simp [composeTransformer, constTransformer]

-- ============================================================
-- Closedness
-- ============================================================

def AST.closed : AST → Prop
  | .bvar _ => False
  | .fvar _ => True
  | .abs body => body.closed
  | .app f a => f.closed ∧ a.closed
  | .lit _ => True
  | .node2 _ a b => a.closed ∧ b.closed
  | .node1 _ a => a.closed
  | .node0 _ => True

theorem lit_closed (n : Nat) : (AST.lit n).closed := by simp [AST.closed]
theorem fvar_closed (n : Nat) : (AST.fvar n).closed := by simp [AST.closed]
theorem node0_closed (tag : Nat) : (AST.node0 tag).closed := by simp [AST.closed]
theorem bvar_not_closed (n : Nat) : ¬(AST.bvar n).closed := by simp [AST.closed]

def preservesClosed (t : Transformer) : Prop :=
  ∀ input, AST.closed input →
    match t.apply input with
    | some output => AST.closed output
    | none => True

theorem id_preserves_closed : preservesClosed idTransformer := by
  intro input hclosed; simp [idTransformer]; exact hclosed

theorem fail_preserves_closed : preservesClosed failTransformer := by
  intro _ _; simp [failTransformer]

theorem compose_preserves_closed (t1 t2 : Transformer)
    (h1 : preservesClosed t1) (h2 : preservesClosed t2) :
    preservesClosed (t1 >=> t2) := by
  intro input hclosed
  simp [composeTransformer]
  cases ht1 : t1.apply input with
  | none => simp
  | some mid =>
    have hmid : AST.closed mid := by have := h1 input hclosed; rw [ht1] at this; exact this
    have := h2 mid hmid
    cases t2.apply mid <;> simp_all

-- ============================================================
-- Multi-step Expansion (bounded iteration)
-- ============================================================

/-- Apply a transformer up to n times. -/
def expandN (t : Transformer) : Nat → AST → AST
  | 0, x => x
  | n + 1, x =>
    match t.apply x with
    | some y => expandN t n y
    | none => x

theorem expandN_zero (t : Transformer) (x : AST) : expandN t 0 x = x := rfl

theorem expandN_fixpoint (t : Transformer) (n : Nat) (x : AST)
    (h : t.apply x = none) : expandN t (n + 1) x = x := by
  simp [expandN, h]

theorem expandN_step (t : Transformer) (n : Nat) (x y : AST)
    (h : t.apply x = some y) : expandN t (n + 1) x = expandN t n y := by
  simp [expandN, h]

theorem expandN_fail (n : Nat) (x : AST) : expandN failTransformer n x = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [expandN, failTransformer, ih]

theorem expandN_one_id (x : AST) :
    expandN idTransformer 1 x = x := by
  simp [expandN, idTransformer]

theorem expandN_const (n : Nat) (x output : AST) (hn : n > 0) :
    expandN (constTransformer output) n x = expandN (constTransformer output) (n - 1) output := by
  cases n with
  | zero => omega
  | succ n => simp [expandN, constTransformer]

-- ============================================================
-- Inversion Lemmas
-- ============================================================

theorem compose_some_implies_both (t1 t2 : Transformer) (input output : AST)
    (h : (t1 >=> t2).apply input = some output) :
    ∃ mid, t1.apply input = some mid ∧ t2.apply mid = some output := by
  simp [composeTransformer] at h
  cases ht1 : t1.apply input with
  | none => simp [ht1] at h
  | some mid => exact ⟨mid, rfl, by rwa [ht1] at h⟩

theorem choice_some_implies_either (t1 t2 : Transformer) (input output : AST)
    (h : (t1 <|> t2).apply input = some output) :
    t1.apply input = some output ∨ (t1.apply input = none ∧ t2.apply input = some output) := by
  simp [choiceTransformer] at h
  cases ht1 : t1.apply input with
  | none => right; exact ⟨rfl, by rwa [ht1] at h⟩
  | some v => left; rwa [ht1] at h

theorem compose_none_implies (t1 t2 : Transformer) (input : AST)
    (h : (t1 >=> t2).apply input = none) :
    t1.apply input = none ∨ ∃ mid, t1.apply input = some mid ∧ t2.apply mid = none := by
  simp [composeTransformer] at h
  cases ht1 : t1.apply input with
  | none => left; rfl
  | some mid => right; exact ⟨mid, rfl, by rwa [ht1] at h⟩

-- ============================================================
-- Determinism
-- ============================================================

theorem all_transformers_deterministic (t : Transformer) (input : AST) (o1 o2 : AST)
    (h1 : t.apply input = some o1) (h2 : t.apply input = some o2) : o1 = o2 := by
  rw [h1] at h2; exact Option.some.inj h2

-- ============================================================
-- Totality Composition
-- ============================================================

theorem choice_total_left (t1 t2 : Transformer) (h : t1.total_) :
    (t1 <|> t2).total_ := by
  intro input
  simp [Transformer.matches_, choiceTransformer]
  have := h input
  simp [Transformer.matches_] at this
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this
  simp [hv, Option.isSome]

theorem compose_total (t1 t2 : Transformer) (h1 : t1.total_) (h2 : t2.total_) :
    (t1 >=> t2).total_ := by
  intro input
  simp [Transformer.matches_, composeTransformer]
  have ht1 := h1 input
  simp [Transformer.matches_] at ht1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ht1
  simp [hv]
  have ht2 := h2 v
  simp [Transformer.matches_] at ht2
  exact ht2

-- ============================================================
-- Pipeline
-- ============================================================

structure Pipeline where
  phases : List Transformer

def Pipeline.run (p : Pipeline) (input : AST) : AST :=
  p.phases.foldl (fun acc phase =>
    match phase.apply acc with
    | some result => result
    | none => acc) input

theorem pipeline_empty (input : AST) : (Pipeline.mk []).run input = input := by
  simp [Pipeline.run]

theorem pipeline_single_some (t : Transformer) (input output : AST)
    (h : t.apply input = some output) :
    (Pipeline.mk [t]).run input = output := by
  simp [Pipeline.run, List.foldl, h]

theorem pipeline_single_none (t : Transformer) (input : AST)
    (h : t.apply input = none) :
    (Pipeline.mk [t]).run input = input := by
  simp [Pipeline.run, List.foldl, h]

-- ============================================================
-- AST Tag Properties
-- ============================================================

def AST.getTag : AST → Option Nat
  | .node2 tag _ _ => some tag
  | .node1 tag _ => some tag
  | .node0 tag => some tag
  | _ => none

theorem node2_tag (tag : Nat) (a b : AST) : (AST.node2 tag a b).getTag = some tag := rfl
theorem node1_tag (tag : Nat) (a : AST) : (AST.node1 tag a).getTag = some tag := rfl
theorem node0_tag (tag : Nat) : (AST.node0 tag).getTag = some tag := rfl
theorem lit_no_tag (n : Nat) : (AST.lit n).getTag = none := rfl
theorem bvar_no_tag (n : Nat) : (AST.bvar n).getTag = none := rfl
theorem fvar_no_tag (n : Nat) : (AST.fvar n).getTag = none := rfl

theorem different_tags_ne (t1 t2 : Nat) (a1 b1 a2 b2 : AST) (h : t1 ≠ t2) :
    AST.node2 t1 a1 b1 ≠ AST.node2 t2 a2 b2 := by
  intro heq; cases heq; exact h rfl

theorem different_tags_node1_ne (t1 t2 : Nat) (a1 a2 : AST) (h : t1 ≠ t2) :
    AST.node1 t1 a1 ≠ AST.node1 t2 a2 := by
  intro heq; cases heq; exact h rfl

theorem different_tags_node0_ne (t1 t2 : Nat) (h : t1 ≠ t2) :
    AST.node0 t1 ≠ AST.node0 t2 := by
  intro heq; cases heq; exact h rfl

-- ============================================================
-- De Bruijn Shifting
-- ============================================================

def AST.shift (d : Nat) (c : Nat) : AST → AST
  | .bvar n => if n >= c then .bvar (n + d) else .bvar n
  | .fvar n => .fvar n
  | .abs body => .abs (body.shift d (c + 1))
  | .app f a => .app (f.shift d c) (a.shift d c)
  | .lit n => .lit n
  | .node2 tag a b => .node2 tag (a.shift d c) (b.shift d c)
  | .node1 tag a => .node1 tag (a.shift d c)
  | .node0 tag => .node0 tag

theorem shift_zero (t : AST) (c : Nat) : t.shift 0 c = t := by
  induction t generalizing c with
  | bvar n =>
    simp only [AST.shift]
    split
    · simp
    · rfl
  | fvar _ => rfl
  | abs body ih => simp [AST.shift, ih]
  | app f a ihf iha => simp [AST.shift, ihf, iha]
  | lit _ => rfl
  | node2 _ a b iha ihb => simp [AST.shift, iha, ihb]
  | node1 _ a ih => simp [AST.shift, ih]
  | node0 _ => rfl

theorem shift_lit (d c n : Nat) : (AST.lit n).shift d c = .lit n := rfl
theorem shift_fvar (d c n : Nat) : (AST.fvar n).shift d c = .fvar n := rfl
theorem shift_node0 (d c tag : Nat) : (AST.node0 tag).shift d c = .node0 tag := rfl

theorem shift_bvar_below (d c n : Nat) (h : n < c) :
    (AST.bvar n).shift d c = .bvar n := by
  simp [AST.shift]; omega

theorem shift_bvar_above (d c n : Nat) (h : n ≥ c) :
    (AST.bvar n).shift d c = .bvar (n + d) := by
  simp [AST.shift]; omega

-- ============================================================
-- Additional Combinator Properties
-- ============================================================

theorem choice_idempotent (t : Transformer) (input : AST) :
    (t <|> t).apply input = t.apply input := by
  simp [choiceTransformer]; cases t.apply input <;> simp

theorem compose_id_id (input : AST) :
    (idTransformer >=> idTransformer).apply input = some input := by
  simp [composeTransformer, idTransformer]

theorem fail_choice_fail (input : AST) :
    (failTransformer <|> failTransformer).apply input = none := by
  simp [choiceTransformer, failTransformer]

-- ============================================================
-- AST Constructors Distinguished
-- ============================================================

theorem lit_ne_bvar (n m : Nat) : AST.lit n ≠ AST.bvar m := by intro h; cases h
theorem lit_ne_fvar (n m : Nat) : AST.lit n ≠ AST.fvar m := by intro h; cases h
theorem lit_ne_abs (n : Nat) (body : AST) : AST.lit n ≠ AST.abs body := by intro h; cases h
theorem lit_ne_app (n : Nat) (f a : AST) : AST.lit n ≠ AST.app f a := by intro h; cases h
theorem bvar_ne_fvar (n m : Nat) : AST.bvar n ≠ AST.fvar m := by intro h; cases h
theorem abs_ne_app (body f a : AST) : AST.abs body ≠ AST.app f a := by intro h; cases h

theorem lit_injective (n m : Nat) (h : AST.lit n = AST.lit m) : n = m := by cases h; rfl
theorem bvar_injective (n m : Nat) (h : AST.bvar n = AST.bvar m) : n = m := by cases h; rfl
theorem fvar_injective (n m : Nat) (h : AST.fvar n = AST.fvar m) : n = m := by cases h; rfl

end SyntaxTransformers
