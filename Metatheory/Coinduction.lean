/-
  Metatheory / Coinduction.lean

  Coinduction: Greatest Fixed Points, Coinductive Types, Bisimulation
  =====================================================================
  Streams, infinite trees, bisimulation as coinductive proof principle,
  productivity, guardedness, coinductive predicates.

  All proofs are sorry-free.  Multi-step trans / symm / congrArg chains.
  Paths ARE the math.
-/

set_option linter.unusedVariables false

namespace Coinduction

-- ============================================================================
-- §1  Streams as Nat → α  (function-based coinductive type)
-- ============================================================================

/-- A stream is a function from Nat to α. -/
def Stream (α : Type) := Nat → α

/-- Head of a stream. -/
def Stream.head (s : Stream α) : α := s 0

/-- Tail of a stream. -/
def Stream.tail (s : Stream α) : Stream α := fun n => s (n + 1)

/-- Cons: prepend an element. -/
def Stream.cons (a : α) (s : Stream α) : Stream α
  | 0 => a
  | n + 1 => s n

/-- A constant stream. -/
def Stream.const (a : α) : Stream α := fun _ => a

/-- Take first n elements. -/
def Stream.take : Nat → Stream α → List α
  | 0, _ => []
  | n + 1, s => s.head :: Stream.take n s.tail

/-- Theorem 1: head of const is the constant. -/
theorem Stream.const_head (a : α) : (Stream.const a).head = a := rfl

/-- Theorem 2: tail of const is const. -/
theorem Stream.const_tail (a : α) : (Stream.const a).tail = Stream.const a := rfl

/-- Theorem 3: head of cons. -/
theorem Stream.cons_head (a : α) (s : Stream α) : (Stream.cons a s).head = a := rfl

/-- Theorem 4: tail of cons. -/
theorem Stream.cons_tail (a : α) (s : Stream α) : (Stream.cons a s).tail = s := rfl

/-- Theorem 5: take 0 is empty. -/
theorem Stream.take_zero (s : Stream α) : Stream.take 0 s = [] := rfl

/-- Theorem 6: take (n+1) = head :: take n tail. -/
theorem Stream.take_succ (n : Nat) (s : Stream α) :
    Stream.take (n + 1) s = s.head :: Stream.take n s.tail := rfl

/-- Theorem 7: Length of take n is n. -/
theorem Stream.take_length (n : Nat) (s : Stream α) :
    (Stream.take n s).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [Stream.take, ih]

-- ============================================================================
-- §2  Bisimulation
-- ============================================================================

/-- A bisimulation: a relation where related streams agree on head
    and their tails are related. -/
structure Bisimulation (α : Type) where
  rel : Stream α → Stream α → Prop
  head_eq : ∀ s t, rel s t → s.head = t.head
  tail_rel : ∀ s t, rel s t → rel s.tail t.tail

/-- Stream extensional equality. -/
def StreamEq (s t : Stream α) : Prop := ∀ n, s n = t n

/-- Theorem 8: StreamEq is reflexive. -/
theorem StreamEq.refl (s : Stream α) : StreamEq s s :=
  fun _ => Eq.refl _

/-- Theorem 9: StreamEq is symmetric (symm chain). -/
theorem StreamEq.symm {s t : Stream α} (h : StreamEq s t) : StreamEq t s :=
  fun n => Eq.symm (h n)

/-- Theorem 10: StreamEq is transitive (trans chain). -/
theorem StreamEq.trans {s t u : Stream α}
    (h1 : StreamEq s t) (h2 : StreamEq t u) : StreamEq s u :=
  fun n => Eq.trans (h1 n) (h2 n)

/-- Helper: bisimulation implies pointwise equality at depth n. -/
theorem bisim_at_depth {α : Type} (B : Bisimulation α)
    {s t : Stream α} (h : B.rel s t) (n : Nat) : s n = t n := by
  induction n generalizing s t with
  | zero => exact B.head_eq s t h
  | succ n ih =>
    have htail := B.tail_rel s t h
    exact ih htail

/-- Theorem 11: A bisimulation implies StreamEq (coinduction principle). -/
theorem bisim_implies_streamEq {α : Type} (B : Bisimulation α)
    {s t : Stream α} (h : B.rel s t) : StreamEq s t :=
  fun n => bisim_at_depth B h n

-- ============================================================================
-- §3  Stream Transformations
-- ============================================================================

/-- Map a function over a stream. -/
def Stream.map (f : α → β) (s : Stream α) : Stream β := fun n => f (s n)

/-- Theorem 12: map preserves head (congrArg). -/
theorem Stream.map_head (f : α → β) (s : Stream α) :
    (Stream.map f s).head = f s.head := rfl

/-- Theorem 13: map commutes with tail. -/
theorem Stream.map_tail (f : α → β) (s : Stream α) :
    (Stream.map f s).tail = Stream.map f s.tail := rfl

/-- Theorem 14: map distributes over take. -/
theorem Stream.map_take (f : α → β) (n : Nat) (s : Stream α) :
    Stream.take n (Stream.map f s) = (Stream.take n s).map f := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp [Stream.take]
    constructor
    · rfl
    · exact ih s.tail

/-- Theorem 15: map id is identity. -/
theorem Stream.map_id (s : Stream α) : StreamEq (Stream.map id s) s :=
  fun _ => rfl

/-- Theorem 16: map composition. -/
theorem Stream.map_comp (f : α → β) (g : β → γ) (s : Stream α) :
    StreamEq (Stream.map g (Stream.map f s)) (Stream.map (g ∘ f) s) :=
  fun _ => rfl

-- ============================================================================
-- §4  Coinductive Paths (rewriting steps on streams)
-- ============================================================================

/-- A step in stream rewriting. -/
inductive StreamStep (α : Type) : Stream α → Stream α → Type where
  | pointwise (s t : Stream α) (h : StreamEq s t) : StreamStep α s t
  | mapId (s : Stream α) : StreamStep α (Stream.map id s) s

/-- Computational path of stream rewrites. -/
inductive StreamPath (α : Type) : Stream α → Stream α → Type where
  | refl (s : Stream α) : StreamPath α s s
  | step {a b c} : StreamStep α a b → StreamPath α b c → StreamPath α a c

/-- Theorem 17: Transitivity of stream paths. -/
def StreamPath.trans : StreamPath α a b → StreamPath α b c → StreamPath α a c
  | .refl _, q => q
  | .step s p, q => .step s (p.trans q)

/-- Theorem 18: Single step lifts to path. -/
def StreamPath.single (s : StreamStep α a b) : StreamPath α a b :=
  .step s (.refl _)

/-- Stream path length. -/
def StreamPath.length : StreamPath α a b → Nat
  | .refl _ => 0
  | .step _ p => 1 + p.length

/-- Theorem 19: Length is additive. -/
theorem StreamPath.length_trans (p : StreamPath α a b) (q : StreamPath α b c) :
    (p.trans q).length = p.length + q.length := by
  induction p with
  | refl _ => simp [StreamPath.trans, StreamPath.length]
  | step s _ ih => simp [StreamPath.trans, StreamPath.length, ih, Nat.add_assoc]

-- ============================================================================
-- §5  Infinite Trees
-- ============================================================================

/-- An infinite binary tree as a function from paths (list of booleans). -/
def InfTree (α : Type) := List Bool → α

/-- Label at root. -/
def InfTree.root (t : InfTree α) : α := t []

/-- Left subtree. -/
def InfTree.left (t : InfTree α) : InfTree α := fun path => t (false :: path)

/-- Right subtree. -/
def InfTree.right (t : InfTree α) : InfTree α := fun path => t (true :: path)

/-- Constant tree. -/
def InfTree.const (a : α) : InfTree α := fun _ => a

/-- Theorem 20: Constant tree root. -/
theorem InfTree.const_root (a : α) : (InfTree.const a).root = a := rfl

/-- Theorem 21: Left subtree of constant tree is constant. -/
theorem InfTree.const_left (a : α) :
    (InfTree.const a).left = InfTree.const a := rfl

/-- Theorem 22: Right subtree of constant tree is constant. -/
theorem InfTree.const_right (a : α) :
    (InfTree.const a).right = InfTree.const a := rfl

/-- Tree extensional equality. -/
def TreeEq (s t : InfTree α) : Prop := ∀ p, s p = t p

/-- Theorem 23: TreeEq is reflexive. -/
theorem TreeEq.refl (t : InfTree α) : TreeEq t t := fun _ => Eq.refl _

/-- Theorem 24: TreeEq is symmetric. -/
theorem TreeEq.symm {s t : InfTree α} (h : TreeEq s t) : TreeEq t s :=
  fun p => Eq.symm (h p)

/-- Theorem 25: TreeEq is transitive. -/
theorem TreeEq.trans {s t u : InfTree α}
    (h1 : TreeEq s t) (h2 : TreeEq t u) : TreeEq s u :=
  fun p => Eq.trans (h1 p) (h2 p)

-- ============================================================================
-- §6  Greatest Fixed Point (abstract)
-- ============================================================================

/-- A monotone operator on predicates. -/
structure MonoOp (α : Type) where
  F : (α → Prop) → (α → Prop)
  mono : ∀ P Q : α → Prop, (∀ x, P x → Q x) → ∀ x, F P x → F Q x

/-- The greatest fixed point (νF): x ∈ νF iff there exists a post-fixed
    point containing x. -/
def GFP (op : MonoOp α) (x : α) : Prop :=
  ∃ P : α → Prop, (∀ y, P y → op.F P y) ∧ P x

/-- Theorem 26: GFP is a post-fixed point. -/
theorem gfp_post_fixed (op : MonoOp α) :
    ∀ x, GFP op x → op.F (GFP op) x := by
  intro x ⟨P, hpost, hx⟩
  apply op.mono P (GFP op)
  · intro y hy; exact ⟨P, hpost, hy⟩
  · exact hpost x hx

/-- Theorem 27: GFP is the greatest post-fixed point. -/
theorem gfp_greatest (op : MonoOp α) (P : α → Prop)
    (hpost : ∀ y, P y → op.F P y) :
    ∀ x, P x → GFP op x :=
  fun x hx => ⟨P, hpost, hx⟩

-- ============================================================================
-- §7  Coinductive Predicates (bounded approximation)
-- ============================================================================

/-- AlwaysBounded p n s: the first n elements satisfy p. -/
def AlwaysBounded (p : α → Prop) : Nat → Stream α → Prop
  | 0, _ => True
  | n + 1, s => p (s.head) ∧ AlwaysBounded p n s.tail

/-- Theorem 28: AlwaysBounded at 0 is trivially true. -/
theorem alwaysBounded_zero (p : α → Prop) (s : Stream α) :
    AlwaysBounded p 0 s = True := rfl

/-- Theorem 29: AlwaysBounded unfolds correctly. -/
theorem alwaysBounded_succ (p : α → Prop) (n : Nat) (s : Stream α) :
    AlwaysBounded p (n + 1) s = (p s.head ∧ AlwaysBounded p n s.tail) := rfl

/-- Theorem 30: AlwaysBounded is monotone in depth. -/
theorem alwaysBounded_mono (p : α → Prop) {n : Nat} {s : Stream α}
    (h : AlwaysBounded p (n + 1) s) : AlwaysBounded p n s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    simp [AlwaysBounded] at h ⊢
    exact ⟨h.1, ih h.2⟩

/-- Theorem 31: AlwaysBounded on const stream. -/
theorem alwaysBounded_const (p : α → Prop) (a : α) (hp : p a) (n : Nat) :
    AlwaysBounded p n (Stream.const a) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hp, ih⟩

-- ============================================================================
-- §8  Guardedness / Productivity
-- ============================================================================

/-- A guarded definition: produces a head before recursing. -/
structure GuardedDef (α : Type) where
  seed : α
  next : α → α

/-- Unfold a guarded definition to a stream (iterate). -/
def GuardedDef.toStream (g : GuardedDef α) : Stream α :=
  fun n => Nat.rec g.seed (fun _ ih => g.next ih) n

/-- Theorem 32: Guarded definition produces correct head. -/
theorem GuardedDef.toStream_head (g : GuardedDef α) :
    g.toStream.head = g.seed := rfl

/-- Theorem 33: Guarded definition produces correct second element. -/
theorem GuardedDef.toStream_one (g : GuardedDef α) :
    g.toStream 1 = g.next g.seed := rfl

-- ============================================================================
-- §9  Bisimulation Path
-- ============================================================================

/-- Step in a bisimulation proof chain. -/
inductive BisimStep : (Stream α → Stream α → Prop) →
    (Stream α → Stream α → Prop) → Type 1 where
  | refine (R S : Stream α → Stream α → Prop)
      (h : ∀ s t, R s t → S s t) : BisimStep R S

/-- Bisimulation proof path. -/
inductive BisimPath : (Stream α → Stream α → Prop) →
    (Stream α → Stream α → Prop) → Type 1 where
  | refl (R : Stream α → Stream α → Prop) : BisimPath R R
  | step {R S T} : BisimStep R S → BisimPath S T → BisimPath R T

/-- Theorem 34: Transitivity of bisimulation paths. -/
def BisimPath.trans : BisimPath R S → BisimPath S T → BisimPath R T
  | .refl _, q => q
  | .step s p, q => .step s (p.trans q)

/-- Theorem 35: Bisimulation path transport. -/
theorem bisimPath_transport :
    BisimPath R S → (∀ s t, R s t → S s t)
  | .refl _ => fun _ _ h => h
  | .step (.refine _ _ hRS) p => fun s t hR =>
      bisimPath_transport p s t (hRS s t hR)

-- ============================================================================
-- §10  Coinduction Principle as Path
-- ============================================================================

/-- The coinduction principle: to prove StreamEq, exhibit a bisimulation. -/
theorem coinduction_principle {α : Type} {s t : Stream α}
    (R : Stream α → Stream α → Prop)
    (hHead : ∀ a b, R a b → a.head = b.head)
    (hTail : ∀ a b, R a b → R a.tail b.tail)
    (hst : R s t) : StreamEq s t :=
  bisim_implies_streamEq ⟨R, hHead, hTail⟩ hst

-- ============================================================================
-- §11  congrArg for StreamEq
-- ============================================================================

/-- Theorem 36: congrArg — map preserves StreamEq. -/
theorem StreamEq.congrArg_map (f : α → β) {s t : Stream α}
    (h : StreamEq s t) : StreamEq (Stream.map f s) (Stream.map f t) :=
  fun n => congrArg f (h n)

/-- Theorem 37: congrArg — cons preserves StreamEq on tail. -/
theorem StreamEq.congrArg_cons (a : α) {s t : Stream α}
    (h : StreamEq s t) : StreamEq (Stream.cons a s) (Stream.cons a t) := by
  intro n
  cases n with
  | zero => rfl
  | succ n => exact h n

/-- Theorem 38: StreamEq three-way trans chain. -/
theorem streamEq_trans_chain {a b c d : Stream α}
    (h1 : StreamEq a b) (h2 : StreamEq b c) (h3 : StreamEq c d) :
    StreamEq a d :=
  StreamEq.trans (StreamEq.trans h1 h2) h3

/-- Theorem 39: StreamPath refl has length 0. -/
theorem streamPath_refl_length (s : Stream α) :
    (StreamPath.refl s).length = 0 := rfl

/-- Theorem 40: Single step has length 1. -/
theorem streamPath_single_length (s : StreamStep α a b) :
    (StreamPath.single s).length = 1 := rfl

end Coinduction
