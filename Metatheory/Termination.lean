/-
  Metatheory / Termination.lean

  Termination analysis for rewriting systems.
  Covers: well-founded orders, lexicographic ordering, multiset ordering,
  polynomial interpretations, dependency pairs, size-change termination,
  Ackermann function termination proof.

  All proofs are sorry-free.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

-- ============================================================
-- §1  Well-founded orders
-- ============================================================

/-- A relation is well-founded when every element is accessible. -/
def WellFounded' (α : Type) (r : α → α → Prop) : Prop :=
  ∀ a, Acc r a

/-- Theorem 1: The empty type has every relation well-founded. -/
theorem empty_wf : WellFounded' Empty (fun _ _ => True) := by
  intro a; exact a.elim

/-- Theorem 2: Nat < is well-founded (wrapping the stdlib). -/
theorem nat_lt_wf' : WellFounded' Nat (· < ·) := by
  intro a; exact (Nat.lt_wfRel.wf).apply a

/-- Theorem 3: No infinite descending chain from 0. -/
theorem no_descent_from_zero (f : Nat → Nat) (hf : ∀ n, f (n + 1) < f n)
    (h0 : f 0 = 0) : False := by
  have := hf 0; omega

/-- Theorem 4: A strictly decreasing function on Nat eventually reaches 0. -/
theorem decreasing_reaches_zero (f : Nat → Nat) (hf : ∀ n, f (n + 1) < f n) :
    ∀ n, f n ≤ f 0 - n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih => have := hf n; omega

-- ============================================================
-- §2  Lexicographic ordering
-- ============================================================

/-- Lexicographic order on pairs. -/
inductive LexLt (r₁ : α → α → Prop) (r₂ : β → β → Prop) :
    α × β → α × β → Prop where
  | left  {a₁ a₂ : α} (b₁ b₂ : β) : r₁ a₁ a₂ → LexLt r₁ r₂ (a₁, b₁) (a₂, b₂)
  | right (a : α) {b₁ b₂ : β} : r₂ b₁ b₂ → LexLt r₁ r₂ (a, b₁) (a, b₂)

/-- Theorem 5: Lex order left component strictly decreasing. -/
theorem lex_left_decreasing (a₁ a₂ : Nat) (b₁ b₂ : Nat) (h : a₁ < a₂) :
    LexLt (· < ·) (· < ·) (a₁, b₁) (a₂, b₂) :=
  LexLt.left b₁ b₂ h

/-- Theorem 6: Lex order right component decreasing when left equal. -/
theorem lex_right_decreasing (a : Nat) (b₁ b₂ : Nat) (h : b₁ < b₂) :
    LexLt (· < ·) (· < ·) (a, b₁) (a, b₂) :=
  LexLt.right a h

/-- Theorem 7: Lex order is irreflexive when components are. -/
theorem lex_irrefl (p : Nat × Nat) :
    ¬ LexLt (· < ·) (· < ·) p p := by
  intro h
  cases h with
  | left _ _ h => omega
  | right _ h => omega

/-- Theorem 8: Lex order is transitive. -/
theorem lex_trans {p₁ p₂ p₃ : Nat × Nat}
    (h₁ : LexLt (· < ·) (· < ·) p₁ p₂)
    (h₂ : LexLt (· < ·) (· < ·) p₂ p₃) :
    LexLt (· < ·) (· < ·) p₁ p₃ := by
  cases h₁ with
  | left b₁ b₂ ha₁ =>
    cases h₂ with
    | left b₃ b₄ ha₂ => exact LexLt.left _ _ (by omega)
    | right _ hb₂ => exact LexLt.left _ _ ha₁
  | right a hb₁ =>
    cases h₂ with
    | left b₃ b₄ ha₂ => exact LexLt.left _ _ ha₂
    | right _ hb₂ => exact LexLt.right _ (by omega)

-- ============================================================
-- §3  Multiset ordering (via lists of Nat)
-- ============================================================

/-- Sum of a list of Nats. -/
def listSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum xs

/-- Theorem 9: Empty list has sum 0. -/
theorem listSum_nil : listSum [] = 0 := rfl

/-- Theorem 10: Sum distributes over append. -/
theorem listSum_append (xs ys : List Nat) :
    listSum (xs ++ ys) = listSum xs + listSum ys := by
  induction xs with
  | nil => simp [listSum]
  | cons x xs ih => simp [listSum, ih]; omega

/-- Theorem 11: Replacing n by m < n strictly decreases the sum. -/
theorem replace_decreases (pre suf : List Nat) (n m : Nat) (h : m < n) :
    listSum (pre ++ [m] ++ suf) < listSum (pre ++ [n] ++ suf) := by
  simp [listSum_append, listSum]
  omega

-- ============================================================
-- §4  Polynomial interpretations
-- ============================================================

/-- A polynomial interpretation maps symbols to monotone functions. -/
structure PolyInterp where
  interp : Nat → Nat → Nat
  monotone : ∀ sym a b, a < b → interp sym a < interp sym b

/-- Theorem 12: x + 1 is a valid monotone interpretation. -/
theorem succ_monotone : ∀ a b : Nat, a < b → a + 1 < b + 1 := by
  intros; omega

/-- Theorem 13: Composition of monotone functions is monotone. -/
theorem compose_monotone {f g : Nat → Nat}
    (hf : ∀ a b, a < b → f a < f b) (hg : ∀ a b, a < b → g a < g b) :
    ∀ a b, a < b → f (g a) < f (g b) := by
  intro a b hab
  exact hf _ _ (hg a b hab)

/-- Theorem 14: A polynomial interpretation proves termination when
    lhs > rhs under interpretation. -/
theorem poly_interp_terminates (interp : Nat → Nat)
    (hm : ∀ a b, a < b → interp a < interp b)
    (lhs rhs : Nat) (h : rhs < lhs) :
    interp rhs < interp lhs :=
  hm rhs lhs h

-- ============================================================
-- §5  Dependency pairs
-- ============================================================

/-- A dependency pair: (caller, callee). -/
structure DepPair where
  caller : Nat
  callee : Nat
deriving DecidableEq, Repr

/-- A dependency pair graph. -/
abbrev DPGraph := List DepPair

/-- A graph has a self-loop if some pair calls itself. -/
def hasSelfLoop (g : DPGraph) : Bool :=
  g.any (fun dp => dp.caller == dp.callee)

/-- Theorem 15: No self-loops in an empty graph. -/
theorem empty_no_self_loop : hasSelfLoop [] = false := rfl

/-- Theorem 16: A non-recursive pair has no self-loop. -/
theorem single_nonrec (f g : Nat) (h : f ≠ g) :
    hasSelfLoop [⟨f, g⟩] = false := by
  simp [hasSelfLoop, List.any]
  omega

/-- Theorem 17: A recursive pair has a self-loop. -/
theorem single_rec (f : Nat) :
    hasSelfLoop [⟨f, f⟩] = true := by
  simp [hasSelfLoop, List.any]

-- ============================================================
-- §6  Size-change termination
-- ============================================================

/-- A size-change graph edge: source param → dest param, strict? -/
structure SCEdge where
  src : Nat
  dst : Nat
  strict : Bool
deriving DecidableEq, Repr

/-- A size-change graph for one call site. -/
structure SCGraph where
  edges : List SCEdge
deriving Repr

/-- Compose two size-change graphs (thread analysis). -/
def SCGraph.compose (g₁ g₂ : SCGraph) : SCGraph :=
  { edges := g₁.edges.flatMap (fun e₁ =>
      (g₂.edges.filter (fun e₂ => e₁.dst == e₂.src)).map (fun e₂ =>
        { src := e₁.src, dst := e₂.dst, strict := e₁.strict || e₂.strict })) }

/-- Has at least one strictly decreasing edge. -/
def SCGraph.hasStrictDescent (g : SCGraph) : Bool :=
  g.edges.any (fun e => e.strict)

/-- Theorem 18: A single strict edge gives strict descent. -/
theorem single_strict_descent (s d : Nat) :
    SCGraph.hasStrictDescent ⟨[⟨s, d, true⟩]⟩ = true := rfl

/-- Theorem 19: An empty graph has no strict descent. -/
theorem empty_no_descent :
    SCGraph.hasStrictDescent ⟨[]⟩ = false := rfl

/-- Theorem 20: Composing two graphs with matching strict edge yields strict result. -/
theorem compose_example :
    SCGraph.hasStrictDescent
      (SCGraph.compose ⟨[⟨0, 1, true⟩]⟩ ⟨[⟨1, 2, false⟩]⟩) = true := by native_decide

-- ============================================================
-- §7  Ackermann function termination
-- ============================================================

/-- The Ackermann function. Lean verifies termination automatically
    using a lexicographic order on (m, n). -/
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

/-- Theorem 21: ack 0 n = n + 1. -/
theorem ack_zero (n : Nat) : ack 0 n = n + 1 := by
  simp [ack]

/-- Theorem 22: ack (m+1) 0 = ack m 1. -/
theorem ack_succ_zero (m : Nat) : ack (m + 1) 0 = ack m 1 := by
  simp [ack]

/-- Theorem 23: ack (m+1) (n+1) = ack m (ack (m+1) n). -/
theorem ack_succ_succ (m n : Nat) :
    ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by
  simp [ack]

/-- Theorem 24: ack 1 n = n + 2. -/
theorem ack_one (n : Nat) : ack 1 n = n + 2 := by
  induction n with
  | zero => simp [ack]
  | succ n ih => simp [ack, ih]

/-- Theorem 25: ack 2 n = 2n + 3. -/
theorem ack_two (n : Nat) : ack 2 n = 2 * n + 3 := by
  induction n with
  | zero => native_decide
  | succ n ih =>
    rw [ack_succ_succ, ih, ack_one]
    omega

/-- Theorem 26: ack m n > n for all m, n. -/
theorem ack_gt_arg : ∀ m n, ack m n > n := by
  intro m
  induction m with
  | zero => intro n; rw [ack_zero]; omega
  | succ m ih =>
    intro n
    induction n with
    | zero =>
      rw [ack_succ_zero]
      have := ih 1; omega
    | succ n ihn =>
      rw [ack_succ_succ]
      have h1 := ihn
      have h2 := ih (ack (m + 1) n)
      omega

/-- Theorem 27: ack is always positive. -/
theorem ack_pos (m n : Nat) : ack m n ≥ 1 := by
  have := ack_gt_arg m n; omega

/-- Theorem 28: The recursive calls in ack decrease lexicographically. -/
theorem ack_lex_decrease (m n : Nat) :
    LexLt (· < ·) (· < ·) (m + 1, n) (m + 1, n + 1) ∧
    LexLt (· < ·) (· < ·) (m, ack (m + 1) n) (m + 1, n + 1) :=
  ⟨LexLt.right _ (by omega), LexLt.left _ _ (by omega)⟩

-- ============================================================
-- §8  Concrete Ackermann values
-- ============================================================

/-- Theorem 29: ack 3 0 = 5. -/
theorem ack_three_zero : ack 3 0 = 5 := by native_decide

/-- Theorem 30: ack 3 1 = 13. -/
theorem ack_three_one : ack 3 1 = 13 := by native_decide
