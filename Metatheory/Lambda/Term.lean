/-
# Lambda Calculus Terms with de Bruijn Indices

This module defines lambda calculus terms using de Bruijn indices,
along with the crucial operations of shifting and substitution.

## De Bruijn Representation

Variables are represented by natural numbers (indices):
- `var 0` refers to the innermost binder
- `var 1` refers to the next outer binder
- etc.

Example: λx. λy. x y is represented as `lam (lam (app (var 1) (var 0)))`

## Key Operations

- `shift d c M` : Shift free variables ≥ c by d
- `subst j N M` : Substitute N for variable j in M
- `M[N]` : Shorthand for `subst 0 N M`
-/

namespace Metatheory.Lambda

/-! ## Term Definition -/

/-- Lambda calculus terms with de Bruijn indices -/
inductive Term : Type where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving Repr, DecidableEq

namespace Term

/-! ## Notation -/

/-- Application notation -/
scoped infixl:70 " @ " => Term.app

/-- Lambda notation -/
scoped prefix:max "ƛ " => Term.lam

/-! ## Shifting

Shifting adjusts free variable indices when moving terms under binders.
`shift d c M` adds d to all variables with index ≥ c. -/

/-- Shift free variables by d, starting from cutoff c -/
def shift (d : Int) (c : Nat) : Term → Term
  | var n => if n < c then var n else var (Int.toNat (n + d))
  | app M N => app (shift d c M) (shift d c N)
  | lam M => lam (shift d (c + 1) M)

/-- Shorthand for shifting by 1 from cutoff 0 -/
abbrev shift1 (M : Term) : Term := shift 1 0 M

/-! ## Substitution

`subst j N M` replaces variable j with N in M, adjusting indices appropriately. -/

/-- Substitute N for variable j in M -/
def subst (j : Nat) (N : Term) : Term → Term
  | var n =>
    if n = j then N                 -- Found the variable, substitute (N already shifted)
    else if n > j then var (n - 1) -- Variable above j, decrease index
    else var n                      -- Variable below j, unchanged
  | app M₁ M₂ => app (subst j N M₁) (subst j N M₂)
  | lam M => lam (subst (j + 1) (shift1 N) M)

/-- Substitute for variable 0 -/
abbrev subst0 (N : Term) (M : Term) : Term := subst 0 N M

/-- Substitution notation: M[N] means substitute N for var 0 in M -/
scoped notation:max M "[" N "]" => subst0 N M

/-! ## Common Combinators -/

/-- Identity: λx.x -/
def I : Term := ƛ (var 0)

/-- K combinator: λx.λy.x -/
def K : Term := ƛ (ƛ (var 1))

/-- S combinator: λx.λy.λz.xz(yz) -/
def S : Term := ƛ (ƛ (ƛ (app (app (var 2) (var 0)) (app (var 1) (var 0)))))

/-- Omega: (λx.xx)(λx.xx) -/
def omega : Term := app (ƛ (app (var 0) (var 0))) (ƛ (app (var 0) (var 0)))

/-! ## Basic Lemmas about Shifting -/

/-- Shifting by 0 is identity -/
theorem shift_zero (c : Nat) (M : Term) : shift 0 c M = M := by
  induction M generalizing c with
  | var n =>
    simp only [shift]
    split
    · rfl
    · simp
  | app M N ih_M ih_N =>
    simp only [shift]
    rw [ih_M, ih_N]
  | lam M ih =>
    simp only [shift]
    rw [ih]

/-- Shifting a variable below cutoff leaves it unchanged -/
theorem shift_var_lt {n c : Nat} {d : Int} (h : n < c) :
    shift d c (var n) = var n := by
  simp only [shift, h, ite_true]

/-- Shifting a variable at or above cutoff increases it -/
theorem shift_var_ge {n c : Nat} {d : Int} (h : n ≥ c) :
    shift d c (var n) = var (Int.toNat (n + d)) := by
  simp only [shift]
  have : ¬(n < c) := Nat.not_lt.mpr h
  simp [this]

/-! ## Shifting Composition -/

/-- Composing shifts (for non-negative shifts) -/
theorem shift_shift (d₁ d₂ : Nat) (c : Nat) (M : Term) :
    shift d₁ c (shift d₂ c M) = shift (d₁ + d₂) c M := by
  induction M generalizing c with
  | var n =>
    simp only [shift]
    split
    · rename_i h_lt
      simp only [shift, h_lt, ite_true]
    · rename_i h_ge
      have h_ge' : n ≥ c := Nat.le_of_not_lt h_ge
      simp only [shift]
      have h1 : ¬(Int.toNat (↑n + ↑d₂) < c) := by
        simp only [Nat.not_lt]
        omega
      simp only [h1, ite_false]
      congr 1
      omega
  | app M N ih_M ih_N =>
    simp only [shift]
    rw [ih_M c, ih_N c]
  | lam M ih =>
    simp only [shift]
    rw [ih (c + 1)]

/-- Composing shifts at consecutive cutoffs.

This lemma states that shifting by 1 at cutoff c+1 after shifting by 1 at cutoff c
equals shifting by 2 at cutoff c. This is a key lemma for substitution proofs.
-/
theorem shift_shift_succ (c : Nat) (M : Term) :
    shift 1 (c + 1) (shift 1 c M) = shift 2 c M := by
  induction M generalizing c with
  | var n =>
    simp only [shift]
    by_cases h : n < c
    · -- n < c: first shift leaves it unchanged, then second also leaves unchanged
      have h1 : n < c + 1 := Nat.lt_succ_of_lt h
      simp only [h, ite_true]
      simp only [shift, h1, ite_true]
    · -- n ≥ c: first shift gives n+1, then n+2
      simp only [h, ite_false]
      have eq1 : Int.toNat (↑n + (1 : Int)) = n + 1 := by omega
      simp only [eq1, shift]
      have h2 : ¬(n + 1 < c + 1) := by omega
      simp only [h2, ite_false]
      -- Both sides reduce to var (n + 2) with different Int expressions
      congr 1
  | app M N ihM ihN =>
    simp only [shift]
    rw [ihM c, ihN c]
  | lam M ih =>
    simp only [shift]
    congr 1
    rw [ih (c + 1)]

/-- Composing shifts at offset cutoffs.

shift 1 (c + b) (shift c b N) = shift (c + 1) b N

This says: shifting by c at cutoff b, then by 1 at cutoff c+b, equals shifting by c+1 at cutoff b.
-/
theorem shift_shift_offset (c b : Nat) (N : Term) :
    shift 1 (c + b) (shift c b N) = shift (c + 1) b N := by
  induction N generalizing c b with
  | var n =>
    simp only [shift]
    by_cases h : n < b
    · -- n < b: both shifts leave it unchanged
      have h1 : n < c + b := Nat.lt_of_lt_of_le h (Nat.le_add_left b c)
      simp only [h, ite_true, shift, h1]
    · -- n ≥ b: first shift gives n + c
      have n_ge_b : n ≥ b := Nat.le_of_not_lt h
      simp only [h, ite_false]
      have eq1 : Int.toNat (↑n + (↑c : Int)) = n + c := by
        have : (↑n : Int) + ↑c = ↑(n + c) := by omega
        simp only [this, Int.toNat_natCast]
      simp only [eq1, shift]
      -- n + c ≥ c + b since n ≥ b
      have h2 : ¬(n + c < c + b) := by omega
      simp only [h2, ite_false]
      congr 1
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [shift]
    rw [ih₁ c b, ih₂ c b]
  | lam M ih =>
    simp only [shift]
    congr 1
    have h_assoc : c + b + 1 = c + (b + 1) := by omega
    rw [h_assoc, ih c (b + 1)]

/-- Helper: composing shifts at different cutoffs when c₁ ≤ c₂

This lemma states that shifts at different cutoffs commute in a specific way.
When c₁ ≤ c₂, shifting by d₁ at c₁ and then by d₂ at (c₂ + d₁) equals
shifting by d₂ at c₂ first and then by d₁ at c₁.
-/
theorem shift_shift_comm (d₁ d₂ : Nat) (c₁ c₂ : Nat) (M : Term) (h : c₁ ≤ c₂) :
    shift (↑d₁) c₁ (shift (↑d₂) c₂ M) = shift (↑d₂) (c₂ + d₁) (shift (↑d₁) c₁ M) := by
  induction M generalizing c₁ c₂ with
  | var n =>
    by_cases h1 : n < c₁
    · -- n < c₁ ≤ c₂
      have h2 : n < c₂ := Nat.lt_of_lt_of_le h1 h
      have h3 : n < c₂ + d₁ := Nat.lt_of_lt_of_le h2 (Nat.le_add_right c₂ d₁)
      simp only [shift, h1, ite_true, h2, h3]
    · -- n ≥ c₁
      have n_ge_c1 : n ≥ c₁ := Nat.le_of_not_lt h1
      by_cases h2 : n < c₂
      · -- c₁ ≤ n < c₂
        have h3 : n + d₁ < c₂ + d₁ := by omega
        have eq1 : Int.toNat (↑n + ↑d₁) = n + d₁ := by
          simp only [← Int.natCast_add, Int.toNat_natCast]
        simp only [shift, h1, ite_false, h2, ite_true, eq1, h3]
      · -- n ≥ c₂
        have n_ge_c2 : n ≥ c₂ := Nat.le_of_not_lt h2
        have h3 : ¬(n + d₂ < c₁) := by omega
        have h4 : ¬(n + d₁ < c₂ + d₁) := by omega
        have eq1 : Int.toNat (↑n + ↑d₂) = n + d₂ := by
          simp only [← Int.natCast_add, Int.toNat_natCast]
        have eq2 : Int.toNat (↑n + ↑d₁) = n + d₁ := by
          simp only [← Int.natCast_add, Int.toNat_natCast]
        simp only [shift, h1, ite_false, h2, eq1, h3, eq2, h4]
        congr 1
        omega
  | app M N ihM ihN =>
    simp only [shift]
    rw [ihM c₁ c₂ h, ihN c₁ c₂ h]
  | lam M ih =>
    simp only [shift]
    congr 1
    have h' : c₁ + 1 ≤ c₂ + 1 := by omega
    have heq : c₂ + 1 + d₁ = c₂ + d₁ + 1 := by omega
    rw [ih (c₁ + 1) (c₂ + 1) h', heq]

/-! ## Substitution Lemmas -/

/-- Substituting into a variable that's not the target -/
theorem subst_var_ne {j n : Nat} (N : Term) (h : n ≠ j) :
    subst j N (var n) = if n > j then var (n - 1) else var n := by
  simp only [subst, h, ite_false]

/-- Substituting into the target variable -/
theorem subst_var_eq {j : Nat} (N : Term) :
    subst j N (var j) = N := by
  simp only [subst, ite_true]

/-! ## Key Substitution-Shift Interaction -/

/-- Generalized version: substituting at c after shifting by 1 at c cancels out. -/
theorem subst_shift_cancel (M : Term) (N : Term) (c : Nat) :
    subst c N (shift 1 c M) = M := by
  induction M generalizing c N with
  | var n =>
    simp only [shift]
    by_cases h : n < c
    · simp only [h, ite_true, subst]
      have ne_c : n ≠ c := Nat.ne_of_lt h
      have not_gt : ¬(n > c) := Nat.not_lt.mpr (Nat.le_of_lt h)
      simp [ne_c, not_gt]
    · simp only [h, ite_false, subst]
      have n_ge_c : n ≥ c := Nat.le_of_not_lt h
      have ne_c : n + 1 ≠ c := by omega
      have gt_c : n + 1 > c := by omega
      simp [ne_c, gt_c]
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [shift, subst]
    rw [ih₁, ih₂]
  | lam M ih =>
    simp only [shift, subst]
    congr 1
    apply ih

/-- Substituting for a shifted variable cancels out. -/
theorem subst_shift1 (M N : Term) : (shift 1 0 M)[N] = M :=
  subst_shift_cancel M N 0

/-! ## Shift-Substitution Interaction Lemmas

The following lemmas establish how shifting and substitution interact.
These are the core de Bruijn infrastructure lemmas.

References:
- Pierce et al. (2023): Software Foundations, Vol 2, "Stlc" chapter
- Aydemir et al. (2008): "Engineering Formal Metatheory"
- Barendregt (1984): "The Lambda Calculus: Its Syntax and Semantics"
-/

/-- Generalized shift-substitution lemma for arbitrary substitution index.

This is the key lemma for proving shift_subst. It states that shifting commutes
with substitution in a specific way: shifting by d at cutoff c of a substitution
at index j equals substituting the shifted term into the shifted original.

The constraint j ≤ c is essential: j represents the binding depth for the
substitution, and c is the cutoff for free variables. In well-formed terms,
variables below the binding depth (< j) are bound, and we only shift free
variables (≥ c). The constraint ensures these ranges don't conflict.

The key insight is that when recursing through lambdas:
- The substitution index j increases by 1
- The cutoff c for shift also increases by 1
- The substituted term N gets shifted by 1 at cutoff 0 (i.e., shift1)
- We use shift_shift_comm to relate shift1 (shift d c N) to shift d (c+1) (shift1 N)
- The constraint j ≤ c is preserved: j+1 ≤ c+1
-/
theorem shift_subst_at (M N : Term) (d : Nat) (c j : Nat) (hjc : j ≤ c) :
    shift d c (subst j N M) = subst j (shift d c N) (shift d (c + 1) M) := by
  induction M generalizing N d c j with
  | var n =>
    simp only [subst]
    by_cases hnj : n = j
    · -- n = j: substitution fires
      simp only [hnj, ite_true]
      -- Need: shift d c N = subst j (shift d c N) (shift d (c + 1) (var j))
      -- Since j ≤ c, we have j < c + 1, so shift d (c + 1) (var j) = var j
      simp only [shift]
      have hjc1 : j < c + 1 := Nat.lt_succ_of_le hjc
      simp only [hjc1, ite_true, subst, ite_true]
    · -- n ≠ j
      simp only [hnj, ite_false]
      by_cases hnj_gt : n > j
      · -- n > j: subst returns var (n - 1)
        simp only [hnj_gt, ite_true, shift]
        by_cases hn1_lt : n - 1 < c
        · -- n - 1 < c: shift d c (var (n - 1)) = var (n - 1)
          simp only [hn1_lt, ite_true]
          -- RHS: shift d (c + 1) (var n)
          -- Since n > j and j ≤ c, we have n ≥ j + 1.
          -- If n - 1 < c, then n ≤ c, so n < c + 1
          have hn_lt : n < c + 1 := by omega
          simp only [hn_lt, ite_true, subst, hnj, ite_false, hnj_gt, ite_true]
        · -- n - 1 ≥ c: shift d c (var (n - 1)) = var (n - 1 + d)
          have hn1_ge : n - 1 ≥ c := Nat.le_of_not_lt hn1_lt
          simp only [hn1_lt, ite_false]
          -- RHS: shift d (c + 1) (var n) where n ≥ c + 1 (since n - 1 ≥ c)
          have hn_ge : n ≥ c + 1 := by omega
          have hn_lt : ¬(n < c + 1) := Nat.not_lt.mpr hn_ge
          simp only [hn_lt, ite_false, subst]
          -- Goal: var (Int.toNat (↑(n - 1) + ↑d)) = if ... then ... else ...
          -- Simplify Int.toNat expressions
          have eq1 : Int.toNat (↑(n - 1) + ↑d) = n - 1 + d := by
            simp only [← Int.natCast_add, Int.toNat_natCast]
          have eq2 : Int.toNat (↑n + ↑d) = n + d := by
            simp only [← Int.natCast_add, Int.toNat_natCast]
          simp only [eq1, eq2]
          have hnd_ne : n + d ≠ j := by omega
          have hnd_gt : n + d > j := by omega
          simp only [hnd_ne, ite_false, hnd_gt, ite_true]
          congr 1
          omega
      · -- n ≤ j and n ≠ j, so n < j
        have hn_lt_j : n < j := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnj_gt) hnj
        simp only [hnj_gt, ite_false, shift]
        -- Since n < j ≤ c, we have n < c
        have hn_lt : n < c := Nat.lt_of_lt_of_le hn_lt_j hjc
        simp only [hn_lt, ite_true]
        have hn_lt_c1 : n < c + 1 := Nat.lt_of_lt_of_le hn_lt (Nat.le_add_right c 1)
        simp only [hn_lt_c1, ite_true, subst, hnj, ite_false, hnj_gt]
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [subst, shift]
    rw [ih₁ N d c j hjc, ih₂ N d c j hjc]
  | lam M ih =>
    simp only [subst, shift]
    congr 1
    -- LHS: shift d (c + 1) (subst (j + 1) (shift1 N) M)
    -- RHS: subst (j + 1) (shift1 (shift d c N)) (shift d (c + 2) M)
    -- By IH with c' = c + 1, j' = j + 1, N' = shift1 N:
    -- Need: j + 1 ≤ c + 1, which follows from j ≤ c
    have hjc' : j + 1 ≤ c + 1 := Nat.add_le_add_right hjc 1
    -- shift d (c + 1) (subst (j + 1) (shift1 N) M)
    --   = subst (j + 1) (shift d (c + 1) (shift1 N)) (shift d (c + 2) M)
    -- So we need: shift d (c + 1) (shift1 N) = shift1 (shift d c N)
    -- Using shift_shift_comm with c₁ = 0, c₂ = c, d₁ = 1, d₂ = d:
    -- shift 1 0 (shift d c N) = shift d (c + 1) (shift 1 0 N)
    -- i.e., shift1 (shift d c N) = shift d (c + 1) (shift1 N)
    have h_comm : shift1 (shift d c N) = shift d (c + 1) (shift1 N) :=
      shift_shift_comm 1 d 0 c N (Nat.zero_le c)
    rw [ih (shift1 N) d (c + 1) (j + 1) hjc']
    rw [h_comm]

/-- Shift-substitution interaction lemma.

This lemma states that shifting after substitution equals substituting shifted terms.

`shift d c (M[N]) = (shift d (c + 1) M)[shift d c N]`

This is a fundamental de Bruijn lemma used throughout the development.
-/
theorem shift_subst (M N : Term) (d : Nat) (c : Nat) :
    shift d c (M[N]) = (shift d (c + 1) M)[shift d c N] :=
  shift_subst_at M N d c 0 (Nat.zero_le c)

/-- Generalized shift-subst lemma with parameterized cutoff.

`shift 1 c (subst (j + c) (shift c 0 N) L) = subst (j + c + 1) (shift (c + 1) 0 N) (shift 1 c L)`

This is the key lemma for proving subst_subst_gen. It generalizes the interaction
between shift and subst to arbitrary cutoffs.
-/
theorem shift1_subst_gen (L N : Term) (j c : Nat) :
    shift 1 c (subst (j + c) (shift c 0 N) L) =
    subst (j + c + 1) (shift (c + 1) 0 N) (shift 1 c L) := by
  induction L generalizing j c N with
  | var n =>
    simp only [subst, shift]
    by_cases hn_eq : n = j + c
    · -- n = j + c: substitution fires, LHS = shift 1 c (shift c 0 N)
      subst hn_eq
      simp only [ite_true]
      -- LHS: shift 1 c (shift c 0 N) = shift (c + 1) 0 N by shift_shift_offset
      have h_shift : shift 1 c (shift c 0 N) = shift (c + 1) 0 N := by
        have h := shift_shift_offset c 0 N
        simp only [Nat.add_zero] at h
        exact h
      rw [h_shift]
      -- RHS: shift 1 c (var (j + c)) = var (j + c + 1) since j + c ≥ c
      have h_ge : ¬(j + c < c) := by omega
      simp only [h_ge, ite_false]
      have eq1 : Int.toNat (↑(j + c) + (1 : Int)) = j + c + 1 := by
        have : (↑(j + c) : Int) + 1 = ↑(j + c + 1) := by omega
        simp only [this, Int.toNat_natCast]
      simp only [eq1, subst, ite_true]
    · -- n ≠ j + c
      simp only [hn_eq, ite_false]
      by_cases hn_gt : n > j + c
      · -- n > j + c: subst gives var (n - 1)
        simp only [hn_gt, ite_true, shift]
        by_cases hn1_lt : n - 1 < c
        · -- n - 1 < c: shift 1 c (var (n-1)) = var (n-1)
          simp only [hn1_lt, ite_true]
          -- n - 1 < c and n > j + c means j + c < n and n - 1 < c
          -- So j + c < n ≤ c, which means j < 0, impossible for Nat
          omega
        · -- n - 1 ≥ c: shift 1 c (var (n-1)) = var n
          have hn1_ge : n - 1 ≥ c := Nat.le_of_not_lt hn1_lt
          simp only [hn1_lt, ite_false]
          have eq1 : Int.toNat (↑(n - 1) + (1 : Int)) = n := by
            have h : n ≥ 1 := by omega
            have : (↑(n - 1) : Int) + 1 = ↑n := by omega
            simp only [this, Int.toNat_natCast]
          simp only [eq1]
          -- RHS: shift 1 c (var n) = var (n + 1) since n > j + c ≥ c
          have h_nge : ¬(n < c) := by omega
          simp only [h_nge, ite_false]
          have eq2 : Int.toNat (↑n + (1 : Int)) = n + 1 := by
            have : (↑n : Int) + 1 = ↑(n + 1) := by omega
            simp only [this, Int.toNat_natCast]
          simp only [eq2, subst]
          have h1 : n + 1 ≠ j + c + 1 := by omega
          have h2 : n + 1 > j + c + 1 := by omega
          simp only [h1, ite_false, h2, ite_true]
          -- Goal: var (n - 1 - 1 + 1) = var (n + 1 - 1)
          -- n - 1 ≥ c and n > j + c, so n - 1 ≥ 1, thus (n - 1) - 1 + 1 = n - 1
          -- and n + 1 - 1 = n
          -- But we need (n - 1) - 1 = n - 1 - 1... wait, the goal should be:
          -- var ((n + 1) - 1 - 1) = var (n - 1) after substitutions
          -- Actually, looking at the context, this should be var (n - 1) on both sides
          rfl
      · -- n ≤ j + c, n ≠ j + c, so n < j + c
        have hn_lt : n < j + c := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn_gt) hn_eq
        simp only [hn_gt, ite_false, shift]
        by_cases hn_c : n < c
        · -- n < c: shift 1 c (var n) = var n
          simp only [hn_c, ite_true, subst]
          have h1 : n ≠ j + c + 1 := by omega
          have h2 : ¬(n > j + c + 1) := by omega
          simp only [h1, ite_false, h2, ite_false]
        · -- n ≥ c: shift 1 c (var n) = var (n + 1)
          have hn_ge : n ≥ c := Nat.le_of_not_lt hn_c
          simp only [hn_c, ite_false]
          have eq1 : Int.toNat (↑n + (1 : Int)) = n + 1 := by
            have : (↑n : Int) + 1 = ↑(n + 1) := by omega
            simp only [this, Int.toNat_natCast]
          simp only [eq1, subst]
          have h1 : n + 1 ≠ j + c + 1 := by omega
          have h2 : ¬(n + 1 > j + c + 1) := by omega
          simp only [h1, ite_false, h2, ite_false]
  | app L₁ L₂ ih₁ ih₂ =>
    simp only [subst, shift]
    -- IH order is reverse of generalizing order: N, j, c
    rw [ih₁ N j c, ih₂ N j c]
  | lam L₀ ih =>
    simp only [subst, shift]
    congr 1
    -- LHS: shift 1 (c + 1) (subst (j + c + 1) (shift1 (shift c 0 N)) L₀)
    -- RHS: subst (j + c + 2) (shift1 (shift (c + 1) 0 N)) (shift 1 (c + 1) L₀)
    -- Note: shift1 (shift c 0 N) = shift (c + 1) 0 N by shift_shift
    have h_s1 : shift1 (shift c 0 N) = shift (c + 1) 0 N := by
      show shift 1 0 (shift c 0 N) = shift (c + 1) 0 N
      have h := shift_shift 1 c 0 N
      -- h : shift 1 0 (shift c 0 N) = shift (1 + c) 0 N
      calc shift 1 0 (shift c 0 N) = shift (1 + c) 0 N := h
        _ = shift (c + 1) 0 N := by congr 1; omega
    -- And shift1 (shift (c + 1) 0 N) = shift (c + 2) 0 N by shift_shift
    have h_s2 : shift1 (shift (c + 1) 0 N) = shift (c + 2) 0 N := by
      show shift 1 0 (shift (c + 1) 0 N) = shift (c + 2) 0 N
      have h := shift_shift 1 (c + 1) 0 N
      calc shift 1 0 (shift (c + 1) 0 N) = shift (1 + (c + 1)) 0 N := h
        _ = shift (c + 2) 0 N := by congr 1; omega
    rw [h_s1, h_s2]
    -- Now goal is:
    -- shift 1 (c + 1) (subst (j + c + 1) (shift (c + 1) 0 N) L₀)
    -- = subst (j + c + 2) (shift (c + 2) 0 N) (shift 1 (c + 1) L₀)
    -- Use IH with c' = c + 1
    exact ih N j (c + 1)

/-- Corollary: shift1 commutes with subst in a specific way.

`shift1 (subst j N L) = subst (j + 1) (shift1 N) (shift1 L)`
-/
theorem shift1_subst (L N : Term) (j : Nat) :
    shift1 (subst j N L) = subst (j + 1) (shift1 N) (shift1 L) := by
  unfold shift1
  have h := shift1_subst_gen L N j 0
  simp only [Nat.add_zero] at h
  -- h : shift 1 0 (subst j (shift 0 0 N) L) = subst (j + 1) (shift 1 0 N) (shift 1 0 L)
  -- The issue is shift 0 0 N in h vs N in goal. They're equal by shift_zero.
  have hz : shift (0 : Nat) 0 N = N := shift_zero 0 N
  -- Rewrite in h to use N directly
  simp only [hz] at h
  -- Now h should match
  exact h

/-- Helper: ↑(a + b) = ↑a + ↑b for Int coercions -/
private theorem int_add_coe (a b : Nat) : (↑(a + b) : Int) = ↑a + ↑b := Int.natCast_add a b

/-- Helper: ↑a + ↑b = ↑(a + b) for Int coercions (symmetric) -/
private theorem int_coe_add (a b : Nat) : (↑a : Int) + ↑b = ↑(a + b) := (Int.natCast_add a b).symm

/-- Helper: shift with Nat argument equals shift with coerced Int argument -/
private theorem shift_coe_eq (d : Nat) (c : Nat) (M : Term) :
    shift (↑d : Int) c M = shift d c M := rfl

/-- Generalized substitution composition lemma with level parameter.

This is the key generalization needed for proving subst_subst_gen.
The parameter `i` tracks the substitution level - under `i` lambdas.

At level i:
- The outer substitution is at index i
- The inner substitution on M is at index j+i+1
- N is shifted by i+1 for the inner substitution
- L is shifted by i for both substitutions

References:
- Barendregt (1984): "The Lambda Calculus: Its Syntax and Semantics", Lemma 2.1.16
- Pierce et al. (2023): Software Foundations, Vol 2, "Stlc" chapter
-/
theorem subst_subst_gen_full (M N L : Term) (j i : Nat) :
    subst i (subst (j+i) (shift i 0 N) (shift i 0 L)) (subst (j + i + 1) (shift (i+1) 0 N) M)
    = subst (j+i) (shift i 0 N) (subst i (shift i 0 L) M) := by
  induction M generalizing N L j i with
  | var n =>
    simp only [subst]
    -- Case analysis on n relative to i and j+i+1
    by_cases hn_eq_i : n = i
    · -- n = i: inner subst leaves var i alone, outer subst fires
      subst hn_eq_i
      -- Now i is replaced by n everywhere (subst replaces the RHS variable)
      -- n ≠ j+n+1 (because j+1 > 0) and n < j+n+1
      have h1 : n ≠ j + n + 1 := by omega
      have h2 : ¬(n > j + n + 1) := by omega
      simp only [h1, ite_false, h2, ite_false, ite_true]
      -- Now goal is: subst n (subst (j+n) ... ...) (var n) = subst (j+n) ... ...
      -- subst n X (var n) = X by definition (since n = n)
      simp only [subst, ite_true]
    · by_cases hn_eq_ji1 : n = j + i + 1
      · -- n = j+i+1: inner subst fires with shift (↑i + 1) 0 N
        simp only [hn_eq_ji1, ite_true]
        -- By subst_shift_cancel with c = i: subst i X (shift 1 i Y) = Y
        -- shift (↑i + 1) 0 N = shift 1 i (shift (↑i) 0 N) by shift_shift_offset
        have h_shift_decomp : shift (↑i + 1) 0 N = shift 1 i (shift (↑i) 0 N) := by
          have h2 := shift_shift_offset i 0 N
          simp only [Nat.add_zero] at h2
          exact h2.symm
        rw [h_shift_decomp, subst_shift_cancel]
        -- RHS: subst (j+i) (shift i 0 N) (subst i (shift i 0 L) (var (j+i+1)))
        have h1 : j + i + 1 ≠ i := by omega
        have h2 : j + i + 1 > i := by omega
        have h3 : j + i + 1 - 1 = j + i := by omega
        simp only [h1, ite_false, h2, ite_true, h3, subst, ite_true]
      · by_cases hn_gt : n > j + i + 1
        · -- n > j+i+1: inner subst decrements
          have h1 : n ≠ j + i + 1 := by omega
          have hn1_ne_i : n - 1 ≠ i := by omega
          have hn1_gt_i : n - 1 > i := by omega
          have hn_ne_i : n ≠ i := by omega
          have hn_gt_i : n > i := by omega
          have hn1_ne_ji : n - 1 ≠ j + i := by omega
          have hn1_gt_ji : n - 1 > j + i := by omega
          simp only [h1, ite_false, hn_gt, ite_true, subst, hn1_ne_i, hn1_gt_i,
                     hn_ne_i, hn_gt_i, hn1_ne_ji, hn1_gt_ji]
        · -- n ≤ j+i+1 and n ≠ j+i+1 and n ≠ i
          have h1 : n ≠ j + i + 1 := by omega
          have h2 : ¬(n > j + i + 1) := by omega
          simp only [h1, ite_false, h2, subst, hn_eq_i]
          by_cases hn_gt_i : n > i
          · have hn1_ne_ji : n - 1 ≠ j + i := by omega
            have hn1_not_gt_ji : ¬(n - 1 > j + i) := by omega
            simp only [hn_gt_i, ite_true, subst, hn1_ne_ji, ite_false, hn1_not_gt_ji]
          · have hn_ne_ji : n ≠ j + i := by omega
            have hn_not_gt_ji : ¬(n > j + i) := by omega
            simp only [hn_gt_i, ite_false, subst, hn_ne_ji, hn_not_gt_ji]
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [subst]
    rw [ih₁ N L j i, ih₂ N L j i]
  | lam M₀ ih =>
    simp only [subst]
    congr 1
    -- Helper for Int addition commutativity: 1 + ↑x = ↑x + 1
    have int_add_comm_1 : ∀ x : Nat, (1 : Int) + ↑x = ↑x + 1 := fun x => Int.add_comm 1 ↑x
    -- Shift lemmas via calc to handle Int.add_comm
    have h_shift_N' : shift1 (shift i 0 N) = shift (i+1) 0 N := by
      calc shift1 (shift i 0 N)
        = shift 1 0 (shift i 0 N) := rfl
        _ = shift (1 + i) 0 N := shift_shift 1 i 0 N
        _ = shift (↑i + 1) 0 N := by rw [int_add_comm_1 i]
    have h_shift_L' : shift1 (shift i 0 L) = shift (i+1) 0 L := by
      calc shift1 (shift i 0 L)
        = shift 1 0 (shift i 0 L) := rfl
        _ = shift (1 + i) 0 L := shift_shift 1 i 0 L
        _ = shift (↑i + 1) 0 L := by rw [int_add_comm_1 i]
    have h_shift1_subst : shift1 (subst (j+i) (shift i 0 N) (shift i 0 L))
                        = subst (j+i+1) (shift (i+1) 0 N) (shift (i+1) 0 L) := by
      rw [shift1_subst, h_shift_N', h_shift_L']
    have h_shift_N'' : shift1 (shift (i+1) 0 N) = shift (i+2) 0 N := by
      calc shift1 (shift (i+1) 0 N)
        = shift 1 0 (shift (i+1) 0 N) := rfl
        _ = shift (1 + (i+1)) 0 N := shift_shift 1 (i+1) 0 N
        _ = shift (↑(i+1) + 1) 0 N := by
            -- Goal: 1 + (↑i + 1) = ↑(i+1) + 1  (after Lean normalizes ↑(i+1) to ↑i + 1)
            congr 1
            -- Use Int.natCast_add to relate ↑(i+1) and ↑i + 1
            have h_coe : (↑(i + 1) : Int) = ↑i + 1 := Int.natCast_add i 1
            omega
    -- Rewrite goal using these lemmas
    rw [h_shift1_subst, h_shift_N'', h_shift_N', h_shift_L']
    -- Apply IH at i+1
    exact ih N L j (i + 1)

/-- Generalized substitution composition lemma.

This lemma expresses how nested substitutions interact. It is the key lemma
for proving that substitution respects beta reduction.

The lemma states that:
- First substituting (shift1 N) for variable (j+1) in M, then substituting (subst j N L) for variable 0
- Equals: First substituting L for variable 0 in M, then substituting N for variable j

Proof: Derived from subst_subst_gen_full at i=0.

References:
- Barendregt (1984): "The Lambda Calculus: Its Syntax and Semantics", Lemma 2.1.16
- Pierce et al. (2023): Software Foundations, Vol 2, "Stlc" chapter
- Terese (2003): "Term Rewriting Systems", Chapter 5
-/
theorem subst_subst_gen (M N L : Term) (j : Nat) :
    (subst (j + 1) (shift1 N) M)[subst j N L] = subst j N (M[L]) := by
  -- At i=0, subst_subst_gen_full gives:
  -- subst 0 (subst j (shift 0 0 N) (shift 0 0 L)) (subst (j+1) (shift 1 0 N) M)
  -- = subst j (shift 0 0 N) (subst 0 (shift 0 0 L) M)
  -- Using shift 0 0 = id, this becomes:
  -- subst 0 (subst j N L) (subst (j+1) (shift1 N) M) = subst j N (subst 0 L M)
  have h := subst_subst_gen_full M N L j 0
  simp only [Nat.add_zero] at h
  -- h has shift (↑0) 0 N. Note: (↑0 : Int) = (0 : Int) definitionally
  -- shift (↑0) 0 N = N and shift (↑0 + 1) 0 N = shift1 N
  have hz1 : shift (↑(0:Nat)) 0 N = N := shift_zero 0 N
  have hz2 : shift (↑(0:Nat)) 0 L = L := shift_zero 0 L
  have hz3 : shift (↑(0:Nat) + 1) 0 N = shift1 N := rfl
  simp only [hz1, hz2, hz3] at h
  exact h

end Term

end Metatheory.Lambda
