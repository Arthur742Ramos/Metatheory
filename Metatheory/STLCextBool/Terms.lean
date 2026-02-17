/-
# Simply Typed Lambda Calculus with Booleans - Terms

This module defines lambda calculus terms extended with boolean literals
and conditional expressions, using de Bruijn indices.

## References

- Pierce, "Types and Programming Languages" (2002), Chapter 11
-/

import Metatheory.STLCextBool.Types

namespace Metatheory.STLCextBool

/-! ## Term Definition -/

/-- Lambda calculus terms with booleans. -/
inductive Term : Type where
  | var   : Nat → Term               -- Variable (de Bruijn index)
  | lam   : Term → Term              -- Lambda abstraction λ.M
  | app   : Term → Term → Term       -- Application M N
  | ttrue : Term                     -- Boolean true
  | tfalse : Term                    -- Boolean false
  | ite   : Term → Term → Term → Term -- if M then N₁ else N₂
  deriving Repr, DecidableEq

namespace Term

/-! ## Notation -/

scoped infixl:70 " @ " => Term.app
scoped prefix:max "ƛ " => Term.lam

/-! ## Shifting -/

/-- Shift free variables by d, starting from cutoff c. -/
def shift (d : Int) (c : Nat) : Term → Term
  | var n => if n < c then var n else var (Int.toNat (n + d))
  | lam M => lam (shift d (c + 1) M)
  | app M N => app (shift d c M) (shift d c N)
  | ttrue => ttrue
  | tfalse => tfalse
  | ite M N₁ N₂ => ite (shift d c M) (shift d c N₁) (shift d c N₂)

/-- Shorthand for shifting by 1 from cutoff 0. -/
abbrev shift1 (M : Term) : Term := shift 1 0 M

/-! ## Substitution -/

/-- Substitute N for variable j in M. -/
def subst (j : Nat) (N : Term) : Term → Term
  | var n =>
    if n = j then N
    else if n > j then var (n - 1)
    else var n
  | lam M => lam (subst (j + 1) (shift1 N) M)
  | app M₁ M₂ => app (subst j N M₁) (subst j N M₂)
  | ttrue => ttrue
  | tfalse => tfalse
  | ite M N₁ N₂ => ite (subst j N M) (subst j N N₁) (subst j N N₂)

/-- Substitute for variable 0. -/
abbrev subst0 (N : Term) (M : Term) : Term := subst 0 N M

/-- Substitution notation: M[N] means substitute N for var 0 in M. -/
scoped notation:max M "[" N "]" => subst0 N M

/-! ## Shift/Substitution Lemmas -/

/-- Shifting by 0 is identity. -/
theorem shift_zero (c : Nat) (M : Term) : shift 0 c M = M := by
  induction M generalizing c with
  | var n =>
    simp [shift]
  | lam M ih =>
    simp [shift, ih]
  | app M N ihM ihN =>
    simp [shift, ihM, ihN]
  | ttrue => rfl
  | tfalse => rfl
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp [shift, ihM, ihN₁, ihN₂]

/-- Substituting at c after shifting by 1 at c cancels out. -/
theorem subst_shift_cancel (M : Term) (N : Term) (c : Nat) :
    subst c N (shift 1 c M) = M := by
  induction M generalizing c N with
  | var n =>
    by_cases hnc : n < c
    · have hne : n ≠ c := Nat.ne_of_lt hnc
      have hngt : ¬n > c := by omega
      simp [shift, subst, hnc, hne, hngt]
    · have hne : n + 1 ≠ c := by omega
      have hgt : n + 1 > c := by omega
      simp [shift, subst, hnc, hne, hgt]
  | lam M ih =>
    simp [shift, subst, ih]
  | app M N ihM ihN =>
    simp [shift, subst, ihM, ihN]
  | ttrue => rfl
  | tfalse => rfl
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp [shift, subst, ihM, ihN₁, ihN₂]

/-- Substituting for a shifted variable cancels out. -/
theorem subst_shift1 (M N : Term) : (shift 1 0 M)[N] = M :=
  subst_shift_cancel M N 0

/-! ## Shifting Composition -/

/-- Shifting a variable below cutoff leaves it unchanged. -/
theorem shift_var_lt {n c : Nat} {d : Int} (h : n < c) :
    shift d c (var n) = var n := by
  simp [shift, h]

/-- Shifting a variable at or above cutoff increases it. -/
theorem shift_var_ge {n c : Nat} {d : Int} (h : n ≥ c) :
    shift d c (var n) = var (Int.toNat (n + d)) := by
  simp [shift]
  have : ¬(n < c) := Nat.not_lt.mpr h
  simp [this]

/-- Composing shifts (for non-negative shifts). -/
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
  | lam M ih =>
    simp only [shift]
    rw [ih (c + 1)]
  | app M N ihM ihN =>
    simp only [shift]
    rw [ihM c, ihN c]
  | ttrue => rfl
  | tfalse => rfl
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp only [shift]
    rw [ihM c, ihN₁ c, ihN₂ c]

/-- Composing shifts at offset cutoffs. -/
theorem shift_shift_offset (c b : Nat) (N : Term) :
    shift 1 (c + b) (shift c b N) = shift (c + 1) b N := by
  induction N generalizing c b with
  | var n =>
    simp only [shift]
    by_cases h : n < b
    · have h1 : n < c + b := Nat.lt_of_lt_of_le h (Nat.le_add_left b c)
      simp only [h, ite_true, shift, h1]
    · have n_ge_b : n ≥ b := Nat.le_of_not_lt h
      simp only [h, ite_false]
      have eq1 : Int.toNat (↑n + (↑c : Int)) = n + c := by
        have : (↑n : Int) + ↑c = ↑(n + c) := by omega
        simp only [this, Int.toNat_natCast]
      simp only [eq1, shift]
      have h2 : ¬(n + c < c + b) := by omega
      simp only [h2, ite_false]
      congr 1
  | lam M ih =>
    simp only [shift]
    congr 1
    have h_assoc : c + b + 1 = c + (b + 1) := by omega
    rw [h_assoc, ih c (b + 1)]
  | app M N ihM ihN =>
    simp only [shift]
    rw [ihM c b, ihN c b]
  | ttrue => rfl
  | tfalse => rfl
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp only [shift]
    rw [ihM c b, ihN₁ c b, ihN₂ c b]

/-- Shifts at different cutoffs commute when c₁ ≤ c₂. -/
theorem shift_shift_comm (d₁ d₂ : Nat) (c₁ c₂ : Nat) (M : Term) (h : c₁ ≤ c₂) :
    shift (↑d₁) c₁ (shift (↑d₂) c₂ M) = shift (↑d₂) (c₂ + d₁) (shift (↑d₁) c₁ M) := by
  induction M generalizing c₁ c₂ with
  | var n =>
    by_cases h1 : n < c₁
    · have h2 : n < c₂ := Nat.lt_of_lt_of_le h1 h
      have h3 : n < c₂ + d₁ := Nat.lt_of_lt_of_le h2 (Nat.le_add_right c₂ d₁)
      simp only [shift, h1, ite_true, h2, h3]
    · have n_ge_c1 : n ≥ c₁ := Nat.le_of_not_lt h1
      by_cases h2 : n < c₂
      · have h3 : n + d₁ < c₂ + d₁ := by omega
        have eq1 : Int.toNat (↑n + ↑d₁) = n + d₁ := by
          simp only [← Int.natCast_add, Int.toNat_natCast]
        simp only [shift, h1, ite_false, h2, ite_true, eq1, h3]
      · have n_ge_c2 : n ≥ c₂ := Nat.le_of_not_lt h2
        have h3 : ¬(n + d₂ < c₁) := by omega
        have h4 : ¬(n + d₁ < c₂ + d₁) := by omega
        have eq1 : Int.toNat (↑n + ↑d₂) = n + d₂ := by
          simp only [← Int.natCast_add, Int.toNat_natCast]
        have eq2 : Int.toNat (↑n + ↑d₁) = n + d₁ := by
          simp only [← Int.natCast_add, Int.toNat_natCast]
        simp only [shift, h1, ite_false, h2, eq1, h3, eq2, h4]
        congr 1
        omega
  | lam M ih =>
    simp only [shift]
    congr 1
    have h' : c₁ + 1 ≤ c₂ + 1 := by omega
    have heq : c₂ + 1 + d₁ = c₂ + d₁ + 1 := by omega
    rw [ih (c₁ + 1) (c₂ + 1) h', heq]
  | app M N ihM ihN =>
    simp only [shift]
    rw [ihM c₁ c₂ h, ihN c₁ c₂ h]
  | ttrue => simp [shift]
  | tfalse => simp [shift]
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp only [shift]
    rw [ihM c₁ c₂ h, ihN₁ c₁ c₂ h, ihN₂ c₁ c₂ h]

/-! ## Shift-Substitution Interaction -/

/-- Generalized shift-substitution lemma. -/
theorem shift_subst_at (M N : Term) (d : Nat) (c j : Nat) (hjc : j ≤ c) :
    shift d c (subst j N M) = subst j (shift d c N) (shift d (c + 1) M) := by
  induction M generalizing N d c j with
  | var n =>
    simp only [subst]
    by_cases hnj : n = j
    · simp only [hnj, ite_true]
      simp only [shift]
      have hjc1 : j < c + 1 := Nat.lt_succ_of_le hjc
      simp only [hjc1, ite_true, subst, ite_true]
    · simp only [hnj, ite_false]
      by_cases hnj_gt : n > j
      · simp only [hnj_gt, ite_true, shift]
        by_cases hn1_lt : n - 1 < c
        · simp only [hn1_lt, ite_true]
          have hn_lt : n < c + 1 := by omega
          simp only [hn_lt, ite_true, subst, hnj, ite_false, hnj_gt, ite_true]
        · have hn1_ge : n - 1 ≥ c := Nat.le_of_not_lt hn1_lt
          simp only [hn1_lt, ite_false]
          have hn_ge : n ≥ c + 1 := by omega
          have hn_lt : ¬(n < c + 1) := Nat.not_lt.mpr hn_ge
          simp only [hn_lt, ite_false, subst]
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
      · have hn_lt_j : n < j := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hnj_gt) hnj
        simp only [hnj_gt, ite_false, shift]
        have hn_lt : n < c := Nat.lt_of_lt_of_le hn_lt_j hjc
        simp only [hn_lt, ite_true]
        have hn_lt_c1 : n < c + 1 := Nat.lt_of_lt_of_le hn_lt (Nat.le_add_right c 1)
        simp only [hn_lt_c1, ite_true, subst, hnj, ite_false, hnj_gt]
  | lam M ih =>
    simp only [subst, shift]
    congr 1
    have hjc' : j + 1 ≤ c + 1 := Nat.add_le_add_right hjc 1
    have h_comm : shift1 (shift d c N) = shift d (c + 1) (shift1 N) :=
      shift_shift_comm 1 d 0 c N (Nat.zero_le c)
    rw [ih (shift1 N) d (c + 1) (j + 1) hjc']
    rw [h_comm]
  | app M₁ M₂ ihM ihN =>
    simp only [subst, shift]
    rw [ihM N d c j hjc, ihN N d c j hjc]
  | ttrue => simp [subst, shift]
  | tfalse => simp [subst, shift]
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp only [subst, shift]
    rw [ihM N d c j hjc, ihN₁ N d c j hjc, ihN₂ N d c j hjc]

/-- Shift-substitution interaction lemma. -/
theorem shift_subst (M N : Term) (d : Nat) (c : Nat) :
    shift d c (M[N]) = (shift d (c + 1) M)[shift d c N] :=
  shift_subst_at M N d c 0 (Nat.zero_le c)

/-- Generalized shift-subst lemma with cutoff parameter. -/
theorem shift1_subst_gen (L N : Term) (j c : Nat) :
    shift 1 c (subst (j + c) (shift c 0 N) L) =
    subst (j + c + 1) (shift (c + 1) 0 N) (shift 1 c L) := by
  induction L generalizing j c N with
  | var n =>
    simp only [subst, shift]
    by_cases hn_eq : n = j + c
    · subst hn_eq
      simp only [ite_true]
      have h_shift : shift 1 c (shift c 0 N) = shift (c + 1) 0 N := by
        have h := shift_shift_offset c 0 N
        simp only [Nat.add_zero] at h
        exact h
      rw [h_shift]
      have h_ge : ¬(j + c < c) := by omega
      simp only [h_ge, ite_false]
      have eq1 : Int.toNat (↑(j + c) + (1 : Int)) = j + c + 1 := by
        have : (↑(j + c) : Int) + 1 = ↑(j + c + 1) := by omega
        simp only [this, Int.toNat_natCast]
      simp only [eq1, subst, ite_true]
    · simp only [hn_eq, ite_false]
      by_cases hn_gt : n > j + c
      · simp only [hn_gt, ite_true, shift]
        by_cases hn1_lt : n - 1 < c
        · omega
        · have hn1_ge : n - 1 ≥ c := Nat.le_of_not_lt hn1_lt
          simp only [hn1_lt, ite_false]
          have eq1 : Int.toNat (↑(n - 1) + (1 : Int)) = n := by
            have h : n ≥ 1 := by omega
            have : (↑(n - 1) : Int) + 1 = ↑n := by omega
            simp only [this, Int.toNat_natCast]
          simp only [eq1]
          have h_nge : ¬(n < c) := by omega
          simp only [h_nge, ite_false]
          have eq2 : Int.toNat (↑n + (1 : Int)) = n + 1 := by
            have : (↑n : Int) + 1 = ↑(n + 1) := by omega
            simp only [this, Int.toNat_natCast]
          simp only [eq2, subst]
          have h1 : n + 1 ≠ j + c + 1 := by omega
          have h2 : n + 1 > j + c + 1 := by omega
          simp only [h1, ite_false, h2, ite_true]
          simp
      · have hn_lt : n < j + c := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn_gt) hn_eq
        simp only [hn_gt, ite_false, shift]
        by_cases hn_c : n < c
        · simp only [hn_c, ite_true, subst]
          have h1 : n ≠ j + c + 1 := by omega
          have h2 : ¬(n > j + c + 1) := by omega
          simp only [h1, ite_false, h2, ite_false]
        · have hn_ge : n ≥ c := Nat.le_of_not_lt hn_c
          simp only [hn_c, ite_false]
          have eq1 : Int.toNat (↑n + (1 : Int)) = n + 1 := by
            have : (↑n : Int) + 1 = ↑(n + 1) := by omega
            simp only [this, Int.toNat_natCast]
          simp only [eq1, subst]
          have h1 : n + 1 ≠ j + c + 1 := by omega
          have h2 : ¬(n + 1 > j + c + 1) := by omega
          simp only [h1, ite_false, h2, ite_false]
  | lam L₀ ih =>
    simp only [subst, shift]
    congr 1
    have h_s1 : shift1 (shift c 0 N) = shift (c + 1) 0 N := by
      show shift 1 0 (shift c 0 N) = shift (c + 1) 0 N
      have h := shift_shift 1 c 0 N
      calc shift 1 0 (shift c 0 N) = shift (1 + c) 0 N := h
        _ = shift (c + 1) 0 N := by congr 1; omega
    have h_s2 : shift1 (shift (c + 1) 0 N) = shift (c + 2) 0 N := by
      show shift 1 0 (shift (c + 1) 0 N) = shift (c + 2) 0 N
      have h := shift_shift 1 (c + 1) 0 N
      calc shift 1 0 (shift (c + 1) 0 N) = shift (1 + (c + 1)) 0 N := h
        _ = shift (c + 2) 0 N := by congr 1; omega
    rw [h_s1, h_s2]
    exact ih N j (c + 1)
  | app L₁ L₂ ih₁ ih₂ =>
    simp only [subst, shift]
    rw [ih₁ N j c, ih₂ N j c]
  | ttrue => simp [subst, shift]
  | tfalse => simp [subst, shift]
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp only [subst, shift]
    rw [ihM N j c, ihN₁ N j c, ihN₂ N j c]

/-- shift1 commutes with subst. -/
theorem shift1_subst (L N : Term) (j : Nat) :
    shift1 (subst j N L) = subst (j + 1) (shift1 N) (shift1 L) := by
  unfold shift1
  have h := shift1_subst_gen L N j 0
  simp only [Nat.add_zero] at h
  have hz : shift (0 : Nat) 0 N = N := shift_zero 0 N
  simp only [hz] at h
  exact h

/-! ## Substitution Composition -/

/-- Generalized substitution composition lemma with level parameter. -/
theorem subst_subst_gen_full (M N L : Term) (j i : Nat) :
    subst i (subst (j+i) (shift i 0 N) (shift i 0 L)) (subst (j + i + 1) (shift (i+1) 0 N) M)
    = subst (j+i) (shift i 0 N) (subst i (shift i 0 L) M) := by
  induction M generalizing N L j i with
  | var n =>
    simp only [subst]
    by_cases hn_eq_i : n = i
    · subst hn_eq_i
      have h1 : n ≠ j + n + 1 := by omega
      have h2 : ¬(n > j + n + 1) := by omega
      simp only [h1, ite_false, h2, ite_false, ite_true]
      simp only [subst, ite_true]
    · by_cases hn_eq_ji1 : n = j + i + 1
      · simp only [hn_eq_ji1, ite_true]
        have h_shift_decomp : shift (↑i + 1) 0 N = shift 1 i (shift (↑i) 0 N) := by
          have h2 := shift_shift_offset i 0 N
          simp only [Nat.add_zero] at h2
          exact h2.symm
        rw [h_shift_decomp, subst_shift_cancel]
        have h1 : j + i + 1 ≠ i := by omega
        have h2 : j + i + 1 > i := by omega
        have h3 : j + i + 1 - 1 = j + i := by omega
        simp only [h1, ite_false, h2, ite_true, h3, subst, ite_true]
      · by_cases hn_gt : n > j + i + 1
        · have h1 : n ≠ j + i + 1 := by omega
          have hn1_ne_i : n - 1 ≠ i := by omega
          have hn1_gt_i : n - 1 > i := by omega
          have hn_ne_i : n ≠ i := by omega
          have hn_gt_i : n > i := by omega
          have hn1_ne_ji : n - 1 ≠ j + i := by omega
          have hn1_gt_ji : n - 1 > j + i := by omega
          simp only [h1, ite_false, hn_gt, ite_true, subst, hn1_ne_i, hn1_gt_i,
                     hn_ne_i, hn_gt_i, hn1_ne_ji, hn1_gt_ji]
        · have h1 : n ≠ j + i + 1 := by omega
          have h2 : ¬(n > j + i + 1) := by omega
          simp only [h1, ite_false, h2, subst, hn_eq_i]
          by_cases hn_gt_i : n > i
          · have hn1_ne_ji : n - 1 ≠ j + i := by omega
            have hn1_not_gt_ji : ¬(n - 1 > j + i) := by omega
            simp only [hn_gt_i, ite_true, subst, hn1_ne_ji, ite_false, hn1_not_gt_ji]
          · have hn_ne_ji : n ≠ j + i := by omega
            have hn_not_gt_ji : ¬(n > j + i) := by omega
            simp only [hn_gt_i, ite_false, subst, hn_ne_ji, hn_not_gt_ji]
  | lam M₀ ih =>
    simp only [subst]
    congr 1
    have int_add_comm_1 : ∀ x : Nat, (1 : Int) + ↑x = ↑x + 1 := fun x => Int.add_comm 1 ↑x
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
            congr 1
            have h_coe : (↑(i + 1) : Int) = ↑i + 1 := Int.natCast_add i 1
            omega
    rw [h_shift1_subst, h_shift_N'', h_shift_N', h_shift_L']
    exact ih N L j (i + 1)
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [subst]
    rw [ih₁ N L j i, ih₂ N L j i]
  | ttrue => simp [subst]
  | tfalse => simp [subst]
  | ite M N₁ N₂ ihM ihN₁ ihN₂ =>
    simp only [subst]
    rw [ihM N L j i, ihN₁ N L j i, ihN₂ N L j i]

/-- Generalized substitution composition lemma. -/
theorem subst_subst_gen (M N L : Term) (j : Nat) :
    (subst (j + 1) (shift1 N) M)[subst j N L] = subst j N (M[L]) := by
  have h := subst_subst_gen_full M N L j 0
  simp only [Nat.add_zero] at h
  have hz1 : shift (↑(0:Nat)) 0 N = N := shift_zero 0 N
  have hz2 : shift (↑(0:Nat)) 0 L = L := shift_zero 0 L
  have hz3 : shift (↑(0:Nat) + 1) 0 N = shift1 N := rfl
  simp only [hz1, hz2, hz3] at h
  exact h

end Term

end Metatheory.STLCextBool
