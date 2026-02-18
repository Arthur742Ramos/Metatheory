/-
# Eta Reduction and Beta-Eta Confluence

This module defines η-reduction for the lambda calculus and proves
that βη-reduction is confluent.

## Eta Reduction

The η-rule expresses extensionality:
  λx. M x →η M   (when x ∉ FV(M))

In de Bruijn notation, a term is η-reducible if it has the form:
  lam (app (shift 1 0 N) (var 0))

and η-reduces to N.

## References

- Barendregt, "The Lambda Calculus" (1984), Chapter 3
- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
-/

import Metatheory.Lambda.Parallel
import Metatheory.Lambda.Confluence
import Metatheory.Rewriting.Diamond
import Metatheory.Rewriting.Basic
import Metatheory.Rewriting.Newman

namespace Metatheory.Lambda

open Term

/-! ## Free Variable Check -/

/-- Check if var k appears free in M. -/
def hasFreeVar : Nat → Term → Bool
  | k, var n => n == k
  | k, app M N => hasFreeVar k M || hasFreeVar k N
  | k, lam M => hasFreeVar (k + 1) M

/-! ## Key Property: shift 1 0 removes var 0 -/

/-- Generalized: After shifting by 1 at cutoff c, var c cannot be free -/
theorem hasFreeVar_shift1_at (M : Term) (c : Nat) : hasFreeVar c (shift 1 c M) = false := by
  induction M generalizing c with
  | var n =>
    unfold shift hasFreeVar
    by_cases h : n < c
    · simp only [h, ite_true]
      have hne : n ≠ c := Nat.ne_of_lt h
      exact beq_eq_false_iff_ne.mpr hne
    · simp only [h, ite_false, Int.toNat_ofNat]
      have hne : n + 1 ≠ c := by omega
      have heq : (↑n + (1 : Int)).toNat = n + 1 := by simp [Int.toNat_ofNat]
      simp only [heq]
      exact beq_eq_false_iff_ne.mpr hne
  | app M N ihM ihN =>
    simp only [shift, hasFreeVar, ihM, ihN, Bool.or_false]
  | lam M ih =>
    simp only [shift, hasFreeVar]
    exact ih (c + 1)

/-- After shifting by 1, var 0 cannot be free -/
theorem hasFreeVar_shift1_zero (M : Term) : hasFreeVar 0 (shift 1 0 M) = false :=
  hasFreeVar_shift1_at M 0

/-! ## Single-Step Eta Reduction -/

/-- Single-step η-reduction. -/
inductive EtaStep : Term → Term → Prop where
  /-- The η-rule: lam (app M (var 0)) →η shift (-1) 0 M when var 0 ∉ FV(M) -/
  | eta : ∀ M, hasFreeVar 0 M = false → EtaStep (lam (app M (var 0))) (shift (-1) 0 M)
  /-- Congruence in left of application -/
  | appL : ∀ {M M' N}, EtaStep M M' → EtaStep (app M N) (app M' N)
  /-- Congruence in right of application -/
  | appR : ∀ {M N N'}, EtaStep N N' → EtaStep (app M N) (app M N')
  /-- Congruence under lambda -/
  | lam : ∀ {M M'}, EtaStep M M' → EtaStep (lam M) (lam M')

/-- Notation for eta reduction -/
scoped infix:50 " →η " => EtaStep

/-! ## Shift-Unshift Cancellation -/

/-- Generalized shift cancellation -/
theorem shift_neg1_shift1_at (M : Term) (c : Nat) : shift (-1) c (shift 1 c M) = M := by
  induction M generalizing c with
  | var n =>
    by_cases h : n < c
    · -- n < c: shift 1 c (var n) = var n, then shift (-1) c (var n) = var n
      have heq1 : shift 1 c (var n) = var n := by simp [shift, h]
      have heq2 : shift (-1) c (var n) = var n := by simp [shift, h]
      simp [heq1, heq2]
    · -- n ≥ c: shift 1 c (var n) = var (n+1), then shift (-1) c (var (n+1)) = var n
      have hge : n ≥ c := Nat.le_of_not_lt h
      have h' : ¬(n + 1 < c) := by omega
      have heq1 : shift 1 c (var n) = var (n + 1) := by
        simp [shift, h, Int.toNat_ofNat]
      have heq2 : shift (-1) c (var (n + 1)) = var n := by
        simp [shift, h']
        omega
      simp [heq1, heq2]
  | app M N ihM ihN =>
    simp [shift, ihM c, ihN c]
  | lam M ih =>
    simp [shift, ih (c + 1)]

/-- Shifting by 1 then -1 is identity -/
theorem shift_neg1_shift1 (M : Term) : shift (-1) 0 (shift 1 0 M) = M :=
  shift_neg1_shift1_at M 0

/-! ## Eta Commutes with Shift -/

/-- Helper: shifting by non-negative d at cutoff ≥ k+1 preserves hasFreeVar k = false -/
theorem hasFreeVar_shiftNat_preserved_gen (N : Term) (d : Nat) (k c : Nat)
    (hkc : k < c) (hN : hasFreeVar k N = false) : hasFreeVar k (shift d c N) = false := by
  induction N generalizing k c with
  | var n =>
    simp only [shift, hasFreeVar]
    by_cases hlt : n < c
    · simp only [hlt, ite_true]
      simp only [hasFreeVar] at hN
      exact hN
    · simp only [hlt, ite_false]
      have hge : n ≥ c := Nat.le_of_not_lt hlt
      have hne : n ≠ k := by
        intro heq
        simp only [hasFreeVar] at hN
        simp only [beq_eq_false_iff_ne] at hN
        exact hN heq
      have hne' : n + d ≠ k := by omega
      have heq : (↑n + (↑d : Int)).toNat = n + d := by omega
      simp only [heq]
      exact beq_eq_false_iff_ne.mpr hne'
  | app N1 N2 ih1 ih2 =>
    simp only [shift, hasFreeVar, Bool.or_eq_false_iff]
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hN
    exact ⟨ih1 k c hkc hN.1, ih2 k c hkc hN.2⟩
  | lam N ih =>
    simp only [shift, hasFreeVar]
    simp only [hasFreeVar] at hN
    exact ih (k + 1) (c + 1) (Nat.add_lt_add_right hkc 1) hN

/-- Helper: shifting by non-negative d at cutoff c+1 preserves hasFreeVar 0 = false -/
theorem hasFreeVar_shiftNat_preserved (N : Term) (d : Nat) (c : Nat)
    (hN : hasFreeVar 0 N = false) : hasFreeVar 0 (shift d (c + 1) N) = false :=
  hasFreeVar_shiftNat_preserved_gen N d 0 (c + 1) (Nat.zero_lt_succ c) hN

/-- Shift commutation for Nat shifts with the eta shift pattern (generalized) -/
theorem shift_shift_nat_comm_eta_gen (N : Term) (d : Nat) (k c : Nat)
    (hkc : k < c) (hN : hasFreeVar k N = false) :
    shift (-1) k (shift d c N) = shift d (c - 1) (shift (-1) k N) := by
  induction N generalizing k c with
  | var n =>
    simp only [hasFreeVar] at hN
    have hn_nek : n ≠ k := beq_eq_false_iff_ne.mp hN
    by_cases hlt : n < c
    · -- n < c: inner shift leaves it alone
      have heq_inner : shift (↑d) c (var n) = var n := by simp [shift, hlt]
      rw [heq_inner]
      by_cases hltk : n < k
      · -- n < k: outer shift leaves it alone on both sides
        have heq_left : shift (-1) k (var n) = var n := by simp [shift, hltk]
        have h' : n < c - 1 := by omega
        have heq_right : shift (↑d) (c - 1) (var n) = var n := by simp [shift, h']
        rw [heq_left, heq_right]
      · -- n ≥ k (but n ≠ k): n > k
        have hn_gtk : n > k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hltk) (Ne.symm hn_nek)
        have heq_left : shift (-1) k (var n) = var (n - 1) := by
          simp [shift, hltk]; omega
        rw [heq_left]
        have hn1_lt_c1 : n - 1 < c - 1 := by omega
        have heq_right : shift (↑d) (c - 1) (var (n - 1)) = var (n - 1) := by
          simp [shift, hn1_lt_c1]
        rw [heq_right]
    · -- n ≥ c: inner shift changes n to n + d
      have n_ge : n ≥ c := Nat.le_of_not_lt hlt
      have heq_inner : shift (↑d) c (var n) = var (n + d) := by
        simp [shift, hlt]; omega
      rw [heq_inner]
      -- n > k (since n ≥ c > k)
      have hn_gtk : n > k := Nat.lt_of_lt_of_le hkc n_ge
      have hnd_gtk : n + d > k := by omega
      have hnd_not_ltk : ¬(n + d < k) := by omega
      have heq_left : shift (-1) k (var (n + d)) = var (n + d - 1) := by
        simp [shift, hnd_not_ltk]; omega
      rw [heq_left]
      have hn_not_ltk : ¬(n < k) := by omega
      have heq_rhs1 : shift (-1) k (var n) = var (n - 1) := by
        simp [shift, hn_not_ltk]; omega
      rw [heq_rhs1]
      have hn1_ge_c1 : ¬(n - 1 < c - 1) := by omega
      have heq_rhs2 : shift (↑d) (c - 1) (var (n - 1)) = var (n - 1 + d) := by
        simp [shift, hn1_ge_c1]; omega
      rw [heq_rhs2]
      congr 1
      omega
  | app N1 N2 ih1 ih2 =>
    simp only [shift]
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hN
    simp only [ih1 k c hkc hN.1, ih2 k c hkc hN.2]
  | lam N ih =>
    simp only [shift]
    simp only [hasFreeVar] at hN
    have hkc' : k + 1 < c + 1 := Nat.add_lt_add_right hkc 1
    have heq1 : c + 1 - 1 = c := Nat.add_sub_cancel c 1
    -- Since k < c and k ≥ 0, we have c ≥ 1, so c - 1 + 1 = c
    have hc_pos : c ≥ 1 := by omega
    have heq2 : c - 1 + 1 = c := Nat.sub_add_cancel hc_pos
    rw [ih (k + 1) (c + 1) hkc' hN, heq1, heq2]

/-- Shift commutation for Nat shifts with the eta shift pattern -/
theorem shift_shift_nat_comm_eta (N : Term) (d : Nat) (c : Nat)
    (hN : hasFreeVar 0 N = false) :
    shift (-1) 0 (shift d (c + 1) N) = shift d c (shift (-1) 0 N) := by
  have h := shift_shift_nat_comm_eta_gen N d 0 (c + 1) (Nat.zero_lt_succ c) hN
  simp only [Nat.add_sub_cancel] at h
  exact h

/-- η-reduction commutes with non-negative shift -/
theorem eta_shiftNat {M M' : Term} (h : M →η M') (d : Nat) (c : Nat) :
    shift d c M →η shift d c M' := by
  induction h generalizing c with
  | eta N hN =>
    -- shift d c (lam (app N (var 0))) = lam (shift d (c+1) (app N (var 0)))
    --   = lam (app (shift d (c+1) N) (shift d (c+1) (var 0)))
    --   = lam (app (shift d (c+1) N) (var 0))  [since 0 < c+1]
    -- This is an η-redex, reducing to shift (-1) 0 (shift d (c+1) N)
    -- = shift d c (shift (-1) 0 N) by shift_shift_nat_comm_eta
    show shift d c (lam (app N (var 0))) →η shift d c (shift (-1) 0 N)
    simp only [shift]
    have h0 : (0 : Nat) < c + 1 := Nat.zero_lt_succ c
    simp only [h0, ite_true]
    have hfree : hasFreeVar 0 (shift d (c + 1) N) = false := hasFreeVar_shiftNat_preserved N d c hN
    have hstep := EtaStep.eta (shift d (c + 1) N) hfree
    have hcomm := shift_shift_nat_comm_eta N d c hN
    rw [hcomm] at hstep
    exact hstep
  | appL _ ih =>
    simp only [shift]
    exact EtaStep.appL (ih c)
  | appR _ ih =>
    simp only [shift]
    exact EtaStep.appR (ih c)
  | lam _ ih =>
    simp only [shift]
    exact EtaStep.lam (ih (c + 1))

/-- Helper: shift (-1) c preserves hasFreeVar k = false when k ≥ c and hasFreeVar (k+1) is false,
    assuming var c is not free (needed for Nat subtraction to work correctly at boundary) -/
theorem hasFreeVar_shiftDown_preserved (N : Term) (k c : Nat) (hkc : k ≥ c)
    (hNc : hasFreeVar c N = false) (hN : hasFreeVar (k + 1) N = false) :
    hasFreeVar k (shift (-1) c N) = false := by
  induction N generalizing k c with
  | var n =>
    simp only [hasFreeVar] at hNc hN
    have hnc : n ≠ c := beq_eq_false_iff_ne.mp hNc
    have hne : n ≠ k + 1 := beq_eq_false_iff_ne.mp hN
    by_cases hlt : n < c
    · -- n < c: shift doesn't change n
      have heq : shift (-1) c (var n) = var n := by simp [shift, hlt]
      rw [heq]
      simp only [hasFreeVar]
      exact beq_eq_false_iff_ne.mpr (by omega)
    · -- n > c (not n = c since hnc): shift decrements n, and n ≥ 1
      have hgt : n > c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm hnc)
      have heq : shift (-1) c (var n) = var (n - 1) := by simp [shift, hlt]; omega
      rw [heq]
      simp only [hasFreeVar]
      exact beq_eq_false_iff_ne.mpr (by omega)
  | app N1 N2 ih1 ih2 =>
    simp only [shift, hasFreeVar, Bool.or_eq_false_iff] at *
    exact ⟨ih1 k c hkc hNc.1 hN.1, ih2 k c hkc hNc.2 hN.2⟩
  | lam N ih =>
    simp only [shift, hasFreeVar] at *
    exact ih (k + 1) (c + 1) (Nat.add_le_add_right hkc 1) hNc hN

/-- η-reduction preserves absence of free variables -/
theorem eta_preserves_noFreeVar {M M' : Term} (h : M →η M') (k : Nat) :
    hasFreeVar k M = false → hasFreeVar k M' = false := by
  intro hM
  induction h generalizing k with
  | eta N hN =>
    -- M = lam (app N (var 0)), M' = shift (-1) 0 N
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hM
    have hNk : hasFreeVar (k + 1) N = false := hM.1
    exact hasFreeVar_shiftDown_preserved N k 0 (Nat.zero_le k) hN hNk
  | appL _ ih =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hM ⊢
    exact ⟨ih k hM.1, hM.2⟩
  | appR _ ih =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hM ⊢
    exact ⟨hM.1, ih k hM.2⟩
  | lam _ ih =>
    simp only [hasFreeVar] at hM ⊢
    exact ih (k + 1) hM

/-- When var k is not free, shifting at cutoff k equals shifting at cutoff k+1 -/
theorem shift_cutoff_eq_of_no_freeVar (N : Term) (d : Int) (k : Nat) (hN : hasFreeVar k N = false) :
    shift d k N = shift d (k + 1) N := by
  induction N generalizing d k with
  | var n =>
    simp only [hasFreeVar] at hN
    have hne : n ≠ k := beq_eq_false_iff_ne.mp hN
    by_cases hltk : n < k
    · -- n < k: both shifts leave n alone
      have hltk1 : n < k + 1 := Nat.lt_succ_of_lt hltk
      simp [shift, hltk, hltk1]
    · -- n ≥ k (but n ≠ k): n > k, so n ≥ k+1
      have hgtk : n > k := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hltk) (Ne.symm hne)
      have hgek1 : ¬(n < k + 1) := by omega
      simp [shift, hltk, hgek1]
  | app N1 N2 ih1 ih2 =>
    simp only [shift, hasFreeVar, Bool.or_eq_false_iff] at *
    rw [ih1 d k hN.1, ih2 d k hN.2]
  | lam N ih =>
    simp only [shift, hasFreeVar] at *
    rw [ih d (k + 1) hN]

/-- When var 0 is not free, shifting at cutoff 0 equals shifting at cutoff 1 -/
theorem shift_cutoff_eq_of_no_freeVar0 (N : Term) (d : Int) (hN : hasFreeVar 0 N = false) :
    shift d 0 N = shift d 1 N :=
  shift_cutoff_eq_of_no_freeVar N d 0 hN

/-- Generalized: After shift (-1) at cutoff c, hasFreeVar k is preserved when k+1 < c.
    This ensures the boundary variable (c-1 → c-2 after decrement) doesn't hit k. -/
theorem hasFreeVarK_shift_neg1_cutoff (N : Term) (k c : Nat) (hkc : k + 1 < c)
    (hN : hasFreeVar k N = false) : hasFreeVar k (shift (-1) c N) = false := by
  induction N generalizing k c with
  | var n =>
    simp only [hasFreeVar] at hN
    have hne : n ≠ k := beq_eq_false_iff_ne.mp hN
    by_cases hlt : n < c
    · have heq : shift (-1) c (var n) = var n := by simp [shift, hlt]
      rw [heq]
      simp only [hasFreeVar]
      exact beq_eq_false_iff_ne.mpr hne
    · -- n ≥ c > k + 1, so n > k + 1, thus n - 1 > k, meaning n - 1 ≠ k
      have hge : n ≥ c := Nat.le_of_not_lt hlt
      have heq : shift (-1) c (var n) = var (n - 1) := by simp [shift, hlt]; omega
      rw [heq]
      simp only [hasFreeVar]
      exact beq_eq_false_iff_ne.mpr (by omega)
  | app N1 N2 ih1 ih2 =>
    simp only [shift, hasFreeVar, Bool.or_eq_false_iff] at *
    exact ⟨ih1 k c hkc hN.1, ih2 k c hkc hN.2⟩
  | lam N ih =>
    simp only [shift, hasFreeVar] at *
    exact ih (k + 1) (c + 1) (by omega) hN

/-- After shift (-1) at cutoff ≥ 2, var 0 remains not free if it wasn't before.
    Note: For c = 1, this can fail if var 1 is in N (it would become var 0). -/
theorem hasFreeVar0_shift_neg1_cutoff (N : Term) (c : Nat) (hc : c ≥ 2)
    (hN : hasFreeVar 0 N = false) : hasFreeVar 0 (shift (-1) c N) = false :=
  hasFreeVarK_shift_neg1_cutoff N 0 c (by omega) hN

/-- Generalized lemma: shift (-1) c preserves hasFreeVar c when hasFreeVar (c+1) is also false -/
theorem hasFreeVarC_shift_neg1_cutoff_succ (N : Term) (c : Nat) (hc : hasFreeVar c N = false)
    (hc1 : hasFreeVar (c + 1) N = false) : hasFreeVar c (shift (-1) (c + 1) N) = false := by
  induction N generalizing c with
  | var n =>
    simp only [hasFreeVar] at hc hc1
    have hn_nec : n ≠ c := beq_eq_false_iff_ne.mp hc
    have hn_nec1 : n ≠ c + 1 := beq_eq_false_iff_ne.mp hc1
    unfold shift hasFreeVar
    by_cases hlt : n < c + 1
    · simp only [hlt, ite_true]
      exact beq_eq_false_iff_ne.mpr hn_nec
    · simp only [hlt, ite_false]
      have hge : n ≥ c + 2 := by omega
      have heq : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
      simp only [heq]
      exact beq_eq_false_iff_ne.mpr (by omega)
  | app N1 N2 ih1 ih2 =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hc hc1
    simp only [shift, hasFreeVar, Bool.or_eq_false_iff]
    exact ⟨ih1 c hc.1 hc1.1, ih2 c hc.2 hc1.2⟩
  | lam N ih =>
    simp only [hasFreeVar] at hc hc1
    simp only [shift, hasFreeVar]
    exact ih (c + 1) hc hc1

/-- Generalized: Two shift (-1) at cutoffs c and c+1 produce the same result when vars c, c+1 are absent -/
theorem shift_neg1_succ_comm (P : Term) (c : Nat) (hc : hasFreeVar c P = false) (hc1 : hasFreeVar (c + 1) P = false) :
    shift (-1) c (shift (-1) (c + 1) P) = shift (-1) c (shift (-1) c P) := by
  induction P generalizing c with
  | var n =>
    simp only [hasFreeVar] at hc hc1
    have hn_nec : n ≠ c := beq_eq_false_iff_ne.mp hc
    have hn_nec1 : n ≠ c + 1 := beq_eq_false_iff_ne.mp hc1
    -- Either n < c or n ≥ c + 2 (since n ≠ c and n ≠ c + 1)
    by_cases hlt : n < c
    · -- n < c: both shifts leave it unchanged
      have hlt' : n < c + 1 := by omega
      simp [shift, hlt, hlt']
    · -- n ≥ c + 2 (since n ≥ c and n ≠ c, n ≠ c + 1)
      have hn_ge : n ≥ c + 2 := by omega
      have hlt_c1 : ¬(n < c + 1) := by omega
      have hlt_c' : ¬(n - 1 < c) := by omega
      have heq1 : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
      have heq2 : Int.toNat (↑(n - 1) + (-1 : Int)) = n - 2 := by omega
      simp [shift, hlt, hlt_c1, heq1, heq2, hlt_c']
  | app P1 P2 ih1 ih2 =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hc hc1
    simp only [shift, ih1 c hc.1 hc1.1, ih2 c hc.2 hc1.2]
  | lam P ih =>
    simp only [hasFreeVar] at hc hc1
    simp only [shift, ih (c + 1) hc hc1]

/-- Helper: shift (-1) 1 preserves hasFreeVar 0 = false when hasFreeVar 1 is also false.
    This is because vars in {0,1} don't exist, and vars ≥ 2 become ≥ 1 > 0. -/
theorem hasFreeVar0_shift_neg1_cutoff1 (N : Term) (h0 : hasFreeVar 0 N = false)
    (h1 : hasFreeVar 1 N = false) : hasFreeVar 0 (shift (-1) 1 N) = false :=
  hasFreeVarC_shift_neg1_cutoff_succ N 0 h0 h1

/-- Helper: Two shift (-1) at cutoffs 0 and 1 produce the same result when both vars 0,1 are absent -/
theorem shift_neg1_01_comm (P : Term) (h0 : hasFreeVar 0 P = false) (h1 : hasFreeVar 1 P = false) :
    shift (-1) 0 (shift (-1) 1 P) = shift (-1) 0 (shift (-1) 0 P) :=
  shift_neg1_succ_comm P 0 h0 h1

/-- Generalized commutation of shift (-1) k and shift (-1) (c+k+1) when vars k and c+k+1 are absent -/
theorem shift_neg1_k_succ_comm (P : Term) (k c : Nat)
    (hk : hasFreeVar k P = false) (hkc : hasFreeVar (c + k + 1) P = false) :
    shift (-1) k (shift (-1) (c + k + 1) P) = shift (-1) (c + k) (shift (-1) k P) := by
  induction P generalizing k c with
  | var n =>
    simp only [hasFreeVar] at hk hkc
    have hn_nek : n ≠ k := beq_eq_false_iff_ne.mp hk
    have hn_nekc : n ≠ c + k + 1 := beq_eq_false_iff_ne.mp hkc
    by_cases hlt_k : n < k
    · -- n < k: both outer shifts leave inner result unchanged
      have hlt_kc : n < c + k + 1 := by omega
      have hlt_ck : n < c + k := by omega
      simp [shift, hlt_k, hlt_kc, hlt_ck]
    · -- n > k (since n ≠ k)
      have hn_gt : n > k := by omega
      by_cases hlt_kc : n < c + k + 1
      · -- k < n < c + k + 1: inner shift unchanged, outer shift decrements
        have heq0 : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
        have hlt_ck : n - 1 < c + k := by omega
        simp [shift, hlt_k, hlt_kc, heq0, hlt_ck]
      · -- n > c + k + 1: both shifts decrement
        have hge : n ≥ c + k + 2 := by omega
        have heq0 : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
        have heq1 : Int.toNat (↑(n - 1) + (-1 : Int)) = n - 2 := by omega
        have hlt_k' : ¬(n - 1 < k) := by omega
        have hlt_ck : ¬(n - 1 < c + k) := by omega
        simp [shift, hlt_k, hlt_kc, heq0, heq1, hlt_k', hlt_ck]
  | app P1 P2 ih1 ih2 =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hk hkc
    simp only [shift, ih1 k c hk.1 hkc.1, ih2 k c hk.2 hkc.2]
  | lam P ih =>
    simp only [hasFreeVar] at hk hkc
    simp only [shift]
    have h := ih (k + 1) c hk hkc
    simp only [Nat.add_right_comm c k 1, Nat.add_assoc] at h
    exact congrArg lam h

/-- Commutation of shift (-1) 0 and shift (-1) (c+1) when vars 0 and c+1 are absent -/
theorem shift_neg1_0_succ_comm (P : Term) (c : Nat)
    (h0 : hasFreeVar 0 P = false) (hc1 : hasFreeVar (c + 1) P = false) :
    shift (-1) 0 (shift (-1) (c + 1) P) = shift (-1) c (shift (-1) 0 P) := by
  have h := shift_neg1_k_succ_comm P 0 c h0 (by simp only [Nat.add_zero]; exact hc1)
  simp only [Nat.add_zero] at h
  exact h

/-- Generalized: η-reduction commutes with shift (-1) at cutoff c when hasFreeVar c M = false -/
theorem eta_shift_neg1_gen {M M' : Term} (h : M →η M') (c : Nat) (hM : hasFreeVar c M = false) :
    shift (-1) c M →η shift (-1) c M' := by
  induction h generalizing c with
  | eta P hP =>
    -- M = lam (app P (var 0)), M' = shift (-1) 0 P
    -- Need: shift (-1) c (lam (app P (var 0))) →η shift (-1) c (shift (-1) 0 P)
    -- Simplify: shift (-1) (c+1) (var 0) = var 0 since 0 < c + 1
    have h0_lt : 0 < c + 1 := Nat.zero_lt_succ c
    simp only [shift, h0_lt, ite_true]
    -- From hM: hasFreeVar c (lam (app P (var 0))) = false
    -- means hasFreeVar (c + 1) (app P (var 0)) = false, so hasFreeVar (c + 1) P = false
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hM
    have hP1 : hasFreeVar (c + 1) P = false := hM.1
    -- For the eta step to fire, we need hasFreeVar 0 (shift (-1) (c+1) P) = false
    have hP_shifted : hasFreeVar 0 (shift (-1) (c + 1) P) = false := by
      cases c with
      | zero => exact hasFreeVar0_shift_neg1_cutoff1 P hP hP1
      | succ c' => exact hasFreeVarK_shift_neg1_cutoff P 0 (c' + 2) (by omega) hP
    have hstep := EtaStep.eta (shift (-1) (c + 1) P) hP_shifted
    -- Use the commutation lemma
    have heq := shift_neg1_0_succ_comm P c hP hP1
    rw [heq] at hstep
    exact hstep
  | appL h' ih =>
    simp only [shift, hasFreeVar, Bool.or_eq_false_iff] at hM ⊢
    exact EtaStep.appL (ih c hM.1)
  | appR h' ih =>
    simp only [shift, hasFreeVar, Bool.or_eq_false_iff] at hM ⊢
    exact EtaStep.appR (ih c hM.2)
  | lam h' ih =>
    simp only [shift, hasFreeVar] at hM ⊢
    exact EtaStep.lam (ih (c + 1) hM)

/-- η-reduction commutes with shift (-1) at cutoff 0 when the term has no free var 0. -/
theorem eta_shift_neg1 {M M' : Term} (h : M →η M') (hM : hasFreeVar 0 M = false) :
    shift (-1) 0 M →η shift (-1) 0 M' :=
  eta_shift_neg1_gen h 0 hM

/-- Multi-step η-reduction (reflexive-transitive closure) -/
abbrev EtaMulti := Rewriting.Star EtaStep

/-- Notation for multi-step eta -/
scoped infix:50 " →η* " => EtaMulti

/-- Multi-step η-reduction commutes with non-negative shift -/
theorem eta_multi_shiftNat {M M' : Term} (h : M →η* M') (d : Nat) (c : Nat) :
    shift d c M →η* shift d c M' := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hstep ih => exact Rewriting.Star.tail ih (eta_shiftNat hstep d c)

/-! ## Standard Eta Expansion/Reduction -/

/-- Eta expansion: M → lam (app (shift 1 0 M) (var 0)) -/
def etaExpand (M : Term) : Term := lam (app (shift 1 0 M) (var 0))

/-- Eta-expanded terms are η-reducible -/
theorem etaExpand_reducible (M : Term) : EtaStep (etaExpand M) M := by
  unfold etaExpand
  have h := hasFreeVar_shift1_at M 0
  have h' := EtaStep.eta (shift 1 0 M) h
  simp only [shift_neg1_shift1_at] at h'
  exact h'

/-! ## Combined Beta-Eta Reduction -/

/-- Single-step βη-reduction -/
inductive BetaEtaStep : Term → Term → Prop where
  | beta : ∀ {M N}, BetaStep M N → BetaEtaStep M N
  | eta  : ∀ {M N}, EtaStep M N → BetaEtaStep M N

/-- Notation for beta-eta reduction -/
scoped infix:50 " →βη " => BetaEtaStep

/-- Multi-step βη-reduction (reflexive-transitive closure) -/
abbrev BetaEtaMulti := Rewriting.Star BetaEtaStep

/-- Notation for multi-step beta-eta -/
scoped infix:50 " →βη* " => BetaEtaMulti

/-! ## Conversion to Multi-step -/

/-- Beta implies beta-eta -/
theorem BetaEtaStep.of_beta {M N : Term} (h : M →β N) : M →βη N :=
  BetaEtaStep.beta h

/-- Eta implies beta-eta -/
theorem BetaEtaStep.of_eta {M N : Term} (h : M →η N) : M →βη N :=
  BetaEtaStep.eta h

/-- Multi-step beta implies multi-step beta-eta -/
theorem BetaEtaMulti.of_beta_multi {M N : Term} (h : M →* N) : M →βη* N := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | step hstep _ ih => exact Rewriting.Star.head (BetaEtaStep.of_beta hstep) ih

/-- Multi-step eta implies multi-step beta-eta -/
theorem BetaEtaMulti.of_eta_multi {M N : Term} (h : M →η* N) : M →βη* N := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hstep ih => exact Rewriting.Star.tail ih (BetaEtaStep.of_eta hstep)

/-! ## Eta Termination -/

/-- Size of a term -/
def termSize : Term → Nat
  | var _ => 1
  | app M N => 1 + termSize M + termSize N
  | lam M => 1 + termSize M

/-- Shift preserves term size -/
theorem termSize_shift (d : Int) (c : Nat) (M : Term) : termSize (shift d c M) = termSize M := by
  induction M generalizing c with
  | var n => simp only [shift, termSize]; split <;> rfl
  | app M N ihM ihN => simp only [shift, termSize, ihM, ihN]
  | lam M ih => simp only [shift, termSize, ih]

/-- η-reduction decreases term size -/
theorem eta_decreases_size {M N : Term} (h : M →η N) : termSize N < termSize M := by
  induction h with
  | eta M _ =>
    simp only [termSize, termSize_shift]
    omega
  | appL _ ih => simp only [termSize]; omega
  | appR _ ih => simp only [termSize]; omega
  | lam _ ih => simp only [termSize]; omega

/-- η-reduction is terminating -/
theorem eta_terminating : Rewriting.Terminating EtaStep := by
  unfold Rewriting.Terminating
  apply WellFounded.intro
  intro M
  generalize hsize : termSize M = n
  induction n using Nat.strongRecOn generalizing M with
  | ind n ih =>
    constructor
    intro N hstep
    cases hstep with
    | single hone =>
      have hdec := eta_decreases_size hone
      exact ih (termSize N) (by omega) N rfl
    | tail hplus hone =>
      rename_i B
      have hsizeB : termSize B < termSize M := by
        clear ih hone N
        induction hplus with
        | single h => exact eta_decreases_size h
        | tail _ hlast ih' =>
          have hdec := eta_decreases_size hlast
          omega
      have hB := ih (termSize B) (by omega) B rfl
      exact Acc.inv hB (Rewriting.Plus.single hone)

/-! ## Eta Confluence

η is terminating and locally confluent, hence confluent by Newman's lemma. -/

/-- Helper: lift eta step through app left -/
theorem appL_multi {M M' N : Term} (h : M →η* M') : app M N →η* app M' N := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hstep ih => exact Rewriting.Star.tail ih (EtaStep.appL hstep)

/-- Helper: lift eta step through app right -/
theorem appR_multi {M N N' : Term} (h : N →η* N') : app M N →η* app M N' := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hstep ih => exact Rewriting.Star.tail ih (EtaStep.appR hstep)

/-- Helper: lift eta step through lam -/
theorem lam_multi {M M' : Term} (h : M →η* M') : lam M →η* lam M' := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hstep ih => exact Rewriting.Star.tail ih (EtaStep.lam hstep)

/-- η-reduction is locally confluent.
    When two η-steps diverge from a, they can be rejoined.
    Key insight: nested η-redexes have constraints that make shift commutation work. -/
theorem eta_localConfluent : Rewriting.LocalConfluent EtaStep := fun a b c hab hac => by
  induction hab generalizing c with
  | eta M hM =>
    -- a = lam (app M (var 0)), b = shift (-1) 0 M
    cases hac with
    | eta M' hM' =>
      -- Same redex: b = c
      exact ⟨shift (-1) 0 M, Rewriting.Star.refl _, Rewriting.Star.refl _⟩
    | lam hinner =>
      -- η-step inside lam
      cases hinner with
      | appL hM_step =>
        -- M →η M''
        rename_i M''
        have hM'' : hasFreeVar 0 M'' = false := eta_preserves_noFreeVar hM_step 0 hM
        exact ⟨shift (-1) 0 M'',
               Rewriting.Star.tail (Rewriting.Star.refl _) (eta_shift_neg1 hM_step hM),
               Rewriting.Star.tail (Rewriting.Star.refl _) (EtaStep.eta M'' hM'')⟩
      | appR hvar_step =>
        cases hvar_step
  | appL hab' ih =>
    -- a = app M N, b = app M' N where M →η M'
    cases hac with
    | appL hac' =>
      have ⟨d, hd1, hd2⟩ := ih _ hac'
      exact ⟨app d _, appL_multi hd1, appL_multi hd2⟩
    | appR hN_step =>
      -- Disjoint: one step in left, one in right
      exact ⟨app _ _,
             Rewriting.Star.tail (Rewriting.Star.refl _) (EtaStep.appR hN_step),
             Rewriting.Star.tail (Rewriting.Star.refl _) (EtaStep.appL hab')⟩
  | appR hab' ih =>
    -- a = app M N, b = app M N' where N →η N'
    cases hac with
    | appL hM_step =>
      -- Disjoint: one step in left, one in right
      exact ⟨app _ _,
             Rewriting.Star.tail (Rewriting.Star.refl _) (EtaStep.appL hM_step),
             Rewriting.Star.tail (Rewriting.Star.refl _) (EtaStep.appR hab')⟩
    | appR hac' =>
      have ⟨d, hd1, hd2⟩ := ih _ hac'
      exact ⟨app _ d, appR_multi hd1, appR_multi hd2⟩
  | lam hab' ih =>
    -- a = lam M, b = lam M' where M →η M'
    cases hac with
    | eta N hN =>
      -- Outer η-redex and inner step: a = lam (app N (var 0))
      -- hab' : app N (var 0) →η M', hac : outer η
      cases hab' with
      | appL hN_step =>
        -- N →η N', so M' = app N' (var 0)
        rename_i N'
        have hN' : hasFreeVar 0 N' = false := eta_preserves_noFreeVar hN_step 0 hN
        exact ⟨shift (-1) 0 N',
               Rewriting.Star.tail (Rewriting.Star.refl _) (EtaStep.eta N' hN'),
               Rewriting.Star.tail (Rewriting.Star.refl _) (eta_shift_neg1 hN_step hN)⟩
      | appR hvar_step =>
        -- var 0 →η ??, impossible
        cases hvar_step
    | lam hac' =>
      have ⟨d, hd1, hd2⟩ := ih _ hac'
      exact ⟨lam d, lam_multi hd1, lam_multi hd2⟩

/-- η-reduction is confluent (by Newman's lemma) -/
theorem eta_confluent : Rewriting.Confluent EtaStep :=
  Rewriting.confluent_of_terminating_localConfluent eta_terminating eta_localConfluent

/-! ## Beta-Eta Commutation Lemmas -/

/-- Shifting up by 1 at cutoff c preserves hasFreeVar for k >= c (indices increase) -/
theorem hasFreeVar_shift1_gen (Q : Term) (k c : Nat) (hkc : k ≥ c) (hQ : hasFreeVar k Q = false) :
    hasFreeVar (k + 1) (shift 1 c Q) = false := by
  induction Q generalizing k c with
  | var n =>
    simp only [shift, hasFreeVar] at *
    have hne : n ≠ k := beq_eq_false_iff_ne.mp hQ
    by_cases hlt : n < c
    · -- n < c: shift doesn't change n, need n ≠ k + 1
      simp only [hlt, ite_true]
      exact beq_eq_false_iff_ne.mpr (by omega)
    · -- n >= c: shift changes n to n + 1, need n + 1 ≠ k + 1, i.e., n ≠ k
      simp only [hlt, ite_false, Int.toNat_ofNat]
      exact beq_eq_false_iff_ne.mpr (by omega)
  | app Q1 Q2 ih1 ih2 =>
    simp only [shift, hasFreeVar, Bool.or_eq_false_iff] at *
    exact ⟨ih1 k c hkc hQ.1, ih2 k c hkc hQ.2⟩
  | lam Q ih =>
    simp only [shift, hasFreeVar] at *
    exact ih (k + 1) (c + 1) (Nat.add_le_add_right hkc 1) hQ

/-- Shifting up by 1 at cutoff 0 preserves hasFreeVar (special case) -/
theorem hasFreeVar_shift1 (Q : Term) (k : Nat) (hQ : hasFreeVar k Q = false) :
    hasFreeVar (k + 1) (shift 1 0 Q) = false :=
  hasFreeVar_shift1_gen Q k 0 (Nat.zero_le k) hQ

/-- Generalized: Substitution at j preserves hasFreeVar k when j ≤ k,
    body doesn't have var (k+1) free, and substitutee doesn't have var k free -/
theorem hasFreeVar_subst_gen (P Q : Term) (k j : Nat) (hjk : j ≤ k)
    (hP : hasFreeVar (k + 1) P = false) (hQ : hasFreeVar k Q = false) :
    hasFreeVar k (subst j Q P) = false := by
  induction P generalizing k j Q with
  | var n =>
    simp only [subst, hasFreeVar]
    simp only [hasFreeVar] at hP
    have hn_ne_k1 : n ≠ k + 1 := beq_eq_false_iff_ne.mp hP
    by_cases hn_eq_j : n = j
    · -- n = j: substitute Q, hasFreeVar k Q = false
      simp only [hn_eq_j, ite_true]
      exact hQ
    · simp only [hn_eq_j, ite_false]
      by_cases hn_gt_j : n > j
      · -- n > j: result is var (n - 1), need n - 1 ≠ k
        simp only [hn_gt_j, ite_true]
        -- n ≠ k + 1 and n > j, so n - 1 ≠ k (since if n - 1 = k then n = k + 1)
        exact beq_eq_false_iff_ne.mpr (by omega)
      · -- n < j ≤ k: result is var n, need n ≠ k
        simp only [hn_gt_j, ite_false]
        have hn_lt_j : n < j := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn_gt_j) hn_eq_j
        exact beq_eq_false_iff_ne.mpr (by omega)
  | app P1 P2 ih1 ih2 =>
    simp only [subst, hasFreeVar, Bool.or_eq_false_iff] at *
    exact ⟨ih1 Q k j hjk hP.1 hQ, ih2 Q k j hjk hP.2 hQ⟩
  | lam P ih =>
    simp only [subst, hasFreeVar] at *
    -- Need: hasFreeVar (k+1) (subst (j+1) (shift1 Q) P) = false
    -- Apply IH at (k+1, j+1)
    have hQ' : hasFreeVar (k + 1) (shift1 Q) = false := hasFreeVar_shift1 Q k hQ
    exact ih (shift1 Q) (k + 1) (j + 1) (by omega) hP hQ'

/-- Substitution at 0 preserves hasFreeVar k when body doesn't have var (k+1) free
    and substitutee doesn't have var k free -/
theorem hasFreeVar_subst0 (P Q : Term) (k : Nat)
    (hP : hasFreeVar (k + 1) P = false) (hQ : hasFreeVar k Q = false) :
    hasFreeVar k (subst 0 Q P) = false :=
  hasFreeVar_subst_gen P Q k 0 (Nat.zero_le k) hP hQ

/-- β-reduction preserves absence of free variables -/
theorem beta_preserves_noFreeVar {M M' : Term} (h : M →β M') (k : Nat) :
    hasFreeVar k M = false → hasFreeVar k M' = false := by
  intro hM
  induction h generalizing k with
  | beta P Q =>
    -- M = app (lam P) Q, hasFreeVar k M = false
    -- Need: hasFreeVar k (subst 0 Q P) = false
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hM
    -- hM : hasFreeVar k (lam P) = false ∧ hasFreeVar k Q = false
    have hlamP : hasFreeVar k (lam P) = false := hM.1
    have hQ : hasFreeVar k Q = false := hM.2
    simp only [hasFreeVar] at hlamP
    -- hlamP : hasFreeVar (k + 1) P = false
    exact hasFreeVar_subst0 P Q k hlamP hQ
  | appL _ ih =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hM ⊢
    exact ⟨ih k hM.1, hM.2⟩
  | appR _ ih =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hM ⊢
    exact ⟨hM.1, ih k hM.2⟩
  | lam _ ih =>
    simp only [hasFreeVar] at hM ⊢
    exact ih (k + 1) hM

/-- β-reduction commutes with non-negative shift -/
theorem beta_shiftNat {M M' : Term} (h : M →β M') (d : Nat) (c : Nat) :
    shift d c M →β shift d c M' := by
  induction h generalizing c with
  | beta P Q =>
    simp only [shift]
    have heq : shift d c (subst 0 Q P) = subst 0 (shift d c Q) (shift d (c + 1) P) :=
      shift_subst_at P Q d c 0 (Nat.zero_le c)
    rw [heq]
    exact BetaStep.beta _ _
  | appL _ ih =>
    simp only [shift]
    exact BetaStep.appL (ih c)
  | appR _ ih =>
    simp only [shift]
    exact BetaStep.appR (ih c)
  | lam _ ih =>
    simp only [shift]
    exact BetaStep.lam (ih (c + 1))

/-- β-reduction commutes with non-negative shift.
    Note: For negative d, the interaction between shift and subst is not well-behaved
    due to Int.toNat truncation. We only prove the non-negative case which suffices
    for most applications. -/
theorem beta_shift {M M' : Term} (h : M →β M') (d : Nat) (c : Nat) :
    shift d c M →β shift d c M' :=
  beta_shiftNat h d c

/-! ## Key Lemma: Shift-Substitution Commutation

This lemma is crucial for proving that η commutes with substitution.
It states that substituting after shifting is the same as shifting after substituting,
with appropriate index adjustments. -/

/-- Shift-subst commutation: substituting at c+d after shifting at cutoff c equals
    shifting at cutoff c after substituting at c.

    `subst (c+d) (shift d c N) (shift d c M) = shift d c (subst c N M)`

    After shift d c, variable c becomes c+d, so we substitute at c+d to target it.
    This is the correct formulation - j must equal c, not just j ≤ c. -/
theorem subst_shift_comm (M N : Term) (d : Nat) (c : Nat) :
    subst (c + d) (shift d c N) (shift d c M) = shift d c (subst c N M) := by
  induction M generalizing c N with
  | var n =>
    by_cases hn_lt : n < c
    · -- n < c: shift doesn't change n
      have hshift : shift (↑d) c (var n) = var n := by simp [shift, hn_lt]
      rw [hshift]
      -- n ≠ c, n < c+d
      have hne : n ≠ c := Nat.ne_of_lt hn_lt
      have hlt_cd : n < c + d := Nat.lt_of_lt_of_le hn_lt (Nat.le_add_right c d)
      have hne_cd : n ≠ c + d := Nat.ne_of_lt hlt_cd
      have hgt_cd : ¬(n > c + d) := by omega
      have hgt_c : ¬(n > c) := by omega
      -- LHS: subst (c+d) (shift d c N) (var n) where n ≠ c+d and n < c+d
      have lhs : subst (c + d) (shift (↑d) c N) (var n) = var n := by
        simp [subst, hne_cd, hgt_cd]
      -- RHS: shift d c (subst c N (var n)) where n ≠ c and n < c
      have rhs : shift (↑d) c (subst c N (var n)) = var n := by
        simp [subst, hne, hgt_c, shift, hn_lt]
      rw [lhs, rhs]
    · -- n ≥ c
      by_cases hn_eq : n = c
      · -- n = c: substitute N
        -- shift d c (var n) = var (n + d) since n ≥ c and n = c
        have hshift : shift (↑d) c (var n) = var (n + d) := by
          simp [shift, hn_lt]
          omega
        rw [hshift, hn_eq]
        -- LHS: subst (c+d) (shift d c N) (var (c+d)) = shift d c N
        have lhs : subst (c + d) (shift (↑d) c N) (var (c + d)) = shift (↑d) c N := by
          simp [subst]
        -- RHS: shift d c (subst c N (var c)) = shift d c N
        have rhs : shift (↑d) c (subst c N (var c)) = shift (↑d) c N := by
          simp [subst]
        rw [lhs, rhs]
      · -- n > c: shift gives n + d
        have hn_gt : n > c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hn_lt) (Ne.symm hn_eq)
        -- shift d c (var n) = var (n + d)
        have hshift : shift (↑d) c (var n) = var (n + d) := by
          simp [shift, hn_lt]
          omega
        rw [hshift]
        -- n + d ≠ c + d, n + d > c + d
        have hne_cd : n + d ≠ c + d := by omega
        have hgt_cd : n + d > c + d := by omega
        -- LHS: subst (c+d) (shift d c N) (var (n+d))
        -- Since n+d ≠ c+d and n+d > c+d, result is var (n+d-1)
        have lhs : subst (c + d) (shift (↑d) c N) (var (n + d)) = var (n + d - 1) := by
          simp [subst, hne_cd, hgt_cd]
        -- RHS: shift d c (subst c N (var n))
        -- Since n ≠ c and n > c, subst gives var (n-1)
        -- Then shift d c (var (n-1)) where n-1 ≥ c (since n > c) gives var (n-1+d)
        have rhs : shift (↑d) c (subst c N (var n)) = var (n - 1 + d) := by
          have hsub : subst c N (var n) = var (n - 1) := by simp [subst, hn_eq, hn_gt]
          rw [hsub]
          have hn1_ge : n - 1 ≥ c := by omega
          have hn1_lt : ¬(n - 1 < c) := by omega
          simp [shift, hn1_lt]
          omega
        rw [lhs, rhs]
        congr 1
        omega
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [shift, subst, ih₁, ih₂]
  | lam M ih =>
    simp only [shift, subst]
    congr 1
    -- LHS: subst (c + d + 1) (shift1 (shift d c N)) (shift d (c + 1) M)
    -- RHS: shift d (c + 1) (subst (c + 1) (shift1 N) M)
    -- Use IH with c' = c + 1 and N' = shift1 N
    have h_shift : shift1 (shift (↑d) c N) = shift (↑d) (c + 1) (shift1 N) := by
      -- shift 1 0 (shift d c N) = shift d (c + 1) (shift 1 0 N)
      -- This is shift_shift_comm with d₁ = 1, d₂ = d, c₁ = 0, c₂ = c
      have h := shift_shift_comm 1 d 0 c N (Nat.zero_le c)
      simp only [Nat.zero_add] at h
      unfold shift1
      exact h
    have h_arith : c + d + 1 = (c + 1) + d := by omega
    rw [h_arith, h_shift]
    exact ih (shift1 N) (c + 1)

/-- Special case: subst at 1 after shift 1 0 equals shift 1 0 after subst at 0 -/
theorem subst1_shift1_comm (M N : Term) :
    subst 1 (shift1 N) (shift 1 0 M) = shift 1 0 (M[N]) := by
  have h := subst_shift_comm M N 1 0
  simp only [Nat.zero_add] at h
  unfold shift1
  exact h

/-! ## Eta Commutes with Substitution -/

/-- Helper: shift 1 0 N has no free var 0 (since all vars are shifted up) -/
theorem hasFreeVar0_shift1 (N : Term) : hasFreeVar 0 (shift1 N) = false :=
  hasFreeVar_shift1_at N 0

/-- General lemma: hasFreeVar k (subst j N P) = false when:
    - k < j and hasFreeVar k P = false, OR
    - hasFreeVar k P = false and hasFreeVar k N = false (for var j case)
    This version handles k < j with the required constraints. -/
theorem hasFreeVar_subst_lt (P N : Term) (k j : Nat) (hkj : k < j)
    (hP : hasFreeVar k P = false) (hN : hasFreeVar k N = false) :
    hasFreeVar k (subst j N P) = false := by
  induction P generalizing k j N with
  | var n =>
    simp only [subst, hasFreeVar] at *
    have hn_nek : n ≠ k := beq_eq_false_iff_ne.mp hP
    by_cases hn_eqj : n = j
    · -- n = j: substitute N
      simp only [hn_eqj, ite_true]
      exact hN
    · simp only [hn_eqj, ite_false]
      by_cases hn_gtj : n > j
      · -- n > j: result is var (n - 1), need n - 1 ≠ k
        simp only [hn_gtj, ite_true]
        -- n > j > k, so n - 1 ≥ j > k, thus n - 1 ≠ k
        exact beq_eq_false_iff_ne.mpr (by omega)
      · -- n < j: result is var n, need n ≠ k (which we have from hn_nek)
        simp only [hn_gtj, ite_false]
        exact beq_eq_false_iff_ne.mpr hn_nek
  | app P1 P2 ih1 ih2 =>
    simp only [subst, hasFreeVar, Bool.or_eq_false_iff] at *
    exact ⟨ih1 N k j hkj hP.1 hN, ih2 N k j hkj hP.2 hN⟩
  | lam P ih =>
    simp only [subst, hasFreeVar] at *
    -- Need: hasFreeVar (k+1) (subst (j+1) (shift1 N) P) = false
    -- Given: hasFreeVar (k+1) P = false (from hP)
    -- Given: hasFreeVar k N = false (from hN)
    -- Need: hasFreeVar (k+1) (shift1 N) = false
    have hN' : hasFreeVar (k + 1) (shift1 N) = false := hasFreeVar_shift1 N k hN
    exact ih (shift1 N) (k + 1) (j + 1) (by omega) hP hN'

/-- Helper: substituting at index 1 preserves hasFreeVar 0 = false when
    the original term has no var 0 and the substitutee has no var 0 -/
theorem hasFreeVar0_subst1 (P N : Term) (hP : hasFreeVar 0 P = false)
    (hN : hasFreeVar 0 N = false) : hasFreeVar 0 (subst 1 N P) = false :=
  hasFreeVar_subst_lt P N 0 1 (Nat.zero_lt_one) hP hN

/-- Generalized commutation: shift (-1) c (subst (c+1) (shift (c+1) 0 N) P) = subst c (shift c 0 N) (shift (-1) c P)
    when hasFreeVar c P = false. -/
theorem shift_neg1_subst_comm_gen (P N : Term) (c : Nat) (hP : hasFreeVar c P = false) :
    shift (-1) c (subst (c + 1) (shift (c + 1) 0 N) P) = subst c (shift c 0 N) (shift (-1) c P) := by
  induction P generalizing N c with
  | var n =>
    simp only [hasFreeVar] at hP
    have hn_nec : n ≠ c := beq_eq_false_iff_ne.mp hP
    by_cases hn_eqc1 : n = c + 1
    · -- n = c + 1: var (c+1) → shift (c+1) 0 N under subst, then shift (-1) c
      subst hn_eqc1
      simp only [subst, ite_true]
      -- LHS: shift (-1) c (shift (c + 1) 0 N) = shift c 0 N
      -- This is because shift (-1) c undoes one level of shift (c+1) 0 at cutoff c
      -- shift (c+1) 0 N: all vars become + (c+1)
      -- shift (-1) c: vars ≥ c become - 1
      -- Since shift (c+1) 0 N has all vars ≥ c+1 > c, they all get decremented
      -- Result: vars become + c
      have hcomm : shift (-1) c (shift (c + 1) 0 N) = shift c 0 N := by
        induction N generalizing c with
        | var m =>
          simp only [shift, Nat.not_lt_zero, ite_false, Int.toNat_ofNat]
          -- LHS: shift (-1) c (var (m + c + 1))
          have h1 : ¬(m + (c + 1) < c) := by omega
          simp only [h1, ite_false]
          have h2 : Int.toNat (↑(m + (c + 1)) + (-1 : Int)) = m + c := by omega
          simp only [h2]
        | app N1 N2 ih1 ih2 =>
          simp only [shift, ih1, ih2]
        | lam N ih =>
          simp only [shift]
          have h : c + 1 + 1 = (c + 1) + 1 := rfl
          rw [ih (c + 1)]
      rw [hcomm]
      -- RHS: subst c (shift c 0 N) (shift (-1) c (var (c + 1)))
      have h_shift : shift (-1) c (var (c + 1)) = var c := by
        simp only [shift]
        have h1 : ¬(c + 1 < c) := by omega
        simp only [h1, ite_false]
        have h2 : Int.toNat (↑(c + 1) + (-1 : Int)) = c := by omega
        simp only [h2]
      simp only [h_shift, subst, ite_true]
    · by_cases hn_gtc1 : n > c + 1
      · -- n > c + 1: subst gives var (n-1), then shift (-1) c gives var (n-2)
        simp only [subst, hn_eqc1, ite_false, hn_gtc1, ite_true, shift]
        have hn1_gec : ¬(n - 1 < c) := by omega
        simp only [hn1_gec, ite_false]
        have h1 : Int.toNat (↑(n - 1) + (-1 : Int)) = n - 2 := by omega
        simp only [h1]
        -- RHS: subst c ... (shift (-1) c (var n))
        have hn_gec : ¬(n < c) := by omega
        simp only [hn_gec, ite_false]
        have h2 : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
        simp only [h2, subst]
        have hn1_nec : n - 1 ≠ c := by omega
        have hn1_gtc : n - 1 > c := by omega
        simp only [hn1_nec, ite_false, hn1_gtc, ite_true]
        congr 1
        omega
      · -- n ≤ c + 1, n ≠ c + 1, n ≠ c: so n < c
        have hn_ltc : n < c := by omega
        simp only [subst, hn_eqc1, ite_false, hn_gtc1, ite_false, shift, hn_ltc, ite_true]
        simp only [subst]
        have hn_nec' : n ≠ c := by omega
        have hn_gtc : ¬(n > c) := by omega
        simp only [hn_nec', ite_false, hn_gtc, ite_false]
  | app P1 P2 ih1 ih2 =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hP
    simp only [subst, shift, ih1 N c hP.1, ih2 N c hP.2]
  | lam P ih =>
    simp only [hasFreeVar] at hP
    simp only [subst, shift]
    congr 1
    -- Need: shift (-1) (c+1) (subst (c+2) (shift1 (shift (c+1) 0 N)) P)
    --     = subst (c+1) (shift1 (shift c 0 N)) (shift (-1) (c+1) P)
    -- Use IH at c' = c + 1
    -- shift1 (shift (c+1) 0 N) = shift 1 0 (shift (c+1) 0 N) = shift (c+2) 0 N by shift_shift
    have h_shift_l : shift1 (shift (c + 1) 0 N) = shift (c + 2) 0 N := by
      unfold shift1
      have h := shift_shift 1 (c + 1) 0 N
      simp only [Nat.add_comm 1 (c + 1)] at h
      exact h
    -- shift1 (shift c 0 N) = shift 1 0 (shift c 0 N) = shift (c+1) 0 N by shift_shift
    have h_shift_r : shift1 (shift c 0 N) = shift (c + 1) 0 N := by
      unfold shift1
      have h := shift_shift 1 c 0 N
      simp only [Nat.add_comm 1 c] at h
      exact h
    rw [h_shift_l, h_shift_r]
    have h_arith : c + 2 = (c + 1) + 1 := by omega
    rw [h_arith]
    exact ih N (c + 1) hP

/-- Key commutation: shift (-1) 0 (subst 1 (shift1 N) P) = subst 0 N (shift (-1) 0 P)
    when hasFreeVar 0 P = false. -/
theorem shift_neg1_subst1_comm (P N : Term) (hP : hasFreeVar 0 P = false) :
    shift (-1) 0 (subst 1 (shift1 N) P) = subst 0 N (shift (-1) 0 P) := by
  have h := shift_neg1_subst_comm_gen P N 0 hP
  simp only [Nat.zero_add, shift_zero] at h
  unfold shift1
  exact h

/-- η-reduction commutes with substitution: if M →η M' then M[N] →η* M'[N] -/
theorem eta_subst {M M' : Term} (h : M →η M') (N : Term) :
    M[N] →η* M'[N] := by
  induction h generalizing N with
  | eta P hP =>
    -- M = lam (app P (var 0)), M' = shift (-1) 0 P
    -- M[N] = lam (subst 1 (shift1 N) (app P (var 0)))
    --      = lam (app (subst 1 (shift1 N) P) (var 0))
    -- M'[N] = subst 0 N (shift (-1) 0 P)
    -- We need M[N] →η* M'[N]
    simp only [subst0, subst]
    -- subst 1 (shift1 N) (var 0) = var 0 since 0 ≠ 1 and 0 < 1
    have h_var0 : subst 1 (shift1 N) (var 0) = var 0 := by simp [subst]
    simp only [h_var0]
    -- Now LHS = lam (app (subst 1 (shift1 N) P) (var 0))
    -- Check if this is an η-redex
    have hP' : hasFreeVar 0 (subst 1 (shift1 N) P) = false := by
      have hN0 : hasFreeVar 0 (shift1 N) = false := hasFreeVar0_shift1 N
      exact hasFreeVar0_subst1 P (shift1 N) hP hN0
    -- LHS →η shift (-1) 0 (subst 1 (shift1 N) P)
    have hstep := EtaStep.eta (subst 1 (shift1 N) P) hP'
    -- And by commutation: shift (-1) 0 (subst 1 (shift1 N) P) = subst 0 N (shift (-1) 0 P) = RHS
    have hcomm := shift_neg1_subst1_comm P N hP
    rw [hcomm] at hstep
    exact Rewriting.Star.tail (Rewriting.Star.refl _) hstep
  | appL hab' ih =>
    simp only [subst0, subst]
    exact appL_multi (ih N)
  | appR hab' ih =>
    simp only [subst0, subst]
    exact appR_multi (ih N)
  | lam hab' ih =>
    simp only [subst0, subst]
    exact lam_multi (ih (shift1 N))

/-- Multi-step η commutes with substitution -/
theorem eta_multi_subst {M M' : Term} (h : M →η* M') (N : Term) :
    M[N] →η* M'[N] := by
  induction h with
  | refl => exact Rewriting.Star.refl _
  | tail _ hstep ih => exact Rewriting.Star.trans ih (eta_subst hstep N)

/-! ## Beta-Eta Commutation

The key result: β and η commute, enabling Hindley-Rosen. -/

/-- Multi-step β reduction commutes with (non-negative) shift -/
theorem beta_multi_shift {M M' : Term} (h : M →* M') (d : Nat) (c : Nat) :
    shift d c M →* shift d c M' := by
  induction h with
  | refl => exact MultiStep.refl _
  | step hstep _ ih => exact MultiStep.step (beta_shift hstep d c) ih

/-- General version: η-step on substitutee at any index -/
theorem eta_subst_arg_gen {N N' : Term} (hN : N →η N') (M : Term) (j : Nat) :
    subst j N M →η* subst j N' M := by
  induction M generalizing j N N' with
  | var n =>
    simp only [subst]
    by_cases hn : n = j
    · simp only [hn, ite_true]
      exact Rewriting.Star.tail (Rewriting.Star.refl _) hN
    · simp only [hn, ite_false]
      by_cases hn' : n > j
      · simp only [hn', ite_true]; exact Rewriting.Star.refl _
      · simp only [hn', ite_false]; exact Rewriting.Star.refl _
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [subst]
    exact Rewriting.Star.trans (appL_multi (ih₁ j N N' hN)) (appR_multi (ih₂ j N N' hN))
  | lam M ih =>
    simp only [subst]
    have hN_shift : shift1 N →η shift1 N' := eta_shiftNat hN 1 0
    exact lam_multi (ih (j + 1) (shift1 N) (shift1 N') hN_shift)

/-- η-step on substitutee: if N →η N' then M[N] →η* M[N'] -/
theorem eta_subst_arg {N N' : Term} (hN : N →η N') (M : Term) :
    M[N] →η* M[N'] :=
  eta_subst_arg_gen hN M 0

/-- When hasFreeVar k P = false, substituting at index k gives the same result as shift (-1) k.
    This is because var k never occurs in P, so the substituted term N is never used,
    and both operations decrement variables > k by 1. -/
theorem subst_eq_shift_neg1_of_noFreeVar (P : Term) (k : Nat) (N : Term) (hP : hasFreeVar k P = false) :
    subst k N P = shift (-1) k P := by
  induction P generalizing k N with
  | var n =>
    simp only [hasFreeVar] at hP
    have hn_nek : n ≠ k := beq_eq_false_iff_ne.mp hP
    simp only [subst, hn_nek, ite_false, shift]
    by_cases hn_gtk : n > k
    · -- n > k: subst gives var (n-1), shift also gives var (n-1)
      simp only [hn_gtk, ite_true]
      have hn_gek : ¬(n < k) := by omega
      simp only [hn_gek, ite_false]
      have heq : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
      simp only [heq]
    · -- n < k: subst gives var n, shift gives var n
      have hn_ltk : n < k := by omega
      simp only [hn_gtk, ite_false, hn_ltk, ite_true]
  | app P₁ P₂ ih₁ ih₂ =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hP
    simp only [subst, shift, ih₁ k N hP.1, ih₂ k N hP.2]
  | lam P ih =>
    simp only [hasFreeVar] at hP
    simp only [subst, shift]
    congr 1
    exact ih (k + 1) (shift1 N) hP

/-- Key identity: substituting (var j) at index j equals shifting down by 1 at cutoff j+1.
    This works because both operations:
    - Leave vars < j unchanged
    - Map var j to var j (identity at target)
    - Decrement vars > j to vars > j - 1 -/
theorem subst_var_eq_shift_neg1 (M : Term) (j : Nat) :
    subst j (var j) M = shift (-1) (j + 1) M := by
  induction M generalizing j with
  | var n =>
    simp only [subst, shift]
    by_cases hn_eq : n = j
    · -- n = j: subst gives (var j), shift leaves unchanged (j < j + 1)
      simp only [hn_eq, ite_true]
      have hlt : j < j + 1 := Nat.lt_succ_self j
      simp only [hlt, ite_true]
    · simp only [hn_eq, ite_false]
      by_cases hn_gt : n > j
      · -- n > j: subst gives var (n - 1), shift at j + 1 gives var (n - 1) for n ≥ j + 1
        simp only [hn_gt, ite_true]
        have hge : n ≥ j + 1 := by omega
        have hlt : ¬(n < j + 1) := by omega
        simp only [hlt, ite_false]
        have heq : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
        simp only [heq]
      · -- n < j: subst gives var n, shift leaves unchanged (n < j + 1)
        simp only [hn_gt, ite_false]
        have hlt : n < j + 1 := by omega
        simp only [hlt, ite_true]
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [subst, shift, ih₁ j, ih₂ j]
  | lam M ih =>
    simp only [subst, shift]
    -- LHS: lam (subst (j + 1) (shift1 (var j)) M) = lam (subst (j + 1) (var (j + 1)) M)
    -- RHS: lam (shift (-1) (j + 2) M)
    have h_shift1_var : shift1 (var j) = var (j + 1) := by
      simp only [shift1, shift, Nat.not_lt_zero, ite_false, Int.toNat_ofNat]
    rw [h_shift1_var]
    congr 1
    exact ih (j + 1)

/-- Generalized commutation: shift (-1) c (subst c N M) = subst c (shift (-1) c N) (shift (-1) (c+1) M)
    when hasFreeVar (c+1) M = false and hasFreeVar c N = false.
    This is the key lemma for β commuting with negative shift. -/
theorem shift_neg1_subst0_comm_gen (M N : Term) (c : Nat) (hM : hasFreeVar (c + 1) M = false)
    (hN : hasFreeVar c N = false) :
    shift (-1) c (subst c N M) = subst c (shift (-1) c N) (shift (-1) (c + 1) M) := by
  induction M generalizing c N with
  | var n =>
    simp only [subst, shift]
    by_cases hn_eq : n = c
    · -- n = c: subst gives N, we need shift (-1) c N = subst c (shift (-1) c N) (shift (-1) (c+1) (var c))
      simp only [hn_eq, ite_true]
      -- shift (-1) (c+1) (var c) = var c since c < c + 1
      have hlt : c < c + 1 := Nat.lt_succ_self c
      simp only [hlt, ite_true, subst, ite_true]
    · simp only [hn_eq, ite_false]
      by_cases hn_gt : n > c
      · -- n > c: subst gives var (n - 1)
        simp only [hn_gt, ite_true]
        -- M = var n with hasFreeVar (c+1) (var n) = false means n ≠ c + 1
        simp only [hasFreeVar] at hM
        have hn_nec1 : n ≠ c + 1 := beq_eq_false_iff_ne.mp hM
        have hn_gec2 : n ≥ c + 2 := by omega
        -- shift (-1) c (var (n-1)) where n - 1 ≥ c + 1 > c
        have hn1_gec : n - 1 ≥ c := by omega
        have hn1_ltc : ¬(n - 1 < c) := by omega
        simp only [hn1_ltc, ite_false]
        have heq1 : Int.toNat (↑(n - 1) + (-1 : Int)) = n - 2 := by omega
        simp only [heq1]
        -- RHS: shift (-1) (c+1) (var n) where n > c + 1
        have hn_ltc1 : ¬(n < c + 1) := by omega
        simp only [hn_ltc1, ite_false]
        have heq2 : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
        simp only [heq2, subst]
        -- n - 1 ≠ c since n ≥ c + 2
        have hn1_nec : n - 1 ≠ c := by omega
        have hn1_gtc : n - 1 > c := by omega
        simp only [hn1_nec, ite_false, hn1_gtc, ite_true]
      · -- n < c: subst gives var n, shift gives var n
        have hn_ltc : n < c := by omega
        simp only [hn_gt, ite_false, hn_ltc, ite_true]
        -- RHS: shift (-1) (c+1) (var n) = var n since n < c < c + 1
        have hn_ltc1 : n < c + 1 := Nat.lt_succ_of_lt hn_ltc
        simp only [hn_ltc1, ite_true, subst]
        have hn_nec : n ≠ c := Nat.ne_of_lt hn_ltc
        have hn_ngc : ¬(n > c) := by omega
        simp only [hn_nec, ite_false, hn_ngc, ite_false]
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hM
    simp only [subst, shift, ih₁ c N hM.1 hN, ih₂ c N hM.2 hN]
  | lam M ih =>
    simp only [hasFreeVar] at hM
    simp only [subst, shift]
    congr 1
    -- Need: shift (-1) (c+1) (subst (c+1) (shift1 N) M) = subst (c+1) (shift1 (shift (-1) c N)) (shift (-1) (c+2) M)
    -- Use IH with c' = c + 1
    -- Need: hasFreeVar (c + 2) M = false (from hM : hasFreeVar (c + 1) (lam M) = hasFreeVar (c + 2) M)
    -- Actually hM already says hasFreeVar (c + 1) M = false... wait, no.
    -- hasFreeVar (c + 1) (lam M) = hasFreeVar (c + 2) M. But hM : hasFreeVar (c + 1) M = false.
    -- Hmm, there's a mismatch. Let me re-check.
    -- Original hM : hasFreeVar (c + 1) M = false where M is the original lam body
    -- In the lam case, we're processing (lam M) and the body is M
    -- hasFreeVar (c + 1) (lam M) = hasFreeVar (c + 2) M
    -- But I wrote hM : hasFreeVar (c + 1) M = false. This is from the outer level.
    -- Need: hasFreeVar ((c+1) + 1) M = hasFreeVar (c + 2) M = false
    -- The IH needs hasFreeVar (c + 2) M = false, but we have hasFreeVar (c + 1) M = false at this level.
    -- Wait, I think the issue is the indices. Let me reconsider.
    -- We're processing the body M of (lam M). At this point:
    -- - c' = c + 1 for the recursion
    -- - Need hasFreeVar (c' + 1) M = hasFreeVar (c + 2) M = false
    -- But hM from pattern says hasFreeVar (c + 1) M = false where M is THIS body
    -- So I need hasFreeVar (c + 2) M from hasFreeVar (c + 1) M -- that's a weakening that doesn't hold!
    -- Actually wait, no. In the lam case above, hM comes from the pattern match on `hasFreeVar` of the
    -- original (lam M). So simp only [hasFreeVar] at hM transforms:
    --   hasFreeVar (c + 1) (lam M) = false
    -- to:
    --   hasFreeVar (c + 2) M = false
    -- So hM : hasFreeVar (c + 2) M = false. Let me check...
    -- Yes! Because hasFreeVar k (lam M) = hasFreeVar (k + 1) M.
    -- So hasFreeVar (c + 1) (lam M) = hasFreeVar (c + 2) M.
    -- Wait no, I'm getting confused. The definition is:
    --   hasFreeVar k (lam M) = hasFreeVar (k + 1) M
    -- So after simp only [hasFreeVar] at hM, if hM was originally hasFreeVar (c + 1) (lam M) = false,
    -- it becomes hasFreeVar (c + 2) M = false.
    -- But in the proof, we're doing structural induction on M, and in the lam case,
    -- M is the whole term (lam <body>), and hM is the hypothesis about M.
    -- After simp, hM : hasFreeVar (c + 1) M = false becomes hasFreeVar (c + 2) <body> = false.
    -- Hmm, let me look at the code again...
    -- Actually, I think the simp unfolds hasFreeVar for (lam M) one level, which gives us the body's constraint.
    -- For the IH, we need the constraint on the lam body.
    -- Actually, looking again, in the case `| lam M ih =>`, M is the BODY of the lambda!
    -- So when the original constraint says hasFreeVar (c + 1) (lam <body>) = false,
    -- simp gives hasFreeVar (c + 2) <body> = false.
    -- But in the code, hM refers to the BODY M, so after simp, hM : hasFreeVar (c + 2) M... no wait.
    --
    -- Let me be very careful. The theorem says:
    -- `shift_neg1_subst0_comm_gen (M N : Term) (c : Nat) (hM : hasFreeVar (c + 1) M = false)`
    -- In the lam case, M is `lam M'` for some M', and we pattern match to get M' (which the code calls M).
    -- So after the match, the local M is actually the body.
    -- hM originally is: hasFreeVar (c + 1) (lam M) = false [where this M is the body]
    -- After simp [hasFreeVar], this becomes: hasFreeVar (c + 2) M = false [where M is body]
    --
    -- Ugh, Lean's naming is confusing here because the pattern reuses M.
    -- Let me trace through: we have the original term T = lam M' where M' is body.
    -- After pattern match `| lam M ih =>`, the local M IS M' (the body).
    -- hM constraint was on T = lam M, so hM : hasFreeVar (c + 1) (lam M) = false
    -- simp [hasFreeVar] at hM unfolds: hasFreeVar (c + 1) (lam M) = hasFreeVar (c + 2) M
    -- So hM becomes: hasFreeVar (c + 2) M = false, where M is the body.
    --
    -- For the IH, we need: hasFreeVar ((c+1) + 1) M = hasFreeVar (c + 2) M = false. ✓
    -- And we need: hasFreeVar (c + 1) (shift1 N) = false
    have hN' : hasFreeVar (c + 1) (shift1 N) = false := by
      unfold shift1
      exact hasFreeVar_shift1_gen N c 0 (Nat.zero_le c) hN
    -- Also need shift1 (shift (-1) c N) relates to shift (-1) (c+1) (shift1 N)
    have h_shift_comm : shift1 (shift (-1) c N) = shift (-1) (c + 1) (shift1 N) := by
      unfold shift1
      induction N generalizing c with
      | var m =>
        simp only [hasFreeVar] at hN
        have hm_nec : m ≠ c := beq_eq_false_iff_ne.mp hN
        simp only [shift]
        by_cases hm_ltc : m < c
        · -- m < c: shift (-1) c leaves it, shift 1 0 gives m + 1
          simp only [hm_ltc, ite_true, Nat.not_lt_zero, ite_false, Int.toNat_ofNat]
          -- LHS: shift 1 0 (var m) = var (m + 1) since m ≥ 0
          -- RHS: shift (-1) (c+1) (var (m + 1))
          -- m + 1 < c + 1 since m < c
          have hm1_ltc1 : m + 1 < c + 1 := by omega
          simp only [hm1_ltc1, ite_true]
        · -- m ≥ c and m ≠ c means m > c
          have hm_gtc : m > c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hm_ltc) (Ne.symm hm_nec)
          simp only [hm_ltc, ite_false]
          have heq1 : Int.toNat (↑m + (-1 : Int)) = m - 1 := by omega
          simp only [heq1]
          -- LHS: shift 1 0 (var (m - 1))
          have hm1_ge0 : ¬(m - 1 < 0) := by omega
          simp only [hm1_ge0, ite_false, Int.toNat_ofNat]
          have heq2 : m - 1 + 1 = m := by omega
          simp only [heq2]
          -- RHS: shift 1 0 (var m) = var (m + 1), then shift (-1) (c + 1) (var (m + 1))
          -- m + 1 > c + 1 since m > c
          have hm1_gec1 : ¬(m + 1 < c + 1) := by omega
          simp only [hm1_gec1, ite_false]
          have heq3 : Int.toNat (↑(m + 1) + (-1 : Int)) = m := by omega
          simp only [heq3]
      | app N₁ N₂ ih₁ ih₂ =>
        simp only [hasFreeVar, Bool.or_eq_false_iff] at hN
        simp only [shift, ih₁ c hN.1, ih₂ c hN.2]
      | lam N ih =>
        simp only [hasFreeVar] at hN
        simp only [shift]
        congr 1
        exact ih (c + 1) hN
    rw [h_shift_comm]
    exact ih (c + 1) (shift1 N) hM hN'

/-- β-reduction commutes with shift (-1) when var 0 is not free.
    This is the safe version of beta_shift for negative shifts. -/
theorem beta_shift_neg1_safe {P P' : Term} (hβ : P →β P') (hP : hasFreeVar 0 P = false) :
    shift (-1) 0 P →β shift (-1) 0 P' := by
  induction hβ generalizing with
  | beta M N =>
    -- P = app (lam M) N, P' = M[N]
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hP
    have hM : hasFreeVar 1 M = false := hP.1
    have hN : hasFreeVar 0 N = false := hP.2
    simp only [shift]
    -- Use the commutation lemma
    have hcomm := shift_neg1_subst0_comm_gen M N 0 hM hN
    simp only [Nat.zero_add] at hcomm
    rw [← hcomm]
    exact BetaStep.beta _ _
  | appL hM ih =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hP
    simp only [shift]
    exact BetaStep.appL (ih hP.1)
  | appR hN ih =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hP
    simp only [shift]
    exact BetaStep.appR (ih hP.2)
  | lam hM ih =>
    simp only [hasFreeVar] at hP
    simp only [shift]
    exact BetaStep.lam (ih hP)

/-- Single β step after η: if a →β b and a →η c, then ∃d with b →η* d and c →β* d -/
theorem beta_eta_diamond {a b c : Term} (hβ : a →β b) (hη : a →η c) :
    ∃ d, (b →η* d) ∧ (c →* d) := by
  induction hβ generalizing c with
  | beta M N =>
    -- a = app (lam M) N, b = M[N]
    -- η can be in (lam M) or in N
    cases hη with
    | appL h_lam_eta =>
      -- lam M →η M'', so c = app M'' N
      cases h_lam_eta with
      | lam h_body_eta =>
        -- M →η M'', a = app (lam M) N, c = app (lam M'') N
        -- b = M[N], we need b →η* d and c →* d
        -- Take d = M''[N]
        -- b = M[N] →η* M''[N] by eta_subst
        -- c = app (lam M'') N →β M''[N]
        rename_i M''
        exact ⟨M''[N],
               eta_subst h_body_eta N,
               MultiStep.step (BetaStep.beta M'' N) (MultiStep.refl _)⟩
      | eta P hP =>
        -- This case means lam M = lam (app P (var 0)) and lam M →η shift (-1) 0 P
        -- But the pattern match is on `h_lam_eta : EtaStep (lam M) M''`
        -- and `eta` gives lam (app P (var 0)) →η shift (-1) 0 P
        -- So M = app P (var 0), and M'' = shift (-1) 0 P
        -- a = app (lam (app P (var 0))) N = app (lam M) N
        -- c = app (shift (-1) 0 P) N
        -- b = M[N] = (app P (var 0))[N] = app (P[shift1 N])[N→shifted] (var 0)[N] = app (subst 1 (shift1 N) P) N
        -- Hmm, this is more complex. Let me reconsider.
        -- Actually this case should match: lam M →η (shift (-1) 0 P) where M = app P (var 0)
        -- So h_lam_eta is eta step on (lam M).
        -- But we pattern matched on EtaStep.lam first, which is congruence under lam.
        -- The EtaStep.eta case for (lam M) would require lam M = lam (app P (var 0))
        -- But EtaStep.eta produces lam (app P (var 0)) →η shift (-1) 0 P
        -- Wait, but we're pattern matching on h_lam_eta : EtaStep (lam M) ?
        -- Let me check the EtaStep definition again...
        -- EtaStep.eta : ∀ M, hasFreeVar 0 M = false → EtaStep (lam (app M (var 0))) (shift (-1) 0 M)
        -- So EtaStep.eta matches (lam (app M (var 0))), not (lam M) directly.
        -- Actually, the `lam M` in our beta case IS the whole term (lam <body>).
        -- If the body <body> = app P (var 0), then (lam (app P (var 0))) matches EtaStep.eta.
        -- So in this case, the original M from beta (i.e., <body>) = app P (var 0)
        -- and h_lam_eta : EtaStep (lam (app P (var 0))) (shift (-1) 0 P)
        -- Hmm, actually looking at the pattern match:
        -- `| appL h_lam_eta =>` followed by `cases h_lam_eta with | eta P hP =>`
        -- This means h_lam_eta : EtaStep (lam M) _
        -- and matching EtaStep.eta means (lam M) = lam (app P (var 0))
        -- No wait, EtaStep.eta has shape: EtaStep (lam (app M (var 0))) (shift (-1) 0 M)
        -- So if h_lam_eta is EtaStep.eta, then the term being stepped is lam (app P (var 0))
        -- But our term is (lam M) where M is the body in the beta redex.
        -- For EtaStep.eta to match, we need (lam M) = lam (app P (var 0)), i.e., M = app P (var 0)
        -- But M here is from BetaStep.beta M N, so M is the body of the lambda in the beta redex.
        -- So we have: a = app (lam (app P (var 0))) N (where the body is app P (var 0))
        --             b = (app P (var 0))[N] = app (subst 1 (shift1 N) P) (subst 1 (shift1 N) (var 0))
        --               = app (subst 1 (shift1 N) P) N  [since subst 1 _ (var 0) = var 0 when 0 < 1]
        --               Wait no: subst 0 N (app P (var 0)) = app (subst 0 N P) (subst 0 N (var 0))
        --               = app (subst 0 N P) N
        -- Actually I had the indices wrong. Let me be careful:
        -- M[N] = subst 0 N M where M = app P (var 0)
        -- subst 0 N (app P (var 0)) = app (subst 0 N P) (subst 0 N (var 0))
        -- subst 0 N (var 0) = N (since 0 = 0)
        -- So b = app (subst 0 N P) N = app (P[N]) N
        -- But wait, P appears inside (lam (app P (var 0))), so when we substitute at 0,
        -- we're substituting for the variable bound by the (lam ...).
        -- Let me reconsider. In a = app (lam (app P (var 0))) N:
        -- - The outer lambda binds variable 0
        -- - P is a subterm where var 0 doesn't appear free (from hP)
        -- - (var 0) in (app P (var 0)) refers to the bound variable
        -- After β-reduction: (lam (app P (var 0))) N →β (app P (var 0))[N]
        -- (app P (var 0))[N] = subst0 N (app P (var 0)) = app (subst0 N P) (subst0 N (var 0))
        --                   = app (P[N]) N  [since (var 0)[N] = N]
        -- Wait, but P has hasFreeVar 0 P = false inside the lambda body.
        -- Since P is inside lam, its free variables are shifted. When we substitute at 0,
        -- if P has no free var 0 (the bound variable), then P[N] = P (modulo shifting).
        -- Actually no, subst 0 N P doesn't necessarily equal P even if hasFreeVar 0 P = false.
        -- subst 0 N P: var 0 → N, var n (n > 0) → var (n-1)
        -- So it decrements all vars > 0 regardless of N.
        --
        -- OK let me just work out what we need:
        -- b = app (P[N]) N where P[N] = subst 0 N P
        -- c = app (shift (-1) 0 P) N
        -- We need d such that b →η* d and c →* d
        -- Since hasFreeVar 0 P = false, we have subst 0 N P = shift (-1) 1 P (by some lemma... wait)
        -- No, that's not quite right either.
        --
        -- Actually, let's use a different approach. Note that:
        -- subst 0 N P when hasFreeVar 0 P = false:
        --   - var 0 doesn't appear (by hP), so var 0 → N never fires
        --   - var n (n > 0) → var (n-1)
        -- shift (-1) 0 P when hasFreeVar 0 P = false:
        --   - var n (n < 0) → var n (never happens)
        --   - var n (n ≥ 0) → var (n-1) when n > 0, but var 0 → var (0-1) = var 0 (Int.toNat of -1 is 0)
        --
        -- Hmm, the shift and subst are different at var 0:
        -- - subst 0 N at var 0: gives N
        -- - shift (-1) 0 at var 0: gives var 0 (since Int.toNat(-1) = 0)
        -- But since hasFreeVar 0 P = false, neither case fires!
        --
        -- Actually wait, looking at hasFreeVar definition:
        -- hasFreeVar 0 P = false means in P, var 0 is not free.
        -- So in the substitution case, var 0 → N would give N, but var 0 doesn't occur.
        -- And in the shift case, var 0 → var (Int.toNat(0-1)) = var 0, but var 0 doesn't occur.
        --
        -- For var n where n > 0:
        -- - subst 0 N: var n → var (n-1)
        -- - shift (-1) 0: var n (n ≥ 0, so n > 0 means n ≥ 1): var n → var (n-1) (since Int.toNat(n-1) = n-1 for n ≥ 1)
        --
        -- So for n > 0, both give var (n-1). For n = 0, both don't apply (since var 0 not free).
        -- Thus subst 0 N P = shift (-1) 0 P when hasFreeVar 0 P = false!
        --
        -- Wait, that's not quite right. The recursion is different for lam:
        -- - subst 0 N (lam Q) = lam (subst 1 (shift1 N) Q)
        -- - shift (-1) 0 (lam Q) = lam (shift (-1) 1 Q)
        --
        -- These are different unless shift1 N at index 1 matches shift (-1) 1.
        -- Let's prove: subst 0 N P = shift (-1) 0 P when hasFreeVar 0 P = false
        -- This would be a very useful lemma!
        --
        -- Wait, no. Consider P = var 1:
        -- - subst 0 N (var 1) = var 0 (since 1 > 0)
        -- - shift (-1) 0 (var 1) = var 0 (since Int.toNat(1 + (-1)) = 0)
        -- These are equal!
        --
        -- Consider P = lam (var 1):
        -- - subst 0 N (lam (var 1)) = lam (subst 1 (shift1 N) (var 1)) = lam (shift1 N) (since 1 = 1)
        -- - shift (-1) 0 (lam (var 1)) = lam (shift (-1) 1 (var 1)) = lam (var 0) (since Int.toNat(0) = 0)
        -- These are different! subst gives lam (shift1 N) but shift gives lam (var 0).
        --
        -- So the lemma subst 0 N P = shift (-1) 0 P when hasFreeVar 0 P = false is FALSE.
        --
        -- OK so I need a different approach for this case. Let me think again...
        --
        -- We have:
        -- b = app (subst 0 N P) N
        -- c = app (shift (-1) 0 P) N
        --
        -- Take d = app (shift (-1) 0 P) N = c
        -- Then c →* d is trivial (refl).
        -- We need b →η* d, i.e., app (subst 0 N P) N →η* app (shift (-1) 0 P) N
        --
        -- So we need subst 0 N P →η* shift (-1) 0 P (and use appL_multi).
        --
        -- Hmm, is this true? Does substituting reduce to shifting?
        -- Not in general... Let me think of a concrete example.
        --
        -- P = var 1 (so hasFreeVar 0 (var 1) = false since 1 ≠ 0)
        -- subst 0 N (var 1) = var 0
        -- shift (-1) 0 (var 1) = var 0
        -- So var 0 →η* var 0 ✓
        --
        -- P = lam (var 2) (so hasFreeVar 0 (lam (var 2)) = hasFreeVar 1 (var 2) = (2 == 1) = false)
        -- subst 0 N (lam (var 2)) = lam (subst 1 (shift1 N) (var 2))
        --                         = lam (var 1) (since 2 > 1, so var 2 → var (2-1) = var 1)
        -- shift (-1) 0 (lam (var 2)) = lam (shift (-1) 1 (var 2))
        --                            = lam (var 1) (since 2 ≥ 1, so var 2 → var (2-1) = var 1)
        -- So lam (var 1) →η* lam (var 1) ✓
        --
        -- P = lam (var 1) (hasFreeVar 0 (lam (var 1)) = hasFreeVar 1 (var 1) = (1 == 1) = true)
        -- This violates hasFreeVar 0 P = false, so this case doesn't apply.
        --
        -- Hmm, let me think about this more carefully...
        -- When hasFreeVar 0 P = false:
        -- - If P = var n, then n ≠ 0, so n > 0. Both subst 0 N and shift (-1) 0 give var (n-1).
        -- - If P = app P1 P2, both recurse and should be equal by IH.
        -- - If P = lam Q, then hasFreeVar 0 (lam Q) = hasFreeVar 1 Q = false.
        --   subst 0 N (lam Q) = lam (subst 1 (shift1 N) Q)
        --   shift (-1) 0 (lam Q) = lam (shift (-1) 1 Q)
        --   Need: subst 1 (shift1 N) Q = shift (-1) 1 Q when hasFreeVar 1 Q = false
        --   By generalization, subst j (shift j 0 N') Q = shift (-1) j Q when hasFreeVar j Q = false?
        --   No, this doesn't seem right dimensionally...
        --
        -- Actually, let me prove the simpler claim: when hasFreeVar 0 P = false,
        -- subst 0 N P = shift (-1) 0 P for ANY N.
        --
        -- Wait, I showed a counterexample: P = lam (var 1) with hasFreeVar 1 (var 1) = true.
        -- But hasFreeVar 0 (lam (var 1)) = hasFreeVar 1 (var 1) = true, so this P doesn't satisfy hasFreeVar 0 P = false.
        --
        -- So actually P = lam Q requires hasFreeVar 1 Q = false for the outer hasFreeVar 0 (lam Q) = false.
        -- In that case:
        -- - subst 0 N (lam Q) = lam (subst 1 (shift1 N) Q)
        -- - shift (-1) 0 (lam Q) = lam (shift (-1) 1 Q)
        -- Need: subst 1 (shift1 N) Q = shift (-1) 1 Q when hasFreeVar 1 Q = false
        --
        -- For var n in Q with hasFreeVar 1 Q = false (so n ≠ 1):
        -- - If n = 0: subst 1 (shift1 N) (var 0) = var 0 (since 0 ≠ 1 and 0 < 1)
        --            shift (-1) 1 (var 0) = var 0 (since 0 < 1)
        --            Equal! ✓
        -- - If n > 1 (n ≥ 2): subst 1 (shift1 N) (var n) = var (n-1) (since n > 1)
        --                     shift (-1) 1 (var n) = var (n-1) (since n ≥ 1)
        --                     Equal! ✓
        --
        -- For app, straightforward by IH.
        -- For lam Q' with hasFreeVar 1 (lam Q') = hasFreeVar 2 Q' = false:
        -- - subst 1 (shift1 N) (lam Q') = lam (subst 2 (shift1 (shift1 N)) Q')
        -- - shift (-1) 1 (lam Q') = lam (shift (-1) 2 Q')
        -- Need: subst 2 (shift1 (shift1 N)) Q' = shift (-1) 2 Q' when hasFreeVar 2 Q' = false
        --
        -- This suggests the general lemma:
        -- subst j (shift j 0 N) Q = shift (-1) j Q when hasFreeVar j Q = false
        --
        -- Wait, but in the recursion: subst 1 (shift1 N) Q, and we need to compare with shift (-1) 1 Q.
        -- The N in shift1 N is just some arbitrary term. If we're claiming this equals shift (-1) 1 Q,
        -- then the N shouldn't matter (since it's never substituted because hasFreeVar 1 Q = false).
        --
        -- Let me prove: when hasFreeVar j P = false, subst j N P = shift (-1) j P for any N.
        --
        -- Hmm actually that's a strong claim. Let me verify for lam:
        -- P = lam Q, hasFreeVar j (lam Q) = hasFreeVar (j+1) Q = false
        -- subst j N (lam Q) = lam (subst (j+1) (shift1 N) Q)
        -- shift (-1) j (lam Q) = lam (shift (-1) (j+1) Q)
        -- Need: subst (j+1) (shift1 N) Q = shift (-1) (j+1) Q when hasFreeVar (j+1) Q = false
        --
        -- This is exactly the generalized claim! So by induction, it should hold.
        --
        -- LEMMA: hasFreeVar j P = false → subst j N P = shift (-1) j P (for any N)
        --
        -- Let me add this lemma and use it.
        --
        -- Actually, I realize this is close to but not quite the same as subst_var_eq_shift_neg1.
        -- That lemma says subst j (var j) M = shift (-1) (j+1) M.
        -- But what I want is: hasFreeVar j P = false → subst j N P = shift (-1) j P.
        --
        -- Wait no, those have different cutoffs for shift! One is j+1, one is j.
        -- Let me re-examine...
        --
        -- OK I think I've been confusing myself. Let me just prove the needed lemma.

        -- For this case: M = app P (var 0), hasFreeVar 0 P = false
        -- b = (app P (var 0))[N] = app (subst 0 N P) (subst 0 N (var 0)) = app (P') N where P' = subst 0 N P
        -- c = app (shift (-1) 0 P) N
        -- We need: ∃d, app P' N →η* d ∧ app (shift (-1) 0 P) N →* d
        --
        -- Key insight: when hasFreeVar 0 P = false:
        --   subst 0 N P = shift (-1) 0 P (need to prove this!)
        --
        -- If this holds, then b = app (shift (-1) 0 P) N = c, and we can take d = c.
        --
        -- Let me prove: hasFreeVar k P = false → subst k N P = shift (-1) (k+1) P
        -- Wait, I need to be careful about the cutoff.
        --
        -- Actually, let me think again about what subst and shift do:
        -- subst k N: var k → N, var n (n > k) → var (n-1), var n (n < k) → var n
        -- shift (-1) (k+1): var n (n < k+1) → var n, var n (n ≥ k+1) → var (n-1)
        --
        -- For var n:
        -- - n < k: subst gives var n, shift gives var n (since n < k+1) ✓
        -- - n = k: subst gives N, shift gives var k (since k < k+1)
        --   These differ unless hasFreeVar k P = false (so n = k never occurs)
        -- - n > k (n ≥ k+1): subst gives var (n-1), shift gives var (n-1) ✓
        --
        -- So with hasFreeVar k P = false, we avoid the n = k case, and get equality!
        --
        -- But wait, for lam:
        -- subst k N (lam Q) = lam (subst (k+1) (shift1 N) Q)
        -- shift (-1) (k+1) (lam Q) = lam (shift (-1) (k+2) Q)
        -- Need: subst (k+1) (shift1 N) Q = shift (-1) (k+2) Q when hasFreeVar (k+1) Q = false
        --
        -- By the generalized claim with k' = k+1, this should hold.
        --
        -- So the lemma is: hasFreeVar k P = false → subst k N P = shift (-1) (k+1) P
        --
        -- Hmm but I need subst 0 N P = shift (-1) 0 P, not shift (-1) 1 P.
        --
        -- Let me reconsider what shift (-1) 0 does:
        -- shift (-1) 0: var n (n < 0) → var n (never), var n (n ≥ 0) → var (Int.toNat(n-1))
        -- For n = 0: var (Int.toNat(-1)) = var 0
        -- For n > 0: var (n-1)
        --
        -- And subst 0 N: var 0 → N, var n (n > 0) → var (n-1), var n (n < 0) → var n (never)
        --
        -- So for n > 0, both give var (n-1). ✓
        -- For n = 0: subst gives N, shift gives var 0. These differ unless var 0 doesn't occur!
        --
        -- With hasFreeVar 0 P = false, var 0 doesn't occur in P, so we never hit this case.
        --
        -- For lam:
        -- subst 0 N (lam Q) = lam (subst 1 (shift1 N) Q)
        -- shift (-1) 0 (lam Q) = lam (shift (-1) 1 Q)
        -- Need: subst 1 (shift1 N) Q = shift (-1) 1 Q when hasFreeVar 1 Q = false
        --
        -- For var n in Q:
        -- - n = 1: doesn't occur (hasFreeVar 1 Q = false)
        -- - n = 0: subst 1 (shift1 N) (var 0) = var 0 (since 0 ≠ 1 and 0 < 1)
        --          shift (-1) 1 (var 0) = var 0 (since 0 < 1) ✓
        -- - n > 1: subst 1 (shift1 N) (var n) = var (n-1) (since n > 1)
        --          shift (-1) 1 (var n) = var (n-1) (since n ≥ 1) ✓
        --
        -- So the claim holds at level 1. By induction on structure, it should hold generally.
        --
        -- OK so I need to prove: hasFreeVar k P = false → ∀N, subst k N P = shift (-1) (k+1) P
        -- No wait, I showed shift (-1) 0, not shift (-1) 1. Let me re-examine...
        --
        -- shift (-1) 0: cutoff is 0, so vars ≥ 0 get decremented (with Int.toNat)
        --   n = 0 → Int.toNat(0 + (-1)) = Int.toNat(-1) = 0
        --   n > 0 → Int.toNat(n + (-1)) = n - 1
        --
        -- subst 0 N: var 0 → N, var n (n > 0) → var (n-1)
        --
        -- These differ at n = 0! subst gives N, shift gives var 0.
        --
        -- BUT if hasFreeVar 0 P = false, var 0 doesn't appear in P, so both operations
        -- behave identically on P: they map var n (n > 0) to var (n-1).
        --
        -- For lam Q with hasFreeVar 0 (lam Q) = hasFreeVar 1 Q = false:
        -- subst 0 N (lam Q) = lam (subst 1 (shift1 N) Q)
        -- shift (-1) 0 (lam Q) = lam (shift (-1) 1 Q)
        --
        -- By the same analysis at level 1 (where hasFreeVar 1 Q = false):
        -- subst 1 (shift1 N) Q and shift (-1) 1 Q both map vars > 1 to vars - 1,
        -- and leave var 0 unchanged. They differ at var 1, but var 1 doesn't appear.
        --
        -- So subst 1 (shift1 N) Q = shift (-1) 1 Q when hasFreeVar 1 Q = false! ✓
        --
        -- Wait, I think the issue is with what happens inside nested lambdas...
        -- Let me trace through lam (lam Q') where hasFreeVar 2 Q' = false:
        -- subst 0 N (lam (lam Q')) = lam (subst 1 (shift1 N) (lam Q'))
        --                          = lam (lam (subst 2 (shift1 (shift1 N)) Q'))
        -- shift (-1) 0 (lam (lam Q')) = lam (shift (-1) 1 (lam Q'))
        --                              = lam (lam (shift (-1) 2 Q'))
        --
        -- Need: subst 2 (shift1 (shift1 N)) Q' = shift (-1) 2 Q' when hasFreeVar 2 Q' = false
        --
        -- At level 2:
        -- - var 0, var 1: kept as is by both (since 0, 1 < 2)
        -- - var 2: doesn't appear (hasFreeVar 2 Q' = false)
        -- - var n (n > 2): both give var (n-1)
        --
        -- So yes, they're equal! The claim holds.
        --
        -- LEMMA to prove: hasFreeVar k P = false → subst k N P = shift (-1) (k+1) P
        --
        -- Wait no, I keep confusing myself. Let me be super careful.
        --
        -- shift (-1) c at var n: if n < c then var n else var (n + (-1)).toNat = var (n-1) for n ≥ c, n ≥ 1
        -- For n = c ≥ 1: var (c-1)
        -- For n < c: var n
        --
        -- subst k N at var n: if n = k then N, if n > k then var (n-1), if n < k then var n
        --
        -- Comparing shift (-1) (k+1) and subst k N:
        -- - n < k: subst gives var n. shift: n < k < k+1, so gives var n. Equal! ✓
        -- - n = k: subst gives N. shift: k < k+1, so gives var k. Different unless k doesn't occur.
        -- - n > k (so n ≥ k+1): subst gives var (n-1). shift: n ≥ k+1, so gives var (n-1). Equal! ✓
        --
        -- So with hasFreeVar k P = false (so n = k doesn't occur), subst k N P = shift (-1) (k+1) P. ✓
        --
        -- But I need to verify this for lam too:
        -- subst k N (lam Q) = lam (subst (k+1) (shift1 N) Q)
        -- shift (-1) (k+1) (lam Q) = lam (shift (-1) (k+2) Q)
        --
        -- With hasFreeVar k (lam Q) = hasFreeVar (k+1) Q = false, by IH:
        -- subst (k+1) (shift1 N) Q = shift (-1) ((k+1)+1) Q = shift (-1) (k+2) Q ✓
        --
        -- Great, so the lemma is:
        -- hasFreeVar k P = false → subst k N P = shift (-1) (k+1) P
        --
        -- But wait, I need subst 0 N P = shift (-1) 0 P for this case, not shift (-1) 1 P!
        --
        -- Hmm, the cutoffs don't match. Let me reconsider...
        --
        -- Actually wait, I think my analysis of shift (-1) 0 was wrong. Let me redo it.
        --
        -- shift (-1) 0 at var n:
        -- if n < 0 then var n [never]
        -- else var ((n : Int) + (-1)).toNat
        --
        -- For n = 0: ((0 : Int) + (-1)).toNat = (-1).toNat = 0 (since Int.toNat of negative is 0)
        -- For n = 1: ((1 : Int) + (-1)).toNat = (0).toNat = 0
        -- For n = 2: ((2 : Int) + (-1)).toNat = (1).toNat = 1
        -- For n ≥ 1: ((n : Int) + (-1)).toNat = (n - 1).toNat = n - 1
        --
        -- Wait, for n = 1, we get var 0, not var 0. Let me re-check: (1 : Int) + (-1 : Int) = 0, toNat 0 = 0.
        -- So shift (-1) 0 (var 1) = var 0. ✓
        --
        -- For n = 0: (0 : Int) + (-1 : Int) = -1, toNat(-1) = 0.
        -- So shift (-1) 0 (var 0) = var 0. This is like the identity at var 0!
        --
        -- And subst 0 N (var 0) = N.
        --
        -- These differ! shift gives var 0, subst gives N.
        --
        -- With hasFreeVar 0 P = false, var 0 doesn't appear in P, so this difference doesn't manifest.
        -- For var n with n > 0: subst 0 N gives var (n-1), shift (-1) 0 gives var (n-1). Equal!
        --
        -- So subst 0 N P = shift (-1) 0 P when hasFreeVar 0 P = false. ✓ (NOT shift (-1) 1!)
        --
        -- But for lam:
        -- subst 0 N (lam Q) = lam (subst 1 (shift1 N) Q)
        -- shift (-1) 0 (lam Q) = lam (shift (-1) 1 Q)
        --
        -- With hasFreeVar 0 (lam Q) = hasFreeVar 1 Q = false, I need:
        -- subst 1 (shift1 N) Q = shift (-1) 1 Q
        --
        -- For var n in Q:
        -- - n = 0: subst 1 (shift1 N) (var 0) = var 0 (since 0 ≠ 1 and 0 < 1)
        --          shift (-1) 1 (var 0) = var 0 (since 0 < 1) ✓
        -- - n = 1: doesn't appear (hasFreeVar 1 Q = false)
        -- - n > 1: subst 1 (shift1 N) (var n) = var (n-1)
        --          shift (-1) 1 (var n) = var (n-1) ✓
        --
        -- For lam Q' in Q with hasFreeVar 1 (lam Q') = hasFreeVar 2 Q' = false:
        -- subst 1 (shift1 N) (lam Q') = lam (subst 2 (shift1 (shift1 N)) Q')
        -- shift (-1) 1 (lam Q') = lam (shift (-1) 2 Q')
        -- By IH (at k = 2), these are equal when hasFreeVar 2 Q' = false. ✓
        --
        -- OK so the general lemma is:
        -- hasFreeVar k P = false → subst k N P = shift (-1) k P
        --
        -- Wait, but I showed shift (-1) (k+1) earlier... Let me re-examine.
        --
        -- At the top level (k = 0):
        -- subst 0 N P = shift (-1) 0 P when hasFreeVar 0 P = false (I showed this above, not shift (-1) 1!)
        --
        -- After entering a lam (k = 1):
        -- subst 1 (shift1 N) Q = shift (-1) 1 Q when hasFreeVar 1 Q = false
        --
        -- After entering two lams (k = 2):
        -- subst 2 (shift2 N) Q = shift (-1) 2 Q when hasFreeVar 2 Q = false
        --
        -- So the pattern is: hasFreeVar k P = false → subst k _ P = shift (-1) k P
        -- NOT shift (-1) (k+1)!
        --
        -- Let me re-verify shift (-1) k at level k:
        -- shift (-1) k at var n:
        -- - n < k: var n
        -- - n ≥ k: var (n + (-1)).toNat = var (n-1) for n ≥ 1, and var 0 for n = 0
        -- For n = k ≥ 1: var (k-1)
        -- For n = k = 0: var 0
        -- For n > k: var (n-1)
        --
        -- subst k _ at var n:
        -- - n = k: gives the substituted term
        -- - n > k: var (n-1)
        -- - n < k: var n
        --
        -- For n > k: both give var (n-1) ✓
        -- For n < k: both give var n ✓
        -- For n = k: subst gives the substituted term, shift gives var (k-1) if k ≥ 1, or var 0 if k = 0.
        --
        -- With hasFreeVar k P = false, n = k doesn't occur, so they're equal!
        --
        -- OK so the lemma is: hasFreeVar k P = false → ∀N, subst k N P = shift (-1) k P
        --
        -- But wait, for the lam case the recursion uses shift1 N at index k+1...
        -- Let me trace through more carefully.
        --
        -- Original: subst k N P where hasFreeVar k P = false.
        -- In lam case: P = lam Q, hasFreeVar k (lam Q) = hasFreeVar (k+1) Q = false.
        -- subst k N (lam Q) = lam (subst (k+1) (shift1 N) Q)
        -- shift (-1) k (lam Q) = lam (shift (-1) (k+1) Q)
        --
        -- By the generalized claim with k' = k+1 and N' = shift1 N:
        -- hasFreeVar (k+1) Q = false → subst (k+1) N' Q = shift (-1) (k+1) Q
        --
        -- And we have hasFreeVar (k+1) Q = false, so:
        -- subst (k+1) (shift1 N) Q = shift (-1) (k+1) Q
        --
        -- So lam (subst (k+1) (shift1 N) Q) = lam (shift (-1) (k+1) Q) ✓
        --
        -- Great! The lemma holds: hasFreeVar k P = false → subst k N P = shift (-1) k P
        --
        -- Wait, but the recursion uses shift1 N, not just N. Does this matter?
        -- The claim is that the result is independent of N when hasFreeVar k P = false.
        -- Since var k never appears in P, the substituted term N is never used.
        -- So the result is purely determined by the structure of P and the "decrementing" behavior
        -- of subst on indices > k.
        --
        -- Actually, let me verify this is TRUE by checking the var case again:
        -- subst k N (var n) where hasFreeVar k (var n) = (n == k) = false, so n ≠ k.
        -- - n < k: subst gives var n. shift (-1) k gives var n (since n < k). ✓
        -- - n > k: subst gives var (n-1). shift (-1) k: n ≥ k and n > k ≥ 0 so n ≥ 1,
        --          gives var (n + (-1)).toNat = var (n-1). ✓
        --
        -- The N is never used since n ≠ k! So yes, the claim holds regardless of N.
        --
        -- OK great, so I need to add the lemma:
        -- subst_eq_shift_neg1_of_noFreeVar : hasFreeVar k P = false → subst k N P = shift (-1) k P
        --
        -- Using this lemma in the current case:
        -- b = app (subst 0 N P) N = app (shift (-1) 0 P) N = c
        -- So we can take d = c, and both b →η* d and c →* d are trivial (refl).

        -- M = app P (var 0), hasFreeVar 0 P = false
        -- b = (app P (var 0))[N] = app (subst 0 N P) N
        -- c = app (shift (-1) 0 P) N
        -- By subst_eq_shift_neg1_of_noFreeVar: subst 0 N P = shift (-1) 0 P
        -- So b = c, and we can take d = app (shift (-1) 0 P) N
        have h_eq : subst 0 N P = shift (-1) 0 P := subst_eq_shift_neg1_of_noFreeVar P 0 N hP
        simp only [subst0, subst, h_eq]
        exact ⟨app (shift (-1) 0 P) N, Rewriting.Star.refl _, MultiStep.refl _⟩
    | appR h_arg_eta =>
      -- N →η N', c = app (lam M) N'
      -- a = app (lam M) N, b = M[N]
      -- We need d such that b →η* d and c →* d
      -- Take d = M[N']: b = M[N] →η* M[N'] by eta_subst_arg, c = app (lam M) N' →β M[N']
      exact ⟨M[N'],
             eta_subst_arg h_arg_eta M,
             MultiStep.step (BetaStep.beta M N') (MultiStep.refl _)⟩
  | appL h_func_step ih =>
    -- a = app M N, M →β M', b = app M' N
    -- η can be in M or N
    cases hη with
    | appL h_eta_func =>
      -- M →η M'', c = app M'' N
      have ⟨d, hd1, hd2⟩ := ih _ h_eta_func
      exact ⟨app d N, appL_multi hd1, MultiStep.appL hd2⟩
    | appR h_eta_arg =>
      -- N →η N', c = app M N'
      -- b = app M' N, c = app M N'
      -- Take d = app M' N'
      exact ⟨app _ _,
             Rewriting.Star.tail (Rewriting.Star.refl _) (EtaStep.appR h_eta_arg),
             MultiStep.step (BetaStep.appL h_func_step) (MultiStep.refl _)⟩
  | appR h_arg_step ih =>
    -- a = app M N, N →β N', b = app M N'
    cases hη with
    | appL h_eta_func =>
      -- M →η M', c = app M' N
      exact ⟨app _ _,
             Rewriting.Star.tail (Rewriting.Star.refl _) (EtaStep.appL h_eta_func),
             MultiStep.step (BetaStep.appR h_arg_step) (MultiStep.refl _)⟩
    | appR h_eta_arg =>
      -- N →η N'', c = app M N''
      have ⟨d, hd1, hd2⟩ := ih _ h_eta_arg
      exact ⟨app _ d, appR_multi hd1, MultiStep.appR hd2⟩
  | lam h_body_step ih =>
    -- a = lam M, M →β M', b = lam M'
    cases hη with
    | eta P hP =>
      -- a = lam (app P (var 0)), c = shift (-1) 0 P, hasFreeVar 0 P = false
      -- Since a = lam M, we have M = app P (var 0)
      -- M →β M' means (app P (var 0)) →β M'
      -- Either P →β P' (appL) or it's a beta redex at root (P = lam Q)
      cases h_body_step with
      | appL h_P_step =>
        -- P →β P', M' = app P' (var 0)
        -- b = lam (app P' (var 0)), c = shift (-1) 0 P
        -- hasFreeVar 0 P' = false by beta_preserves_noFreeVar
        have hP' := beta_preserves_noFreeVar h_P_step 0 hP
        -- d = shift (-1) 0 P' works:
        -- b = lam (app P' (var 0)) →η shift (-1) 0 P' (eta rule)
        -- c = shift (-1) 0 P →β shift (-1) 0 P' (beta_shift_neg1_safe)
        exact ⟨shift (-1) 0 _,
               Rewriting.Star.tail (Rewriting.Star.refl _) (EtaStep.eta _ hP'),
               MultiStep.step (beta_shift_neg1_safe h_P_step hP) (MultiStep.refl _)⟩
      | appR h_var0_step =>
        -- (var 0) →β ?, impossible
        cases h_var0_step
      | beta M' N' =>
        -- P = lam M', (app (lam M') (var 0)) →β M'[var 0]
        -- a = lam (app (lam M') (var 0))
        -- b = lam (M'[var 0]) = lam (subst 0 (var 0) M')
        -- c = shift (-1) 0 (lam M') = lam (shift (-1) 1 M')
        -- By subst_var_eq_shift_neg1: subst 0 (var 0) M' = shift (-1) 1 M'
        -- So b = lam (shift (-1) 1 M') = c
        -- Take d = c = b
        have h_eq : subst 0 (var 0) M' = shift (-1) 1 M' := subst_var_eq_shift_neg1 M' 0
        simp only [subst0] at *
        rw [h_eq]
        exact ⟨c, Rewriting.Star.refl _, MultiStep.refl _⟩
    | lam h_inner_eta =>
      -- M →η M'', c = lam M''
      have ⟨d, hd1, hd2⟩ := ih _ h_inner_eta
      exact ⟨lam d, lam_multi hd1, MultiStep.lam hd2⟩

/-- Single η step after β: if a →η b and a →β c, then ∃d with b →β* d and c →η* d
    This is the reverse direction of beta_eta_diamond. -/
theorem eta_beta_diamond {a b c : Term} (hη : a →η b) (hβ : a →β c) :
    ∃ d, (b →* d) ∧ (c →η* d) := by
  -- Use beta_eta_diamond with arguments swapped
  obtain ⟨d, hbd, hcd⟩ := beta_eta_diamond hβ hη
  exact ⟨d, hcd, hbd⟩

/-- Lifting β steps from shifted terms: if shift (-1) 0 M →β N and hasFreeVar 0 M = false,
    then ∃ M', M →β M' and N = shift (-1) 0 M'. -/
theorem beta_lift_from_shift {M N : Term} (hβ : shift (-1) 0 M →β N) (hM : hasFreeVar 0 M = false) :
    ∃ M', (M →β M') ∧ (N = shift (-1) 0 M') := by
  -- The key insight: β redexes in shift (-1) 0 M correspond to β redexes in M
  -- because shift only adjusts indices, not the structure of terms.
  -- We prove this by induction on M, tracking where the β redex occurs.
  induction M generalizing N with
  | var n =>
    -- M = var n, shift (-1) 0 (var n) is still a var, can't β-reduce
    simp only [shift] at hβ
    by_cases h : n < 0
    · simp only [h, ite_true] at hβ; cases hβ
    · simp only [h, ite_false] at hβ; cases hβ
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hM
    simp only [shift] at hβ
    -- The β step could be at the root (if M₁ = lam _) or in M₁ or M₂
    cases hβ with
    | beta B A =>
      -- Root β: shift (-1) 0 M₁ = lam B, shift (-1) 0 M₂ = A
      -- So M₁ = lam B' for some B' with shift (-1) 1 B' = B
      cases M₁ with
      | lam B' =>
        simp only [shift] at *
        -- N = subst 0 A B = subst 0 (shift (-1) 0 M₂) (shift (-1) 1 B')
        -- M = app (lam B') M₂
        -- M →β subst 0 M₂ B'
        -- Need to show N = shift (-1) 0 (subst 0 M₂ B')
        -- This requires shift_neg1_subst0_comm
        have hB' : hasFreeVar 1 B' = false := hM.1
        have hM₂ : hasFreeVar 0 M₂ = false := hM.2
        use subst 0 M₂ B'
        constructor
        · exact BetaStep.beta B' M₂
        · -- Show subst 0 (shift (-1) 0 M₂) (shift (-1) 1 B') = shift (-1) 0 (subst 0 M₂ B')
          exact (shift_neg1_subst0_comm_gen B' M₂ 0 hB' hM₂).symm
      | var _ => simp only [shift] at *; contradiction
      | app _ _ => simp only [shift] at *; contradiction
    | appL hβ₁ =>
      -- β in left subterm
      obtain ⟨M₁', hM₁'step, hM₁'eq⟩ := ih₁ hβ₁ hM.1
      exact ⟨app M₁' M₂, BetaStep.appL hM₁'step, by simp only [shift, hM₁'eq]⟩
    | appR hβ₂ =>
      -- β in right subterm
      obtain ⟨M₂', hM₂'step, hM₂'eq⟩ := ih₂ hβ₂ hM.2
      exact ⟨app M₁ M₂', BetaStep.appR hM₂'step, by simp only [shift, hM₂'eq]⟩
  | lam M' ih =>
    simp only [hasFreeVar] at hM
    simp only [shift] at hβ
    cases hβ with
    | lam hβ' =>
      obtain ⟨M'', hM''step, hM''eq⟩ := ih hβ' hM
      exact ⟨lam M'', BetaStep.lam hM''step, by simp only [shift, hM''eq]⟩

/-- Sequential swap: η ; β can be reordered to β* ; η*.
    Given x' →η y and y →β z, we can find w with x' →β* w and w →η* z. -/
theorem eta_beta_seq_swap {x' y z : Term} (hη : x' →η y) (hβ : y →β z) :
    ∃ w, (x' →* w) ∧ (w →η* z) := by
  induction hη with
  | eta M hM =>
    -- x' = lam (app M (var 0)), y = shift (-1) 0 M, hasFreeVar 0 M = false
    -- y →β z, so shift (-1) 0 M →β z
    -- Lift the β step to M
    obtain ⟨M', hM'step, hz_eq⟩ := beta_lift_from_shift hβ hM
    -- M →β M'
    -- z = shift (-1) 0 M'
    -- hasFreeVar 0 M' = false (by beta_preserves_noFreeVar)
    have hM' : hasFreeVar 0 M' = false := beta_preserves_noFreeVar hM'step 0 hM
    -- x' = lam (app M (var 0)) →β lam (app M' (var 0)) →η shift (-1) 0 M' = z
    use shift (-1) 0 M'
    constructor
    · -- x' →* shift (-1) 0 M': x' →β lam (app M' (var 0)) →η shift (-1) 0 M'
      -- Actually we go: lam (app M (var 0)) →β lam (app M' (var 0))
      -- then lam (app M' (var 0)) →η shift (-1) 0 M'
      -- But we want x' →β* w, not mixed β and η.
      -- So w = lam (app M' (var 0)), and then w →η z
      exact MultiStep.step (BetaStep.lam (BetaStep.appL hM'step)) (MultiStep.refl _)
    · -- lam (app M' (var 0)) →η shift (-1) 0 M' = z
      rw [← hz_eq]
      exact Rewriting.Star.single (EtaStep.eta M' hM')
  | appL hη_inner ih =>
    -- x' = app P Q, P →η P', y = app P' Q
    -- y →β z: either β at root, in P', or in Q
    cases hβ with
    | beta B A =>
      -- y = app (lam B) A →β B[A], but y = app P' Q
      -- So P' = lam B, Q = A
      -- x' = app P Q where P →η lam B = P'
      -- Need to handle: does P →η lam B mean P = lam (app B' (var 0))?
      -- The η step P →η P' where P' = lam B could be:
      -- - root eta: P = lam (app B' (var 0)) →η shift (-1) 0 B' = lam B (impossible, shift doesn't give lam)
      -- - lam congruence: P = lam P_body, P_body →η B, P' = lam B
      cases hη_inner with
      | lam hη_body =>
        -- P = lam P_body, P_body →η B
        -- x' = app (lam P_body) Q →β P_body[Q] (root β)
        -- z = B[A] = B[Q]
        -- We need: x' →β* w and w →η* z
        -- x' = app (lam P_body) Q →β P_body[Q]
        -- z = B[Q] where P_body →η B
        -- By eta_subst: P_body[Q] →η* B[Q]
        use subst 0 Q P_body
        constructor
        · exact MultiStep.step (BetaStep.beta P_body Q) (MultiStep.refl _)
        · exact eta_subst hη_body Q
      | eta M hM =>
        -- P = lam (app M (var 0)) →η shift (-1) 0 M = lam B
        -- But shift (-1) 0 M = lam B would require M = lam M' (shifted)
        -- shift (-1) 0 M gives lam only if M = lam M' (which it can't generally be the same as lam B)
        -- Actually shift (-1) 0 doesn't change the term constructor, so if shift (-1) 0 M = lam B,
        -- then M must be lam M' for some M', and shift (-1) 0 (lam M') = lam (shift (-1) 1 M')
        -- So B = shift (-1) 1 M'
        cases M with
        | lam M' =>
          simp only [shift] at *
          -- M = lam M', so P = lam (app (lam M') (var 0))
          -- P →η shift (-1) 0 (lam M') = lam (shift (-1) 1 M') = lam B
          -- So B = shift (-1) 1 M'
          -- x' = app P Q = app (lam (app (lam M') (var 0))) Q
          -- z = B[Q] = (shift (-1) 1 M')[Q] = subst 0 Q (shift (-1) 1 M')
          -- We can: x' →β (app (lam M') (var 0))[Q] = app (lam (subst 1 (shift 1 0 Q) M')) Q
          -- Then this →β (subst 1 (shift 1 0 Q) M')[Q] = subst 0 Q (subst 1 (shift 1 0 Q) M')
          -- This is getting complicated. Let me use a different approach.
          -- Use eta_beta_diamond in a different way.
          -- We have P →η lam B and app (lam B) Q →β B[Q]
          -- Actually, let me just use the IH approach differently.
          --
          -- x' = app (lam (app (lam M') (var 0))) Q
          -- This can β-reduce in multiple ways. Let me just go directly.
          -- x' →β (app (lam M') (var 0))[Q] = app (lam (subst 1 (shift 1 0 Q) M')) Q
          -- (simplifying: the (var 0) becomes Q, and M' gets adjusted)
          -- Actually subst 0 Q (app (lam M') (var 0)) = app (lam (subst 1 (shift 1 0 Q) M')) Q
          -- Wait no, subst 0 Q (app (lam M') (var 0)) = app (subst 0 Q (lam M')) (subst 0 Q (var 0))
          --                                           = app (lam (subst 1 (shift 1 0 Q) M')) Q
          -- Now this can →β (subst 1 (shift 1 0 Q) M')[Q] = subst 0 Q (subst 1 (shift 1 0 Q) M')
          --
          -- Meanwhile z = (shift (-1) 1 M')[Q] = subst 0 Q (shift (-1) 1 M')
          --
          -- So we need to connect subst 0 Q (subst 1 (shift 1 0 Q) M') with subst 0 Q (shift (-1) 1 M')
          -- via η* steps.
          --
          -- This requires showing: subst 1 (shift 1 0 Q) M' →η* shift (-1) 1 M'
          -- when hasFreeVar 0 (lam M') = false, i.e., hasFreeVar 1 M' = false.
          --
          -- Actually, if hasFreeVar 1 M' = false, then:
          -- subst 1 (shift 1 0 Q) M' = shift (-1) 1 M' (by subst_eq_shift_neg1_of_noFreeVar generalized)
          --
          -- So x' →β app (lam ...) Q →β subst 0 Q (shift (-1) 1 M') = z
          -- That means we can take w = z, and x' →β* z (two β steps), and z →η* z (refl).

          have hM' : hasFreeVar 1 M' = false := by
            simp only [hasFreeVar, Bool.or_eq_false_iff] at hM
            exact hM.1
          -- subst 1 (shift 1 0 Q) M' = shift (-1) 1 M' when hasFreeVar 1 M' = false
          have h_eq : subst 1 (shift 1 0 Q) M' = shift (-1) 1 M' :=
            subst_eq_shift_neg1_of_noFreeVar M' 1 (shift 1 0 Q) hM'
          use z
          constructor
          · -- x' = app (lam (app (lam M') (var 0))) Q →β* z
            -- First: →β subst 0 Q (app (lam M') (var 0)) = app (lam (subst 1 (shift 1 0 Q) M')) Q
            -- Second: →β subst 0 Q (subst 1 (shift 1 0 Q) M')
            -- Using h_eq: = subst 0 Q (shift (-1) 1 M') = (shift (-1) 1 M')[Q] = B[Q] = z
            calc MultiStep (app (lam (app (lam M') (var 0))) Q) z :=
              MultiStep.step (BetaStep.beta (app (lam M') (var 0)) Q)
                (by simp only [subst0, subst, shift1, h_eq]
                    exact MultiStep.step (BetaStep.beta (shift (-1) 1 M') Q) (MultiStep.refl _))
          · exact Rewriting.Star.refl _
        | var _ =>
          simp only [hasFreeVar] at hM
          simp only [shift] at *
          -- shift (-1) 0 (var n) = lam B is impossible
          by_cases h : (0 : Nat) < 0 <;> simp [shift, h] at *
        | app _ _ =>
          simp only [shift] at *
          -- shift (-1) 0 (app ...) = lam B is impossible
          cases ‹lam _ = app _ _›
      | appL _ => cases ‹lam _ = app _ _›
      | appR _ => cases ‹lam _ = app _ _›
    | appL hβ_inner =>
      -- β in left subterm P'
      -- P →η P' and P' →β P''
      -- By IH: ∃ w, P →* w and w →η* P''
      obtain ⟨w', hw'β, hw'η⟩ := ih hβ_inner
      use app w' Q
      constructor
      · exact MultiStep.appL hw'β
      · exact appL_multi hw'η
    | appR hβ_Q =>
      -- β in right subterm Q
      -- x' = app P Q, y = app P' Q, z = app P' Q'
      -- where Q →β Q'
      -- Take w = app P Q'
      use app _ _
      constructor
      · exact MultiStep.step (BetaStep.appR hβ_Q) (MultiStep.refl _)
      · exact Rewriting.Star.single (EtaStep.appL hη_inner)
  | appR hη_Q ih =>
    -- Similar to appL
    cases hβ with
    | beta B A =>
      -- y = app (lam B) A →β B[A], but y = app P Q'
      -- This means P = lam B, but P didn't change (only Q changed)
      -- x' = app (lam B) Q, Q →η Q' = A
      -- z = B[A] = B[Q']
      -- x' →β B[Q], and B[Q] →η* B[Q'] by eta_subst_arg
      use subst 0 Q B
      constructor
      · exact MultiStep.step (BetaStep.beta B Q) (MultiStep.refl _)
      · exact eta_subst_arg hη_Q B
    | appL hβ_P =>
      -- β in P, Q →η Q'
      -- x' = app P Q, y = app P Q', z = app P' Q'
      use app P' Q
      constructor
      · exact MultiStep.step (BetaStep.appL hβ_P) (MultiStep.refl _)
      · exact Rewriting.Star.single (EtaStep.appR hη_Q)
    | appR hβ_Q' =>
      -- β in Q'
      -- Q →η Q' and Q' →β Q''
      obtain ⟨w', hw'β, hw'η⟩ := ih hβ_Q'
      use app P w'
      constructor
      · exact MultiStep.appR hw'β
      · exact appR_multi hw'η
  | lam hη_inner ih =>
    -- x' = lam P, P →η P', y = lam P'
    -- y →β z: must be lam congruence
    cases hβ with
    | lam hβ_inner =>
      obtain ⟨w', hw'β, hw'η⟩ := ih hβ_inner
      use lam w'
      constructor
      · exact MultiStep.lam hw'β
      · exact lam_multi hw'η

/-! ## Star-Star Commutation

The key lemma for βη-confluence: Star β and Star η commute.

We prove this in stages:
1. Single η commutes past β* (eta_step_beta_star)
2. Single β commutes past η* (beta_step_eta_star)
3. β* commutes with η* (commute_beta_eta_stars) -/

/-- Single η step commutes past Star β: η a b → β* a c → ∃ d, β* b d ∧ η* c d -/
theorem eta_step_beta_star {a b c : Term} (hη : a →η b) (hβ : a →* c) :
    ∃ d, (b →* d) ∧ (c →η* d) := by
  induction hβ generalizing b with
  | refl => exact ⟨b, MultiStep.refl _, Rewriting.Star.single hη⟩
  | step hβ_step hβ_rest ih =>
    -- hβ_step : a →β x
    -- hβ_rest : x →* c
    -- hη : a →η b
    -- Use beta_eta_diamond on the divergent pair
    obtain ⟨d', hbd', hxd'⟩ := beta_eta_diamond hβ_step hη
    -- hbd' : b →η* d'
    -- hxd' : x →* d'
    -- Now use IH on each η step in hbd' against the remaining β path
    -- Actually, we need to commute hβ_rest : x →* c with the η* from x
    -- But hxd' goes from x to d', not continuing from the original η target
    -- This approach needs refinement. Let me use a different strategy.
    --
    -- Alternative: for each step in hbd' : b →η* d', we need to track where x goes
    -- Since hxd' : x →* d', we have x and d' both reachable
    -- We need to show that c (reached from x via β*) can join with the η* path from b
    --
    -- Key insight: η* from b to d' and β* from x to d' meet at d'
    -- We need to extend this to β* from x to c
    --
    -- Use induction on hβ_rest with the η* path from d'
    -- For this we need: given η* y d' and β* y c, find e with η* c e and β* d' e
    -- That's exactly commute_eta_star_beta_star, which we're trying to prove!
    --
    -- Let me restructure: prove both directions together or use a different lemma order
    -- Actually, since we have beta_eta_diamond giving η* and β* outputs,
    -- we can iterate to get the full commutation.

    -- Strategy: induction on β* path, using eta_beta_diamond at each step
    -- eta_beta_diamond : η a b → β a c → ∃ d, β* b d ∧ η* c d

    -- First η step: a →η b, a →β x gives d₁ with b →* d₁ and x →η* d₁
    obtain ⟨d₁, hbd₁, hxd₁⟩ := eta_beta_diamond hη hβ_step

    -- Now we have x →* c (hβ_rest) and x →η* d₁ (hxd₁)
    -- We need to commute these. Induct on the η* path.
    -- For each η step in x →η* d₁, use eta_beta_diamond against each β step in x →* c
    -- This is complex. Let me use a helper.

    -- Helper: commute single η past remaining β*
    have h_aux : ∀ (y z w : Term), y →η* z → y →* w → ∃ e, z →* e ∧ w →η* e := by
      intro y z w hyz hyw
      induction hyz generalizing w with
      | refl => exact ⟨w, hyw, Rewriting.Star.refl _⟩
      | tail hyz' hy'z ih_inner =>
        -- hyz' : y →η* y' for some y'
        -- hy'z : y' →η z
        -- ih_inner : ∀ w, y →* w → ∃ e, y' →* e ∧ w →η* e
        obtain ⟨e', hy'e', hwe'⟩ := ih_inner hyw
        -- hy'e' : y' →* e'
        -- hwe' : w →η* e'
        -- Now commute hy'z : y' →η z with hy'e' : y' →* e'
        obtain ⟨e, hze, he'e⟩ := eta_step_beta_star hy'z hy'e'
        exact ⟨e, hze, Rewriting.Star.trans hwe' he'e⟩

    obtain ⟨e, hd₁e, hce⟩ := h_aux x d₁ c hxd₁ hβ_rest
    exact ⟨e, MultiStep.trans hbd₁ hd₁e, hce⟩
termination_by sizeOf hβ

/-- Single β step commutes past Star η: β a b → η* a c → ∃ d, η* b d ∧ β* c d -/
theorem beta_step_eta_star {a b c : Term} (hβ : a →β b) (hη : a →η* c) :
    ∃ d, (b →η* d) ∧ (c →* d) := by
  induction hη generalizing b with
  | refl => exact ⟨b, Rewriting.Star.refl _, MultiStep.refl _⟩
  | tail hη_rest hη_step ih =>
    -- hη_rest : a →η* x
    -- hη_step : x →η c
    -- hβ : a →β b
    obtain ⟨d', hbd', hxd'⟩ := ih hβ
    -- hbd' : b →η* d'
    -- hxd' : x →* d'
    -- Now commute hη_step : x →η c with hxd' : x →* d'
    obtain ⟨e, hce, hd'e⟩ := eta_step_beta_star hη_step hxd'
    -- hce : c →* e
    -- hd'e : d' →η* e
    exact ⟨e, Rewriting.Star.trans hbd' hd'e, hce⟩

/-- Star β commutes with Star η -/
theorem commute_beta_eta_stars {a b c : Term} (hβ : a →* b) (hη : a →η* c) :
    ∃ d, (b →η* d) ∧ (c →* d) := by
  induction hβ generalizing c with
  | refl => exact ⟨c, hη, MultiStep.refl _⟩
  | step hβ_step hβ_rest ih =>
    -- hβ_step : a →β x
    -- hβ_rest : x →* b
    -- hη : a →η* c
    obtain ⟨d', hxd', hcd'⟩ := beta_step_eta_star hβ_step hη
    -- hxd' : x →η* d'
    -- hcd' : c →* d'
    obtain ⟨e, hbe, hd'e⟩ := ih hxd'
    -- hbe : b →η* e
    -- hd'e : d' →* e
    exact ⟨e, hbe, MultiStep.trans hcd' hd'e⟩

/-- Decompose a βη* path into β* followed by η*.
    Any interleaved sequence of β and η steps can be reordered to β* ; η*
    by bubbling β steps to the front using the commutation property. -/
theorem betaeta_decompose {a b : Term} (h : a →βη* b) :
    ∃ m, (a →* m) ∧ (m →η* b) := by
  induction h with
  | refl => exact ⟨a, MultiStep.refl _, Rewriting.Star.refl _⟩
  | tail hab' hb'b ih =>
    obtain ⟨m, ham, hmb'⟩ := ih
    cases hb'b with
    | beta hβ =>
      -- b' →β b, need to commute past the η* from m to b'
      -- Use eta_step_beta_star: η b' ? and β* b' b gives commutation
      -- Actually we need the reverse: β b' b and η* m b' gives...
      -- We have hmb' : m →η* b' and hβ : b' →β b
      -- Use commute_beta_eta_stars in reverse:
      -- From b' →β b (single step) and m →η* b' (backwards!)
      -- We need: given m →η* b' and b' →β b, find n with m →* n and n →η* b
      -- That's exactly what eta_step_beta_star gives for single η,
      -- but we have η* here.
      --
      -- Key insight: use eta_step_beta_star on each η step
      -- For single β step after η*: m →η* b' and b' →β b
      -- We can iterate: for each step in m →η* b', commute β past it
      have h_comm : ∀ (x y z : Term), x →η* y → y →β z → ∃ w, x →* w ∧ w →η* z := by
        intro x y z hxy hyz
        induction hxy generalizing z with
        | refl =>
          -- y = x, so x →β z, trivially x →* z and z →η* z
          exact ⟨z, MultiStep.step hyz (MultiStep.refl _), Rewriting.Star.refl _⟩
        | tail hxy' hy'y ih_inner =>
          -- hxy' : x →η* x' (some intermediate)
          -- hy'y : x' →η y
          -- ih_inner : ∀ z, x' →β z → ∃ w, x →* w ∧ w →η* z
          -- We have y →β z (hyz) and x' →η y (hy'y)
          --
          -- Use eta_beta_seq_swap: x' →η y and y →β z gives w' with x' →β* w' and w' →η* z
          obtain ⟨w', hw'β, hw'η⟩ := eta_beta_seq_swap hy'y hyz
          -- hw'β : x' →* w'
          -- hw'η : w' →η* z
          --
          -- Now bubble the β* path hw'β through the earlier η* path hxy'
          -- For each β step in x' →* w', use ih_inner to get the result
          have h_bubble : ∀ (y' z' : Term), x →η* y' → y' →* z' → ∃ w, x →* w ∧ w →η* z' := by
            intro y' z' hxy'' hy'z'
            induction hy'z' generalizing with
            | refl => exact ⟨y', Rewriting.Star.refl _, hxy''⟩
            | step hβ' hrest ih' =>
              -- hy'z' = y' →β m' →* z'
              -- Need to bubble y' →β m' through x →η* y'
              -- Then recursively handle m' →* z'
              induction hxy'' generalizing with
              | refl =>
                -- x = y', so x →β m' →* z'
                -- Result: x →* z' (by hrest extended), z' →η* z' (refl)
                exact ⟨z', MultiStep.step hβ' hrest, Rewriting.Star.refl _⟩
              | tail hxm hmy' ih'' =>
                -- x →η* m'' →η y' and y' →β m'
                -- Use eta_beta_seq_swap on hmy' : m'' →η y' and hβ' : y' →β m'
                obtain ⟨w'', hw''β, hw''η⟩ := eta_beta_seq_swap hmy' hβ'
                -- hw''β : m'' →* w''
                -- hw''η : w'' →η* m'
                -- Recursively: x →η* m'' and m'' →* w'' gives x →* w₁ and w₁ →η* w''
                obtain ⟨w₁, hw₁β, hw₁η⟩ := ih'' hw''β
                -- Now: x →* w₁ →η* w'' →η* m' →* z'
                -- We need x →* ? and ? →η* z'
                -- Use ih' on w'' →η* m' and m' →* z'
                -- But ih' expects (x →η* y') which is different...
                -- Actually, we can use the outer recursion structure
                -- Let's compose: x →* w₁ (β*), w₁ →η* w'' (η*), w'' →η* m' (η*), m' →* z' (β*)
                -- Combine η*: w₁ →η* m' (via w'')
                have hw₁m' : w₁ →η* m' := Rewriting.Star.trans hw₁η hw''η
                -- Now use h_bubble recursively on w₁ →η* m' and m' →* z'
                -- But that's circular! We need well-founded recursion.
                -- Actually, the recursion is fine because hrest is smaller than hy'z'.
                -- Let's restructure to use termination properly.
                obtain ⟨final, hfinalβ, hfinalη⟩ := ih' hw₁m'
                exact ⟨final, MultiStep.trans hw₁β hfinalβ, hfinalη⟩
          exact h_bubble x' w' hxy' hw'β
      obtain ⟨n, han, hnb⟩ := h_comm m b' b hmb' hβ
      exact ⟨n, MultiStep.trans ham han, hnb⟩
    | eta hη =>
      -- b' →η b, just extend the η* part
      exact ⟨m, ham, Rewriting.Star.tail hmb' hη⟩

/-- βη-reduction is confluent.

    Proof: We use the fact that β and η are individually confluent and commute.
    Given βη* a b and βη* a c, we decompose each path into β* ; η* form,
    then use β-confluence, η-confluence, and star-star commutation to join. -/
theorem beta_eta_confluent : Rewriting.Confluent BetaEtaStep := by
  intro a b c hab hac
  -- Decompose both paths into β* ; η* form
  obtain ⟨b', hab', hb'b⟩ := betaeta_decompose hab
  obtain ⟨c', hac', hc'c⟩ := betaeta_decompose hac
  -- hab' : a →* b' (β*)
  -- hb'b : b' →η* b
  -- hac' : a →* c' (β*)
  -- hc'c : c' →η* c

  -- Use β-confluence to join b' and c'
  obtain ⟨m, hb'm, hc'm⟩ := confluence hab' hac'
  -- hb'm : b' →* m
  -- hc'm : c' →* m

  -- Use star-star commutation to push β* past η*
  -- For b side: b' →η* b and b' →* m, find d₁ with b →* d₁ and m →η* d₁
  obtain ⟨d₁, hbd₁, hmd₁⟩ := commute_beta_eta_stars hb'm hb'b
  -- hbd₁ : b →η* d₁
  -- hmd₁ : m →* d₁

  -- For c side: c' →η* c and c' →* m, find d₂ with c →* d₂ and m →η* d₂
  obtain ⟨d₂, hcd₂, hmd₂⟩ := commute_beta_eta_stars hc'm hc'c
  -- hcd₂ : c →η* d₂
  -- hmd₂ : m →* d₂

  -- Now join d₁ and d₂. Both are reachable from m:
  -- m →* d₁ (β*) and m →* d₂ (β*)
  -- Also m →η* d₁ and m →η* d₂
  -- Wait, that's wrong. Let me re-read.
  -- hmd₁ : m →* d₁ (β*)
  -- hmd₂ : m →* d₂ (β*)
  -- hbd₁ : b →η* d₁
  -- hcd₂ : c →η* d₂

  -- Use β-confluence to join d₁ and d₂
  obtain ⟨e, hd₁e, hd₂e⟩ := confluence hmd₁ hmd₂
  -- hd₁e : d₁ →* e
  -- hd₂e : d₂ →* e

  -- Final assembly: b →βη* e and c →βη* e
  -- b →η* d₁ →* e: convert to βη*
  have hbe : b →βη* e := Rewriting.Star.trans
    (BetaEtaMulti.of_eta_multi hbd₁) (BetaEtaMulti.of_beta_multi hd₁e)
  have hce : c →βη* e := Rewriting.Star.trans
    (BetaEtaMulti.of_eta_multi hcd₂) (BetaEtaMulti.of_beta_multi hd₂e)

  exact ⟨e, hbe, hce⟩

end Metatheory.Lambda
