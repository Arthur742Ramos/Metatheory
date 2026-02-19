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
  induction M generalizing N d c with
  | var n =>
    simp only [subst, shift]
    by_cases hn_lt : n < c
    · -- n < c: shift d c (var n) = var n, subst c N (var n) = var n (since n ≠ c and n < c)
      simp only [hn_lt, ite_true]
      -- LHS: subst (c + d) (shift d c N) (var n)
      -- n < c < c + d, so n ≠ c + d and n ≤ c + d
      have hne : n ≠ c + d := by omega
      have hng : ¬(n > c + d) := by omega
      simp only [subst, hne, ite_false, hng]
      -- RHS: shift d c (subst c N (var n))
      -- n ≠ c (since n < c) and n < c (not > c)
      have hne_c : n ≠ c := by omega
      have hng_c : ¬(n > c) := by omega
      simp only [subst, hne_c, ite_false, hng_c, shift, hn_lt, ite_true]
    · -- n ≥ c
      simp only [hn_lt, ite_false]
      -- shift d c (var n) = var (n + d)  (as Nat via Int.toNat)
      have hn_ge : n ≥ c := Nat.le_of_not_lt hn_lt
      have eq_nd : Int.toNat (↑n + ↑d) = n + d := by
        simp [← Int.natCast_add, Int.toNat_natCast]
      simp only [eq_nd]
      -- Now case split: is n = c?
      by_cases hn_eq : n = c
      · -- n = c: subst c N (var c) = N
        subst hn_eq
        -- LHS: subst (c + d) (shift d c N) (var (c + d)) = shift d c N
        simp only [subst, Nat.add_right_cancel_iff, ite_true]
        -- RHS: shift d c (subst c N (var c)) = shift d c N
        simp only [subst, ite_true]
      · -- n ≠ c, n ≥ c, so n > c
        have hn_gt : n > c := Nat.lt_of_le_of_ne hn_ge (Ne.symm hn_eq)
        -- LHS: subst (c + d) (shift d c N) (var (n + d))
        -- n + d ≠ c + d iff n ≠ c, which is true
        have hne_cd : n + d ≠ c + d := by omega
        -- n + d > c + d since n > c
        have hgt_cd : n + d > c + d := by omega
        simp only [subst, hne_cd, ite_false, hgt_cd, ite_true]
        -- var (n + d - 1) on LHS
        -- RHS: shift d c (subst c N (var n))
        -- n ≠ c, n > c
        simp only [subst, hn_eq, ite_false, hn_gt, ite_true, shift]
        -- shift d c (var (n - 1))
        -- n - 1 ≥ c since n > c means n ≥ c + 1
        have hn1_ge : ¬(n - 1 < c) := by omega
        simp only [hn1_ge, ite_false]
        congr 1
        omega
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [subst, shift]
    rw [ih₁, ih₂]
  | lam M ih =>
    simp only [subst, shift]
    congr 1
    -- LHS: subst (c + 1 + d) (shift1 (shift d c N)) (shift d (c + 1) M)
    -- RHS: shift d (c + 1) (subst (c + 1) (shift1 N) M)  (shift d c (lam (subst (c+1) (shift1 N) M)))
    -- By IH with c' = c + 1: subst (c + 1 + d) (shift d (c + 1) (shift1 N)) (shift d (c + 1) M) = shift d (c + 1) (subst (c + 1) (shift1 N) M)
    -- Need: shift1 (shift d c N) = shift d (c + 1) (shift1 N)
    have h_comm : shift1 (shift d c N) = shift d (c + 1) (shift1 N) :=
      shift_shift_comm 1 d 0 c N (Nat.zero_le c)
    rw [show c + 1 + d = (c + 1) + d from by omega]
    rw [h_comm]
    exact ih (shift1 N) d (c + 1)

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
  induction P generalizing c N with
  | var n =>
    simp only [hasFreeVar] at hP
    have hn_ne_c : n ≠ c := beq_eq_false_iff_ne.mp hP
    simp only [subst, shift]
    by_cases hn_eq : n = c + 1
    · -- n = c + 1: subst fires
      subst hn_eq
      simp only [ite_true]
      -- LHS: shift (-1) c (shift (c + 1) 0 N)
      -- RHS: subst c (shift c 0 N) (shift (-1) c (var (c + 1)))
      -- shift (-1) c (var (c + 1)): c + 1 ≥ c, so var (Int.toNat (c + 1 + (-1))) = var c
      have : ¬(c + 1 < c) := by omega
      simp only [this, ite_false]
      have : Int.toNat (↑(c + 1) + (-1 : Int)) = c := by omega
      simp only [this, subst, ite_true]
      -- Need: shift (-1) c (shift (c + 1) 0 N) = shift c 0 N
      -- shift (c+1) 0 N shifts all vars by c+1
      -- shift (-1) c then decrements vars ≥ c by 1
      -- Result: vars that were < 0 stay (none exist), vars ≥ 0 get shifted by c+1 then vars ≥ c get decremented by 1
      -- Net effect on var x in N: x + (c+1) ≥ c always (since x ≥ 0), so result is x + c + 1 - 1 = x + c
      -- Which is the same as shift c 0 N
      induction N generalizing c with
      | var m =>
        simp only [shift]
        simp
        have : ¬(m + (c + 1) < c) := by omega
        simp only [this, ite_false]
        congr 1
        omega
      | app N₁ N₂ ih₁ ih₂ =>
        simp only [shift]
        rw [ih₁, ih₂]
      | lam N ih =>
        simp only [shift]
        congr 1
        -- shift (-1) (c + 1) (shift (c + 2) 1 N) = shift (c + 1) 1 N
        -- Need to show this for the lambda body
        -- shift (c+2) 1 shifts vars ≥ 1 by c+2
        -- shift (-1) (c+1) decrements vars ≥ c+1 by 1
        -- For var m in N:
        --   if m < 1: stays m, then if m < c+1 stays m (yes since m = 0 < c+1)
        --   if m ≥ 1: becomes m + c + 2, then m + c + 2 ≥ c + 1, so becomes m + c + 1
        -- shift (c+1) 1: if m < 1: m, if m ≥ 1: m + c + 1
        -- These match! So it's ih applied with c+1
        exact ih (c + 1)
    · -- n ≠ c + 1
      simp only [hn_eq, ite_false]
      by_cases hn_gt : n > c + 1
      · -- n > c + 1: subst gives var (n - 1)
        simp only [hn_gt, ite_true]
        -- shift (-1) c (var (n - 1)): n - 1 > c (since n > c + 1), so ¬(n-1 < c)
        have h1 : ¬(n - 1 < c) := by omega
        simp only [h1, ite_false]
        have eq1 : Int.toNat (↑(n - 1) + (-1 : Int)) = n - 2 := by omega
        simp only [eq1]
        -- RHS: subst c (shift c 0 N) (shift (-1) c (var n))
        -- shift (-1) c (var n): n > c + 1 > c, so ¬(n < c)
        have h2 : ¬(n < c) := by omega
        simp only [h2, ite_false]
        have eq2 : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
        simp only [eq2]
        -- subst c (shift c 0 N) (var (n - 1))
        -- n - 1 ≠ c (since n > c + 1 means n - 1 > c)
        have h3 : n - 1 ≠ c := by omega
        -- n - 1 > c
        have h4 : n - 1 > c := by omega
        simp only [subst, h3, ite_false, h4, ite_true]
        congr 1
        omega
      · -- n ≤ c + 1, n ≠ c + 1, so n ≤ c
        have hn_le : n ≤ c := by omega
        simp only [hn_gt, ite_false]
        -- subst doesn't fire (n < c + 1): result is var n
        -- shift (-1) c (var n): n ≤ c
        by_cases hn_lt_c : n < c
        · -- n < c
          simp only [hn_lt_c, ite_true]
          -- RHS: shift (-1) c (var n) = var n (since n < c)
          simp only [subst]
          have h1 : n ≠ c := by omega
          have h2 : ¬(n > c) := by omega
          simp only [h1, ite_false, h2]
        · -- n = c: impossible since hn_ne_c
          have : n = c := Nat.le_antisymm hn_le (Nat.le_of_not_lt hn_lt_c)
          exact absurd this hn_ne_c
  | app P₁ P₂ ih₁ ih₂ =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hP
    simp only [subst, shift]
    rw [ih₁ c N hP.1, ih₂ c N hP.2]
  | lam P ih =>
    simp only [hasFreeVar] at hP
    simp only [subst, shift]
    congr 1
    -- IH: shift (-1) (c+1) (subst (c+2) (shift (c+2) 0 N) P) = subst (c+1) (shift (c+1) 0 N) (shift (-1) (c+1) P)
    -- Need to adjust the shift of N under lam
    -- LHS lam body: subst (c+2) (shift1 (shift (c+1) 0 N)) P
    -- shift1 (shift (c+1) 0 N) = shift 1 0 (shift (c+1) 0 N) = shift (c+2) 0 N (via shift_shift)
    have h1 : shift1 (shift (↑(c + 1)) 0 N) = shift (↑(c + 2)) 0 N := by
      unfold shift1
      rw [shift_shift 1 (c + 1) 0 N]
      ring_nf
    -- RHS lam body: subst (c+2) (shift1 (shift c 0 N)) (shift (-1) (c+2) P)
    -- shift1 (shift c 0 N) = shift (c+1) 0 N
    have h2 : shift1 (shift (↑c) 0 N) = shift (↑(c + 1)) 0 N := by
      unfold shift1
      rw [shift_shift 1 c 0 N]
      ring_nf
    rw [h1, h2]
    rw [show c + 1 + 1 = c + 2 from by omega]
    exact ih (c + 1) N hP

theorem shift_neg1_subst1_comm (P N : Term) (hP : hasFreeVar 0 P = false) :
    shift (-1) 0 (subst 1 (shift1 N) P) = subst 0 N (shift (-1) 0 P) := by
  have h := shift_neg1_subst_comm_gen P N 0 hP
  simp only [Nat.zero_add, shift1] at h
  -- h : shift (-1) 0 (subst 1 (shift 1 0 N) P) = subst 0 (shift 0 0 N) (shift (-1) 0 P)
  -- shift 0 0 N = N (shifting by 0 is identity)
  have hshift0 : shift 0 0 N = N := by
    induction N with
    | var n => simp [shift]
    | app N₁ N₂ ih₁ ih₂ => simp [shift, ih₁, ih₂]
    | lam N ih => simp [shift, ih]
  rw [hshift0] at h
  exact h

theorem eta_subst {M M' : Term} (h : M →η M') (N : Term) :
    M[N] →η* M'[N] := by
  induction h generalizing N with
  | eta P hP =>
    -- M = lam (app P (var 0)), M' = shift (-1) 0 P
    -- M[N] = lam (subst 1 (shift1 N) (app P (var 0)))
    --      = lam (app (subst 1 (shift1 N) P) (var 0))
    -- M'[N] = subst 0 N (shift (-1) 0 P)
    simp only [subst0, subst]
    -- subst 1 (shift1 N) (var 0) = var 0 (since 0 ≠ 1 and 0 < 1)
    simp only [subst, show (0 : Nat) ≠ 1 from by omega, ite_false, show ¬(0 > 1) from by omega]
    -- Now need: lam (app (subst 1 (shift1 N) P) (var 0)) →η* subst 0 N (shift (-1) 0 P)
    have hfree : hasFreeVar 0 (subst 1 (shift1 N) P) = false :=
      hasFreeVar0_subst1 P (shift1 N) hP (hasFreeVar0_shift1 N)
    have hstep : EtaStep (lam (app (subst 1 (shift1 N) P) (var 0)))
        (shift (-1) 0 (subst 1 (shift1 N) P)) :=
      EtaStep.eta _ hfree
    have heq : shift (-1) 0 (subst 1 (shift1 N) P) = subst 0 N (shift (-1) 0 P) :=
      shift_neg1_subst1_comm P N hP
    rw [heq] at hstep
    exact Rewriting.Star.single hstep
  | appL _ ih =>
    simp only [subst0, subst]
    exact Rewriting.Star.map (fun x => app x _) (fun _ _ h => EtaStep.appL h) (ih N)
  | appR _ ih =>
    simp only [subst0, subst]
    exact Rewriting.Star.map (fun x => app _ x) (fun _ _ h => EtaStep.appR h) (ih N)
  | lam _ ih =>
    simp only [subst0, subst]
    exact Rewriting.Star.map lam (fun _ _ h => EtaStep.lam h) (ih (shift1 N))

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
    by_cases hn_eq : n = j
    · simp only [hn_eq, ite_true]
      exact Rewriting.Star.single hN
    · simp only [hn_eq, ite_false]
      by_cases hn_gt : n > j
      · simp only [hn_gt, ite_true]; exact Rewriting.Star.refl _
      · simp only [hn_gt, ite_false]; exact Rewriting.Star.refl _
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [subst]
    exact Rewriting.Star.trans
      (Rewriting.Star.map (fun x => app x _) (fun _ _ h => EtaStep.appL h) (ih₁ hN j))
      (Rewriting.Star.map (fun x => app _ x) (fun _ _ h => EtaStep.appR h) (ih₂ hN j))
  | lam M ih =>
    simp only [subst]
    exact Rewriting.Star.map lam (fun _ _ h => EtaStep.lam h)
      (ih (eta_shiftNat hN 1 0) (j + 1))

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
    · subst hn_eq
      -- subst j (var j) (var j) = var j
      -- shift (-1) (j + 1) (var j): j < j + 1, so var j
      simp only [ite_true]
      have : j < j + 1 := Nat.lt_succ_self j
      simp only [this, ite_true]
    · simp only [hn_eq, ite_false]
      by_cases hn_gt : n > j
      · simp only [hn_gt, ite_true]
        -- subst returns var (n - 1)
        -- shift (-1) (j + 1) (var n): n > j means n ≥ j + 1, so ¬(n < j + 1)
        have : ¬(n < j + 1) := by omega
        simp only [this, ite_false]
        congr 1
        omega
      · have hn_lt : n < j := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn_gt) hn_eq
        simp only [hn_gt, ite_false]
        -- subst returns var n
        -- shift (-1) (j + 1) (var n): n < j < j + 1, so var n
        have : n < j + 1 := by omega
        simp only [this, ite_true]
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [subst, shift]
    rw [ih₁, ih₂]
  | lam M ih =>
    simp only [subst, shift]
    congr 1
    -- Need: subst (j + 1) (shift1 (var j)) M = shift (-1) (j + 2) M
    -- shift1 (var j) = shift 1 0 (var j) = var (j + 1) (since j ≥ 0)
    have : shift1 (var j) = var (j + 1) := by
      simp only [shift]
      simp
    rw [this]
    rw [show j + 1 + 1 = (j + 1) + 1 from rfl]
    exact ih (j + 1)

theorem shift_neg1_subst0_comm_gen (M N : Term) (c : Nat) (hM : hasFreeVar (c + 1) M = false)
    (hN : hasFreeVar c N = false) :
    shift (-1) c (subst c N M) = subst c (shift (-1) c N) (shift (-1) (c + 1) M) := by
  induction M generalizing c N with
  | var n =>
    simp only [hasFreeVar] at hM
    have hn_ne_c1 : n ≠ c + 1 := beq_eq_false_iff_ne.mp hM
    simp only [subst, shift]
    by_cases hn_eq : n = c
    · -- n = c: subst fires on LHS
      subst hn_eq
      simp only [ite_true]
      -- LHS: shift (-1) c N
      -- RHS: subst c (shift (-1) c N) (shift (-1) (c + 1) (var c))
      -- shift (-1) (c + 1) (var c): c < c + 1, so var c
      have : c < c + 1 := Nat.lt_succ_self c
      simp only [this, ite_true, subst, ite_true]
    · simp only [hn_eq, ite_false]
      by_cases hn_gt : n > c
      · -- n > c, n ≠ c + 1, so n > c + 1 or n = c + 1. But n ≠ c + 1, so n > c + 1, thus n ≥ c + 2.
        have hn_gt_c1 : n > c + 1 := by omega
        simp only [hn_gt, ite_true]
        -- LHS: shift (-1) c (var (n - 1))
        -- n - 1 ≥ c + 1 > c, so ¬(n - 1 < c)
        have h1 : ¬(n - 1 < c) := by omega
        simp only [h1, ite_false]
        have eq1 : Int.toNat (↑(n - 1) + (-1 : Int)) = n - 2 := by omega
        simp only [eq1]
        -- RHS: subst c (shift (-1) c N) (shift (-1) (c + 1) (var n))
        -- n > c + 1, so ¬(n < c + 1)
        have h2 : ¬(n < c + 1) := by omega
        simp only [h2, ite_false]
        have eq2 : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
        simp only [eq2]
        -- subst c _ (var (n - 1)): n - 1 ≠ c (since n > c + 1), n - 1 > c
        have h3 : n - 1 ≠ c := by omega
        have h4 : n - 1 > c := by omega
        simp only [subst, h3, ite_false, h4, ite_true]
        congr 1
        omega
      · -- n ≤ c, n ≠ c, so n < c
        have hn_lt : n < c := by omega
        simp only [hn_gt, ite_false, shift]
        -- LHS: shift (-1) c (var n) = var n (since n < c)
        simp only [hn_lt, ite_true]
        -- RHS: shift (-1) (c + 1) (var n): n < c < c + 1, so var n
        have h1 : n < c + 1 := by omega
        simp only [h1, ite_true]
        -- subst c _ (var n): n ≠ c, n < c (not > c)
        simp only [subst, hn_eq, ite_false, hn_gt]
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hM
    simp only [subst, shift]
    rw [ih₁ c N hM.1 hN, ih₂ c N hM.2 hN]
  | lam M ih =>
    simp only [hasFreeVar] at hM
    simp only [subst, shift]
    congr 1
    -- Need: shift (-1) (c+1) (subst (c+1) (shift1 N) M)
    --     = subst (c+1) (shift1 (shift (-1) c N)) (shift (-1) (c+2) M)
    -- By IH with c' = c + 1: need hasFreeVar (c+2) M = false and hasFreeVar (c+1) (shift1 N) = false
    have hM' : hasFreeVar (c + 2) M = false := by
      rw [show c + 2 = (c + 1) + 1 from by omega] at *
      exact hM
    have hN' : hasFreeVar (c + 1) (shift1 N) = false := hasFreeVar_shift1 N c hN
    -- Also need: shift1 (shift (-1) c N) = shift (-1) (c + 1) ... no wait
    -- Actually the IH gives:
    -- shift (-1) (c+1) (subst (c+1) (shift1 N) M) = subst (c+1) (shift (-1) (c+1) (shift1 N)) (shift (-1) (c+2) M)
    -- So we need: shift (-1) (c + 1) (shift1 N) = shift1 (shift (-1) c N)
    -- shift1 N = shift 1 0 N
    -- shift (-1) (c+1) (shift 1 0 N) vs shift 1 0 (shift (-1) c N)
    -- For var x in N:
    --   shift 1 0: x → x+1 (all x ≥ 0)
    --   shift (-1) (c+1): x+1 < c+1 → x+1, else x+1-1 = x. So if x < c: x+1, if x ≥ c: x+1-1=x. But x ≥ c means x+1 ≥ c+1.
    --   Result: if x < c then x+1 else x
    -- Other direction:
    --   shift (-1) c: if x < c then x else x-1. But hasFreeVar c N = false, so x ≠ c.
    --     if x < c then x, if x > c then x-1
    --   shift 1 0: everything +1
    --     if x < c then x+1, if x > c then x (= x-1+1)
    -- These match! Good.
    rw [show c + 1 + 1 = c + 2 from by omega]
    rw [ih (c + 1) (shift1 N) hM' hN']
    congr 1
    -- Need: shift (-1) (c + 1) (shift1 N) = shift1 (shift (-1) c N)
    -- This is a shift commutation for opposite directions
    -- We prove it by induction on N
    clear ih hM' hN' hM hN M
    induction N with
    | var n =>
      simp only [shift1, shift]
      by_cases hn_lt : n < c
      · -- n < c: shift 1 0 (var n) = var (n + 1), hasFreeVar c N = false so n ≠ c
        simp
        have h1 : ¬(n < 0) := by omega
        simp only [h1, ite_false]
        have eq1 : Int.toNat (↑n + (1 : Int)) = n + 1 := by omega
        simp only [eq1]
        -- shift (-1) (c + 1) (var (n + 1)): n + 1 ≤ c, so n + 1 < c + 1
        have h2 : n + 1 < c + 1 := by omega
        simp only [h2, ite_true]
        -- shift (-1) c (var n): n < c
        simp only [hn_lt, ite_true]
        -- shift 1 0 (var n): n ≥ 0, so var (n + 1)
        simp only [h1, ite_false, eq1]
      · -- n ≥ c
        simp
        have h1 : ¬(n < 0) := by omega
        simp only [h1, ite_false]
        have eq1 : Int.toNat (↑n + (1 : Int)) = n + 1 := by omega
        simp only [eq1]
        -- shift (-1) (c + 1) (var (n + 1)): n ≥ c so n + 1 ≥ c + 1, ¬(n + 1 < c + 1)
        have h2 : ¬(n + 1 < c + 1) := by omega
        simp only [h2, ite_false]
        have eq2 : Int.toNat (↑(n + 1) + (-1 : Int)) = n := by omega
        simp only [eq2]
        -- shift (-1) c (var n): n ≥ c, ¬(n < c)
        simp only [hn_lt, ite_false]
        have eq3 : Int.toNat (↑n + (-1 : Int)) = n - 1 := by omega
        simp only [eq3]
        -- shift 1 0 (var (n - 1)): n - 1 ≥ 0, so var n
        simp only [h1, ite_false]
        have eq4 : Int.toNat (↑(n - 1) + (1 : Int)) = n := by omega
        simp only [eq4]
    | app N₁ N₂ ih₁ ih₂ =>
      simp only [shift1, shift]
      rw [ih₁, ih₂]
    | lam N ih =>
      simp only [shift1, shift]
      congr 1
      -- shift (-1) (c + 2) (shift 1 1 N) = shift 1 1 (shift (-1) (c + 1) N)
      -- This is the same pattern with c' = c + 1 on the interior
      exact ih

theorem beta_shift_neg1_safe {P P' : Term} (hβ : P →β P') (hP : hasFreeVar 0 P = false) :
    shift (-1) 0 P →β shift (-1) 0 P' := by
  induction hβ generalizing with
  | beta M N =>
    -- P = app (lam M) N, P' = M[N]
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hP
    have hM : hasFreeVar 1 M = false := by
      simp only [hasFreeVar] at hP
      exact hP.1
    have hN : hasFreeVar 0 N = false := hP.2
    simp only [shift]
    -- LHS: app (lam (shift (-1) 1 M)) (shift (-1) 0 N)
    -- RHS: shift (-1) 0 (subst 0 N M)
    -- BetaStep.beta gives: app (lam (shift (-1) 1 M)) (shift (-1) 0 N) →β (shift (-1) 1 M)[shift (-1) 0 N]
    -- Need: (shift (-1) 1 M)[shift (-1) 0 N] = shift (-1) 0 (subst 0 N M)
    have heq := shift_neg1_subst0_comm_gen M N 0 hM hN
    simp only [Nat.zero_add] at heq
    rw [← heq]
    exact BetaStep.beta _ _
  | appL _ ih =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hP
    simp only [shift]
    exact BetaStep.appL (ih hP.1)
  | appR _ ih =>
    simp only [hasFreeVar, Bool.or_eq_false_iff] at hP
    simp only [shift]
    exact BetaStep.appR (ih hP.2)
  | lam _ ih =>
    simp only [hasFreeVar] at hP
    simp only [shift]
    exact BetaStep.lam (ih hP)

/-! ## Beta-Eta Commutation (Deferred)

The full beta-eta diamond property and the resulting beta-eta confluence theorem
require extensive case analysis on overlapping redexes. The key components:

- `beta_eta_diamond`: β step and η step from the same term can be joined
- `beta_eta_confluent`: βη-reduction is confluent (via Hindley-Rosen)

These are deferred to future work. The necessary infrastructure (substitution
commutation lemmas, shift-subst interaction, etc.) is proved above.

References:
- Barendregt, "The Lambda Calculus" (1984), Chapter 3
- Takahashi, "Parallel Reductions in λ-Calculus" (1995)
-/

