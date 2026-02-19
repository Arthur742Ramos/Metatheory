/-
# System F Subject Reduction

This module proves subject reduction (type preservation) for System F.

Subject reduction states that reduction preserves types:
if `k ; Γ ⊢ M : τ` and `M ⟶ N`, then `k ; Γ ⊢ N : τ`.

## References

- Pierce, "Types and Programming Languages" (2002), Chapter 23
- Girard, Lafont & Taylor, "Proofs and Types" (1989)
-/

import Metatheory.SystemF.Typing

/-! ## Axiom-Free List Lemmas

The standard library versions of these lemmas use propext. We prove axiom-free
versions by induction. -/

/-- Axiom-free version of List.length_map -/
theorem List.length_map_af {α β : Type _} (f : α → β) (l : List α) :
    (l.map f).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih => exact congrArg Nat.succ ih

/-- Axiom-free version of List.getElem?_map -/
theorem List.getElem?_map_af {α β : Type _} (f : α → β) (l : List α) (n : Nat) :
    (l.map f)[n]? = l[n]?.map f := by
  induction l generalizing n with
  | nil => rfl
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n' => exact ih n'

/-- Axiom-free version of List.getElem?_append_left -/
theorem List.getElem?_append_left_af {α : Type _} (l₁ l₂ : List α) {n : Nat} (hn : n < l₁.length) :
    (l₁ ++ l₂)[n]? = l₁[n]? := by
  induction l₁ generalizing n with
  | nil => exact absurd hn (Nat.not_lt_zero n)
  | cons a as ih =>
    cases n with
    | zero => rfl
    | succ n' =>
      have hn' : n' < as.length := Nat.lt_of_succ_lt_succ hn
      exact ih hn'

/-- Axiom-free version of List.getElem?_append_right -/
theorem List.getElem?_append_right_af {α : Type _} (l₁ l₂ : List α) (n : Nat) (hn : l₁.length ≤ n) :
    (l₁ ++ l₂)[n]? = l₂[n - l₁.length]? := by
  induction l₁ generalizing n with
  | nil => rfl
  | cons a as ih =>
    match n with
    | 0 => exact absurd hn (Nat.not_succ_le_zero as.length)
    | n' + 1 =>
      have hn' : as.length ≤ n' := Nat.le_of_succ_le_succ hn
      -- Goal: (a :: as ++ l₂)[n' + 1]? = l₂[n' + 1 - (a :: as).length]?
      -- LHS is definitionally (as ++ l₂)[n']?
      -- (a :: as).length = as.length + 1
      have hlen : (a :: as).length = as.length + 1 := rfl
      -- So RHS is l₂[(n' + 1) - (as.length + 1)]? = l₂[n' - as.length]?
      have h : (n' + 1) - (a :: as).length = n' - as.length := by
        rw [hlen, Nat.add_one n', Nat.add_one as.length, Nat.succ_sub_succ]
      rw [h]
      exact ih n' hn'

/-- Axiom-free combined version of List.getElem?_append -/
theorem List.getElem?_append_af {α : Type _} (l₁ l₂ : List α) (n : Nat) :
    (l₁ ++ l₂)[n]? = if n < l₁.length then l₁[n]? else l₂[n - l₁.length]? := by
  by_cases h : n < l₁.length
  · rw [if_pos h, List.getElem?_append_left_af l₁ l₂ h]
  · rw [if_neg h, List.getElem?_append_right_af l₁ l₂ n (Nat.not_lt.mp h)]

/-- Axiom-free version of List.map_append -/
theorem List.map_append_af {α β : Type _} {f : α → β} {l₁ l₂ : List α} :
    (l₁ ++ l₂).map f = l₁.map f ++ l₂.map f := by
  induction l₁ with
  | nil => rfl
  | cons a as ih => exact congrArg (f a :: ·) ih

/-- Axiom-free version of List.map_take -/
theorem List.map_take_af {α β : Type _} (f : α → β) (n : Nat) (l : List α) :
    (l.take n).map f = (l.map f).take n := by
  induction n generalizing l with
  | zero => rfl
  | succ n' ih =>
    cases l with
    | nil => rfl
    | cons a as => exact congrArg (f a :: ·) (ih as)

/-- Axiom-free version of List.map_drop -/
theorem List.map_drop_af {α β : Type _} (f : α → β) (n : Nat) (l : List α) :
    (l.drop n).map f = (l.map f).drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n' ih =>
    cases l with
    | nil => rfl
    | cons a as => exact ih as


/-- Axiom-free version of List.getElem?_take (without propext) -/
theorem List.getElem?_take_af {α : Type _} (l : List α) (n m : Nat) (hm : m < n) :
    (l.take n)[m]? = l[m]? := by
  induction n generalizing l m with
  | zero => exact absurd hm (Nat.not_lt_zero m)
  | succ n' ih =>
    cases l with
    | nil => rfl
    | cons a as =>
      cases m with
      | zero => rfl
      | succ m' =>
        have hm' : m' < n' := Nat.lt_of_succ_lt_succ hm
        exact ih as m' hm'

/-- Axiom-free version of List.getElem?_drop -/
theorem List.getElem?_drop_af {α : Type _} (l : List α) (n m : Nat) :
    (l.drop n)[m]? = l[n + m]? := by
  induction n generalizing l m with
  | zero =>
    -- Goal: (drop 0 l)[m]? = l[0 + m]?
    -- l.drop 0 = l definitionally, need 0 + m = m
    show l[m]? = l[0 + m]?
    rw [Nat.zero_add]
  | succ n' ih =>
    cases l with
    | nil => rfl
    | cons a as =>
      -- Goal: (as.drop n')[m]? = (a :: as)[n'.succ + m]?
      -- IH: (as.drop n')[m]? = as[n' + m]?
      -- n'.succ + m = (n' + m).succ by Nat.succ_add
      rw [Nat.succ_add]
      exact ih as m

/-- Axiom-free version of List.map_map -/
theorem List.map_map_af {α β γ : Type _} (f : α → β) (g : β → γ) (l : List α) :
    (l.map f).map g = l.map (g ∘ f) := by
  induction l with
  | nil => rfl
  | cons a as ih => exact congrArg (g (f a) :: ·) ih

/-- Axiom-free version of List.map_id -/
theorem List.map_id_af {α : Type _} (l : List α) : l.map id = l := by
  induction l with
  | nil => rfl
  | cons a as ih => exact congrArg (a :: ·) ih

/-- Axiom-free version of List.length_take_of_le_af -/
theorem List.length_take_of_le_af {α : Type _} {n : Nat} {l : List α} (h : n ≤ l.length) :
    (l.take n).length = n := by
  induction n generalizing l with
  | zero => rfl
  | succ n' ih =>
    cases l with
    | nil => exact absurd h (Nat.not_succ_le_zero n')
    | cons a as =>
      have h' : n' ≤ as.length := Nat.le_of_succ_le_succ h
      exact congrArg Nat.succ (ih h')

namespace Metatheory.SystemF

open Ty Term

/-! ## Term Variable Operations -/

/-- Term weakening: if a term is typeable in Γ, it's typeable with a weaker context -/
theorem weakening {k : TyVarCount} {Γ Γ' : Context} {M : Term} {τ : Ty}
    (htype : k ; Γ ⊢ M : τ)
    (hweak : ∀ n A, lookup Γ n = some A → lookup Γ' n = some A) :
    k ; Γ' ⊢ M : τ := by
  induction htype generalizing Γ' with
  | var hlook =>
    exact HasType.var (hweak _ _ hlook)
  | lam hτ₁ _ ih =>
    apply HasType.lam hτ₁
    apply ih
    intro n A hlook
    cases n with
    | zero => exact hlook
    | succ n' => exact hweak n' A hlook
  | app _ _ ih₁ ih₂ =>
    exact HasType.app (ih₁ hweak) (ih₂ hweak)
  | @tlam k' Γ_ctx M' τ' hbody ih =>
    apply HasType.tlam
    apply ih
    intro n A hlook
    simp only [shiftContext, lookup] at hlook ⊢
    rw [List.getElem?_map_af] at hlook ⊢
    cases hΓn : Γ_ctx[n]? with
    | none =>
      rw [hΓn, Option.map_none] at hlook
      exact absurd hlook (Option.noConfusion)
    | some B =>
      rw [hΓn, Option.map_some] at hlook
      have hΓ'n := hweak n B hΓn
      simp only [lookup] at hΓ'n
      rw [hΓ'n, Option.map_some]
      exact hlook
  | tapp _ hσ ih =>
    exact HasType.tapp (ih hweak) hσ

/-! ## Context Lookup Lemmas -/

/-- Context lookup relation for shiftContext -/
theorem shiftContext_lookup {Γ : Context} {n : Nat} {τ : Ty} :
    lookup (shiftContext Γ) n = some τ ↔ ∃ τ', lookup Γ n = some τ' ∧ τ = shiftTyUp 1 0 τ' := by
  simp only [shiftContext, lookup, List.getElem?_map_af]
  constructor
  · intro h
    cases hget : Γ[n]? with
    | none =>
      simp only [hget, Option.map_none] at h
      exact absurd h (Option.noConfusion)
    | some τ' =>
      simp only [hget, Option.map_some] at h
      cases h
      exact ⟨τ', rfl, rfl⟩
  · intro ⟨τ', hτ', heq⟩
    simp only [hτ', Option.map_some]
    rw [heq]

/-! ## Type Substitution Lemmas -/

/-- Generalized lemma: substituting for a shifted type cancels the shift.
    `substTy k σ (shiftTyUp 1 k τ) = τ` -/
theorem substTy_shiftTyUp_cancel (k : Nat) (σ : Ty) (τ : Ty) :
    substTy k σ (shiftTyUp 1 k τ) = τ := by
  induction τ generalizing k σ with
  | tvar n =>
    unfold shiftTyUp substTy
    by_cases h : n < k
    · simp only [if_pos h]
    · simp only [if_neg h]
      have hkn : k ≤ n := Nat.not_lt.mp h
      have h1 : ¬(n + 1 < k) := Nat.not_lt.mpr (Nat.le_succ_of_le hkn)
      have h2 : n + 1 ≠ k := Nat.ne_of_gt (Nat.lt_succ_of_le hkn)
      rw [if_neg h1, if_neg h2, Nat.add_sub_cancel]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    unfold shiftTyUp substTy
    rw [ih₁, ih₂]
  | all τ ih =>
    unfold shiftTyUp substTy
    rw [ih (k + 1) (shiftTyUp 1 0 σ)]

/-- Substituting for a shifted type variable cancels the shift -/
theorem substTy0_shiftTyUp_cancel (σ : Ty) (τ : Ty) : substTy0 σ (shiftTyUp 1 0 τ) = τ :=
  substTy_shiftTyUp_cancel 0 σ τ

/-! ## Shift Commutation Lemmas -/

/-- Generalized shift commutation: shifting at d then at c (where d <= c) commutes with adjustment.
    shiftTyUp 1 d (shiftTyUp 1 c τ) = shiftTyUp 1 (c + 1) (shiftTyUp 1 d τ) when d <= c -/
theorem shiftTyUp_shiftTyUp_comm_gen (τ : Ty) (d c : Nat) (hdc : d ≤ c) :
    shiftTyUp 1 d (shiftTyUp 1 c τ) = shiftTyUp 1 (c + 1) (shiftTyUp 1 d τ) := by
  induction τ generalizing d c with
  | tvar n =>
    simp only [shiftTyUp]
    by_cases hnd : n < d
    · -- n < d <= c: both sides reduce to tvar n
      have hnc : n < c := Nat.lt_of_lt_of_le hnd hdc
      have hnc1 : n < c + 1 := Nat.lt_succ_of_le (Nat.le_of_lt hnc)
      simp only [hnd, hnc, ↓reduceIte, shiftTyUp, hnc1]
    · by_cases hnc : n < c
      · -- d <= n < c: both sides reduce to tvar (n + 1)
        have hn1c1 : n + 1 < c + 1 := Nat.succ_lt_succ hnc
        simp only [hnd, hnc, ↓reduceIte, shiftTyUp, hn1c1]
      · -- c <= n: both sides reduce to tvar (n + 2)
        have hn1c1 : ¬(n + 1 < c + 1) := fun h => hnc (Nat.lt_of_succ_lt_succ h)
        have hn1d : ¬(n + 1 < d) := fun h => hnd (Nat.lt_of_succ_lt h)
        simp only [hnd, hnc, ↓reduceIte, shiftTyUp, hn1d, hn1c1]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp only [shiftTyUp]
    congr 1
    · exact ih₁ d c hdc
    · exact ih₂ d c hdc
  | all τ ih =>
    simp only [shiftTyUp]
    congr 1
    exact ih (d + 1) (c + 1) (Nat.succ_le_succ hdc)

/-- Shift commutation for types at cutoff 0 -/
theorem shiftTyUp_shiftTyUp_comm (τ : Ty) (c : Nat) :
    shiftTyUp 1 0 (shiftTyUp 1 c τ) = shiftTyUp 1 (c + 1) (shiftTyUp 1 0 τ) :=
  shiftTyUp_shiftTyUp_comm_gen τ 0 c (Nat.zero_le c)

/-- shiftContext distributes over cons -/
theorem shiftContext_cons (A : Ty) (Γ : Context) :
    shiftContext (A :: Γ) = shiftTyUp 1 0 A :: shiftContext Γ := by
  simp only [shiftContext, List.map]

/-! ## Term Weakening -/

/-- Generalized term weakening: inserting A at position j in context.
    A is explicit so it can be shifted when going under type binders. -/
theorem term_weakening_at {k : TyVarCount} {Γ : Context} {M : Term} {τ : Ty} (A : Ty) {j : Nat}
    (htype : k ; Γ ⊢ M : τ) (hj : j ≤ Γ.length) :
    k ; (Γ.take j ++ A :: Γ.drop j) ⊢ shiftTermUp 1 j M : τ := by
  induction htype generalizing A j with
  | @var k' Γ' n τ' hlook =>
    simp only [shiftTermUp]
    by_cases hn : n < j
    · simp only [hn, ↓reduceIte]
      apply HasType.var
      simp only [lookup] at hlook ⊢
      rw [List.getElem?_append_left_af]
      · rw [List.getElem?_take_af _ _ _ hn]; exact hlook
      · rw [List.length_take_of_le_af hj]; exact hn
    · simp only [hn, ↓reduceIte]
      apply HasType.var
      simp only [lookup] at hlook ⊢
      rw [List.getElem?_append_right_af]
      · have hjn : j ≤ n := Nat.not_lt.mp hn
        have hlen : (Γ'.take j).length = j := List.length_take_of_le_af hj
        simp only [hlen]
        have h1 : n + 1 - j ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt (Nat.lt_succ_of_le hjn))
        cases hm : n + 1 - j with
        | zero => exact absurd hm h1
        | succ m =>
          simp only [List.getElem?_cons_succ]
          rw [List.getElem?_drop_af]
          have h2 : j + m = n := by
            have hsub : n + 1 - j = (n - j) + 1 := Nat.succ_sub hjn
            rw [hsub] at hm
            have hm' : n - j = m := Nat.succ.inj hm
            rw [← hm']
            exact Nat.add_sub_cancel' hjn
          simp only [h2, hlook]
      · rw [List.length_take_of_le_af hj]; exact Nat.le_succ_of_le (Nat.not_lt.mp hn)
  | @lam k' Γ' τ₁ τ₂ M' hτwf hbody ih =>
    simp only [shiftTermUp]
    apply HasType.lam hτwf
    -- Body M' is typed in τ₁ :: Γ', so we insert A at position j+1
    have hj' : j + 1 ≤ (τ₁ :: Γ').length := Nat.succ_le_succ hj
    have h := ih A hj'
    simp only [List.take, List.drop] at h
    exact h
  | @app k' Γ' M₁ M₂ τ₁ τ₂ hM₁ hM₂ ih₁ ih₂ =>
    simp only [shiftTermUp]
    exact HasType.app (ih₁ A hj) (ih₂ A hj)
  | @tlam k' Γ' M' τ' hbody ih =>
    simp only [shiftTermUp]
    apply HasType.tlam
    -- Body M' is typed in shiftContext Γ', so we insert shiftTyUp 1 0 A at position j
    have hj' : j ≤ (shiftContext Γ').length := by
      unfold shiftContext; rw [List.length_map_af]; exact hj
    have h := ih (shiftTyUp 1 0 A) hj'
    -- Need to show contexts are equal
    have heq : shiftContext (Γ'.take j ++ A :: Γ'.drop j) =
               (shiftContext Γ').take j ++ shiftTyUp 1 0 A :: (shiftContext Γ').drop j := by
      simp only [shiftContext, List.map_append_af, List.map_take_af, List.map_drop_af, List.map]
    rw [heq]
    exact h
  | @tapp k' Γ' M' τ' σ hM hσ ih =>
    simp only [shiftTermUp]
    exact HasType.tapp (ih A hj) hσ

/-- Term weakening: prepending a type to context.
    If `k ; Γ ⊢ M : τ`, then `k ; (A :: Γ) ⊢ shiftTermUp 1 0 M : τ`. -/
theorem term_weakening {k : TyVarCount} {Γ : Context} {M : Term} {τ A : Ty}
    (htype : k ; Γ ⊢ M : τ) :
    k ; (A :: Γ) ⊢ shiftTermUp 1 0 M : τ := by
  have h := term_weakening_at A htype (Nat.zero_le Γ.length)
  simp only [List.take_zero, List.nil_append, List.drop] at h
  exact h

/-! ## Shift-Substitution Commutation -/

/-- Generalized shift-substitution commutation: when substitution cutoff d ≤ shift cutoff c,
    shiftTyUp 1 c (substTy d σ τ) = substTy d (shiftTyUp 1 c σ) (shiftTyUp 1 (c + 1) τ) -/
theorem shiftTyUp_substTy_comm_gen (d c : Nat) (σ τ : Ty) (hdc : d ≤ c) :
    shiftTyUp 1 c (substTy d σ τ) = substTy d (shiftTyUp 1 c σ) (shiftTyUp 1 (c + 1) τ) := by
  induction τ generalizing d c σ with
  | tvar n =>
    unfold substTy shiftTyUp
    by_cases hnd : n < d
    · -- n < d: substTy gives n, shift gives n (since n < d <= c)
      have hnc : n < c := Nat.lt_of_lt_of_le hnd hdc
      have hnc1 : n < c + 1 := Nat.lt_succ_of_lt hnc
      simp only [hnd, hnc, hnc1, ↓reduceIte]
    · simp only [hnd, ↓reduceIte]
      by_cases hneqd : n = d
      · -- n = d: substTy gives σ, then shift gives shiftTyUp 1 c σ
        -- RHS: shiftTyUp gives d (since d < c+1), then substTy at d gives σ shifted
        have hdc1 : d < c + 1 := Nat.lt_succ_of_le hdc
        have hnn : ¬(d < d) := Nat.lt_irrefl d
        simp only [hneqd, hnn, hdc1, ↓reduceIte]
      · -- n > d: substTy decrements n to n-1
        simp only [hneqd, ↓reduceIte]
        have hngd : n > d := Nat.lt_of_le_of_ne (Nat.not_lt.mp hnd) (Ne.symm hneqd)
        by_cases hn1c : n - 1 < c
        · -- n-1 < c: LHS = tvar (n-1), RHS = tvar (n-1)
          have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le d) hngd
          have hnc1 : n < c + 1 := by
            have h1 : n - 1 + 1 = n := Nat.sub_add_cancel hpos
            have h2 : n - 1 + 1 < c + 1 := Nat.succ_lt_succ hn1c
            rw [h1] at h2; exact h2
          simp only [hn1c, hnc1, hnd, hneqd, ↓reduceIte]
        · -- n-1 >= c: LHS = tvar n, RHS = tvar n
          have hn1c' : ¬(n - 1 < c) := hn1c
          have hclen1 : c ≤ n - 1 := Nat.not_lt.mp hn1c
          have hnc1 : ¬(n < c + 1) := Nat.not_lt.mpr (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hclen1 (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le d) hngd) Nat.one_pos)))
          have hdle_n : d ≤ n := Nat.le_of_lt hngd
          have hn1d : ¬(n + 1 < d) := Nat.not_lt.mpr (Nat.le_add_right_of_le hdle_n)
          have hn1neqd : n + 1 ≠ d := Nat.ne_of_gt (Nat.lt_of_le_of_lt hdle_n (Nat.lt_succ_self n))
          simp only [hn1c', hnc1, hn1d, hn1neqd, ↓reduceIte]
          -- Goal: tvar (n - 1 + 1) = tvar (n + 1 - 1)
          have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le d) hngd
          rw [Nat.sub_add_cancel hpos, Nat.add_sub_cancel]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp only [substTy, shiftTyUp]
    congr 1
    · exact ih₁ d c σ hdc
    · exact ih₂ d c σ hdc
  | all τ ih =>
    simp only [substTy, shiftTyUp]
    congr 1
    have ih' := ih (d + 1) (c + 1) (shiftTyUp 1 0 σ) (Nat.succ_le_succ hdc)
    rw [shiftTyUp_shiftTyUp_comm σ c]
    exact ih'

/-- Shift-substitution commutation at cutoff c -/
theorem shiftTyUp_substTy_comm (c : Nat) (σ τ : Ty) :
    shiftTyUp 1 c (substTy0 σ τ) = substTy 0 (shiftTyUp 1 c σ) (shiftTyUp 1 (c + 1) τ) := by
  simp only [substTy0]
  exact shiftTyUp_substTy_comm_gen 0 c σ τ (Nat.zero_le c)

/-- Shift-substitution commutation at cutoff 0 -/
theorem shiftTyUp_substTy0_comm (σ τ : Ty) :
    shiftTyUp 1 0 (substTy0 σ τ) = substTy 0 (shiftTyUp 1 0 σ) (shiftTyUp 1 1 τ) :=
  shiftTyUp_substTy_comm 0 σ τ

/-- Generalized shift-subst commutation at arbitrary cutoff.
    shiftTyUp 1 c (substTy c σ τ) = substTy (c+1) (shiftTyUp 1 c σ) (shiftTyUp 1 c τ) -/
theorem shiftTyUp_substTy_comm_alt (c : Nat) (σ τ : Ty) :
    shiftTyUp 1 c (substTy c σ τ) = substTy (c + 1) (shiftTyUp 1 c σ) (shiftTyUp 1 c τ) := by
  induction τ generalizing c σ with
  | tvar n =>
    simp only [substTy, shiftTyUp]
    by_cases hn_lt_c : n < c
    · -- n < c: LHS = tvar n, RHS = substTy (c+1) _ (tvar n) = tvar n
      have h1 : n < c + 1 := Nat.lt_succ_of_lt hn_lt_c
      simp only [hn_lt_c, h1, ↓reduceIte, substTy, shiftTyUp]
    · simp only [hn_lt_c, ↓reduceIte]
      by_cases hn_eq_c : n = c
      · -- n = c: LHS = shiftTyUp 1 c σ, RHS = substTy (c+1) (shiftTyUp 1 c σ) (tvar c)
        have h1 : ¬(c < c) := Nat.lt_irrefl c
        have h2 : c < c + 1 := Nat.lt_succ_self c
        have h3 : ¬(c + 1 < c + 1) := Nat.lt_irrefl (c + 1)
        simp only [hn_eq_c, h3, ↓reduceIte, substTy]
      · simp only [hn_eq_c, ↓reduceIte]
        have hn_gt_c : n > c := Nat.lt_of_le_of_ne (Nat.not_lt.mp hn_lt_c) (Ne.symm hn_eq_c)
        -- Given n > c, we have n - 1 >= c, so h1 : n - 1 < c is impossible
        have hc_le_n1 : c ≤ n - 1 := by
          have h := Nat.sub_le_sub_right (Nat.succ_le_of_lt hn_gt_c) 1
          simp only [Nat.succ_sub_one] at h; exact h
        by_cases h1 : n - 1 < c
        · -- This case is actually impossible given n > c
          exact absurd h1 (Nat.not_lt.mpr hc_le_n1)
        · have h3 : ¬(n < c) := hn_lt_c
          have hn_gt_c' : c + 1 ≤ n := Nat.succ_le_of_lt hn_gt_c
          have h4 : ¬(n + 1 < c + 1) := Nat.not_lt.mpr (Nat.le_add_right_of_le hn_gt_c')
          have h5 : n + 1 ≠ c + 1 := Nat.ne_of_gt (Nat.succ_lt_succ hn_gt_c)
          simp only [h1, h4, h5, ↓reduceIte, substTy, shiftTyUp]
          -- Goal: tvar (n - 1 + 1) = tvar (n + 1 - 1)
          have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le c) hn_gt_c
          rw [Nat.sub_add_cancel hpos, Nat.add_sub_cancel]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp only [substTy, shiftTyUp]
    congr 1
    · exact ih₁ c σ
    · exact ih₂ c σ
  | all τ ih =>
    simp only [substTy, shiftTyUp]
    congr 1
    have ih' := ih (c + 1) (shiftTyUp 1 0 σ)
    rw [shiftTyUp_shiftTyUp_comm σ c]
    exact ih'

/-- Alternative shift-subst commutation at cutoff 0. -/
theorem shiftTyUp_substTy0_comm_alt (σ τ : Ty) :
    shiftTyUp 1 0 (substTy0 σ τ) = substTy 1 (shiftTyUp 1 0 σ) (shiftTyUp 1 0 τ) :=
  shiftTyUp_substTy_comm_alt 0 σ τ

/-! ## Type Shifting in Terms Preserves Typing -/

/-- Generalized shift typing at arbitrary cutoff -/
theorem shiftTypeInTerm_typing_gen (c : Nat) {k : TyVarCount} {Γ : Context} {M : Term} {τ : Ty}
    (h : k ; Γ ⊢ M : τ) :
    (k + 1) ; Γ.map (shiftTyUp 1 c) ⊢ shiftTypeInTerm 1 c M : shiftTyUp 1 c τ := by
  induction h generalizing c with
  | @var k' Γ' n τ' hlook =>
    apply HasType.var
    simp only [lookup, List.getElem?_map_af]
    simp only [lookup] at hlook
    rw [hlook, Option.map_some]
  | @lam k' Γ' τ₁ τ₂ M' hτ₁wf hbody ih =>
    simp only [shiftTypeInTerm, shiftTyUp]
    apply HasType.lam (WF_shiftTyUp 1 c hτ₁wf)
    have heq : shiftTyUp 1 c τ₁ :: Γ'.map (shiftTyUp 1 c) = (τ₁ :: Γ').map (shiftTyUp 1 c) := by
      simp only [List.map]
    rw [heq]
    exact ih c
  | @app k' Γ' M₁ M₂ τ₁ τ₂ hM₁ hM₂ ih₁ ih₂ =>
    simp only [shiftTypeInTerm]
    exact HasType.app (ih₁ c) (ih₂ c)
  | @tlam k' Γ' M' τ' hbody ih =>
    simp only [shiftTypeInTerm, shiftTyUp]
    apply HasType.tlam
    -- Need to show: shiftContext (Γ'.map (shiftTyUp 1 c)) ⊢ ... : shiftTyUp 1 (c+1) τ'
    -- IH gives: (shiftContext Γ').map (shiftTyUp 1 (c+1)) ⊢ ... : shiftTyUp 1 (c+1) τ'
    have heq : shiftContext (Γ'.map (shiftTyUp 1 c)) =
               (shiftContext Γ').map (shiftTyUp 1 (c + 1)) := by
      simp only [shiftContext, List.map_map_af]
      congr 1
      ext τ
      exact shiftTyUp_shiftTyUp_comm τ c
    rw [heq]
    exact ih (c + 1)
  | @tapp k' Γ' M' τ' σ hM hσ ih =>
    simp only [shiftTypeInTerm]
    have hσ' : Ty.WF (k' + 1) (shiftTyUp 1 c σ) := WF_shiftTyUp 1 c hσ
    have htype := HasType.tapp (ih c) hσ'
    -- Goal: ... ⊢ shiftTypeInTerm 1 c (tapp M' σ) : shiftTyUp 1 c (substTy0 σ τ')
    -- htype: ... ⊢ tapp ... : substTy 0 (shiftTyUp 1 c σ) (shiftTyUp 1 (c+1) τ')
    -- Need to show these types are equal
    rw [shiftTyUp_substTy_comm c σ τ']
    exact htype

/-- Shifting types in a term preserves typing with shifted context -/
theorem shiftTypeInTerm_typing {k : TyVarCount} {Γ : Context} {M : Term} {τ : Ty}
    (h : k ; Γ ⊢ M : τ) :
    (k + 1) ; shiftContext Γ ⊢ shiftTypeInTerm 1 0 M : shiftTyUp 1 0 τ := by
  have hgen := shiftTypeInTerm_typing_gen 0 h
  simp only [shiftContext]
  exact hgen

/-! ## Term Substitution Typing -/

/-- Auxiliary: substitution typing with generic context (for induction).
    If k ; Γ ⊢ M : B and Γ = Γ_pre ++ A :: Γ_post with |Γ_pre| = j,
    and k ; Γ_pre ++ Γ_post ⊢ N : A, then k ; Γ_pre ++ Γ_post ⊢ substTerm j N M : B. -/
theorem substitution_typing_aux {k : TyVarCount} {Γ : Context} {M : Term} {B : Ty}
    (hM : k ; Γ ⊢ M : B) :
    ∀ {j : Nat} {Γ_pre Γ_post : Context} {N : Term} {A : Ty},
    Γ = Γ_pre ++ A :: Γ_post →
    Γ_pre.length = j →
    (k ; (Γ_pre ++ Γ_post) ⊢ N : A) →
    (k ; (Γ_pre ++ Γ_post) ⊢ substTerm j N M : B) := by
  induction hM with
  | @var k' Γ' n τ' hlook =>
    intro j Γ_pre Γ_post N A hΓ hlen hN
    simp only [substTerm]
    subst hΓ
    simp only [lookup, List.getElem?_append_af] at hlook
    by_cases hn_lt_j : n < j
    · -- n < j: variable is in Γ_pre, just keep it
      simp only [hn_lt_j, ite_true]
      apply HasType.var
      simp only [lookup, List.getElem?_append_af]
      have hn_lt_len : n < Γ_pre.length := hlen ▸ hn_lt_j
      simp only [hn_lt_len, ite_true] at hlook ⊢
      exact hlook
    · simp only [hn_lt_j, ite_false]
      have hn_ge_len : ¬(n < Γ_pre.length) := hlen ▸ hn_lt_j
      simp only [hn_ge_len, ite_false] at hlook
      by_cases hn_eq_j : n = j
      · -- n = j: substitute N
        simp only [hn_eq_j, ite_true]
        have hn_minus : n - Γ_pre.length = 0 := by rw [hn_eq_j, hlen, Nat.sub_self]
        simp only [hn_minus] at hlook
        cases hlook with
        | refl => exact hN
      · -- n > j: decrement and look up in Γ_post
        simp only [hn_eq_j, ite_false]
        apply HasType.var
        simp only [lookup, List.getElem?_append_af]
        have hn_gt_j : n > j := Nat.lt_of_le_of_ne (Nat.not_lt.mp hn_lt_j) (Ne.symm hn_eq_j)
        have hn_minus_pos : n - Γ_pre.length > 0 := Nat.sub_pos_of_lt (hlen ▸ hn_gt_j)
        cases hn_eq : n - Γ_pre.length with
        | zero => exact absurd hn_eq (Nat.ne_of_gt hn_minus_pos)
        | succ m =>
          -- hlook : (A :: Γ_post)[succ m]? = some τ'
          -- n - 1 in new context
          have hlen_le_n1 : Γ_pre.length ≤ n - 1 := by
            have h := Nat.sub_le_sub_right (Nat.succ_le_of_lt (hlen ▸ hn_gt_j)) 1
            simp only [Nat.succ_sub_one] at h; exact h
          have h1 : ¬(n - 1 < Γ_pre.length) := Nat.not_lt.mpr hlen_le_n1
          simp only [h1, ite_false]
          have h2 : n - 1 - Γ_pre.length = m := by
            have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j) hn_gt_j
            rw [Nat.sub_sub, Nat.add_comm, ← Nat.sub_sub]
            have h3 : n - Γ_pre.length - 1 = m := by rw [hn_eq]; rfl
            exact h3
          simp only [h2]
          rw [hn_eq, List.getElem?_cons_succ] at hlook
          exact hlook
  | @lam k' Γ' τ₁ τ₂ M' hτwf hbody ih =>
    intro j Γ_pre Γ_post N A hΓ hlen hN
    simp only [substTerm]
    subst hΓ
    apply HasType.lam hτwf
    -- Apply IH with context (τ₁ :: Γ_pre) ++ A :: Γ_post
    have heq : τ₁ :: (Γ_pre ++ A :: Γ_post) = (τ₁ :: Γ_pre) ++ A :: Γ_post :=
      List.cons_append.symm
    have hlen' : (τ₁ :: Γ_pre).length = j + 1 := by rw [List.length_cons, hlen]
    have hN' : k' ; ((τ₁ :: Γ_pre) ++ Γ_post) ⊢ shiftTermUp 1 0 N : A := by
      have heq2 : (τ₁ :: Γ_pre) ++ Γ_post = τ₁ :: (Γ_pre ++ Γ_post) := List.cons_append
      rw [heq2]
      exact term_weakening hN
    have result := ih heq hlen' hN'
    rw [List.cons_append] at result
    exact result
  | @app k' Γ' M₁ M₂ τ₁ τ₂ hM₁ hM₂ ih₁ ih₂ =>
    intro j Γ_pre Γ_post N A hΓ hlen hN
    simp only [substTerm]
    exact HasType.app (ih₁ hΓ hlen hN) (ih₂ hΓ hlen hN)
  | @tlam k' Γ' M' τ' hbody ih =>
    intro j Γ_pre Γ_post N A hΓ hlen hN
    simp only [substTerm]
    subst hΓ
    apply HasType.tlam
    -- hbody has context shiftContext (Γ_pre ++ A :: Γ_post)
    have hshift : shiftContext (Γ_pre ++ A :: Γ_post) =
                  shiftContext Γ_pre ++ shiftTyUp 1 0 A :: shiftContext Γ_post := by
      simp only [shiftContext, List.map_append_af, List.map]
    have hlen' : (shiftContext Γ_pre).length = j := by
      unfold shiftContext; rw [List.length_map_af, hlen]
    have hN' : (k' + 1) ; (shiftContext Γ_pre ++ shiftContext Γ_post) ⊢
               shiftTypeInTerm 1 0 N : shiftTyUp 1 0 A := by
      have heq : shiftContext Γ_pre ++ shiftContext Γ_post = shiftContext (Γ_pre ++ Γ_post) := by
        unfold shiftContext; exact List.map_append_af.symm
      rw [heq]
      exact shiftTypeInTerm_typing hN
    have hctx_eq : shiftContext (Γ_pre ++ Γ_post) = shiftContext Γ_pre ++ shiftContext Γ_post := by
      unfold shiftContext; exact List.map_append_af
    rw [hctx_eq]
    exact ih hshift hlen' hN'
  | @tapp k' Γ' M' τ' σ hM hσ ih =>
    intro j Γ_pre Γ_post N A hΓ hlen hN
    simp only [substTerm]
    exact HasType.tapp (ih hΓ hlen hN) hσ

/-- Term substitution preserves typing.
    If `k ; (A :: Γ) ⊢ M : B` and `k ; Γ ⊢ N : A`, then `k ; Γ ⊢ substTerm0 N M : B`. -/
theorem substitution_typing {k : TyVarCount} {Γ : Context} {M N : Term} {A B : Ty}
    (hM : k ; (A :: Γ) ⊢ M : B)
    (hN : k ; Γ ⊢ N : A) :
    k ; Γ ⊢ substTerm0 N M : B := by
  -- Use substitution_typing_aux with Γ_pre = [], Γ_post = Γ, j = 0
  have haux := @substitution_typing_aux k (A :: Γ) M B hM 0 [] Γ N A rfl rfl hN
  simp only [List.nil_append] at haux
  exact haux

/-! ## Type Substitution in Terms Typing -/

/-- Shift a type up by 1 at cutoff 0, n times. -/
def shiftTyUpN : Nat → Ty → Ty
  | 0, τ => τ
  | n + 1, τ => shiftTyUp 1 0 (shiftTyUpN n τ)

theorem shiftTyUpN_zero (τ : Ty) : shiftTyUpN 0 τ = τ := rfl
theorem shiftTyUpN_succ (n : Nat) (τ : Ty) : shiftTyUpN (n + 1) τ = shiftTyUp 1 0 (shiftTyUpN n τ) := rfl

/-- Shift-subst commutation: shift at cutoff d commutes with subst at cutoff c ≥ d.
    The substitution cutoff increases by 1 and the shift cutoff stays the same.
    shiftTyUp 1 d (substTy c σ τ) = substTy (c + 1) (shiftTyUp 1 d σ) (shiftTyUp 1 d τ) -/
theorem shiftTyUp_low_substTy_comm (d c : Nat) (σ τ : Ty) (hdc : d ≤ c) :
    shiftTyUp 1 d (substTy c σ τ) = substTy (c + 1) (shiftTyUp 1 d σ) (shiftTyUp 1 d τ) := by
  induction τ generalizing d c σ with
  | tvar n =>
    unfold substTy shiftTyUp
    by_cases hn_lt_d : n < d
    · -- n < d ≤ c: stays as tvar n on both sides
      have hn_lt_c : n < c := Nat.lt_of_lt_of_le hn_lt_d hdc
      have h1 : n < c + 1 := Nat.lt_succ_of_lt hn_lt_c
      simp only [hn_lt_c, hn_lt_d, h1, ↓reduceIte]
    · by_cases hn_lt_c : n < c
      · -- d ≤ n < c: shifts to n+1, then stays as tvar (n+1)
        have h1 : n + 1 < c + 1 := Nat.succ_lt_succ hn_lt_c
        have h2 : ¬(n + 1 < d) := Nat.not_lt.mpr (Nat.le_succ_of_le (Nat.not_lt.mp hn_lt_d))
        simp only [hn_lt_c, hn_lt_d, h1, ↓reduceIte]
      · by_cases hn_eq_c : n = c
        · -- n = c: substituted by σ, then shifted
          subst hn_eq_c
          have h1 : ¬(n + 1 < n + 1) := Nat.lt_irrefl (n + 1)
          have h2 : ¬(n + 1 < d) := Nat.not_lt.mpr (Nat.le_succ_of_le (Nat.not_lt.mp hn_lt_d))
          simp only [hn_lt_c, hn_lt_d, h1, ↓reduceIte]
        · -- n > c ≥ d: decremented to n-1, then shifted
          have hn_gt_c : n > c := Nat.lt_of_le_of_ne (Nat.not_lt.mp hn_lt_c) (Ne.symm hn_eq_c)
          have h1 : ¬(n + 1 < c + 1) := Nat.not_lt.mpr (Nat.succ_le_succ (Nat.le_of_lt hn_gt_c))
          have h2 : n + 1 ≠ c + 1 := Nat.ne_of_gt (Nat.succ_lt_succ hn_gt_c)
          have hn_gt_d : n > d := Nat.lt_of_le_of_lt hdc hn_gt_c
          have h_d_le_n1 : d ≤ n - 1 := by
            have h := Nat.sub_le_sub_right (Nat.succ_le_of_lt hn_gt_d) 1
            simp only [Nat.succ_sub_one] at h; exact h
          by_cases hn1_lt_d : n - 1 < d
          · -- This case is impossible: n > d implies n - 1 >= d
            exact absurd hn1_lt_d (Nat.not_lt.mpr h_d_le_n1)
          · have h3 : ¬(n + 1 < d) := Nat.not_lt.mpr (Nat.le_succ_of_le (Nat.not_lt.mp hn_lt_d))
            simp only [hn_lt_c, hn_eq_c, hn_lt_d, hn1_lt_d, h1, h2, ↓reduceIte]
            -- Goal: tvar (n - 1 + 1) = tvar (n + 1 - 1)
            have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le d) hn_gt_d
            rw [Nat.sub_add_cancel hpos, Nat.add_sub_cancel]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp only [substTy, shiftTyUp, ih₁ d c σ hdc, ih₂ d c σ hdc]
  | all τ ih =>
    simp only [substTy, shiftTyUp]
    congr 1
    -- Goal has: shiftTyUp 1 0 (shiftTyUp 1 d σ)
    -- IH gives: shiftTyUp 1 (d+1) (shiftTyUp 1 0 σ)
    -- Use: shiftTyUp 1 0 (shiftTyUp 1 d σ) = shiftTyUp 1 (d+1) (shiftTyUp 1 0 σ)
    rw [shiftTyUp_shiftTyUp_comm σ d]
    exact ih (d + 1) (c + 1) (shiftTyUp 1 0 σ) (Nat.succ_le_succ hdc)

/-- Shift at cutoff 0 commutes with substitution at arbitrary cutoff c.
    This is key for shiftContext which always shifts at cutoff 0. -/
theorem shiftTyUp0_substTy_comm (c : Nat) (σ τ : Ty) :
    shiftTyUp 1 0 (substTy c σ τ) = substTy (c + 1) (shiftTyUp 1 0 σ) (shiftTyUp 1 0 τ) :=
  shiftTyUp_low_substTy_comm 0 c σ τ (Nat.zero_le c)

/-- Key lemma: shifting context commutes with type substitution.
    shiftContext (Γ.map (substTy c σ)) = (shiftContext Γ).map (substTy (c+1) (shiftTyUp 1 0 σ)) -/
theorem shiftContext_map_substTy_comm (c : Nat) (σ : Ty) (Γ : Context) :
    shiftContext (Γ.map (substTy c σ)) = (shiftContext Γ).map (substTy (c + 1) (shiftTyUp 1 0 σ)) := by
  simp only [shiftContext, List.map_map_af]
  congr 1
  ext τ
  exact shiftTyUp0_substTy_comm c σ τ

/-! ## Helper Lemmas for Type Substitution Typing -/

/-- WF is preserved by shiftTyUpN -/
theorem WF_shiftTyUpN (c : Nat) {k : Nat} {σ : Ty} (h : Ty.WF k σ) : Ty.WF (k + c) (shiftTyUpN c σ) := by
  induction c with
  | zero => exact h
  | succ c ih =>
    simp only [shiftTyUpN_succ]
    have this := Ty.WF_shiftTyUp 1 0 ih
    -- this : Ty.WF (k + c + 1) (shiftTyUp 1 0 (shiftTyUpN c σ))
    -- goal : Ty.WF (k + (c + 1)) (shiftTyUp 1 0 (shiftTyUpN c σ))
    have heq : k + c + 1 = k + (c + 1) := Nat.add_assoc k c 1
    rw [← heq]
    exact this

/-- Standard substitution composition lemma for System F types.
    substTy k σ (substTy j σ' τ) = substTy j (substTy k σ σ') (substTy (k + 1) (shiftTyUp 1 j σ) τ)
    when j ≤ k.

    This is the key lemma for type substitution in System F. -/
theorem substTy_substTy_std (j k : Nat) (σ σ' τ : Ty) (h : j ≤ k) :
    substTy k σ (substTy j σ' τ) =
    substTy j (substTy k σ σ') (substTy (k + 1) (shiftTyUp 1 j σ) τ) := by
  induction τ generalizing j k σ σ' with
  | tvar n =>
    simp only [substTy]
    -- Case analysis on n vs j
    by_cases hnj : n < j
    · -- Case n < j: inner subst on LHS gives tvar n
      have hnk : n < k := Nat.lt_of_lt_of_le hnj h
      have hnk1 : n < k + 1 := Nat.lt_succ_of_le (Nat.le_of_lt hnk)
      -- LHS: substTy k σ (tvar n) = tvar n since n < k
      -- RHS: substTy j ... (tvar n) = tvar n since n < j
      simp only [if_pos hnj, if_pos hnk, if_pos hnk1, substTy]
    · by_cases hneqj : n = j
      · -- Case n = j: inner subst on LHS gives σ'
        subst hneqj  -- Now j is replaced with n, h : n ≤ k
        have hnk1 : n < k + 1 := Nat.lt_succ_of_le h
        have hn_not_lt_n : ¬(n < n) := Nat.lt_irrefl n
        -- LHS: substTy k σ σ', RHS: substTy n (substTy k σ σ') (tvar n) where n = n, so = substTy k σ σ'
        simp only [hn_not_lt_n, if_true, if_pos hnk1, if_false, substTy]
      · -- Case n > j: inner subst on LHS gives tvar (n-1)
        have hngej : j < n := Nat.lt_of_le_of_ne (Nat.not_lt.mp hnj) (Ne.symm hneqj)
        by_cases hnk1 : n < k + 1
        · -- n < k + 1, so n ≤ k
          have hn_le_k : n ≤ k := Nat.lt_succ_iff.mp hnk1
          -- Now analyze n - 1 vs k
          by_cases hn1k : n - 1 < k
          · -- LHS: substTy k σ (tvar (n-1)) = tvar (n-1) since n-1 < k
            -- RHS: substTy j ... (tvar n) = tvar (n-1) since n > j
            simp only [if_neg hnj, if_neg hneqj, if_pos hnk1, if_pos hn1k, substTy]
          · -- n - 1 ≥ k, with n ≤ k means n - 1 = k (so n = k + 1), contradiction with n < k + 1
            -- From ¬(n - 1 < k), we have k ≤ n - 1, so k < n (when n > 0, which holds since n > j ≥ 0)
            have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j) hngej
            have hk_lt_n : k < n := Nat.lt_of_le_of_lt (Nat.not_lt.mp hn1k) (Nat.sub_lt hpos Nat.one_pos)
            exact absurd hk_lt_n (Nat.not_lt.mpr hn_le_k)
        · by_cases hneqk1 : n = k + 1
          · -- n = k + 1
            have hn1_eq_k : n - 1 = k := by rw [hneqk1]; exact Nat.add_sub_cancel k 1
            have hn1_not_lt_k : ¬(n - 1 < k) := by rw [hn1_eq_k]; exact Nat.lt_irrefl k
            -- LHS: substTy k σ (tvar (n-1)) = substTy k σ (tvar k) = σ
            -- RHS: substTy j ... (shiftTyUp 1 j σ) = σ by cancel
            simp only [if_neg hnj, if_neg hneqj, if_neg hnk1, if_pos hneqk1,
                       hn1_eq_k, Nat.lt_irrefl, if_true, substTy]
            exact (substTy_shiftTyUp_cancel j (substTy k σ σ') σ).symm
          · -- n > k + 1
            have hngek1 : k + 1 < n := Nat.lt_of_le_of_ne (Nat.not_lt.mp hnk1) (Ne.symm hneqk1)
            have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le (k + 1)) hngek1
            have hk_lt_n1 : k < n - 1 := by
              have h1 : k + 1 + 1 ≤ n := Nat.succ_le_of_lt hngek1
              have h2 : (k + 1 + 1) - 1 ≤ n - 1 := Nat.sub_le_sub_right h1 1
              simp only [Nat.add_sub_cancel] at h2
              exact Nat.lt_of_succ_le h2
            have hn1gtk : ¬(n - 1 < k) := Nat.not_lt.mpr (Nat.le_of_lt hk_lt_n1)
            have hn1neqk : n - 1 ≠ k := Nat.ne_of_gt hk_lt_n1
            have hj_lt_n1 : j < n - 1 := Nat.lt_of_le_of_lt h hk_lt_n1
            have hn1gtj : ¬(n - 1 < j) := Nat.not_lt.mpr (Nat.le_of_lt hj_lt_n1)
            have hn1neqj : n - 1 ≠ j := Nat.ne_of_gt hj_lt_n1
            -- LHS: substTy k σ (tvar (n-1)) = tvar (n-2) since n-1 > k
            -- RHS: substTy j ... (tvar (n-1)) = tvar (n-2) since n-1 > j
            simp only [if_neg hnj, if_neg hneqj, if_neg hnk1, if_neg hneqk1,
                       if_neg hn1gtk, if_neg hn1neqk, if_neg hn1gtj, if_neg hn1neqj, substTy]
  | arr τ₁ τ₂ ih₁ ih₂ =>
    simp only [substTy]
    exact congr (congrArg arr (ih₁ j k σ σ' h)) (ih₂ j k σ σ' h)
  | all τ ih =>
    simp only [substTy]
    -- Set up the helper equalities
    have eq1 : substTy (k + 1) (shiftTyUp 1 0 σ) (shiftTyUp 1 0 σ') = shiftTyUp 1 0 (substTy k σ σ') :=
      (shiftTyUp0_substTy_comm k σ σ').symm
    have eq2 : shiftTyUp 1 (j + 1) (shiftTyUp 1 0 σ) = shiftTyUp 1 0 (shiftTyUp 1 j σ) :=
      (shiftTyUp_shiftTyUp_comm_gen σ 0 j (Nat.zero_le j)).symm
    -- Get the IH and rewrite with the equalities
    have ih' := ih (j + 1) (k + 1) (shiftTyUp 1 0 σ) (shiftTyUp 1 0 σ') (Nat.succ_le_succ h)
    simp only [eq1, eq2] at ih'
    exact congrArg all ih'

/-- Substitution composition at inner cutoff 0 (form used in proofs). -/
theorem substTy_substTy_gen (c : Nat) (σ σ' τ : Ty) :
    substTy c σ (substTy 0 σ' τ) = substTy 0 (substTy c σ σ') (substTy (c + 1) (shiftTyUp 1 0 σ) τ) :=
  substTy_substTy_std 0 c σ σ' τ (Nat.zero_le c)

/-- Fully generalized type substitution typing at arbitrary cutoff c.

    When a term M has n type variables in scope and we substitute a type σ for
    variable c (where n = k + c + 1 and σ is well-formed at k + c), the result
    has k + c type variables and the same typing relation holds with appropriately
    substituted context and type. -/
theorem type_substitution_typing_full {n : TyVarCount} {Γ : Context} {M : Term} {τ : Ty}
    (hM : n ; Γ ⊢ M : τ) :
    ∀ {c k : Nat} {σ : Ty},
    n = k + c + 1 →
    Ty.WF (k + c) σ →
    (k + c) ; Γ.map (substTy c σ) ⊢
      substTypeInTerm c σ M : substTy c σ τ := by
  induction hM with
  | @var n' Γ' x τ' hlook =>
    intro c k σ hn hσ
    simp only [substTypeInTerm]
    apply HasType.var
    simp only [lookup] at hlook ⊢
    simp only [List.getElem?_map_af, hlook, Option.map_some]
  | @lam n' Γ' τ₁' τ₂' M' hwf hbody ih =>
    intro c k σ hn hσ
    simp only [substTypeInTerm, substTy]
    apply HasType.lam
    · -- WF (k + c) (substTy c σ τ₁')
      subst hn
      exact Ty.WF_substTy (Nat.le_add_left c k) hwf hσ
    · -- (k + c) ; substTy c σ τ₁' :: Γ'.map (substTy c σ) ⊢ ... : ...
      have h := ih hn hσ
      simp only [List.map_cons] at h
      exact h
  | @app n' Γ' M' N' τ₁' τ₂' hfun harg ihfun iharg =>
    intro c k σ hn hσ
    simp only [substTypeInTerm]
    apply HasType.app
    · exact ihfun hn hσ
    · exact iharg hn hσ
  | @tlam n' Γ' M' τ' hbody ih =>
    intro c k σ hn hσ
    simp only [substTypeInTerm, substTy]
    apply HasType.tlam
    -- Under tlam, body has n' + 1 type vars in context shiftContext Γ'
    -- We substitute at cutoff c + 1 with shiftTyUp 1 0 σ
    -- Use shiftContext_map_substTy_comm: shifting commutes with substitution
    have hctx : shiftContext (Γ'.map (substTy c σ)) =
                (shiftContext Γ').map (substTy (c + 1) (shiftTyUp 1 0 σ)) := by
      exact shiftContext_map_substTy_comm c σ Γ'
    rw [hctx]
    -- Apply IH at cutoff c + 1
    -- Body has n' + 1 = (k + c + 1) + 1 = k + (c + 1) + 1 type vars
    subst hn
    have hn' : (k + c + 1) + 1 = k + (c + 1) + 1 := by rw [Nat.add_assoc k c 1]
    have hσ' : Ty.WF (k + (c + 1)) (shiftTyUp 1 0 σ) := by
      have hwf := Ty.WF_shiftTyUp 1 0 hσ
      have heq : k + c + 1 = k + (c + 1) := Nat.add_assoc k c 1
      rw [heq] at hwf
      exact hwf
    have result := ih hn' hσ'
    -- k + (c + 1) = k + c + 1
    have heq : k + c + 1 = k + (c + 1) := Nat.add_assoc k c 1
    rw [heq]
    exact result
  | @tapp n' Γ' M' τ' σ' hfun hwf ih =>
    intro c k σ hn hσ
    simp only [substTypeInTerm]
    have hfun' := ih hn hσ
    simp only [substTy] at hfun'
    -- Need to establish the type equality using substTy_substTy_gen
    have hsubst_eq : substTy c σ (substTy0 σ' τ') =
        substTy0 (substTy c σ σ') (substTy (c + 1) (shiftTyUp 1 0 σ) τ') := by
      exact substTy_substTy_gen c σ σ' τ'
    rw [hsubst_eq]
    apply HasType.tapp hfun'
    subst hn
    exact Ty.WF_substTy (Nat.le_add_left c k) hwf hσ

/-- Type substitution typing at cutoff 0 (standard form). -/
theorem type_substitution_typing_aux {n : TyVarCount} {Γ : Context} {M : Term} {τ : Ty}
    (hM : n ; Γ ⊢ M : τ) :
    ∀ {k : Nat} {σ : Ty},
    n = k + 1 →
    Ty.WF k σ →
    k ; Γ.map (substTy 0 σ) ⊢
      substTypeInTerm 0 σ M : substTy 0 σ τ := by
  intro k σ hn hσ
  have h := type_substitution_typing_full hM (c := 0) (k := k) (σ := σ)
  simp only [Nat.add_zero] at h
  exact h hn hσ

theorem type_substitution_typing_gen {k : TyVarCount} {Γ : Context} {M : Term} {τ σ : Ty}
    (hM : (k + 1) ; Γ ⊢ M : τ)
    (hσ : Ty.WF k σ) :
    k ; Γ.map (substTy 0 σ) ⊢
      substTypeInTerm 0 σ M : substTy 0 σ τ :=
  type_substitution_typing_aux hM rfl hσ

/-- Type substitution in terms preserves typing.
    If `(k+1) ; shiftContext Γ ⊢ M : τ` and `Ty.WF k σ`,
    then `k ; Γ ⊢ substTypeInTerm0 σ M : substTy0 σ τ`. -/
theorem type_substitution_typing {k : TyVarCount} {Γ : Context} {M : Term} {τ σ : Ty}
    (hM : (k + 1) ; shiftContext Γ ⊢ M : τ)
    (hσ : Ty.WF k σ) :
    k ; Γ ⊢ substTypeInTerm0 σ M : substTy0 σ τ := by
  have hgen := type_substitution_typing_gen hM hσ
  -- Need: (shiftContext Γ).map (substTy 0 σ) = Γ
  have hctx : (shiftContext Γ).map (substTy 0 σ) = Γ := by
    simp only [shiftContext, List.map_map, Function.comp_def]
    have heq : ∀ τ', substTy 0 σ (shiftTyUp 1 0 τ') = τ' := substTy0_shiftTyUp_cancel σ
    have : (fun x => substTy 0 σ (shiftTyUp 1 0 x)) = id := funext heq
    simp only [this, List.map_id_af]
  rw [hctx] at hgen
  exact hgen

/-! ## Subject Reduction Theorem -/

/-- Subject Reduction (Type Preservation): reduction preserves types.

    If `k ; Γ ⊢ M : τ` and `M ⟶ N`, then `k ; Γ ⊢ N : τ`. -/
theorem subject_reduction {k : TyVarCount} {Γ : Context} {M N : Term} {τ : Ty}
    (htype : k ; Γ ⊢ M : τ)
    (hstep : M ⟶ N) :
    k ; Γ ⊢ N : τ := by
  induction hstep generalizing k Γ τ with
  | @beta τ₁ M' N' =>
    cases htype with
    | @app _ _ _ _ τ₁' τ₂ hM hN =>
      cases hM with
      | @lam _ _ _ _ _ hτwf hBody =>
        exact substitution_typing hBody hN
  | @tbeta M' σ' =>
    cases htype with
    | @tapp _ _ _ τ' σ'' hM hσ =>
      cases hM with
      | @tlam _ _ _ _ hBody =>
        exact type_substitution_typing hBody hσ
  | @appL M' M'' N' hstep ih =>
    cases htype with
    | app hM hN =>
      exact HasType.app (ih hM) hN
  | @appR M' N' N'' hstep ih =>
    cases htype with
    | app hM hN =>
      exact HasType.app hM (ih hN)
  | @tappL M' M'' σ' hstep ih =>
    cases htype with
    | tapp hM hσ =>
      exact HasType.tapp (ih hM) hσ

/-- Subject reduction for multi-step reduction -/
theorem subject_reduction_multi {k : TyVarCount} {Γ : Context} {M N : Term} {τ : Ty}
    (htype : k ; Γ ⊢ M : τ)
    (hsteps : M ⟶* N) :
    k ; Γ ⊢ N : τ := by
  induction hsteps with
  | refl => exact htype
  | step hstep _ ih =>
    exact ih (subject_reduction htype hstep)

end Metatheory.SystemF
