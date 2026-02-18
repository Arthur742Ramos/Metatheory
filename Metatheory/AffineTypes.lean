/-
  Armada 646: Affine Type System (Rust-like Ownership Types)

  A simply-typed lambda calculus with affine (use-at-most-once) typing,
  modelling Rust-like ownership / move semantics.
-/

-- ══════════════════════════════════════════════════════════════
-- SECTION 1 : SYNTAX
-- ══════════════════════════════════════════════════════════════

namespace Affine

inductive Ty where
  | unit  : Ty
  | nat   : Ty
  | bool  : Ty
  | fn    : Ty → Ty → Ty
  | prod  : Ty → Ty → Ty
  | owned : Ty → Ty
  deriving DecidableEq, Repr

inductive Expr where
  | var    : Nat → Expr
  | unit   : Expr
  | natLit : Nat → Expr
  | boolLit: Bool → Expr
  | lam    : Ty → Expr → Expr
  | app    : Expr → Expr → Expr
  | pair   : Expr → Expr → Expr
  | fst    : Expr → Expr
  | snd    : Expr → Expr
  | letE   : Expr → Expr → Expr
  | own    : Expr → Expr
  | move   : Expr → Expr
  | ite    : Expr → Expr → Expr → Expr
  deriving DecidableEq, Repr

-- ══════════════════════════════════════════════════════════════
-- SECTION 2 : VALUES
-- ══════════════════════════════════════════════════════════════

inductive IsValue : Expr → Prop where
  | unit   : IsValue Expr.unit
  | natLit : IsValue (Expr.natLit n)
  | boolLit: IsValue (Expr.boolLit b)
  | lam    : IsValue (Expr.lam τ body)
  | pair   : IsValue e₁ → IsValue e₂ → IsValue (Expr.pair e₁ e₂)
  | own    : IsValue e → IsValue (Expr.own e)

-- ══════════════════════════════════════════════════════════════
-- SECTION 3 : SUBSTITUTION
-- ══════════════════════════════════════════════════════════════

def substVar (j : Nat) (s : Expr) (n : Nat) : Expr :=
  if n = j then s else Expr.var n

def subst (j : Nat) (s : Expr) : Expr → Expr
  | Expr.var n       => substVar j s n
  | Expr.unit        => Expr.unit
  | Expr.natLit n    => Expr.natLit n
  | Expr.boolLit b   => Expr.boolLit b
  | Expr.lam τ body  => Expr.lam τ (subst (j + 1) s body)
  | Expr.app f a     => Expr.app (subst j s f) (subst j s a)
  | Expr.pair a b    => Expr.pair (subst j s a) (subst j s b)
  | Expr.fst e       => Expr.fst (subst j s e)
  | Expr.snd e       => Expr.snd (subst j s e)
  | Expr.letE a b    => Expr.letE (subst j s a) (subst (j + 1) s b)
  | Expr.own e       => Expr.own (subst j s e)
  | Expr.move e      => Expr.move (subst j s e)
  | Expr.ite c t f   => Expr.ite (subst j s c) (subst j s t) (subst j s f)

-- ══════════════════════════════════════════════════════════════
-- SECTION 4 : SMALL-STEP SEMANTICS
-- ══════════════════════════════════════════════════════════════

inductive Step : Expr → Expr → Prop where
  | appFun    : Step e₁ e₁' → Step (Expr.app e₁ e₂) (Expr.app e₁' e₂)
  | appArg    : IsValue v₁ → Step e₂ e₂' → Step (Expr.app v₁ e₂) (Expr.app v₁ e₂')
  | appBeta   : IsValue v → Step (Expr.app (Expr.lam τ body) v) (subst 0 v body)
  | pairL     : Step e₁ e₁' → Step (Expr.pair e₁ e₂) (Expr.pair e₁' e₂)
  | pairR     : IsValue v₁ → Step e₂ e₂' → Step (Expr.pair v₁ e₂) (Expr.pair v₁ e₂')
  | fstStep   : Step e e' → Step (Expr.fst e) (Expr.fst e')
  | fstBeta   : IsValue v₁ → IsValue v₂ → Step (Expr.fst (Expr.pair v₁ v₂)) v₁
  | sndStep   : Step e e' → Step (Expr.snd e) (Expr.snd e')
  | sndBeta   : IsValue v₁ → IsValue v₂ → Step (Expr.snd (Expr.pair v₁ v₂)) v₂
  | letStep   : Step e₁ e₁' → Step (Expr.letE e₁ e₂) (Expr.letE e₁' e₂)
  | letBeta   : IsValue v → Step (Expr.letE v e₂) (subst 0 v e₂)
  | ownStep   : Step e e' → Step (Expr.own e) (Expr.own e')
  | moveStep  : Step e e' → Step (Expr.move e) (Expr.move e')
  | moveBeta  : IsValue v → Step (Expr.move (Expr.own v)) v
  | iteStep   : Step c c' → Step (Expr.ite c t f) (Expr.ite c' t f)
  | iteTrue   : Step (Expr.ite (Expr.boolLit true) t f) t
  | iteFalse  : Step (Expr.ite (Expr.boolLit false) t f) f

-- ══════════════════════════════════════════════════════════════
-- SECTION 5 : VALUE / STEP EXCLUSION
-- ══════════════════════════════════════════════════════════════

theorem isValue_not_var : ¬ IsValue (Expr.var n) := by intro h; cases h
theorem isValue_not_app : ¬ IsValue (Expr.app e₁ e₂) := by intro h; cases h
theorem isValue_not_fst : ¬ IsValue (Expr.fst e) := by intro h; cases h
theorem isValue_not_snd : ¬ IsValue (Expr.snd e) := by intro h; cases h
theorem isValue_not_move : ¬ IsValue (Expr.move e) := by intro h; cases h
theorem isValue_not_ite : ¬ IsValue (Expr.ite c t f) := by intro h; cases h
theorem isValue_not_letE : ¬ IsValue (Expr.letE e₁ e₂) := by intro h; cases h

theorem value_no_step : IsValue e → Step e e' → False := by
  intro hv hs
  induction hv generalizing e' with
  | unit => cases hs
  | natLit => cases hs
  | boolLit => cases hs
  | lam => cases hs
  | pair _ _ ih1 ih2 =>
    cases hs with
    | pairL h => exact ih1 h
    | pairR _ h => exact ih2 h
  | own _ ih =>
    cases hs with
    | ownStep h => exact ih h

theorem step_not_value : Step e e' → ¬ IsValue e :=
  fun hs hv => value_no_step hv hs

-- ══════════════════════════════════════════════════════════════
-- SECTION 6 : DETERMINISM
-- ══════════════════════════════════════════════════════════════

private theorem val_no_step' {e e' : Expr} (hv : IsValue e) (hs : Step e e') : False :=
  value_no_step hv hs

theorem step_det : Step e e₁ → Step e e₂ → e₁ = e₂ := by
  intro h1 h2
  induction h1 generalizing e₂ with
  | appFun s ih =>
    cases h2 with
    | appFun s2 => exact congrArg (Expr.app · _) (ih s2)
    | appArg hv _ => exact absurd hv (fun hv => val_no_step' hv s)
    | appBeta _ => cases s
  | appArg hv s ih =>
    cases h2 with
    | appFun s2 => exact absurd hv (fun hv => val_no_step' hv s2)
    | appArg _ s2 => exact congrArg (Expr.app _) (ih s2)
    | appBeta hv2 => exact absurd hv2 (fun hv2 => val_no_step' hv2 s)
  | appBeta hv =>
    cases h2 with
    | appFun s2 => cases s2
    | appArg _ s2 => exact absurd hv (fun hv => val_no_step' hv s2)
    | appBeta _ => rfl
  | pairL s ih =>
    cases h2 with
    | pairL s2 => exact congrArg (Expr.pair · _) (ih s2)
    | pairR hv _ => exact absurd hv (fun hv => val_no_step' hv s)
  | pairR hv s ih =>
    cases h2 with
    | pairL s2 => exact absurd hv (fun hv => val_no_step' hv s2)
    | pairR _ s2 => exact congrArg (Expr.pair _) (ih s2)
  | fstStep s ih =>
    cases h2 with
    | fstStep s2 => exact congrArg Expr.fst (ih s2)
    | fstBeta hv1 hv2 =>
      cases s with
      | pairL s => exact (val_no_step' hv1 s).elim
      | pairR _ s => exact (val_no_step' hv2 s).elim
  | fstBeta hv1 hv2 =>
    cases h2 with
    | fstStep s2 =>
      cases s2 with
      | pairL s => exact (val_no_step' hv1 s).elim
      | pairR _ s => exact (val_no_step' hv2 s).elim
    | fstBeta _ _ => rfl
  | sndStep s ih =>
    cases h2 with
    | sndStep s2 => exact congrArg Expr.snd (ih s2)
    | sndBeta hv1 hv2 =>
      cases s with
      | pairL s => exact (val_no_step' hv1 s).elim
      | pairR _ s => exact (val_no_step' hv2 s).elim
  | sndBeta hv1 hv2 =>
    cases h2 with
    | sndStep s2 =>
      cases s2 with
      | pairL s => exact (val_no_step' hv1 s).elim
      | pairR _ s => exact (val_no_step' hv2 s).elim
    | sndBeta _ _ => rfl
  | letStep s ih =>
    cases h2 with
    | letStep s2 => exact congrArg (Expr.letE · _) (ih s2)
    | letBeta hv => exact (val_no_step' hv s).elim
  | letBeta hv =>
    cases h2 with
    | letStep s2 => exact (val_no_step' hv s2).elim
    | letBeta _ => rfl
  | ownStep s ih =>
    cases h2 with
    | ownStep s2 => exact congrArg Expr.own (ih s2)
  | moveStep s ih =>
    cases h2 with
    | moveStep s2 => exact congrArg Expr.move (ih s2)
    | moveBeta hv =>
      cases s with
      | ownStep s => exact (val_no_step' hv s).elim
  | moveBeta hv =>
    cases h2 with
    | moveStep s2 =>
      cases s2 with
      | ownStep s => exact (val_no_step' hv s).elim
    | moveBeta _ => rfl
  | iteStep s ih =>
    cases h2 with
    | iteStep s2 => exact congrArg (fun c => Expr.ite c _ _) (ih s2)
    | iteTrue => cases s
    | iteFalse => cases s
  | iteTrue =>
    cases h2 with
    | iteStep s2 => cases s2
    | iteTrue => rfl
  | iteFalse =>
    cases h2 with
    | iteStep s2 => cases s2
    | iteFalse => rfl

-- ══════════════════════════════════════════════════════════════
-- SECTION 7 : TYPING CONTEXTS (affine splitting)
-- ══════════════════════════════════════════════════════════════

abbrev Ctx := List (Option Ty)

inductive CtxSplit : Ctx → Ctx → Ctx → Prop where
  | nil   : CtxSplit [] [] []
  | left  : CtxSplit Γ Γ₁ Γ₂ →
            CtxSplit (some τ :: Γ) (some τ :: Γ₁) (none :: Γ₂)
  | right : CtxSplit Γ Γ₁ Γ₂ →
            CtxSplit (some τ :: Γ) (none :: Γ₁) (some τ :: Γ₂)
  | none  : CtxSplit Γ Γ₁ Γ₂ →
            CtxSplit (none :: Γ) (none :: Γ₁) (none :: Γ₂)

def ctxEmpty : Ctx → Prop :=
  fun Γ => ∀ i, Γ.get? i = some none ∨ Γ.get? i = Option.none

def ctxSingleton (Γ : Ctx) (i : Nat) (τ : Ty) : Prop :=
  Γ.get? i = some (some τ) ∧
  ∀ j, j ≠ i → (Γ.get? j = some none ∨ Γ.get? j = Option.none)

-- ══════════════════════════════════════════════════════════════
-- SECTION 8 : TYPING RULES
-- ══════════════════════════════════════════════════════════════

inductive HasType : Ctx → Expr → Ty → Prop where
  | var    : ctxSingleton Γ i τ → HasType Γ (Expr.var i) τ
  | unit   : ctxEmpty Γ → HasType Γ Expr.unit Ty.unit
  | natLit : ctxEmpty Γ → HasType Γ (Expr.natLit n) Ty.nat
  | boolLit: ctxEmpty Γ → HasType Γ (Expr.boolLit b) Ty.bool
  | lam    : HasType (some τ₁ :: Γ) body τ₂ →
             HasType Γ (Expr.lam τ₁ body) (Ty.fn τ₁ τ₂)
  | app    : CtxSplit Γ Γ₁ Γ₂ → HasType Γ₁ f (Ty.fn τ₁ τ₂) → HasType Γ₂ a τ₁ →
             HasType Γ (Expr.app f a) τ₂
  | pair   : CtxSplit Γ Γ₁ Γ₂ → HasType Γ₁ e₁ τ₁ → HasType Γ₂ e₂ τ₂ →
             HasType Γ (Expr.pair e₁ e₂) (Ty.prod τ₁ τ₂)
  | fst    : HasType Γ e (Ty.prod τ₁ τ₂) → HasType Γ (Expr.fst e) τ₁
  | snd    : HasType Γ e (Ty.prod τ₁ τ₂) → HasType Γ (Expr.snd e) τ₂
  | letE   : CtxSplit Γ Γ₁ Γ₂ → HasType Γ₁ e₁ τ₁ → HasType (some τ₁ :: Γ₂) e₂ τ₂ →
             HasType Γ (Expr.letE e₁ e₂) τ₂
  | own    : HasType Γ e τ → HasType Γ (Expr.own e) (Ty.owned τ)
  | move   : HasType Γ e (Ty.owned τ) → HasType Γ (Expr.move e) τ
  | ite    : CtxSplit Γ Γ₁ Γ₂ → HasType Γ₁ c Ty.bool →
             HasType Γ₂ t τ → HasType Γ₂ f τ →
             HasType Γ (Expr.ite c t f) τ

-- ══════════════════════════════════════════════════════════════
-- SECTION 9 : CONTEXT SPLIT PROPERTIES
-- ══════════════════════════════════════════════════════════════

theorem CtxSplit.len_left : CtxSplit Γ Γ₁ Γ₂ → Γ₁.length = Γ.length := by
  intro h; induction h with
  | nil => rfl
  | left _ ih | right _ ih | none _ ih => simp [List.length_cons, ih]

theorem CtxSplit.len_right : CtxSplit Γ Γ₁ Γ₂ → Γ₂.length = Γ.length := by
  intro h; induction h with
  | nil => rfl
  | left _ ih | right _ ih | none _ ih => simp [List.length_cons, ih]

theorem CtxSplit.symm : CtxSplit Γ Γ₁ Γ₂ → CtxSplit Γ Γ₂ Γ₁ := by
  intro h; induction h with
  | nil => exact CtxSplit.nil
  | left _ ih => exact CtxSplit.right ih
  | right _ ih => exact CtxSplit.left ih
  | none _ ih => exact CtxSplit.none ih

theorem CtxSplit.nil_inv : CtxSplit [] Γ₁ Γ₂ → Γ₁ = [] ∧ Γ₂ = [] := by
  intro h; cases h; exact ⟨rfl, rfl⟩

-- ══════════════════════════════════════════════════════════════
-- SECTION 10 : CANONICAL FORMS
-- ══════════════════════════════════════════════════════════════

theorem canonical_unit : IsValue e → HasType Γ e Ty.unit → e = Expr.unit := by
  intro hv ht
  cases hv with
  | unit => rfl
  | natLit => cases ht
  | boolLit => cases ht
  | lam => cases ht
  | pair _ _ => cases ht
  | own _ => cases ht

theorem canonical_nat : IsValue e → HasType Γ e Ty.nat → ∃ n, e = Expr.natLit n := by
  intro hv ht
  cases hv with
  | natLit => exact ⟨_, rfl⟩
  | unit => cases ht
  | boolLit => cases ht
  | lam => cases ht
  | pair _ _ => cases ht
  | own _ => cases ht

theorem canonical_bool : IsValue e → HasType Γ e Ty.bool → ∃ b, e = Expr.boolLit b := by
  intro hv ht
  cases hv with
  | boolLit => exact ⟨_, rfl⟩
  | unit => cases ht
  | natLit => cases ht
  | lam => cases ht
  | pair _ _ => cases ht
  | own _ => cases ht

theorem canonical_fn : IsValue e → HasType Γ e (Ty.fn τ₁ τ₂) →
    ∃ body, e = Expr.lam τ₁ body := by
  intro hv ht
  cases hv with
  | lam => cases ht; exact ⟨_, rfl⟩
  | unit => cases ht
  | natLit => cases ht
  | boolLit => cases ht
  | pair _ _ => cases ht
  | own _ => cases ht

theorem canonical_prod : IsValue e → HasType Γ e (Ty.prod τ₁ τ₂) →
    ∃ v₁ v₂, e = Expr.pair v₁ v₂ ∧ IsValue v₁ ∧ IsValue v₂ := by
  intro hv ht
  cases hv with
  | pair h1 h2 => cases ht; exact ⟨_, _, rfl, h1, h2⟩
  | unit => cases ht
  | natLit => cases ht
  | boolLit => cases ht
  | lam => cases ht
  | own _ => cases ht

theorem canonical_owned : IsValue e → HasType Γ e (Ty.owned τ) →
    ∃ v, e = Expr.own v ∧ IsValue v := by
  intro hv ht
  cases hv with
  | own h => cases ht; exact ⟨_, rfl, h⟩
  | unit => cases ht
  | natLit => cases ht
  | boolLit => cases ht
  | lam => cases ht
  | pair _ _ => cases ht

-- ══════════════════════════════════════════════════════════════
-- SECTION 11 : PROGRESS
-- ══════════════════════════════════════════════════════════════

theorem progress : HasType [] e τ → IsValue e ∨ ∃ e', Step e e' := by
  intro ht
  generalize hΓ : ([] : Ctx) = Γ at ht
  induction ht with
  | var hs => subst hΓ; exfalso; obtain ⟨h, _⟩ := hs; simp at h
  | unit _ => exact Or.inl IsValue.unit
  | natLit _ => exact Or.inl IsValue.natLit
  | boolLit _ => exact Or.inl IsValue.boolLit
  | lam _ _ => exact Or.inl IsValue.lam
  | app hsplit htf hta ihf iha =>
    subst hΓ; cases hsplit with
    | nil =>
      match ihf rfl with
      | Or.inl hvf =>
        match iha rfl with
        | Or.inl hva =>
          obtain ⟨body, rfl⟩ := canonical_fn hvf htf
          exact Or.inr ⟨_, Step.appBeta hva⟩
        | Or.inr ⟨a', hsa⟩ => exact Or.inr ⟨_, Step.appArg hvf hsa⟩
      | Or.inr ⟨f', hsf⟩ => exact Or.inr ⟨_, Step.appFun hsf⟩
  | pair hsplit ht1 ht2 ih1 ih2 =>
    subst hΓ; cases hsplit with
    | nil =>
      match ih1 rfl with
      | Or.inl hv1 =>
        match ih2 rfl with
        | Or.inl hv2 => exact Or.inl (IsValue.pair hv1 hv2)
        | Or.inr ⟨e', hs⟩ => exact Or.inr ⟨_, Step.pairR hv1 hs⟩
      | Or.inr ⟨e', hs⟩ => exact Or.inr ⟨_, Step.pairL hs⟩
  | fst ht ih =>
    subst hΓ
    match ih rfl with
    | Or.inl hv =>
      obtain ⟨v₁, v₂, rfl, hv1, hv2⟩ := canonical_prod hv ht
      exact Or.inr ⟨_, Step.fstBeta hv1 hv2⟩
    | Or.inr ⟨e', hs⟩ => exact Or.inr ⟨_, Step.fstStep hs⟩
  | snd ht ih =>
    subst hΓ
    match ih rfl with
    | Or.inl hv =>
      obtain ⟨v₁, v₂, rfl, hv1, hv2⟩ := canonical_prod hv ht
      exact Or.inr ⟨_, Step.sndBeta hv1 hv2⟩
    | Or.inr ⟨e', hs⟩ => exact Or.inr ⟨_, Step.sndStep hs⟩
  | letE hsplit ht1 _ ih1 _ =>
    subst hΓ; cases hsplit with
    | nil =>
      match ih1 rfl with
      | Or.inl hv => exact Or.inr ⟨_, Step.letBeta hv⟩
      | Or.inr ⟨e', hs⟩ => exact Or.inr ⟨_, Step.letStep hs⟩
  | own ht ih =>
    subst hΓ
    match ih rfl with
    | Or.inl hv => exact Or.inl (IsValue.own hv)
    | Or.inr ⟨e', hs⟩ => exact Or.inr ⟨_, Step.ownStep hs⟩
  | move ht ih =>
    subst hΓ
    match ih rfl with
    | Or.inl hv =>
      obtain ⟨v, rfl, hv'⟩ := canonical_owned hv ht
      exact Or.inr ⟨_, Step.moveBeta hv'⟩
    | Or.inr ⟨e', hs⟩ => exact Or.inr ⟨_, Step.moveStep hs⟩
  | ite hsplit htc _ _ ihc _ _ =>
    subst hΓ; cases hsplit with
    | nil =>
      match ihc rfl with
      | Or.inl hv =>
        obtain ⟨b, rfl⟩ := canonical_bool hv htc
        match b with
        | true => exact Or.inr ⟨_, Step.iteTrue⟩
        | false => exact Or.inr ⟨_, Step.iteFalse⟩
      | Or.inr ⟨c', hsc⟩ => exact Or.inr ⟨_, Step.iteStep hsc⟩

-- ══════════════════════════════════════════════════════════════
-- SECTION 12 : TYPE SAFETY
-- ══════════════════════════════════════════════════════════════

theorem type_safety : HasType [] e τ → IsValue e ∨ ∃ e', Step e e' :=
  progress

-- ══════════════════════════════════════════════════════════════
-- SECTION 13 : MULTI-STEP
-- ══════════════════════════════════════════════════════════════

inductive MultiStep : Expr → Expr → Prop where
  | refl  : MultiStep e e
  | step  : Step e₁ e₂ → MultiStep e₂ e₃ → MultiStep e₁ e₃

theorem MultiStep.single : Step e₁ e₂ → MultiStep e₁ e₂ :=
  fun h => MultiStep.step h MultiStep.refl

theorem MultiStep.trans : MultiStep e₁ e₂ → MultiStep e₂ e₃ → MultiStep e₁ e₃ := by
  intro h₁ h₂
  induction h₁ with
  | refl => exact h₂
  | step s _ ih => exact MultiStep.step s (ih h₂)

-- ══════════════════════════════════════════════════════════════
-- SECTION 14 : NORMAL FORMS
-- ══════════════════════════════════════════════════════════════

def NormalForm (e : Expr) : Prop := ¬ ∃ e', Step e e'

theorem value_is_normal : IsValue e → NormalForm e :=
  fun hv ⟨_, hs⟩ => value_no_step hv hs

theorem normal_closed_is_value : HasType [] e τ → NormalForm e → IsValue e := by
  intro ht hn
  have h := progress ht
  cases h with
  | inl hv => exact hv
  | inr hex => exact absurd hex hn

-- ══════════════════════════════════════════════════════════════
-- SECTION 15 : EXPRESSION & TYPE SIZE
-- ══════════════════════════════════════════════════════════════

def exprSize : Expr → Nat
  | Expr.var _       => 1
  | Expr.unit        => 1
  | Expr.natLit _    => 1
  | Expr.boolLit _   => 1
  | Expr.lam _ body  => 1 + exprSize body
  | Expr.app f a     => 1 + exprSize f + exprSize a
  | Expr.pair a b    => 1 + exprSize a + exprSize b
  | Expr.fst e       => 1 + exprSize e
  | Expr.snd e       => 1 + exprSize e
  | Expr.letE a b    => 1 + exprSize a + exprSize b
  | Expr.own e       => 1 + exprSize e
  | Expr.move e      => 1 + exprSize e
  | Expr.ite c t f   => 1 + exprSize c + exprSize t + exprSize f

def exprDepth : Expr → Nat
  | Expr.var _       => 0
  | Expr.unit        => 0
  | Expr.natLit _    => 0
  | Expr.boolLit _   => 0
  | Expr.lam _ body  => 1 + exprDepth body
  | Expr.app f a     => 1 + max (exprDepth f) (exprDepth a)
  | Expr.pair a b    => 1 + max (exprDepth a) (exprDepth b)
  | Expr.fst e       => 1 + exprDepth e
  | Expr.snd e       => 1 + exprDepth e
  | Expr.letE a b    => 1 + max (exprDepth a) (exprDepth b)
  | Expr.own e       => 1 + exprDepth e
  | Expr.move e      => 1 + exprDepth e
  | Expr.ite c t f   => 1 + max (exprDepth c) (max (exprDepth t) (exprDepth f))

theorem exprSize_pos : ∀ e, 0 < exprSize e := by
  intro e; cases e <;> simp [exprSize] <;> omega

def tySize : Ty → Nat
  | Ty.unit     => 1
  | Ty.nat      => 1
  | Ty.bool     => 1
  | Ty.fn a b   => 1 + tySize a + tySize b
  | Ty.prod a b => 1 + tySize a + tySize b
  | Ty.owned t  => 1 + tySize t

theorem tySize_pos : ∀ τ, 0 < tySize τ := by
  intro τ; cases τ <;> simp [tySize] <;> omega

-- ══════════════════════════════════════════════════════════════
-- SECTION 16 : TYPE PROPERTIES
-- ══════════════════════════════════════════════════════════════

def isBaseTy : Ty → Bool
  | Ty.unit | Ty.nat | Ty.bool => true
  | _ => false

def isArrowTy : Ty → Bool
  | Ty.fn _ _ => true
  | _ => false

theorem base_not_arrow : isBaseTy τ = true → isArrowTy τ = false := by
  intro h; cases τ <;> simp [isBaseTy, isArrowTy] at *

-- ══════════════════════════════════════════════════════════════
-- SECTION 17 : MULTISTEP CONGRUENCES
-- ══════════════════════════════════════════════════════════════

theorem ms_app_fun : MultiStep f f' → MultiStep (Expr.app f a) (Expr.app f' a) := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.appFun s) ih

theorem ms_pair_left : MultiStep e₁ e₁' → MultiStep (Expr.pair e₁ e₂) (Expr.pair e₁' e₂) := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.pairL s) ih

theorem ms_fst : MultiStep e e' → MultiStep (Expr.fst e) (Expr.fst e') := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.fstStep s) ih

theorem ms_snd : MultiStep e e' → MultiStep (Expr.snd e) (Expr.snd e') := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.sndStep s) ih

theorem ms_move : MultiStep e e' → MultiStep (Expr.move e) (Expr.move e') := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.moveStep s) ih

theorem ms_own : MultiStep e e' → MultiStep (Expr.own e) (Expr.own e') := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.ownStep s) ih

theorem ms_letE : MultiStep e₁ e₁' → MultiStep (Expr.letE e₁ e₂) (Expr.letE e₁' e₂) := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.letStep s) ih

theorem ms_ite : MultiStep c c' → MultiStep (Expr.ite c t f) (Expr.ite c' t f) := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.iteStep s) ih

-- ══════════════════════════════════════════════════════════════
-- SECTION 18 : FREE VARIABLE COUNTING
-- ══════════════════════════════════════════════════════════════

def freeCount (i : Nat) : Expr → Nat
  | Expr.var n       => if n = i then 1 else 0
  | Expr.unit        => 0
  | Expr.natLit _    => 0
  | Expr.boolLit _   => 0
  | Expr.lam _ body  => freeCount (i + 1) body
  | Expr.app f a     => freeCount i f + freeCount i a
  | Expr.pair a b    => freeCount i a + freeCount i b
  | Expr.fst e       => freeCount i e
  | Expr.snd e       => freeCount i e
  | Expr.letE a b    => freeCount i a + freeCount (i + 1) b
  | Expr.own e       => freeCount i e
  | Expr.move e      => freeCount i e
  | Expr.ite c t f   => freeCount i c + freeCount i t + freeCount i f

def isClosed (e : Expr) : Prop := ∀ i, freeCount i e = 0

theorem unit_closed : isClosed Expr.unit := fun _ => rfl
theorem nat_closed : isClosed (Expr.natLit n) := fun _ => rfl
theorem bool_closed : isClosed (Expr.boolLit b) := fun _ => rfl

-- ══════════════════════════════════════════════════════════════
-- SECTION 19 : TYPE INJECTIVITY / DISJOINTNESS
-- ══════════════════════════════════════════════════════════════

theorem fn_inj : Ty.fn a₁ b₁ = Ty.fn a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
  intro h; injection h; exact ⟨‹_›, ‹_›⟩

theorem prod_inj : Ty.prod a₁ b₁ = Ty.prod a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
  intro h; injection h; exact ⟨‹_›, ‹_›⟩

theorem owned_inj : Ty.owned a = Ty.owned b → a = b := by intro h; injection h

theorem fn_ne_unit : Ty.fn a b ≠ Ty.unit := by intro h; injection h
theorem fn_ne_nat : Ty.fn a b ≠ Ty.nat := by intro h; injection h
theorem fn_ne_bool : Ty.fn a b ≠ Ty.bool := by intro h; injection h
theorem prod_ne_fn : Ty.prod a b ≠ Ty.fn c d := by intro h; injection h
theorem owned_ne_unit : Ty.owned a ≠ Ty.unit := by intro h; injection h
theorem owned_ne_nat : Ty.owned a ≠ Ty.nat := by intro h; injection h
theorem owned_ne_bool : Ty.owned a ≠ Ty.bool := by intro h; injection h
theorem owned_ne_fn : Ty.owned a ≠ Ty.fn b c := by intro h; injection h
theorem owned_ne_prod : Ty.owned a ≠ Ty.prod b c := by intro h; injection h

-- ══════════════════════════════════════════════════════════════
-- SECTION 20 : EXPR INJECTIVITY
-- ══════════════════════════════════════════════════════════════

theorem lam_inj : Expr.lam τ₁ b₁ = Expr.lam τ₂ b₂ → τ₁ = τ₂ ∧ b₁ = b₂ := by
  intro h; injection h; exact ⟨‹_›, ‹_›⟩

theorem app_inj : Expr.app f₁ a₁ = Expr.app f₂ a₂ → f₁ = f₂ ∧ a₁ = a₂ := by
  intro h; injection h; exact ⟨‹_›, ‹_›⟩

theorem pair_inj : Expr.pair a₁ b₁ = Expr.pair a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
  intro h; injection h; exact ⟨‹_›, ‹_›⟩

theorem var_inj : Expr.var n₁ = Expr.var n₂ → n₁ = n₂ := by intro h; injection h

theorem own_inj : Expr.own e₁ = Expr.own e₂ → e₁ = e₂ := by intro h; injection h

theorem ite_inj : Expr.ite c₁ t₁ f₁ = Expr.ite c₂ t₂ f₂ →
    c₁ = c₂ ∧ t₁ = t₂ ∧ f₁ = f₂ := by
  intro h; injection h; exact ⟨‹_›, ‹_›, ‹_›⟩

-- ══════════════════════════════════════════════════════════════
-- SECTION 21 : SUBST PROPERTIES
-- ══════════════════════════════════════════════════════════════

theorem subst_unit_eq : subst j s Expr.unit = Expr.unit := by
  simp [subst]

theorem subst_nat_eq : subst j s (Expr.natLit n) = Expr.natLit n := by
  simp [subst]

theorem subst_bool_eq : subst j s (Expr.boolLit b) = Expr.boolLit b := by
  simp [subst]

theorem subst_var_hit : subst j s (Expr.var j) = s := by
  simp [subst, substVar]

theorem subst_var_miss (h : n ≠ j) : subst j s (Expr.var n) = Expr.var n := by
  simp [subst, substVar, h]

end Affine
