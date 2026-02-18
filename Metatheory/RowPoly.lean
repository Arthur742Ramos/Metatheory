/-
  Armada 646: Row Polymorphism & Extensible Records

  A type system with extensible records and row-based typing.
  Uses List (Label × Ty) as rows to avoid mutual inductives.
-/

namespace RowPoly

-- ══════════════════════════════════════════════════════════════
-- SECTION 1 : TYPES
-- ══════════════════════════════════════════════════════════════

abbrev Label := Nat

inductive Ty where
  | unit   : Ty
  | nat    : Ty
  | bool   : Ty
  | fn     : Ty → Ty → Ty
  | record : List (Label × Ty) → Ty

abbrev Row := List (Label × Ty)

-- ══════════════════════════════════════════════════════════════
-- SECTION 2 : ROW OPERATIONS
-- ══════════════════════════════════════════════════════════════

def rowLookup : Row → Label → Option Ty
  | [], _ => none
  | (l, τ) :: r, l' => if l = l' then some τ else rowLookup r l'

def rowRemove : Row → Label → Row
  | [], _ => []
  | (l, τ) :: r, l' => if l = l' then r else (l, τ) :: rowRemove r l'

def rowHasLabel : Row → Label → Bool
  | [], _ => false
  | (l, _) :: r, l' => l == l' || rowHasLabel r l'

def rowWidth : Row → Nat := List.length

def rowLabels : Row → List Label := List.map Prod.fst

-- ══════════════════════════════════════════════════════════════
-- SECTION 3 : EXPRESSIONS
-- ══════════════════════════════════════════════════════════════

inductive Expr where
  | var      : Nat → Expr
  | unit     : Expr
  | natLit   : Nat → Expr
  | boolLit  : Bool → Expr
  | lam      : Ty → Expr → Expr
  | app      : Expr → Expr → Expr
  | empty    : Expr
  | extend   : Expr → Label → Expr → Expr  -- { l = v | rec }
  | sel      : Expr → Label → Expr          -- e.l
  | restrict : Expr → Label → Expr          -- e \ l
  | ite      : Expr → Expr → Expr → Expr
  | letE     : Expr → Expr → Expr

-- ══════════════════════════════════════════════════════════════
-- SECTION 4 : VALUES
-- ══════════════════════════════════════════════════════════════

inductive IsValue : Expr → Prop where
  | unit    : IsValue Expr.unit
  | natLit  : IsValue (Expr.natLit n)
  | boolLit : IsValue (Expr.boolLit b)
  | lam     : IsValue (Expr.lam τ body)
  | empty   : IsValue Expr.empty
  | extend  : IsValue v → IsValue rec → IsValue (Expr.extend rec l v)

theorem isValue_not_var : ¬ IsValue (Expr.var n) := by intro h; cases h
theorem isValue_not_app : ¬ IsValue (Expr.app e₁ e₂) := by intro h; cases h
theorem isValue_not_sel : ¬ IsValue (Expr.sel e l) := by intro h; cases h
theorem isValue_not_restrict : ¬ IsValue (Expr.restrict e l) := by intro h; cases h
theorem isValue_not_ite : ¬ IsValue (Expr.ite c t f) := by intro h; cases h
theorem isValue_not_letE : ¬ IsValue (Expr.letE e₁ e₂) := by intro h; cases h

-- ══════════════════════════════════════════════════════════════
-- SECTION 5 : RECORD VALUE LOOKUP & REMOVE
-- ══════════════════════════════════════════════════════════════

inductive RecLookup : Expr → Label → Expr → Prop where
  | here  : l₁ = l₂ → RecLookup (Expr.extend rec l₁ v) l₂ v
  | there : l₁ ≠ l₂ → RecLookup rec l₂ v →
            RecLookup (Expr.extend rec l₁ w) l₂ v

inductive RecRemove : Expr → Label → Expr → Prop where
  | here  : l₁ = l₂ → RecRemove (Expr.extend rec l₁ v) l₂ rec
  | there : l₁ ≠ l₂ → RecRemove rec l₂ rec' →
            RecRemove (Expr.extend rec l₁ v) l₂ (Expr.extend rec' l₁ v)

-- ══════════════════════════════════════════════════════════════
-- SECTION 6 : SUBSTITUTION
-- ══════════════════════════════════════════════════════════════

def substVar (j : Nat) (s : Expr) (n : Nat) : Expr :=
  if n = j then s else Expr.var n

def subst (j : Nat) (s : Expr) : Expr → Expr
  | Expr.var n          => substVar j s n
  | Expr.unit           => Expr.unit
  | Expr.natLit n       => Expr.natLit n
  | Expr.boolLit b      => Expr.boolLit b
  | Expr.lam τ body     => Expr.lam τ (subst (j + 1) s body)
  | Expr.app f a        => Expr.app (subst j s f) (subst j s a)
  | Expr.empty          => Expr.empty
  | Expr.extend rec l v => Expr.extend (subst j s rec) l (subst j s v)
  | Expr.sel e l        => Expr.sel (subst j s e) l
  | Expr.restrict e l   => Expr.restrict (subst j s e) l
  | Expr.ite c t f      => Expr.ite (subst j s c) (subst j s t) (subst j s f)
  | Expr.letE a b       => Expr.letE (subst j s a) (subst (j + 1) s b)

-- ══════════════════════════════════════════════════════════════
-- SECTION 7 : SMALL-STEP SEMANTICS
-- ══════════════════════════════════════════════════════════════

inductive Step : Expr → Expr → Prop where
  | appFun      : Step e₁ e₁' → Step (Expr.app e₁ e₂) (Expr.app e₁' e₂)
  | appArg      : IsValue v₁ → Step e₂ e₂' → Step (Expr.app v₁ e₂) (Expr.app v₁ e₂')
  | appBeta     : IsValue v → Step (Expr.app (Expr.lam τ body) v) (subst 0 v body)
  | extendRec   : Step rec rec' → Step (Expr.extend rec l v) (Expr.extend rec' l v)
  | extendVal   : IsValue rec → Step v v' → Step (Expr.extend rec l v) (Expr.extend rec l v')
  | selStep     : Step e e' → Step (Expr.sel e l) (Expr.sel e' l)
  | selBeta     : IsValue e → RecLookup e l v → Step (Expr.sel e l) v
  | restrictStep : Step e e' → Step (Expr.restrict e l) (Expr.restrict e' l)
  | restrictBeta : IsValue e → RecRemove e l e' → Step (Expr.restrict e l) e'
  | iteStep     : Step c c' → Step (Expr.ite c t f) (Expr.ite c' t f)
  | iteTrue     : Step (Expr.ite (Expr.boolLit true) t f) t
  | iteFalse    : Step (Expr.ite (Expr.boolLit false) t f) f
  | letStep     : Step e₁ e₁' → Step (Expr.letE e₁ e₂) (Expr.letE e₁' e₂)
  | letBeta     : IsValue v → Step (Expr.letE v e₂) (subst 0 v e₂)

-- ══════════════════════════════════════════════════════════════
-- SECTION 8 : VALUE / STEP EXCLUSION
-- ══════════════════════════════════════════════════════════════

theorem value_no_step : IsValue e → Step e e' → False := by
  intro hv hs
  induction hv generalizing e' with
  | unit => cases hs
  | natLit => cases hs
  | boolLit => cases hs
  | lam => cases hs
  | empty => cases hs
  | extend hv_v hv_rec ih_v ih_rec =>
    cases hs with
    | extendRec hs' => exact ih_rec hs'
    | extendVal _ hs' => exact ih_v hs'

theorem step_not_value : Step e e' → ¬ IsValue e :=
  fun hs hv => value_no_step hv hs

-- ══════════════════════════════════════════════════════════════
-- SECTION 9 : MULTI-STEP
-- ══════════════════════════════════════════════════════════════

inductive MultiStep : Expr → Expr → Prop where
  | refl  : MultiStep e e
  | step  : Step e₁ e₂ → MultiStep e₂ e₃ → MultiStep e₁ e₃

theorem MultiStep.single : Step e₁ e₂ → MultiStep e₁ e₂ :=
  fun h => MultiStep.step h MultiStep.refl

theorem MultiStep.trans : MultiStep e₁ e₂ → MultiStep e₂ e₃ → MultiStep e₁ e₃ := by
  intro h₁ h₂; induction h₁ with
  | refl => exact h₂
  | step s _ ih => exact MultiStep.step s (ih h₂)

-- ══════════════════════════════════════════════════════════════
-- SECTION 10 : TYPING
-- ══════════════════════════════════════════════════════════════

abbrev Ctx := List Ty

/-- Typed row membership -/
inductive RowHas : Row → Label → Ty → Prop where
  | here  : l₁ = l₂ → RowHas ((l₁, τ) :: r) l₂ τ
  | there : l₁ ≠ l₂ → RowHas r l₂ τ → RowHas ((l₁, τ') :: r) l₂ τ

inductive HasType : Ctx → Expr → Ty → Prop where
  | var      : Γ.get? i = some τ → HasType Γ (Expr.var i) τ
  | unit     : HasType Γ Expr.unit Ty.unit
  | natLit   : HasType Γ (Expr.natLit n) Ty.nat
  | boolLit  : HasType Γ (Expr.boolLit b) Ty.bool
  | lam      : HasType (τ₁ :: Γ) body τ₂ → HasType Γ (Expr.lam τ₁ body) (Ty.fn τ₁ τ₂)
  | app      : HasType Γ f (Ty.fn τ₁ τ₂) → HasType Γ a τ₁ →
               HasType Γ (Expr.app f a) τ₂
  | empty    : HasType Γ Expr.empty (Ty.record [])
  | extend   : HasType Γ rec (Ty.record r) → HasType Γ v τ →
               HasType Γ (Expr.extend rec l v) (Ty.record ((l, τ) :: r))
  | sel      : HasType Γ e (Ty.record r) → RowHas r l τ →
               HasType Γ (Expr.sel e l) τ
  | restrict : HasType Γ e (Ty.record ((l, τ) :: r)) →
               HasType Γ (Expr.restrict e l) (Ty.record r)
  | ite      : HasType Γ c Ty.bool → HasType Γ t τ → HasType Γ f τ →
               HasType Γ (Expr.ite c t f) τ
  | letE     : HasType Γ e₁ τ₁ → HasType (τ₁ :: Γ) e₂ τ₂ →
               HasType Γ (Expr.letE e₁ e₂) τ₂

-- ══════════════════════════════════════════════════════════════
-- SECTION 11 : ROW PROPERTIES
-- ══════════════════════════════════════════════════════════════

theorem rowLookup_nil : rowLookup [] l = none := rfl
theorem rowLookup_head_eq : rowLookup ((l, τ) :: r) l = some τ := by simp [rowLookup]
theorem rowRemove_nil : rowRemove [] l = [] := rfl

theorem rowLookup_head_ne (h : l₁ ≠ l₂) :
    rowLookup ((l₁, τ) :: r) l₂ = rowLookup r l₂ := by
  simp [rowLookup, h]

-- ══════════════════════════════════════════════════════════════
-- SECTION 12 : CANONICAL FORMS
-- ══════════════════════════════════════════════════════════════

theorem canonical_unit : IsValue e → HasType Γ e Ty.unit → e = Expr.unit := by
  intro hv ht; cases hv with
  | unit => rfl
  | natLit => cases ht
  | boolLit => cases ht
  | lam => cases ht
  | empty => cases ht
  | extend _ _ => cases ht

theorem canonical_nat : IsValue e → HasType Γ e Ty.nat → ∃ n, e = Expr.natLit n := by
  intro hv ht; cases hv with
  | natLit => exact ⟨_, rfl⟩
  | unit => cases ht
  | boolLit => cases ht
  | lam => cases ht
  | empty => cases ht
  | extend _ _ => cases ht

theorem canonical_bool : IsValue e → HasType Γ e Ty.bool → ∃ b, e = Expr.boolLit b := by
  intro hv ht; cases hv with
  | boolLit => exact ⟨_, rfl⟩
  | unit => cases ht
  | natLit => cases ht
  | lam => cases ht
  | empty => cases ht
  | extend _ _ => cases ht

theorem canonical_fn : IsValue e → HasType Γ e (Ty.fn τ₁ τ₂) →
    ∃ body, e = Expr.lam τ₁ body := by
  intro hv ht; cases hv with
  | lam => cases ht; exact ⟨_, rfl⟩
  | unit => cases ht
  | natLit => cases ht
  | boolLit => cases ht
  | empty => cases ht
  | extend _ _ => cases ht

-- ══════════════════════════════════════════════════════════════
-- SECTION 13 : RECORD LOOKUP EXISTENCE
-- ══════════════════════════════════════════════════════════════

theorem record_value_has_lookup
    (hv : IsValue e) (ht : HasType Γ e (Ty.record r)) (hr : RowHas r l τ) :
    ∃ v, RecLookup e l v := by
  induction hv generalizing r l τ Γ with
  | empty =>
    cases ht with | empty => cases hr
  | extend hv_v hv_rec ih_v ih_rec =>
    cases ht with
    | extend ht_rec ht_v =>
      cases hr with
      | here heq => exact ⟨_, RecLookup.here heq⟩
      | there hne hr' =>
        obtain ⟨v, hlk⟩ := ih_rec ht_rec hr'
        exact ⟨v, RecLookup.there hne hlk⟩
  | unit => cases ht
  | natLit => cases ht
  | boolLit => cases ht
  | lam => cases ht

theorem record_value_has_remove
    (hv : IsValue e) (ht : HasType Γ e (Ty.record ((l, τ) :: r))) :
    ∃ e', RecRemove e l e' := by
  cases hv with
  | extend hv_v hv_rec =>
    cases ht with
    | extend ht_rec ht_v => exact ⟨_, RecRemove.here rfl⟩
  | empty => cases ht
  | unit => cases ht
  | natLit => cases ht
  | boolLit => cases ht
  | lam => cases ht

-- ══════════════════════════════════════════════════════════════
-- SECTION 14 : PROGRESS
-- ══════════════════════════════════════════════════════════════

theorem progress : HasType [] e τ → IsValue e ∨ ∃ e', Step e e' := by
  intro ht
  generalize hΓ : ([] : Ctx) = Γ at ht
  induction ht with
  | var h => subst hΓ; simp at h
  | unit => exact Or.inl IsValue.unit
  | natLit => exact Or.inl IsValue.natLit
  | boolLit => exact Or.inl IsValue.boolLit
  | lam _ _ => exact Or.inl IsValue.lam
  | app htf hta ihf iha =>
    subst hΓ
    match ihf rfl with
    | Or.inl hvf =>
      match iha rfl with
      | Or.inl hva =>
        obtain ⟨body, rfl⟩ := canonical_fn hvf htf
        exact Or.inr ⟨_, Step.appBeta hva⟩
      | Or.inr ⟨a', hsa⟩ => exact Or.inr ⟨_, Step.appArg hvf hsa⟩
    | Or.inr ⟨f', hsf⟩ => exact Or.inr ⟨_, Step.appFun hsf⟩
  | empty => exact Or.inl IsValue.empty
  | extend hte htv ihe ihv =>
    subst hΓ
    match ihe rfl with
    | Or.inl hve =>
      match ihv rfl with
      | Or.inl hvv => exact Or.inl (IsValue.extend hvv hve)
      | Or.inr ⟨v', hsv⟩ => exact Or.inr ⟨_, Step.extendVal hve hsv⟩
    | Or.inr ⟨e', hse⟩ => exact Or.inr ⟨_, Step.extendRec hse⟩
  | sel hte hr ihe =>
    subst hΓ
    match ihe rfl with
    | Or.inl hve =>
      obtain ⟨v, hlk⟩ := record_value_has_lookup hve hte hr
      exact Or.inr ⟨_, Step.selBeta hve hlk⟩
    | Or.inr ⟨e', hse⟩ => exact Or.inr ⟨_, Step.selStep hse⟩
  | restrict hte ihe =>
    subst hΓ
    match ihe rfl with
    | Or.inl hve =>
      obtain ⟨e', hrm⟩ := record_value_has_remove hve hte
      exact Or.inr ⟨_, Step.restrictBeta hve hrm⟩
    | Or.inr ⟨e', hse⟩ => exact Or.inr ⟨_, Step.restrictStep hse⟩
  | ite htc _ _ ihc _ _ =>
    subst hΓ
    match ihc rfl with
    | Or.inl hv =>
      obtain ⟨b, rfl⟩ := canonical_bool hv htc
      match b with
      | true => exact Or.inr ⟨_, Step.iteTrue⟩
      | false => exact Or.inr ⟨_, Step.iteFalse⟩
    | Or.inr ⟨c', hsc⟩ => exact Or.inr ⟨_, Step.iteStep hsc⟩
  | letE _ _ ih1 _ =>
    subst hΓ
    match ih1 rfl with
    | Or.inl hv => exact Or.inr ⟨_, Step.letBeta hv⟩
    | Or.inr ⟨e', hs⟩ => exact Or.inr ⟨_, Step.letStep hs⟩

-- ══════════════════════════════════════════════════════════════
-- SECTION 15 : TYPE SAFETY
-- ══════════════════════════════════════════════════════════════

theorem type_safety : HasType [] e τ → IsValue e ∨ ∃ e', Step e e' :=
  progress

-- ══════════════════════════════════════════════════════════════
-- SECTION 16 : NORMAL FORMS
-- ══════════════════════════════════════════════════════════════

def NormalForm (e : Expr) : Prop := ¬ ∃ e', Step e e'

theorem value_is_normal : IsValue e → NormalForm e :=
  fun hv ⟨_, hs⟩ => value_no_step hv hs

theorem normal_closed_is_value : HasType [] e τ → NormalForm e → IsValue e := by
  intro ht hn
  match progress ht with
  | Or.inl hv => exact hv
  | Or.inr hex => exact absurd hex hn

-- ══════════════════════════════════════════════════════════════
-- SECTION 17 : EXPRESSION SIZE
-- ══════════════════════════════════════════════════════════════

def exprSize : Expr → Nat
  | Expr.var _          => 1
  | Expr.unit           => 1
  | Expr.natLit _       => 1
  | Expr.boolLit _      => 1
  | Expr.lam _ body     => 1 + exprSize body
  | Expr.app f a        => 1 + exprSize f + exprSize a
  | Expr.empty          => 1
  | Expr.extend rec _ v => 1 + exprSize rec + exprSize v
  | Expr.sel e _        => 1 + exprSize e
  | Expr.restrict e _   => 1 + exprSize e
  | Expr.ite c t f      => 1 + exprSize c + exprSize t + exprSize f
  | Expr.letE a b       => 1 + exprSize a + exprSize b

theorem exprSize_pos : ∀ e, 0 < exprSize e := by
  intro e; cases e <;> simp [exprSize] <;> omega

-- ══════════════════════════════════════════════════════════════
-- SECTION 18 : TYPE SIZE
-- ══════════════════════════════════════════════════════════════

def tySize : Ty → Nat
  | Ty.unit     => 1
  | Ty.nat      => 1
  | Ty.bool     => 1
  | Ty.fn a b   => 1 + tySize a + tySize b
  | Ty.record _ => 1  -- simplified; avoids termination issues with nested

theorem tySize_pos : ∀ τ, 0 < tySize τ := by
  intro τ; cases τ <;> simp [tySize] <;> omega

-- ══════════════════════════════════════════════════════════════
-- SECTION 19 : TYPE INJECTIVITY / DISJOINTNESS
-- ══════════════════════════════════════════════════════════════

theorem fn_inj : Ty.fn a₁ b₁ = Ty.fn a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
  intro h; injection h; exact ⟨‹_›, ‹_›⟩

theorem record_inj : Ty.record r₁ = Ty.record r₂ → r₁ = r₂ := by
  intro h; injection h

theorem fn_ne_record : Ty.fn a b ≠ Ty.record r := by intro h; injection h
theorem fn_ne_unit : Ty.fn a b ≠ Ty.unit := by intro h; injection h
theorem fn_ne_nat : Ty.fn a b ≠ Ty.nat := by intro h; injection h
theorem fn_ne_bool : Ty.fn a b ≠ Ty.bool := by intro h; injection h
theorem record_ne_unit : Ty.record r ≠ Ty.unit := by intro h; injection h
theorem record_ne_nat : Ty.record r ≠ Ty.nat := by intro h; injection h
theorem record_ne_bool : Ty.record r ≠ Ty.bool := by intro h; injection h

-- ══════════════════════════════════════════════════════════════
-- SECTION 20 : MULTISTEP CONGRUENCES
-- ══════════════════════════════════════════════════════════════

theorem ms_app_fun : MultiStep f f' → MultiStep (Expr.app f a) (Expr.app f' a) := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.appFun s) ih

theorem ms_sel : MultiStep e e' → MultiStep (Expr.sel e l) (Expr.sel e' l) := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.selStep s) ih

theorem ms_extend_rec : MultiStep rec rec' →
    MultiStep (Expr.extend rec l v) (Expr.extend rec' l v) := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.extendRec s) ih

theorem ms_restrict : MultiStep e e' →
    MultiStep (Expr.restrict e l) (Expr.restrict e' l) := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.restrictStep s) ih

theorem ms_ite_cond : MultiStep c c' →
    MultiStep (Expr.ite c t f) (Expr.ite c' t f) := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.iteStep s) ih

theorem ms_letE : MultiStep e₁ e₁' →
    MultiStep (Expr.letE e₁ e₂) (Expr.letE e₁' e₂) := by
  intro h; induction h with
  | refl => exact MultiStep.refl
  | step s _ ih => exact MultiStep.step (Step.letStep s) ih

-- ══════════════════════════════════════════════════════════════
-- SECTION 21 : EXPR INJECTIVITY
-- ══════════════════════════════════════════════════════════════

theorem lam_inj : Expr.lam τ₁ b₁ = Expr.lam τ₂ b₂ → τ₁ = τ₂ ∧ b₁ = b₂ := by
  intro h; injection h; exact ⟨‹_›, ‹_›⟩

theorem app_inj : Expr.app f₁ a₁ = Expr.app f₂ a₂ → f₁ = f₂ ∧ a₁ = a₂ := by
  intro h; injection h; exact ⟨‹_›, ‹_›⟩

theorem var_inj : Expr.var n₁ = Expr.var n₂ → n₁ = n₂ := by intro h; injection h

theorem sel_inj : Expr.sel e₁ l₁ = Expr.sel e₂ l₂ → e₁ = e₂ ∧ l₁ = l₂ := by
  intro h; injection h; exact ⟨‹_›, ‹_›⟩

-- ══════════════════════════════════════════════════════════════
-- SECTION 22 : SUBST PROPERTIES
-- ══════════════════════════════════════════════════════════════

theorem subst_unit_eq : subst j s Expr.unit = Expr.unit := by simp [subst]
theorem subst_nat_eq : subst j s (Expr.natLit n) = Expr.natLit n := by simp [subst]
theorem subst_bool_eq : subst j s (Expr.boolLit b) = Expr.boolLit b := by simp [subst]
theorem subst_empty_eq : subst j s Expr.empty = Expr.empty := by simp [subst]
theorem subst_var_hit : subst j s (Expr.var j) = s := by simp [subst, substVar]
theorem subst_var_miss (h : n ≠ j) : subst j s (Expr.var n) = Expr.var n := by
  simp [subst, substVar, h]

-- ══════════════════════════════════════════════════════════════
-- SECTION 23 : STEP IMPOSSIBILITY
-- ══════════════════════════════════════════════════════════════

theorem step_ite_true_det : Step (Expr.ite (Expr.boolLit true) t f) e' → e' = t := by
  intro h; cases h with
  | iteStep s => cases s
  | iteTrue => rfl

theorem step_ite_false_det : Step (Expr.ite (Expr.boolLit false) t f) e' → e' = f := by
  intro h; cases h with
  | iteStep s => cases s
  | iteFalse => rfl

theorem no_step_unit : ¬ Step Expr.unit e' := by intro h; cases h
theorem no_step_nat : ¬ Step (Expr.natLit n) e' := by intro h; cases h
theorem no_step_bool : ¬ Step (Expr.boolLit b) e' := by intro h; cases h
theorem no_step_lam : ¬ Step (Expr.lam τ body) e' := by intro h; cases h
theorem no_step_empty : ¬ Step Expr.empty e' := by intro h; cases h

-- ══════════════════════════════════════════════════════════════
-- SECTION 24 : ROWHAS PROPERTIES
-- ══════════════════════════════════════════════════════════════

theorem RowHas.head : RowHas ((l, τ) :: r) l τ := RowHas.here rfl

theorem RowHas.tail (hne : l₁ ≠ l₂) (h : RowHas r l₂ τ) :
    RowHas ((l₁, τ') :: r) l₂ τ := RowHas.there hne h

-- ══════════════════════════════════════════════════════════════
-- SECTION 25 : RECLOOKUP / RECREMOVE PROPERTIES
-- ══════════════════════════════════════════════════════════════

theorem RecLookup_extend_here (rec : Expr) (l : Label) (v : Expr) :
    RecLookup (Expr.extend rec l v) l v :=
  RecLookup.here rfl

theorem RecRemove_extend_here (rec : Expr) (l : Label) (v : Expr) :
    RecRemove (Expr.extend rec l v) l rec :=
  RecRemove.here rfl

-- ══════════════════════════════════════════════════════════════
-- SECTION 26 : VALUE CONSTRUCTORS
-- ══════════════════════════════════════════════════════════════

theorem val_unit : IsValue Expr.unit := IsValue.unit
theorem val_nat : IsValue (Expr.natLit n) := IsValue.natLit
theorem val_bool : IsValue (Expr.boolLit b) := IsValue.boolLit
theorem val_lam : IsValue (Expr.lam τ body) := IsValue.lam
theorem val_empty : IsValue Expr.empty := IsValue.empty

-- ══════════════════════════════════════════════════════════════
-- SECTION 27 : ROW LOOKUP ↔ ROWHAS
-- ══════════════════════════════════════════════════════════════

theorem rowLookup_to_rowHas : rowLookup r l = some τ → RowHas r l τ := by
  intro h
  induction r with
  | nil => simp [rowLookup] at h
  | cons p rest ih =>
    obtain ⟨l', τ'⟩ := p
    simp only [rowLookup] at h
    by_cases heq : l' = l
    · simp [heq] at h; subst h; exact RowHas.here heq
    · simp [heq] at h; exact RowHas.there heq (ih h)

theorem rowHas_to_rowLookup : RowHas r l τ → rowLookup r l = some τ := by
  intro h
  induction h with
  | here heq => simp [rowLookup, heq]
  | there hne _ ih => simp [rowLookup, hne, ih]

-- ══════════════════════════════════════════════════════════════
-- SECTION 28 : ROW WIDTH PROPERTIES
-- ══════════════════════════════════════════════════════════════

theorem rowWidth_nil : rowWidth ([] : Row) = 0 := rfl
theorem rowWidth_cons : rowWidth (((l, τ) :: r) : Row) = 1 + rowWidth r := by
  simp [rowWidth, List.length]; omega

theorem rowLabels_nil : rowLabels ([] : Row) = [] := rfl
theorem rowLabels_cons : rowLabels (((l, τ) :: r) : Row) = l :: rowLabels r := by
  simp [rowLabels, List.map]

end RowPoly
