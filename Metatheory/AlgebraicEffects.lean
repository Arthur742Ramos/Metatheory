/-
  Armada 649: Algebraic Effects with Handlers & Effect Rows

  A type-and-effect system for algebraic effects: effect rows,
  handler typing, effect row subtyping, and small-step semantics.
-/

namespace AlgebraicEffects

-- ══════════════════════════════════════════════════════════════
-- SECTION 1 : EFFECT LABELS & ROWS
-- ══════════════════════════════════════════════════════════════

abbrev EffLabel := Nat
abbrev EffRow := List EffLabel

def effMember : EffLabel → EffRow → Bool
  | _, []     => false
  | l, x::xs => l == x || effMember l xs

def effInsert : EffLabel → EffRow → EffRow
  | l, [] => [l]
  | l, x::xs =>
    if l == x then x :: xs
    else if l < x then l :: x :: xs
    else x :: effInsert l xs

def effRemove : EffLabel → EffRow → EffRow
  | _, []     => []
  | l, x::xs => if l == x then xs else x :: effRemove l xs

-- ══════════════════════════════════════════════════════════════
-- SECTION 2 : EFFECT ROW LEMMAS
-- ══════════════════════════════════════════════════════════════

theorem effMember_nil (l : EffLabel) : effMember l [] = false := rfl

theorem effMember_cons (l x : EffLabel) (xs : EffRow) :
    effMember l (x :: xs) = (l == x || effMember l xs) := rfl

theorem effMember_insert_self (l : EffLabel) (r : EffRow) :
    effMember l (effInsert l r) = true := by
  induction r with
  | nil => simp [effInsert, effMember]
  | cons x xs ih =>
    simp only [effInsert]
    split
    · rename_i h; simp [effMember, beq_iff_eq] at h ⊢; left; exact h
    · split
      · simp [effMember]
      · simp only [effMember, ih, Bool.or_true]

theorem effRemove_nil (l : EffLabel) : effRemove l [] = [] := rfl

theorem effRemove_length (l : EffLabel) (r : EffRow) :
    (effRemove l r).length ≤ r.length := by
  induction r with
  | nil => simp [effRemove]
  | cons x xs ih =>
    simp only [effRemove]
    split <;> simp <;> omega

theorem effInsert_length (l : EffLabel) (r : EffRow) :
    (effInsert l r).length ≤ r.length + 1 := by
  induction r with
  | nil => simp [effInsert]
  | cons x xs ih =>
    simp only [effInsert]
    split
    · simp
    · split
      · simp
      · simp; omega

-- ══════════════════════════════════════════════════════════════
-- SECTION 3 : TYPES
-- ══════════════════════════════════════════════════════════════

inductive VTy where
  | unit : VTy
  | nat  : VTy
  | bool : VTy
  | fn   : VTy → VTy → EffRow → VTy
  | prod : VTy → VTy → VTy
  deriving DecidableEq

-- ══════════════════════════════════════════════════════════════
-- SECTION 4 : EXPRESSIONS
-- ══════════════════════════════════════════════════════════════

inductive Expr where
  | var     : Nat → Expr
  | unit    : Expr
  | natLit  : Nat → Expr
  | true_   : Expr
  | false_  : Expr
  | lam     : VTy → Expr → Expr
  | app     : Expr → Expr → Expr
  | pair    : Expr → Expr → Expr
  | fst     : Expr → Expr
  | snd     : Expr → Expr
  | ite     : Expr → Expr → Expr → Expr
  | letE    : Expr → Expr → Expr
  | ret     : Expr → Expr
  | handle  : Expr → Expr → Expr
  | do_     : Expr → Expr → Expr

-- ══════════════════════════════════════════════════════════════
-- SECTION 5 : VALUES
-- ══════════════════════════════════════════════════════════════

inductive IsValue : Expr → Prop where
  | unit   : IsValue .unit
  | natLit : IsValue (.natLit n)
  | true_  : IsValue .true_
  | false_ : IsValue .false_
  | lam    : IsValue (.lam τ e)
  | pair   : IsValue v₁ → IsValue v₂ → IsValue (.pair v₁ v₂)

theorem val_not_var : ¬ IsValue (.var n) := by intro h; cases h
theorem val_not_app : ¬ IsValue (.app e₁ e₂) := by intro h; cases h
theorem val_not_fst : ¬ IsValue (.fst e) := by intro h; cases h
theorem val_not_snd : ¬ IsValue (.snd e) := by intro h; cases h
theorem val_not_ite : ¬ IsValue (.ite c t f) := by intro h; cases h
theorem val_not_letE : ¬ IsValue (.letE e₁ e₂) := by intro h; cases h
theorem val_not_ret : ¬ IsValue (.ret e) := by intro h; cases h
theorem val_not_handle : ¬ IsValue (.handle e h) := by intro h'; cases h'
theorem val_not_do : ¬ IsValue (.do_ e₁ e₂) := by intro h; cases h

-- ══════════════════════════════════════════════════════════════
-- SECTION 6 : SUBSTITUTION
-- ══════════════════════════════════════════════════════════════

def shift (d c : Nat) : Expr → Expr
  | .var n       => if n ≥ c then .var (n + d) else .var n
  | .unit        => .unit
  | .natLit n    => .natLit n
  | .true_       => .true_
  | .false_      => .false_
  | .lam τ e     => .lam τ (shift d (c+1) e)
  | .app e₁ e₂   => .app (shift d c e₁) (shift d c e₂)
  | .pair e₁ e₂  => .pair (shift d c e₁) (shift d c e₂)
  | .fst e       => .fst (shift d c e)
  | .snd e       => .snd (shift d c e)
  | .ite a b e   => .ite (shift d c a) (shift d c b) (shift d c e)
  | .letE a b    => .letE (shift d c a) (shift d (c+1) b)
  | .ret e       => .ret (shift d c e)
  | .handle e h  => .handle (shift d c e) (shift d (c+1) h)
  | .do_ a b     => .do_ (shift d c a) (shift d (c+1) b)

def subst (j : Nat) (s : Expr) : Expr → Expr
  | .var n       => if n = j then s else .var n
  | .unit        => .unit
  | .natLit n    => .natLit n
  | .true_       => .true_
  | .false_      => .false_
  | .lam τ e     => .lam τ (subst (j+1) (shift 1 0 s) e)
  | .app e₁ e₂   => .app (subst j s e₁) (subst j s e₂)
  | .pair e₁ e₂  => .pair (subst j s e₁) (subst j s e₂)
  | .fst e       => .fst (subst j s e)
  | .snd e       => .snd (subst j s e)
  | .ite a b c   => .ite (subst j s a) (subst j s b) (subst j s c)
  | .letE a b    => .letE (subst j s a) (subst (j+1) (shift 1 0 s) b)
  | .ret e       => .ret (subst j s e)
  | .handle e h  => .handle (subst j s e) (subst (j+1) (shift 1 0 s) h)
  | .do_ a b     => .do_ (subst j s a) (subst (j+1) (shift 1 0 s) b)

-- ══════════════════════════════════════════════════════════════
-- SECTION 7 : OPERATIONAL SEMANTICS
-- ══════════════════════════════════════════════════════════════

inductive Step : Expr → Expr → Prop where
  | appLam   : IsValue v → Step (.app (.lam τ body) v) (subst 0 v body)
  | appL     : Step e₁ e₁' → Step (.app e₁ e₂) (.app e₁' e₂)
  | appR     : IsValue v → Step e₂ e₂' → Step (.app v e₂) (.app v e₂')
  | fstPair  : IsValue v₁ → IsValue v₂ → Step (.fst (.pair v₁ v₂)) v₁
  | sndPair  : IsValue v₁ → IsValue v₂ → Step (.snd (.pair v₁ v₂)) v₂
  | fstStep  : Step e e' → Step (.fst e) (.fst e')
  | sndStep  : Step e e' → Step (.snd e) (.snd e')
  | pairL    : Step e₁ e₁' → Step (.pair e₁ e₂) (.pair e₁' e₂)
  | pairR    : IsValue v → Step e₂ e₂' → Step (.pair v e₂) (.pair v e₂')
  | iteTrue  : Step (.ite .true_ t f) t
  | iteFalse : Step (.ite .false_ t f) f
  | iteCond  : Step c c' → Step (.ite c t f) (.ite c' t f)
  | letV     : IsValue v → Step (.letE v body) (subst 0 v body)
  | letStep  : Step e e' → Step (.letE e body) (.letE e' body)
  | handleRet  : IsValue v → Step (.handle (.ret v) retC) (subst 0 v retC)
  | handleStep : Step e e' → Step (.handle e retC) (.handle e' retC)
  | doRet    : IsValue v → Step (.do_ (.ret v) body) (subst 0 v body)
  | doStep   : Step e e' → Step (.do_ e body) (.do_ e' body)

-- ══════════════════════════════════════════════════════════════
-- SECTION 8 : VALUE / STEP EXCLUSION
-- ══════════════════════════════════════════════════════════════

theorem value_no_step : IsValue e → Step e e' → False := by
  intro hv hs
  induction hv generalizing e' with
  | unit => cases hs
  | natLit => cases hs
  | true_ => cases hs
  | false_ => cases hs
  | lam => cases hs
  | pair _ _ ih1 ih2 =>
    cases hs with
    | pairL hs' => exact ih1 hs'
    | pairR _ hs' => exact ih2 hs'

theorem step_not_value : Step e e' → ¬ IsValue e :=
  fun hs hv => value_no_step hv hs

-- ══════════════════════════════════════════════════════════════
-- SECTION 9 : MULTI-STEP
-- ══════════════════════════════════════════════════════════════

inductive MultiStep : Expr → Expr → Prop where
  | refl : MultiStep e e
  | step : Step e₁ e₂ → MultiStep e₂ e₃ → MultiStep e₁ e₃

theorem multi_single (h : Step e₁ e₂) : MultiStep e₁ e₂ :=
  MultiStep.step h MultiStep.refl

theorem multi_trans (h1 : MultiStep e₁ e₂) (h2 : MultiStep e₂ e₃) : MultiStep e₁ e₃ := by
  induction h1 with
  | refl => exact h2
  | step s _ ih => exact .step s (ih h2)

theorem multi_app_l (h : MultiStep e₁ e₁') :
    MultiStep (.app e₁ e₂) (.app e₁' e₂) := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.appL s) ih

theorem multi_app_r (hv : IsValue v) (h : MultiStep e₂ e₂') :
    MultiStep (.app v e₂) (.app v e₂') := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.appR hv s) ih

theorem multi_fst (h : MultiStep e e') : MultiStep (.fst e) (.fst e') := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.fstStep s) ih

theorem multi_snd (h : MultiStep e e') : MultiStep (.snd e) (.snd e') := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.sndStep s) ih

theorem multi_pair_l (h : MultiStep e₁ e₁') :
    MultiStep (.pair e₁ e₂) (.pair e₁' e₂) := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.pairL s) ih

theorem multi_pair_r (hv : IsValue v) (h : MultiStep e₂ e₂') :
    MultiStep (.pair v e₂) (.pair v e₂') := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.pairR hv s) ih

theorem multi_ite_cond (h : MultiStep c c') :
    MultiStep (.ite c t f) (.ite c' t f) := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.iteCond s) ih

theorem multi_letE (h : MultiStep e₁ e₁') :
    MultiStep (.letE e₁ body) (.letE e₁' body) := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.letStep s) ih

theorem multi_handle (h : MultiStep e e') :
    MultiStep (.handle e retC) (.handle e' retC) := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.handleStep s) ih

theorem multi_do (h : MultiStep e e') :
    MultiStep (.do_ e body) (.do_ e' body) := by
  induction h with
  | refl => exact .refl
  | step s _ ih => exact .step (.doStep s) ih

-- ══════════════════════════════════════════════════════════════
-- SECTION 10 : EFFECT ROW SUBTYPING
-- ══════════════════════════════════════════════════════════════

def EffSub (r₁ r₂ : EffRow) : Prop :=
  ∀ l, effMember l r₁ = true → effMember l r₂ = true

theorem effSub_refl (r : EffRow) : EffSub r r := fun _ h => h

theorem effSub_trans (h1 : EffSub r₁ r₂) (h2 : EffSub r₂ r₃) :
    EffSub r₁ r₃ := fun l hl => h2 l (h1 l hl)

theorem effSub_nil (r : EffRow) : EffSub [] r := by
  intro l h; simp [effMember] at h

theorem effSub_cons_right (h : EffSub r₁ r₂) :
    EffSub r₁ (x :: r₂) := by
  intro l hl; simp [effMember]; right; exact h l hl

-- ══════════════════════════════════════════════════════════════
-- SECTION 11 : VALUE TYPE SUBTYPING
-- ══════════════════════════════════════════════════════════════

inductive VSub : VTy → VTy → Prop where
  | refl : VSub τ τ
  | fn   : VSub σ₂ σ₁ → VSub τ₁ τ₂ → EffSub ε₁ ε₂ →
           VSub (.fn σ₁ τ₁ ε₁) (.fn σ₂ τ₂ ε₂)
  | prod : VSub a₁ a₂ → VSub b₁ b₂ → VSub (.prod a₁ b₁) (.prod a₂ b₂)

theorem vsub_refl (τ : VTy) : VSub τ τ := VSub.refl

theorem vsub_prod_co (h1 : VSub a₁ a₂) (h2 : VSub b₁ b₂) :
    VSub (.prod a₁ b₁) (.prod a₂ b₂) := VSub.prod h1 h2

theorem vsub_fn_contra_co (h1 : VSub σ₂ σ₁) (h2 : VSub τ₁ τ₂) (he : EffSub ε₁ ε₂) :
    VSub (.fn σ₁ τ₁ ε₁) (.fn σ₂ τ₂ ε₂) := VSub.fn h1 h2 he

theorem vsub_fn_pure_to_eff (σ τ : VTy) (ε : EffRow) :
    VSub (.fn σ τ []) (.fn σ τ ε) := VSub.fn VSub.refl VSub.refl (effSub_nil ε)

-- ══════════════════════════════════════════════════════════════
-- SECTION 12 : TYPING  (no effSub rule → clean canonical forms)
-- ══════════════════════════════════════════════════════════════

abbrev Ctx := List VTy

inductive HasType : Ctx → Expr → VTy → EffRow → Prop where
  | var     : Γ.get? n = some τ → HasType Γ (.var n) τ ε
  | unit    : HasType Γ .unit .unit ε
  | natLit  : HasType Γ (.natLit n) .nat ε
  | true_   : HasType Γ .true_ .bool ε
  | false_  : HasType Γ .false_ .bool ε
  | lam     : HasType (σ :: Γ) body τ ε →
              HasType Γ (.lam σ body) (.fn σ τ ε) ε'
  | app     : HasType Γ e₁ (.fn σ τ ε) ε →
              HasType Γ e₂ σ ε →
              HasType Γ (.app e₁ e₂) τ ε
  | pair    : HasType Γ e₁ τ₁ ε → HasType Γ e₂ τ₂ ε →
              HasType Γ (.pair e₁ e₂) (.prod τ₁ τ₂) ε
  | fst     : HasType Γ e (.prod τ₁ τ₂) ε → HasType Γ (.fst e) τ₁ ε
  | snd     : HasType Γ e (.prod τ₁ τ₂) ε → HasType Γ (.snd e) τ₂ ε
  | ite     : HasType Γ c .bool ε → HasType Γ t τ ε → HasType Γ f τ ε →
              HasType Γ (.ite c t f) τ ε
  | letE    : HasType Γ e₁ σ ε → HasType (σ :: Γ) e₂ τ ε →
              HasType Γ (.letE e₁ e₂) τ ε
  | ret     : HasType Γ v τ ε → HasType Γ (.ret v) τ ε
  | handle  : HasType Γ e τ₁ ε₁ → HasType (τ₁ :: Γ) retC τ₂ ε₂ →
              HasType Γ (.handle e retC) τ₂ ε₂
  | do_     : HasType Γ e₁ σ ε → HasType (σ :: Γ) e₂ τ ε →
              HasType Γ (.do_ e₁ e₂) τ ε

-- ══════════════════════════════════════════════════════════════
-- SECTION 13 : TYPING EXAMPLES
-- ══════════════════════════════════════════════════════════════

theorem type_unit_pure : HasType [] .unit .unit [] := HasType.unit
theorem type_nat_pure : HasType [] (.natLit 42) .nat [] := HasType.natLit
theorem type_true_pure : HasType [] .true_ .bool [] := HasType.true_
theorem type_false_pure : HasType [] .false_ .bool [] := HasType.false_

theorem type_id_fn (τ : VTy) (ε : EffRow) :
    HasType [] (.lam τ (.var 0)) (.fn τ τ ε) [] :=
  HasType.lam (HasType.var rfl)

theorem type_ret_unit : HasType [] (.ret .unit) .unit [1, 2, 3] :=
  HasType.ret HasType.unit

theorem type_pair_nats : HasType [] (.pair (.natLit 1) (.natLit 2)) (.prod .nat .nat) [] :=
  HasType.pair HasType.natLit HasType.natLit

theorem type_const_fn (σ τ : VTy) (ε₁ ε₂ : EffRow) :
    HasType [] (.lam σ (.lam τ (.var 1))) (.fn σ (.fn τ σ ε₂) ε₁) [] :=
  HasType.lam (HasType.lam (HasType.var rfl))

-- ══════════════════════════════════════════════════════════════
-- SECTION 14 : CANONICAL FORMS
-- ══════════════════════════════════════════════════════════════

theorem canonical_unit : IsValue e → HasType Γ e .unit ε → e = .unit := by
  intro hv ht; cases hv with
  | unit => rfl
  | natLit => cases ht
  | true_ => cases ht
  | false_ => cases ht
  | lam => cases ht
  | pair _ _ => cases ht

theorem canonical_nat : IsValue e → HasType Γ e .nat ε → ∃ n, e = .natLit n := by
  intro hv ht; cases hv with
  | natLit => exact ⟨_, rfl⟩
  | unit => cases ht
  | true_ => cases ht
  | false_ => cases ht
  | lam => cases ht
  | pair _ _ => cases ht

theorem canonical_bool : IsValue e → HasType Γ e .bool ε →
    e = .true_ ∨ e = .false_ := by
  intro hv ht; cases hv with
  | true_ => left; rfl
  | false_ => right; rfl
  | unit => cases ht
  | natLit => cases ht
  | lam => cases ht
  | pair _ _ => cases ht

theorem canonical_fn : IsValue e → HasType Γ e (.fn σ τ ε') ε →
    ∃ body, e = .lam σ body := by
  intro hv ht; cases hv with
  | lam => cases ht; exact ⟨_, rfl⟩
  | unit => cases ht
  | natLit => cases ht
  | true_ => cases ht
  | false_ => cases ht
  | pair _ _ => cases ht

theorem canonical_prod : IsValue e → HasType Γ e (.prod τ₁ τ₂) ε →
    ∃ v₁ v₂, e = .pair v₁ v₂ := by
  intro hv ht; cases hv with
  | pair _ _ => exact ⟨_, _, rfl⟩
  | unit => cases ht
  | natLit => cases ht
  | true_ => cases ht
  | false_ => cases ht
  | lam => cases ht

-- ══════════════════════════════════════════════════════════════
-- SECTION 15 : HANDLER & DO REDUCTIONS
-- ══════════════════════════════════════════════════════════════

theorem handle_ret_reduces (v : Expr) (hv : IsValue v) (retC : Expr) :
    Step (.handle (.ret v) retC) (subst 0 v retC) :=
  Step.handleRet hv

theorem multi_handle_ret (v : Expr) (hv : IsValue v) (retC : Expr) :
    MultiStep (.handle (.ret v) retC) (subst 0 v retC) :=
  multi_single (handle_ret_reduces v hv retC)

theorem do_ret_reduces (v : Expr) (hv : IsValue v) (body : Expr) :
    Step (.do_ (.ret v) body) (subst 0 v body) :=
  Step.doRet hv

theorem multi_do_ret (v : Expr) (hv : IsValue v) (body : Expr) :
    MultiStep (.do_ (.ret v) body) (subst 0 v body) :=
  multi_single (do_ret_reduces v hv body)

-- ══════════════════════════════════════════════════════════════
-- SECTION 16 : TYPING HELPERS
-- ══════════════════════════════════════════════════════════════

theorem type_app_id (τ : VTy) (h : HasType Γ e τ ε) :
    HasType Γ (.app (.lam τ (.var 0)) e) τ ε :=
  HasType.app (HasType.lam (HasType.var rfl)) h

theorem type_fst_pair (h1 : HasType Γ e₁ τ₁ ε) (h2 : HasType Γ e₂ τ₂ ε) :
    HasType Γ (.fst (.pair e₁ e₂)) τ₁ ε :=
  HasType.fst (HasType.pair h1 h2)

theorem type_snd_pair (h1 : HasType Γ e₁ τ₁ ε) (h2 : HasType Γ e₂ τ₂ ε) :
    HasType Γ (.snd (.pair e₁ e₂)) τ₂ ε :=
  HasType.snd (HasType.pair h1 h2)

theorem type_let_simple (h1 : HasType Γ e₁ σ ε) (h2 : HasType (σ :: Γ) e₂ τ ε) :
    HasType Γ (.letE e₁ e₂) τ ε :=
  HasType.letE h1 h2

-- ══════════════════════════════════════════════════════════════
-- SECTION 17 : CONTEXT LEMMAS
-- ══════════════════════════════════════════════════════════════

theorem ctx_cons_zero : (τ :: Γ).get? 0 = some τ := rfl
theorem ctx_cons_succ : (τ :: Γ).get? (n+1) = Γ.get? n := rfl
theorem ctx_nil_lookup (n : Nat) : ([] : Ctx).get? n = none := by
  cases n <;> rfl

-- ══════════════════════════════════════════════════════════════
-- SECTION 18 : PURE COMPUTATIONS
-- ══════════════════════════════════════════════════════════════

def isPure (Γ : Ctx) (e : Expr) (τ : VTy) : Prop := HasType Γ e τ []

theorem pure_unit : isPure [] .unit .unit := HasType.unit
theorem pure_natLit (n : Nat) : isPure [] (.natLit n) .nat := HasType.natLit
theorem pure_true : isPure [] .true_ .bool := HasType.true_
theorem pure_false : isPure [] .false_ .bool := HasType.false_

theorem pure_ret (h : HasType Γ v τ []) : isPure Γ (.ret v) τ :=
  HasType.ret h

-- ══════════════════════════════════════════════════════════════
-- SECTION 19 : STEP EXAMPLES
-- ══════════════════════════════════════════════════════════════

theorem beta_unit :
    Step (.app (.lam .unit (.var 0)) .unit) (subst 0 .unit (.var 0)) :=
  Step.appLam IsValue.unit

theorem fst_reduces :
    Step (.fst (.pair .unit (.natLit 0))) .unit :=
  Step.fstPair IsValue.unit IsValue.natLit

theorem snd_reduces :
    Step (.snd (.pair .unit (.natLit 0))) (.natLit 0) :=
  Step.sndPair IsValue.unit IsValue.natLit

theorem ite_true_reduces :
    Step (.ite .true_ (.natLit 1) (.natLit 2)) (.natLit 1) :=
  Step.iteTrue

theorem ite_false_reduces :
    Step (.ite .false_ (.natLit 1) (.natLit 2)) (.natLit 2) :=
  Step.iteFalse

-- ══════════════════════════════════════════════════════════════
-- SECTION 20 : MULTI-STEP COMPOSITIONS
-- ══════════════════════════════════════════════════════════════

theorem multi_app_full (hv : IsValue v) (hmf : MultiStep e₁ (.lam τ body))
    (hma : MultiStep e₂ v) :
    MultiStep (.app e₁ e₂) (subst 0 v body) :=
  multi_trans (multi_app_l hmf)
    (multi_trans (multi_app_r IsValue.lam hma)
      (multi_single (Step.appLam hv)))

theorem multi_fst_pair (hv1 : IsValue v₁) (hv2 : IsValue v₂)
    (h1 : MultiStep e₁ v₁) (h2 : MultiStep e₂ v₂) :
    MultiStep (.fst (.pair e₁ e₂)) v₁ :=
  multi_trans (multi_fst (multi_trans (multi_pair_l h1) (multi_pair_r hv1 h2)))
    (multi_single (Step.fstPair hv1 hv2))

theorem multi_snd_pair (hv1 : IsValue v₁) (hv2 : IsValue v₂)
    (h1 : MultiStep e₁ v₁) (h2 : MultiStep e₂ v₂) :
    MultiStep (.snd (.pair e₁ e₂)) v₂ :=
  multi_trans (multi_snd (multi_trans (multi_pair_l h1) (multi_pair_r hv1 h2)))
    (multi_single (Step.sndPair hv1 hv2))

-- ══════════════════════════════════════════════════════════════
-- SECTION 21 : EFFECT ROW EXTRAS
-- ══════════════════════════════════════════════════════════════

theorem effSub_empty : EffSub ([] : EffRow) r := effSub_nil r
theorem pure_eff_sub (r : EffRow) : EffSub [] r := effSub_nil r

end AlgebraicEffects
