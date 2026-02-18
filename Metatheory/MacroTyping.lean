/-
  Macro Typing and Staged Computation
-/

namespace MacroTyping

-- ============================================================
-- Types with Staging
-- ============================================================

inductive Ty where
  | nat : Ty
  | bool : Ty
  | arrow : Ty → Ty → Ty
  | code : Ty → Ty
  | product : Ty → Ty → Ty
deriving DecidableEq, Repr

infixr:25 " ⇒ " => Ty.arrow

def Ty.size : Ty → Nat
  | .nat => 1
  | .bool => 1
  | .arrow a b => 1 + a.size + b.size
  | .code t => 1 + t.size
  | .product a b => 1 + a.size + b.size

theorem ty_size_pos (τ : Ty) : τ.size > 0 := by
  cases τ <;> simp [Ty.size] <;> omega

-- ============================================================
-- Staged Expressions (MetaML Core)
-- ============================================================

structure SVar where
  name : Nat
  level : Nat
deriving DecidableEq, Repr

inductive SExpr where
  | svar : SVar → SExpr
  | snum : Nat → SExpr
  | sbool : Bool → SExpr
  | slam : Nat → Ty → SExpr → SExpr
  | sapp : SExpr → SExpr → SExpr
  | bracket : SExpr → SExpr
  | escape : SExpr → SExpr
  | run : SExpr → SExpr
  | spair : SExpr → SExpr → SExpr
  | sfst : SExpr → SExpr
  | ssnd : SExpr → SExpr
  | site : SExpr → SExpr → SExpr → SExpr
deriving DecidableEq, Repr

-- ============================================================
-- Typing Context
-- ============================================================

structure CtxEntry where
  name : Nat
  ty : Ty
  level : Nat
deriving DecidableEq, Repr

abbrev Ctx := List CtxEntry

def ctxLookup (Γ : Ctx) (x : Nat) (n : Nat) : Option Ty :=
  match Γ with
  | [] => none
  | e :: rest =>
    if e.name = x ∧ e.level = n then some e.ty
    else ctxLookup rest x n

theorem ctxLookup_nil (x n : Nat) : ctxLookup [] x n = none := rfl

theorem ctxLookup_hit (Γ : Ctx) (x n : Nat) (τ : Ty) :
    ctxLookup (⟨x, τ, n⟩ :: Γ) x n = some τ := by simp [ctxLookup]

-- ============================================================
-- Typing Judgment
-- ============================================================

inductive HasType : Ctx → Nat → SExpr → Ty → Prop where
  | tVar : ∀ {Γ n x τ},
    ctxLookup Γ x n = some τ →
    HasType Γ n (.svar ⟨x, n⟩) τ
  | tNum : ∀ {Γ n k},
    HasType Γ n (.snum k) .nat
  | tBool : ∀ {Γ n b},
    HasType Γ n (.sbool b) .bool
  | tLam : ∀ {Γ n x τ₁ τ₂ body},
    HasType (⟨x, τ₁, n⟩ :: Γ) n body τ₂ →
    HasType Γ n (.slam x τ₁ body) (τ₁ ⇒ τ₂)
  | tApp : ∀ {Γ n f a τ₁ τ₂},
    HasType Γ n f (τ₁ ⇒ τ₂) →
    HasType Γ n a τ₁ →
    HasType Γ n (.sapp f a) τ₂
  | tBracket : ∀ {Γ n e τ},
    HasType Γ (n + 1) e τ →
    HasType Γ n (.bracket e) (.code τ)
  | tEscape : ∀ {Γ n e τ},
    HasType Γ n e (.code τ) →
    HasType Γ (n + 1) (.escape e) τ
  | tRun : ∀ {Γ e τ},
    HasType Γ 0 e (.code τ) →
    HasType Γ 0 (.run e) τ
  | tPair : ∀ {Γ n e₁ e₂ τ₁ τ₂},
    HasType Γ n e₁ τ₁ →
    HasType Γ n e₂ τ₂ →
    HasType Γ n (.spair e₁ e₂) (.product τ₁ τ₂)
  | tFst : ∀ {Γ n e τ₁ τ₂},
    HasType Γ n e (.product τ₁ τ₂) →
    HasType Γ n (.sfst e) τ₁
  | tSnd : ∀ {Γ n e τ₁ τ₂},
    HasType Γ n e (.product τ₁ τ₂) →
    HasType Γ n (.ssnd e) τ₂
  | tIte : ∀ {Γ n c t f τ},
    HasType Γ n c .bool →
    HasType Γ n t τ →
    HasType Γ n f τ →
    HasType Γ n (.site c t f) τ

-- ============================================================
-- Basic Typing Theorems
-- ============================================================

theorem type_num (Γ : Ctx) (n k : Nat) : HasType Γ n (.snum k) .nat := HasType.tNum
theorem type_bool (Γ : Ctx) (n : Nat) (b : Bool) : HasType Γ n (.sbool b) .bool := HasType.tBool

theorem bracket_type_is_code (Γ : Ctx) (n : Nat) (e : SExpr) (τ : Ty)
    (h : HasType Γ n (.bracket e) τ) : ∃ τ', τ = .code τ' := by
  cases h with | tBracket _ => exact ⟨_, rfl⟩

theorem run_requires_code (Γ : Ctx) (e : SExpr) (τ : Ty)
    (h : HasType Γ 0 (.run e) τ) : ∃ τ', HasType Γ 0 e (.code τ') ∧ τ = τ' := by
  cases h with | tRun h' => exact ⟨τ, h', rfl⟩

-- ============================================================
-- Staging Level Properties
-- ============================================================

theorem bracket_increases_level (Γ : Ctx) (n : Nat) (e : SExpr) (τ : Ty)
    (h : HasType Γ n (.bracket e) (.code τ)) :
    HasType Γ (n + 1) e τ := by
  cases h with | tBracket h' => exact h'

theorem escape_decreases_level (Γ : Ctx) (n : Nat) (e : SExpr) (τ : Ty)
    (h : HasType Γ (n + 1) (.escape e) τ) :
    HasType Γ n e (.code τ) := by
  cases h with | tEscape h' => exact h'

theorem bracket_escape_roundtrip (Γ : Ctx) (n : Nat) (e : SExpr) (τ : Ty)
    (h : HasType Γ (n + 1) e τ) :
    HasType Γ (n + 1) (.escape (.bracket e)) τ :=
  HasType.tEscape (HasType.tBracket h)

theorem bracket_escape_type_cancel (Γ : Ctx) (n : Nat) (e : SExpr) (τ : Ty)
    (h : HasType Γ n e (.code τ)) :
    HasType Γ n (.bracket (.escape e)) (.code τ) :=
  HasType.tBracket (HasType.tEscape h)

-- ============================================================
-- Code Generation Typing
-- ============================================================

theorem code_gen_bracket (Γ : Ctx) (n : Nat) (e : SExpr) (τ : Ty)
    (h : HasType Γ (n+1) e τ) :
    HasType Γ n (.bracket e) (.code τ) := HasType.tBracket h

theorem run_preserves_type (Γ : Ctx) (e : SExpr) (τ : Ty)
    (h : HasType Γ 0 e (.code τ)) :
    HasType Γ 0 (.run e) τ := HasType.tRun h

theorem lam_level_inv (Γ : Ctx) (n x : Nat) (τ₁ τ₂ : Ty) (body : SExpr)
    (h : HasType Γ n (.slam x τ₁ body) (τ₁ ⇒ τ₂)) :
    HasType (⟨x, τ₁, n⟩ :: Γ) n body τ₂ := by
  cases h with | tLam hbody => exact hbody

-- ============================================================
-- Type Discrimination
-- ============================================================

theorem code_type_not_nat : ∀ τ, Ty.code τ ≠ Ty.nat := by intro τ h; cases h
theorem code_type_not_bool : ∀ τ, Ty.code τ ≠ Ty.bool := by intro τ h; cases h
theorem code_type_not_arrow : ∀ τ τ₁ τ₂, Ty.code τ ≠ Ty.arrow τ₁ τ₂ := by intro τ τ₁ τ₂ h; cases h
theorem code_type_injective : ∀ τ₁ τ₂, Ty.code τ₁ = Ty.code τ₂ → τ₁ = τ₂ := by intros τ₁ τ₂ h; cases h; rfl
theorem arrow_injective_left : ∀ τ₁ τ₂ τ₃ τ₄, Ty.arrow τ₁ τ₂ = Ty.arrow τ₃ τ₄ → τ₁ = τ₃ := by intros; cases ‹_›; rfl
theorem arrow_injective_right : ∀ τ₁ τ₂ τ₃ τ₄, Ty.arrow τ₁ τ₂ = Ty.arrow τ₃ τ₄ → τ₂ = τ₄ := by intros; cases ‹_›; rfl
theorem product_injective_left : ∀ τ₁ τ₂ τ₃ τ₄, Ty.product τ₁ τ₂ = Ty.product τ₃ τ₄ → τ₁ = τ₃ := by intros; cases ‹_›; rfl
theorem product_injective_right : ∀ τ₁ τ₂ τ₃ τ₄, Ty.product τ₁ τ₂ = Ty.product τ₃ τ₄ → τ₂ = τ₄ := by intros; cases ‹_›; rfl
theorem nat_ne_bool : Ty.nat ≠ Ty.bool := by intro h; cases h
theorem nat_ne_arrow : ∀ τ₁ τ₂, Ty.nat ≠ Ty.arrow τ₁ τ₂ := by intros; intro h; cases h
theorem bool_ne_arrow : ∀ τ₁ τ₂, Ty.bool ≠ Ty.arrow τ₁ τ₂ := by intros; intro h; cases h

-- ============================================================
-- Derived Typing Forms
-- ============================================================

theorem let_as_app (Γ : Ctx) (n x : Nat) (e body : SExpr) (τ₁ τ₂ : Ty)
    (he : HasType Γ n e τ₁)
    (hbody : HasType (⟨x, τ₁, n⟩ :: Γ) n body τ₂) :
    HasType Γ n (.sapp (.slam x τ₁ body) e) τ₂ :=
  HasType.tApp (HasType.tLam hbody) he

theorem identity_macro_typed (Γ : Ctx) (τ : Ty) :
    HasType Γ 0 (.slam 0 τ (.svar ⟨0, 0⟩)) (τ ⇒ τ) := by
  apply HasType.tLam; apply HasType.tVar; simp [ctxLookup]

theorem constant_macro_typed (Γ : Ctx) (τ₁ : Ty) (k : Nat) :
    HasType Γ 0 (.slam 0 τ₁ (.snum k)) (τ₁ ⇒ .nat) := by
  apply HasType.tLam; exact HasType.tNum

theorem staged_identity (Γ : Ctx) (τ : Ty) :
    HasType Γ 0 (.bracket (.slam 0 τ (.svar ⟨0, 1⟩))) (.code (τ ⇒ τ)) := by
  apply HasType.tBracket; apply HasType.tLam; apply HasType.tVar; simp [ctxLookup]

-- ============================================================
-- Macro Signatures
-- ============================================================

structure MacroSig where
  inputTy : Ty
  outputTy : Ty
deriving DecidableEq, Repr

structure TypedMacro where
  sig : MacroSig
  transformer : SExpr
deriving Repr

def macroWellTyped (Γ : Ctx) (m : TypedMacro) : Prop :=
  HasType Γ 0 m.transformer (m.sig.inputTy ⇒ m.sig.outputTy)

-- ============================================================
-- Quasi-Quotation Typing
-- ============================================================

inductive QQTyped : Ctx → Nat → SExpr → Ty → Prop where
  | qqBase : ∀ {Γ n e τ},
    HasType Γ (n+1) e τ →
    QQTyped Γ n (.bracket e) (.code τ)
  | qqSplice : ∀ {Γ n e τ},
    HasType Γ n e (.code τ) →
    QQTyped Γ n (.bracket (.escape e)) (.code τ)

theorem qq_produces_code (Γ : Ctx) (n : Nat) (e : SExpr) (τ : Ty)
    (h : QQTyped Γ n e τ) : ∃ τ', τ = .code τ' := by
  cases h with
  | qqBase _ => exact ⟨_, rfl⟩
  | qqSplice _ => exact ⟨_, rfl⟩

theorem qq_base_typing (Γ : Ctx) (n : Nat) (e : SExpr) (τ : Ty)
    (h : HasType Γ (n+1) e τ) : QQTyped Γ n (.bracket e) (.code τ) :=
  QQTyped.qqBase h

-- ============================================================
-- Values
-- ============================================================

inductive IsValue₀ : SExpr → Prop where
  | vNum : ∀ n, IsValue₀ (.snum n)
  | vBool : ∀ b, IsValue₀ (.sbool b)
  | vLam : ∀ x τ body, IsValue₀ (.slam x τ body)
  | vBracket : ∀ e, IsValue₀ (.bracket e)
  | vPair : ∀ e₁ e₂, IsValue₀ e₁ → IsValue₀ e₂ → IsValue₀ (.spair e₁ e₂)

-- ============================================================
-- Substitution for stage-0 reduction
-- ============================================================

def substS (x : Nat) (v : SExpr) : SExpr → SExpr
  | .svar ⟨y, n⟩ => if y = x ∧ n = 0 then v else .svar ⟨y, n⟩
  | .snum n => .snum n
  | .sbool b => .sbool b
  | .slam y τ body => if y = x then .slam y τ body else .slam y τ (substS x v body)
  | .sapp f a => .sapp (substS x v f) (substS x v a)
  | .bracket e => .bracket e
  | .escape e => .escape (substS x v e)
  | .run e => .run (substS x v e)
  | .spair a b => .spair (substS x v a) (substS x v b)
  | .sfst e => .sfst (substS x v e)
  | .ssnd e => .ssnd (substS x v e)
  | .site c t f => .site (substS x v c) (substS x v t) (substS x v f)

-- ============================================================
-- Small-step reduction
-- ============================================================

inductive Step₀ : SExpr → SExpr → Prop where
  | sAppLam : ∀ {x τ body arg},
    IsValue₀ arg →
    Step₀ (.sapp (.slam x τ body) arg) (substS x arg body)
  | sApp1 : ∀ {f f' a},
    Step₀ f f' →
    Step₀ (.sapp f a) (.sapp f' a)
  | sApp2 : ∀ {f a a'},
    IsValue₀ f →
    Step₀ a a' →
    Step₀ (.sapp f a) (.sapp f a')
  | sRunBracket : ∀ {e},
    Step₀ (.run (.bracket e)) e
  | sRun : ∀ {e e'},
    Step₀ e e' →
    Step₀ (.run e) (.run e')
  | sFst : ∀ {e₁ e₂},
    IsValue₀ e₁ → IsValue₀ e₂ →
    Step₀ (.sfst (.spair e₁ e₂)) e₁
  | sSnd : ∀ {e₁ e₂},
    IsValue₀ e₁ → IsValue₀ e₂ →
    Step₀ (.ssnd (.spair e₁ e₂)) e₂
  | sIteTrue : ∀ {t f},
    Step₀ (.site (.sbool true) t f) t
  | sIteFalse : ∀ {t f},
    Step₀ (.site (.sbool false) t f) f
  | sPair1 : ∀ {e₁ e₁' e₂},
    Step₀ e₁ e₁' →
    Step₀ (.spair e₁ e₂) (.spair e₁' e₂)
  | sPair2 : ∀ {e₁ e₂ e₂'},
    IsValue₀ e₁ → Step₀ e₂ e₂' →
    Step₀ (.spair e₁ e₂) (.spair e₁ e₂')
  | sFstStep : ∀ {e e'},
    Step₀ e e' →
    Step₀ (.sfst e) (.sfst e')
  | sSndStep : ∀ {e e'},
    Step₀ e e' →
    Step₀ (.ssnd e) (.ssnd e')
  | sIteCond : ∀ {c c' t f},
    Step₀ c c' →
    Step₀ (.site c t f) (.site c' t f)

-- ============================================================
-- Canonical Forms
-- ============================================================

theorem canonical_nat (e : SExpr) (h : HasType [] 0 e .nat) (hv : IsValue₀ e) :
    ∃ n, e = .snum n := by
  cases hv with
  | vNum n => exact ⟨n, rfl⟩
  | vBool _ => cases h
  | vLam _ _ _ => cases h
  | vBracket _ => cases h
  | vPair _ _ _ _ => cases h

theorem canonical_bool (e : SExpr) (h : HasType [] 0 e .bool) (hv : IsValue₀ e) :
    ∃ b, e = .sbool b := by
  cases hv with
  | vBool b => exact ⟨b, rfl⟩
  | vNum _ => cases h
  | vLam _ _ _ => cases h
  | vBracket _ => cases h
  | vPair _ _ _ _ => cases h

theorem canonical_arrow (e : SExpr) (τ₁ τ₂ : Ty) (h : HasType [] 0 e (τ₁ ⇒ τ₂)) (hv : IsValue₀ e) :
    ∃ x body, e = .slam x τ₁ body := by
  cases hv with
  | vLam x τ body => cases h with | tLam _ => exact ⟨x, body, rfl⟩
  | vNum _ => cases h
  | vBool _ => cases h
  | vBracket _ => cases h
  | vPair _ _ _ _ => cases h

theorem canonical_code (e : SExpr) (τ : Ty) (h : HasType [] 0 e (.code τ)) (hv : IsValue₀ e) :
    ∃ e', e = .bracket e' := by
  cases hv with
  | vBracket e' => exact ⟨e', rfl⟩
  | vNum _ => cases h
  | vBool _ => cases h
  | vLam _ _ _ => cases h
  | vPair _ _ _ _ => cases h

theorem canonical_product (e : SExpr) (τ₁ τ₂ : Ty) (h : HasType [] 0 e (.product τ₁ τ₂)) (hv : IsValue₀ e) :
    ∃ e₁ e₂, e = .spair e₁ e₂ ∧ IsValue₀ e₁ ∧ IsValue₀ e₂ := by
  cases hv with
  | vPair e₁ e₂ v1 v2 => exact ⟨e₁, e₂, rfl, v1, v2⟩
  | vNum _ => cases h
  | vBool _ => cases h
  | vLam _ _ _ => cases h
  | vBracket _ => cases h

-- ============================================================
-- Value irreducibility
-- ============================================================

theorem value_no_step (e : SExpr) (hv : IsValue₀ e) : ¬∃ e', Step₀ e e' := by
  induction hv with
  | vNum _ => intro ⟨_, hs⟩; cases hs
  | vBool _ => intro ⟨_, hs⟩; cases hs
  | vLam _ _ _ => intro ⟨_, hs⟩; cases hs
  | vBracket _ => intro ⟨_, hs⟩; cases hs
  | vPair _ _ _ _ ih1 ih2 =>
    intro ⟨_, hs⟩
    cases hs with
    | sPair1 h => exact ih1 ⟨_, h⟩
    | sPair2 _ h => exact ih2 ⟨_, h⟩

end MacroTyping
