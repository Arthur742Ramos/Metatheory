/-
  Armada 649: Refinement Types & Predicate Subtyping

  A type system with base types refined by decidable predicates,
  subtyping via predicate implication, and typing.
-/

namespace RefinementTypes

-- ══════════════════════════════════════════════════════════════
-- SECTION 1 : PREDICATES & TYPES
-- ══════════════════════════════════════════════════════════════

inductive Pred where
  | tt   : Pred
  | ff   : Pred
  | eq   : Nat → Pred
  | lt   : Nat → Pred
  | le   : Nat → Pred
  | andP : Pred → Pred → Pred
  | orP  : Pred → Pred → Pred
  | notP : Pred → Pred
  deriving DecidableEq

def Pred.eval : Pred → Nat → Bool
  | .tt, _       => true
  | .ff, _       => false
  | .eq n, v     => v == n
  | .lt n, v     => v < n
  | .le n, v     => v ≤ n
  | .andP p q, v => p.eval v && q.eval v
  | .orP p q, v  => p.eval v || q.eval v
  | .notP p, v   => !p.eval v

def Pred.implies (p q : Pred) : Prop := ∀ v, p.eval v = true → q.eval v = true
infix:50 " ⊑p " => Pred.implies

inductive Ty where
  | unit : Ty
  | bool : Ty
  | nat  : Pred → Ty
  | fn   : Ty → Ty → Ty
  | prod : Ty → Ty → Ty
  deriving DecidableEq

-- ══════════════════════════════════════════════════════════════
-- SECTION 2 : PREDICATE LEMMAS
-- ══════════════════════════════════════════════════════════════

theorem pred_implies_refl (p : Pred) : p ⊑p p := fun _ h => h

theorem pred_implies_trans {p q r : Pred} (h1 : p ⊑p q) (h2 : q ⊑p r) : p ⊑p r :=
  fun v hv => h2 v (h1 v hv)

theorem tt_top (p : Pred) : p ⊑p .tt := fun _ _ => rfl

theorem ff_bot (p : Pred) : Pred.ff ⊑p p := fun v h => by simp [Pred.eval] at h

theorem andP_left (p q : Pred) : (Pred.andP p q) ⊑p p := by
  intro v h; simp [Pred.eval] at h; exact h.1

theorem andP_right (p q : Pred) : (Pred.andP p q) ⊑p q := by
  intro v h; simp [Pred.eval] at h; exact h.2

theorem orP_left (p q : Pred) : p ⊑p (Pred.orP p q) := by
  intro v h; simp [Pred.eval]; left; exact h

theorem orP_right (p q : Pred) : q ⊑p (Pred.orP p q) := by
  intro v h; simp [Pred.eval]; right; exact h

theorem andP_intro {p q r : Pred} (h1 : r ⊑p p) (h2 : r ⊑p q) :
    r ⊑p (Pred.andP p q) := by
  intro v h; simp [Pred.eval]; exact ⟨h1 v h, h2 v h⟩

theorem orP_elim {p q r : Pred} (h1 : p ⊑p r) (h2 : q ⊑p r) :
    (Pred.orP p q) ⊑p r := by
  intro v h
  simp [Pred.eval] at h
  cases hp : p.eval v <;> simp [hp] at h
  · exact h2 v h
  · exact h1 v hp

theorem notP_double_neg (p : Pred) : (Pred.notP (Pred.notP p)) ⊑p p := by
  intro v h; simp [Pred.eval] at h; exact h

theorem notP_anti {p q : Pred} (h : p ⊑p q) : Pred.notP q ⊑p Pred.notP p := by
  intro v hv
  simp [Pred.eval] at hv ⊢
  cases hp : p.eval v
  · rfl
  · simp [h v hp] at hv

theorem andP_comm (p q : Pred) : (Pred.andP p q) ⊑p (Pred.andP q p) := by
  intro v h; simp [Pred.eval] at h ⊢; exact ⟨h.2, h.1⟩

theorem orP_comm (p q : Pred) : (Pred.orP p q) ⊑p (Pred.orP q p) := by
  intro v h; simp [Pred.eval] at h ⊢
  cases hp : p.eval v <;> simp_all

theorem andP_assoc (p q r : Pred) :
    (Pred.andP (Pred.andP p q) r) ⊑p (Pred.andP p (Pred.andP q r)) := by
  intro v h; simp [Pred.eval] at h ⊢; exact ⟨h.1.1, h.1.2, h.2⟩

theorem orP_assoc (p q r : Pred) :
    (Pred.orP (Pred.orP p q) r) ⊑p (Pred.orP p (Pred.orP q r)) := by
  intro v h; simp [Pred.eval] at h ⊢
  cases hp : p.eval v <;> simp_all

theorem andP_idem (p : Pred) : (Pred.andP p p) ⊑p p := andP_left p p

theorem orP_idem (p : Pred) : (Pred.orP p p) ⊑p p := by
  intro v h; simp [Pred.eval] at h
  cases hp : p.eval v <;> simp_all

theorem andP_absorb_or (p q : Pred) : (Pred.andP p (Pred.orP p q)) ⊑p p :=
  andP_left p _

-- ══════════════════════════════════════════════════════════════
-- SECTION 3 : EVALUATION LEMMAS
-- ══════════════════════════════════════════════════════════════

theorem eval_tt (v : Nat) : Pred.tt.eval v = true := rfl
theorem eval_ff (v : Nat) : Pred.ff.eval v = false := rfl
theorem eval_andP (p q : Pred) (v : Nat) :
    (Pred.andP p q).eval v = (p.eval v && q.eval v) := rfl
theorem eval_orP (p q : Pred) (v : Nat) :
    (Pred.orP p q).eval v = (p.eval v || q.eval v) := rfl
theorem eval_notP (p : Pred) (v : Nat) :
    (Pred.notP p).eval v = (!p.eval v) := rfl

theorem eval_eq_iff (n v : Nat) : (Pred.eq n).eval v = true ↔ v = n := by
  simp [Pred.eval, Nat.beq_eq]

theorem eval_lt_iff (n v : Nat) : (Pred.lt n).eval v = true ↔ v < n := by
  simp [Pred.eval, Nat.blt_eq]

theorem eval_le_iff (n v : Nat) : (Pred.le n).eval v = true ↔ v ≤ n := by
  simp [Pred.eval, Nat.ble_eq]

-- ══════════════════════════════════════════════════════════════
-- SECTION 4 : ARITHMETIC BOUND PREDICATES
-- ══════════════════════════════════════════════════════════════

theorem lt_implies_le (n : Nat) : (Pred.lt n) ⊑p (Pred.le n) := by
  intro v h; simp [Pred.eval] at h ⊢; omega

theorem eq_implies_le (n : Nat) : (Pred.eq n) ⊑p (Pred.le n) := by
  intro v h; simp [Pred.eval] at h ⊢; omega

theorem eq_implies_lt_succ (n : Nat) : (Pred.eq n) ⊑p (Pred.lt (n+1)) := by
  intro v h; simp [Pred.eval] at h ⊢; omega

theorem lt_mono {n m : Nat} (h : n ≤ m) : (Pred.lt n) ⊑p (Pred.lt m) := by
  intro v hv; simp [Pred.eval] at hv ⊢; omega

theorem le_mono {n m : Nat} (h : n ≤ m) : (Pred.le n) ⊑p (Pred.le m) := by
  intro v hv; simp [Pred.eval] at hv ⊢; omega

theorem le_lt_succ (n : Nat) : (Pred.le n) ⊑p (Pred.lt (n+1)) := by
  intro v hv; simp [Pred.eval] at hv ⊢; omega

-- ══════════════════════════════════════════════════════════════
-- SECTION 5 : SUBTYPING
-- ══════════════════════════════════════════════════════════════

inductive Sub : Ty → Ty → Prop where
  | refl  : Sub τ τ
  | trans : Sub τ₁ τ₂ → Sub τ₂ τ₃ → Sub τ₁ τ₃
  | nat   : (p ⊑p q) → Sub (.nat p) (.nat q)
  | fn    : Sub σ₁ σ₂ → Sub τ₁ τ₂ → Sub (.fn σ₂ τ₁) (.fn σ₁ τ₂)
  | prod  : Sub τ₁ τ₂ → Sub σ₁ σ₂ → Sub (.prod τ₁ σ₁) (.prod τ₂ σ₂)

theorem sub_refl (τ : Ty) : Sub τ τ := Sub.refl
theorem sub_trans' {τ₁ τ₂ τ₃ : Ty} : Sub τ₁ τ₂ → Sub τ₂ τ₃ → Sub τ₁ τ₃ := Sub.trans
theorem sub_nat_tt (p : Pred) : Sub (.nat p) (.nat .tt) := Sub.nat (tt_top p)
theorem sub_fn_refl (σ τ : Ty) : Sub (.fn σ τ) (.fn σ τ) := Sub.refl
theorem sub_prod_refl (τ₁ τ₂ : Ty) : Sub (.prod τ₁ τ₂) (.prod τ₁ τ₂) := Sub.refl
theorem sub_unit_refl : Sub Ty.unit Ty.unit := Sub.refl
theorem sub_bool_refl : Sub Ty.bool Ty.bool := Sub.refl
theorem sub_lt_le (n : Nat) : Sub (.nat (.lt n)) (.nat (.le n)) := Sub.nat (lt_implies_le n)
theorem sub_eq_le (n : Nat) : Sub (.nat (.eq n)) (.nat (.le n)) := Sub.nat (eq_implies_le n)
theorem sub_nat_meet_left (p q : Pred) : Sub (.nat (.andP p q)) (.nat p) :=
  Sub.nat (andP_left p q)
theorem sub_nat_meet_right (p q : Pred) : Sub (.nat (.andP p q)) (.nat q) :=
  Sub.nat (andP_right p q)
theorem sub_nat_join_left (p q : Pred) : Sub (.nat p) (.nat (.orP p q)) :=
  Sub.nat (orP_left p q)
theorem sub_nat_join_right (p q : Pred) : Sub (.nat q) (.nat (.orP p q)) :=
  Sub.nat (orP_right p q)
theorem sub_fn_co_contra {a b c d : Ty} (h1 : Sub c a) (h2 : Sub b d) :
    Sub (.fn a b) (.fn c d) := Sub.fn h1 h2
theorem sub_prod_co {a b c d : Ty} (h1 : Sub a c) (h2 : Sub b d) :
    Sub (.prod a b) (.prod c d) := Sub.prod h1 h2
theorem sub_nat_chain (h1 : p ⊑p q) (h2 : q ⊑p r) : Sub (.nat p) (.nat r) :=
  Sub.nat (pred_implies_trans h1 h2)

-- ══════════════════════════════════════════════════════════════
-- SECTION 6 : EXPRESSIONS & VALUES
-- ══════════════════════════════════════════════════════════════

inductive Expr where
  | var     : Nat → Expr
  | unit    : Expr
  | true_   : Expr
  | false_  : Expr
  | natLit  : Nat → Expr
  | lam     : Ty → Expr → Expr
  | app     : Expr → Expr → Expr
  | pair    : Expr → Expr → Expr
  | fst     : Expr → Expr
  | snd     : Expr → Expr
  | ite     : Expr → Expr → Expr → Expr
  | letE    : Expr → Expr → Expr

inductive IsValue : Expr → Prop where
  | unit   : IsValue .unit
  | true_  : IsValue .true_
  | false_ : IsValue .false_
  | natLit : IsValue (.natLit n)
  | lam    : IsValue (.lam τ e)
  | pair   : IsValue v₁ → IsValue v₂ → IsValue (.pair v₁ v₂)

theorem val_not_var : ¬ IsValue (.var n) := by intro h; cases h
theorem val_not_app : ¬ IsValue (.app e₁ e₂) := by intro h; cases h
theorem val_not_fst : ¬ IsValue (.fst e) := by intro h; cases h
theorem val_not_snd : ¬ IsValue (.snd e) := by intro h; cases h
theorem val_not_ite : ¬ IsValue (.ite c t f) := by intro h; cases h
theorem val_not_letE : ¬ IsValue (.letE e₁ e₂) := by intro h; cases h

-- ══════════════════════════════════════════════════════════════
-- SECTION 7 : SUBSTITUTION
-- ══════════════════════════════════════════════════════════════

def shift (d c : Nat) : Expr → Expr
  | .var n       => if n ≥ c then .var (n + d) else .var n
  | .unit        => .unit
  | .true_       => .true_
  | .false_      => .false_
  | .natLit n    => .natLit n
  | .lam τ e     => .lam τ (shift d (c+1) e)
  | .app e₁ e₂   => .app (shift d c e₁) (shift d c e₂)
  | .pair e₁ e₂  => .pair (shift d c e₁) (shift d c e₂)
  | .fst e       => .fst (shift d c e)
  | .snd e       => .snd (shift d c e)
  | .ite a b e   => .ite (shift d c a) (shift d c b) (shift d c e)
  | .letE a b    => .letE (shift d c a) (shift d (c+1) b)

def subst (j : Nat) (s : Expr) : Expr → Expr
  | .var n       => if n = j then s else .var n
  | .unit        => .unit
  | .true_       => .true_
  | .false_      => .false_
  | .natLit n    => .natLit n
  | .lam τ e     => .lam τ (subst (j+1) (shift 1 0 s) e)
  | .app e₁ e₂   => .app (subst j s e₁) (subst j s e₂)
  | .pair e₁ e₂  => .pair (subst j s e₁) (subst j s e₂)
  | .fst e       => .fst (subst j s e)
  | .snd e       => .snd (subst j s e)
  | .ite a b c   => .ite (subst j s a) (subst j s b) (subst j s c)
  | .letE a b    => .letE (subst j s a) (subst (j+1) (shift 1 0 s) b)

-- ══════════════════════════════════════════════════════════════
-- SECTION 8 : SMALL-STEP SEMANTICS
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

-- ══════════════════════════════════════════════════════════════
-- SECTION 9 : TYPING
-- ══════════════════════════════════════════════════════════════

abbrev Ctx := List Ty

inductive HasType : Ctx → Expr → Ty → Prop where
  | var     : Γ.get? n = some τ → HasType Γ (.var n) τ
  | unit    : HasType Γ .unit .unit
  | true_   : HasType Γ .true_ .bool
  | false_  : HasType Γ .false_ .bool
  | natLit  : p.eval n = true → HasType Γ (.natLit n) (.nat p)
  | lam     : HasType (σ :: Γ) body τ → HasType Γ (.lam σ body) (.fn σ τ)
  | app     : HasType Γ e₁ (.fn σ τ) → HasType Γ e₂ σ → HasType Γ (.app e₁ e₂) τ
  | pair    : HasType Γ e₁ τ₁ → HasType Γ e₂ τ₂ → HasType Γ (.pair e₁ e₂) (.prod τ₁ τ₂)
  | fst     : HasType Γ e (.prod τ₁ τ₂) → HasType Γ (.fst e) τ₁
  | snd     : HasType Γ e (.prod τ₁ τ₂) → HasType Γ (.snd e) τ₂
  | ite     : HasType Γ c .bool → HasType Γ t τ → HasType Γ f τ → HasType Γ (.ite c t f) τ
  | letE    : HasType Γ e₁ σ → HasType (σ :: Γ) e₂ τ → HasType Γ (.letE e₁ e₂) τ

-- ══════════════════════════════════════════════════════════════
-- SECTION 10 : VALUE / STEP EXCLUSION
-- ══════════════════════════════════════════════════════════════

theorem value_no_step : IsValue e → Step e e' → False := by
  intro hv hs
  induction hv generalizing e' with
  | unit => cases hs
  | true_ => cases hs
  | false_ => cases hs
  | natLit => cases hs
  | lam => cases hs
  | pair _ _ ih1 ih2 =>
    cases hs with
    | pairL hs' => exact ih1 hs'
    | pairR _ hs' => exact ih2 hs'

theorem step_not_value : Step e e' → ¬ IsValue e :=
  fun hs hv => value_no_step hv hs

-- ══════════════════════════════════════════════════════════════
-- SECTION 11 : MULTI-STEP
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

-- ══════════════════════════════════════════════════════════════
-- SECTION 12 : CANONICAL FORMS
-- ══════════════════════════════════════════════════════════════

theorem canonical_unit : IsValue e → HasType Γ e .unit → e = .unit := by
  intro hv ht; cases hv with
  | unit => rfl
  | true_ => cases ht
  | false_ => cases ht
  | natLit => cases ht
  | lam => cases ht
  | pair _ _ => cases ht

theorem canonical_bool : IsValue e → HasType Γ e .bool → e = .true_ ∨ e = .false_ := by
  intro hv ht; cases hv with
  | true_ => left; rfl
  | false_ => right; rfl
  | unit => cases ht
  | natLit => cases ht
  | lam => cases ht
  | pair _ _ => cases ht

theorem canonical_nat : IsValue e → HasType Γ e (.nat p) → ∃ n, e = .natLit n := by
  intro hv ht; cases hv with
  | natLit => exact ⟨_, rfl⟩
  | unit => cases ht
  | true_ => cases ht
  | false_ => cases ht
  | lam => cases ht
  | pair _ _ => cases ht

theorem canonical_fn : IsValue e → HasType Γ e (.fn σ τ) → ∃ body, e = .lam σ body := by
  intro hv ht; cases hv with
  | lam => cases ht; exact ⟨_, rfl⟩
  | unit => cases ht
  | true_ => cases ht
  | false_ => cases ht
  | natLit => cases ht
  | pair _ _ => cases ht

theorem canonical_prod : IsValue e → HasType Γ e (.prod τ₁ τ₂) →
    ∃ v₁ v₂, e = .pair v₁ v₂ := by
  intro hv ht; cases hv with
  | pair _ _ => exact ⟨_, _, rfl⟩
  | unit => cases ht
  | true_ => cases ht
  | false_ => cases ht
  | natLit => cases ht
  | lam => cases ht

-- ══════════════════════════════════════════════════════════════
-- SECTION 13 : TYPING EXAMPLES
-- ══════════════════════════════════════════════════════════════

theorem type_unit_intro : HasType [] .unit .unit := HasType.unit
theorem type_true_intro : HasType [] .true_ .bool := HasType.true_
theorem type_false_intro : HasType [] .false_ .bool := HasType.false_

theorem type_nat_tt (n : Nat) : HasType [] (.natLit n) (.nat .tt) :=
  HasType.natLit rfl

theorem type_nat_eq (n : Nat) : HasType [] (.natLit n) (.nat (.eq n)) :=
  HasType.natLit (by simp [Pred.eval])

theorem type_nat_le_self (n : Nat) : HasType [] (.natLit n) (.nat (.le n)) :=
  HasType.natLit (by simp [Pred.eval])

theorem type_id_fn (τ : Ty) : HasType [] (.lam τ (.var 0)) (.fn τ τ) :=
  HasType.lam (HasType.var rfl)

theorem type_const_fn (σ τ : Ty) :
    HasType [] (.lam σ (.lam τ (.var 1))) (.fn σ (.fn τ σ)) :=
  HasType.lam (HasType.lam (HasType.var rfl))

theorem subtype_eq5_le10 : Sub (.nat (.eq 5)) (.nat (.le 10)) :=
  Sub.nat (fun v h => by simp [Pred.eval] at h ⊢; omega)

theorem type_pair_nats : HasType [] (.pair (.natLit 1) (.natLit 2)) (.prod (.nat .tt) (.nat .tt)) :=
  HasType.pair (type_nat_tt 1) (type_nat_tt 2)

theorem type_ite_refined :
    HasType [] (.ite .true_ (.natLit 1) (.natLit 2)) (.nat .tt) :=
  HasType.ite HasType.true_ (type_nat_tt 1) (type_nat_tt 2)

-- ══════════════════════════════════════════════════════════════
-- SECTION 14 : TYPING HELPERS
-- ══════════════════════════════════════════════════════════════

theorem type_app_id (τ : Ty) (h : HasType Γ e τ) :
    HasType Γ (.app (.lam τ (.var 0)) e) τ :=
  HasType.app (HasType.lam (HasType.var rfl)) h

theorem type_fst_pair (h1 : HasType Γ e₁ τ₁) (h2 : HasType Γ e₂ τ₂) :
    HasType Γ (.fst (.pair e₁ e₂)) τ₁ :=
  HasType.fst (HasType.pair h1 h2)

theorem type_snd_pair (h1 : HasType Γ e₁ τ₁) (h2 : HasType Γ e₂ τ₂) :
    HasType Γ (.snd (.pair e₁ e₂)) τ₂ :=
  HasType.snd (HasType.pair h1 h2)

theorem type_let_simple (h1 : HasType Γ e₁ σ) (h2 : HasType (σ :: Γ) e₂ τ) :
    HasType Γ (.letE e₁ e₂) τ :=
  HasType.letE h1 h2

-- ══════════════════════════════════════════════════════════════
-- SECTION 15 : CONTEXT LEMMAS
-- ══════════════════════════════════════════════════════════════

theorem ctx_cons_zero : (τ :: Γ).get? 0 = some τ := rfl
theorem ctx_cons_succ : (τ :: Γ).get? (n+1) = Γ.get? n := rfl
theorem ctx_nil_lookup (n : Nat) : ([] : Ctx).get? n = none := by
  cases n <;> rfl

-- ══════════════════════════════════════════════════════════════
-- SECTION 16 : MULTI-STEP COMPOSITIONS
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
-- SECTION 17 : STEP EXAMPLES
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

end RefinementTypes
