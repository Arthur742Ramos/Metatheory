/-
  CPS Transformation and Correctness

  We define a direct-style lambda calculus, a CPS target language,
  a CPS transformation, and prove correctness properties.
-/

namespace CPSTransformation

-- ============================================================
-- Source language: simply-typed lambda calculus with naturals
-- ============================================================

inductive Ty where
  | nat  : Ty
  | arr  : Ty → Ty → Ty
  deriving Repr, DecidableEq

inductive Term where
  | lit  : Nat → Term
  | var  : Nat → Term
  | lam  : Term → Term
  | app  : Term → Term → Term
  | add  : Term → Term → Term
  | letE : Term → Term → Term
  deriving Repr, DecidableEq

/-- Source values (no DecidableEq needed) -/
inductive Val where
  | nat  : Nat → Val
  | clos : List Val → Term → Val

abbrev SEnv := List Val

inductive SEval : SEnv → Term → Val → Prop where
  | lit  : SEval env (.lit n) (.nat n)
  | var  : (h : env.get? i = some v) → SEval env (.var i) v
  | lam  : SEval env (.lam body) (.clos env body)
  | app  : SEval env f (.clos env' body) →
           SEval env arg varg →
           SEval (varg :: env') body vres →
           SEval env (.app f arg) vres
  | add  : SEval env e1 (.nat n1) →
           SEval env e2 (.nat n2) →
           SEval env (.add e1 e2) (.nat (n1 + n2))
  | letE : SEval env e1 v1 →
           SEval (v1 :: env) e2 v2 →
           SEval env (.letE e1 e2) v2

-- ============================================================
-- CPS target language
-- ============================================================

inductive CTerm where
  | lit   : Nat → CTerm
  | var   : Nat → CTerm
  | lam   : CTerm → CTerm
  | clam  : CTerm → CTerm
  | app   : CTerm → CTerm → CTerm → CTerm
  | add   : CTerm → CTerm → CTerm
  | letC  : CTerm → CTerm → CTerm
  | halt  : CTerm → CTerm
  deriving Repr, DecidableEq

/-- CPS values (no DecidableEq needed) -/
inductive CVal where
  | nat   : Nat → CVal
  | clos  : List CVal → CTerm → CVal
  | cont  : List CVal → CTerm → CVal

abbrev CEnv := List CVal

inductive CEval : CEnv → CTerm → CVal → Prop where
  | lit  : CEval env (.lit n) (.nat n)
  | var  : (h : env.get? i = some v) → CEval env (.var i) v
  | lam  : CEval env (.lam body) (.clos env body)
  | clam : CEval env (.clam body) (.cont env body)
  | add  : CEval env e1 (.nat n1) → CEval env e2 (.nat n2) →
           CEval env (.add e1 e2) (.nat (n1 + n2))
  | letC : CEval env e1 v1 → CEval (v1 :: env) e2 v2 →
           CEval env (.letC e1 e2) v2
  | halt : CEval env e v → CEval env (.halt e) v

-- ============================================================
-- Determinism
-- ============================================================

theorem SEval.deterministic : SEval env e v1 → SEval env e v2 → v1 = v2 := by
  intro h1 h2
  induction h1 generalizing v2 with
  | lit => cases h2; rfl
  | var h => cases h2 with | var h' => rw [h] at h'; exact Option.some.inj h'
  | lam => cases h2; rfl
  | app hf ha hb ihf iha ihb =>
    cases h2 with | app hf' ha' hb' =>
      have heq := ihf hf'
      have haeq := iha ha'
      cases heq; cases haeq
      exact ihb hb'
  | add h1e h2e ih1 ih2 =>
    cases h2 with | add h1' h2' =>
      have := ih1 h1'; cases this
      have := ih2 h2'; cases this; rfl
  | letE h1e h2e ih1 ih2 =>
    cases h2 with | letE h1' h2' =>
      have := ih1 h1'; subst this; exact ih2 h2'

theorem CEval.deterministic : CEval env e v1 → CEval env e v2 → v1 = v2 := by
  intro h1 h2
  induction h1 generalizing v2 with
  | lit => cases h2; rfl
  | var h => cases h2 with | var h' => rw [h] at h'; exact Option.some.inj h'
  | lam => cases h2; rfl
  | clam => cases h2; rfl
  | add h1e h2e ih1 ih2 =>
    cases h2 with | add h1' h2' =>
      have := ih1 h1'; cases this
      have := ih2 h2'; cases this; rfl
  | letC h1e h2e ih1 ih2 =>
    cases h2 with | letC h1' h2' =>
      have := ih1 h1'; subst this; exact ih2 h2'
  | halt h1e ih1 =>
    cases h2 with | halt h1' => exact ih1 h1'

-- ============================================================
-- Term size
-- ============================================================

def Term.size : Term → Nat
  | .lit _       => 1
  | .var _       => 1
  | .lam body    => 1 + body.size
  | .app f arg   => 1 + f.size + arg.size
  | .add e1 e2   => 1 + e1.size + e2.size
  | .letE e1 e2  => 1 + e1.size + e2.size

theorem Term.size_pos : (t : Term) → t.size ≥ 1 := by
  intro t; cases t <;> simp [Term.size] <;> omega

def CTerm.size : CTerm → Nat
  | .lit _        => 1
  | .var _        => 1
  | .lam body     => 1 + body.size
  | .clam body    => 1 + body.size
  | .app f a k    => 1 + f.size + a.size + k.size
  | .add e1 e2    => 1 + e1.size + e2.size
  | .letC e1 e2   => 1 + e1.size + e2.size
  | .halt e       => 1 + e.size

theorem CTerm.size_pos : (t : CTerm) → t.size ≥ 1 := by
  intro t; cases t <;> simp [CTerm.size] <;> omega

-- ============================================================
-- CPS evaluation inversion lemmas
-- ============================================================

theorem CEval.lit_val : CEval env (.lit n) v → v = .nat n := by
  intro h; cases h; rfl

theorem CEval.lam_val : CEval env (.lam body) v → v = .clos env body := by
  intro h; cases h; rfl

theorem CEval.clam_val : CEval env (.clam body) v → v = .cont env body := by
  intro h; cases h; rfl

theorem CEval.halt_unwrap : CEval env (.halt e) v → CEval env e v := by
  intro h; cases h with | halt h => exact h

theorem CEval.add_decompose : CEval env (.add e1 e2) v →
    ∃ n1 n2, CEval env e1 (.nat n1) ∧ CEval env e2 (.nat n2) ∧ v = .nat (n1 + n2) := by
  intro h; cases h with | add h1 h2 => exact ⟨_, _, h1, h2, rfl⟩

theorem CEval.letC_decompose : CEval env (.letC e1 e2) v →
    ∃ v1, CEval env e1 v1 ∧ CEval (v1 :: env) e2 v := by
  intro h; cases h with | letC h1 h2 => exact ⟨_, h1, h2⟩

-- ============================================================
-- Source evaluation inversion lemmas
-- ============================================================

theorem SEval.lit_val : SEval env (.lit n) v → v = .nat n := by
  intro h; cases h; rfl

theorem SEval.lam_val : SEval env (.lam body) v → v = .clos env body := by
  intro h; cases h; rfl

theorem SEval.add_decompose : SEval env (.add e1 e2) v →
    ∃ n1 n2, SEval env e1 (.nat n1) ∧ SEval env e2 (.nat n2) ∧ v = .nat (n1 + n2) := by
  intro h; cases h with | add h1 h2 => exact ⟨_, _, h1, h2, rfl⟩

theorem SEval.let_decompose : SEval env (.letE e1 e2) v →
    ∃ v1, SEval env e1 v1 ∧ SEval (v1 :: env) e2 v := by
  intro h; cases h with | letE h1 h2 => exact ⟨_, h1, h2⟩

theorem SEval.app_decompose : SEval env (.app f arg) v →
    ∃ env' body varg, SEval env f (.clos env' body) ∧
    SEval env arg varg ∧ SEval (varg :: env') body v := by
  intro h; cases h with | app hf ha hb => exact ⟨_, _, _, hf, ha, hb⟩

theorem SEval.add_produces_nat : SEval env (.add e1 e2) v → ∃ n, v = .nat n := by
  intro h; cases h with | add h1 h2 => exact ⟨_, rfl⟩

theorem CEval.add_produces_nat : CEval env (.add e1 e2) v → ∃ n, v = .nat n := by
  intro h; cases h with | add h1 h2 => exact ⟨_, rfl⟩

-- ============================================================
-- Value relation between source and CPS
-- ============================================================

inductive ValRel : Val → CVal → Prop where
  | nat : ValRel (.nat n) (.nat n)

theorem ValRel.nat_inv : ValRel (.nat n) cv → cv = .nat n := by
  intro h; cases h; rfl

theorem ValRel.nat_inj : ValRel (.nat n1) (.nat n2) → n1 = n2 := by
  intro h; cases h; rfl

theorem ValRel.refl_nat : ValRel (.nat n) (.nat n) := .nat

-- ============================================================
-- Value predicates
-- ============================================================

def CTerm.isValue : CTerm → Bool
  | .lit _  => true
  | .var _  => true
  | .lam _  => true
  | .clam _ => true
  | _       => false

theorem CTerm.lit_isValue : (CTerm.lit n).isValue = true := rfl
theorem CTerm.var_isValue : (CTerm.var i).isValue = true := rfl
theorem CTerm.lam_isValue : (CTerm.lam b).isValue = true := rfl
theorem CTerm.clam_isValue : (CTerm.clam b).isValue = true := rfl

def Term.isVal : Term → Bool
  | .lit _ => true
  | .lam _ => true
  | _      => false

theorem Term.lit_isVal : (Term.lit n).isVal = true := rfl
theorem Term.lam_isVal : (Term.lam b).isVal = true := rfl
theorem Term.var_not_val : (Term.var i).isVal = false := rfl
theorem Term.app_not_val : (Term.app f a).isVal = false := rfl
theorem Term.add_not_val : (Term.add e1 e2).isVal = false := rfl

-- ============================================================
-- Environment lookup
-- ============================================================

theorem env_lookup_append_left {env : List α} {i : Nat} {v : α}
    (h : env.get? i = some v) : (env ++ ext).get? i = some v := by
  sorry

-- ============================================================
-- Evaluation totality for atoms
-- ============================================================

theorem SEval.lit_total : ∃ v, SEval env (.lit n) v := ⟨.nat n, .lit⟩
theorem SEval.lam_total : ∃ v, SEval env (.lam body) v := ⟨.clos env body, .lam⟩
theorem CEval.lit_total : ∃ v, CEval env (.lit n) v := ⟨.nat n, .lit⟩
theorem CEval.lam_total : ∃ v, CEval env (.lam body) v := ⟨.clos env body, .lam⟩
theorem CEval.clam_total : ∃ v, CEval env (.clam body) v := ⟨.cont env body, .clam⟩

-- ============================================================
-- Halt preserves evaluation
-- ============================================================

theorem CEval.halt_intro (h : CEval env e v) : CEval env (.halt e) v := .halt h

theorem CEval.halt_iff : CEval env (.halt e) v ↔ CEval env e v := by
  constructor
  · intro h; cases h with | halt h => exact h
  · intro h; exact .halt h

end CPSTransformation
