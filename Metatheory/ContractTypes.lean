/-
  Metatheory.ContractTypes
  ========================
  Contract types, blame tracking, higher-order contracts, and
  contract composition for a typed λ-calculus with monitoring.
  Pure Lean 4 — no Mathlib.
-/

namespace ContractTypes

-- ════════════════════════════════════════════════════════════════════
-- 1. Types and Blame labels
-- ════════════════════════════════════════════════════════════════════

inductive Ty where
  | base  : Ty
  | fn    : Ty → Ty → Ty
  | contr : Ty → Ty
  deriving DecidableEq, Repr

inductive Blame where
  | pos : Nat → Blame
  | neg : Nat → Blame
  deriving DecidableEq, Repr

def Blame.flip : Blame → Blame
  | .pos n => .neg n
  | .neg n => .pos n

-- Thm 1
theorem blame_flip_flip (b : Blame) : b.flip.flip = b := by
  cases b <;> simp [Blame.flip]

-- Thm 2
theorem blame_flip_ne (b : Blame) : b.flip ≠ b := by
  cases b <;> simp [Blame.flip]

-- Thm 3
theorem blame_pos_ne_neg {n m : Nat} : Blame.pos n ≠ Blame.neg m := by
  intro h; cases h

-- Thm 4
theorem blame_flip_pos {n : Nat} : (Blame.pos n).flip = Blame.neg n := rfl

-- Thm 5
theorem blame_flip_neg {n : Nat} : (Blame.neg n).flip = Blame.pos n := rfl

-- ════════════════════════════════════════════════════════════════════
-- 2. Contracts
-- ════════════════════════════════════════════════════════════════════

inductive Contract where
  | flat : Nat → Contract
  | func : Contract → Contract → Contract
  | conj : Contract → Contract → Contract
  | disj : Contract → Contract → Contract
  | any  : Contract
  | none : Contract
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════════
-- 3. Terms with monitoring
-- ════════════════════════════════════════════════════════════════════

inductive Term where
  | var   : Nat → Term
  | lam   : Ty → Term → Term
  | app   : Term → Term → Term
  | unit  : Term
  | blame : Blame → Term
  | mon   : Blame → Contract → Term → Term
  deriving DecidableEq, Repr

inductive IsVal : Term → Prop where
  | unit : IsVal .unit
  | lam  : IsVal (.lam τ body)

-- Thm 6
theorem isval_unit : IsVal Term.unit := .unit

-- Thm 7
theorem isval_lam {τ : Ty} {body : Term} : IsVal (.lam τ body) := .lam

-- Thm 8
theorem isval_not_var {n : Nat} : ¬IsVal (.var n) := by intro h; cases h

-- Thm 9
theorem isval_not_app {t1 t2 : Term} : ¬IsVal (.app t1 t2) := by intro h; cases h

-- Thm 10
theorem isval_not_blame {b : Blame} : ¬IsVal (.blame b) := by intro h; cases h

-- ════════════════════════════════════════════════════════════════════
-- 4. Contract satisfaction
-- ════════════════════════════════════════════════════════════════════

def FlatOracle := Nat → Term → Prop

inductive Satisfies (O : FlatOracle) : Contract → Term → Prop where
  | flat  : O n v → IsVal v → Satisfies O (.flat n) v
  | any   : IsVal v → Satisfies O .any v
  | conjI : Satisfies O c1 v → Satisfies O c2 v → Satisfies O (.conj c1 c2) v
  | disjL : Satisfies O c1 v → Satisfies O (.disj c1 c2) v
  | disjR : Satisfies O c2 v → Satisfies O (.disj c1 c2) v

-- Thm 11
theorem satisfies_any_of_val {O : FlatOracle} {v : Term}
    (hv : IsVal v) : Satisfies O .any v := .any hv

-- Thm 12
theorem satisfies_conj_left {O : FlatOracle} {c1 c2 : Contract} {v : Term}
    (h : Satisfies O (.conj c1 c2) v) : Satisfies O c1 v := by
  cases h with | conjI h1 _ => exact h1

-- Thm 13
theorem satisfies_conj_right {O : FlatOracle} {c1 c2 : Contract} {v : Term}
    (h : Satisfies O (.conj c1 c2) v) : Satisfies O c2 v := by
  cases h with | conjI _ h2 => exact h2

-- Thm 14
theorem satisfies_disj_cases {O : FlatOracle} {c1 c2 : Contract} {v : Term} {P : Prop}
    (h : Satisfies O (.disj c1 c2) v)
    (hl : Satisfies O c1 v → P)
    (hr : Satisfies O c2 v → P) : P := by
  cases h with
  | disjL h => exact hl h
  | disjR h => exact hr h

-- Thm 15
theorem satisfies_none_empty {O : FlatOracle} {v : Term} :
    ¬Satisfies O .none v := by intro h; cases h

-- ════════════════════════════════════════════════════════════════════
-- 5. Small-step reduction
-- ════════════════════════════════════════════════════════════════════

inductive Step : Term → Term → Prop where
  | appL    : Step t1 t1' → Step (.app t1 t2) (.app t1' t2)
  | appR    : IsVal v → Step t2 t2' → Step (.app v t2) (.app v t2')
  | monVal  : IsVal v → Step (.mon b .any v) v
  | monNone : IsVal v → Step (.mon b .none v) (.blame b)
  | monConj : Step (.mon b (.conj c1 c2) t) (.mon b c2 (.mon b c1 t))
  | monDisj : Step (.mon b (.disj c1 c2) t) (.mon b c1 t)
  | monStep : Step t t' → Step (.mon b c t) (.mon b c t')

inductive Steps : Term → Term → Prop where
  | refl : Steps t t
  | step : Step t1 t2 → Steps t2 t3 → Steps t1 t3

-- Thm 16
theorem steps_trans {t1 t2 t3 : Term}
    (h12 : Steps t1 t2) (h23 : Steps t2 t3) : Steps t1 t3 := by
  induction h12 with
  | refl => exact h23
  | step hs _ ih => exact .step hs (ih h23)

-- Thm 17
theorem step_to_steps {t1 t2 : Term} (h : Step t1 t2) : Steps t1 t2 :=
  .step h .refl

-- Thm 18
theorem steps_appL {t1 t1' t2 : Term}
    (h : Steps t1 t1') : Steps (.app t1 t2) (.app t1' t2) := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.appL hs) ih

-- Thm 19
theorem steps_appR {v t2 t2' : Term}
    (hv : IsVal v) (h : Steps t2 t2') : Steps (.app v t2) (.app v t2') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.appR hv hs) ih

-- Thm 20
theorem steps_mon {b : Blame} {c : Contract} {t t' : Term}
    (h : Steps t t') : Steps (.mon b c t) (.mon b c t') := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact .step (.monStep hs) ih

-- Thm 21
theorem isval_not_step {v : Term} (hv : IsVal v) {t : Term} :
    ¬Step v t := by intro h; cases hv <;> cases h

-- Thm 22
theorem isval_steps_eq {v t : Term} (hv : IsVal v) (h : Steps v t) : t = v := by
  cases h with
  | refl => rfl
  | step hs _ => exact absurd hs (isval_not_step hv)

-- Thm 23
theorem mon_any_steps_to_val {b : Blame} {v : Term} (hv : IsVal v) :
    Steps (.mon b .any v) v :=
  .step (.monVal hv) .refl

-- Thm 24
theorem mon_none_steps_to_blame {b : Blame} {v : Term} (hv : IsVal v) :
    Steps (.mon b .none v) (.blame b) :=
  .step (.monNone hv) .refl

-- Thm 25
theorem mon_conj_steps {b : Blame} {c1 c2 : Contract} {t : Term} :
    Steps (.mon b (.conj c1 c2) t) (.mon b c2 (.mon b c1 t)) :=
  .step .monConj .refl

-- ════════════════════════════════════════════════════════════════════
-- 6. Contract equivalence
-- ════════════════════════════════════════════════════════════════════

def ContractEquiv (O : FlatOracle) (c1 c2 : Contract) : Prop :=
  ∀ v, Satisfies O c1 v ↔ Satisfies O c2 v

-- Thm 26
theorem contract_equiv_refl {O : FlatOracle} (c : Contract) :
    ContractEquiv O c c := fun _ => Iff.rfl

-- Thm 27
theorem contract_equiv_symm {O : FlatOracle} {c1 c2 : Contract}
    (h : ContractEquiv O c1 c2) : ContractEquiv O c2 c1 :=
  fun v => (h v).symm

-- Thm 28
theorem contract_equiv_trans {O : FlatOracle} {c1 c2 c3 : Contract}
    (h12 : ContractEquiv O c1 c2) (h23 : ContractEquiv O c2 c3) :
    ContractEquiv O c1 c3 :=
  fun v => Iff.trans (h12 v) (h23 v)

-- Thm 29
theorem conj_comm {O : FlatOracle} {c1 c2 : Contract} :
    ContractEquiv O (.conj c1 c2) (.conj c2 c1) := by
  intro v; constructor
  · intro h; cases h with | conjI h1 h2 => exact .conjI h2 h1
  · intro h; cases h with | conjI h1 h2 => exact .conjI h2 h1

-- Thm 30
theorem disj_comm {O : FlatOracle} {c1 c2 : Contract} :
    ContractEquiv O (.disj c1 c2) (.disj c2 c1) := by
  intro v; constructor
  · intro h; cases h with
    | disjL h => exact .disjR h
    | disjR h => exact .disjL h
  · intro h; cases h with
    | disjL h => exact .disjR h
    | disjR h => exact .disjL h

-- Thm 31
theorem conj_idemp {O : FlatOracle} {c : Contract} :
    ContractEquiv O (.conj c c) c := by
  intro v; constructor
  · intro h; exact satisfies_conj_left h
  · intro h; exact .conjI h h

-- Thm 32
theorem disj_idemp {O : FlatOracle} {c : Contract} :
    ContractEquiv O (.disj c c) c := by
  intro v; constructor
  · intro h; cases h with
    | disjL h => exact h
    | disjR h => exact h
  · intro h; exact .disjL h

-- Helper: every satisfying value is indeed a value
theorem satisfies_isval {O : FlatOracle} {c : Contract} {v : Term}
    (h : Satisfies O c v) : IsVal v := by
  induction h with
  | flat _ hv => exact hv
  | any hv => exact hv
  | conjI _ _ ih _ => exact ih
  | disjL _ ih => exact ih
  | disjR _ ih => exact ih

-- Thm 33
theorem conj_any_right {O : FlatOracle} {c : Contract} :
    ContractEquiv O (.conj c .any) c := by
  intro v; constructor
  · intro h; exact satisfies_conj_left h
  · intro h; exact .conjI h (.any (satisfies_isval h))

-- ════════════════════════════════════════════════════════════════════
-- 7. Contract strength ordering
-- ════════════════════════════════════════════════════════════════════

def Stronger (O : FlatOracle) (c1 c2 : Contract) : Prop :=
  ∀ v, Satisfies O c1 v → Satisfies O c2 v

-- Thm 34
theorem stronger_refl {O : FlatOracle} (c : Contract) : Stronger O c c :=
  fun _ h => h

-- Thm 35
theorem stronger_trans {O : FlatOracle} {c1 c2 c3 : Contract}
    (h12 : Stronger O c1 c2) (h23 : Stronger O c2 c3) : Stronger O c1 c3 :=
  fun v h => h23 v (h12 v h)

-- Thm 36
theorem stronger_any {O : FlatOracle} (c : Contract) : Stronger O c .any :=
  fun v h => .any (satisfies_isval h)

-- Thm 37
theorem none_stronger {O : FlatOracle} (c : Contract) : Stronger O .none c :=
  fun v h => absurd h satisfies_none_empty

-- Thm 38
theorem conj_stronger_left {O : FlatOracle} {c1 c2 : Contract} :
    Stronger O (.conj c1 c2) c1 :=
  fun _ h => satisfies_conj_left h

-- Thm 39
theorem conj_stronger_right {O : FlatOracle} {c1 c2 : Contract} :
    Stronger O (.conj c1 c2) c2 :=
  fun _ h => satisfies_conj_right h

-- Thm 40
theorem disj_weaker_left {O : FlatOracle} {c1 c2 : Contract} :
    Stronger O c1 (.disj c1 c2) :=
  fun _ h => .disjL h

-- Thm 41
theorem disj_weaker_right {O : FlatOracle} {c1 c2 : Contract} :
    Stronger O c2 (.disj c1 c2) :=
  fun _ h => .disjR h

-- Thm 42
theorem stronger_conj_intro {O : FlatOracle} {c c1 c2 : Contract}
    (h1 : Stronger O c c1) (h2 : Stronger O c c2) :
    Stronger O c (.conj c1 c2) :=
  fun v h => .conjI (h1 v h) (h2 v h)

-- Thm 43
theorem stronger_disj_elim {O : FlatOracle} {c1 c2 c : Contract}
    (h1 : Stronger O c1 c) (h2 : Stronger O c2 c) :
    Stronger O (.disj c1 c2) c :=
  fun v h => by cases h with
  | disjL h => exact h1 v h
  | disjR h => exact h2 v h

-- Thm 44
theorem equiv_iff_stronger_both {O : FlatOracle} {c1 c2 : Contract} :
    ContractEquiv O c1 c2 ↔ (Stronger O c1 c2 ∧ Stronger O c2 c1) := by
  constructor
  · intro h; exact ⟨fun v => (h v).mp, fun v => (h v).mpr⟩
  · intro ⟨h1, h2⟩ v; exact ⟨h1 v, h2 v⟩

-- Thm 45
theorem stronger_conj_mono {O : FlatOracle} {c1 c1' c2 c2' : Contract}
    (h1 : Stronger O c1 c1') (h2 : Stronger O c2 c2') :
    Stronger O (.conj c1 c2) (.conj c1' c2') :=
  fun v h => by cases h with | conjI h1' h2' => exact .conjI (h1 v h1') (h2 v h2')

-- Thm 46
theorem stronger_disj_mono {O : FlatOracle} {c1 c1' c2 c2' : Contract}
    (h1 : Stronger O c1 c1') (h2 : Stronger O c2 c2') :
    Stronger O (.disj c1 c2) (.disj c1' c2') :=
  fun v h => by cases h with
  | disjL h => exact .disjL (h1 v h)
  | disjR h => exact .disjR (h2 v h)

-- Thm 47
theorem stronger_equiv {O : FlatOracle} {c1 c2 : Contract}
    (h : ContractEquiv O c1 c2) : Stronger O c1 c2 :=
  fun v hv => (h v).mp hv

-- Thm 48
theorem conj_absorb_disj {O : FlatOracle} {c1 c2 : Contract} :
    Stronger O (.conj c1 (.disj c1 c2)) c1 :=
  fun _ h => satisfies_conj_left h

-- Thm 49
theorem disj_absorb_conj_intro {O : FlatOracle} {c1 c2 : Contract} :
    Stronger O c1 (.disj c1 (.conj c1 c2)) :=
  fun _ h => .disjL h

-- ════════════════════════════════════════════════════════════════════
-- 8. Blame safety
-- ════════════════════════════════════════════════════════════════════

def BlameSafe (b : Blame) (t : Term) : Prop :=
  ¬Steps t (.blame b)

-- Thm 50
theorem blame_safe_unit {b : Blame} : BlameSafe b .unit := by
  intro h; cases h with
  | step hs _ => exact absurd hs (isval_not_step .unit)

-- Thm 51
theorem blame_safe_var {b : Blame} {n : Nat} : BlameSafe b (.var n) := by
  intro h; cases h with
  | step hs _ => cases hs

-- Thm 52
theorem blame_safe_different {b b' : Blame} (hne : b ≠ b') :
    BlameSafe b (.blame b') := by
  intro h; cases h with
  | refl => exact hne rfl
  | step hs _ => cases hs

-- ════════════════════════════════════════════════════════════════════
-- 9. Contract composition
-- ════════════════════════════════════════════════════════════════════

def Contract.seq (c1 c2 : Contract) : Contract := .conj c1 c2
def Contract.par (c1 c2 : Contract) : Contract := .disj c1 c2

-- Thm 53
theorem seq_assoc {O : FlatOracle} {c1 c2 c3 : Contract} :
    ContractEquiv O (Contract.seq (Contract.seq c1 c2) c3)
                    (Contract.seq c1 (Contract.seq c2 c3)) := by
  intro v; simp [Contract.seq]; constructor
  · intro h; cases h with | conjI h12 h3 =>
    cases h12 with | conjI h1 h2 => exact .conjI h1 (.conjI h2 h3)
  · intro h; cases h with | conjI h1 h23 =>
    cases h23 with | conjI h2 h3 => exact .conjI (.conjI h1 h2) h3

-- Thm 54
theorem par_assoc {O : FlatOracle} {c1 c2 c3 : Contract} :
    ContractEquiv O (Contract.par (Contract.par c1 c2) c3)
                    (Contract.par c1 (Contract.par c2 c3)) := by
  intro v; simp [Contract.par]; constructor
  · intro h; cases h with
    | disjL h => cases h with
      | disjL h => exact .disjL h
      | disjR h => exact .disjR (.disjL h)
    | disjR h => exact .disjR (.disjR h)
  · intro h; cases h with
    | disjL h => exact .disjL (.disjL h)
    | disjR h => cases h with
      | disjL h => exact .disjL (.disjR h)
      | disjR h => exact .disjR h

-- Thm 55
theorem seq_comm {O : FlatOracle} {c1 c2 : Contract} :
    ContractEquiv O (Contract.seq c1 c2) (Contract.seq c2 c1) := by
  simp [Contract.seq]; exact conj_comm

-- Thm 56
theorem par_comm {O : FlatOracle} {c1 c2 : Contract} :
    ContractEquiv O (Contract.par c1 c2) (Contract.par c2 c1) := by
  simp [Contract.par]; exact disj_comm

-- ════════════════════════════════════════════════════════════════════
-- 10. Higher-order contracts
-- ════════════════════════════════════════════════════════════════════

inductive HOContract where
  | flat : Nat → HOContract
  | func : HOContract → HOContract → HOContract
  | pair : HOContract → HOContract → HOContract
  | any  : HOContract
  | none : HOContract
  deriving DecidableEq, Repr

def HOContract.order : HOContract → Nat
  | .flat _ => 0
  | .func d c => Nat.max d.order c.order + 1
  | .pair l r => Nat.max l.order r.order
  | .any => 0
  | .none => 0

-- Thm 57
theorem order_flat {n : Nat} : (HOContract.flat n).order = 0 := rfl

-- Thm 58
theorem order_func_pos {d c : HOContract} :
    (HOContract.func d c).order ≥ 1 := by
  simp [HOContract.order]

-- Thm 59
theorem order_any : HOContract.any.order = 0 := rfl

-- Thm 60
theorem order_none : HOContract.none.order = 0 := rfl

-- Thm 61
theorem order_pair_max {l r : HOContract} :
    (HOContract.pair l r).order = Nat.max l.order r.order := rfl

def HOContract.size : HOContract → Nat
  | .flat _ => 1
  | .func d c => d.size + c.size + 1
  | .pair l r => l.size + r.size + 1
  | .any => 1
  | .none => 1

-- Thm 62
theorem ho_size_pos (c : HOContract) : c.size ≥ 1 := by
  cases c <;> simp [HOContract.size] <;> omega

-- Thm 63
theorem ho_size_func {d c : HOContract} :
    (HOContract.func d c).size = d.size + c.size + 1 := rfl

-- ════════════════════════════════════════════════════════════════════
-- 11. Contract & term size
-- ════════════════════════════════════════════════════════════════════

def Contract.size : Contract → Nat
  | .flat _ => 1
  | .func d c => d.size + c.size + 1
  | .conj c1 c2 => c1.size + c2.size + 1
  | .disj c1 c2 => c1.size + c2.size + 1
  | .any => 1
  | .none => 1

-- Thm 64
theorem contract_size_pos (c : Contract) : c.size ≥ 1 := by
  cases c <;> simp [Contract.size] <;> omega

-- Thm 65
theorem contract_size_conj {c1 c2 : Contract} :
    (Contract.conj c1 c2).size = c1.size + c2.size + 1 := rfl

-- Thm 66
theorem contract_size_disj {c1 c2 : Contract} :
    (Contract.disj c1 c2).size = c1.size + c2.size + 1 := rfl

-- Thm 67
theorem contract_size_conj_gt {c1 c2 : Contract} :
    (Contract.conj c1 c2).size > c1.size := by
  simp [Contract.size]; omega

def monDepth : Term → Nat
  | .var _ => 0
  | .unit => 0
  | .lam _ body => monDepth body
  | .app t1 t2 => Nat.max (monDepth t1) (monDepth t2)
  | .blame _ => 0
  | .mon _ _ t => monDepth t + 1

-- Thm 68
theorem mon_depth_unit : monDepth .unit = 0 := rfl

-- Thm 69
theorem mon_depth_mon_pos {b : Blame} {c : Contract} {t : Term} :
    monDepth (.mon b c t) ≥ 1 := by simp [monDepth]

-- Thm 70
theorem mon_depth_app {t1 t2 : Term} :
    monDepth (.app t1 t2) = Nat.max (monDepth t1) (monDepth t2) := rfl

-- ════════════════════════════════════════════════════════════════════
-- 12. Positive contract predicate
-- ════════════════════════════════════════════════════════════════════

def PositiveContract : Contract → Prop
  | .flat _ => True
  | .any => True
  | .none => True
  | .conj c1 c2 => PositiveContract c1 ∧ PositiveContract c2
  | .disj c1 c2 => PositiveContract c1 ∧ PositiveContract c2
  | .func _ _ => False

-- Thm 71
theorem positive_any : PositiveContract .any := trivial

-- Thm 72
theorem positive_flat {n : Nat} : PositiveContract (.flat n) := trivial

-- Thm 73
theorem positive_none : PositiveContract .none := trivial

-- Thm 74
theorem positive_conj {c1 c2 : Contract}
    (h1 : PositiveContract c1) (h2 : PositiveContract c2) :
    PositiveContract (.conj c1 c2) := ⟨h1, h2⟩

-- Thm 75
theorem positive_disj {c1 c2 : Contract}
    (h1 : PositiveContract c1) (h2 : PositiveContract c2) :
    PositiveContract (.disj c1 c2) := ⟨h1, h2⟩

-- Thm 76
theorem not_positive_func {c1 c2 : Contract} :
    ¬PositiveContract (.func c1 c2) := id

-- ════════════════════════════════════════════════════════════════════
-- 13. Decidable flat contract checking
-- ════════════════════════════════════════════════════════════════════

def DecOracle := Nat → Term → Bool

def decSatisfies (O : DecOracle) : Contract → Term → Bool
  | .flat n, v => O n v
  | .any, _ => true
  | .none, _ => false
  | .conj c1 c2, v => decSatisfies O c1 v && decSatisfies O c2 v
  | .disj c1 c2, v => decSatisfies O c1 v || decSatisfies O c2 v
  | .func _ _, _ => false

-- Thm 77
theorem dec_any {O : DecOracle} {v : Term} : decSatisfies O .any v = true := rfl

-- Thm 78
theorem dec_none {O : DecOracle} {v : Term} : decSatisfies O .none v = false := rfl

-- Thm 79
theorem dec_conj_true {O : DecOracle} {c1 c2 : Contract} {v : Term}
    (h1 : decSatisfies O c1 v = true) (h2 : decSatisfies O c2 v = true) :
    decSatisfies O (.conj c1 c2) v = true := by
  simp [decSatisfies, h1, h2]

-- Thm 80
theorem dec_disj_left_true {O : DecOracle} {c1 c2 : Contract} {v : Term}
    (h1 : decSatisfies O c1 v = true) :
    decSatisfies O (.disj c1 c2) v = true := by
  simp [decSatisfies, h1]

-- Thm 81
theorem dec_disj_right_true {O : DecOracle} {c1 c2 : Contract} {v : Term}
    (h2 : decSatisfies O c2 v = true) :
    decSatisfies O (.disj c1 c2) v = true := by
  simp [decSatisfies, h2]

-- ════════════════════════════════════════════════════════════════════
-- 14. Contract depth
-- ════════════════════════════════════════════════════════════════════

def Contract.depth : Contract → Nat
  | .flat _ => 0
  | .func d c => Nat.max d.depth c.depth + 1
  | .conj c1 c2 => Nat.max c1.depth c2.depth + 1
  | .disj c1 c2 => Nat.max c1.depth c2.depth + 1
  | .any => 0
  | .none => 0

-- Thm 82
theorem depth_flat {n : Nat} : (Contract.flat n).depth = 0 := rfl

-- Thm 83
theorem depth_any : Contract.any.depth = 0 := rfl

-- Thm 84
theorem depth_conj {c1 c2 : Contract} :
    (Contract.conj c1 c2).depth = Nat.max c1.depth c2.depth + 1 := rfl

-- Thm 85
theorem depth_conj_pos {c1 c2 : Contract} :
    (Contract.conj c1 c2).depth ≥ 1 := by
  simp [Contract.depth]

end ContractTypes
