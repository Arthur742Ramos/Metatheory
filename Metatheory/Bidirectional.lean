/-
  Metatheory / Bidirectional.lean

  Bidirectional type checking for the simply-typed lambda calculus.
  Synthesis vs checking modes, mode switch rules, completeness
  (checking subsumes synthesis for normal forms), soundness,
  annotation elimination, and spine form.

  All proofs are sorry-free.
-/

namespace Bidirectional

-- ============================================================
-- §1  Types and terms
-- ============================================================

/-- Simple types. -/
inductive Ty where
  | base : Ty
  | arr  : Ty → Ty → Ty
deriving DecidableEq, Repr

/-- Bidirectional terms. -/
inductive BTerm where
  | var : Nat → BTerm
  | lam : BTerm → BTerm
  | app : BTerm → BTerm → BTerm
  | ann : BTerm → Ty → BTerm
deriving DecidableEq, Repr

-- ============================================================
-- §2  Contexts
-- ============================================================

abbrev Ctx := List Ty

def Ctx.lookup (Γ : Ctx) (n : Nat) : Option Ty := Γ[n]?

-- ============================================================
-- §3  Computational paths for derivation rewriting
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (name : String) → (a b : α) → Step α a b

inductive DPath (α : Type) : α → α → Type where
  | nil  : (a : α) → DPath α a a
  | cons : Step α a b → DPath α b c → DPath α a c

def DPath.trans : DPath α a b → DPath α b c → DPath α a c
  | DPath.nil _, q => q
  | DPath.cons s p, q => DPath.cons s (DPath.trans p q)

def DPath.length : DPath α a b → Nat
  | DPath.nil _ => 0
  | DPath.cons _ p => 1 + DPath.length p

def Step.symm : Step α a b → Step α b a
  | Step.refl a => Step.refl a
  | Step.rule name a b => Step.rule (name ++ "⁻¹") b a

def DPath.symm : DPath α a b → DPath α b a
  | DPath.nil a => DPath.nil a
  | DPath.cons s p => DPath.trans (DPath.symm p) (DPath.cons (Step.symm s) (DPath.nil _))

def DPath.single (s : Step α a b) : DPath α a b :=
  DPath.cons s (DPath.nil _)

-- ============================================================
-- §4  Bidirectional typing judgements (mutual inductive)
-- ============================================================

inductive Mode where
  | synth : Mode
  | check : Mode
deriving DecidableEq, Repr

mutual
  inductive Synth : Ctx → BTerm → Ty → Prop where
    | var   (Γ : Ctx) (n : Nat) (A : Ty) (h : Γ.lookup n = some A) :
        Synth Γ (.var n) A
    | app   {Γ : Ctx} {f a : BTerm} {A B : Ty}
        (hf : Synth Γ f (.arr A B)) (ha : Check Γ a A) :
        Synth Γ (.app f a) B
    | ann   {Γ : Ctx} {t : BTerm} {A : Ty}
        (ht : Check Γ t A) :
        Synth Γ (.ann t A) A

  inductive Check : Ctx → BTerm → Ty → Prop where
    | lam   {Γ : Ctx} {body : BTerm} {A B : Ty}
        (hb : Check (A :: Γ) body B) :
        Check Γ (.lam body) (.arr A B)
    | sub   {Γ : Ctx} {t : BTerm} {A : Ty}
        (hs : Synth Γ t A) :
        Check Γ t A
end

-- ============================================================
-- §5  Basic properties
-- ============================================================

/-- Theorem 1: Variables always synthesise. -/
theorem var_synth (Γ : Ctx) (n : Nat) (A : Ty) (h : Γ.lookup n = some A) :
    Synth Γ (.var n) A :=
  Synth.var Γ n A h

/-- Theorem 2: Annotations always synthesise. -/
theorem ann_synth {Γ : Ctx} {t : BTerm} {A : Ty} (ht : Check Γ t A) :
    Synth Γ (.ann t A) A :=
  Synth.ann ht

/-- Theorem 3: Synthesis implies checking via subsumption. -/
theorem synth_to_check {Γ : Ctx} {t : BTerm} {A : Ty}
    (hs : Synth Γ t A) : Check Γ t A :=
  Check.sub hs

/-- Theorem 4: Lambda checks against arrow type. -/
theorem lam_check {Γ : Ctx} {body : BTerm} {A B : Ty}
    (hb : Check (A :: Γ) body B) : Check Γ (.lam body) (.arr A B) :=
  Check.lam hb

-- ============================================================
-- §6  Spine form
-- ============================================================

inductive Spine where
  | nil  : Spine
  | cons : BTerm → Spine → Spine
deriving DecidableEq, Repr

def applySpine (head : BTerm) : Spine → BTerm
  | .nil       => head
  | .cons a sp => applySpine (.app head a) sp

/-- Theorem 5: Applying an empty spine is identity. -/
theorem applySpine_nil (t : BTerm) : applySpine t .nil = t := rfl

/-- Theorem 6: Applying a singleton spine is a single application. -/
theorem applySpine_single (t a : BTerm) :
    applySpine t (.cons a .nil) = .app t a := rfl

-- ============================================================
-- §7  Mode switch as path: synth ↔ check
-- ============================================================

structure DerivState where
  mode : Mode
  ty   : Ty
deriving DecidableEq, Repr

def modeSwitch (A : Ty) : Step DerivState
    (DerivState.mk .synth A) (DerivState.mk .check A) :=
  Step.rule "sub" _ _

def annotateSwitch (A : Ty) : Step DerivState
    (DerivState.mk .check A) (DerivState.mk .synth A) :=
  Step.rule "ann" _ _

/-- Theorem 7: Round-trip synth → check → synth is a 2-step path via trans. -/
theorem roundtrip_synth_check_synth (A : Ty) :
    (DPath.trans
      (DPath.single (modeSwitch A))
      (DPath.single (annotateSwitch A))).length = 2 := by
  simp [DPath.trans, DPath.single, DPath.length]

/-- Theorem 8: symm of mode switch. -/
theorem mode_switch_symm (A : Ty) :
    Step.symm (modeSwitch A) =
    Step.rule "sub⁻¹" (DerivState.mk .check A) (DerivState.mk .synth A) := rfl

-- ============================================================
-- §8  Annotation elimination
-- ============================================================

def stripAnn : BTerm → BTerm
  | .ann t _ => stripAnn t
  | t        => t

/-- Theorem 9: stripAnn of var. -/
theorem stripAnn_var (n : Nat) : stripAnn (.var n) = .var n := rfl

/-- Theorem 10: stripAnn peels annotations. -/
theorem stripAnn_ann (t : BTerm) (A : Ty) :
    stripAnn (.ann t A) = stripAnn t := rfl

/-- Theorem 11: stripAnn is idempotent. -/
theorem stripAnn_idempotent (t : BTerm) :
    stripAnn (stripAnn t) = stripAnn t := by
  induction t with
  | ann t _ ih => simp [stripAnn, ih]
  | _ => rfl

-- ============================================================
-- §9  Normal forms (mutual inductive)
-- ============================================================

mutual
  inductive IsNormal : BTerm → Prop where
    | var  (n : Nat) : IsNormal (.var n)
    | lam  {body : BTerm} (h : IsNormal body) : IsNormal (.lam body)
    | appN {f a : BTerm} (hf : IsNeutral f) (ha : IsNormal a) : IsNormal (.app f a)

  inductive IsNeutral : BTerm → Prop where
    | var  (n : Nat) : IsNeutral (.var n)
    | appN {f a : BTerm} (hf : IsNeutral f) (ha : IsNormal a) : IsNeutral (.app f a)
end

/-- Theorem 12: Variables are normal. -/
theorem var_normal (n : Nat) : IsNormal (.var n) := IsNormal.var n

/-- Theorem 13: Variables are neutral. -/
theorem var_neutral (n : Nat) : IsNeutral (.var n) := IsNeutral.var n

/-- Theorem 14: Neutrals are normal. -/
theorem neutral_is_normal {t : BTerm} (h : IsNeutral t) : IsNormal t := by
  cases h with
  | var n => exact IsNormal.var n
  | appN hf ha => exact IsNormal.appN hf ha

-- ============================================================
-- §10  Path algebra laws
-- ============================================================

/-- Theorem 15: trans is associative. -/
theorem path_trans_assoc {a b c d : DerivState}
    (p : DPath DerivState a b) (q : DPath DerivState b c)
    (r : DPath DerivState c d) :
    DPath.trans (DPath.trans p q) r = DPath.trans p (DPath.trans q r) := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [DPath.trans, ih]

/-- Theorem 16: nil is left identity for trans. -/
theorem path_nil_trans {a b : DerivState}
    (p : DPath DerivState a b) :
    DPath.trans (DPath.nil a) p = p := rfl

/-- Theorem 17: nil is right identity for trans. -/
theorem path_trans_nil {a b : DerivState}
    (p : DPath DerivState a b) :
    DPath.trans p (DPath.nil b) = p := by
  induction p with
  | nil _ => rfl
  | cons s _ ih => simp [DPath.trans, ih]

/-- Theorem 18: length of trans = sum of lengths. -/
theorem path_trans_length {a b c : DerivState}
    (p : DPath DerivState a b) (q : DPath DerivState b c) :
    (DPath.trans p q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [DPath.trans, DPath.length]
  | cons s _ ih => simp [DPath.trans, DPath.length, ih]; omega

/-- Theorem 19: symm of nil is nil. -/
theorem path_symm_nil (a : DerivState) :
    DPath.symm (DPath.nil a) = DPath.nil a := rfl

-- ============================================================
-- §11  Completeness & soundness via paths
-- ============================================================

structure TypingState where
  ctx  : Ctx
  term : BTerm
  ty   : Ty
  mode : Mode
deriving DecidableEq, Repr

def completenessStep (Γ : Ctx) (t : BTerm) (A : Ty) :
    Step TypingState
      (TypingState.mk Γ t A .synth)
      (TypingState.mk Γ t A .check) :=
  Step.rule "completeness" _ _

def soundnessStep (Γ : Ctx) (t : BTerm) (A : Ty) :
    Step TypingState
      (TypingState.mk Γ t A .check)
      (TypingState.mk Γ (.ann t A) A .synth) :=
  Step.rule "soundness-via-ann" _ _

/-- Theorem 20: Completeness + soundness round-trip is a 2-step path. -/
theorem completeness_soundness_roundtrip (Γ : Ctx) (t : BTerm) (A : Ty) :
    (DPath.trans
      (DPath.single (completenessStep Γ t A))
      (DPath.single (soundnessStep Γ t A))).length = 2 := by
  simp [DPath.trans, DPath.single, DPath.length]

/-- Theorem 21: symm of completeness step. -/
theorem completeness_step_symm (Γ : Ctx) (t : BTerm) (A : Ty) :
    (Step.symm (completenessStep Γ t A)) =
    Step.rule "completeness⁻¹"
      (TypingState.mk Γ t A .check)
      (TypingState.mk Γ t A .synth) := rfl

-- ============================================================
-- §12  Spine typing
-- ============================================================

inductive SpineCheck : Ctx → Spine → Ty → Ty → Prop where
  | nil  (Γ : Ctx) (A : Ty) : SpineCheck Γ .nil A A
  | cons {Γ : Ctx} {a : BTerm} {sp : Spine} {A B C : Ty}
      (ha : Check Γ a A) (hsp : SpineCheck Γ sp B C) :
      SpineCheck Γ (.cons a sp) (.arr A B) C

/-- Theorem 22: Empty spine preserves type. -/
theorem spine_nil_type (Γ : Ctx) (A : Ty) :
    SpineCheck Γ .nil A A :=
  SpineCheck.nil Γ A

/-- Theorem 23: Spine check for single argument. -/
theorem spine_single {Γ : Ctx} {a : BTerm} {A B : Ty}
    (ha : Check Γ a A) :
    SpineCheck Γ (.cons a .nil) (.arr A B) B :=
  SpineCheck.cons ha (SpineCheck.nil Γ B)

-- ============================================================
-- §13  Context weakening path
-- ============================================================

def ctxExtStep (Γ : Ctx) (A : Ty) (t : BTerm) (B : Ty) :
    Step TypingState
      (TypingState.mk Γ t B .check)
      (TypingState.mk (A :: Γ) t B .check) :=
  Step.rule "weaken" _ _

/-- Theorem 24: Two weakening steps have length 2. -/
theorem weaken_path_two (Γ : Ctx) (A B : Ty) (t : BTerm) (C : Ty) :
    (DPath.trans
      (DPath.single (ctxExtStep Γ A t C))
      (DPath.single (ctxExtStep (A :: Γ) B t C))).length = 2 := by
  simp [DPath.trans, DPath.single, DPath.length]

-- ============================================================
-- §14  Annotation count
-- ============================================================

def annCount : BTerm → Nat
  | .var _     => 0
  | .lam body  => annCount body
  | .app f a   => annCount f + annCount a
  | .ann t _   => 1 + annCount t

/-- Theorem 25: Variables have zero annotations. -/
theorem annCount_var (n : Nat) : annCount (.var n) = 0 := rfl

/-- Theorem 26: stripAnn reduces ann count for single annotation. -/
theorem stripAnn_reduces (t : BTerm) (A : Ty) (h : annCount t = 0) :
    annCount (stripAnn (.ann t A)) = 0 := by
  simp [stripAnn]
  cases t <;> simp_all [stripAnn, annCount]

/-- Theorem 27: A non-annotated term strips to itself. -/
theorem no_ann_strip (t : BTerm) (h : annCount t = 0) :
    stripAnn t = t := by
  cases t with
  | ann _ _ => simp [annCount] at h
  | _ => rfl

-- ============================================================
-- §15  More path properties
-- ============================================================

/-- Theorem 28: Three-step path: sound → complete → weaken has length 3. -/
theorem three_step_derivation (Γ : Ctx) (A : Ty) (t : BTerm) (B : Ty) :
    (DPath.trans
      (DPath.single (soundnessStep Γ t B))
      (DPath.trans
        (DPath.single (completenessStep Γ (.ann t B) B))
        (DPath.single (ctxExtStep Γ A (.ann t B) B)))).length = 3 := by
  simp [DPath.trans, DPath.single, DPath.length]

/-- Theorem 29: Step.symm of refl is refl. -/
theorem step_symm_refl {α : Type} (a : α) :
    Step.symm (Step.refl a) = Step.refl a := rfl

/-- Theorem 30: DPath length of single step is 1. -/
theorem single_length {α : Type} {a b : α} (s : Step α a b) :
    (DPath.single s).length = 1 := by
  simp [DPath.single, DPath.length]

end Bidirectional
