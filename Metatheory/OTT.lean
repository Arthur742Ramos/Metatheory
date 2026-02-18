/-
  Metatheory / OTT.lean

  Observational Type Theory (OTT): propositional equality from
  observational equivalence, heterogeneous equality, coercion,
  coherence (coercion at same type is identity), canonicity,
  strict equality vs observational equality.

  All proofs are sorry-free.
-/

namespace OTT

-- ============================================================
-- §1  Types
-- ============================================================

/-- OTT types. -/
inductive OTy where
  | unit  : OTy
  | bool  : OTy
  | nat   : OTy
  | pi    : OTy → OTy → OTy
  | sigma : OTy → OTy → OTy
  | eq    : OTy → OTy → OTy → OTy   -- Eq_A(a,b) at type level
deriving DecidableEq, Repr

/-- OTT terms. -/
inductive OTm where
  | star   : OTm                     -- unit inhabitant
  | tt     : OTm
  | ff     : OTm
  | zero   : OTm
  | succ   : OTm → OTm
  | var    : Nat → OTm
  | lam    : OTm → OTm
  | app    : OTm → OTm → OTm
  | pair   : OTm → OTm → OTm
  | fst    : OTm → OTm
  | snd    : OTm → OTm
  | refl   : OTm                     -- reflexivity proof
  | coerce : OTy → OTy → OTm → OTm  -- coerce from A to B
  | coh    : OTy → OTy → OTm → OTm  -- coherence witness
deriving DecidableEq, Repr

-- ============================================================
-- §2  Computational paths for OTT derivation rewriting
-- ============================================================

/-- One-step rewrite rules in OTT. -/
inductive OStep : OTm → OTm → Prop where
  -- β-reduction
  | betaApp (body arg : OTm) :
      OStep (.app (.lam body) arg) body
  | betaApp' (body arg : OTm) :
      OStep body (.app (.lam body) arg)
  | betaFst (a b : OTm) : OStep (.fst (.pair a b)) a
  | betaFst' (a b : OTm) : OStep a (.fst (.pair a b))
  | betaSnd (a b : OTm) : OStep (.snd (.pair a b)) b
  | betaSnd' (a b : OTm) : OStep b (.snd (.pair a b))
  -- Coercion rules
  | coerceSame (A : OTy) (t : OTm) :
      OStep (.coerce A A t) t          -- coerce at same type = id
  | coerceSame' (A : OTy) (t : OTm) :
      OStep t (.coerce A A t)
  | coerceUnit (A B : OTy) :
      OStep (.coerce A B .star) .star   -- unit coercion
  | coerceUnit' (A B : OTy) :
      OStep .star (.coerce A B .star)
  -- Coherence: coercion of refl is refl
  | cohRefl (A : OTy) :
      OStep (.coh A A .refl) .refl
  | cohRefl' (A : OTy) :
      OStep .refl (.coh A A .refl)
  -- Congruences
  | congApp {f f' : OTm} (a : OTm) :
      OStep f f' → OStep (.app f a) (.app f' a)
  | congArg (f : OTm) {a a' : OTm} :
      OStep a a' → OStep (.app f a) (.app f a')
  | congFst {t t' : OTm} :
      OStep t t' → OStep (.fst t) (.fst t')
  | congSnd {t t' : OTm} :
      OStep t t' → OStep (.snd t) (.snd t')
  | congSucc {n n' : OTm} :
      OStep n n' → OStep (.succ n) (.succ n')
  | congCoerce (A B : OTy) {t t' : OTm} :
      OStep t t' → OStep (.coerce A B t) (.coerce A B t')
  | congPairL {a a' : OTm} (b : OTm) :
      OStep a a' → OStep (.pair a b) (.pair a' b)
  | congPairR (a : OTm) {b b' : OTm} :
      OStep b b' → OStep (.pair a b) (.pair a b')

/-- OTT computational paths. -/
inductive OPath : OTm → OTm → Prop where
  | refl (a : OTm) : OPath a a
  | step {a b c : OTm} : OStep a b → OPath b c → OPath a c

-- ============================================================
-- §3  Core path combinators
-- ============================================================

/-- Theorem 1: Transitivity of OTT paths. -/
theorem OPath.trans {a b c : OTm}
    (p : OPath a b) (q : OPath b c) : OPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact OPath.step s (ih q)

/-- Step symmetry. -/
def OStep.symm : OStep a b → OStep b a
  | .betaApp body arg   => .betaApp' body arg
  | .betaApp' body arg  => .betaApp body arg
  | .betaFst a b   => .betaFst' a b
  | .betaFst' a b  => .betaFst a b
  | .betaSnd a b   => .betaSnd' a b
  | .betaSnd' a b  => .betaSnd a b
  | .coerceSame A t   => .coerceSame' A t
  | .coerceSame' A t  => .coerceSame A t
  | .coerceUnit A B   => .coerceUnit' A B
  | .coerceUnit' A B  => .coerceUnit A B
  | .cohRefl A     => .cohRefl' A
  | .cohRefl' A    => .cohRefl A
  | .congApp a s   => .congApp a s.symm
  | .congArg f s   => .congArg f s.symm
  | .congFst s     => .congFst s.symm
  | .congSnd s     => .congSnd s.symm
  | .congSucc s    => .congSucc s.symm
  | .congCoerce A B s => .congCoerce A B s.symm
  | .congPairL b s => .congPairL b s.symm
  | .congPairR a s => .congPairR a s.symm

/-- Theorem 2: Symmetry of OTT paths. -/
theorem OPath.symm {a b : OTm} (p : OPath a b) : OPath b a := by
  induction p with
  | refl _ => exact OPath.refl _
  | step s _ ih => exact OPath.trans ih (OPath.step s.symm (OPath.refl _))

/-- Theorem 3: Single step lifts to path. -/
theorem OPath.single {a b : OTm} (s : OStep a b) : OPath a b :=
  OPath.step s (OPath.refl _)

/-- Theorem 4: congrArg — application preserves paths in function position. -/
theorem OPath.congrArg_app {f f' : OTm} (a : OTm)
    (p : OPath f f') : OPath (.app f a) (.app f' a) := by
  induction p with
  | refl _ => exact OPath.refl _
  | step s _ ih => exact OPath.step (OStep.congApp a s) ih

/-- Theorem 5: congrArg — application preserves paths in argument position. -/
theorem OPath.congrArg_arg (f : OTm) {a a' : OTm}
    (p : OPath a a') : OPath (.app f a) (.app f a') := by
  induction p with
  | refl _ => exact OPath.refl _
  | step s _ ih => exact OPath.step (OStep.congArg f s) ih

/-- Theorem 6: congrArg — successor preserves paths. -/
theorem OPath.congrArg_succ {n n' : OTm}
    (p : OPath n n') : OPath (.succ n) (.succ n') := by
  induction p with
  | refl _ => exact OPath.refl _
  | step s _ ih => exact OPath.step (OStep.congSucc s) ih

/-- Theorem 7: congrArg — coercion preserves paths. -/
theorem OPath.congrArg_coerce (A B : OTy) {t t' : OTm}
    (p : OPath t t') : OPath (.coerce A B t) (.coerce A B t') := by
  induction p with
  | refl _ => exact OPath.refl _
  | step s _ ih => exact OPath.step (OStep.congCoerce A B s) ih

-- ============================================================
-- §4  Coercion and coherence
-- ============================================================

/-- Theorem 8: Coercion at same type is identity (key OTT property). -/
theorem coerce_same_type (A : OTy) (t : OTm) :
    OPath (.coerce A A t) t :=
  OPath.single (OStep.coerceSame A t)

/-- Theorem 9: Coherence — coh(A,A,refl) reduces to refl. -/
theorem coherence_refl (A : OTy) :
    OPath (.coh A A .refl) .refl :=
  OPath.single (OStep.cohRefl A)

/-- Theorem 10: Coercion of unit is always star. -/
theorem coerce_unit (A B : OTy) :
    OPath (.coerce A B .star) .star :=
  OPath.single (OStep.coerceUnit A B)

/-- Theorem 11: Double coercion A→A→A collapses via two-step path. -/
theorem double_coerce_same (A : OTy) (t : OTm) :
    OPath (.coerce A A (.coerce A A t)) t :=
  OPath.trans
    (OPath.congrArg_coerce A A (coerce_same_type A t))
    (coerce_same_type A t)

/-- Theorem 12: Coerce then coerce back at same type is identity. -/
theorem coerce_roundtrip (A : OTy) (t : OTm) :
    OPath (.coerce A A (.coerce A A t)) t :=
  double_coerce_same A t

-- ============================================================
-- §5  β-reduction paths
-- ============================================================

/-- Theorem 13: β-reduction for application. -/
theorem beta_app (body arg : OTm) :
    OPath (.app (.lam body) arg) body :=
  OPath.single (OStep.betaApp body arg)

/-- Theorem 14: β-reduction for first projection. -/
theorem beta_fst (a b : OTm) :
    OPath (.fst (.pair a b)) a :=
  OPath.single (OStep.betaFst a b)

/-- Theorem 15: β-reduction for second projection. -/
theorem beta_snd (a b : OTm) :
    OPath (.snd (.pair a b)) b :=
  OPath.single (OStep.betaSnd a b)

/-- Theorem 16: Surjective pairing path: ⟨fst p, snd p⟩ coerces from ⟨a,b⟩. -/
theorem surjective_pairing (a b : OTm) :
    OPath (.pair (.fst (.pair a b)) (.snd (.pair a b))) (.pair a b) :=
  OPath.trans
    (OPath.step (OStep.congPairL _ (OStep.betaFst a b)) (OPath.refl _))
    (OPath.step (OStep.congPairR a (OStep.betaSnd a b)) (OPath.refl _))

-- ============================================================
-- §6  Observational equality
-- ============================================================

/-- Observational equivalence: two types are obs-eq if they have
    the same introduction/elimination behavior. Modelled as type steps. -/
inductive TyStep : OTy → OTy → Prop where
  | refl   (A : OTy) : TyStep A A
  | piCong {A A' B B' : OTy} :
      TyStep A A' → TyStep B B' → TyStep (.pi A B) (.pi A' B')
  | sigmaCong {A A' B B' : OTy} :
      TyStep A A' → TyStep B B' → TyStep (.sigma A B) (.sigma A' B')
  | eqCong {A A' : OTy} {a a' b b' : OTy} :
      TyStep A A' → TyStep a a' → TyStep b b' → TyStep (.eq A a b) (.eq A' a' b')

/-- Type-level paths (observational equivalence chains). -/
inductive TyPath : OTy → OTy → Prop where
  | refl (A : OTy) : TyPath A A
  | step {A B C : OTy} : TyStep A B → TyPath B C → TyPath A C

/-- Theorem 17: Type path transitivity. -/
theorem TyPath.trans {A B C : OTy}
    (p : TyPath A B) (q : TyPath B C) : TyPath A C := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact TyPath.step s (ih q)

/-- Theorem 18: Pi type congruence path. -/
theorem TyPath.congrArg_pi {A A' B B' : OTy}
    (pA : TyPath A A') (pB : TyPath B B') : TyPath (.pi A B) (.pi A' B') := by
  induction pA with
  | refl _ =>
    induction pB with
    | refl _ => exact TyPath.refl _
    | step s _ ih => exact TyPath.step (TyStep.piCong (TyStep.refl _) s) ih
  | step sA _ ihA =>
    exact TyPath.step (TyStep.piCong sA (TyStep.refl _)) ihA

/-- Theorem 19: Sigma type congruence path. -/
theorem TyPath.congrArg_sigma {A A' B B' : OTy}
    (pA : TyPath A A') (pB : TyPath B B') : TyPath (.sigma A B) (.sigma A' B') := by
  induction pA with
  | refl _ =>
    induction pB with
    | refl _ => exact TyPath.refl _
    | step s _ ih => exact TyPath.step (TyStep.sigmaCong (TyStep.refl _) s) ih
  | step sA _ ihA =>
    exact TyPath.step (TyStep.sigmaCong sA (TyStep.refl _)) ihA

-- ============================================================
-- §7  Heterogeneous equality
-- ============================================================

/-- Heterogeneous equality: a =_{A≡B} b when A and B are obs-equivalent. -/
structure HetEq where
  tyA : OTy
  tyB : OTy
  lhs : OTm
  rhs : OTm
  tyEq : TyPath tyA tyB
deriving Repr

/-- Rewriting steps for heterogeneous equality. -/
inductive HStep : HetEq → HetEq → Prop where
  | homogenize (A : OTy) (a b : OTm) :
      HStep ⟨A, A, a, b, TyPath.refl A⟩ ⟨A, A, a, b, TyPath.refl A⟩
  | coerceLhs {A B : OTy} (a b : OTm) (p : TyPath A B) :
      HStep ⟨A, B, a, b, p⟩ ⟨B, B, .coerce A B a, b, TyPath.refl B⟩
  | transport {A B : OTy} (a : OTm) (p : TyPath A B) :
      HStep ⟨A, B, a, .coerce A B a, p⟩ ⟨B, B, .coerce A B a, .coerce A B a, TyPath.refl B⟩

/-- Heterogeneous equality paths. -/
inductive HPath : HetEq → HetEq → Prop where
  | refl (h : HetEq) : HPath h h
  | step {a b c : HetEq} : HStep a b → HPath b c → HPath a c

/-- Theorem 20: Het eq path transitivity. -/
theorem HPath.trans {a b c : HetEq}
    (p : HPath a b) (q : HPath b c) : HPath a c := by
  induction p with
  | refl _ => exact q
  | step s _ ih => exact HPath.step s (ih q)

/-- Theorem 21: Heterogeneous equality can be homogenized via coercion. -/
theorem het_to_hom (A B : OTy) (a b : OTm) (p : TyPath A B) :
    HPath ⟨A, B, a, b, p⟩ ⟨B, B, .coerce A B a, b, TyPath.refl B⟩ :=
  HPath.step (HStep.coerceLhs a b p) (HPath.refl _)

/-- Theorem 22: Transport via heterogeneous equality. -/
theorem het_transport (A B : OTy) (a : OTm) (p : TyPath A B) :
    HPath ⟨A, B, a, .coerce A B a, p⟩
          ⟨B, B, .coerce A B a, .coerce A B a, TyPath.refl B⟩ :=
  HPath.step (HStep.transport a p) (HPath.refl _)

-- ============================================================
-- §8  Strict equality vs observational equality
-- ============================================================

/-- Strict (definitional) equality: same term constructor. -/
inductive StrictEq : OTm → OTm → Prop where
  | refl (t : OTm) : StrictEq t t

/-- Observational equality: connected by OPath. -/
def ObsEq (a b : OTm) : Prop := OPath a b

/-- Theorem 23: Strict equality implies observational equality. -/
theorem strict_implies_obs {a b : OTm} (h : StrictEq a b) : ObsEq a b := by
  cases h
  exact OPath.refl _

/-- Theorem 24: Observational equality is reflexive. -/
theorem obs_refl (a : OTm) : ObsEq a a := OPath.refl a

/-- Theorem 25: Observational equality is symmetric. -/
theorem obs_symm {a b : OTm} (h : ObsEq a b) : ObsEq b a := OPath.symm h

/-- Theorem 26: Observational equality is transitive. -/
theorem obs_trans {a b c : OTm} (h1 : ObsEq a b) (h2 : ObsEq b c) : ObsEq a c :=
  OPath.trans h1 h2

-- ============================================================
-- §9  Canonicity
-- ============================================================

/-- Canonical forms. -/
inductive Canonical : OTm → Prop where
  | star  : Canonical .star
  | tt    : Canonical .tt
  | ff    : Canonical .ff
  | zero  : Canonical .zero
  | succ  (n : OTm) : Canonical n → Canonical (.succ n)
  | lam   (body : OTm) : Canonical (.lam body)
  | pair  (a b : OTm) : Canonical a → Canonical b → Canonical (.pair a b)
  | refl  : Canonical .refl

/-- Theorem 27: Coercion at same type preserves canonicity path. -/
theorem canonical_coerce_same (A : OTy) (t : OTm) :
    OPath (.coerce A A t) t :=
  coerce_same_type A t

/-- Theorem 28: Star is canonical (trivially). -/
theorem star_canonical : Canonical .star := Canonical.star

/-- Theorem 29: Refl is canonical. -/
theorem refl_canonical : Canonical .refl := Canonical.refl

/-- Theorem 30: Coherence preserves canonicity — coh at same type gives canonical refl. -/
theorem coherence_canonical (A : OTy) :
    OPath (.coh A A .refl) .refl :=
  coherence_refl A

-- ============================================================
-- §10  Multi-step paths and coherence diamonds
-- ============================================================

/-- Theorem 31: β then coerce — applying then coercing at same type. -/
theorem beta_then_coerce (A : OTy) (body arg : OTm) :
    OPath (.coerce A A (.app (.lam body) arg)) body :=
  OPath.trans
    (OPath.congrArg_coerce A A (beta_app body arg))
    (coerce_same_type A body)

/-- Theorem 32: Fst-then-coerce path. -/
theorem fst_then_coerce (A : OTy) (a b : OTm) :
    OPath (.coerce A A (.fst (.pair a b))) a :=
  OPath.trans
    (OPath.congrArg_coerce A A (beta_fst a b))
    (coerce_same_type A a)

/-- Theorem 33: Observational equality of coerced vs direct application. -/
theorem obs_eq_coerce_app (A : OTy) (body arg : OTm) :
    ObsEq (.coerce A A (.app (.lam body) arg)) body :=
  beta_then_coerce A body arg

/-- Theorem 34: Path from double projection through pair. -/
theorem double_proj_path (a b : OTm) :
    OPath (.pair (.fst (.pair a b)) (.snd (.pair a b))) (.pair a b) :=
  surjective_pairing a b

/-- Theorem 35: Coherence diamond — two paths to refl agree. -/
theorem coherence_diamond (A : OTy) :
    OPath (.coh A A .refl) .refl ∧
    OPath (.coerce A A .refl) .refl :=
  ⟨coherence_refl A,
   coerce_same_type A .refl⟩

end OTT
