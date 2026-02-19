import Metatheory.SystemF.StrongNormalization
import Metatheory.SystemF.SubjectReduction

/-!
# System F Relational Parametricity

This module packages a binary (Reynolds-style) parametricity layer on top of the
existing System F reducibility infrastructure.

The core idea is:
- type variables are interpreted by binary relations (`RelInterp`)
- types are interpreted by paired reducibility (`RelTy`)
- the abstraction theorem follows from the existing fundamental lemma on each side

It also includes three concrete free-theorem style examples for the canonical
System F inhabitants in this development.
-/

namespace Metatheory.SystemF

open Ty
open Term

/-! ## Binary relation environments -/

/-- Binary relation on terms. -/
abbrev TermRel := Term → Term → Prop

/-- Closed (well-typed) terms in the empty context. -/
def ClosedTerm (M : Term) : Prop := ∃ τ, HasType 0 [] M τ

/-- A relational interpretation maps type variables to binary relations. -/
abbrev RelInterp := Nat → TermRel

namespace RelInterp

/-- Extend a relational interpretation with a new innermost relation. -/
def extend (ρ : RelInterp) (R : TermRel) : RelInterp
  | 0 => R
  | n + 1 => ρ n

/-- Equality relation at every type-variable index. -/
def eq : RelInterp := fun _ M N => M = N

/-- A relation environment is closed if every related pair is closed. -/
def Closed (ρ : RelInterp) : Prop :=
  ∀ n M N, ρ n M N → ClosedTerm M ∧ ClosedTerm N

/-- Build a relation environment from two unary candidate environments. -/
def ofTyEnvs (k : Nat) (ρ₁ ρ₂ : TyEnv) : RelInterp :=
  fun n M N => (ρ₁ n).pred k M ∧ (ρ₂ n).pred k N

end RelInterp

/-! ## Relational interpretation of types -/

/-- Binary relational interpretation of a type at world `k`. -/
def RelTy (k : Nat) (ρ₁ ρ₂ : TyEnv) (τ : Ty) : TermRel :=
  fun M N => Red k ρ₁ τ M ∧ Red k ρ₂ τ N

theorem relTy_tvar_iff {k : Nat} {ρ₁ ρ₂ : TyEnv} {n : Nat} {M N : Term} :
    RelTy k ρ₁ ρ₂ (tvar n) M N ↔ RelInterp.ofTyEnvs k ρ₁ ρ₂ n M N :=
  Iff.rfl

/-! ## Abstraction theorem (fundamental theorem of parametricity) -/

/-- Abstraction theorem: related substitutions send a well-typed term to related outputs. -/
theorem abstraction {k : Nat} {Γ : Context} {M : Term} {τ : Ty}
    (hM : HasType k Γ M τ) {k' : Nat} (hk : k ≤ k')
    {ρ₁ ρ₂ : TyEnv} {σ₁ σ₂ : Subst}
    (hσ₁ : RedSubst k' ρ₁ Γ σ₁)
    (hσ₂ : RedSubst k' ρ₂ Γ σ₂) :
    RelTy k' ρ₁ ρ₂ τ (applySubst σ₁ M) (applySubst σ₂ M) := by
  exact ⟨fundamental_lemma hM hk hσ₁, fundamental_lemma hM hk hσ₂⟩

/-- Identity extension lemma (diagonal instance of abstraction). -/
theorem identity_extension {k : Nat} {Γ : Context} {M : Term} {τ : Ty}
    (hM : HasType k Γ M τ) {k' : Nat} (hk : k ≤ k')
    {ρ : TyEnv} {σ : Subst}
    (hσ : RedSubst k' ρ Γ σ) :
    RelTy k' ρ ρ τ (applySubst σ M) (applySubst σ M) := by
  exact abstraction hM hk hσ hσ

/-- Closed-term specialization at the default environment and identity substitution. -/
theorem abstraction_closed {M : Term} {τ : Ty} (hM : HasType 0 [] M τ) :
    RelTy 0 defaultTyEnv defaultTyEnv τ M M := by
  have hdiag := identity_extension hM (k' := 0) (Nat.le_refl 0) (ρ := defaultTyEnv) idSubst_red
  simpa [applySubst_id] using hdiag

/-! ## A polymorphic K combinator -/

/-- The polymorphic K combinator: `Λα. Λβ. λx:α. λy:β. x`. -/
def polyK : Term :=
  tlam (tlam (lam (tvar 1) (lam (tvar 0) (var 1))))

/-- Type of the polymorphic K combinator. -/
def kTy : Ty := all (all (tvar 1 ⇒ tvar 0 ⇒ tvar 1))

theorem polyK_hasType : HasType 0 [] polyK kTy := by
  unfold polyK kTy
  apply HasType.tlam
  simp only [shiftContext, List.map_nil]
  apply HasType.tlam
  simp only [shiftContext, List.map_nil]
  apply HasType.lam
  · simp only [Ty.WF]
    omega
  · apply HasType.lam
    · simp only [Ty.WF]
      omega
    · apply HasType.var
      native_decide

/-! ## Free theorem examples -/

/-- Free theorem example (∀a. a -> a): the canonical inhabitant acts as identity. -/
theorem free_theorem_forall_a_a_to_a_only_identity (τ : Ty) (x : Term) :
    app (tapp polyId τ) x ⟶* x := by
  have h1 : app (tapp polyId τ) x ⟶ app (lam τ (var 0)) x := by
    unfold polyId
    simpa [substTypeInTerm0, substTypeInTerm, substTy] using
      Step.appL (Step.tbeta (lam (tvar 0) (var 0)) τ)
  have h2 : app (lam τ (var 0)) x ⟶ x := by
    simpa [substTerm0, substTerm] using Step.beta τ (var 0) x
  exact MultiStep.step h1 (MultiStep.step h2 (MultiStep.refl x))

/-- Parametricity witness for the canonical inhabitant of `forall a, a -> a`. -/
theorem free_theorem_forall_a_a_to_a_parametric :
    RelTy 0 defaultTyEnv defaultTyEnv idTy polyId polyId :=
  abstraction_closed (M := polyId) (τ := idTy) (by
    simpa using (show HasType 0 [] polyId idTy from by
      unfold polyId idTy
      apply HasType.tlam
      simp only [shiftContext, List.map_nil]
      apply HasType.lam
      · simp only [Ty.WF]
        omega
      · apply HasType.var
        native_decide))

/-- Free theorem example (forall a, a -> a -> a): `cTrue` returns the first argument. -/
theorem free_theorem_forall_a_a_to_a_to_a_true (τ : Ty) (x y : Term) :
    app (app (tapp cTrue τ) x) y ⟶* x := by
  have h1 : app (app (tapp cTrue τ) x) y ⟶ app (app (lam τ (lam τ (var 1))) x) y := by
    unfold cTrue
    simpa [substTypeInTerm0, substTypeInTerm, substTy] using
      Step.appL (Step.appL (Step.tbeta (lam (tvar 0) (lam (tvar 0) (var 1))) τ))
  have h2 : app (app (lam τ (lam τ (var 1))) x) y ⟶ app (lam τ (shiftTermUp 1 0 x)) y := by
    simpa [substTerm0, substTerm] using
      Step.appL (Step.beta τ (lam τ (var 1)) x)
  have h3 : app (lam τ (shiftTermUp 1 0 x)) y ⟶ x := by
    simpa [substTerm0, substTerm_shiftTermUp_cancel] using
      Step.beta τ (shiftTermUp 1 0 x) y
  exact MultiStep.step h1 (MultiStep.step h2 (MultiStep.step h3 (MultiStep.refl x)))

/-- Free theorem example (forall a, a -> a -> a): `cFalse` returns the second argument. -/
theorem free_theorem_forall_a_a_to_a_to_a_false (τ : Ty) (x y : Term) :
    app (app (tapp cFalse τ) x) y ⟶* y := by
  have h1 : app (app (tapp cFalse τ) x) y ⟶ app (app (lam τ (lam τ (var 0))) x) y := by
    unfold cFalse
    simpa [substTypeInTerm0, substTypeInTerm, substTy] using
      Step.appL (Step.appL (Step.tbeta (lam (tvar 0) (lam (tvar 0) (var 0))) τ))
  have h2 : app (app (lam τ (lam τ (var 0))) x) y ⟶ app (lam τ (var 0)) y := by
    simpa [substTerm0, substTerm] using
      Step.appL (Step.beta τ (lam τ (var 0)) x)
  have h3 : app (lam τ (var 0)) y ⟶ y := by
    simpa [substTerm0, substTerm] using Step.beta τ (var 0) y
  exact MultiStep.step h1 (MultiStep.step h2 (MultiStep.step h3 (MultiStep.refl y)))

/-- The two canonical inhabitants witness the boolean free theorem behavior. -/
theorem free_theorem_forall_a_a_to_a_to_a_two_inhabitants (τ : Ty) (x y : Term) :
    (app (app (tapp cTrue τ) x) y ⟶* x) ∧
    (app (app (tapp cFalse τ) x) y ⟶* y) :=
  ⟨free_theorem_forall_a_a_to_a_to_a_true τ x y,
    free_theorem_forall_a_a_to_a_to_a_false τ x y⟩

/-- Free theorem example (K-combinator): polymorphic K always returns its first argument. -/
theorem free_theorem_k_combinator_uniqueness (α β : Ty) (x y : Term) :
    app (app (tapp (tapp polyK α) β) x) y ⟶* x := by
  have h1 : app (app (tapp (tapp polyK α) β) x) y ⟶
      app (app (tapp (tlam (lam (shiftTyUp 1 0 α) (lam (tvar 0) (var 1)))) β) x) y := by
    unfold polyK
    simpa [substTypeInTerm0, substTypeInTerm, substTy] using
      Step.appL (Step.appL (Step.tappL (Step.tbeta (tlam (lam (tvar 1) (lam (tvar 0) (var 1)))) α)))
  have h2 : app (app (tapp (tlam (lam (shiftTyUp 1 0 α) (lam (tvar 0) (var 1)))) β) x) y ⟶
      app (app (lam α (lam β (var 1))) x) y := by
    simpa [substTypeInTerm0, substTypeInTerm, substTy, substTy0_shiftTyUp_cancel] using
      Step.appL (Step.appL (Step.tbeta (lam (shiftTyUp 1 0 α) (lam (tvar 0) (var 1))) β))
  have h3 : app (app (lam α (lam β (var 1))) x) y ⟶ app (lam β (shiftTermUp 1 0 x)) y := by
    simpa [substTerm0, substTerm] using
      Step.appL (Step.beta α (lam β (var 1)) x)
  have h4 : app (lam β (shiftTermUp 1 0 x)) y ⟶ x := by
    simpa [substTerm0, substTerm_shiftTermUp_cancel] using
      Step.beta β (shiftTermUp 1 0 x) y
  exact MultiStep.step h1 (MultiStep.step h2 (MultiStep.step h3 (MultiStep.step h4 (MultiStep.refl x))))

/-- Parametricity witness for the polymorphic K combinator. -/
theorem free_theorem_k_parametric :
    RelTy 0 defaultTyEnv defaultTyEnv kTy polyK polyK :=
  abstraction_closed polyK_hasType

end Metatheory.SystemF
