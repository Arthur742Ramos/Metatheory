import Metatheory.SystemF.Decidability
import Metatheory.SystemF.StrongNormalization

namespace Metatheory.SystemF

open Ty Term

abbrev cTrue : Term := Term.cTrue
abbrev cFalse : Term := Term.cFalse
abbrev cZero : Term := Term.cZero
def cSucc : Term :=
  lam natTy (tlam (lam (tvar 0 ⇒ tvar 0) (lam (tvar 0)
    (app (var 1) (app (app (tapp (var 2) (tvar 0)) (var 1)) (var 0))))))

/-- Church conditional. -/
def cIf : Term :=
  lam boolTy (tlam (lam (tvar 0) (lam (tvar 0)
    (app (app (tapp (var 2) (tvar 0)) (var 1)) (var 0)))))

/-- Church negation. -/
def cNot : Term :=
  lam boolTy (app (app (tapp (app cIf (var 0)) boolTy) cFalse) cTrue)

/-- Church conjunction. -/
def cAnd : Term :=
  lam boolTy (lam boolTy (app (app (tapp (app cIf (var 1)) boolTy) (var 0)) cFalse))

/-- Church disjunction. -/
def cOr : Term :=
  lam boolTy (lam boolTy (app (app (tapp (app cIf (var 1)) boolTy) cTrue) (var 0)))

/-- Instantiate a Church boolean and apply both branches. -/
def cIfApp (A : Ty) (b t f : Term) : Term :=
  app (app (tapp (app cIf b) A) t) f

/-- Church numeral constructor. -/
def cNum : Nat → Term
  | 0 => cZero
  | n + 1 => app cSucc (cNum n)

/-- Instantiate a Church numeral with an algebra `(A, s, z)`. -/
def cNatApp (n : Term) (A : Ty) (s z : Term) : Term :=
  app (app (tapp n A) s) z

/-- Church addition. -/
def cPlus : Term :=
  lam natTy (lam natTy (tlam (lam (tvar 0 ⇒ tvar 0) (lam (tvar 0)
    (app
      (app (tapp (var 3) (tvar 0)) (var 1))
      (app (app (tapp (var 2) (tvar 0)) (var 1)) (var 0)))))))

/-- Church multiplication. -/
def cMult : Term :=
  lam natTy (lam natTy (tlam (lam (tvar 0 ⇒ tvar 0) (lam (tvar 0)
    (app
      (app (tapp (var 3) (tvar 0)) (app (tapp (var 2) (tvar 0)) (var 1))
      )
      (var 0))))))

/-- Church-encoded pair type. -/
def pairTy (A B : Ty) : Ty :=
  all (((shiftTyUp 1 0 A) ⇒ (shiftTyUp 1 0 B) ⇒ tvar 0) ⇒ tvar 0)

/-- Church pair constructor. -/
def cPair (A B : Ty) : Term :=
  lam A (lam B
    (tlam (lam ((shiftTyUp 1 0 A) ⇒ (shiftTyUp 1 0 B) ⇒ tvar 0)
      (app (app (var 0) (var 2)) (var 1)))))

/-- Church first projection. -/
def cFst (A B : Ty) : Term :=
  lam (pairTy A B)
    (app (tapp (var 0) A) (lam A (lam B (var 1))))

/-- Church second projection. -/
def cSnd (A B : Ty) : Term :=
  lam (pairTy A B)
    (app (tapp (var 0) B) (lam A (lam B (var 0))))

def cPairApp (A B : Ty) (a b : Term) : Term :=
  app (app (cPair A B) a) b

theorem cIf_true_reduces (A : Ty) (t f : Term) :
    cIfApp A cTrue t f ⟶* t := by
  unfold cIfApp
  refine MultiStep.step (Step.appL (Step.appL (Step.tappL (Step.beta _ _ _)))) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  simpa [cIf, cTrue, Term.substTerm0, Term.substTerm, Term.substTypeInTerm0, Term.substTypeInTerm,
    Term.shiftTypeInTerm, Term.shiftTermUp, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, substTerm_shiftTermUp_cancel]
    using (MultiStep.refl t)

theorem cIf_false_reduces (A : Ty) (t f : Term) :
    cIfApp A cFalse t f ⟶* f := by
  unfold cIfApp
  refine MultiStep.step (Step.appL (Step.appL (Step.tappL (Step.beta _ _ _)))) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  simpa [cIf, cFalse, Term.substTerm0, Term.substTerm, Term.substTypeInTerm0, Term.substTypeInTerm,
    Term.shiftTypeInTerm, Term.shiftTermUp, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, substTerm_shiftTermUp_cancel]
    using (MultiStep.refl f)

theorem cNot_true_reduces :
    app cNot cTrue ⟶* cFalse := by
  refine MultiStep.trans (MultiStep.single (Step.beta _ _ _)) ?_
  simpa [cNot, cIfApp] using cIf_true_reduces boolTy cFalse cTrue

theorem cNot_false_reduces :
    app cNot cFalse ⟶* cTrue := by
  refine MultiStep.trans (MultiStep.single (Step.beta _ _ _)) ?_
  simpa [cNot, cIfApp] using cIf_false_reduces boolTy cFalse cTrue

theorem cAnd_true_reduces (b : Term) :
    app (app cAnd cTrue) b ⟶* b := by
  refine MultiStep.trans (MultiStep.single (Step.appL (Step.beta _ _ _))) ?_
  refine MultiStep.trans (MultiStep.single (Step.beta _ _ _)) ?_
  simpa [cAnd, cIfApp] using cIf_true_reduces boolTy b cFalse

theorem cAnd_false_reduces (b : Term) :
    app (app cAnd cFalse) b ⟶* cFalse := by
  refine MultiStep.trans (MultiStep.single (Step.appL (Step.beta _ _ _))) ?_
  refine MultiStep.trans (MultiStep.single (Step.beta _ _ _)) ?_
  simpa [cAnd, cIfApp] using cIf_false_reduces boolTy b cFalse

theorem cOr_true_reduces (b : Term) :
    app (app cOr cTrue) b ⟶* cTrue := by
  refine MultiStep.trans (MultiStep.single (Step.appL (Step.beta _ _ _))) ?_
  refine MultiStep.trans (MultiStep.single (Step.beta _ _ _)) ?_
  simpa [cOr, cIfApp] using cIf_true_reduces boolTy cTrue b

theorem cOr_false_reduces (b : Term) :
    app (app cOr cFalse) b ⟶* b := by
  refine MultiStep.trans (MultiStep.single (Step.appL (Step.beta _ _ _))) ?_
  refine MultiStep.trans (MultiStep.single (Step.beta _ _ _)) ?_
  simpa [cOr, cIfApp] using cIf_false_reduces boolTy cTrue b

theorem cNum_zero_reduces (A : Ty) (s z : Term) :
    cNatApp (cNum 0) A s z ⟶* z := by
  unfold cNum cNatApp cZero
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  simpa [Term.substTerm0, Term.substTerm, Term.substTypeInTerm0, Term.substTypeInTerm,
    Term.shiftTermUp, Term.shiftTypeInTerm, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, substTerm_shiftTermUp_cancel]
    using (MultiStep.refl z)

theorem cSucc_unfold (n : Term) :
    app cSucc n ⟶* substTerm0 n
      (tlam (lam (tvar 0 ⇒ tvar 0) (lam (tvar 0)
        (app (var 1) (app (app (tapp (var 2) (tvar 0)) (var 1)) (var 0)))))) :=
  MultiStep.single (Step.beta _ _ _)

theorem cPlus_step (m n : Term) :
    app (app cPlus m) n ⟶
      app
        (substTerm0 m
          (lam natTy (tlam (lam (tvar 0 ⇒ tvar 0) (lam (tvar 0)
            (app
              (app (tapp (var 3) (tvar 0)) (var 1))
              (app (app (tapp (var 2) (tvar 0)) (var 1)) (var 0))))))))
        n :=
  Step.appL (Step.beta _ _ _)

theorem cMult_step (m n : Term) :
    app (app cMult m) n ⟶
      app
        (substTerm0 m
          (lam natTy (tlam (lam (tvar 0 ⇒ tvar 0) (lam (tvar 0)
            (app
              (app (tapp (var 3) (tvar 0)) (app (tapp (var 2) (tvar 0)) (var 1)))
              (var 0))))))
        )
        n :=
  Step.appL (Step.beta _ _ _)

theorem cPair_step (A B : Ty) (a b : Term) :
    cPairApp A B a b ⟶
      app
        (substTerm0 a
          (lam B
            (tlam (lam ((shiftTyUp 1 0 A) ⇒ (shiftTyUp 1 0 B) ⇒ tvar 0)
              (app (app (var 0) (var 2)) (var 1)))))
        )
        b := by
  unfold cPairApp
  exact Step.appL (Step.beta _ _ _)

theorem cFst_unfold (A B : Ty) (p : Term) :
    app (cFst A B) p ⟶ app (tapp p A) (lam A (lam B (var 1))) :=
  Step.beta _ _ _

theorem cSnd_unfold (A B : Ty) (p : Term) :
    app (cSnd A B) p ⟶ app (tapp p B) (lam A (lam B (var 0))) :=
  Step.beta _ _ _

theorem cIf_hasType :
    ⊢ cIf : boolTy ⇒ boolTy := by
  exact typeCheck_sound (M := cIf) (τ := boolTy ⇒ boolTy) (by native_decide)

theorem cNot_hasType :
    ⊢ cNot : boolTy ⇒ boolTy := by
  exact typeCheck_sound (M := cNot) (τ := boolTy ⇒ boolTy) (by native_decide)

theorem cAnd_hasType :
    ⊢ cAnd : boolTy ⇒ boolTy ⇒ boolTy := by
  exact typeCheck_sound (M := cAnd) (τ := boolTy ⇒ boolTy ⇒ boolTy) (by native_decide)

theorem cOr_hasType :
    ⊢ cOr : boolTy ⇒ boolTy ⇒ boolTy := by
  exact typeCheck_sound (M := cOr) (τ := boolTy ⇒ boolTy ⇒ boolTy) (by native_decide)

theorem cZero_hasType :
    ⊢ cZero : natTy := by
  exact typeCheck_sound (M := cZero) (τ := natTy) (by native_decide)

theorem cSucc_hasType :
    ⊢ cSucc : natTy ⇒ natTy := by
  exact typeCheck_sound (M := cSucc) (τ := natTy ⇒ natTy) (by native_decide)

theorem cNum_hasType (n : Nat) :
    ⊢ cNum n : natTy := by
  induction n with
  | zero =>
    simpa [cNum] using cZero_hasType
  | succ n ih =>
    simpa [cNum] using HasType.app cSucc_hasType ih

theorem cPlus_hasType :
    ⊢ cPlus : natTy ⇒ natTy ⇒ natTy := by
  exact typeCheck_sound (M := cPlus) (τ := natTy ⇒ natTy ⇒ natTy) (by native_decide)

theorem cMult_hasType :
    ⊢ cMult : natTy ⇒ natTy ⇒ natTy := by
  exact typeCheck_sound (M := cMult) (τ := natTy ⇒ natTy ⇒ natTy) (by native_decide)

theorem pairTy_wf {A B : Ty} (hA : Ty.WF 0 A) (hB : Ty.WF 0 B) :
    Ty.WF 0 (pairTy A B) := by
  unfold pairTy Ty.WF
  constructor
  · constructor
    · exact Ty.WF_shiftTyUp 1 0 hA
    · constructor
      · exact Ty.WF_shiftTyUp 1 0 hB
      · exact Nat.zero_lt_one
  · exact Nat.zero_lt_one

theorem cPair_hasType {A B : Ty} (hA : Ty.WF 0 A) (hB : Ty.WF 0 B) :
    ⊢ cPair A B : A ⇒ B ⇒ pairTy A B := by
  unfold cPair
  apply HasType.lam hA
  apply HasType.lam hB
  apply HasType.tlam
  simp only [shiftContext, List.map]
  have hFunWF : Ty.WF 1 ((shiftTyUp 1 0 A) ⇒ (shiftTyUp 1 0 B) ⇒ tvar 0) := by
    unfold Ty.WF
    exact ⟨Ty.WF_shiftTyUp 1 0 hA, ⟨Ty.WF_shiftTyUp 1 0 hB, Nat.zero_lt_one⟩⟩
  apply HasType.lam hFunWF
  refine HasType.app (τ₁ := shiftTyUp 1 0 B) ?_ ?_
  · refine HasType.app (τ₁ := shiftTyUp 1 0 A) ?_ ?_
    · apply HasType.var
      simp [lookup]
    · apply HasType.var
      simp [lookup]
  · apply HasType.var
    simp [lookup]

theorem cFst_hasType {A B : Ty} (hA : Ty.WF 0 A) (hB : Ty.WF 0 B) :
    ⊢ cFst A B : pairTy A B ⇒ A := by
  unfold cFst
  apply HasType.lam (pairTy_wf hA hB)
  refine HasType.app (τ₁ := (A ⇒ B ⇒ A)) ?_ ?_
  · have hVar : (0 ; [pairTy A B] ⊢ var 0 : pairTy A B) := by
      apply HasType.var
      simp [lookup]
    have hTapp : 0 ; [pairTy A B] ⊢ tapp (var 0) A : (A ⇒ B ⇒ A) ⇒ A := by
      have hAA : substTy 0 A (shiftTyUp 1 0 A) = A :=
        Ty.substTy_shiftTyUp_cancel (k := 0) (σ := A) A
      have hAB : substTy 0 A (shiftTyUp 1 0 B) = B :=
        Ty.substTy_shiftTyUp_cancel (k := 0) (σ := A) B
      simpa [pairTy, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, hAA, hAB] using HasType.tapp hVar hA
    exact hTapp
  · apply HasType.lam hA
    apply HasType.lam hB
    apply HasType.var
    simp [lookup]

theorem cSnd_hasType {A B : Ty} (hA : Ty.WF 0 A) (hB : Ty.WF 0 B) :
    ⊢ cSnd A B : pairTy A B ⇒ B := by
  unfold cSnd
  apply HasType.lam (pairTy_wf hA hB)
  refine HasType.app (τ₁ := (A ⇒ B ⇒ B)) ?_ ?_
  · have hVar : (0 ; [pairTy A B] ⊢ var 0 : pairTy A B) := by
      apply HasType.var
      simp [lookup]
    have hTapp : 0 ; [pairTy A B] ⊢ tapp (var 0) B : (A ⇒ B ⇒ B) ⇒ B := by
      have hBA : substTy 0 B (shiftTyUp 1 0 A) = A :=
        Ty.substTy_shiftTyUp_cancel (k := 0) (σ := B) A
      have hBB : substTy 0 B (shiftTyUp 1 0 B) = B :=
        Ty.substTy_shiftTyUp_cancel (k := 0) (σ := B) B
      simpa [pairTy, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, hBA, hBB] using HasType.tapp hVar hB
    exact hTapp
  · apply HasType.lam hA
    apply HasType.lam hB
    apply HasType.var
    simp [lookup]

end Metatheory.SystemF
