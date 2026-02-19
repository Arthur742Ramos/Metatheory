import Metatheory.SystemF.StrongNormalization
import Metatheory.SystemF.Typing

namespace Metatheory.SystemF

open Ty Term

abbrev cTrue : Term := Term.cTrue
abbrev cFalse : Term := Term.cFalse
abbrev cZero : Term := Term.cZero
abbrev cSucc : Term := Term.cSucc

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
      (app (tapp (var 3) (tvar 0))
        (app (app (tapp (var 2) (tvar 0)) (var 1)))
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

namespace MultiStep

theorem appCongr {M M' N N' : Term} (hM : M ⟶* M') (hN : N ⟶* N') :
    app M N ⟶* app M' N' :=
  trans (appL hM) (appR hN)

theorem appL_appL {M M' N P : Term} (h : M ⟶* M') :
    app (app M N) P ⟶* app (app M' N) P :=
  appL (appL h)

end MultiStep

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

theorem cSucc_reduces (A : Ty) (n s z : Term) :
    cNatApp (app cSucc n) A s z ⟶* app s (cNatApp n A s z) := by
  unfold cNatApp
  refine MultiStep.step (Step.appL (Step.appL (Step.tappL (Step.beta _ _ _)))) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  simpa [cSucc, Term.substTerm0, Term.substTerm, Term.substTypeInTerm0, Term.substTypeInTerm,
    Term.shiftTypeInTerm, Term.shiftTermUp, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, substTerm_shiftTermUp_cancel]
    using (MultiStep.refl (app s (app (app (tapp n A) s) z)))

theorem cNum_zero_reduces (A : Ty) (s z : Term) :
    cNatApp (cNum 0) A s z ⟶* z := by
  unfold cNum cNatApp cZero
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  simpa [Term.substTerm0, Term.substTerm, Term.substTypeInTerm0, Term.substTypeInTerm,
    Term.shiftTermUp, Term.shiftTypeInTerm, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, substTerm_shiftTermUp_cancel]
    using (MultiStep.refl z)

theorem cPlus_zero_left_reduces (A : Ty) (n s z : Term) :
    cNatApp (app (app cPlus cZero) n) A s z ⟶* cNatApp n A s z := by
  unfold cNatApp
  refine MultiStep.step (Step.appL (Step.appL (Step.tappL (Step.appL (Step.beta _ _ _))))) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tappL (Step.beta _ _ _)))) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  simpa [cPlus, cZero, Term.substTerm0, Term.substTerm, Term.substTypeInTerm0, Term.substTypeInTerm,
    Term.shiftTypeInTerm, Term.shiftTermUp, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, substTerm_shiftTermUp_cancel]
    using (MultiStep.refl (app (app (tapp n A) s) z))

theorem cMult_zero_left_reduces (A : Ty) (n s z : Term) :
    cNatApp (app (app cMult cZero) n) A s z ⟶* z := by
  unfold cNatApp
  refine MultiStep.step (Step.appL (Step.appL (Step.tappL (Step.appL (Step.beta _ _ _))))) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tappL (Step.beta _ _ _)))) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  simpa [cMult, cZero, Term.substTerm0, Term.substTerm, Term.substTypeInTerm0, Term.substTypeInTerm,
    Term.shiftTypeInTerm, Term.shiftTermUp, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, substTerm_shiftTermUp_cancel]
    using (MultiStep.refl z)

theorem cFst_pair_reduces (A B : Ty) (a b : Term) :
    app (cFst A B) (cPairApp A B a b) ⟶* a := by
  unfold cPairApp
  refine MultiStep.step (Step.beta _ _ _) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  simpa [cPair, cFst, Term.substTerm0, Term.substTerm, Term.substTypeInTerm0, Term.substTypeInTerm,
    Term.shiftTypeInTerm, Term.shiftTermUp, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, substTerm_shiftTermUp_cancel]
    using (MultiStep.refl a)

theorem cSnd_pair_reduces (A B : Ty) (a b : Term) :
    app (cSnd A B) (cPairApp A B a b) ⟶* b := by
  unfold cPairApp
  refine MultiStep.step (Step.beta _ _ _) ?_
  refine MultiStep.step (Step.appL (Step.appL (Step.tbeta _ _))) ?_
  refine MultiStep.step (Step.appL (Step.beta _ _ _)) ?_
  refine MultiStep.step (Step.beta _ _ _) ?_
  simpa [cPair, cSnd, Term.substTerm0, Term.substTerm, Term.substTypeInTerm0, Term.substTypeInTerm,
    Term.shiftTypeInTerm, Term.shiftTermUp, Ty.substTy0, Ty.substTy, Ty.shiftTyUp, substTerm_shiftTermUp_cancel]
    using (MultiStep.refl b)

theorem cIf_hasType :
    ⊢ cIf : boolTy ⇒ boolTy := by
  unfold cIf boolTy
  apply HasType.lam
  · unfold Ty.WF
    exact Nat.zero_lt_one
  · apply HasType.tlam
    simp only [shiftContext, List.map_cons, List.map_nil]
    apply HasType.lam
    · unfold Ty.WF
      exact Nat.zero_lt_one
    · apply HasType.lam
      · unfold Ty.WF
        exact Nat.zero_lt_one
      · apply HasType.app
        · apply HasType.app
          · apply HasType.tapp
            · apply HasType.var
              native_decide
            · unfold Ty.WF
              exact Nat.zero_lt_one
          · apply HasType.var
            native_decide
        · apply HasType.var
          native_decide

theorem cNot_hasType :
    ⊢ cNot : boolTy ⇒ boolTy := by
  unfold cNot
  apply HasType.lam
  · exact boolTy_closed
  · apply HasType.app
    · apply HasType.app
      · apply HasType.tapp
        · apply HasType.app
          · exact cIf_hasType
          · apply HasType.var
            native_decide
        · exact boolTy_closed
      · exact (by simpa [cFalse] using (show ⊢ Term.cFalse : boolTy from by
          unfold Term.cFalse boolTy
          apply HasType.tlam
          simp only [shiftContext, List.map_nil]
          apply HasType.lam
          · simp [Ty.WF]
          · apply HasType.lam
            · simp [Ty.WF]
            · apply HasType.var
              native_decide))
    · exact (by simpa [cTrue] using (show ⊢ Term.cTrue : boolTy from by
        unfold Term.cTrue boolTy
        apply HasType.tlam
        simp only [shiftContext, List.map_nil]
        apply HasType.lam
        · simp [Ty.WF]
        · apply HasType.lam
          · simp [Ty.WF]
          · apply HasType.var
            native_decide))

theorem cAnd_hasType :
    ⊢ cAnd : boolTy ⇒ boolTy ⇒ boolTy := by
  unfold cAnd
  apply HasType.lam
  · exact boolTy_closed
  · apply HasType.lam
    · exact boolTy_closed
    · apply HasType.app
      · apply HasType.app
        · apply HasType.tapp
          · apply HasType.app
            · exact cIf_hasType
            · apply HasType.var
              native_decide
          · exact boolTy_closed
        · apply HasType.var
          native_decide
      · simpa [cFalse] using (show ⊢ Term.cFalse : boolTy from by
          unfold Term.cFalse boolTy
          apply HasType.tlam
          simp only [shiftContext, List.map_nil]
          apply HasType.lam
          · simp [Ty.WF]
          · apply HasType.lam
            · simp [Ty.WF]
            · apply HasType.var
              native_decide)

theorem cOr_hasType :
    ⊢ cOr : boolTy ⇒ boolTy ⇒ boolTy := by
  unfold cOr
  apply HasType.lam
  · exact boolTy_closed
  · apply HasType.lam
    · exact boolTy_closed
    · apply HasType.app
      · apply HasType.app
        · apply HasType.tapp
          · apply HasType.app
            · exact cIf_hasType
            · apply HasType.var
              native_decide
          · exact boolTy_closed
        · simpa [cTrue] using (show ⊢ Term.cTrue : boolTy from by
            unfold Term.cTrue boolTy
            apply HasType.tlam
            simp only [shiftContext, List.map_nil]
            apply HasType.lam
            · simp [Ty.WF]
            · apply HasType.lam
              · simp [Ty.WF]
              · apply HasType.var
                native_decide)
      · apply HasType.var
        native_decide

theorem cZero_hasType :
    ⊢ cZero : natTy := by
  simpa [cZero, Term.cZero] using (show ⊢ Term.cZero : natTy from by
    unfold Term.cZero natTy
    apply HasType.tlam
    simp only [shiftContext, List.map_nil]
    apply HasType.lam
    · simp [Ty.WF]
    · apply HasType.lam
      · simp [Ty.WF]
      · apply HasType.var
        native_decide)

theorem cSucc_hasType :
    ⊢ cSucc : natTy ⇒ natTy := by
  unfold cSucc natTy
  apply HasType.lam
  · exact natTy_closed
  · apply HasType.tlam
    simp only [shiftContext, List.map_cons, List.map_nil]
    apply HasType.lam
    · simp [Ty.WF]
    · apply HasType.lam
      · simp [Ty.WF]
      · apply HasType.app
        · apply HasType.var
          native_decide
        · apply HasType.app
          · apply HasType.app
            · apply HasType.tapp
              · apply HasType.var
                native_decide
              · simp [Ty.WF]
            · apply HasType.var
              native_decide
          · apply HasType.var
            native_decide

theorem cNum_hasType (n : Nat) :
    ⊢ cNum n : natTy := by
  induction n with
  | zero =>
    simpa [cNum] using cZero_hasType
  | succ n ih =>
    simpa [cNum] using HasType.app cSucc_hasType ih

theorem cPlus_hasType :
    ⊢ cPlus : natTy ⇒ natTy ⇒ natTy := by
  unfold cPlus natTy
  apply HasType.lam
  · exact natTy_closed
  · apply HasType.lam
    · exact natTy_closed
    · apply HasType.tlam
      simp only [shiftContext, List.map_cons, List.map]
      apply HasType.lam
      · simp [Ty.WF]
      · apply HasType.lam
        · simp [Ty.WF]
        · apply HasType.app
          · apply HasType.app
            · apply HasType.tapp
              · apply HasType.var
                native_decide
              · simp [Ty.WF]
            · apply HasType.var
              native_decide
          · apply HasType.app
            · apply HasType.app
              · apply HasType.tapp
                · apply HasType.var
                  native_decide
                · simp [Ty.WF]
              · apply HasType.var
                native_decide
            · apply HasType.var
              native_decide

theorem cMult_hasType :
    ⊢ cMult : natTy ⇒ natTy ⇒ natTy := by
  unfold cMult natTy
  apply HasType.lam
  · exact natTy_closed
  · apply HasType.lam
    · exact natTy_closed
    · apply HasType.tlam
      simp only [shiftContext, List.map_cons, List.map]
      apply HasType.lam
      · simp [Ty.WF]
      · apply HasType.lam
        · simp [Ty.WF]
        · apply HasType.app
          · apply HasType.app
            · apply HasType.tapp
              · apply HasType.var
                native_decide
              · simp [Ty.WF]
            · apply HasType.app
              · apply HasType.app
                · apply HasType.tapp
                  · apply HasType.var
                    native_decide
                  · simp [Ty.WF]
                · apply HasType.var
                  native_decide
              · apply HasType.var
                native_decide
          · apply HasType.var
            native_decide

theorem pairTy_wf {A B : Ty} (hA : Ty.WF 0 A) (hB : Ty.WF 0 B) :
    Ty.WF 0 (pairTy A B) := by
  unfold pairTy Ty.WF
  exact ⟨⟨Ty.WF_shiftTyUp 1 0 hA, Ty.WF_shiftTyUp 1 0 hB⟩, Nat.zero_lt_one⟩

theorem cPair_hasType {A B : Ty} (hA : Ty.WF 0 A) (hB : Ty.WF 0 B) :
    ⊢ cPair A B : A ⇒ B ⇒ pairTy A B := by
  unfold cPair
  apply HasType.lam
  · exact hA
  · apply HasType.lam
    · exact hB
    · apply HasType.tlam
      simp only [shiftContext, List.map_cons, List.map]
      apply HasType.lam
      · unfold Ty.WF
        exact ⟨Ty.WF_shiftTyUp 1 0 hA, Ty.WF_shiftTyUp 1 0 hB, Nat.zero_lt_one⟩
      · apply HasType.app
        · apply HasType.app
          · apply HasType.var
            native_decide
          · apply HasType.var
            native_decide
        · apply HasType.var
          native_decide

theorem cFst_hasType {A B : Ty} (hA : Ty.WF 0 A) (hB : Ty.WF 0 B) :
    ⊢ cFst A B : pairTy A B ⇒ A := by
  unfold cFst
  apply HasType.lam
  · exact pairTy_wf hA hB
  · apply HasType.app
    · apply HasType.tapp
      · apply HasType.var
        native_decide
      · exact hA
    · apply HasType.lam
      · exact hA
      · apply HasType.lam
        · exact hB
        · apply HasType.var
          native_decide

theorem cSnd_hasType {A B : Ty} (hA : Ty.WF 0 A) (hB : Ty.WF 0 B) :
    ⊢ cSnd A B : pairTy A B ⇒ B := by
  unfold cSnd
  apply HasType.lam
  · exact pairTy_wf hA hB
  · apply HasType.app
    · apply HasType.tapp
      · apply HasType.var
        native_decide
      · exact hB
    · apply HasType.lam
      · exact hA
      · apply HasType.lam
        · exact hB
        · apply HasType.var
          native_decide

end Metatheory.SystemF
