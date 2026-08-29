import PalomarCommon

/-!
# Palomar solution

The finite facts below are proved by enumeration of the independently
specified semantic relation.  The final theorem first checks the executable
certificate, reflects that result into the proposition-level package, and
then applies the generic decreasing-diagram theorem.
-/

namespace Metatheory.Palomar433

open Node

theorem semanticSteps_sound : StepsSound semanticSteps SemanticStep := by
  intro s hs
  simp [semanticSteps] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact SemanticStep.rootLeft
  · exact SemanticStep.rootRight
  · exact SemanticStep.leftJoin
  · exact SemanticStep.rightJoin
  · exact SemanticStep.joinRoot

theorem semanticSteps_complete : StepsComplete semanticSteps SemanticStep := by
  intro l a b h
  cases h <;> simp [semanticSteps]

theorem semanticCertificates_valid :
    CoversAllPeaks semanticSteps semanticCertificates SemanticStep (· < ·) := by
  intro s₁ s₂ hs₁ hs₂ hsource
  have hs₁' : s₁ = (⟨3, root, left⟩ : StepTriple) ∨
      s₁ = ⟨3, root, right⟩ ∨ s₁ = ⟨2, left, join⟩ ∨
      s₁ = ⟨2, right, join⟩ ∨ s₁ = ⟨1, join, root⟩ := by
    simpa [semanticSteps] using hs₁
  have hs₂' : s₂ = (⟨3, root, left⟩ : StepTriple) ∨
      s₂ = ⟨3, root, right⟩ ∨ s₂ = ⟨2, left, join⟩ ∨
      s₂ = ⟨2, right, join⟩ ∨ s₂ = ⟨1, join, root⟩ := by
    simpa [semanticSteps] using hs₂
  rcases hs₁' with h₁ | h₁ | h₁ | h₁ | h₁
  all_goals rcases hs₂' with h₂ | h₂ | h₂ | h₂ | h₂
  all_goals simp_all [semanticSteps, semanticCertificates, Matches,
    CertificateValid, RouteValid, RouteDecreasing, SemanticStep.leftJoin,
    SemanticStep.rightJoin]

theorem checked_complete_confluence
    {steps : List StepTriple} {certs : List PeakCertificate}
    (hcheck : checkB steps certs = true)
    (hcomplete : StepsComplete steps SemanticStep) :
    Confluent (LabeledUnion SemanticStep) := by
  exact confluent_of_locallyDecreasing Nat.lt_wfRel.wf
    (packageValid_locallyDecreasing
      (packageValid_of_checkB_eq_true hcheck) hcomplete)

theorem main_result :
    checkB semanticSteps semanticCertificates = true ∧
      StepsComplete semanticSteps SemanticStep ∧
      StrictPackageValid semanticSteps semanticCertificates SemanticStep (· < ·) ∧
      Confluent (LabeledUnion SemanticStep) := by
  have hcheck : checkB semanticSteps semanticCertificates = true := by
    decide
  have hstrict :
      StrictPackageValid semanticSteps semanticCertificates SemanticStep (· < ·) :=
    strictPackageValid_of_checkB_eq_true hcheck
  exact ⟨hcheck, semanticSteps_complete, hstrict,
    checked_complete_confluence hcheck semanticSteps_complete⟩

end Metatheory.Palomar433
