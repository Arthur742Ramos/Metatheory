import PalomarCommon

/-!
# Palomar challenge

The challenge is to verify the checked-in finite certificate and derive
confluence for the independently specified labeled rewrite relation.  The
shared file contains the certificate language, executable checker, and the
generic decreasing-diagram theorem; the finite enumeration and final proof
belong to the solution surface.
-/

namespace Metatheory.Palomar433

/-- A checked certificate package with a complete step table implies confluence
of the relation whose steps the table describes. -/
theorem checked_complete_confluence
    {steps : List StepTriple} {certs : List PeakCertificate}
    (hcheck : checkB steps certs = true)
    (hcomplete : StepsComplete steps SemanticStep) :
    Confluent (LabeledUnion SemanticStep) := by
  sorry

/-- The finite certificate is accepted, its strict package is valid, and the
embedded rewrite relation is confluent. -/
theorem main_result :
    checkB semanticSteps semanticCertificates = true ∧
      StepsComplete semanticSteps SemanticStep ∧
      StrictPackageValid semanticSteps semanticCertificates SemanticStep (· < ·) ∧
      Confluent (LabeledUnion SemanticStep) := by
  sorry

end Metatheory.Palomar433
