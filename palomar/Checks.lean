import PalomarCommon

/-!
# Positive and negative checker regressions

These examples exercise the executable boundary independently of the
proposition-level proof in `Solution.lean`: the accepted package is positive,
while missing coverage, a symmetric duplicate, and a bad valley are rejected.
-/

namespace Metatheory.Palomar433

open Node

def symmetricCertificate : PeakCertificate :=
  { leftStep := ⟨3, root, right⟩
    rightStep := ⟨3, root, left⟩
    join := join
    leftPath := [⟨2, right, join⟩]
    rightPath := [⟨2, left, join⟩] }

def badValleyCertificate : PeakCertificate :=
  { leftStep := ⟨3, root, left⟩
    rightStep := ⟨3, root, right⟩
    join := root
    leftPath := [⟨2, left, join⟩]
    rightPath := [⟨2, right, join⟩] }

#eval checkB semanticSteps semanticCertificates
#eval checkB semanticSteps []
#eval checkB semanticSteps [symmetricCertificate]
#eval checkB semanticSteps [badValleyCertificate]

example : checkB semanticSteps semanticCertificates = true := by
  decide

example : checkB semanticSteps [] = false := by
  decide

example : checkB semanticSteps [symmetricCertificate] = false := by
  decide

example : checkB semanticSteps [badValleyCertificate] = false := by
  decide

end Metatheory.Palomar433
