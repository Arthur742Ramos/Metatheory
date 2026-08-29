import PalomarProof

/-!
# Proved certificate-soundness theorem

The generic proof development is kept in `PalomarProof.lean` as proof-only
support: the Challenge imports no project source at all. Comparator compares
the theorem below against the core-only statement in `Challenge.lean`.
-/

namespace Metatheory.Palomar433

universe u v

theorem checked_complete_confluence
    {α : Type u} {L : Type v} [DecidableEq α] [DecidableEq L]
    {r : LabeledARS α L} {lt : L → L → Prop}
    {stepB : L → α → α → Bool} {ltB : L → L → Bool}
    {key : Certificate.Edge α L → Nat}
    {steps : List (Certificate.Edge α L)}
    {certs : List (Certificate.PeakCertificate α L)}
    (hstep : ∀ l a b, stepB l a b = true ↔ r l a b)
    (hlt : ∀ l₁ l₂, ltB l₁ l₂ = true ↔ lt l₁ l₂)
    (hcheck : Certificate.checkB stepB ltB key steps certs = true)
    (hcomplete : Certificate.StepsComplete steps r)
    (wf : WellFounded lt) :
    Confluent (LabeledUnion r) := by
  exact Certificate.checked_complete_confluence hstep hlt hcheck hcomplete wf

end Metatheory.Palomar433
