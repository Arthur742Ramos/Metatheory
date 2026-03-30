import Metatheory.Rewriting.DecreasingDiagramsCertificate

namespace Rewriting

universe u v

namespace RawCertifiedLocallyDecreasing

variable {α : Type u} {L : Type v}
variable {lt : L → L → Prop}

/-- Interpret the artifact's step list as the entire labeled transition relation. -/
def embeddedRelation (raw : RawCertifiedLocallyDecreasing α L) : LabeledARS α L :=
  fun l a b => { label := l, source := a, target := b } ∈ raw.steps

instance instDecidableEmbeddedRelation [DecidableEq α] [DecidableEq L]
    (raw : RawCertifiedLocallyDecreasing α L) :
    ∀ l a b, Decidable (raw.embeddedRelation l a b) := by
  intro l a b
  dsimp [embeddedRelation]
  infer_instance

/-- The embedded relation is complete by construction. -/
theorem stepsComplete_embeddedRelation (raw : RawCertifiedLocallyDecreasing α L) :
    raw.StepsComplete raw.embeddedRelation := by
  intro a b l hstep
  exact hstep

/-- The embedded relation is sound by construction. -/
theorem stepsSound_embeddedRelation (raw : RawCertifiedLocallyDecreasing α L) :
    raw.StepsSound raw.embeddedRelation := by
  intro step hstep
  simpa [embeddedRelation] using hstep

/-- Self-contained checking for artifacts whose step list defines the entire system. -/
def selfContainedCheck [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    (raw : RawCertifiedLocallyDecreasing α L) : Bool :=
  raw.check (r := raw.embeddedRelation) (lt := lt)

/-- A successful self-contained raw check certifies confluence of the embedded system. -/
theorem confluent_of_selfContainedCheck_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    (wf : WellFounded lt) {raw : RawCertifiedLocallyDecreasing α L}
    (hcheck : raw.selfContainedCheck (lt := lt) = true) :
    Confluent (LabeledUnion raw.embeddedRelation) :=
  raw.confluent_of_check_eq_true (r := raw.embeddedRelation) (lt := lt) wf
    raw.stepsComplete_embeddedRelation hcheck

end RawCertifiedLocallyDecreasing

namespace CompressedRawCertifiedLocallyDecreasing

variable {α : Type u} {L : Type v}
variable {r : LabeledARS α L} {lt : L → L → Prop}

/-- Every stored compressed certificate must be non-trivial and canonically oriented. -/
def CanonicalCerts [DecidableEq α] [DecidableEq L]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) : Prop :=
  ∀ cert, cert ∈ raw.certs → shouldKeep raw.steps cert = true

/-- Boolean check for the canonical compressed-format invariant. -/
def canonicalCertsB [DecidableEq α] [DecidableEq L]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) : Bool :=
  raw.certs.all (fun cert => shouldKeep raw.steps cert)

theorem canonicalCerts_of_canonicalCertsB_eq_true [DecidableEq α] [DecidableEq L]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hcheck : raw.canonicalCertsB = true) :
    raw.CanonicalCerts := by
  intro cert hmem
  exact (List.all_eq_true.mp hcheck) cert hmem

theorem canonicalCertsB_eq_true_of_canonicalCerts [DecidableEq α] [DecidableEq L]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hcanon : raw.CanonicalCerts) :
    raw.canonicalCertsB = true := by
  apply List.all_eq_true.mpr
  intro cert hmem
  exact hcanon cert hmem

/-- Strengthened validity for compressed artifacts: certified peaks plus the canonical format invariant. -/
def StrictValid [DecidableEq α] [DecidableEq L]
    (raw : CompressedRawCertifiedLocallyDecreasing α L)
    (r : LabeledARS α L) (lt : L → L → Prop) : Prop :=
  raw.Valid r lt ∧ raw.CanonicalCerts

/-- Strong checker for compressed artifacts, enforcing the canonical representation invariant. -/
def strictCheck [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) : Bool :=
  raw.canonicalCertsB && raw.check (r := r) (lt := lt)

theorem strictValid_of_strictCheck_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hcheck : raw.strictCheck (r := r) (lt := lt) = true) :
    raw.StrictValid r lt := by
  have hand : raw.canonicalCertsB = true ∧ raw.check (r := r) (lt := lt) = true := by
    simpa [strictCheck, Bool.and_eq_true] using hcheck
  exact ⟨raw.valid_of_check_eq_true (r := r) (lt := lt) hand.2,
    raw.canonicalCerts_of_canonicalCertsB_eq_true hand.1⟩

theorem strictCheck_eq_true_of_strictValid [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hvalid : raw.StrictValid r lt) :
    raw.strictCheck (r := r) (lt := lt) = true := by
  rcases hvalid with ⟨hcore, hcanon⟩
  unfold strictCheck
  rw [raw.canonicalCertsB_eq_true_of_canonicalCerts hcanon,
    raw.check_eq_true_of_valid (r := r) (lt := lt) hcore]
  rfl

/-- Compression always produces canonically oriented non-trivial certificates. -/
theorem canonicalCerts_of_ofRaw [DecidableEq α] [DecidableEq L]
    {raw : RawCertifiedLocallyDecreasing α L} :
    (CompressedRawCertifiedLocallyDecreasing.ofRaw raw).CanonicalCerts := by
  intro cert hmem
  exact (List.mem_filter.mp hmem).2

/-- Compression preserves both certificate validity and the canonical representation invariant. -/
theorem strictValid_of_ofRaw_valid [DecidableEq α] [DecidableEq L]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hvalid : raw.Valid r lt) :
    (CompressedRawCertifiedLocallyDecreasing.ofRaw raw).StrictValid r lt := by
  exact ⟨CompressedRawCertifiedLocallyDecreasing.valid_of_ofRaw_valid (r := r) (lt := lt) hvalid,
    canonicalCerts_of_ofRaw⟩

theorem strictCheck_eq_true_of_ofRaw_valid [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    [∀ l a b, Decidable (r l a b)]
    {raw : RawCertifiedLocallyDecreasing α L}
    (hvalid : raw.Valid r lt) :
    (CompressedRawCertifiedLocallyDecreasing.ofRaw raw).strictCheck (r := r) (lt := lt) = true :=
  strictCheck_eq_true_of_strictValid (r := r) (lt := lt) (strictValid_of_ofRaw_valid (r := r) (lt := lt) hvalid)

/-- Interpret the artifact's step list as the entire labeled transition relation. -/
def embeddedRelation (raw : CompressedRawCertifiedLocallyDecreasing α L) : LabeledARS α L :=
  fun l a b => { label := l, source := a, target := b } ∈ raw.steps

instance instDecidableEmbeddedRelation [DecidableEq α] [DecidableEq L]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) :
    ∀ l a b, Decidable (raw.embeddedRelation l a b) := by
  intro l a b
  dsimp [embeddedRelation]
  infer_instance

/-- The embedded relation is complete by construction. -/
theorem stepsComplete_embeddedRelation (raw : CompressedRawCertifiedLocallyDecreasing α L) :
    raw.StepsComplete raw.embeddedRelation := by
  intro a b l hstep
  exact hstep

/-- The embedded relation is sound by construction. -/
theorem stepsSound_embeddedRelation (raw : CompressedRawCertifiedLocallyDecreasing α L) :
    raw.StepsSound raw.embeddedRelation := by
  intro step hstep
  simpa [embeddedRelation] using hstep

/-- Self-contained checking for compressed artifacts against their embedded relation. -/
def selfContainedCheck [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    (raw : CompressedRawCertifiedLocallyDecreasing α L) : Bool :=
  raw.strictCheck (r := raw.embeddedRelation) (lt := lt)

/-- A successful self-contained compressed check certifies confluence of the embedded system. -/
theorem confluent_of_selfContainedCheck_eq_true [DecidableEq α] [DecidableEq L] [DecidableRel lt]
    (wf : WellFounded lt) {raw : CompressedRawCertifiedLocallyDecreasing α L}
    (hcheck : raw.selfContainedCheck (lt := lt) = true) :
    Confluent (LabeledUnion raw.embeddedRelation) := by
  have hstrict : raw.StrictValid raw.embeddedRelation lt :=
    raw.strictValid_of_strictCheck_eq_true (r := raw.embeddedRelation) (lt := lt) hcheck
  exact raw.confluent_of_valid (r := raw.embeddedRelation) (lt := lt) wf
    hstrict.1 raw.stepsComplete_embeddedRelation

end CompressedRawCertifiedLocallyDecreasing

end Rewriting
