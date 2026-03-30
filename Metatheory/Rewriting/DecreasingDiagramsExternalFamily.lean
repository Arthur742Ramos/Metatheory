import Metatheory.Rewriting.DecreasingDiagramsExternal

namespace Metatheory.RewritingExternalFamily

open Rewriting

abbrev Node := Nat
abbrev Label := Nat

def step (label source target : Nat) : StepTriple Node Label :=
  { label := label, source := source, target := target }

def hub (i : Nat) : Node :=
  4 * i

def left (i : Nat) : Node :=
  4 * i + 1

def right (i : Nat) : Node :=
  4 * i + 2

def join (i : Nat) : Node :=
  4 * i + 3

def peakLabel (i : Nat) : Label :=
  2 * i + 2

def downLabel (i : Nat) : Label :=
  2 * i + 1

def loopLabel : Label :=
  0

def reflCert (edge : StepTriple Node Label) : RawPeakCertificate Node Label where
  source := edge.source
  leftLabel := edge.label
  leftTarget := edge.target
  rightLabel := edge.label
  rightTarget := edge.target
  valley := RawValleyCertificate.refl edge.target

def peakCert (source leftLabel leftTarget rightLabel rightTarget join : Nat)
    (leftPath rightPath : PathData Node Label) : RawPeakCertificate Node Label where
  source := source
  leftLabel := leftLabel
  leftTarget := leftTarget
  rightLabel := rightLabel
  rightTarget := rightTarget
  valley := { join := join, leftPath := leftPath, rightPath := rightPath }

def gadgetSteps (i : Nat) : List (StepTriple Node Label) :=
  [ step (peakLabel i) (hub i) (left i)
  , step (peakLabel i) (hub i) (right i)
  , step (downLabel i) (left i) (join i)
  , step (downLabel i) (right i) (join i)
  , step loopLabel (join i) (hub i)
  ]

def gadgetPeakCertLR (i : Nat) : RawPeakCertificate Node Label :=
  peakCert (hub i) (peakLabel i) (left i) (peakLabel i) (right i) (join i)
    [(downLabel i, join i)] [(downLabel i, join i)]

def gadgetPeakCertRL (i : Nat) : RawPeakCertificate Node Label :=
  peakCert (hub i) (peakLabel i) (right i) (peakLabel i) (left i) (join i)
    [(downLabel i, join i)] [(downLabel i, join i)]

def gadgetRawCerts (i : Nat) : List (RawPeakCertificate Node Label) :=
  (gadgetSteps i).map reflCert ++ [gadgetPeakCertLR i, gadgetPeakCertRL i]

def stepsUpTo : Nat → List (StepTriple Node Label)
  | 0 => []
  | k + 1 => stepsUpTo k ++ gadgetSteps k

def rawCertsUpTo : Nat → List (RawPeakCertificate Node Label)
  | 0 => []
  | k + 1 => rawCertsUpTo k ++ gadgetRawCerts k

@[simp] theorem gadgetSteps_length (i : Nat) :
    (gadgetSteps i).length = 5 := by
  simp [gadgetSteps]

@[simp] theorem gadgetRawCerts_length (i : Nat) :
    (gadgetRawCerts i).length = 7 := by
  simp [gadgetRawCerts]

@[simp] theorem stepsUpTo_length (k : Nat) :
    (stepsUpTo k).length = 5 * k := by
  induction k with
  | zero =>
      simp [stepsUpTo]
  | succ k ih =>
      simp [stepsUpTo, ih, Nat.mul_succ, Nat.add_comm]

@[simp] theorem rawCertsUpTo_length (k : Nat) :
    (rawCertsUpTo k).length = 7 * k := by
  induction k with
  | zero =>
      simp [rawCertsUpTo]
  | succ k ih =>
      simp [rawCertsUpTo, ih, Nat.mul_succ, Nat.add_comm]

/-- Family instance `n` contains `n + 1` independent self-contained peak gadgets. -/
def raw (n : Nat) : RawCertifiedLocallyDecreasing Node Label where
  steps := stepsUpTo (n + 1)
  certs := rawCertsUpTo (n + 1)

/-- Canonically compressed self-contained family instance `n`. -/
def compressed (n : Nat) : CompressedRawCertifiedLocallyDecreasing Node Label :=
  CompressedRawCertifiedLocallyDecreasing.ofRaw (raw n)

/-- Compact JSON for the uncompressed external family artifact. -/
def rawJson (n : Nat) : String :=
  RawCertifiedLocallyDecreasing.toJsonStringCompressed (raw n)

/-- Compact JSON for the compressed external family artifact. -/
def compressedJson (n : Nat) : String :=
  CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed (compressed n)

def rawArtifactName (n : Nat) : String :=
  s!"family-{n}.raw.json"

def compressedArtifactName (n : Nat) : String :=
  s!"family-{n}.json"

def rawArtifacts (maxN : Nat) : List (String × String) :=
  (List.range (maxN + 1)).map fun n => (rawArtifactName n, rawJson n)

def compressedArtifacts (maxN : Nat) : List (String × String) :=
  (List.range (maxN + 1)).map fun n => (compressedArtifactName n, compressedJson n)

/-- Exact artifact statistics for one external family instance. -/
structure ExternalFamilyStats where
  steps : Nat
  rawCerts : Nat
  compressedCerts : Nat
  rawJsonBytes : Nat
  compressedJsonBytes : Nat
  deriving Repr

def stats (n : Nat) : ExternalFamilyStats where
  steps := (raw n).steps.length
  rawCerts := (raw n).certs.length
  compressedCerts := (compressed n).certs.length
  rawJsonBytes := (rawJson n).utf8ByteSize
  compressedJsonBytes := (compressedJson n).utf8ByteSize

/-- Canonical compression is deterministic on the generated external family. -/
def roundtripMatches (n : Nat) : Bool :=
  match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) (rawJson n) with
  | Except.ok cert =>
      CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed
          (CompressedRawCertifiedLocallyDecreasing.ofRaw cert) = compressedJson n
  | Except.error _ => false

theorem raw_steps_length (n : Nat) :
    (raw n).steps.length = 5 * (n + 1) := by
  simp [raw]

theorem raw_certs_length (n : Nat) :
    (raw n).certs.length = 7 * (n + 1) := by
  simp [raw]

theorem stats_steps (n : Nat) :
    (stats n).steps = 5 * (n + 1) := by
  simp [stats, raw_steps_length]

theorem stats_rawCerts (n : Nat) :
    (stats n).rawCerts = 7 * (n + 1) := by
  simp [stats, raw_certs_length]

theorem roundtrip0_matches :
    roundtripMatches 0 = true := by
  native_decide

theorem roundtrip5_matches :
    roundtripMatches 5 = true := by
  native_decide

theorem raw0_selfContainedCheck :
    (raw 0).selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem compressed0_selfContainedCheck :
    (compressed 0).selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem raw5_selfContainedCheck :
    (raw 5).selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem compressed5_selfContainedCheck :
    (compressed 5).selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

def rawMissingLoopSelf (n : Nat) : RawCertifiedLocallyDecreasing Node Label where
  steps := (raw n).steps
  certs := (raw n).certs.erase (reflCert (step loopLabel (join 0) (hub 0)))

def compressedExtraTrivial (n : Nat) : CompressedRawCertifiedLocallyDecreasing Node Label where
  steps := (compressed n).steps
  certs := (compressed n).certs ++ [reflCert (step loopLabel (join 0) (hub 0))]

def compressedSymmetricDuplicate (n : Nat) : CompressedRawCertifiedLocallyDecreasing Node Label where
  steps := (compressed n).steps
  certs := (compressed n).certs ++ [gadgetPeakCertRL 0]

def compressedMissingPeak (n : Nat) : CompressedRawCertifiedLocallyDecreasing Node Label where
  steps := (compressed n).steps
  certs := (compressed n).certs.drop 1

def badValleyCert : RawPeakCertificate Node Label :=
  peakCert (hub 0) (peakLabel 0) (left 0) (peakLabel 0) (right 0) (join 0)
    [(downLabel 0, join 0)] [(downLabel 0, hub 0)]

def compressedBadValley (n : Nat) : CompressedRawCertifiedLocallyDecreasing Node Label where
  steps := (compressed n).steps
  certs := badValleyCert :: (compressed n).certs.drop 1

def negativeRawArtifacts : List (String × String) :=
  [ ("family-5-missing-loop-self.raw.json",
      RawCertifiedLocallyDecreasing.toJsonStringCompressed (rawMissingLoopSelf 5))
  ]

def negativeCompressedArtifacts : List (String × String) :=
  [ ("family-5-extra-trivial.json",
      CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed (compressedExtraTrivial 5))
  , ("family-5-symmetric-duplicate.json",
      CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed (compressedSymmetricDuplicate 5))
  , ("family-5-missing-peak.json",
      CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed (compressedMissingPeak 5))
  , ("family-5-bad-valley.json",
      CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed (compressedBadValley 5))
  ]

theorem raw5MissingLoopSelf_rejected :
    (rawMissingLoopSelf 5).selfContainedCheck (lt := (· < ·)) = false := by
  native_decide

theorem compressed5ExtraTrivial_rejected :
    (compressedExtraTrivial 5).selfContainedCheck (lt := (· < ·)) = false := by
  native_decide

theorem compressed5SymmetricDuplicate_rejected :
    (compressedSymmetricDuplicate 5).selfContainedCheck (lt := (· < ·)) = false := by
  native_decide

theorem compressed5MissingPeak_rejected :
    (compressedMissingPeak 5).selfContainedCheck (lt := (· < ·)) = false := by
  native_decide

theorem compressed5BadValley_rejected :
    (compressedBadValley 5).selfContainedCheck (lt := (· < ·)) = false := by
  native_decide

/-- External raw JSON artifact for the `n = 0` self-contained family instance. -/
def rawFileJson0 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external-family" / "family-0.raw.json"

/-- External compressed JSON artifact for the `n = 0` self-contained family instance. -/
def fileJson0 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external-family" / "family-0.json"

/-- External raw JSON artifact for the `n = 5` self-contained family instance. -/
def rawFileJson5 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external-family" / "family-5.raw.json"

/-- External compressed JSON artifact for the `n = 5` self-contained family instance. -/
def fileJson5 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external-family" / "family-5.json"

def rawMissingLoopSelfFileJson5 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external-family-negative" /
    "family-5-missing-loop-self.raw.json"

def extraTrivialFileJson5 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external-family-negative" /
    "family-5-extra-trivial.json"

def symmetricDuplicateFileJson5 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external-family-negative" /
    "family-5-symmetric-duplicate.json"

def missingPeakFileJson5 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external-family-negative" /
    "family-5-missing-peak.json"

def badValleyFileJson5 : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external-family-negative" /
    "family-5-bad-valley.json"

theorem rawFileJson0_eq_rawJson :
    rawFileJson0 = rawJson 0 := by
  native_decide

theorem fileJson0_eq_compressedJson :
    fileJson0 = compressedJson 0 := by
  native_decide

theorem rawFileJson5_eq_rawJson :
    rawFileJson5 = rawJson 5 := by
  native_decide

theorem fileJson5_eq_compressedJson :
    fileJson5 = compressedJson 5 := by
  native_decide

theorem rawFileJson0_checks :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) rawFileJson0 with
    | Except.ok cert => cert.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem fileJson0_checks :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) fileJson0 with
    | Except.ok cert => cert.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem rawFileJson5_checks :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) rawFileJson5 with
    | Except.ok cert => cert.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem fileJson5_checks :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) fileJson5 with
    | Except.ok cert => cert.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem rawMissingLoopSelfFileJson5_rejected :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) rawMissingLoopSelfFileJson5 with
    | Except.ok cert => cert.selfContainedCheck (lt := (· < ·)) = false
    | Except.error _ => false) = true := by
  native_decide

theorem extraTrivialFileJson5_rejected :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) extraTrivialFileJson5 with
    | Except.ok cert => cert.selfContainedCheck (lt := (· < ·)) = false
    | Except.error _ => false) = true := by
  native_decide

theorem symmetricDuplicateFileJson5_rejected :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label)
        symmetricDuplicateFileJson5 with
    | Except.ok cert => cert.selfContainedCheck (lt := (· < ·)) = false
    | Except.error _ => false) = true := by
  native_decide

theorem missingPeakFileJson5_rejected :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) missingPeakFileJson5 with
    | Except.ok cert => cert.selfContainedCheck (lt := (· < ·)) = false
    | Except.error _ => false) = true := by
  native_decide

theorem badValleyFileJson5_rejected :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) badValleyFileJson5 with
    | Except.ok cert => cert.selfContainedCheck (lt := (· < ·)) = false
    | Except.error _ => false) = true := by
  native_decide

/-- Confluence of the smallest external family instance via the compressed certificate. -/
theorem compressed0_confluent :
    Confluent (LabeledUnion (compressed 0).embeddedRelation) :=
  (compressed 0).confluent_of_selfContainedCheck_eq_true (lt := (· < ·)) Nat.lt_wfRel.wf
    compressed0_selfContainedCheck

/-- Confluence of the larger sampled external family instance via the compressed certificate. -/
theorem compressed5_confluent :
    Confluent (LabeledUnion (compressed 5).embeddedRelation) :=
  (compressed 5).confluent_of_selfContainedCheck_eq_true (lt := (· < ·)) Nat.lt_wfRel.wf
    compressed5_selfContainedCheck

end Metatheory.RewritingExternalFamily
