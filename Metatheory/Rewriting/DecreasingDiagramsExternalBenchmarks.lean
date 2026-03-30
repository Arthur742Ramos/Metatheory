import Metatheory.Rewriting.DecreasingDiagramsExternal

namespace Metatheory.RewritingExternalBenchmarks

open Rewriting

abbrev Node := Nat
abbrev Label := Nat

def step (label source target : Nat) : StepTriple Node Label :=
  { label := label, source := source, target := target }

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

def peakPair (source leftLabel leftTarget rightLabel rightTarget join : Nat)
    (leftPath rightPath : PathData Node Label) : List (RawPeakCertificate Node Label) :=
  let cert := peakCert source leftLabel leftTarget rightLabel rightTarget join leftPath rightPath
  [cert, cert.swap]

def trivialCerts (steps : List (StepTriple Node Label)) : List (RawPeakCertificate Node Label) :=
  steps.map reflCert

structure ExternalBenchmark where
  name : String
  raw : RawCertifiedLocallyDecreasing Node Label
  deriving Repr

namespace ExternalBenchmark

def compressed (benchmark : ExternalBenchmark) : CompressedRawCertifiedLocallyDecreasing Node Label :=
  CompressedRawCertifiedLocallyDecreasing.ofRaw benchmark.raw

def rawJson (benchmark : ExternalBenchmark) : String :=
  RawCertifiedLocallyDecreasing.toJsonStringCompressed benchmark.raw

def compressedJson (benchmark : ExternalBenchmark) : String :=
  CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed benchmark.compressed

end ExternalBenchmark

/-! ## Positive Benchmarks -/

def fan3Steps : List (StepTriple Node Label) :=
  [ step 3 0 1
  , step 3 0 2
  , step 3 0 3
  , step 2 1 4
  , step 2 2 4
  , step 2 3 4
  , step 0 4 0
  ]

def fan3PeakCerts : List (RawPeakCertificate Node Label) :=
  [ peakCert 0 3 1 3 2 4 [(2, 4)] [(2, 4)]
  , peakCert 0 3 1 3 3 4 [(2, 4)] [(2, 4)]
  , peakCert 0 3 2 3 1 4 [(2, 4)] [(2, 4)]
  , peakCert 0 3 2 3 3 4 [(2, 4)] [(2, 4)]
  , peakCert 0 3 3 3 1 4 [(2, 4)] [(2, 4)]
  , peakCert 0 3 3 3 2 4 [(2, 4)] [(2, 4)]
  ]

def fan3 : ExternalBenchmark where
  name := "fan3"
  raw :=
    { steps := fan3Steps
      certs := trivialCerts fan3Steps ++ fan3PeakCerts }

def fan4Steps : List (StepTriple Node Label) :=
  [ step 4 0 1
  , step 4 0 2
  , step 4 0 3
  , step 4 0 4
  , step 2 1 5
  , step 2 2 5
  , step 2 3 5
  , step 2 4 5
  , step 0 5 0
  ]

def fan4PeakCerts : List (RawPeakCertificate Node Label) :=
  peakPair 0 4 1 4 2 5 [(2, 5)] [(2, 5)] ++
  peakPair 0 4 1 4 3 5 [(2, 5)] [(2, 5)] ++
  peakPair 0 4 1 4 4 5 [(2, 5)] [(2, 5)] ++
  peakPair 0 4 2 4 3 5 [(2, 5)] [(2, 5)] ++
  peakPair 0 4 2 4 4 5 [(2, 5)] [(2, 5)] ++
  peakPair 0 4 3 4 4 5 [(2, 5)] [(2, 5)]

def fan4 : ExternalBenchmark where
  name := "fan4"
  raw :=
    { steps := fan4Steps
      certs := trivialCerts fan4Steps ++ fan4PeakCerts }

def staggeredSteps : List (StepTriple Node Label) :=
  [ step 5 0 1
  , step 4 0 2
  , step 2 1 3
  , step 1 3 5
  , step 3 2 5
  , step 0 5 0
  ]

def staggeredPeakCerts : List (RawPeakCertificate Node Label) :=
  [ peakCert 0 5 1 4 2 5 [(2, 3), (1, 5)] [(3, 5)]
  , peakCert 0 4 2 5 1 5 [(3, 5)] [(2, 3), (1, 5)]
  ]

def staggered : ExternalBenchmark where
  name := "staggered"
  raw :=
    { steps := staggeredSteps
      certs := trivialCerts staggeredSteps ++ staggeredPeakCerts }

def shortcutSteps : List (StepTriple Node Label) :=
  [ step 5 0 1
  , step 4 0 2
  , step 1 1 2
  , step 0 2 0
  ]

def shortcutPeakCerts : List (RawPeakCertificate Node Label) :=
  peakPair 0 5 1 4 2 2 [(1, 2)] []

def shortcut : ExternalBenchmark where
  name := "shortcut"
  raw :=
    { steps := shortcutSteps
      certs := trivialCerts shortcutSteps ++ shortcutPeakCerts }

def zigzagSteps : List (StepTriple Node Label) :=
  [ step 7 0 1
  , step 6 0 2
  , step 3 1 3
  , step 1 3 6
  , step 4 2 4
  , step 2 4 5
  , step 1 5 6
  , step 0 6 0
  ]

def zigzagPeakCerts : List (RawPeakCertificate Node Label) :=
  peakPair 0 7 1 6 2 6 [(3, 3), (1, 6)] [(4, 4), (2, 5), (1, 6)]

def zigzag : ExternalBenchmark where
  name := "zigzag"
  raw :=
    { steps := zigzagSteps
      certs := trivialCerts zigzagSteps ++ zigzagPeakCerts }

def funnelSteps : List (StepTriple Node Label) :=
  [ step 6 0 1
  , step 5 0 2
  , step 4 0 3
  , step 2 1 4
  , step 1 4 7
  , step 1 2 7
  , step 3 3 5
  , step 2 5 6
  , step 1 6 7
  , step 0 7 0
  ]

def funnelPeakCerts : List (RawPeakCertificate Node Label) :=
  peakPair 0 6 1 5 2 7 [(2, 4), (1, 7)] [(1, 7)] ++
  peakPair 0 6 1 4 3 7 [(2, 4), (1, 7)] [(3, 5), (2, 6), (1, 7)] ++
  peakPair 0 5 2 4 3 7 [(1, 7)] [(3, 5), (2, 6), (1, 7)]

def funnel : ExternalBenchmark where
  name := "funnel"
  raw :=
    { steps := funnelSteps
      certs := trivialCerts funnelSteps ++ funnelPeakCerts }

def doublePeakSteps : List (StepTriple Node Label) :=
  [ step 4 0 1
  , step 4 0 2
  , step 2 1 3
  , step 2 2 3
  , step 3 3 4
  , step 3 3 5
  , step 1 4 6
  , step 1 5 6
  , step 0 6 0
  ]

def doublePeakCerts : List (RawPeakCertificate Node Label) :=
  [ peakCert 0 4 1 4 2 3 [(2, 3)] [(2, 3)]
  , peakCert 0 4 2 4 1 3 [(2, 3)] [(2, 3)]
  , peakCert 3 3 4 3 5 6 [(1, 6)] [(1, 6)]
  , peakCert 3 3 5 3 4 6 [(1, 6)] [(1, 6)]
  ]

def doublePeak : ExternalBenchmark where
  name := "double-peak"
  raw :=
    { steps := doublePeakSteps
      certs := trivialCerts doublePeakSteps ++ doublePeakCerts }

def benchmarks : List ExternalBenchmark :=
  [ fan3
  , fan4
  , staggered
  , shortcut
  , zigzag
  , funnel
  , doublePeak
  ]

def benchmarkNames : List String :=
  benchmarks.map (·.name)

def findBenchmark? (name : String) : Option ExternalBenchmark :=
  benchmarks.find? (fun benchmark => benchmark.name = name)

def positiveRawArtifacts : List (String × String) :=
  benchmarks.map fun benchmark => (s!"{benchmark.name}.raw.json", benchmark.rawJson)

def positiveCompressedArtifacts : List (String × String) :=
  benchmarks.map fun benchmark => (s!"{benchmark.name}.json", benchmark.compressedJson)

/-! ## Negative Benchmarks -/

def fan3MissingLoopSelfPeak : RawCertifiedLocallyDecreasing Node Label where
  steps := fan3.raw.steps
  certs := fan3.raw.certs.erase (reflCert (step 0 4 0))

def fan3ExtraTrivial : CompressedRawCertifiedLocallyDecreasing Node Label where
  steps := fan3.compressed.steps
  certs := fan3.compressed.certs ++ [reflCert (step 0 4 0)]

def fan3MissingPeak : CompressedRawCertifiedLocallyDecreasing Node Label where
  steps := fan3.compressed.steps
  certs := fan3.compressed.certs.drop 1

def staggeredBadValley : CompressedRawCertifiedLocallyDecreasing Node Label where
  steps := staggered.compressed.steps
  certs := [peakCert 0 5 1 4 2 5 [(2, 3), (1, 5)] [(4, 5)]]

def malformedCompressedJson : String :=
  "{\"steps\":["

def negativeRawArtifacts : List (String × String) :=
  [ ("fan3-missing-loop-self.raw.json",
      RawCertifiedLocallyDecreasing.toJsonStringCompressed fan3MissingLoopSelfPeak)
  ]

def negativeCompressedArtifacts : List (String × String) :=
  [ ("fan3-extra-trivial.json",
      CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed fan3ExtraTrivial)
  , ("fan3-missing-peak.json",
      CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed fan3MissingPeak)
  , ("staggered-bad-valley.json",
      CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed staggeredBadValley)
  , ("malformed.json", malformedCompressedJson)
  ]

/-! ## Regression Checks -/

def fan3RawFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "fan3.raw.json"

def fan3FileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "fan3.json"

def fan4RawFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "fan4.raw.json"

def fan4FileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "fan4.json"

def staggeredRawFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "staggered.raw.json"

def staggeredFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "staggered.json"

def shortcutRawFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "shortcut.raw.json"

def shortcutFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "shortcut.json"

def zigzagRawFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "zigzag.raw.json"

def zigzagFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "zigzag.json"

def funnelRawFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "funnel.raw.json"

def funnelFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "funnel.json"

def doublePeakRawFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "double-peak.raw.json"

def doublePeakFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "external" / "double-peak.json"

def fan3MissingLoopSelfFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "negative" / "fan3-missing-loop-self.raw.json"

def fan3ExtraTrivialFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "negative" / "fan3-extra-trivial.json"

def fan3MissingPeakFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "negative" / "fan3-missing-peak.json"

def staggeredBadValleyFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "negative" / "staggered-bad-valley.json"

def malformedCompressedFileJson : String :=
  include_str "../../artifacts" / "decreasing-diagrams" / "negative" / "malformed.json"

theorem fan3_raw_selfContainedCheck :
    fan3.raw.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem fan3_compressed_selfContainedCheck :
    fan3.compressed.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem fan4_raw_selfContainedCheck :
    fan4.raw.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem fan4_compressed_selfContainedCheck :
    fan4.compressed.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem staggered_raw_selfContainedCheck :
    staggered.raw.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem staggered_compressed_selfContainedCheck :
    staggered.compressed.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem shortcut_raw_selfContainedCheck :
    shortcut.raw.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem shortcut_compressed_selfContainedCheck :
    shortcut.compressed.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem zigzag_raw_selfContainedCheck :
    zigzag.raw.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem zigzag_compressed_selfContainedCheck :
    zigzag.compressed.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem funnel_raw_selfContainedCheck :
    funnel.raw.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem funnel_compressed_selfContainedCheck :
    funnel.compressed.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem doublePeak_raw_selfContainedCheck :
    doublePeak.raw.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem doublePeak_compressed_selfContainedCheck :
    doublePeak.compressed.selfContainedCheck (lt := (· < ·)) = true := by
  native_decide

theorem fan3MissingLoopSelfPeak_rejected :
    fan3MissingLoopSelfPeak.selfContainedCheck (lt := (· < ·)) = false := by
  native_decide

theorem fan3ExtraTrivial_rejected :
    fan3ExtraTrivial.selfContainedCheck (lt := (· < ·)) = false := by
  native_decide

theorem fan3MissingPeak_rejected :
    fan3MissingPeak.selfContainedCheck (lt := (· < ·)) = false := by
  native_decide

theorem staggeredBadValley_rejected :
    staggeredBadValley.selfContainedCheck (lt := (· < ·)) = false := by
  native_decide

theorem malformedCompressedJson_rejected :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label)
        malformedCompressedJson with
    | Except.error _ => true
    | _ => false) = true := by
  native_decide

theorem fan3RawFile_checks :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) fan3RawFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem fan3File_checks :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) fan3FileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem fan4RawFile_checks :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) fan4RawFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem fan4File_checks :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) fan4FileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem staggeredRawFile_checks :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) staggeredRawFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem staggeredFile_checks :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) staggeredFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem shortcutRawFile_checks :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) shortcutRawFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem shortcutFile_checks :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) shortcutFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem zigzagRawFile_checks :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) zigzagRawFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem zigzagFile_checks :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) zigzagFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem funnelRawFile_checks :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) funnelRawFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem funnelFile_checks :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) funnelFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem doublePeakRawFile_checks :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) doublePeakRawFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem doublePeakFile_checks :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) doublePeakFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·))
    | Except.error _ => false) = true := by
  native_decide

theorem fan3MissingLoopSelfFile_rejected :
    (match RawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) fan3MissingLoopSelfFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·)) = false
    | Except.error _ => false) = true := by
  native_decide

theorem fan3ExtraTrivialFile_rejected :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) fan3ExtraTrivialFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·)) = false
    | Except.error _ => false) = true := by
  native_decide

theorem fan3MissingPeakFile_rejected :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) fan3MissingPeakFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·)) = false
    | Except.error _ => false) = true := by
  native_decide

theorem staggeredBadValleyFile_rejected :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label) staggeredBadValleyFileJson with
    | Except.ok raw => raw.selfContainedCheck (lt := (· < ·)) = false
    | Except.error _ => false) = true := by
  native_decide

theorem malformedCompressedFile_rejected :
    (match CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Node) (L := Label)
        malformedCompressedFileJson with
    | Except.error _ => true
    | _ => false) = true := by
  native_decide

end Metatheory.RewritingExternalBenchmarks
