import Metatheory.Rewriting.DecreasingDiagramsCertificate
import Metatheory.Rewriting.DecreasingDiagramsExample
import Metatheory.Rewriting.DecreasingDiagramsExternalBenchmarks
import Metatheory.Rewriting.DecreasingDiagramsExternalFamily
import Metatheory.Rewriting.DecreasingDiagramsFamily

open Rewriting
open System
open Metatheory.RewritingExternalBenchmarks

namespace Ddcert

def usage : String :=
  String.intercalate "\n"
    [ "Usage:"
    , "  lake exe ddcert export-example <output.json>"
    , "  lake exe ddcert export-family <n> <output.json>"
    , "  lake exe ddcert export-bundle <output-dir> <max-family-n>"
    , "  lake exe ddcert check-example <artifact.json>"
    , "  lake exe ddcert check-family <n> <artifact.json>"
    , "  lake exe ddcert stats-family <n>"
    , "  lake exe ddcert stats-range <max-family-n>"
    , "  lake exe ddcert list-external-benchmarks"
    , "  lake exe ddcert export-external-benchmark <name> <output.json>"
    , "  lake exe ddcert export-external-benchmark-raw <name> <output.json>"
    , "  lake exe ddcert export-external-bundle <output-dir>"
    , "  lake exe ddcert export-external-family <n> <output.json>"
    , "  lake exe ddcert export-external-family-raw <n> <output.json>"
    , "  lake exe ddcert export-external-family-bundle <output-dir> <max-family-n>"
    , "  lake exe ddcert export-external-family-negative-bundle <output-dir>"
    , "  lake exe ddcert check-external <artifact.json>"
    , "  lake exe ddcert check-external-raw <artifact.json>"
    , "  lake exe ddcert compress-external <input.raw.json> <output.json>"
    , "  lake exe ddcert roundtrip-external-family <n>"
    , "  lake exe ddcert roundtrip-external-family-range <max-family-n>"
    , "  lake exe ddcert stats-external-benchmark <name>"
    , "  lake exe ddcert stats-external-benchmarks"
    , "  lake exe ddcert stats-external-family <n>"
    , "  lake exe ddcert stats-external-family-range <max-family-n>"
    ]

def asPath (path : String) : FilePath :=
  ⟨path⟩

def ensureParentDir (path : FilePath) : IO Unit := do
  if let some parent := path.parent then
    IO.FS.createDirAll parent

def writeArtifact (path : FilePath) (artifact : String) : IO Unit := do
  ensureParentDir path
  IO.FS.writeFile path artifact
  IO.println s!"wrote {path}"

def writeNamedArtifacts (dir : FilePath) (artifacts : List (String × String)) : IO Nat := do
  let mut count := 0
  for (name, artifact) in artifacts do
    writeArtifact (dir / name) artifact
    count := count + 1
  pure count

def parseNatArg (cmd : String) (name value : String) : Except String Nat :=
  match value.toNat? with
  | some n => Except.ok n
  | none => Except.error s!"{cmd}: expected {name} to be a natural number, got '{value}'"

def lookupExternalBenchmark (name : String) :
    Except String Metatheory.RewritingExternalBenchmarks.ExternalBenchmark :=
  match findBenchmark? name with
  | some benchmark => Except.ok benchmark
  | none =>
      Except.error <|
        s!"unknown external benchmark '{name}'; available benchmarks: " ++
          String.intercalate ", " benchmarkNames

def exportExample (output : String) : IO UInt32 := do
  writeArtifact (asPath output) Metatheory.RewritingExample.stepCertificateJson
  pure 0

def exportFamily (n : Nat) (output : String) : IO UInt32 := do
  writeArtifact (asPath output) (Metatheory.RewritingFamily.stepCertificateJson n)
  pure 0

def exportBundle (outputDir : String) (maxFamily : Nat) : IO UInt32 := do
  let dir := asPath outputDir
  IO.FS.createDirAll dir
  writeArtifact (dir / "example.json") Metatheory.RewritingExample.stepCertificateJson
  for n in List.range (maxFamily + 1) do
    writeArtifact (dir / s!"family-{n}.json") (Metatheory.RewritingFamily.stepCertificateJson n)
  IO.println s!"exported {maxFamily + 2} decreasing-diagram artifacts to {dir}"
  pure 0

def reportCheck (systemName : String) (path : FilePath) (result : Except String Bool) : IO UInt32 := do
  match result with
  | Except.ok true =>
      IO.println s!"ok: {systemName} certificate checks for {path}"
      pure 0
  | Except.ok false =>
      IO.eprintln s!"check failed: {systemName} certificate rejected {path}"
      pure 1
  | Except.error err =>
      IO.eprintln s!"parse failed for {path}: {err}"
      pure 1

def checkExample (input : String) : IO UInt32 := do
  let path := asPath input
  let artifact ← IO.FS.readFile path
  reportCheck "example" path <|
    CompressedRawCertifiedLocallyDecreasing.checkJson
      (α := Metatheory.RewritingExample.Node) (L := Nat)
      (r := Metatheory.RewritingExample.LStep) (lt := (· < ·))
      artifact

def checkFamily (n : Nat) (input : String) : IO UInt32 := do
  let path := asPath input
  let artifact ← IO.FS.readFile path
  reportCheck s!"family[{n}]" path <|
    CompressedRawCertifiedLocallyDecreasing.checkJson
      (α := Metatheory.RewritingFamily.Node n) (L := Metatheory.RewritingFamily.Label n)
      (r := Metatheory.RewritingFamily.LStep n) (lt := Metatheory.RewritingFamily.LabelLt n)
      artifact

def checkExternalRawArtifact (artifact : String) : Except String Bool := do
  let raw ← RawCertifiedLocallyDecreasing.parseJson? (α := Nat) (L := Nat) artifact
  pure (raw.selfContainedCheck (lt := (· < ·)))

def checkExternalCompressedArtifact (artifact : String) : Except String Bool := do
  let raw ← CompressedRawCertifiedLocallyDecreasing.parseJson? (α := Nat) (L := Nat) artifact
  pure (raw.selfContainedCheck (lt := (· < ·)))

def listExternalBenchmarks : IO UInt32 := do
  for name in benchmarkNames do
    IO.println name
  pure 0

def exportExternalBenchmark (name output : String) : IO UInt32 := do
  match lookupExternalBenchmark name with
  | Except.error err =>
      IO.eprintln err
      pure 1
  | Except.ok benchmark =>
      writeArtifact (asPath output) benchmark.compressedJson
      pure 0

def exportExternalBenchmarkRaw (name output : String) : IO UInt32 := do
  match lookupExternalBenchmark name with
  | Except.error err =>
      IO.eprintln err
      pure 1
  | Except.ok benchmark =>
      writeArtifact (asPath output) benchmark.rawJson
      pure 0

def exportExternalBundle (outputDir : String) : IO UInt32 := do
  let dir := asPath outputDir
  let externalDir := dir / "external"
  let negativeDir := dir / "negative"
  IO.FS.createDirAll externalDir
  IO.FS.createDirAll negativeDir
  let positiveCount ← writeNamedArtifacts externalDir positiveRawArtifacts
  let positiveCount := positiveCount + (← writeNamedArtifacts externalDir positiveCompressedArtifacts)
  let negativeCount ← writeNamedArtifacts negativeDir negativeRawArtifacts
  let negativeCount := negativeCount + (← writeNamedArtifacts negativeDir negativeCompressedArtifacts)
  IO.println s!"exported {positiveCount} external benchmark artifacts and {negativeCount} negative artifacts"
  pure 0

def exportExternalFamily (n : Nat) (output : String) : IO UInt32 := do
  writeArtifact (asPath output) (Metatheory.RewritingExternalFamily.compressedJson n)
  pure 0

def exportExternalFamilyRaw (n : Nat) (output : String) : IO UInt32 := do
  writeArtifact (asPath output) (Metatheory.RewritingExternalFamily.rawJson n)
  pure 0

def exportExternalFamilyBundle (outputDir : String) (maxFamily : Nat) : IO UInt32 := do
  let dir := asPath outputDir
  IO.FS.createDirAll dir
  let rawCount ← writeNamedArtifacts dir (Metatheory.RewritingExternalFamily.rawArtifacts maxFamily)
  let compressedCount ← writeNamedArtifacts dir (Metatheory.RewritingExternalFamily.compressedArtifacts maxFamily)
  IO.println s!"exported {rawCount} raw and {compressedCount} compressed external family artifacts to {dir}"
  pure 0

def exportExternalFamilyNegativeBundle (outputDir : String) : IO UInt32 := do
  let dir := asPath outputDir
  IO.FS.createDirAll dir
  let rawCount ← writeNamedArtifacts dir Metatheory.RewritingExternalFamily.negativeRawArtifacts
  let compressedCount ← writeNamedArtifacts dir Metatheory.RewritingExternalFamily.negativeCompressedArtifacts
  IO.println s!"exported {rawCount} raw and {compressedCount} compressed negative external family artifacts to {dir}"
  pure 0

def checkExternal (input : String) : IO UInt32 := do
  let path := asPath input
  let artifact ← IO.FS.readFile path
  reportCheck "external" path (checkExternalCompressedArtifact artifact)

def checkExternalRaw (input : String) : IO UInt32 := do
  let path := asPath input
  let artifact ← IO.FS.readFile path
  reportCheck "external raw" path (checkExternalRawArtifact artifact)

def compressExternal (input output : String) : IO UInt32 := do
  let path := asPath input
  let artifact ← IO.FS.readFile path
  match RawCertifiedLocallyDecreasing.parseJson? (α := Nat) (L := Nat) artifact with
  | Except.error err =>
      IO.eprintln s!"parse failed for {path}: {err}"
      pure 1
  | Except.ok raw =>
      writeArtifact (asPath output) <|
        CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed
          (CompressedRawCertifiedLocallyDecreasing.ofRaw raw)
      pure 0

def roundtripExternalFamilyArtifact (n : Nat) : Except String Bool := do
  let raw ← RawCertifiedLocallyDecreasing.parseJson? (α := Nat) (L := Nat)
    (Metatheory.RewritingExternalFamily.rawJson n)
  pure <|
    CompressedRawCertifiedLocallyDecreasing.toJsonStringCompressed
        (CompressedRawCertifiedLocallyDecreasing.ofRaw raw) =
      Metatheory.RewritingExternalFamily.compressedJson n

def roundtripExternalFamily (n : Nat) : IO UInt32 := do
  match roundtripExternalFamilyArtifact n with
  | Except.ok true =>
      IO.println s!"ok: external-family[{n}] roundtrip matches canonical compression"
      pure 0
  | Except.ok false =>
      IO.eprintln s!"roundtrip failed: external-family[{n}] recompression does not match the canonical artifact"
      pure 1
  | Except.error err =>
      IO.eprintln s!"roundtrip failed: external-family[{n}] could not parse its raw artifact: {err}"
      pure 1

def roundtripExternalFamilyRange (maxFamily : Nat) : IO UInt32 := do
  IO.println "n,roundtrip"
  let mut ok := true
  for n in List.range (maxFamily + 1) do
    let status :=
      match roundtripExternalFamilyArtifact n with
      | Except.ok true => "ok"
      | Except.ok false => "mismatch"
      | Except.error err => s!"error:{err}"
    if status ≠ "ok" then
      ok := false
    IO.println s!"{n},{status}"
  pure <| if ok then 0 else 1

def percentSaved (old new : Nat) : Nat :=
  if old = 0 then
    0
  else
    ((old - new) * 100) / old

def benchmarkRuns : Nat := 50

def timeThunkNanos {α : Type} (f : Unit → α) : IO (Nat × α) := do
  let start ← IO.monoNanosNow
  let result := f ()
  let finish ← IO.monoNanosNow
  pure (finish - start, result)

def timeThunkAvgMicros {α : Type} (runs : Nat) (f : Unit → α) : IO (Nat × α) := do
  let runs := max runs 1
  let start ← IO.monoNanosNow
  let mut last? : Option α := none
  for _ in List.range runs do
    last? := some (f ())
  let finish ← IO.monoNanosNow
  match last? with
  | some result =>
      let avgNanos := ((finish - start) + runs / 2) / runs
      pure ((avgNanos + 500) / 1000, result)
  | none =>
      unreachable!

def renderCheckResult (result : Except String Bool) : String :=
  match result with
  | Except.ok true => "ok"
  | Except.ok false => "false"
  | Except.error err => s!"error:{err}"

def statsFamily (n : Nat) : IO UInt32 := do
  let stats := Metatheory.RewritingFamily.stats n
  let (rawMicros, rawResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
    RawCertifiedLocallyDecreasing.checkJson
      (α := Metatheory.RewritingFamily.Node n) (L := Metatheory.RewritingFamily.Label n)
      (r := Metatheory.RewritingFamily.LStep n) (lt := Metatheory.RewritingFamily.LabelLt n)
      (Metatheory.RewritingFamily.rawStepCertificateJson n)
  let (compressedMicros, compressedResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
    CompressedRawCertifiedLocallyDecreasing.checkJson
      (α := Metatheory.RewritingFamily.Node n) (L := Metatheory.RewritingFamily.Label n)
      (r := Metatheory.RewritingFamily.LStep n) (lt := Metatheory.RewritingFamily.LabelLt n)
      (Metatheory.RewritingFamily.stepCertificateJson n)
  IO.println s!"family[{n}]"
  IO.println s!"steps: {stats.steps}"
  IO.println s!"raw certs: {stats.rawCerts}"
  IO.println s!"compressed certs: {stats.compressedCerts}"
  IO.println s!"cert reduction: {percentSaved stats.rawCerts stats.compressedCerts}%"
  IO.println s!"raw json bytes: {stats.rawJsonBytes}"
  IO.println s!"compressed json bytes: {stats.compressedJsonBytes}"
  IO.println s!"json reduction: {percentSaved stats.rawJsonBytes stats.compressedJsonBytes}%"
  IO.println s!"benchmark runs: {benchmarkRuns}"
  IO.println s!"raw check: {renderCheckResult rawResult} ({rawMicros} us avg)"
  IO.println s!"compressed check: {renderCheckResult compressedResult} ({compressedMicros} us avg)"
  pure <|
    if rawResult = Except.ok true ∧ compressedResult = Except.ok true then
      0
    else
      1

def statsRange (maxFamily : Nat) : IO UInt32 := do
  IO.println "n,steps,raw_certs,compressed_certs,cert_saved_pct,raw_json_bytes,compressed_json_bytes,json_saved_pct,benchmark_runs,raw_check_us,compressed_check_us,raw_check,compressed_check"
  let mut ok := true
  for n in List.range (maxFamily + 1) do
    let stats := Metatheory.RewritingFamily.stats n
    let (rawMicros, rawResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
      RawCertifiedLocallyDecreasing.checkJson
        (α := Metatheory.RewritingFamily.Node n) (L := Metatheory.RewritingFamily.Label n)
        (r := Metatheory.RewritingFamily.LStep n) (lt := Metatheory.RewritingFamily.LabelLt n)
        (Metatheory.RewritingFamily.rawStepCertificateJson n)
    let (compressedMicros, compressedResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
      CompressedRawCertifiedLocallyDecreasing.checkJson
        (α := Metatheory.RewritingFamily.Node n) (L := Metatheory.RewritingFamily.Label n)
        (r := Metatheory.RewritingFamily.LStep n) (lt := Metatheory.RewritingFamily.LabelLt n)
        (Metatheory.RewritingFamily.stepCertificateJson n)
    if rawResult ≠ Except.ok true ∨ compressedResult ≠ Except.ok true then
      ok := false
    IO.println <|
      String.intercalate ","
        [ toString n
        , toString stats.steps
        , toString stats.rawCerts
        , toString stats.compressedCerts
        , toString (percentSaved stats.rawCerts stats.compressedCerts)
        , toString stats.rawJsonBytes
        , toString stats.compressedJsonBytes
        , toString (percentSaved stats.rawJsonBytes stats.compressedJsonBytes)
        , toString benchmarkRuns
        , toString rawMicros
        , toString compressedMicros
        , renderCheckResult rawResult
        , renderCheckResult compressedResult
        ]
  pure <| if ok then 0 else 1

def statsExternalBenchmark (name : String) : IO UInt32 := do
  match lookupExternalBenchmark name with
  | Except.error err =>
      IO.eprintln err
      pure 1
  | Except.ok benchmark =>
      let rawJson := benchmark.rawJson
      let compressedJson := benchmark.compressedJson
      let steps := benchmark.raw.steps.length
      let rawCerts := benchmark.raw.certs.length
      let compressedCerts := benchmark.compressed.certs.length
      let rawJsonBytes := rawJson.utf8ByteSize
      let compressedJsonBytes := compressedJson.utf8ByteSize
      let (rawMicros, rawResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
        checkExternalRawArtifact rawJson
      let (compressedMicros, compressedResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
        checkExternalCompressedArtifact compressedJson
      IO.println s!"external[{name}]"
      IO.println s!"steps: {steps}"
      IO.println s!"raw certs: {rawCerts}"
      IO.println s!"compressed certs: {compressedCerts}"
      IO.println s!"cert reduction: {percentSaved rawCerts compressedCerts}%"
      IO.println s!"raw json bytes: {rawJsonBytes}"
      IO.println s!"compressed json bytes: {compressedJsonBytes}"
      IO.println s!"json reduction: {percentSaved rawJsonBytes compressedJsonBytes}%"
      IO.println s!"benchmark runs: {benchmarkRuns}"
      IO.println s!"raw check: {renderCheckResult rawResult} ({rawMicros} us avg)"
      IO.println s!"compressed check: {renderCheckResult compressedResult} ({compressedMicros} us avg)"
      pure <|
        if rawResult = Except.ok true ∧ compressedResult = Except.ok true then
          0
        else
          1

def statsExternalBenchmarks : IO UInt32 := do
  IO.println "name,steps,raw_certs,compressed_certs,cert_saved_pct,raw_json_bytes,compressed_json_bytes,json_saved_pct,benchmark_runs,raw_check_us,compressed_check_us,raw_check,compressed_check"
  let mut ok := true
  for benchmark in benchmarks do
    let rawJson := benchmark.rawJson
    let compressedJson := benchmark.compressedJson
    let steps := benchmark.raw.steps.length
    let rawCerts := benchmark.raw.certs.length
    let compressedCerts := benchmark.compressed.certs.length
    let rawJsonBytes := rawJson.utf8ByteSize
    let compressedJsonBytes := compressedJson.utf8ByteSize
    let (rawMicros, rawResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
      checkExternalRawArtifact rawJson
    let (compressedMicros, compressedResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
      checkExternalCompressedArtifact compressedJson
    if rawResult ≠ Except.ok true ∨ compressedResult ≠ Except.ok true then
      ok := false
    IO.println <|
      String.intercalate ","
        [ benchmark.name
        , toString steps
        , toString rawCerts
        , toString compressedCerts
        , toString (percentSaved rawCerts compressedCerts)
        , toString rawJsonBytes
        , toString compressedJsonBytes
        , toString (percentSaved rawJsonBytes compressedJsonBytes)
        , toString benchmarkRuns
        , toString rawMicros
        , toString compressedMicros
        , renderCheckResult rawResult
        , renderCheckResult compressedResult
        ]
  pure <| if ok then 0 else 1

def statsExternalFamily (n : Nat) : IO UInt32 := do
  let stats := Metatheory.RewritingExternalFamily.stats n
  let rawJson := Metatheory.RewritingExternalFamily.rawJson n
  let compressedJson := Metatheory.RewritingExternalFamily.compressedJson n
  let (rawMicros, rawResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
    checkExternalRawArtifact rawJson
  let (compressedMicros, compressedResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
    checkExternalCompressedArtifact compressedJson
  IO.println s!"external-family[{n}]"
  IO.println s!"steps: {stats.steps}"
  IO.println s!"raw certs: {stats.rawCerts}"
  IO.println s!"compressed certs: {stats.compressedCerts}"
  IO.println s!"cert reduction: {percentSaved stats.rawCerts stats.compressedCerts}%"
  IO.println s!"raw json bytes: {stats.rawJsonBytes}"
  IO.println s!"compressed json bytes: {stats.compressedJsonBytes}"
  IO.println s!"json reduction: {percentSaved stats.rawJsonBytes stats.compressedJsonBytes}%"
  IO.println s!"benchmark runs: {benchmarkRuns}"
  IO.println s!"raw check: {renderCheckResult rawResult} ({rawMicros} us avg)"
  IO.println s!"compressed check: {renderCheckResult compressedResult} ({compressedMicros} us avg)"
  pure <|
    if rawResult = Except.ok true ∧ compressedResult = Except.ok true then
      0
    else
      1

def statsExternalFamilyRange (maxFamily : Nat) : IO UInt32 := do
  IO.println "n,steps,raw_certs,compressed_certs,cert_saved_pct,raw_json_bytes,compressed_json_bytes,json_saved_pct,benchmark_runs,raw_check_us,compressed_check_us,raw_check,compressed_check"
  let mut ok := true
  for n in List.range (maxFamily + 1) do
    let stats := Metatheory.RewritingExternalFamily.stats n
    let rawJson := Metatheory.RewritingExternalFamily.rawJson n
    let compressedJson := Metatheory.RewritingExternalFamily.compressedJson n
    let (rawMicros, rawResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
      checkExternalRawArtifact rawJson
    let (compressedMicros, compressedResult) ← timeThunkAvgMicros benchmarkRuns fun _ =>
      checkExternalCompressedArtifact compressedJson
    if rawResult ≠ Except.ok true ∨ compressedResult ≠ Except.ok true then
      ok := false
    IO.println <|
      String.intercalate ","
        [ toString n
        , toString stats.steps
        , toString stats.rawCerts
        , toString stats.compressedCerts
        , toString (percentSaved stats.rawCerts stats.compressedCerts)
        , toString stats.rawJsonBytes
        , toString stats.compressedJsonBytes
        , toString (percentSaved stats.rawJsonBytes stats.compressedJsonBytes)
        , toString benchmarkRuns
        , toString rawMicros
        , toString compressedMicros
        , renderCheckResult rawResult
        , renderCheckResult compressedResult
        ]
  pure <| if ok then 0 else 1

def badNat (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

def run (args : List String) : IO UInt32 := do
  match args with
  | ["export-example", output] =>
      exportExample output
  | ["export-family", n, output] =>
      match parseNatArg "export-family" "n" n with
      | Except.ok n => exportFamily n output
      | Except.error msg => badNat msg
  | ["export-bundle", outputDir, maxFamily] =>
      match parseNatArg "export-bundle" "max-family-n" maxFamily with
      | Except.ok maxFamily => exportBundle outputDir maxFamily
      | Except.error msg => badNat msg
  | ["check-example", input] =>
      checkExample input
  | ["check-family", n, input] =>
      match parseNatArg "check-family" "n" n with
      | Except.ok n => checkFamily n input
      | Except.error msg => badNat msg
  | ["stats-family", n] =>
      match parseNatArg "stats-family" "n" n with
      | Except.ok n => statsFamily n
      | Except.error msg => badNat msg
  | ["stats-range", maxFamily] =>
      match parseNatArg "stats-range" "max-family-n" maxFamily with
      | Except.ok maxFamily => statsRange maxFamily
      | Except.error msg => badNat msg
  | ["list-external-benchmarks"] =>
      listExternalBenchmarks
  | ["export-external-benchmark", name, output] =>
      exportExternalBenchmark name output
  | ["export-external-benchmark-raw", name, output] =>
      exportExternalBenchmarkRaw name output
  | ["export-external-bundle", outputDir] =>
      exportExternalBundle outputDir
  | ["export-external-family", n, output] =>
      match parseNatArg "export-external-family" "n" n with
      | Except.ok n => exportExternalFamily n output
      | Except.error msg => badNat msg
  | ["export-external-family-raw", n, output] =>
      match parseNatArg "export-external-family-raw" "n" n with
      | Except.ok n => exportExternalFamilyRaw n output
      | Except.error msg => badNat msg
  | ["export-external-family-bundle", outputDir, maxFamily] =>
      match parseNatArg "export-external-family-bundle" "max-family-n" maxFamily with
      | Except.ok maxFamily => exportExternalFamilyBundle outputDir maxFamily
      | Except.error msg => badNat msg
  | ["export-external-family-negative-bundle", outputDir] =>
      exportExternalFamilyNegativeBundle outputDir
  | ["check-external", input] =>
      checkExternal input
  | ["check-external-raw", input] =>
      checkExternalRaw input
  | ["compress-external", input, output] =>
      compressExternal input output
  | ["roundtrip-external-family", n] =>
      match parseNatArg "roundtrip-external-family" "n" n with
      | Except.ok n => roundtripExternalFamily n
      | Except.error msg => badNat msg
  | ["roundtrip-external-family-range", maxFamily] =>
      match parseNatArg "roundtrip-external-family-range" "max-family-n" maxFamily with
      | Except.ok maxFamily => roundtripExternalFamilyRange maxFamily
      | Except.error msg => badNat msg
  | ["stats-external-benchmark", name] =>
      statsExternalBenchmark name
  | ["stats-external-benchmarks"] =>
      statsExternalBenchmarks
  | ["stats-external-family", n] =>
      match parseNatArg "stats-external-family" "n" n with
      | Except.ok n => statsExternalFamily n
      | Except.error msg => badNat msg
  | ["stats-external-family-range", maxFamily] =>
      match parseNatArg "stats-external-family-range" "max-family-n" maxFamily with
      | Except.ok maxFamily => statsExternalFamilyRange maxFamily
      | Except.error msg => badNat msg
  | _ =>
      IO.eprintln usage
      pure 1

end Ddcert

def main (args : List String) : IO UInt32 :=
  Ddcert.run args
