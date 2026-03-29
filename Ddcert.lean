import Metatheory.Rewriting.DecreasingDiagramsCertificate
import Metatheory.Rewriting.DecreasingDiagramsExample
import Metatheory.Rewriting.DecreasingDiagramsFamily

open Rewriting
open System

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

def parseNatArg (cmd : String) (name value : String) : Except String Nat :=
  match value.toNat? with
  | some n => Except.ok n
  | none => Except.error s!"{cmd}: expected {name} to be a natural number, got '{value}'"

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
  | _ =>
      IO.eprintln usage
      pure 1

end Ddcert

def main (args : List String) : IO UInt32 :=
  Ddcert.run args
