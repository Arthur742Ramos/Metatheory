$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
Set-Location $repoRoot

Write-Host "Running lake build..."
lake build

Write-Host "Checking for forbidden placeholders (sorry/admit) in Metatheory/..."
$leanFiles =
  Get-ChildItem -Recurse -Filter *.lean |
  Where-Object { $_.FullName -notmatch '\\\.lake\\' }

$matches = $leanFiles | Select-String -Pattern '\bsorry\b|\badmit\b' -List

if ($matches) {
  $matches | ForEach-Object { Write-Host "$($_.Path):$($_.LineNumber):$($_.Line)" }
  throw "Found forbidden placeholders (sorry/admit)."
}

Write-Host "Checking for axiom/constant declarations in Lean sources..."
$axioms = $leanFiles | Select-String -Pattern '^\s*(axiom|constant)\b' -List

if ($axioms) {
  $axioms | ForEach-Object { Write-Host "$($_.Path):$($_.LineNumber):$($_.Line)" }
  throw "Found axiom/constant declarations."
}

Write-Host "OK"
