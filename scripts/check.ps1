$ErrorActionPreference = "Stop"

$repoRoot = Resolve-Path (Join-Path $PSScriptRoot "..")
Set-Location $repoRoot

Write-Host "Running lake build..."
lake build

Write-Host "Checking for forbidden placeholders (sorry/admit) in production Lean sources..."
$leanFiles =
  Get-ChildItem -Recurse -Filter *.lean |
  Where-Object {
    $_.FullName -notmatch '[/\\]\.lake[/\\]' -and
    $_.FullName -notmatch '[/\\]palomar[/\\]'
  }

$placeholderFiles = @()
foreach ($leanFile in $leanFiles) {
  $source = Get-Content -Raw -LiteralPath $leanFile.FullName
  $source = [regex]::Replace($source, '(?s)/-.*?-/', '')
  $source = [regex]::Replace($source, '--[^\r\n]*', '')
  if ($source -match '\bsorry\b|\badmit\b') {
    $placeholderFiles += $leanFile.FullName
  }
}

if ($placeholderFiles.Count -gt 0) {
  $placeholderFiles | ForEach-Object { Write-Host $_ }
  throw "Found forbidden placeholders (sorry/admit)."
}

Write-Host "Checking for axiom/constant declarations in Lean sources..."
$axiomFiles = @()
foreach ($leanFile in $leanFiles) {
  $source = Get-Content -Raw -LiteralPath $leanFile.FullName
  $source = [regex]::Replace($source, '(?s)/-.*?-/', '')
  $source = [regex]::Replace($source, '--[^\r\n]*', '')
  if ($source -match '(?m)^\s*(axiom|constant)\b') {
    $axiomFiles += $leanFile.FullName
  }
}

if ($axiomFiles.Count -gt 0) {
  $axiomFiles | ForEach-Object { Write-Host $_ }
  throw "Found axiom/constant declarations."
}

Write-Host "OK"
