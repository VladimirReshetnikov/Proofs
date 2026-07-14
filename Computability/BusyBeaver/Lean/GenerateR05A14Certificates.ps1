param(
  [switch] $Initialize,
  [string] $Split = ""
)

# Untrusted proof-engineering utility: it only chooses module boundaries and
# writes theorem statements/proof scripts. Lean checks every emitted theorem.
$ErrorActionPreference = 'Stop'
$here = Split-Path -Parent $MyInvocation.MyCommand.Path
$root = Join-Path $here 'BusyBeaver/BB4/Certificates/R05/A14'
$moduleRoot = 'BusyBeaver.BB4.Certificates.R05.A14'
$actions = 0..15 | ForEach-Object { 'a{0:00}' -f $_ }

function Parse-Path([string] $text) {
  if ([string]::IsNullOrWhiteSpace($text)) { return [int[]]@() }
  return [int[]]($text.Split(',') | ForEach-Object { [int]$_.Trim() })
}

function Action([int] $value) { return 'a{0:00}' -f $value }
function Stem([int[]] $path) {
  return ($path | ForEach-Object { 'a{0:00}' -f $_ }) -join '_'
}
function Lean-List([int[]] $path) {
  return '[' + (($path | ForEach-Object { Action $_ }) -join ', ') + ']'
}
function File-Path([int[]] $path) {
  $parts = $path | ForEach-Object { 'A{0:00}' -f $_ }
  $dir = $root
  for ($i = 0; $i -lt $parts.Count - 1; ++$i) {
    $dir = Join-Path $dir $parts[$i]
  }
  [IO.Directory]::CreateDirectory($dir) | Out-Null
  return Join-Path $dir ($parts[-1] + '.lean')
}
function Module-Name([int[]] $path) {
  return $moduleRoot + '.' + (($path | ForEach-Object { 'A{0:00}' -f $_ }) -join '.')
}
function Write-Lean([string] $path, [string] $content) {
  [IO.File]::WriteAllText($path, ($content -replace "`r`n", "`n"))
}

function Write-Leaf([int[]] $path) {
  $stem = Stem $path
  $list = Lean-List $path
  $content = @"
import $moduleRoot.Common

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14

theorem pathCheck_$stem : CertWork.pathCheck $list = true := by
  decide

end SetTheory.BusyBeaver.BB4.Certificates.R05A14
"@
  Write-Lean (File-Path $path) $content
}

function Write-Parent([int[]] $path) {
  $stem = Stem $path
  $list = Lean-List $path
  $used = 3
  foreach ($choice in $path) {
    if (($choice % 4) -eq 3) { $used = 4 }
  }
  $canonical = if ($used -eq 3) { 'canonicalActions_three_eq' } else { 'canonicalActions_four_eq' }
  $imports = 0..15 | ForEach-Object {
    $child = [int[]]($path + $_)
    'import ' + (Module-Name $child)
  }
  $haves = 0..15 | ForEach-Object {
    $suffix = '{0:00}' -f $_
    $childStem = $stem + '_a' + $suffix
    @"
    have h$suffix : ((CertWork.after $list).assign a$suffix).check = true := by
      rw [CertWork.assign_check_eq_pathAppend]
      exact pathCheck_$childStem
"@
  }
  $names = (0..15 | ForEach-Object { 'h{0:00}' -f $_ }) -join ', '
  $content = @"
$($imports -join "`n")

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14

theorem pathCheck_$stem : CertWork.pathCheck $list = true := by
  have hAll :
      (TNF.canonicalActions (CertWork.after $list).used).all
        (fun action => ((CertWork.after $list).assign action).check) = true := by
$($haves -join '')
    rw [show (CertWork.after $list).used = $used by decide,
      Certificates.$canonical]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      $names]
    simp
  rw [CertWork.pathCheck_eq_expand]
  change
    (haltWritesSafe (CertWork.after $list).cfg &&
      (TNF.canonicalActions (CertWork.after $list).used).all
        (fun action => ((CertWork.after $list).assign action).check)) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates.R05A14
"@
  Write-Lean (File-Path $path) $content
}

function Write-Top {
  $imports = 0..15 | ForEach-Object {
    'import ' + $moduleRoot + '.A' + ('{0:00}' -f $_)
  }
  $haves = 0..15 | ForEach-Object {
    $suffix = '{0:00}' -f $_
    @"
    have h$suffix : Certificates.thirdBranch_a05_a14 a$suffix = true := by
      rw [CertWork.thirdBranch_eq_pathCheck]
      exact pathCheck_a$suffix
"@
  }
  $names = (0..15 | ForEach-Object { 'h{0:00}' -f $_ }) -join ', '
  $content = @"
$($imports -join "`n")

namespace SetTheory.BusyBeaver.BB4.Certificates.R05A14

theorem secondBranch_a05_a14 : Certificates.secondBranch a05 a14 = true := by
  have hAll : (TNF.canonicalActions 3).all
      Certificates.thirdBranch_a05_a14 = true := by
$($haves -join '')
    rw [Certificates.canonicalActions_three_eq]
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true,
      $names]
    simp
  change
    (haltWritesSafe (stepGo (stepGo (initial 4) a05) a14) &&
      (TNF.canonicalActions 3).all Certificates.thirdBranch_a05_a14) = true
  exact Bool.and_eq_true_iff.mpr ⟨by decide, hAll⟩

end SetTheory.BusyBeaver.BB4.Certificates.R05A14
"@
  Write-Lean (Join-Path $root '..\A14.lean') $content
}

if ($Initialize) {
  $splitRoots = @(0, 1, 2, 3, 7, 8, 9, 10, 11, 15)
  foreach ($rootAction in 0..15) {
    $path = [int[]]@($rootAction)
    if ($rootAction -in $splitRoots) {
      Write-Parent $path
      foreach ($child in 0..15) { Write-Leaf ([int[]]($path + $child)) }
    } else {
      Write-Leaf $path
    }
  }
  Write-Top
}

if (-not [string]::IsNullOrWhiteSpace($Split)) {
  $path = Parse-Path $Split
  if ($path.Count -eq 0) { throw 'A nonempty comma-separated path is required.' }
  Write-Parent $path
  foreach ($child in 0..15) { Write-Leaf ([int[]]($path + $child)) }
}

if (-not $Initialize -and [string]::IsNullOrWhiteSpace($Split)) {
  throw 'Pass -Initialize and/or -Split path.'
}
