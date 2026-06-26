# mini-yoneda-lite: Check script (PowerShell)
# Validates the package structure and basic integrity

param(
    [switch]$Verbose
)

$ErrorActionPreference = "Stop"
$base = Split-Path -Parent $PSScriptRoot

Write-Host "=== mini-yoneda-lite Check ===" -ForegroundColor Cyan

# Check required files exist
$requiredFiles = @(
    "lakefile.lean",
    "lean-toolchain",
    "Main.lean",
    "MiniYonedaLite.lean",
    "README.md",
    "MiniYonedaLite/Core/Basic.lean",
    "MiniYonedaLite/Core/Objects.lean",
    "MiniYonedaLite/Core/Laws.lean",
    "MiniYonedaLite/Morphisms/Hom.lean",
    "MiniYonedaLite/Morphisms/Iso.lean",
    "MiniYonedaLite/Morphisms/Equivalence.lean",
    "MiniYonedaLite/Constructions/Products.lean",
    "MiniYonedaLite/Constructions/Universal.lean",
    "MiniYonedaLite/Constructions/Subobjects.lean",
    "MiniYonedaLite/Constructions/Quotients.lean",
    "MiniYonedaLite/Properties/Invariants.lean",
    "MiniYonedaLite/Properties/Preservation.lean",
    "MiniYonedaLite/Properties/ClassificationData.lean",
    "MiniYonedaLite/Theorems/Basic.lean",
    "MiniYonedaLite/Theorems/UniversalProperties.lean",
    "MiniYonedaLite/Theorems/Classification.lean",
    "MiniYonedaLite/Theorems/Main.lean",
    "MiniYonedaLite/Examples/Standard.lean",
    "MiniYonedaLite/Examples/Counterexamples.lean",
    "MiniYonedaLite/Bridges/ToAlgebra.lean",
    "MiniYonedaLite/Bridges/ToTopology.lean",
    "MiniYonedaLite/Bridges/ToGeometry.lean",
    "MiniYonedaLite/Bridges/ToComputation.lean",
    "Test/Smoke.lean",
    "Test/Examples.lean",
    "Test/Regression.lean",
    "Benchmark/CoreCoverage.lean",
    "Benchmark/Princeton.lean",
    "Benchmark/CambridgePartIII.lean",
    "Benchmark/Harvard.lean",
    "Benchmark/MIT.lean",
    "Benchmark/OxfordPartC.lean",
    "docs/architecture.md",
    "docs/coverage.md",
    "docs/dependency.md",
    "scripts/check.ps1",
    "scripts/check.sh",
    "Computation/notebooks/.gitkeep",
    "Computation/python/.gitkeep",
    "Computation/sage/.gitkeep"
)

$missing = @()
$found = @()
foreach ($file in $requiredFiles) {
    $fullPath = Join-Path $base $file
    if (Test-Path $fullPath) {
        $found += $file
        if ($Verbose) {
            Write-Host "  OK: $file" -ForegroundColor Green
        }
    } else {
        $missing += $file
        Write-Host "  MISSING: $file" -ForegroundColor Red
    }
}

Write-Host ""
Write-Host "Results: $($found.Count) found, $($missing.Count) missing" -ForegroundColor $(if ($missing.Count -eq 0) { "Green" } else { "Red" })

if ($missing.Count -eq 0) {
    Write-Host "All 45 files present!" -ForegroundColor Green
} else {
    Write-Host "Missing files detected!" -ForegroundColor Red
    exit 1
}
