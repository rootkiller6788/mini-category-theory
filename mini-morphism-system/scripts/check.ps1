Write-Host "Checking mini-morphism-system ..."

$projectDir = Split-Path -Parent $PSScriptRoot

Push-Location $projectDir
try {
    Write-Host "  Building MiniMorphismSystem..."
    $result = lake build 2>&1
    if ($LASTEXITCODE -ne 0) {
        Write-Host "  BUILD FAILED" -ForegroundColor Red
        Write-Host $result
        Pop-Location
        exit 1
    }
    Write-Host "  Build: OK"

    Write-Host "  Running smoke tests..."
    $result = lake env lean --run Test/Smoke.lean 2>&1
    if ($LASTEXITCODE -ne 0) {
        Write-Host "  SMOKE TESTS FAILED" -ForegroundColor Red
        Write-Host $result
        Pop-Location
        exit 1
    }
    Write-Host "  Smoke tests: OK"

    Write-Host "  Running examples..."
    $result = lake env lean --run Test/Examples.lean 2>&1
    if ($LASTEXITCODE -ne 0) {
        Write-Host "  EXAMPLES FAILED" -ForegroundColor Red
        Write-Host $result
        Pop-Location
        exit 1
    }
    Write-Host "  Examples: OK"

    Write-Host "  Running regression tests..."
    $result = lake env lean --run Test/Regression.lean 2>&1
    if ($LASTEXITCODE -ne 0) {
        Write-Host "  REGRESSION TESTS FAILED" -ForegroundColor Red
        Write-Host $result
        Pop-Location
        exit 1
    }
    Write-Host "  Regression: OK"

    Write-Host "  Running CoreCoverage benchmark..."
    $result = lake env lean --run Benchmark/CoreCoverage.lean 2>&1
    if ($LASTEXITCODE -ne 0) {
        Write-Host "  COVERAGE BENCHMARK FAILED" -ForegroundColor Red
        Write-Host $result
        Pop-Location
        exit 1
    }
    Write-Host "  Coverage: OK"

    Write-Host ""
    Write-Host "All checks passed!" -ForegroundColor Green
} finally {
    Pop-Location
}
