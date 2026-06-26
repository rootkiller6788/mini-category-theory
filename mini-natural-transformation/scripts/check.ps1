# mini-natural-transformation check script (PowerShell)
Write-Host "=== mini-natural-transformation: Checking build ==="
Set-Location $PSScriptRoot/..
try {
    lake build 2>&1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "Build succeeded."
    } else {
        Write-Host "Build failed with exit code $LASTEXITCODE."
        exit $LASTEXITCODE
    }
} catch {
    Write-Host "Error: $_"
    exit 1
}
