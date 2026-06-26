#!/bin/bash
set -e

echo "Checking mini-limit-colimit ..."

PROJECT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_DIR"

echo "  Building MiniLimitColimit..."
lake build
echo "  Build: OK"

echo "  Running smoke tests..."
lake env lean --run Test/Smoke.lean
echo "  Smoke tests: OK"

echo "  Running examples..."
lake env lean --run Test/Examples.lean
echo "  Examples: OK"

echo "  Running regression tests..."
lake env lean --run Test/Regression.lean
echo "  Regression: OK"

echo "  Running CoreCoverage benchmark..."
lake env lean --run Benchmark/CoreCoverage.lean
echo "  Coverage: OK"

echo ""
echo "All checks passed!"
