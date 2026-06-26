#!/bin/bash
# mini-yoneda-lite: Check script (Bash)
# Validates the package structure and basic integrity

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BASE="$(dirname "$SCRIPT_DIR")"
VERBOSE=false

if [ "$1" = "-v" ] || [ "$1" = "--verbose" ]; then
    VERBOSE=true
fi

echo "=== mini-yoneda-lite Check ==="

REQUIRED_FILES=(
    "lakefile.lean"
    "lean-toolchain"
    "Main.lean"
    "MiniYonedaLite.lean"
    "README.md"
    "MiniYonedaLite/Core/Basic.lean"
    "MiniYonedaLite/Core/Objects.lean"
    "MiniYonedaLite/Core/Laws.lean"
    "MiniYonedaLite/Morphisms/Hom.lean"
    "MiniYonedaLite/Morphisms/Iso.lean"
    "MiniYonedaLite/Morphisms/Equivalence.lean"
    "MiniYonedaLite/Constructions/Products.lean"
    "MiniYonedaLite/Constructions/Universal.lean"
    "MiniYonedaLite/Constructions/Subobjects.lean"
    "MiniYonedaLite/Constructions/Quotients.lean"
    "MiniYonedaLite/Properties/Invariants.lean"
    "MiniYonedaLite/Properties/Preservation.lean"
    "MiniYonedaLite/Properties/ClassificationData.lean"
    "MiniYonedaLite/Theorems/Basic.lean"
    "MiniYonedaLite/Theorems/UniversalProperties.lean"
    "MiniYonedaLite/Theorems/Classification.lean"
    "MiniYonedaLite/Theorems/Main.lean"
    "MiniYonedaLite/Examples/Standard.lean"
    "MiniYonedaLite/Examples/Counterexamples.lean"
    "MiniYonedaLite/Bridges/ToAlgebra.lean"
    "MiniYonedaLite/Bridges/ToTopology.lean"
    "MiniYonedaLite/Bridges/ToGeometry.lean"
    "MiniYonedaLite/Bridges/ToComputation.lean"
    "Test/Smoke.lean"
    "Test/Examples.lean"
    "Test/Regression.lean"
    "Benchmark/CoreCoverage.lean"
    "Benchmark/Princeton.lean"
    "Benchmark/CambridgePartIII.lean"
    "Benchmark/Harvard.lean"
    "Benchmark/MIT.lean"
    "Benchmark/OxfordPartC.lean"
    "docs/architecture.md"
    "docs/coverage.md"
    "docs/dependency.md"
    "scripts/check.ps1"
    "scripts/check.sh"
    "Computation/notebooks/.gitkeep"
    "Computation/python/.gitkeep"
    "Computation/sage/.gitkeep"
)

FOUND=0
MISSING=0

for file in "${REQUIRED_FILES[@]}"; do
    if [ -f "$BASE/$file" ]; then
        FOUND=$((FOUND + 1))
        if [ "$VERBOSE" = true ]; then
            echo "  OK: $file"
        fi
    else
        MISSING=$((MISSING + 1))
        echo "  MISSING: $file"
    fi
done

echo ""
echo "Results: $FOUND found, $MISSING missing"

if [ "$MISSING" -eq 0 ]; then
    echo "All 45 files present!"
else
    echo "Missing files detected!"
    exit 1
fi
