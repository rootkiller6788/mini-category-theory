#!/usr/bin/env bash
# mini-natural-transformation check script (POSIX)
echo "=== mini-natural-transformation: Checking build ==="
cd "$(dirname "$0")/.." || exit 1
lake build
if [ $? -eq 0 ]; then
    echo "Build succeeded."
else
    echo "Build failed."
    exit 1
fi
