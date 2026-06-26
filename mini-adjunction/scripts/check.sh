#!/bin/bash
echo "mini-adjunction check..."
lake build 2>&1 && echo "BUILD OK" || echo "BUILD FAILED"
