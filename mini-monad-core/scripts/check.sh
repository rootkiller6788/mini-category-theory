#!/bin/bash
echo "mini-monad-core check..."
lake build 2>&1 && echo "BUILD OK" || echo "BUILD FAILED"
