#!/bin/bash
echo "mini-category-core check..."
lake build 2>&1 && echo "BUILD OK" || echo "BUILD FAILED"
