#!/usr/bin/env sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

cd "$repo_root"

INPUT_DIR="${INPUT_DIR:-LeanMathNote}"
OUTPUT_DIR="${OUTPUT_DIR:-out}"

echo "Running: lake exe mdgen $INPUT_DIR $OUTPUT_DIR"
lake exe mdgen "$INPUT_DIR" "$OUTPUT_DIR"
