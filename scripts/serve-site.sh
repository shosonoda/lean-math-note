#!/usr/bin/env sh
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

cd "$repo_root"

MKDOCS_SERVE_CONFIG="${MKDOCS_SERVE_CONFIG:-.mkdocs.serve.yml}"
SERVE_LIVERELOAD="${SERVE_LIVERELOAD:-0}"

MKDOCS_GENERATED_CONFIG="$MKDOCS_SERVE_CONFIG" \
BUILD_MKDOCS=0 \
"$script_dir/build-site.sh"

if [ "$SERVE_LIVERELOAD" = "1" ]; then
  echo "Running: mkdocs serve --livereload -f $MKDOCS_SERVE_CONFIG $*"
  mkdocs serve --livereload -f "$MKDOCS_SERVE_CONFIG" "$@"
else
  echo "Running: mkdocs serve --no-livereload -f $MKDOCS_SERVE_CONFIG $*"
  mkdocs serve --no-livereload -f "$MKDOCS_SERVE_CONFIG" "$@"
fi
