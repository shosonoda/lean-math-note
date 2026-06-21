#!/usr/bin/env sh
set -eu

usage() {
  echo "Usage:" >&2
  echo "  $0" >&2
  echo "  $0 input.md [output.pdf]" >&2
  echo "  $0 input_dir [output_dir]" >&2
  echo "" >&2
  echo "With no arguments, INPUT_DIR defaults to LeanMathNote and OUTPUT_DIR defaults to out." >&2
}

if [ "$#" -gt 2 ]; then
  usage
  exit 2
fi

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

cd "$repo_root"

cache_var=${TEXMFVAR:-"$repo_root/.tex-cache/texmf-var"}
cache_config=${TEXMFCONFIG:-"$repo_root/.tex-cache/texmf-config"}
mkdir -p "$cache_var" "$cache_config"

export TEXMFVAR=$cache_var
export TEXMFCONFIG=$cache_config

: "${CJKMAINFONT:=Hiragino Sans}"
: "${MONOFONT:=Menlo}"

convert_md() {
  src=$1
  dest=$2

  mkdir -p "$(dirname -- "$dest")"

  pandoc "$src" \
    -o "$dest" \
    --pdf-engine=xelatex \
    --resource-path="$(dirname -- "$src"):." \
    -V documentclass=bxjsarticle \
    -V classoption=xelatex \
    -V classoption=a4paper \
    -V CJKmainfont="$CJKMAINFONT" \
    -V monofont="$MONOFONT" \
    -V colorlinks=true

  echo "Generated: $dest"
}

convert_dir() {
  dir=$1
  dest_dir=${2:-}

  input_dir=${dir%/}
  if [ -z "$input_dir" ]; then
    input_dir=/
  fi

  if [ -n "$dest_dir" ]; then
    dest_dir=${dest_dir%/}
    if [ -z "$dest_dir" ]; then
      dest_dir=/
    fi
    mkdir -p "$dest_dir"
  fi

  tmp_file=$(mktemp "${TMPDIR:-/tmp}/md2pdf.XXXXXX")
  trap 'rm -f "$tmp_file"' EXIT HUP INT TERM

  find "$input_dir" -type f -name '*.md' | sort > "$tmp_file"
  if [ ! -s "$tmp_file" ]; then
    echo "No Markdown files found in: $dir" >&2
    exit 1
  fi

  while IFS= read -r src; do
    if [ -n "$dest_dir" ]; then
      rel=${src#"$input_dir"/}
      output=$dest_dir/${rel%.md}.pdf
    else
      output=${src%.md}.pdf
    fi

    convert_md "$src" "$output"
  done < "$tmp_file"
}

if [ "$#" -eq 0 ]; then
  input_dir=${INPUT_DIR:-LeanMathNote}
  output_dir=${OUTPUT_DIR:-out}

  echo "Running: lake exe mdgen $input_dir $output_dir"
  lake exe mdgen "$input_dir" "$output_dir"
  convert_dir "$output_dir" "$output_dir"
  exit 0
fi

input=$1

if [ -f "$input" ]; then
  case "$input" in
    *.md) ;;
    *)
      echo "Input file must have .md extension: $input" >&2
      exit 1
      ;;
  esac

  if [ "$#" -eq 2 ]; then
    output=$2
  else
    output=${input%.md}.pdf
  fi

  convert_md "$input" "$output"
elif [ -d "$input" ]; then
  if [ "$#" -eq 2 ]; then
    convert_dir "$input" "$2"
  else
    convert_dir "$input"
  fi
else
  echo "Input file or directory not found: $input" >&2
  exit 1
fi
