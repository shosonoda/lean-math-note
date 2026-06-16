#!/usr/bin/env sh
set -eu

INPUT_DIR="${INPUT_DIR:-LeanMathNote}"
DOCS_DIR="${DOCS_DIR:-site-src}"
PAGES_DIR="${PAGES_DIR:-site-pages}"
SITE_DIR="${SITE_DIR:-docs}"
MKDOCS_GENERATED_CONFIG=".mkdocs.generated.yml"

cleanup_generated_config() {
  rm -f "$MKDOCS_GENERATED_CONFIG"
}

trap cleanup_generated_config EXIT HUP INT TERM

echo "Running: lake exe mdgen $INPUT_DIR $DOCS_DIR"
lake exe mdgen "$INPUT_DIR" "$DOCS_DIR"

for file in "$DOCS_DIR"/chapter*.md; do
  [ -e "$file" ] || continue
  tmp="${file}.tmp"
  sed 's/^```lean$/```lean4/' "$file" | awk '
    BEGIN {
      prev_blank = 1
    }

    /^```/ {
      if (!in_math) {
        in_code = !in_code
      }
      print
      prev_blank = 0
      next
    }

    !in_code && /^[[:space:]]*\$\$[[:space:]]*$/ {
      if (!in_math && !prev_blank) {
        print ""
      }

      print "$$"

      if (in_math) {
        in_math = 0
        need_blank = 1
      } else {
        in_math = 1
      }

      prev_blank = 0
      next
    }

    {
      if (!in_code && need_blank && $0 != "") {
        print ""
      }

      need_blank = 0
      print
      prev_blank = ($0 == "")
    }
  ' > "$tmp"
  mv "$tmp" "$file"
done

echo "Running: python3 scripts/split_chapters.py $DOCS_DIR $PAGES_DIR"
python3 scripts/split_chapters.py "$DOCS_DIR" "$PAGES_DIR"

echo "Running: python3 scripts/generate_print_page.py $PAGES_DIR"
python3 scripts/generate_print_page.py "$PAGES_DIR"

echo "Running: python3 scripts/generate_mkdocs_config.py $PAGES_DIR mkdocs.yml $MKDOCS_GENERATED_CONFIG"
python3 scripts/generate_mkdocs_config.py "$PAGES_DIR" mkdocs.yml "$MKDOCS_GENERATED_CONFIG"

echo "Running: mkdocs build --strict -f $MKDOCS_GENERATED_CONFIG"
mkdocs build --strict -f "$MKDOCS_GENERATED_CONFIG"

touch "$SITE_DIR/.nojekyll"
echo "Generated site: $SITE_DIR"
