#!/usr/bin/env sh
set -eu

INPUT_DIR="${INPUT_DIR:-LeanMathNote}"
CONTENT_DIR="${CONTENT_DIR:-site-src}"
GENERATED_MD_DIR="${GENERATED_MD_DIR:-site-generated}"
BUILD_SOURCE_DIR="${BUILD_SOURCE_DIR:-.site-build-src}"
PAGES_DIR="${PAGES_DIR:-site-pages}"
SITE_DIR="${SITE_DIR:-docs}"
MKDOCS_CONFIG="${MKDOCS_CONFIG:-mkdocs.yml}"
MKDOCS_GENERATED_CONFIG="${MKDOCS_GENERATED_CONFIG:-.mkdocs.generated.yml}"
PRINT_PAGE_NAME="${PRINT_PAGE_NAME:-print_page.md}"
BUILD_MKDOCS="${BUILD_MKDOCS:-1}"
NAV_BEFORE="${NAV_BEFORE:-$CONTENT_DIR/nav-before.yml}"
NAV_AFTER="${NAV_AFTER:-$CONTENT_DIR/nav-after.yml}"

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

cd "$repo_root"

if [ ! -d "$CONTENT_DIR" ]; then
  echo "Content directory not found: $CONTENT_DIR" >&2
  exit 1
fi

if [ ! -f "$MKDOCS_CONFIG" ]; then
  echo "MkDocs config not found: $MKDOCS_CONFIG" >&2
  exit 1
fi

echo "Running: lake exe mdgen $INPUT_DIR $GENERATED_MD_DIR"
rm -rf "$GENERATED_MD_DIR"
mkdir -p "$GENERATED_MD_DIR"
lake exe mdgen "$INPUT_DIR" "$GENERATED_MD_DIR"

find "$GENERATED_MD_DIR" -type f -name 'chapter*.md' | while IFS= read -r file; do
  tmp="${file}.tmp"
  sed -E \
    -e 's/^```lean([[:space:]].*)?$/```lean4\1/' \
    -e 's/^(```lean4[[:space:]]+title)[[:space:]]*=[[:space:]]*/\1=/' \
    "$file" | awk '
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

echo "Preparing MkDocs source: $BUILD_SOURCE_DIR"
rm -rf "$BUILD_SOURCE_DIR"
mkdir -p "$BUILD_SOURCE_DIR"
cp -R "$CONTENT_DIR"/. "$BUILD_SOURCE_DIR"/

find "$BUILD_SOURCE_DIR" -type f -name 'chapter*.md' -exec rm -f {} +

cp -R "$GENERATED_MD_DIR"/. "$BUILD_SOURCE_DIR"/

echo "Running: python3 scripts/split_chapters.py $BUILD_SOURCE_DIR $PAGES_DIR"
python3 scripts/split_chapters.py "$BUILD_SOURCE_DIR" "$PAGES_DIR"

echo "Running: python3 scripts/generate_print_page.py $PAGES_DIR $PRINT_PAGE_NAME"
python3 scripts/generate_print_page.py "$PAGES_DIR" "$PRINT_PAGE_NAME"

if [ ! -f "$PAGES_DIR/$PRINT_PAGE_NAME" ]; then
  echo "Generated print page not found: $PAGES_DIR/$PRINT_PAGE_NAME" >&2
  exit 1
fi

echo "Running: python3 scripts/generate_mkdocs_config.py $PAGES_DIR $MKDOCS_CONFIG $MKDOCS_GENERATED_CONFIG $NAV_BEFORE $NAV_AFTER"
python3 scripts/generate_mkdocs_config.py "$PAGES_DIR" "$MKDOCS_CONFIG" "$MKDOCS_GENERATED_CONFIG" "$NAV_BEFORE" "$NAV_AFTER"

python3 scripts/generate_print_page.py "$PAGES_DIR" "$PRINT_PAGE_NAME"

if [ "$BUILD_MKDOCS" != "1" ]; then
  echo "Generated MkDocs source: $PAGES_DIR"
  echo "Generated MkDocs config: $MKDOCS_GENERATED_CONFIG"
  exit 0
fi

echo "Running: mkdocs build --strict -f $MKDOCS_GENERATED_CONFIG"
mkdocs build --strict -f "$MKDOCS_GENERATED_CONFIG"

touch "$SITE_DIR/.nojekyll"
echo "Generated site: $SITE_DIR"
