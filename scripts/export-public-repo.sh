#!/usr/bin/env sh
set -eu

usage() {
  echo "Usage: $0 [--dry-run] [--skip-build] [--allow-dirty] [--codespaces] [public_repo_url_or_path]" >&2
  echo "" >&2
  echo "Builds docs/ in this development repository and publishes it to the public repository." >&2
  echo "With --codespaces, publishes the Lean project files to the Codespaces template repository." >&2
  echo "" >&2
  echo "Environment variables:" >&2
  echo "  PUBLIC_REPO_URL     Default: https://github.com/shosonoda/lean-math-note.git" >&2
  echo "  CODESPACES_REPO_URL Default: https://github.com/shosonoda/lean-math-note-template.git" >&2
  echo "  PUBLIC_BRANCH       Default: main" >&2
  echo "  SOURCE_BRANCH       Default: main" >&2
  echo "  BUILD_SCRIPT        Default: ./scripts/build-site.sh" >&2
  echo "  MD_SCRIPT           Default: ./scripts/lean2md.sh" >&2
  echo "  COMMIT_MESSAGE      Commit message for the public repository." >&2
  echo "  PUBLIC_REPO_ALLOW_DIRTY=1 permits publishing from a dirty worktree." >&2
}

dry_run=0
skip_build=0
allow_dirty=${PUBLIC_REPO_ALLOW_DIRTY:-0}
publish_mode=site
repo_arg=

while [ "$#" -gt 0 ]; do
  case "$1" in
    --dry-run)
      dry_run=1
      ;;
    --skip-build)
      skip_build=1
      ;;
    --allow-dirty)
      allow_dirty=1
      ;;
    --codespaces)
      publish_mode=codespaces
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    -*)
      usage
      exit 2
      ;;
    *)
      if [ -n "$repo_arg" ]; then
        usage
        exit 2
      fi
      repo_arg=$1
      ;;
  esac
  shift
done

PUBLIC_BRANCH=${PUBLIC_BRANCH:-main}
SOURCE_BRANCH=${SOURCE_BRANCH:-main}
BUILD_SCRIPT=${BUILD_SCRIPT:-./scripts/build-site.sh}
MD_SCRIPT=${MD_SCRIPT:-./scripts/lean2md.sh}
SITE_DIR=${SITE_DIR:-docs}

case "$publish_mode" in
  site)
    PUBLIC_REPO_URL=${repo_arg:-${PUBLIC_REPO_URL:-https://github.com/shosonoda/lean-math-note.git}}
    PUBLISH_PATHS="LeanMathNote.lean LeanMathNote lean-toolchain lakefile.toml site-src mkdocs.yml requirements-mkdocs.txt scripts out $SITE_DIR"
    OBSOLETE_PUBLIC_PATHS="build-site.sh lean2md.sh md2pdf.sh"
    require_site_dir=1
    ;;
  codespaces)
    PUBLIC_REPO_URL=${repo_arg:-${CODESPACES_REPO_URL:-https://github.com/shosonoda/lean-math-note-template.git}}
    PUBLISH_PATHS="LeanMathNote.lean LeanMathNote lean-toolchain lakefile.toml lake-manifest.json"
    OBSOLETE_PUBLIC_PATHS=""
    require_site_dir=0
    skip_build=1
    ;;
  *)
    echo "Unknown publish mode: $publish_mode" >&2
    exit 2
    ;;
esac

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

cd "$repo_root"

current_branch=$(git branch --show-current)
if [ "$current_branch" != "$SOURCE_BRANCH" ]; then
  echo "Run this script on $SOURCE_BRANCH. Current branch: $current_branch" >&2
  exit 1
fi

source_commit=$(git rev-parse --short HEAD)
if [ "$publish_mode" = "codespaces" ]; then
  COMMIT_MESSAGE=${COMMIT_MESSAGE:-"Publish Codespaces template from lean-note-dev ${source_commit}"}
else
  COMMIT_MESSAGE=${COMMIT_MESSAGE:-"Publish site from lean-note-dev ${source_commit}"}
fi

if [ "$allow_dirty" != "1" ]; then
  dirty_paths=$(git status --porcelain -- $PUBLISH_PATHS $OBSOLETE_PUBLIC_PATHS)
  if [ -n "$dirty_paths" ]; then
    echo "The source worktree has uncommitted publish-related changes." >&2
    echo "Commit them first, or rerun with --allow-dirty." >&2
    printf '%s\n' "$dirty_paths" >&2
    exit 1
  fi
fi

if [ "$skip_build" -ne 1 ]; then
  if [ ! -x "$BUILD_SCRIPT" ]; then
    echo "Build script is not executable: $BUILD_SCRIPT" >&2
    exit 1
  fi

  echo "Running: $BUILD_SCRIPT"
  "$BUILD_SCRIPT"

  if [ ! -x "$MD_SCRIPT" ]; then
    echo "Markdown generation script is not executable: $MD_SCRIPT" >&2
    exit 1
  fi

  echo "Running: $MD_SCRIPT"
  "$MD_SCRIPT"
fi

if [ "$require_site_dir" -eq 1 ] && [ ! -d "$SITE_DIR" ]; then
  echo "Generated site directory not found: $SITE_DIR" >&2
  exit 1
fi

tmp_root=$(mktemp -d "${TMPDIR:-/tmp}/lean-math-note-public.XXXXXX")
cleanup() {
  rm -rf "$tmp_root"
}
trap cleanup EXIT HUP INT TERM

public_clone=$tmp_root/public

echo "Cloning public repository: $PUBLIC_REPO_URL"
git clone "$PUBLIC_REPO_URL" "$public_clone"

cd "$public_clone"

if git show-ref --verify --quiet "refs/heads/$PUBLIC_BRANCH"; then
  git checkout "$PUBLIC_BRANCH"
elif git show-ref --verify --quiet "refs/remotes/origin/$PUBLIC_BRANCH"; then
  git checkout -B "$PUBLIC_BRANCH" "origin/$PUBLIC_BRANCH"
else
  git checkout --orphan "$PUBLIC_BRANCH"
  git rm -rf . >/dev/null 2>&1 || true
fi

for path in $PUBLISH_PATHS; do
  if [ ! -e "$repo_root/$path" ]; then
    echo "Expected publish path not found: $path" >&2
    exit 1
  fi

  rm -rf "$path"
  mkdir -p "$(dirname "$path")"
  cp -R "$repo_root/$path" "$path"
done

for path in $OBSOLETE_PUBLIC_PATHS; do
  rm -rf "$path"
  git rm -r --ignore-unmatch -- "$path" >/dev/null
done

git add -A -- $PUBLISH_PATHS

if git diff --cached --quiet; then
  echo "No changes to publish."
  exit 0
fi

echo "Changes to publish:"
git status --short

if [ "$dry_run" -eq 1 ]; then
  echo "Dry run: leaving the public repository unchanged."
  exit 0
fi

git commit -m "$COMMIT_MESSAGE"
git push origin "$PUBLIC_BRANCH"

echo "Published generated site to $PUBLIC_REPO_URL ($PUBLIC_BRANCH)."
