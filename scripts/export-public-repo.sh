#!/usr/bin/env sh
set -eu

usage() {
  echo "Usage: $0 [--dry-run] [--skip-build] [--allow-dirty] [public_repo_url_or_path]" >&2
  echo "" >&2
  echo "Builds docs/ in this development repository and publishes it to the public repository." >&2
  echo "" >&2
  echo "Environment variables:" >&2
  echo "  PUBLIC_REPO_URL     Default: https://github.com/shosonoda/lean-math-note.git" >&2
  echo "  PUBLIC_BRANCH       Default: main" >&2
  echo "  SOURCE_BRANCH       Default: main" >&2
  echo "  BUILD_SCRIPT        Default: ./scripts/build-site.sh" >&2
  echo "  COMMIT_MESSAGE      Commit message for the public repository." >&2
  echo "  PUBLIC_REPO_ALLOW_DIRTY=1 permits publishing from a dirty worktree." >&2
}

dry_run=0
skip_build=0
allow_dirty=${PUBLIC_REPO_ALLOW_DIRTY:-0}
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

PUBLIC_REPO_URL=${repo_arg:-${PUBLIC_REPO_URL:-https://github.com/shosonoda/lean-math-note.git}}
PUBLIC_BRANCH=${PUBLIC_BRANCH:-main}
SOURCE_BRANCH=${SOURCE_BRANCH:-main}
BUILD_SCRIPT=${BUILD_SCRIPT:-./scripts/build-site.sh}
SITE_DIR=${SITE_DIR:-docs}
PUBLISH_PATHS="LeanMathNote.lean LeanMathNote lean-toolchain lakefile.toml site-src mkdocs.yml requirements-mkdocs.txt scripts build-site.sh $SITE_DIR"

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

cd "$repo_root"

current_branch=$(git branch --show-current)
if [ "$current_branch" != "$SOURCE_BRANCH" ]; then
  echo "Run this script on $SOURCE_BRANCH. Current branch: $current_branch" >&2
  exit 1
fi

source_commit=$(git rev-parse --short HEAD)
COMMIT_MESSAGE=${COMMIT_MESSAGE:-"Publish site from lean-note-dev ${source_commit}"}

if [ "$allow_dirty" != "1" ]; then
  dirty_paths=$(git status --porcelain -- $PUBLISH_PATHS)
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
fi

if [ ! -d "$SITE_DIR" ]; then
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

git add -A -- $PUBLISH_PATHS

if git diff --cached --quiet; then
  echo "No changes to publish."
  exit 0
fi

echo "Changes to publish:"
git status --short -- $PUBLISH_PATHS

if [ "$dry_run" -eq 1 ]; then
  echo "Dry run: leaving the public repository unchanged."
  exit 0
fi

git commit -m "$COMMIT_MESSAGE"
git push origin "$PUBLIC_BRANCH"

echo "Published generated site to $PUBLIC_REPO_URL ($PUBLIC_BRANCH)."
