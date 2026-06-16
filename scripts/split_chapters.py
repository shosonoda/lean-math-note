#!/usr/bin/env python3
from __future__ import annotations

import re
import shutil
import sys
from pathlib import Path


CHAPTER_RE = re.compile(r"chapter\d+\.md$")
FENCE_RE = re.compile(r"^\s*```")
HEADING_RE = re.compile(r"^(#{1,6})\s+(.*\S)\s*$")
SPLIT_RE = re.compile(r"^\s*---\s*$")


def split_on_markers(lines: list[str]) -> list[list[str]]:
    pages: list[list[str]] = []
    current: list[str] = []
    in_code = False

    for line in lines:
        if FENCE_RE.match(line):
            in_code = not in_code
            current.append(line)
            continue

        if not in_code and SPLIT_RE.match(line):
            if any(part.strip() for part in current):
                pages.append(trim_blank_edges(current))
            current = []
            continue

        current.append(line)

    if any(part.strip() for part in current):
        pages.append(trim_blank_edges(current))

    return pages


def trim_blank_edges(lines: list[str]) -> list[str]:
    start = 0
    end = len(lines)

    while start < end and lines[start].strip() == "":
        start += 1
    while end > start and lines[end - 1].strip() == "":
        end -= 1

    return lines[start:end]


def first_heading(lines: list[str]) -> tuple[int, int, str] | None:
    for index, line in enumerate(lines):
        match = HEADING_RE.match(line)
        if match:
            return index, len(match.group(1)), match.group(2)
    return None


def promote_headings(lines: list[str]) -> list[str]:
    heading = first_heading(lines)
    if heading is None:
        return ["# Section\n", "\n", *lines]

    first_index, base_level, _title = heading
    if base_level == 1:
        return lines

    promoted: list[str] = []
    for index, line in enumerate(lines):
        match = HEADING_RE.match(line)
        if not match:
            promoted.append(line)
            continue

        level = len(match.group(1))
        if index == first_index:
            level = 1
            promoted.append(f"{'#' * level} {match.group(2)}\n")
        elif level >= base_level:
            level = max(2, level - base_level + 1)
            promoted.append(f"{'#' * level} {match.group(2)}\n")
        else:
            promoted.append(line)

    return promoted


def write_page(path: Path, lines: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = "".join(lines).rstrip() + "\n"
    path.write_text(text, encoding="utf-8")


def copy_static_files(src_dir: Path, dest_dir: Path) -> None:
    for item in src_dir.iterdir():
        if item.name == "old":
            continue
        if item.is_file() and CHAPTER_RE.fullmatch(item.name):
            continue

        target = dest_dir / item.name
        if item.is_dir():
            shutil.copytree(item, target)
        else:
            shutil.copy2(item, target)


def rewrite_index_links(index_path: Path) -> None:
    if not index_path.exists():
        return

    text = index_path.read_text(encoding="utf-8")
    text = re.sub(r"\((chapter\d+)\.md\)", r"(\1/index.md)", text)
    index_path.write_text(text, encoding="utf-8")


def split_chapter(path: Path, dest_dir: Path) -> None:
    chapter_name = path.stem
    chapter_dir = dest_dir / chapter_name
    lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
    pages = split_on_markers(lines)

    if not pages:
        return

    write_page(chapter_dir / "index.md", pages[0])

    for index, page in enumerate(pages[1:], start=1):
        write_page(chapter_dir / f"{index:02d}.md", promote_headings(page))


def main() -> int:
    if len(sys.argv) != 3:
        print("Usage: split_chapters.py <source_dir> <output_dir>", file=sys.stderr)
        return 2

    src_dir = Path(sys.argv[1])
    dest_dir = Path(sys.argv[2])

    if not src_dir.is_dir():
        print(f"Source directory not found: {src_dir}", file=sys.stderr)
        return 1

    if dest_dir.exists():
        shutil.rmtree(dest_dir)
    dest_dir.mkdir(parents=True)

    copy_static_files(src_dir, dest_dir)
    rewrite_index_links(dest_dir / "index.md")

    for chapter in sorted(src_dir.glob("chapter*.md")):
        split_chapter(chapter, dest_dir)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
