#!/usr/bin/env python3
"""Validate a Markdown ut-lean-review scoreboard against RUBRICS.md."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ALLOWED_VERDICTS = {"approve", "request_changes", "block"}
PLACEHOLDERS = {"", "replace", "todo", "tbd", "n/a"}
METADATA = ("Reviewed", "Subject", "Base", "Head", "Reviewer")


def is_placeholder(value: str) -> bool:
    normalized = value.strip().lower()
    return (
        normalized in PLACEHOLDERS
        or "yyyy-mm-dd" in normalized
        or normalized.startswith("pr number or pre-pr")
        or normalized.startswith("exact base commit")
        or normalized.startswith("exact reviewed commit")
        or normalized.startswith("independent reviewer identity")
    )


def split_row(line: str) -> list[str]:
    cells = re.split(r"(?<!\\)\|", line.strip().strip("|"))
    return [cell.replace(r"\|", "|").strip().strip("`") for cell in cells]


def registry_ids(path: Path) -> list[str]:
    ids: list[str] = []
    for line in path.read_text().splitlines():
        cells = split_row(line) if line.lstrip().startswith("|") else []
        if len(cells) == 3 and re.fullmatch(r"[a-z][a-z0-9-]*", cells[0]):
            ids.append(cells[0])
    if not ids:
        raise ValueError(f"no rubric ids found in {path}")
    return ids


def evidence_rows(text: str) -> list[tuple[str, str, str, str]]:
    rows = []
    for line in text.splitlines():
        if not line.lstrip().startswith("|"):
            continue
        cells = split_row(line)
        if len(cells) != 4 or cells[0] in {"rubric id", "---"}:
            continue
        if re.fullmatch(r"[a-z][a-z0-9-]*", cells[0]):
            rows.append(tuple(cells))
    return rows


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print("usage: validate-review-evidence.py REVIEW.md [RUBRICS.md]", file=sys.stderr)
        return 2
    review = Path(sys.argv[1])
    registry = Path(sys.argv[2]) if len(sys.argv) == 3 else Path(__file__).parent.parent / "RUBRICS.md"
    text = review.read_text()
    required = registry_ids(registry)
    rows = evidence_rows(text)
    errors: list[str] = []

    for key in METADATA:
        match = re.search(rf"^- {re.escape(key)}:\s*(.+)$", text, re.MULTILINE)
        if not match or is_placeholder(match.group(1)):
            errors.append(f"missing or placeholder metadata: {key}")

    seen: dict[str, int] = {}
    for rubric, verdict, evidence, comment in rows:
        seen[rubric] = seen.get(rubric, 0) + 1
        if verdict not in ALLOWED_VERDICTS:
            errors.append(f"{rubric}: invalid verdict {verdict!r}")
        elif verdict != "approve":
            errors.append(f"{rubric}: non-passing verdict {verdict!r}")
        if is_placeholder(evidence):
            errors.append(f"{rubric}: missing concrete evidence")
        if is_placeholder(comment):
            errors.append(f"{rubric}: missing reviewer comment")

    missing = [rubric for rubric in required if rubric not in seen]
    duplicate = [rubric for rubric, count in seen.items() if count > 1]
    unknown = [rubric for rubric in seen if rubric not in required]
    if missing:
        errors.append("missing rubric ids: " + ", ".join(missing))
    if duplicate:
        errors.append("duplicate rubric ids: " + ", ".join(duplicate))
    if unknown:
        errors.append("unknown rubric ids: " + ", ".join(unknown))

    if errors:
        for error in errors:
            print(f"REVIEW-EVIDENCE: FAIL — {error}", file=sys.stderr)
        return 1
    print(f"REVIEW-EVIDENCE: PASS — {len(required)} rubric verdicts approved")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
