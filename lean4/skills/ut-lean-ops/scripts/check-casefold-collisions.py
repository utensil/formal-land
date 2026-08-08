#!/usr/bin/env python3
"""Reject a Git tree that cannot be represented by this worktree."""

import subprocess
import sys


def main() -> int:
    if len(sys.argv) != 2:
        print(f"usage: {sys.argv[0]} <target-revision>", file=sys.stderr)
        return 2

    ignore_case = subprocess.run(
        ["git", "config", "--bool", "--get", "core.ignorecase"],
        check=False,
        stdout=subprocess.PIPE,
        text=True,
    ).stdout.strip()
    if ignore_case != "true":
        return 0

    tree = subprocess.check_output(
        [
            "git",
            "rev-parse",
            "--verify",
            "--end-of-options",
            f"{sys.argv[1]}^{{tree}}",
        ]
    ).strip()
    paths = subprocess.check_output(
        ["git", "ls-tree", "-r", "-t", "-z", "--name-only", tree.decode("ascii")]
    )

    seen = {}
    collisions = []
    for raw_path in paths.split(b"\0"):
        if not raw_path:
            continue
        path = raw_path.decode("utf-8", "surrogateescape")
        folded = path.casefold()
        previous = seen.setdefault(folded, path)
        if previous != path:
            collisions.append((previous, path))

    if not collisions:
        return 0

    print(
        f"error: {sys.argv[1]} contains case-folded path collisions:",
        file=sys.stderr,
    )
    for left, right in collisions:
        print(f"  {left}\n  {right}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
