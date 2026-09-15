#!/usr/bin/env python3
"""Refresh all labeled GeometricTopology PRs and retain previously recorded history."""
import argparse
import concurrent.futures
import datetime as dt
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
REPO = "TauCetiProject/TauCeti"


def api(path):
    for attempt in range(3):
        try:
            result = subprocess.run(["gh", "api", path], capture_output=True, text=True, timeout=60)
        except subprocess.TimeoutExpired:
            result = None
        if result is not None and not result.returncode:
            return json.loads(result.stdout)
        transient = result is None or re.search(r"HTTP (?:5\d\d|429)|connection|timeout|TLS", result.stderr, re.I)
        if not transient or attempt == 2:
            raise RuntimeError(f"GitHub request failed: {path.split('?')[0]}")
        time.sleep(attempt + 1)


def utc_timestamp(value):
    """Keep source instants timezone-aware and serialize them in UTC."""
    if value is None:
        return None
    instant = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    if instant.tzinfo is None:
        raise ValueError("Timestamp must have an explicit timezone")
    return instant.astimezone(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def pages(path):
    result = []
    for page in range(1, 101):
        batch = api(f"{path}?per_page=100&page={page}")
        if not isinstance(batch, list):
            raise ValueError("Expected a paginated array")
        result.extend(batch)
        if len(batch) < 100:
            return result
    raise RuntimeError("Pagination limit reached; snapshot was not changed")


def merge_observations(previous, fresh):
    """Keep observations from overwritten public comments, without repeated rows."""
    unique = {json.dumps(row, sort_keys=True): row for row in previous + fresh}
    return sorted(unique.values(), key=lambda row: (row.get("at", row.get("updated_at", "")), json.dumps(row, sort_keys=True)))


def clean_title(value):
    return re.sub(r"[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}", "[redacted]", value)


def collect(number, previous):
    base = f"repos/{REPO}"
    pr = api(f"{base}/pulls/{number}")
    comments = pages(f"{base}/issues/{number}/comments")
    events = pages(f"{base}/issues/{number}/events")
    boards, reviews = [], []
    for comment in comments:
        match = re.search(r"<!--tauceti-meta:v1 (.*?)-->", comment.get("body", ""), re.S)
        if not match:
            continue
        try:
            meta = json.loads(match.group(1))
        except ValueError:
            continue
        if meta.get("states"):
            boards.append({"head": meta.get("head_sha"), "round": meta.get("round"),
                           "states": meta["states"], "updated_at": utc_timestamp(comment["updated_at"]),
                           "url": comment["html_url"]})
        for run in meta.get("runs", []):
            reviews.append({"kind": "review", "at": utc_timestamp(meta.get("ts") or comment["updated_at"]),
                            "head": meta.get("head_sha"), "round": meta.get("round"),
                            "rubric": run.get("rubric") or meta.get("rubric"),
                            "verdict": run.get("verdict"), "url": comment["html_url"]})
    lifecycle = []
    for event in events:
        if event["event"] not in {"labeled", "unlabeled", "closed", "reopened", "merged", "ready_for_review", "convert_to_draft"}:
            continue
        lifecycle.append({"kind": event["event"], "at": utc_timestamp(event["created_at"]),
                          "label": (event.get("label") or {}).get("name"), "url": pr["html_url"]})
    checks = []
    for page in range(1, 101):
        batch = api(f"{base}/commits/{pr['head']['sha']}/check-runs?per_page=100&page={page}")
        checks.extend({"name": check["name"], "status": check["status"],
                       "conclusion": check["conclusion"], "url": check["html_url"],
                       "started_at": utc_timestamp(check["started_at"]),
                       "completed_at": utc_timestamp(check["completed_at"])} for check in batch["check_runs"])
        if len(checks) >= batch["total_count"]:
            break
    else:
        raise RuntimeError("Check-run pagination limit reached; snapshot was not changed")
    # An exact-head snapshot cannot combine metadata from before and after a push.
    latest = api(f"{base}/pulls/{number}")
    if (pr["head"]["sha"], pr["state"], pr["merged_at"]) != (latest["head"]["sha"], latest["state"], latest["merged_at"]):
        raise RuntimeError(f"PR #{number} changed during collection; retry the refresh")
    return {
        "number": number, "title": clean_title(pr["title"]), "url": pr["html_url"],
        "author": pr["user"]["login"], "head": pr["head"]["sha"],
        "state": "merged" if pr["merged_at"] else "draft" if pr["draft"] and pr["state"] == "open" else pr["state"],
        **{key: utc_timestamp(pr[key]) for key in ("created_at", "updated_at", "closed_at", "merged_at")},
        "labels": sorted(label["name"] for label in pr["labels"]),
        "review_boards": merge_observations(previous.get("review_boards", []), boards),
        "review_events": merge_observations(previous.get("review_events", []), reviews),
        "events": merge_observations(previous.get("events", []), lifecycle),
        "checks": checks,
    }


ROADMAP_LABEL = "roadmap/GeometricTopology"


def discover():
    """Paginate every state; never publish a truncated search inventory."""
    query = f"search/issues?q=repo%3A{REPO}%20is%3Apr%20label%3Aroadmap%2FGeometricTopology&per_page=100"
    found = {}
    expected = None
    for page in range(1, 11):
        result = api(f"{query}&page={page}")
        total = result["total_count"]
        if result.get("incomplete_results") or total > 1000:
            raise RuntimeError("Discovery result incomplete; snapshot was not changed")
        if expected is not None and expected != total:
            raise RuntimeError("Discovery changed during pagination; retry the refresh")
        expected = total
        for item in result["items"]:
            found[item["number"]] = item
        if len(found) == total:
            return found
        if len(result["items"]) < 100:
            break
    raise RuntimeError("Discovery pagination incomplete; snapshot was not changed")


def refresh_snapshot(selection, previous, discovered, refresh_all=False):
    cached = {pr["number"]: pr for pr in previous["prs"]}
    mapped = {item["number"] for item in selection}
    # Historical records survive closure, label removal and annotation edits.
    numbers = set(cached) | mapped | set(discovered)
    todo = sorted(n for n in numbers if refresh_all or n not in cached or
                  cached[n]["state"] not in {"merged", "closed"} or
                  (n in discovered and utc_timestamp(discovered[n]["updated_at"]) !=
                   utc_timestamp(cached[n]["updated_at"])))
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        fresh = list(pool.map(lambda n: collect(n, cached.get(n, {})), todo))
    cached.update({pr["number"]: pr for pr in fresh})
    return {"collected_at": utc_timestamp(dt.datetime.now(dt.timezone.utc).isoformat()),
            "coverage": {"label": ROADMAP_LABEL, "discovered": sorted(discovered),
                         "retained": sorted(numbers - set(discovered))},
            "prs": [cached[n] for n in sorted(numbers)]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true", help="also refresh unchanged terminal evidence")
    parser.add_argument("--discover", action="store_true", help="list labeled PRs without milestone mappings")
    args = parser.parse_args()
    selection = json.loads((ROOT / "data/selection.json").read_text())
    discovered = discover()
    if args.discover:
        mapped = {item["number"] for item in selection}
        for number in sorted(set(discovered) - mapped):
            item = discovered[number]
            print(f"#{number} {item['state']} {clean_title(item['title'])}")
        return
    path = ROOT / "data/prs.json"
    previous = json.loads(path.read_text()) if path.exists() else {"prs": []}
    snapshot = refresh_snapshot(selection, previous, discovered, args.all)
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(snapshot, ensure_ascii=False, indent=2) + "\n")
    temporary.replace(path)
    print(f"Collected {len(snapshot['prs'])} PRs: {len(discovered)} labeled, "
          f"{len(snapshot['coverage']['retained'])} retained historical records. Run python3 geotopo/build.py.")


if __name__ == "__main__":
    main()
