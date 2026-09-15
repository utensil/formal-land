#!/usr/bin/env python3
"""Validate route data and regenerate the single-file, offline explorer."""
import argparse
import datetime as dt
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
HIGH_IMPACT = {"scope", "api-design", "generality", "reuse", "proof-quality"}
UNASSESSED = {"pending", "running", "not_run", "skipped", "absent", "stale"}


def health(pr, scope_reset=0):
    """The SpinRep public-review churn formula, evaluated on preserved evidence."""
    boards = pr["review_boards"]
    exact = [board for board in boards if board["head"] == pr["head"]]
    current = max(exact, key=lambda board: board["updated_at"]) if exact else None
    bad_pairs, block_pairs = set(), set()
    rounds = []
    for board in boards:
        if isinstance(board.get("round"), int):
            rounds.append(board["round"])
        for rubric, state in board["states"].items():
            if state not in {"green"} | UNASSESSED:
                bad_pairs.add((rubric, board.get("round")))
            if state in {"blocking_block", "block"}:
                block_pairs.add((rubric, board.get("round")))
    for event in pr["review_events"]:
        if isinstance(event.get("round"), int):
            rounds.append(event["round"])
        if event.get("rubric") and event.get("verdict") in {"request_changes", "block", "error"}:
            pair = (event["rubric"], event.get("round"))
            bad_pairs.add(pair)
            if event["verdict"] == "block":
                block_pairs.add(pair)
    failed = {rubric for rubric, _ in bad_pairs}
    # As in SpinRep: one L penalty per rubric that is non-green in multiple rounds.
    repeated = sum(len({r for rubric, r in bad_pairs if rubric == name and r is not None}) >= 2 for name in failed)
    terms = {"A": max(0, max(rounds, default=1) - 1), "D": len(failed),
             "H": len(failed & HIGH_IMPACT), "L": repeated, "B": len(block_pairs),
             "S": scope_reset, "U": sum(state != "green" for state in current["states"].values()) if current else None}
    # Missing or partial exact-head evidence must never become a perfect health score.
    complete = current and len(current["states"]) >= 10 and all(state not in UNASSESSED for state in current["states"].values())
    score = max(0, 100 - sum(terms[k] * w for k, w in {"A": 3, "D": 4, "H": 3, "L": 6, "B": 8, "S": 12, "U": 5}.items())) if complete else None
    return {"score": score, "terms": terms, "failed": sorted(failed), "exactHead": bool(current),
            "source": current["url"] if current else None,
            "reason": None if complete else "No complete scoreboard for the snapshot PR head"}


def validate(roadmap, selection, snapshot):
    assert roadmap["timezone"] == "UTC" and roadmap["timeDisplay"] == "browser-local", "UTC data and browser-local display required"
    def check_utc(value):
        if value is not None:
            instant = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
            assert instant.tzinfo is not None and instant.utcoffset() == dt.timedelta(0), "Source timestamps must be UTC"
    check_utc(roadmap["contextAsOf"])
    check_utc(snapshot["collected_at"])
    for pr in snapshot["prs"]:
        for key in ("created_at", "updated_at", "closed_at", "merged_at"):
            check_utc(pr.get(key))
        for key in ("review_boards", "review_events", "events", "checks"):
            for event in pr.get(key, []):
                for field in ("at", "updated_at", "started_at", "completed_at"):
                    if field in event:
                        check_utc(event[field])
    nodes = {node["id"]: node for node in roadmap["nodes"]}
    rows = {row["id"]: i for i, row in enumerate(roadmap["rows"])}
    assert len(nodes) == len(roadmap["nodes"]), "Duplicate milestone ID"
    assert all(node["row"] in rows for node in nodes.values()), "Unknown row"
    for node in nodes.values():
        if node.get("kind") == "proof" and node["status"] == "done":
            assert node.get("completionEvidence", "").startswith("https://github.com/"), "A completed proof needs explicit source evidence"
    assert {node["layer"] for node in nodes.values()} == {f"L{i}" for i in range(1, 12)}, "Missing roadmap layer"
    edges = {edge["id"]: edge for edge in roadmap["edges"]}
    assert len(edges) == len(roadmap["edges"]), "Duplicate edge ID"
    adjacency = {node: [] for node in nodes}
    for edge in edges.values():
        a, b = edge["fromNode"], edge["toNode"]
        assert a in nodes and b in nodes, "Unknown dependency endpoint"
        assert rows[nodes[a]["row"]] <= rows[nodes[b]["row"]], "An edge travels upward"
        assert edge["source"].startswith("https://github.com/"), "Missing dependency source"
        adjacency[a].append(b)
    visiting, visited = set(), set()
    def visit(node):
        assert node not in visiting, "Dependency cycle"
        if node in visited:
            return
        visiting.add(node)
        for target in adjacency[node]:
            visit(target)
        visiting.remove(node)
        visited.add(node)
    for node in nodes:
        visit(node)
    for route in roadmap["routes"]:
        assert route["summits"] and all(summit in nodes for summit in route["summits"])
        assert all(nodes[summit].get("kind") == "proof" for summit in route["summits"]), "A proof summit must be a proof milestone"
        route_nodes = {endpoint for edge_id in route["edges"] for endpoint in (edges[edge_id]["fromNode"], edges[edge_id]["toNode"])}
        assert route["checkpoints"] and route["finish"], "Goal needs checkpoints and a completion criterion"
        for checkpoint in route["checkpoints"]:
            assert checkpoint["nodes"] and all(node in route_nodes for node in checkpoint["nodes"]), "Checkpoint lies outside its route"
        assert all(edge in edges for edge in route["edges"]), "Route is not a dependency subgraph"
        assert all(node in nodes for node in route["frontier"])
        leaves = set()
        branches = []
        def check_tree(branch):
            assert branch["nodes"] and all(node in route_nodes for node in branch["nodes"]), "Tree node lies outside its route"
            branches.append(len(branch["children"]))
            if not branch["children"]:
                leaves.update(branch["nodes"])
            for child in branch["children"]:
                check_tree(child)
        check_tree(route["tree"])
        assert max(branches) >= 2, "A route tree must branch"
        assert set(route["summits"]) <= leaves, "Every proof summit must appear as a tree leaf"
    ids = [entry["number"] for entry in selection]
    assert len(ids) == len(set(ids)), "Duplicate selected PR"
    for entry in selection:
        assert entry["worked"] or entry["reviewed"], "Unrelated PR in selected cohort"
        assert entry["nodes"] and all(node in nodes for node in entry["nodes"]), "Map every selected PR to a milestone"
        assert not entry["reviewed"] or entry["reviewEvidence"], "Reviewed marker needs evidence"
    assert set(ids) <= {pr["number"] for pr in snapshot["prs"]}, "Refresh the snapshot after changing selection"
    snapshot_ids = {pr["number"] for pr in snapshot["prs"]}
    assert len(snapshot_ids) == len(snapshot["prs"]), "Duplicate snapshot PR"
    coverage = snapshot.get("coverage")
    if coverage:
        assert coverage["label"] == "roadmap/GeometricTopology", "Wrong roadmap inventory"
        assert set(coverage["discovered"]) | set(coverage["retained"]) == snapshot_ids, "Incomplete roadmap inventory"


def generate():
    roadmap = json.loads((ROOT / "data/roadmap.json").read_text())
    selection = json.loads((ROOT / "data/selection.json").read_text())
    snapshot = json.loads((ROOT / "data/prs.json").read_text())
    validate(roadmap, selection, snapshot)
    selected = {item["number"]: item for item in selection}
    prs = []
    for pr in snapshot["prs"]:
        annotation = selected.get(pr["number"], {"nodes": [], "worked": False, "reviewed": False,
                                                   "reviewEvidence": [], "scopeReset": 0})
        prs.append({**pr, **annotation, "health": health(pr, annotation["scopeReset"])})
    data = {"roadmap": roadmap, "collected_at": snapshot["collected_at"], "coverage": snapshot.get("coverage", {}), "prs": prs}
    encoded = json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("<", "\\u003c").replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")
    result = (ROOT / "src/page.html").read_text().replace("/*__STYLE__*/", (ROOT / "src/style.css").read_text()).replace("/*__DATA__*/", encoded).replace("/*__TIME__*/", (ROOT / "src/time.js").read_text()).replace("/*__APP__*/", (ROOT / "src/app.js").read_text())
    assert not re.search(r"(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|/Users/|[\w.+-]+@[\w.-]+\.[A-Za-z]{2,})", result), "Private data in generated page"
    assert "/*__" not in result, "Unexpanded template marker"
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail when the committed HTML differs from its inputs")
    args = parser.parse_args()
    result = generate()
    path = ROOT / "geotopo-route-map.html"
    if args.check:
        assert path.read_text() == result, "Generated HTML is stale; run python3 geotopo/build.py"
        print("Validated data and deterministic standalone HTML")
    else:
        path.write_text(result)
        print(f"Built {path.name}: {len(result.encode()):,} bytes")


if __name__ == "__main__":
    main()
