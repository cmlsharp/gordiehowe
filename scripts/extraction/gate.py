#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""The identity check between two builds (proofs, plans, bench records).

Run every identity capture on one build in parallel, or compare two gate runs.

`run` drives capture.py (one task per test binary, profile and mode: normal,
seeded-1, seeded-2), capture_benchmarks.py (one task per bench case),
export_plans.py, capture_baselines.py and CTest, then merges each kind into
one file in the output directory:
  suite.json, benchmarks.json, exports.json, baselines.json, ctest.json.
CTest starts first, then the suite runs longest first (by --durations, a
previous gate's suite.json, else by the known slow binaries), then the rest,
so the critical path stays near the slowest single run. Runs matching
--heavy (default the QROM pq_mdoc_test runs) are capped at
--heavy-jobs at once. --quick runs the normal pass and one seeded pass only
(no seeded-2, so no nondeterminism check); compare accepts a --quick
candidate against a full reference and lists the seeded-2 runs it skipped.

An incremental build is fine for `run` after a fresh configure, provided no
test binary moved: a binary left behind by a moved target is a stale
duplicate, which `run` refuses and compare reports.

exports.json hashes every module the exports write, the data modules (Plan,
Program) and the proof modules (Valid, Realize, Honest), each with its provenance
lines masked.

`compare` checks a candidate gate run against a reference gate run and fails
closed on any difference, on a failed task in the candidate's gate.json, and
on shape (compare.py): duplicate targets or runs, and candidate runs without
a reference counterpart other than those of new targets, which it lists
apart. It prints the task, target and run counts of both sides.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import capture  # noqa: E402
import capture_benchmarks  # noqa: E402


def clean_env():
    return {k: v for k, v in os.environ.items()
            if not k.startswith(("GH_", "PQ_", "LFB_")) and k != "NOBE"}


def test_targets(build):
    paths = sorted(p for p in (build / "gordiehowe").rglob("*_test")
                   if p.is_file() and os.access(p, os.X_OK))
    if (build / "random/transcript_test").is_file():
        paths.append(build / "random/transcript_test")
    # Two binaries of one name (a stale one left by a moved target) would
    # run as one task twice; refuse them.
    by_name = {}
    for p in paths:
        by_name.setdefault(p.name, []).append(p.relative_to(build).as_posix())
    clashes = {n: ps for n, ps in by_name.items() if len(ps) > 1}
    if clashes:
        raise SystemExit(f"duplicate test binaries under {build}: {clashes}")
    return sorted(by_name)


def bench_cases():
    names = []
    for profile in ("narrow", "wide"):
        for case in capture_benchmarks.report_cases(profile):
            if case not in names:
                names.append(case)
    # Standalone cases, as capture_benchmarks.main names them.
    names += [f"pq-mdoc-{arm}-{n}" for n in (1, 2, 4) for arm in ("fq", "goldilocks")]
    names += [f"pq-mdoc-{arm}-ablations" for arm in ("fq", "goldilocks")]
    names += ["composite"]
    names += [f"rsa-{field}-{size}" for field in ("narrow", "narrow-fp128") for size in (64, 2048)]
    return names


def run_task(name, command, log, gate=None):
    if gate is not None:
        gate.acquire()
    try:
        with log.open("w") as out:
            code = subprocess.run(command, env=clean_env(), stdout=out,
                                  stderr=subprocess.STDOUT).returncode
    finally:
        if gate is not None:
            gate.release()
    print(f"{name}: exit={code}", flush=True)
    return name, code


# Seconds per suite run of the slowest binaries on a 128-core AMD EPYC 9754
# host, the order when no --durations file is given.
KNOWN_SLOW = {"pq_mdoc_test": 700, "mdoc_signatures_test": 500, "expand_a_test": 180,
              "mldsa_native_test": 165, "rsa_pkcs1_test": 120}


def suite_runs(targets, quick, durations=None):
    """The suite's (target, profile, mode) runs, longest first: by DURATIONS
    {(target, profile, mode): seconds} where known, else KNOWN_SLOW."""
    modes = capture.MODES[:2] if quick else capture.MODES
    runs = [(t, p, m) for t in targets for p in capture.PROFILES for m in modes]

    def seconds(run):
        if durations and run in durations:
            return durations[run]
        return KNOWN_SLOW.get(run[0], 0)
    return sorted(runs, key=lambda r: (-seconds(r), r))


def load_durations(path):
    data = json.loads(Path(path).read_text())
    return {(r["target"], r["profile"], r["mode"]): r.get("elapsed_seconds", 0)
            for r in data["runs"]}


def merge_suite(parts, quick=False):
    merged = {"schema": 1, "targets": {}, "runs": [], "unstable_proof_tests": []}
    for part in parts:
        data = json.loads(part.read_text())
        merged["commit"] = data["commit"]
        merged["targets"].update(data["targets"])
        merged["runs"] += data["runs"]
    merged["runs"].sort(key=lambda r: (r["target"], capture.PROFILES.index(r["profile"]),
                                       capture.MODES.index(r["mode"])))
    # The seeded passes ran as separate tasks: compare them here.
    merged["unstable_proof_tests"] = capture.unstable_tests(merged["runs"])
    merged["normal_runs_passed"] = all(r["exit_code"] == 0 for r in merged["runs"]
                                       if r["mode"] == "normal")
    if quick:
        merged["quick"] = True
    return merged


def merge_benchmarks(parts):
    merged = {"schema": 1, "seed": 7, "runs": [], "complete": True}
    for part in parts:
        data = json.loads(part.read_text())
        merged["commit"] = data["commit"]
        merged["runs"] += data["runs"]
        merged["complete"] &= bool(data.get("complete"))
    return merged


def ctest_results(build, output, jobs):
    log = output / "ctest.log"
    env = dict(clean_env(), GH_THREADS="single")
    with log.open("w") as out:
        code = subprocess.run(["ctest", "--test-dir", str(build), f"-j{jobs}", "--timeout", "5400",
                               "--output-junit", str(output / "ctest.xml")],
                              env=env, stdout=out, stderr=subprocess.STDOUT).returncode
    return dict(parse_ctest(log.read_text(errors="replace")), exit_code=code)


def parse_ctest(text):
    passed = sorted(re.findall(r"Test +#\d+: (\S+) \.+ +Passed", text))
    # The DISABLED_ measurement tests register as tests that CTest does not run.
    disabled = set(re.findall(r"Test +#\d+: (\S+) \.+\**\s*Not Run \(Disabled\)", text))
    failed = sorted(set(re.findall(r"Test +#\d+: (\S+) \.+\**\s*(?:Failed|Not Run|Timeout|"
                                   r"Exception|SEGFAULT|Subprocess aborted|\*\*\*)", text)))
    # Targets whose executables failed to build show up as "Not Run".
    return {"passed": passed,
            "failed": [t for t in failed if t not in disabled], "disabled": sorted(disabled)}


def run(args):
    build = args.build.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    parts = output / "parts"
    parts.mkdir()
    py = sys.executable
    tasks = []
    durations = load_durations(args.durations) if args.durations else None
    heavy = re.compile(args.heavy)
    for target, profile, mode in suite_runs(test_targets(build), args.quick, durations):
        name = f"suite-{target}-{profile}-{mode}"
        tasks.append((name, [py, str(HERE / "capture.py"), "--build", str(build),
                      "--output", str(parts / name), "--commit", args.commit,
                      "--target", target, "--profile", profile, "--mode", mode],
                      bool(heavy.search(f"{target}@{profile}"))))
    for case in bench_cases():
        tasks.append((f"bench-{case}", [py, str(HERE / "capture_benchmarks.py"), "--build",
                      str(build), "--output", str(parts / f"bench-{case}"), "--commit",
                      args.commit, "--case", case], False))
    tasks.append(("exports", [py, str(HERE / "export_plans.py"), "--build", str(build),
                  "--output", str(output / "exports"), "--commit", args.commit], False))
    if args.baseline_build:
        tasks.append(("baselines", [py, str(HERE / "capture_baselines.py"), "--build",
                      str(args.baseline_build.resolve()), "--output", str(output / "baselines"),
                      "--commit", args.baseline_commit], False))
    if args.only:
        tasks = [t for t in tasks if re.search(args.only, t[0])]
    logs = output / "logs"
    logs.mkdir()
    heavy_gate = threading.Semaphore(args.heavy_jobs)
    with ThreadPoolExecutor(args.jobs) as pool:
        futures = []
        # CTest first: it is one long task.
        if not args.only and not args.skip_ctest:
            futures.append(pool.submit(lambda: ("ctest", ctest_results(build, output, args.ctest_jobs))))
        futures += [pool.submit(run_task, name, cmd, logs / f"{name}.log",
                                heavy_gate if is_heavy else None)
                    for name, cmd, is_heavy in tasks]
        results = [f.result() for f in futures]
    summary = {"commit": args.commit, "build": str(build), "tasks": {}}
    for name, value in results:
        if name == "ctest":
            (output / "ctest.json").write_text(json.dumps(value, indent=2) + "\n")
        else:
            summary["tasks"][name] = value
    suite = sorted(parts.glob("suite-*/capture.json"))
    if suite:
        (output / "suite.json").write_text(json.dumps(merge_suite(suite, args.quick), indent=2) + "\n")
    bench = sorted(parts.glob("bench-*/benchmarks.json"))
    if bench:
        (output / "benchmarks.json").write_text(json.dumps(merge_benchmarks(bench), indent=2) + "\n")
    if (output / "exports/exports.json").is_file():
        (output / "exports.json").write_text((output / "exports/exports.json").read_text())
    if (output / "baselines/baselines.json").is_file():
        (output / "baselines.json").write_text((output / "baselines/baselines.json").read_text())
    (output / "gate.json").write_text(json.dumps(summary, indent=2) + "\n")
    failed = [n for n, c in summary["tasks"].items() if c]
    print(json.dumps({"failed_tasks": failed}, indent=2))
    return 1 if failed else 0


def compare_baselines(a, b):
    differences, count = [], 0
    if not (a.get("complete") and b.get("complete")):
        differences.append("baseline capture incomplete")
    for side, d in (("reference", a), ("candidate", b)):
        keys = [(r["profile"], r["case"]) for r in d["runs"]]
        differences += [f"duplicate baseline in {side}: {k}"
                        for k in sorted(set(k for k in keys if keys.count(k) > 1))]
    left, right = ({(r["profile"], r["case"]): r for r in d["runs"]} for d in (a, b))
    for key in sorted(set(left) | set(right)):
        if key not in left or key not in right:
            differences.append(f"missing baseline: {key}")
            continue
        x, y = left[key], right[key]
        if not (x["verified"] and y["verified"]):
            differences.append(f"unverified baseline: {key}")
        count += len(y["proof_bytes"])
        if x["proof_digests"] or y["proof_digests"]:
            # Seeded baselines: exact digests and sizes.
            if (x["proof_digests"], x["proof_bytes"]) != (y["proof_digests"], y["proof_bytes"]):
                differences.append(f"changed baseline proofs: {key}")
        elif len(x["proof_bytes"]) != len(y["proof_bytes"]):
            differences.append(f"changed baseline proof count: {key}")
    return count, differences


def failed_tasks(gate):
    """The failed tasks a gate.json records: nonzero exit codes, and any
    failed_tasks list."""
    tasks = gate.get("tasks", {})
    return sorted(set(gate.get("failed_tasks", [])) | {n for n, c in tasks.items() if c})


def compare(args):
    ref, cand = args.reference.resolve(), args.candidate.resolve()
    report = {}
    status = 0
    for side, d in (("reference", ref), ("candidate", cand)):
        if not (d / "gate.json").is_file():
            report["gate.json"] = {"differences": [f"{side} has no gate.json"]}
            status = 1
    if not status:
        gates = {side: json.loads((d / "gate.json").read_text())
                 for side, d in (("reference", ref), ("candidate", cand))}
        failed = failed_tasks(gates["candidate"])
        report["gate.json"] = {
            "tasks": {side: len(g.get("tasks", {})) for side, g in gates.items()},
            "reference_failed_tasks": failed_tasks(gates["reference"]),
            "differences": [f"candidate task failed: {n}" for n in failed]}
        status |= bool(failed)
    for name in ("suite.json", "benchmarks.json", "exports.json"):
        if not (ref / name).is_file() or not (cand / name).is_file():
            report[name] = {"differences": ["missing"]}
            status = 1
            continue
        command = [sys.executable, str(HERE / "compare.py"), str(ref / name), str(cand / name)]
        if name == "exports.json" and args.allow_added_modules:
            # A reference from before the exporter wrote the proof modules.
            command += ["--allow-added", r"/(Valid|Realize|Honest)\.lean$"]
        result = subprocess.run(command, capture_output=True, text=True)
        report[name] = json.loads(result.stdout)
        status |= result.returncode
    if (ref / "baselines.json").is_file() or (cand / "baselines.json").is_file():
        a, b = (json.loads((d / "baselines.json").read_text()) for d in (ref, cand))
        count, diffs = compare_baselines(a, b)
        report["baselines.json"] = {"compared": count, "differences": diffs}
        status |= bool(diffs)
    if (ref / "ctest.json").is_file() and (cand / "ctest.json").is_file():
        a, b = (json.loads((d / "ctest.json").read_text()) for d in (ref, cand))
        # A reference build may register tests the candidate does not;
        # compare the outcome of every test the candidate registers.
        def outcomes(d):
            disabled = set(d.get("disabled", []))
            return {**{t: "passed" for t in d["passed"]},
                    **{t: "failed" for t in d["failed"] if t not in disabled}}
        outcome_a, outcome_b = outcomes(a), outcomes(b)
        diffs = [f"{t}: reference {outcome_a.get(t, 'absent')}, candidate {o}"
                 for t, o in sorted(outcome_b.items()) if outcome_a.get(t) != o]
        report["ctest.json"] = {"compared": len(outcome_b), "differences": diffs,
                                "candidate_failed": b["failed"],
                                "reference_only": len(set(outcome_a) - set(outcome_b))}
        status |= bool(diffs)
    print(json.dumps(report, indent=2))
    return status


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    r = sub.add_parser("run", description=(
        "Every identity capture on one build, one task per suite run, longest first. "
        "An incremental build is fine after a fresh configure, provided no test binary "
        "moved: a stale binary left by a move is refused as a duplicate. --quick drops "
        "the seeded-2 pass; compare accepts such a candidate against a full reference."))
    r.add_argument("--build", type=Path, required=True)
    r.add_argument("--output", type=Path, required=True)
    r.add_argument("--commit", required=True)
    r.add_argument("--baseline-build", type=Path)
    r.add_argument("--baseline-commit", default="f47f3657bd20e7c3401be846bdc5d78120cbb51a")
    r.add_argument("--jobs", type=int, default=24)
    r.add_argument("--only", help="Regex over task names")
    r.add_argument("--skip-ctest", action="store_true")
    r.add_argument("--quick", action="store_true",
                   help="The normal pass and one seeded pass only (no seeded-2)")
    r.add_argument("--durations", type=Path,
                   help="A previous gate's suite.json: its run times order the suite runs")
    r.add_argument("--heavy", default=r"^pq_mdoc_test@wide$",
                   help="Regex over TARGET@PROFILE of the runs --heavy-jobs caps")
    r.add_argument("--heavy-jobs", type=int, default=3,
                   help="Heavy runs at once")
    r.add_argument("--ctest-jobs", type=int, default=8)
    c = sub.add_parser("compare")
    c.add_argument("reference", type=Path)
    c.add_argument("candidate", type=Path)
    c.add_argument("--allow-added-modules", action="store_true",
                   help="Accept proof modules (Valid.lean, Realize.lean, Honest.lean) that "
                        "only the candidate's exports hold, for a reference gated before the "
                        "exporter wrote them; every other export must still match")
    args = parser.parse_args()
    return run(args) if args.command == "run" else compare(args)


if __name__ == "__main__":
    raise SystemExit(main())
