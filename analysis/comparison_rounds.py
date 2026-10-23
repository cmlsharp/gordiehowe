#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""The round errors of a hash-comparison proof (SHA3-256 or SHA-256 batched, one domain H) from its
plan export alone, with plan_rounds.py's charges (each GKR round its own error).

Usage: comparison_rounds.py PLAN.lean [PLAN.lean ...] [--run-log RUN_LOG] [--json FILE] [--notes]

The plan gives the tableau (N, k, t, ldt_reps, masking), the batches, the circuit shape and the
field (plan_rounds.parse_plan, program_from_plan). A and B are the run's PQ_PARAMS record's when
--run-log has a record of the plan's configuration at the plan's tableau, else the screen's choice
at the profile's target (screen_run.lr_rounds; A belongs to the soundness argument). The run's
record of a plan is that of a single-threaded worker whose configuration is the plan's bench
configuration (run_config: the sha3 preset's records are keccak-sha3-batched at every message
length) and whose tableaus, masking and circuit shapes equal the plan's (plan_rounds.plan_mismatch).
Each row lists every round (plan_rounds.case_errors' rounds, in bits), the per-round maximum
(round_max) and its binding round, as eval_params.py's rows do, and the matched worker
(run_record, null without one).

--notes prints, in place of the JSON, one line per row whose round_max exceeds its target and per
row without a matching run record (notes), as run_bench.sh records them in manifest.txt.
"""
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import plan_rounds as pr  # noqa: E402
import screen_run as sr  # noqa: E402


def run_records(log_text):
    """<config>-<profile> -> worker -> half -> PQ_PARAMS record, single-threaded workers only (a
    configuration run at several sizes has one worker per size)."""
    out = {}
    for line in log_text.splitlines():
        m = re.match(r"\[([^]@]+)\] PQ_PARAMS (.*)", line)
        if m:
            e = json.loads(m.group(2))
            out.setdefault(f"{e['config']}-{e['profile']}", {}).setdefault(
                m.group(1), {})[e["half"]] = e
    return out


# Plan configurations whose bench records carry another name: the sha3 preset's exports are
# sha3-256-batched-<size> and its bench records keccak-sha3-batched (keccak_compare_test.cc).
RUN_CONFIGS = ((re.compile(r"^sha3-256-batched-.+-(narrow|wide)$"), r"keccak-sha3-batched-\1"),)


def run_config(cfg):
    """The bench configuration (with its profile) of the plan configuration CFG."""
    for pattern, repl in RUN_CONFIGS:
        if pattern.match(cfg):
            return pattern.sub(repl, cfg)
    return cfg


def match_record(plan, records):
    """(worker, half -> record) of the run's worker of PLAN's bench configuration whose records
    match PLAN's tableaus (plan_rounds.plan_mismatch), else (None, None)."""
    for worker, recs in sorted(records.get(run_config(plan["head"]["config"]), {}).items()):
        if pr.plan_mismatch(plan, recs) is None:
            return worker, recs
    return None, None


def evaluate(path, records):
    text = Path(path).read_text()
    plan = pr.parse_plan(text)
    prog = pr.program_from_plan(text)
    cfg = plan["head"]["config"]
    profile = next(p for p in ("narrow", "wide") if cfg.endswith("-" + p))
    target = sr.DEFAULT_TARGETS[profile]["default"]
    worker, recs = match_record(plan, records)
    matched = recs is not None
    ligero, tabs = {}, {}
    for name, d in plan["domains"].items():
        masking = "split" if d["masking"] == "split" else "untested"
        if matched and recs[name]["half_params"]["ligero"].get("A"):
            lg = recs[name]["half_params"]["ligero"]
            A, B, source = lg["A"], lg["exceptions"], "run record"
        else:
            _, A, B, found = sr.lr_rounds(d["N"], d["k"], d["t"], d["F"], masking, target,
                                          d["ldt_reps"])
            if not found:
                raise SystemExit(f"{cfg} {name}: no A meets the target {target}")
            source = "screen"
        ligero[name] = dict(sr.ligero_errors(d["N"], d["k"], d["t"], d["F"], A, B, masking,
                                             d["ldt_reps"]), F=d["F"], masking=masking)
        tabs[name] = dict(field=d["field"], N=d["N"], k=d["k"], t=d["t"], ldt_reps=d["ldt_reps"],
                          masking=masking, A=A, B=B, A_B_source=source,
                          circuit=d["circuit"], inputs=d["inputs"])
    errs = pr.case_errors(plan, prog, ligero)
    rounds = {key: round(sr.bits(v), 4) for key, v in errs["rounds"].items()}
    v, key = pr.worst(errs["rounds"])
    gkr = {n: {k2: (round(sr.bits(x), 4) if k2 in ("initial", "layer", "sumcheck_even",
                                                     "sumcheck_odd", "input", "round_max", "sum")
                    else x) for k2, x in d["gkr"].items()}
           for n, d in errs["domains"].items() if "gkr" in d}
    return {"config": cfg, "plan": str(path), "plan_run": plan["head"]["runId"],
            "plan_commit": plan["head"]["cppCommit"], "target": target,
            "run_record_matches_plan": matched, "run_record": worker, "tableaux": tabs,
            "round_max": {"bits": round(sr.bits(v), 4), "binding": key},
            "rounds": dict(sorted(rounds.items(), key=lambda kv: kv[1])), "gkr": gkr}


def notes(rows):
    """The rows' notes: a round_max above the row's per-round target, a plan without a matching
    run record."""
    out = []
    for row in rows:
        rm = row["round_max"]
        if rm["bits"] < row["target"]:
            out.append(f"hash rounds: {row['config']} round_max 2^-{rm['bits']} "
                       f"({rm['binding']}) above the per-round target 2^-{row['target']}")
        if not row["run_record_matches_plan"]:
            out.append(f"hash rounds: {row['config']} has no run record matching its plan")
    return out


def main(argv):
    plans, log, out, want_notes = [], None, None, False
    while argv:
        a = argv.pop(0)
        if a == "--run-log" and argv:
            log = Path(argv.pop(0))
        elif a == "--json" and argv:
            out = Path(argv.pop(0))
        elif a == "--notes":
            want_notes = True
        else:
            plans.append(a)
    if not plans:
        raise SystemExit(__doc__)
    records = run_records(log.read_text()) if log else {}
    rows = [evaluate(p, records) for p in plans]
    text = json.dumps({"rows": rows}, indent=1) + "\n"
    if out:
        out.write_text(text)
    if want_notes:
        for line in notes(rows):
            print(line)
    else:
        print(text, end="")


if __name__ == "__main__":
    main(sys.argv[1:])
