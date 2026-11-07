#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Compare a statement closure with the audit ledger; a stale row or a new unrecorded declaration
fails the check.

A row is stale when its declaration is in the closure and its recorded fingerprint differs from
the closure's. A closure declaration with no ledger row must be listed in the baseline of
unrecorded declarations (`--baseline`, audit/unrecorded.txt); one that is not is new to the
statement surface and fails until it is audited and recorded. Baseline names that are recorded or
no longer in the closure, rows without a fingerprint and rows no longer in the closure are
reported and do not fail (audit/README.md).

`--write-baseline` rewrites the baseline as the closure's unrecorded declarations that it already
lists, so it only shrinks; with `--accept-new` it also adds the new unrecorded declarations (an
audit deferred, visible in the baseline's diff). Run it on the full closure,
audit/statement_closure.txt as `check.sh --certs` writes it: a smaller closure would drop the
names it does not reach.
"""

import argparse
import os
import sys


def read_closure(path):
    """The closure's own fingerprints and the headlines' transitive fingerprints."""
    own, transitive = {}, {}
    with open(path) as lines:
        for line in lines:
            fields = line.rstrip("\n").split("\t")
            if line.startswith("# transitive\t") and len(fields) == 3:
                transitive[fields[1]] = fields[2]
            elif not line.startswith("#") and len(fields) >= 3:
                own[fields[1]] = fields[2]
    return own, transitive


def read_ledger(path):
    """Each ledger row's declaration and fingerprint (empty when it records none)."""
    ledger = {}
    with open(path) as lines:
        for line in lines:
            if line.startswith("#") or not line.strip():
                continue
            fields = line.rstrip("\n").split("\t")
            ledger[fields[0]] = fields[3] if len(fields) > 3 else ""
    return ledger


def read_baseline(path):
    """The declarations listed in a baseline of unrecorded declarations, one per line."""
    with open(path) as lines:
        return {line.strip() for line in lines if line.strip() and not line.startswith("#")}


BASELINE_HEADER = """\
# Statement-closure declarations with no audit-ledger row, recorded so that only new ones fail.
# scripts/audit_ledger.py fails on a closure declaration that is neither in audit/audited.txt nor
# listed here. Audit and record a new declaration rather than adding it here; refresh this file with
# `python3 scripts/audit_ledger.py audit/statement_closure.txt audit/audited.txt
#   --baseline audit/unrecorded.txt --write-baseline` (audit/README.md).
"""


def write_baseline(path, names):
    """Write a baseline: its header, then the names sorted, one per line."""
    tmp = f"{path}.tmp"
    with open(tmp, "w") as out:
        out.write(BASELINE_HEADER)
        for name in sorted(names):
            out.write(name + "\n")
    os.replace(tmp, path)


def compare(closure, ledger, baseline=None):
    """The ledger's state against a closure's own fingerprints; with a baseline, the unrecorded
    declarations it does not list (`new`) and its names now recorded or out of the closure."""
    unrecorded = sorted(n for n in closure if n not in ledger)
    listed = baseline if baseline is not None else set(unrecorded)
    return {
        "unrecorded": unrecorded,
        "new": [n for n in unrecorded if n not in listed],
        "settled": sorted(n for n in listed if n in ledger or n not in closure),
        "stale": sorted(n for n in closure if ledger.get(n) and ledger[n] != closure[n]),
        "no_fingerprint": sorted(n for n in closure if n in ledger and not ledger[n]),
        "gone": sorted(n for n in ledger if n not in closure),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("closure")
    parser.add_argument("ledger")
    parser.add_argument("--previous", help="the previous closure, for the transitive fingerprints")
    parser.add_argument("--baseline", help="the unrecorded declarations allowed (audit/unrecorded.txt)")
    parser.add_argument("--write-baseline", action="store_true",
                        help="rewrite the baseline as its names still unrecorded in the closure")
    parser.add_argument("--accept-new", action="store_true",
                        help="with --write-baseline, also add the new unrecorded declarations")
    args = parser.parse_args(argv)
    if (args.write_baseline or args.accept_new) and not args.baseline:
        parser.error("--write-baseline and --accept-new need --baseline")
    if args.accept_new and not args.write_baseline:
        parser.error("--accept-new needs --write-baseline")
    current, transitive = read_closure(args.closure)
    ledger = read_ledger(args.ledger)
    baseline = read_baseline(args.baseline) if args.baseline else None
    state = compare(current, ledger, baseline)
    if args.write_baseline:
        keep = set(state["unrecorded"]) - set(state["new"])
        if args.accept_new:
            keep |= set(state["new"])
        write_baseline(args.baseline, keep)
        print(f"{args.baseline}: {len(keep)} declarations ({len(baseline - keep)} removed, "
              f"{len(keep - baseline)} added)")
        return 0
    previous, previous_transitive = read_closure(args.previous) if args.previous else ({}, {})
    moved = sorted(h for h in transitive
                   if h in previous_transitive and transitive[h] != previous_transitive[h])
    hidden = [h for h in moved if current.get(h) == previous.get(h)]
    print(f"headline transitive fingerprints changed since the previous closure: {len(moved)} of "
          f"{len(transitive)}, {len(hidden)} with the headline's own fingerprint unchanged (a "
          "dependency's type or body changed; see audit/README.md)")
    for headline in hidden[:20]:
        print("  transitive only:", headline)
    print(f"not yet recorded in audit/audited.txt: {len(state['unrecorded'])}, of them not in the "
          f"baseline: {len(state['new'])}; changed since audit (re-audit): {len(state['stale'])}; "
          f"recorded without fingerprint: {len(state['no_fingerprint'])}; ledger entries no longer "
          f"in the closure: {len(state['gone'])} (the changed entries and the unrecorded ones not in "
          "the baseline fail; see audit/README.md)")
    if baseline is not None and state["settled"]:
        print(f"baseline names now recorded or not in this closure: {len(state['settled'])} (after a "
              "--certs check, --write-baseline removes them)")
    status = 0
    if state["stale"]:
        print(f"FAIL: {len(state['stale'])} stale audit-ledger rows; re-audit each declaration and "
              f"record its new fingerprint in {args.ledger}:")
        for name in state["stale"]:
            print(f"  {name}: ledger {ledger[name]}, closure {current[name]}")
        status = 1
    if state["new"]:
        print(f"FAIL: {len(state['new'])} declarations entered the statement closure with no row in "
              f"{args.ledger} and are not in {args.baseline}. Audit each one adversarially "
              f"(audit/README.md) and record it in {args.ledger} with its fingerprint (third column "
              "of the closure); a declaration renamed from a listed one is carried over by "
              "scripts/carry_audits.py:")
        for name in state["new"]:
            print(f"  {name}\t{current[name]}")
        status = 1
    return status


if __name__ == "__main__":
    sys.exit(main())
