#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Compare a statement closure with the audit ledger; a stale ledger row fails the check.

A row is stale when its declaration is in the closure and its recorded fingerprint differs from
the closure's. Declarations not yet recorded, rows without a fingerprint and rows no longer in the
closure are reported and do not fail (audit/README.md).
"""

import argparse
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


def compare(closure, ledger):
    """The ledger's state against a closure's own fingerprints."""
    return {
        "unrecorded": sorted(n for n in closure if n not in ledger),
        "stale": sorted(n for n in closure if ledger.get(n) and ledger[n] != closure[n]),
        "no_fingerprint": sorted(n for n in closure if n in ledger and not ledger[n]),
        "gone": sorted(n for n in ledger if n not in closure),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("closure")
    parser.add_argument("previous", help="the previous closure, for the transitive fingerprints")
    parser.add_argument("ledger")
    args = parser.parse_args(argv)
    current, transitive = read_closure(args.closure)
    previous, previous_transitive = read_closure(args.previous)
    moved = sorted(h for h in transitive
                   if h in previous_transitive and transitive[h] != previous_transitive[h])
    hidden = [h for h in moved if current.get(h) == previous.get(h)]
    print(f"headline transitive fingerprints changed since the previous closure: {len(moved)} of "
          f"{len(transitive)}, {len(hidden)} with the headline's own fingerprint unchanged (a "
          "dependency's type or body changed; see audit/README.md)")
    for headline in hidden[:20]:
        print("  transitive only:", headline)
    ledger = read_ledger(args.ledger)
    state = compare(current, ledger)
    print(f"not yet recorded in audit/audited.txt: {len(state['unrecorded'])}; changed since audit "
          f"(re-audit): {len(state['stale'])}; recorded without fingerprint: "
          f"{len(state['no_fingerprint'])}; ledger entries no longer in the closure: "
          f"{len(state['gone'])} (only the changed entries fail; see audit/README.md)")
    if state["stale"]:
        print(f"FAIL: {len(state['stale'])} stale audit-ledger rows; re-audit each declaration and "
              f"record its new fingerprint in {args.ledger}:")
        for name in state["stale"]:
            print(f"  {name}: ledger {ledger[name]}, closure {current[name]}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
