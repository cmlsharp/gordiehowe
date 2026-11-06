#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Reject loss of computability or compiled IR against the fixed f1 baseline."""

import argparse
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path


def read_inventory(text: str) -> dict[str, tuple[bool, bool]]:
    rows = csv.DictReader(io.StringIO(text), delimiter="\t")
    if rows.fieldnames != ["name", "noncomputable", "has_ir"]:
        raise ValueError("invalid computability inventory header")
    result = {}
    for row in rows:
        name = row["name"]
        if not name or name in result or None in row:
            raise ValueError(f"empty, duplicate or malformed declaration: {name!r}")
        flags = [row["noncomputable"], row["has_ir"]]
        if any(flag not in ("true", "false") for flag in flags):
            raise ValueError(f"invalid computability flags for {name}")
        result[name] = tuple(flag == "true" for flag in flags)
    if not result:
        raise ValueError("empty computability inventory")
    return result


def compare(baseline: dict, candidate: dict) -> dict:
    common = baseline.keys() & candidate.keys()
    if not common:
        raise ValueError("inventories have no common definitions")
    return {
        "baseline_definitions": len(baseline),
        "candidate_definitions": len(candidate),
        "common_definitions": len(common),
        "became_noncomputable": sorted(
            name for name in common if not baseline[name][0] and candidate[name][0]
        ),
        "lost_ir": sorted(
            name for name in common if baseline[name][1] and not candidate[name][1]
        ),
        # Removal is not loss of code in a surviving definition. The statement-closure
        # audit reviews removed declarations separately; retain all names as evidence.
        "removed": sorted(baseline.keys() - candidate.keys()),
        "added": sorted(candidate.keys() - baseline.keys()),
    }


def main() -> int:
    formal = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inventory", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    baseline_path = formal / "audit/computability-f1.tsv.gz"
    metadata = json.loads((formal / "audit/computability-f1.json").read_text())
    compressed = baseline_path.read_bytes()
    raw = gzip.decompress(compressed)
    for data, key in ((compressed, "compressed_sha256"), (raw, "uncompressed_sha256")):
        if hashlib.sha256(data).hexdigest() != metadata[key]:
            raise ValueError(f"baseline integrity mismatch: {key}")
    if (formal / "lean-toolchain").read_text().strip() != metadata["toolchain"]:
        raise ValueError("computability baseline toolchain differs from current toolchain")
    baseline = read_inventory(raw.decode())
    if len(baseline) != metadata["definitions"]:
        raise ValueError("baseline definition count mismatch")
    candidate_raw = args.inventory.read_bytes()
    result = compare(baseline, read_inventory(candidate_raw.decode()))
    result["baseline_revision"] = metadata["revision"]
    result["inventory_sha256"] = hashlib.sha256(candidate_raw).hexdigest()
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(
        f"computability regression: {result['common_definitions']} common definitions; "
        f"{len(result['became_noncomputable'])} became noncomputable; "
        f"{len(result['lost_ir'])} lost compiled IR; "
        f"{len(result['added'])} added, {len(result['removed'])} removed "
        "(recorded for closure review)"
    )
    for key in ("became_noncomputable", "lost_ir"):
        for name in result[key]:
            print(f"FAIL {key}: {name}")
    return int(bool(result["became_noncomputable"] or result["lost_ir"]))


if __name__ == "__main__":
    raise SystemExit(main())
