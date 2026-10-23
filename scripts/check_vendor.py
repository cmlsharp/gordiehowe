#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Check unchanged Longfellow files against their manifest and upstream pin.

Also checks that third_party/longfellow/licensing.json, beside the manifest,
pins the same upstream commit and classes every manifest file as vendored.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    upstream = args.upstream or root / "comparisons/longfellow/upstream"
    manifest = json.loads((root / "third_party/longfellow/manifest.json").read_text())
    licensing = json.loads((root / "third_party/longfellow/licensing.json").read_text())
    if licensing["upstream"].split()[-1] != manifest["upstream_commit"]:
        raise SystemExit(f"licensing.json pins {licensing['upstream']}, the manifest "
                         f"{manifest['upstream_commit']}")
    vendored = {f["path"] for f in licensing["files"] if f["class"] == "vendored"}
    unlisted = sorted({row["path"] for row in manifest["files"]} - vendored)
    if unlisted:
        raise SystemExit(f"Manifest files licensing.json does not class as vendored: {unlisted}")
    commit = subprocess.check_output(["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True).strip()
    if commit != manifest["upstream_commit"]:
        raise SystemExit(f"Wrong upstream pin: {commit}")
    for row in manifest["files"]:
        vendored = (root / row["path"]).read_bytes()
        original = subprocess.check_output(["git", "-C", str(upstream), "show", f"{commit}:{row['upstream_path']}"])
        if hashlib.sha256(vendored).hexdigest() != row["sha256"] or vendored != original:
            raise SystemExit(f"Vendor mismatch: {row['path']}")
    print(f"{len(manifest['files'])} files match Longfellow {commit}")


if __name__ == "__main__":
    main()
