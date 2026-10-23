#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Export paper configurations and hash plans, masking only provenance headers."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


# The bench executables whose export command runs at its defaults in both
# profiles (build/bench/<name> export).
EXPORTS = ("falcon_emulated_bench", "falcon_native_bench", "mldsa_native_bench",
           "mldsa_emulated_bench", "falcon_ring_bench", "mldsa_ring_bench",
           "sha256_compare_bench", "pq_mdoc_bench", "composite_bench")
RSA_CONFIGS = ("auto:9:64:batched:2:narrow,auto:9:2048:batched:2:narrow,"
               "auto:11:64:batched:3:narrow-fp128,auto:11:2048:batched:3:narrow-fp128")
# The modules every export writes per configuration: the data modules and
# the proof modules (lib/gordiehowe/compiler/plan_proofs.h).
MODULES = ("Plan.lean", "Program.lean", "Valid.lean", "Realize.lean", "Honest.lean")


# The license header every exported module opens with (plan_export.h's
# kLeanLicenseHeader); a reference exported before it existed lacks it.
LICENSE_HEADER = (b"-- Copyright 2026 Chad Sharp and Paul Grubbs\n"
                  b"-- SPDX-License-Identifier: Apache-2.0\n\n")


def normalized(data):
    if data.startswith(LICENSE_HEADER):
        data = data[len(LICENSE_HEADER):]
    data = re.sub(rb"(?m)^- (C\+\+ commit|bench run): `[^`]*`$",
                  rb"- \1: `<masked>`", data)
    return re.sub(rb'(?m)^(\s*(?:cppCommit|runId) := )"[^"]*"(,?)$',
                  rb'\1"<masked>"\2', data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--timeout", type=int, default=5400)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    binaries = args.build.resolve() / "bench"
    required = set(EXPORTS) | {"mdoc_bench", "rsa_pkcs1_bench", "keccak_compare_bench"}
    missing = [name for name in sorted(required) if not (binaries / name).is_file()]
    if missing:
        raise ValueError(f"Missing export binaries: {missing}")
    clean_env = {k: v for k, v in os.environ.items()
                 if not k.startswith(("GH_", "PQ_")) and k != "NOBE"}
    runs = []
    for profile in ("narrow", "wide"):
        cases = [(target, "default", []) for target in EXPORTS]
        if profile == "narrow":
            cases += [("mdoc_bench", "default", []), ("rsa_pkcs1_bench", "default", [])]
        for size in (64, 1024):
            cases += [(target, f"ring-{size}", ["--ring-size", str(size)])
                      for target in ("falcon_ring_bench", "mldsa_ring_bench")]
        for size in (1024, 8192, 32768):
            cases += [("keccak_compare_bench", f"hash-{size}", ["--bytes", str(size)]),
                      ("sha256_compare_bench", f"hash-{size}",
                       ["--mode", "batched", "--bytes", str(size)])]
        # The SHA-256 comparison's checked-in plans also cover 64 B and 2 KiB.
        for size in (64, 2048):
            cases += [("sha256_compare_bench", f"hash-{size}",
                       ["--mode", "batched", "--bytes", str(size)])]
        for target, group, options in cases:
            directory = output / profile / group
            directory.mkdir(parents=True, exist_ok=True)
            if target == "pq_mdoc_bench":
                options = options + ["--attrs", "1,2,4" if profile == "narrow" else "1"]
            if target == "rsa_pkcs1_bench":
                options = options + ["--configs", RSA_CONFIGS]
            command = [str(binaries / target), "export", "--profile", profile,
                       "--dir", str(directory), "--commit", args.commit,
                       "--run-id", output.name, *options]
            env = dict(clean_env, GH_THREADS="single")
            log_path = directory / f"{target}.log"
            with log_path.open("w") as log:
                result = subprocess.run(command, env=env, cwd=binaries, stdout=log,
                                        stderr=subprocess.STDOUT, timeout=args.timeout)
            runs.append({"profile": profile, "target": target, "group": group,
                         "exit_code": result.returncode})
            print(f"{profile}/{group}/{target}: exit={result.returncode}", flush=True)
            if result.returncode:
                raise RuntimeError(f"Export failed: {log_path}")
    # Every configuration directory holds all of its modules.
    for directory in sorted({p.parent for p in output.rglob("*.lean")}):
        missing = [m for m in MODULES if not (directory / m).is_file()]
        if missing:
            raise RuntimeError(f"Export incomplete: {directory} lacks {missing}")
    files = []
    for path in sorted(output.rglob("*.lean")):
        data = path.read_bytes()
        files.append({"path": path.relative_to(output).as_posix(),
                      "sha256": hashlib.sha256(data).hexdigest(),
                      "normalized_sha256": hashlib.sha256(normalized(data)).hexdigest()})
    if not files:
        raise RuntimeError("Exporters produced no plans")
    (output / "exports.json").write_text(json.dumps(
        {"schema": 1, "normalization": "provenance-v2", "commit": args.commit,
         "runs": runs, "files": files}, indent=2) + "\n")


if __name__ == "__main__":
    main()
