#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Compile actual generated programs and their algorithms; never builds dependencies.

Run on a built certificate tree with explicit PQ_MEM_MAX and PQ_LAKE_JOBS. Every
case closes over generated computational constants, emits C, and requires compiler
IR for its ordinary definitions. Each invocation is bounded to 120 seconds.
Use --list or --emit-only to inspect coverage without invoking Lean. A selected
subset is reported as partial coverage; unavailable or noncomputable cases fail.
"""

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
import re
from pathlib import Path, PurePosixPath
import subprocess
import time


@dataclass(frozen=True)
class Family:
    key: str
    program: str
    application: bool = False


FAMILIES = (
    Family("falcon_native", "Falcon512.Native.ROMParams", True),
    Family("falcon_emulated", "Falcon512.Emulated.ROMParams", True),
    Family("falcon_ring_native", "Falcon512.Ring.Native.ROMParams", True),
    Family("falcon_ring_carrier", "Falcon512.Ring.Carrier.ROMParams", True),
    Family("mldsa_native", "MLDSA44.Native.ROMParams", True),
    Family("mldsa_emulated", "MLDSA44.Emulated.ROMParams", True),
    Family("mldsa_ring_native", "MLDSA44.Ring.Native.ROMParams", True),
    Family("mldsa_ring_carrier", "MLDSA44.Ring.Carrier.ROMParams", True),
    Family("mdl_ecdsa", "MDL.ECDSA.ROMParams"),
    Family("mdl_mldsa", "MDL.MLDSA44.Attrs1.ROMParams"),
    Family("rsa2048", "RSA2048.Goldilocks2.Msg2KiB.ROMParams"),
    Family("sha3", "SHA3.Batched1KiB.ROMParams"),
    Family("sha256", "SHA256.Batched64B.ROMParams"),
)
ROLES = ("proof_system", "prover", "verifier", "simulator", "extractor", "source_width")


@dataclass(frozen=True)
class Case:
    key: str
    imports: tuple[str, ...]
    body: str
    definitions: tuple[str, ...] = ("witness",)
    scope: str = "actual application"

    def source(self) -> str:
        imports = "\n".join(f"import {name}" for name in self.imports)
        checks = "\n".join(
            f'  unless (IR.findEnvDecl (← getEnv) ``GordieHowe.RuntimeSmoke.{name}).isSome do\n'
            f'    throwError "runtime smoke: {name} has no compiler IR"'
            for name in self.definitions
        )
        return (
            "-- Copyright 2026 Chad Sharp and Paul Grubbs\n"
            "-- SPDX-License-Identifier: Apache-2.0\n\n"
            f"{imports}\nimport Lean\n\nnamespace GordieHowe.RuntimeSmoke\n"
            f"{self.body}\nend GordieHowe.RuntimeSmoke\n\n"
            "open Lean Elab Command\nrun_cmd do\n"
            f'{checks}\n  logInfo "runtime smoke: {self.key} compiled"\n'
        )


def family_case(family: Family, role: str) -> Case:
    generated = f"GordieHowe.Generated.{family.program}"
    app = f"GordieHowe.{family.program}"
    imports = (f"GordieHoweCerts.Generated.{family.program}.Certified",)
    scope = "actual application" if family.application else "actual core program"
    if role == "source_width":
        return Case(
            f"{family.key}.{role}", imports,
            f"def witness := {generated}.runtimeParts.width\n"
            "#eval witness 0\n"
            '#eval (show IO Unit from do\n  unless witness 1000000000 == 0 do\n'
            '    throw (IO.userError "source width outside exported circuits is not zero"))',
            scope=scope,
        )
    if family.application:
        imports += (f"GordieHoweCerts.Applications.{family.program}",)
        system = f"{app}.proofSystem"
        binder = ""
        signer_arg = ""
        strategy = f"{app}.honestStrategy"
        if family.program.startswith("Falcon512.Ring."):
            binder = " (signer : GordieHowe.Falcon512.Ring.Native.Signer 32)"
            signer_arg = " signer"
            strategy += " signer"
        elif family.program.startswith("MLDSA44.Ring.Native."):
            strategy += " 34"
        elif family.program.startswith("MLDSA44.Ring.Carrier."):
            strategy += " (msgLen := 34)"
        algorithm = {
            "proof_system": system,
            "prover": f"{app}.prover{signer_arg} {system} ({strategy})",
            "verifier": f"{app}.verifierROM{signer_arg} {system}",
            "simulator": f"{app}.simulator{signer_arg} {system}",
            "extractor": f"{app}.{'ringKeyExtractor' if '.Ring.' in family.program else 'keyExtractor'}{signer_arg} {system}",
        }[role]
        # The signer is a genuine input of the Falcon ring application, not a
        # supplied proof system, prover, simulator, or generated runtime record.
        if role == "proof_system":
            binder = ""
        return Case(f"{family.key}.{role}", imports, f"def witness{binder} := {algorithm}")
    imports += ("GordieHowe.ProofSystem.Program.FieldProofSystem",)
    system = f"{generated}.proofSystem"
    if role == "proof_system":
        body = f"def witness := {system}"
    elif role == "verifier":
        body = f"def witness := {system}.verifier"
    elif role == "extractor":
        body = (
            f"def witness {{W : Type}} [Inhabited W]\n"
            f"    (proj : {generated}.Program.program.Valuation {generated}.interp →\n"
            f"      {generated}.Program.program.Assignment {generated}.interp → W) :=\n"
            f"  {system}.extractor proj"
        )
    else:
        # Core-only exports have no application-specific honest completion.
        # Close over their actual field-domain runtime data; only the required
        # source honest algorithm remains an input of the generic prover.
        body = (
            f"def ready := {generated}.runtimeInputs.ready\n"
            f"  {generated}.core.readyFacts\n"
            f"def fieldSystem := {system}.withFieldProofs ready\n"
        )
        if role == "simulator":
            body += f"def witness := fieldSystem.simulator ({system}.fieldSims ready)"
        else:
            body += (
                f"def witness {{Inp : Type}}\n"
                f"    {{relH : Set ({generated}.Program.program.Valuation {generated}.interp × Inp)}}\n"
                f"    (honest : {generated}.Program.program.HonestCore {generated}.interp relH) :=\n"
                f"  fieldSystem.prover ({system}.fieldHonestDomains ready) honest"
            )
            scope += "; source HonestCore input, no exported application completion"
        return Case(f"{family.key}.{role}", imports, body,
                    ("ready", "fieldSystem", "witness"), scope)
    return Case(f"{family.key}.{role}", imports, body, scope=scope)


def cases() -> list[Case]:
    result = [family_case(family, role) for family in FAMILIES for role in ROLES]
    for variant in ("Native", "Carrier"):
        for profile in ("ROMParams", "QROMParams"):
            program = f"MLDSA44.Ring.{variant}.{profile}"
            app = f"GordieHowe.{program}"
            result.append(Case(
                f"converted_{variant.lower()}_{profile.lower()}",
                (f"GordieHoweCerts.Applications.{program}.RingForger",),
                f"def data := {app}.convertedSim {app}.proofSystem\n"
                "def witness := GordieHowe.RealizedProgram.ProofSystem.IOP.simulator data",
                ("data", "witness"), "actual converted Ring simulator",
            ))
    return result


def digest(path: Path) -> str:
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def validate_source_manifest(path: Path, formal: Path) -> tuple[str, int]:
    """Check G's files mapping against the actual source tree before invoking Lean."""
    def unique_object(pairs: list[tuple[str, object]]) -> dict:
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate manifest key: {key}")
            result[key] = value
        return result

    raw = path.read_bytes()
    manifest = json.loads(raw, object_pairs_hook=unique_object)
    if not isinstance(manifest, dict):
        raise ValueError("source manifest must be a JSON object")
    files = manifest.get("files")
    if not isinstance(files, dict) or not files:
        raise ValueError("source manifest files must be a nonempty mapping")
    formal = formal.resolve()
    mismatches = []
    for name, expected in files.items():
        relative = PurePosixPath(name)
        if (len(relative.parts) < 2 or relative.parts[0] != "formal"
                or ".." in relative.parts or "\\" in name or str(relative) != name):
            raise ValueError(f"invalid manifest source path: {name}")
        if not isinstance(expected, str) or re.fullmatch(r"[0-9a-f]{64}", expected) is None:
            raise ValueError(f"invalid SHA256 digest for {name}")
        source = formal.joinpath(*relative.parts[1:]).resolve()
        if not source.is_relative_to(formal):
            raise ValueError(f"manifest source escapes formal tree: {name}")
        if not source.is_file():
            mismatches.append(f"{name}: missing file")
        elif digest(source) != expected:
            mismatches.append(f"{name}: SHA256 mismatch")
    if mismatches:
        raise ValueError("source manifest verification failed: " + "; ".join(mismatches))
    return hashlib.sha256(raw).hexdigest(), len(files)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--formal", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--source-manifest", type=Path, help="JSON files mapping to verify against the actual formal source tree")
    parser.add_argument("--case", action="append", default=[], help="exact case key; repeatable")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--emit-only", action="store_true")
    parser.add_argument("--report-role", action="append", default=[], choices=ROLES,
                        help="run this role's cases but report their status without failing; repeatable")
    args = parser.parse_args()
    available = cases()
    unknown = set(args.case) - {case.key for case in available}
    if unknown:
        parser.error(f"unknown cases: {sorted(unknown)}")
    selected = [case for case in available if not args.case or case.key in args.case]
    if args.list:
        for case in selected:
            print(f"{case.key}\t{case.scope}")
        return 0
    if args.output is None:
        parser.error("--output is required to retain sources, C output, logs and results")
    if not args.emit_only and any(not os.environ.get(v) for v in ("PQ_MEM_MAX", "PQ_LAKE_JOBS")):
        parser.error("set PQ_MEM_MAX and PQ_LAKE_JOBS explicitly")
    formal, output = args.formal.resolve(), args.output.resolve()
    manifest_hash, manifest_count = None, None
    if args.source_manifest:
        try:
            manifest_hash, manifest_count = validate_source_manifest(args.source_manifest, formal)
        except (OSError, ValueError) as error:
            parser.error(str(error))
        print(f"source manifest: verified {manifest_count} files", flush=True)
    output.mkdir(parents=True, exist_ok=True)
    results = []
    for case in selected:
        source = output / (case.key + ".lean")
        c_output = source.with_suffix(".c")
        log = source.with_suffix(".log")
        source.write_text(case.source())
        row = {"case": case.key, "scope": case.scope, "source_sha256": digest(source),
               "imports": {name: digest(formal / (name.replace(".", "/") + ".lean"))
                           for name in case.imports},
               "import_oleans": {
                   name: digest(path) if path.exists() else None
                   for name in case.imports
                   for path in [formal / ".lake/build/lib/lean" / (name.replace(".", "/") + ".olean")]
               }, "status": "emitted"}
        if not args.emit_only:
            c_output.unlink(missing_ok=True)
            command = ["timeout", "120", str(formal / "scripts/lake.sh"), "env", "lean",
                       "-R", str(output), "-c", str(c_output), str(source)]
            start = time.monotonic()
            with log.open("w") as stream:
                try:
                    result = subprocess.run(command, cwd=formal, stdout=stream,
                                            stderr=subprocess.STDOUT, timeout=130, check=False)
                    row["exit_code"] = result.returncode
                except subprocess.TimeoutExpired:
                    row["exit_code"] = 124
            row["seconds"] = round(time.monotonic() - start, 3)
            text = log.read_text()
            has_c = c_output.exists() and all(
                f"l_GordieHowe_RuntimeSmoke_{name}" in c_output.read_text()
                for name in case.definitions
            )
            passed = (row["exit_code"] == 0 and has_c and "PANIC" not in text
                      and f"runtime smoke: {case.key} compiled" in text)
            row["status"] = "passed" if passed else "failed"
            row["log_sha256"] = digest(log)
            if c_output.exists():
                row["c_sha256"] = digest(c_output)
            print(f"{case.key}: {row['status']} ({row['seconds']}s)", flush=True)
        results.append(row)
        (output / "results.json").write_text(json.dumps({
            "coverage": "all" if len(selected) == len(available) else "partial",
            "selected": len(selected), "total": len(available),
            "completed": len(results), "run_complete": len(results) == len(selected),
            "source_manifest_sha256": manifest_hash,
            "source_manifest_validated_files": manifest_count, "cases": results,
        }, indent=2) + "\n")
    reported = [row for row in results if row["case"].rsplit(".", 1)[-1] in args.report_role]
    for row in reported:
        print(f"report only: {row['case']}: {row['status']}", flush=True)
    if reported:
        computable = sum(row["status"] != "failed" for row in reported)
        print(f"report only ({', '.join(args.report_role)}): {computable} of {len(reported)} "
              "cases compile; the exclusion can go when all do", flush=True)
    return int(any(row["status"] == "failed" for row in results if row not in reported))


if __name__ == "__main__":
    raise SystemExit(main())
