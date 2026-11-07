#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Regenerate every program's generated Lean files from a C++ build, or check them.

Runs each program's bench executable (BUILD/bench/<target> export) into a scratch directory, with
one run id and the commit placeholder, and compares the results byte for byte with
formal/GordieHoweCerts/Generated/<program>/ and formal/Check/{Native,Kernel}/GordieHoweCheck/<program>
(.lean and directory). Nothing is masked: a file whose provenance differs is a difference. Without
--check the tree is updated, files an export no longer writes are removed, and the result is compared
again. With --check nothing is written and any difference fails. No file is written unless every
export succeeded. Raw .cert files are not checked in.

Build the executables first (EXPORT_TARGETS below; formal/README.md). The list of programs is the
checked-in set: an exported program outside it is ignored, a listed program with no export fails, and
a checked-in file of no listed program fails.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

COMMIT = "EXPORTER_COMMIT"
RUN_ID = "exports"
GENERATED = "GordieHoweCerts/Generated/"
CHECKS = ("Check/Native/GordieHoweCheck/", "Check/Kernel/GordieHoweCheck/")

CONSTRUCTIONS = ("Falcon512/Emulated", "Falcon512/Native", "Falcon512/Ring/Carrier",
                 "Falcon512/Ring/Native", "MLDSA44/Emulated", "MLDSA44/Native",
                 "MLDSA44/Ring/Carrier", "MLDSA44/Ring/Native", "MDL/MLDSA44/Attrs1",
                 "SHA256/Batched8Blocks", "SHA256/Batched8KiB", "SHA3/Batched1KiB")
ROM_ONLY = ("MDL/ECDSA", "RSA2048/Goldilocks2/Msg2KiB", "SHA256/Batched1KiB", "SHA256/Batched2KiB",
            "SHA256/Batched32KiB", "SHA256/Batched64B", "SHA3/Batched32KiB", "SHA3/Batched8KiB")
PROGRAMS = frozenset(
    [f"{p}/{params}" for p in CONSTRUCTIONS for params in ("ROMParams", "QROMParams")]
    + [f"{p}/ROMParams" for p in ROM_ONLY])

RSA_CONFIG = "auto:9:2048:batched:2:narrow"


def cases():
    """Each export: (profile, bench target, its options). narrow writes ROMParams, wide QROMParams."""
    result = []
    for profile in ("narrow", "wide"):
        for target in ("falcon_emulated_bench", "falcon_native_bench", "mldsa_native_bench",
                       "mldsa_emulated_bench", "sha256_compare_bench"):
            result.append((profile, target, ()))
        for target in ("falcon_ring_bench", "mldsa_ring_bench"):
            result.append((profile, target, ("--ring-size", "64")))
        result.append((profile, "pq_mdoc_bench", ("--attrs", "1")))
    result.append(("narrow", "mdoc_bench", ()))
    result.append(("narrow", "rsa_pkcs1_bench", ("--configs", RSA_CONFIG)))
    for profile, sizes in (("narrow", (64, 1024, 2048, 8192, 32768)), ("wide", (8192,))):
        result += [(profile, "sha256_compare_bench", ("--mode", "batched", "--bytes", str(size)))
                   for size in sizes]
    for profile, sizes in (("narrow", (1024, 8192, 32768)), ("wide", (1024,))):
        result += [(profile, "keccak_compare_bench", ("--bytes", str(size))) for size in sizes]
    return result


EXPORT_TARGETS = tuple(sorted({case[1] for case in cases()}))


def owner(rel, programs):
    """The program a path below formal/ belongs to, or None."""
    for root in (GENERATED, *CHECKS):
        if rel.startswith(root):
            stem = rel[len(root):]
            if root != GENERATED and stem.endswith(".lean"):
                stem_program = stem[:-len(".lean")]
                if stem_program in programs:
                    return stem_program
            parts = stem.split("/")
            for i in range(len(parts) - 1, 0, -1):
                candidate = "/".join(parts[:i])
                if candidate in programs:
                    return candidate
            return None
    return None


def provenance_errors(rel, data):
    """Where an exported Lean file states provenance other than the fixed commit and run id."""
    errors = []
    for line in re.findall(rb"(?m)^- C\+\+ commit: `([^`]*)`$", data):
        if line != COMMIT.encode():
            errors.append(f"{rel}: C++ commit {line.decode()}")
    for line in re.findall(rb"(?m)^- bench run: `([^`]*)`$", data):
        if line != RUN_ID.encode():
            errors.append(f"{rel}: bench run {line.decode()}")
    for line in re.findall(rb'(?m)^\s*cppCommit := "([^"]*)"', data):
        if line != COMMIT.encode():
            errors.append(f"{rel}: cppCommit {line.decode()}")
    for line in re.findall(rb'(?m)^\s*runId := "([^"]*)"', data):
        if line != RUN_ID.encode():
            errors.append(f"{rel}: runId {line.decode()}")
    return errors


def run_export(build, scratch, index, case, timeout):
    """One export into its own scratch directory; raises on failure."""
    profile, target, options = case
    directory = scratch / f"{index:02d}-{profile}-{target}"
    directory.mkdir(parents=True)
    env = {k: v for k, v in os.environ.items() if not k.startswith(("GH_", "PQ_"))}
    env["GH_THREADS"] = "single"
    command = [str(build / "bench" / target), "export", "--profile", profile, "--dir",
               str(directory), "--commit", COMMIT, "--run-id", RUN_ID, *options]
    result = subprocess.run(command, cwd=directory, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=timeout, check=False)
    if result.returncode:
        tail = result.stdout.decode(errors="replace")[-2000:]
        raise RuntimeError(f"export failed ({result.returncode}): {' '.join(command)}\n{tail}")
    print(f"exported {profile} {target} {' '.join(options)}", flush=True)
    return directory


def collect(directories, programs):
    """The exported files of the listed programs, as {path below formal/: source file}."""
    found = {}
    ignored = 0
    for directory in directories:
        for path in sorted(p for p in directory.rglob("*") if p.is_file()):
            rel = path.relative_to(directory).as_posix()
            if path.suffix == ".cert":
                continue
            if path.suffix not in (".lean", ".ghc"):
                raise RuntimeError(f"unexpected export file: {rel}")
            if owner(rel, programs) is None:
                ignored += 1
                continue
            if rel in found and found[rel].read_bytes() != path.read_bytes():
                raise RuntimeError(f"two exports disagree: {rel}")
            found[rel] = path
    return found, ignored


def tracked_files(formal):
    """Every file under the generated and check trees, as paths below formal/."""
    result = []
    for root in (GENERATED, *CHECKS):
        base = formal / root
        if base.is_dir():
            result += [p.relative_to(formal).as_posix() for p in base.rglob("*") if p.is_file()]
    return sorted(result)


def compare(formal, found, programs):
    """Files to write, files to remove, and files of no listed program."""
    write = [rel for rel, source in sorted(found.items())
             if not (formal / rel).is_file()
             or (formal / rel).read_bytes() != source.read_bytes()]
    current = tracked_files(formal)
    remove = [rel for rel in current if rel not in found and owner(rel, programs) is not None]
    unowned = [rel for rel in current if owner(rel, programs) is None]
    return write, remove, unowned


def regenerate(build, formal, *, case_list=None, programs=PROGRAMS, check=False, jobs=4,
               timeout=1800, scratch_parent=None):
    """Returns 0 when the tree matches the exports at the end, otherwise 1."""
    case_list = cases() if case_list is None else case_list
    missing = sorted({c[1] for c in case_list if not (build / "bench" / c[1]).is_file()})
    if missing:
        raise RuntimeError(f"build these targets first: {' '.join(missing)}")
    with tempfile.TemporaryDirectory(prefix="regenerate-exports-", dir=scratch_parent) as folder:
        scratch = Path(folder)
        with ThreadPoolExecutor(jobs) as pool:
            directories = list(pool.map(
                lambda item: run_export(build, scratch, item[0], item[1], timeout),
                enumerate(case_list)))
        found, ignored = collect(directories, programs)
        absent = sorted(programs - {owner(rel, programs) for rel in found})
        if absent:
            raise RuntimeError(f"no export of: {' '.join(absent)}")
        errors = [e for rel, source in found.items() if rel.endswith(".lean")
                  for e in provenance_errors(rel, source.read_bytes())]
        if errors:
            raise RuntimeError("wrong provenance:\n" + "\n".join(errors))
        write, remove, unowned = compare(formal, found, programs)
        if unowned:
            print("FAIL: files of no listed program:\n  " + "\n  ".join(unowned))
            return 1
        print(f"{len(found)} files of {len(programs)} programs; {ignored} other exported files "
              f"ignored; differ or new: {len(write)}; no longer exported: {len(remove)}")
        if check:
            for rel in write:
                print("  differs:", rel)
            for rel in remove:
                print("  no longer exported:", rel)
            return 1 if write or remove else 0
        for rel in write:
            target = formal / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(found[rel], target)
        for rel in remove:
            (formal / rel).unlink()
        write, remove, unowned = compare(formal, found, programs)
        if write or remove or unowned:
            print(f"FAIL: the tree differs after writing: {write + remove + unowned}")
            return 1
        print("the tree matches the exports")
        return 0


def main(argv=None):
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--build", type=Path, required=True, help="the C++ build directory")
    parser.add_argument("--formal", type=Path, default=root / "formal")
    parser.add_argument("--check", action="store_true", help="compare only; a difference fails")
    parser.add_argument("--jobs", type=int, default=4, help="exports at once")
    parser.add_argument("--timeout", type=int, default=1800, help="seconds per export")
    parser.add_argument("--scratch", type=Path, default=None, help="parent of the scratch directory")
    args = parser.parse_args(argv)
    try:
        return regenerate(args.build.resolve(), args.formal.resolve(), check=args.check,
                          jobs=args.jobs, timeout=args.timeout, scratch_parent=args.scratch)
    except (RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"FAIL: {error}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
