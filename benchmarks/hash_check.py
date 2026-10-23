#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Check every benchmarked system's protocol hash against its field profile.

Usage:
  hash_check.py --profile narrow|wide [--report LOG] [--log NAME=LOG]...
                   [--expect NAME=CONFIG,...]...
                   [--baselines-build DIR] [--baseline LABEL=DIR/TARGET]...
                   [--upstream-pin COMMIT] [--upstream-checkout DIR]
                   [--binius-tree DIR --binius-merkle SUITE]
                   > hashes.json
  hash_check.py --manifest hashes.json    (manifest.txt's lines)

Each field profile fixes its protocol hash (lib/params/param_sets.h):
SHA-256 at the ROM parameters (profiles narrow and narrow-fp128) and SHA-384
at the QROM parameters (profile wide). run_bench.sh runs this before timing and refuses
to time when it fails.

--report LOG    report_bench --probe: one "BUILD <case>" line per worker,
                then the workers' "[<case>] PQ_HASH {json}" lines
                (lib/bench/bench_hook.h). Every case needs at least one.
--log NAME=LOG  a bench executable's bench command with --hash-probe
                (rsa_pkcs1_bench, pq_mdoc_bench, composite_bench): its
                "PQ_HASH {json}" lines, at least one.
--expect NAME=CONFIG,...
                the configurations (and arms) the log NAME must cover: one
                PQ_HASH record of each, and no record of another.
--baseline LABEL=DIR/TARGET
                a longfellow-baselines binary built under DIR
                (--baselines-build, the clone's build directory). Its hash is
                read from the build: a target whose CMake files under
                DIR/baselines/<dir>/CMakeFiles/<target>.dir name
                baselines/common-wide (its include path, link line or the
                headers its objects depend on) uses common-wide's SHA-384;
                any other uses upstream Longfellow's SHA-256; the target's
                name must agree (TARGET_wide exactly for common-wide). The salts follow
                the hash's code: upstream's Merkle leaf nonce is one digest,
                and neither carries a proof seed. No baseline prints a
                PQ_HASH line, so the build is the source.
--upstream-pin COMMIT
                the baselines' upstream gitlink (snapshot_baselines.py
                --info), which must be the commit the vendored files come
                from (third_party/longfellow/manifest.json, d5e6be77);
                --upstream-checkout DIR also checks the snapshot's upstream
                checkout (git rev-parse HEAD) against it.
--binius-tree DIR, --binius-merkle SUITE
                Binius64 (benchmarks/binius.sh tree; ROM parameters only):
                its benchmarks print no Fiat-Shamir hash, so the pinned
                tree's source is read: the challenger of create_proof and
                create_proof_zk (crates/examples/src/lib.rs, StdChallenger),
                which must be HasherChallenger<StdDigest>
                (crates/verifier/src/config.rs and
                crates/spartan-verifier/src/config.rs), and StdDigest
                (crates/hash/src/lib.rs). SUITE is the Merkle hash suite
                binius.sh passes its benchmarks (HASH). Both must be the
                profile's hash.

Each PQ_HASH record must name a profile of the run's family and carry the
family's hash, digest bytes, proof-salt bytes (the proof seed,
random/transcript.h), leaf-salt bytes (the Merkle leaf nonce,
merkle/merkle_commitment.h) and Fiat-Shamir stream bytes e beyond the first k
(kFSStreamExtraBytes, random/transcript.h). Each baseline must use the family's hash. The
output (stdout) lists every record; failures go to stderr and the exit status
is 1.
"""

import argparse
import json
import pathlib
import re
import subprocess
import sys

# The GordieHowe systems of each profile family: the hash and the sizes the
# code derives from its digest k (seed k bytes, leaf nonce 2k bytes).
EXPECTED = {
    "narrow": {"name": "SHA-256", "digest_bytes": 32, "proof_salt_bytes": 32,
               "leaf_salt_bytes": 64, "fs_stream_extra_bytes": 206848},
    "wide": {"name": "SHA-384", "digest_bytes": 48, "proof_salt_bytes": 48,
             "leaf_salt_bytes": 96, "fs_stream_extra_bytes": 206848},
}
# The profile ids of each family.
FAMILY = {"narrow": "narrow", "narrow-fp128": "narrow", "wide": "wide"}
# Binius64's Rust digest types and Merkle suites (binius.sh's HASH), by hash name.
BINIUS_DIGESTS = {"sha2::Sha256": "SHA-256", "sha2::Sha384": "SHA-384"}
BINIUS_MERKLE = {"sha256": "SHA-256", "blake3": "BLAKE3"}
# The vendored Longfellow files' upstream commit.
VENDOR_MANIFEST = pathlib.Path(__file__).resolve().parent.parent / \
    "third_party" / "longfellow" / "manifest.json"
# The baselines' hash in each family; the salts are upstream's sizes.
BASELINE = {
    "narrow": {"name": "SHA-256", "digest_bytes": 32, "proof_salt_bytes": 0,
               "leaf_salt_bytes": 32},
    "wide": {"name": "SHA-384", "digest_bytes": 48, "proof_salt_bytes": 0,
             "leaf_salt_bytes": 48},
}

REPORT_BUILD = re.compile(r"^BUILD (\S+)\s*$")
REPORT_HASH = re.compile(r"^\[([^\]]+)\] PQ_HASH (\{.*\})\s*$")
PLAIN_HASH = re.compile(r"^PQ_HASH (\{.*\})\s*$")


def read_report(text):
    cases, records = [], []
    for line in text.splitlines():
        m = REPORT_BUILD.match(line)
        if m:
            cases.append(m.group(1))
            continue
        m = REPORT_HASH.match(line)
        if m:
            e = json.loads(m.group(2))
            e["case"] = m.group(1)
            records.append(e)
    return cases, records


def read_plain(name, text):
    records = []
    for line in text.splitlines():
        m = PLAIN_HASH.match(line)
        if m:
            e = json.loads(m.group(1))
            e["case"] = name
            records.append(e)
    return records


def uses_common_wide(target_dir):
    """Whether any CMake file of the target names baselines/common-wide: its
    flags, link line and dependency files (object files are skipped)."""
    for f in target_dir.rglob("*"):
        if f.is_file() and f.suffix != ".o" and b"common-wide" in f.read_bytes():
            return True
    return False


def baseline_record(build, label, spec):
    d, _, target = spec.partition("/")
    if not d or not target:
        raise SystemExit(f"--baseline {label}={spec}: expected DIR/TARGET")
    tdir = pathlib.Path(build) / "baselines" / d / "CMakeFiles" / f"{target}.dir"
    if not tdir.is_dir():
        return {"case": label, "target": spec, "hash": None,
                "error": f"no CMake target directory {tdir}"}
    fam = "wide" if uses_common_wide(tdir) else "narrow"
    return {"case": label, "target": spec, "hash": dict(BASELINE[fam]),
            "source": "baselines/common-wide" if fam == "wide"
            else "upstream Longfellow"}


def binius_record(tree, merkle):
    """Binius64's Fiat-Shamir hash and Merkle suite from the pinned tree."""
    tree = pathlib.Path(tree)

    def read(rel):
        try:
            return (tree / rel).read_text()
        except OSError:
            return None
    lib = read("crates/hash/src/lib.rs")
    m = re.search(r"pub type StdDigest = ([\w:]+);", lib or "")
    digest = m.group(1) if m else None
    errors = []
    if digest is None:
        errors.append(f"no StdDigest in {tree}/crates/hash/src/lib.rs")
    for rel in ("crates/verifier/src/config.rs", "crates/spartan-verifier/src/config.rs"):
        if not re.search(r"pub type StdChallenger\s*=\s*(binius_transcript::fiat_shamir::)?"
                         r"HasherChallenger<StdDigest>;", read(rel) or ""):
            errors.append(f"{rel}: StdChallenger is not HasherChallenger<StdDigest>")
    examples = read("crates/examples/src/lib.rs") or ""
    if "config::StdChallenger" not in examples or "StdChallenger::default()" not in examples:
        errors.append("crates/examples/src/lib.rs: the proofs do not use StdChallenger")
    return {"case": "binius64", "tree": str(tree),
            "fiat_shamir": {"challenger": "HasherChallenger<StdDigest>", "digest": digest,
                            "name": BINIUS_DIGESTS.get(digest)},
            "merkle": {"suite": merkle, "name": BINIUS_MERKLE.get(merkle)},
            "errors": errors}


def git_head(path):
    try:
        return subprocess.run(["git", "-C", str(path), "rev-parse", "HEAD"],
                              capture_output=True, text=True, timeout=60).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        return ""


def check_upstream(pin, checkout=None, manifest=VENDOR_MANIFEST):
    want = json.loads(pathlib.Path(manifest).read_text())["upstream_commit"]
    out = {"pin": pin, "expected": want}
    errors = []
    if pin != want:
        errors.append(f"baselines upstream pin {pin} is not the vendored "
                      f"Longfellow commit {want}")
    if checkout is not None:
        out["checkout"] = git_head(checkout)
        if out["checkout"] != want:
            errors.append(f"baselines upstream checkout {checkout} is at "
                          f"{out['checkout'] or 'no commit'}, not {want}")
    return out, errors


def check(profile, report=None, logs=(), baselines_build=None, baselines=(),
          expect=None, upstream=None, binius=None):
    """EXPECT: {log name: [config, ...]}; UPSTREAM: (pin, checkout or
    None[, manifest]); BINIUS: (tree, Merkle suite)."""
    errors, systems = [], []
    want = EXPECTED[profile]
    if report is not None:
        cases, records = read_report(report)
        if not cases:
            errors.append("report: no BUILD lines")
        seen = {r["case"] for r in records}
        for c in cases:
            if c not in seen:
                errors.append(f"{c}: no PQ_HASH line")
        systems += records
    expect = expect or {}
    for name in sorted(set(expect) - {n for n, _ in logs}):
        errors.append(f"--expect {name}: no such log")
    for name, text in logs:
        records = read_plain(name, text)
        if not records:
            errors.append(f"{name}: no PQ_HASH line")
        if name in expect:
            # One record per configuration and arm the run times.
            got = [r.get("config") for r in records]
            for c in expect[name]:
                if got.count(c) != 1:
                    errors.append(f"{name}: {got.count(c)} PQ_HASH lines of {c}, expected 1")
            for c in sorted(set(got) - set(expect[name])):
                errors.append(f"{name}: PQ_HASH line of {c}, which the run does not time")
        systems += records
    for r in systems:
        where = f"{r['case']} {r.get('config', '?')}"
        fam = FAMILY.get(r.get("profile"))
        if fam is None:
            errors.append(f"{where}: unknown profile {r.get('profile')!r}")
        elif fam != profile:
            errors.append(f"{where}: profile {r['profile']} in a {profile} run")
        if r.get("hash") != want:
            errors.append(f"{where}: hash {r.get('hash')} where the {profile} "
                          f"profile fixes {want}")
    bl = []
    if baselines and baselines_build is None:
        raise SystemExit("--baseline needs --baselines-build")
    for label, spec in baselines:
        rec = baseline_record(baselines_build, label, spec)
        bl.append(rec)
        if rec["hash"] is None:
            errors.append(f"baseline {label}: {rec['error']}")
        elif (rec["hash"]["name"] == "SHA-384") != spec.endswith("_wide"):
            errors.append(f"baseline {label} ({spec}): the build says "
                          f"{rec['hash']['name']}, which its target name "
                          "(TARGET_wide for common-wide) contradicts")
        elif rec["hash"]["name"] != BASELINE[profile]["name"]:
            errors.append(f"baseline {label} ({spec}): {rec['hash']['name']} "
                          f"in a {profile} run, which needs "
                          f"{BASELINE[profile]['name']}")
    out = {"profile": profile, "expected": want,
           "expected_baselines": BASELINE[profile], "systems": systems,
           "baselines": bl}
    if upstream is not None:
        out["upstream"], errs = check_upstream(*upstream)
        errors += errs
    if binius is not None:
        rec = binius_record(*binius)
        errors += [f"binius64: {e}" for e in rec.pop("errors")]
        for part in ("fiat_shamir", "merkle"):
            if rec[part]["name"] != want["name"]:
                errors.append(f"binius64: {part} hash {rec[part]['name'] or 'unknown'} "
                              f"where the {profile} profile fixes {want['name']}")
        out["binius"] = rec
    out.update(ok=not errors, errors=errors)
    return out


def pairs(values, flag):
    out = []
    for v in values:
        k, sep, x = v.partition("=")
        if not sep or not k or not x:
            raise SystemExit(f"{flag} {v}: expected NAME=VALUE")
        out.append((k, x))
    return out


def manifest(path):
    h = json.loads(pathlib.Path(path).read_text())
    print(f"protocol hash ({h['profile']} profile, checked before timing; "
          "hashes.json):")
    for r in h["systems"] + h["baselines"]:
        x = r["hash"]
        name = r["case"] + " " + (r["config"] if "config" in r else r["target"])
        if r.get("ring"):
            name += f" R={r['ring']}"
        line = (f"  {name}: {x['name']}, digest {x['digest_bytes']} B, proof salt "
                f"{x['proof_salt_bytes']} B, leaf salt {x['leaf_salt_bytes']} B")
        if "fs_stream_extra_bytes" in x:
            line += f", Fiat-Shamir stream extra {x['fs_stream_extra_bytes']} B"
        print(line)
    if "upstream" in h:
        u = h["upstream"]
        print(f"  baselines upstream: {u['pin']}" +
              (f", checkout {u['checkout']}" if "checkout" in u else ""))
    if "binius" in h:
        b = h["binius"]
        print(f"  binius64: Fiat-Shamir {b['fiat_shamir']['name']} "
              f"({b['fiat_shamir']['challenger']}, StdDigest = {b['fiat_shamir']['digest']}), "
              f"Merkle {b['merkle']['name']} (HASH={b['merkle']['suite']})")


def main(argv):
    if argv[:1] == ["--manifest"] and len(argv) == 2:
        manifest(argv[1])
        return
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--profile", required=True, choices=sorted(EXPECTED))
    ap.add_argument("--report")
    ap.add_argument("--log", action="append", default=[])
    ap.add_argument("--baselines-build")
    ap.add_argument("--baseline", action="append", default=[])
    ap.add_argument("--expect", action="append", default=[])
    ap.add_argument("--upstream-pin")
    ap.add_argument("--upstream-checkout")
    ap.add_argument("--binius-tree")
    ap.add_argument("--binius-merkle")
    a = ap.parse_args(argv)
    report = pathlib.Path(a.report).read_text() if a.report else None
    logs = [(n, pathlib.Path(p).read_text()) for n, p in pairs(a.log, "--log")]
    expect = {n: [c for c in v.split(",") if c] for n, v in pairs(a.expect, "--expect")}
    if a.upstream_checkout and not a.upstream_pin:
        raise SystemExit("--upstream-checkout needs --upstream-pin")
    upstream = (a.upstream_pin, a.upstream_checkout) if a.upstream_pin else None
    if bool(a.binius_tree) != bool(a.binius_merkle):
        raise SystemExit("--binius-tree and --binius-merkle go together")
    binius = (a.binius_tree, a.binius_merkle) if a.binius_tree else None
    out = check(a.profile, report, logs, a.baselines_build,
                pairs(a.baseline, "--baseline"), expect, upstream, binius)
    json.dump(out, sys.stdout, indent=1)
    sys.stdout.write("\n")
    if not out["ok"]:
        for e in out["errors"]:
            print(f"hash_check: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main(sys.argv[1:])
