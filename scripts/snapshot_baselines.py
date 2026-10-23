#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Snapshot a committed standalone or imported Longfellow baseline tree.

run_bench.sh builds and runs the baselines from a snapshot of their committed tree
(comparisons/longfellow, or a standalone longfellow-baselines checkout) with upstream/ at its
pinned commit: a git repository of its own, so that common/build.sh's `nix develop ./common`
copies only its tracked files, never the build directory inside it. The snapshot's name carries
the baseline tree's id, so commits outside the baselines reuse it.

    snapshot_baselines.py SOURCE --info            the commit, tree and upstream pin (JSON)
    snapshot_baselines.py SOURCE DESTINATION       create or check the snapshot
"""

import argparse
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args]).decode().strip()


def source_info(source, revision="HEAD"):
    source = source.resolve()
    root = Path(git(source, "rev-parse", "--show-toplevel"))
    prefix = git(source, "rev-parse", "--show-prefix").rstrip("/")
    commit = git(root, "rev-parse", f"{revision}^{{commit}}")
    tree = git(root, "rev-parse", f"{commit}:{prefix}" if prefix else f"{commit}^{{tree}}")
    upstream_path = f"{prefix}/upstream" if prefix else "upstream"
    entry = git(root, "ls-tree", commit, "--", upstream_path).split()
    if len(entry) != 4 or entry[0] != "160000":
        raise ValueError(f"Baseline upstream is not a pinned submodule: {source}")
    return root, prefix, {"source_commit": commit, "source_tree": tree,
                          "upstream_commit": entry[2]}


def snapshot(source, destination, revision="HEAD"):
    root, prefix, info = source_info(source, revision)
    if destination.exists():
        saved = json.loads((destination / "source_info.json").read_text())
        if (saved["source_tree"], saved["upstream_commit"]) != (
                info["source_tree"], info["upstream_commit"]):
            raise ValueError(f"Existing baseline snapshot has different inputs: {destination}")
        # The build directory inside the snapshot is untracked; a tracked change is not.
        if git(destination, "status", "--porcelain", "--untracked-files=no"):
            raise ValueError(f"Existing baseline snapshot is dirty: {destination}")
        return saved
    if not (source / "upstream" / ".git").exists():
        raise ValueError(f"{source / 'upstream'} is not checked out "
                         "(git submodule update --init --recursive)")
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=destination.name + ".tmp-", dir=destination.parent))
    try:
        treeish = f"{info['source_commit']}:{prefix}" if prefix else info["source_commit"]
        archive = subprocess.check_output(["git", "-C", str(root), "archive", "--format=tar", treeish])
        with tarfile.open(fileobj=io.BytesIO(archive)) as stream:
            stream.extractall(temporary, filter="data")
        upstream = temporary / "upstream"
        if upstream.exists():
            upstream.rmdir()  # git archive emits only an empty directory for a gitlink.
        subprocess.run(["git", "init", "-q", str(temporary)], check=True)
        subprocess.run(["git", "clone", "-q", "--no-checkout", "--dissociate",
                        str(source / "upstream"), str(upstream)], check=True)
        subprocess.run(["git", "-C", str(upstream), "checkout", "-q", "--detach",
                        info["upstream_commit"]], check=True)
        # Register the local clone as a submodule with the public upstream URL.
        (temporary / ".gitmodules").write_text(
            '[submodule "upstream"]\n\tpath = upstream\n'
            '\turl = https://github.com/google/longfellow-zk.git\n')
        (temporary / "source_info.json").write_text(json.dumps(info, indent=2) + "\n")
        subprocess.run(["git", "-C", str(temporary), "add", "--all"], check=True,
                       stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        subprocess.run(["git", "-C", str(temporary), "-c", "user.name=GordieHowe reproduction",
                        "-c", "user.email=repro@invalid.example", "commit", "-q", "-m",
                        f"Baseline snapshot of {info['source_tree']}"], check=True)
        temporary.rename(destination)
        return info
    except BaseException:
        shutil.rmtree(temporary)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path, nargs="?")
    parser.add_argument("--revision", default="HEAD")
    parser.add_argument("--info", action="store_true")
    args = parser.parse_args()
    if args.info:
        info = source_info(args.source, args.revision)[2]
    else:
        if args.destination is None:
            parser.error("destination is required unless --info is given")
        info = snapshot(args.source.resolve(), args.destination.resolve(), args.revision)
    print(json.dumps(info, sort_keys=True))


if __name__ == "__main__":
    main()
