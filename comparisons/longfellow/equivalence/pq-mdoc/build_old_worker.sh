#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

# Builds the old side of the pq-mdoc equivalence run.
#
# usage: equivalence/pq-mdoc/build_old_worker.sh OLD_TREE BUILD_DIR HASH384
#
# OLD_TREE: a `git archive b7dfdb34 lib flake.nix flake.lock` of the fork.
# Builds the fork's pq_mdoc_baseline_test with the fork's recipe
# (equivalence/old_build.sh), then compiles old_worker.cc with that test's
# own compile command (its flags, defines and precompiled header) and links
# it with the test's own link command, less the gtest main
# (testing_main), into OLD_TREE/BUILD_DIR/pq_mdoc_old_worker.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
tree=$1
bdir=$2
h384=$3
"$root/equivalence/old_build.sh" "$tree" "$bdir" "$h384" pq_mdoc_baseline_test
cd "$tree/$bdir"
nix --extra-experimental-features 'nix-command flakes' develop "$tree" --command bash -c "
set -euo pipefail
export NIX_ENFORCE_NO_NATIVE=0
python3 - <<'PY'
import json, re, shlex, subprocess
root = '$root'
for e in json.load(open('compile_commands.json')):
    if e['file'].endswith('gordiehowe/examples/pq_mdoc_baseline_test.cc'):
        cmd, d = e['command'], e['directory']
        break
args = shlex.split(cmd)
out = 'pq_mdoc_old_worker.o'
i = args.index('-o'); args[i + 1] = '$tree/$bdir/' + out
j = args.index('-c'); args[j + 1] = root + '/equivalence/pq-mdoc/old_worker.cc'
args.insert(1, '-I' + root + '/common')
print('compile:', ' '.join(args[:3]), '...')
subprocess.run(args, cwd=d, check=True)
link = open('gordiehowe/examples/CMakeFiles/pq_mdoc_baseline_test.dir/link.txt').read().split()
link = ['$tree/$bdir/' + out if a.endswith('pq_mdoc_baseline_test.cc.o') else a
        for a in link if 'testing_main' not in a]
k = link.index('-o'); link[k + 1] = '$tree/$bdir/pq_mdoc_old_worker'
subprocess.run(link, cwd='gordiehowe/examples', check=True)
print('linked', '$tree/$bdir/pq_mdoc_old_worker')
PY
"
echo BUILD_DONE
