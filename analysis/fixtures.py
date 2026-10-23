# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
"""Benchmark-run fixtures of the script tests.

Each fixtures/<run>.tar.xz holds the files of one benchmark run directory that the tests read
(<run>/<profile>/...), as the run wrote them; fixtures/SOURCES.json records their origin, the
paths stripped of the build directory's prefix, and their checksums. The one archive is ROM_RUN. run(name) extracts an archive once per process into a temporary directory
and returns <tmp>/<run>.
"""

import atexit
import pathlib
import shutil
import tarfile
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
# The ROM run (repro.sh's rom stage): its narrow/ directory, the files the tests read.
ROM_RUN = "2026-10-19-rom-run"
_ROOT = []


def run(name):
    """The extracted run directory NAME (benchmarks/<name> in the source repository)."""
    if not _ROOT:
        _ROOT.append(pathlib.Path(tempfile.mkdtemp(prefix="pq-script-fixtures-")))
        atexit.register(shutil.rmtree, _ROOT[0], True)
    out = _ROOT[0] / name
    if not out.is_dir():
        with tarfile.open(HERE / "fixtures" / f"{name}.tar.xz") as archive:
            archive.extractall(_ROOT[0], filter="data")
    return out
