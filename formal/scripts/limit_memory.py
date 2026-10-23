#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Run a command with a sampled aggregate RSS limit (macOS, or Linux without a systemd user manager).

PQ_MEM_MAX accepts bytes or a K/M/G suffix (default 96G). All descendants inherit
the child's process group. This bounds resident memory at one-second intervals;
unlike the Linux cgroup wrapper, it cannot prohibit swap or transient overshoot.
"""

import os
import re
import signal
import subprocess
import sys


def main():
    value = os.environ.get("PQ_MEM_MAX", "96G")
    match = re.fullmatch(r"(\d+)([KMG]?)", value.upper())
    if not match or int(match[1]) == 0:
        sys.exit("PQ_MEM_MAX must be a positive byte count, optionally suffixed K, M, or G")
    limit = int(match[1]) * 1024 ** ("KMG".find(match[2]) + 1 if match[2] else 0)
    child = subprocess.Popen(sys.argv[1:], start_new_session=True)

    def stop_group(signum, _frame=None):
        try:
            os.killpg(child.pid, signum)
        except ProcessLookupError:
            pass

    def interrupted(signum, _frame):
        stop_group(signal.SIGKILL)
        child.wait()
        sys.exit(128 + signum)

    signal.signal(signal.SIGINT, interrupted)
    signal.signal(signal.SIGTERM, interrupted)
    try:
        while child.poll() is None:
            snapshot = subprocess.check_output(
                ["/bin/ps", "-axo", "pgid=,rss="], text=True
            )
            rss = sum(
                int(fields[1]) * 1024
                for line in snapshot.splitlines()
                if len(fields := line.split()) == 2 and int(fields[0]) == child.pid
            )
            if rss > limit:
                print(f"lake: process group RSS exceeds PQ_MEM_MAX={value}; stopping", file=sys.stderr)
                stop_group(signal.SIGKILL)
                child.wait()
                return 137
            try:
                child.wait(timeout=1)
            except subprocess.TimeoutExpired:
                pass
        return child.returncode if child.returncode >= 0 else 128 - child.returncode
    finally:
        if child.poll() is None:
            stop_group(signal.SIGKILL)
            child.wait()


if __name__ == "__main__":
    sys.exit(main())
