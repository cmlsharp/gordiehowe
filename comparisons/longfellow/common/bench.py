#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""The bench harness of every baseline.

usage: common/bench.py SPEC.json OUTDIR

SPEC.json:
  {"name": "...", "warmup": 1, "trials": 9, "cpu": "100" or null,
   "busy_exe_prefixes": ["/data/..."] or null, "busy_cpu_pct": 50 or null,
   "busy_wait_s": 3600, "busy_cpus": "0-127", "setup_jobs": 4,
   "cases": [{"label": "...", "argv": ["path", "arg", ...],
              "env": {"K": "V"}, "cwd": "dir" or null,
              "build_info": "build/build_info.txt" or null}]}

Paths in argv[0], cwd and build_info are relative to the repository root
unless absolute.  Every case is a worker process (common/bench_worker.h, or
the fork's bench_worker.h for the equivalence runs): the harness starts
them, lets them build their circuits and witnesses unpinned, at most
`setup_jobs` (default 4) at a time, then pins each (all threads) to `cpu`
with taskset, if given.  It
runs `warmup` unrecorded trials per case, then `trials` rounds of one trial
per case, the order rotating by one case per round.  One trial runs at a
time.

The harness holds an exclusive flock on /tmp/longfellow-baselines-bench.lock
(LFB_BENCH_LOCK overrides the path) for the whole run, worker setup
included, so two runs from any checkout of this repository on one host
never overlap.  Before the warm-up
and before each round it waits (polling every 30 s, at most busy_wait_s in
all, lock wait included) while any process other than its workers runs an
executable under one of busy_exe_prefixes: other people's benchmark trees on
a shared host.  Compilers live elsewhere, so their builds do not count;
with busy_cpu_pct set it also waits while any other process (a build, a
test) uses more than that percentage of a core over a 2-second sample, and
it discards and repeats any round during which everything else on the host
together (from /proc/stat, so processes that exited count too) used more
than that share of one core on average (meta.json lists them).  Both
tests count only the cores busy_cpus (default 0-127): a process counts if
its CPU affinity includes one of them, and the host total sums only their
lines of /proc/stat.  On a 128-core AMD EPYC 9754 host (256 logical
CPUs) the timing pins to a core below 128 and
builds run under `taskset -c 128-255 nice -n 19`, so they do not count.

OUTDIR gets:
  raw.jsonl     one JSON object per recorded trial: case, round, commit_ms,
                prove_ms, prover_ms (= commit + prove), witness_prover_ms
                (= the detail witness + commit + prove, when the worker
                reports a witness time), verify_ms, proof_bytes, ok,
                details (the worker's PQ_DETAIL values)
  summary.tsv   per case: n, then median, min and max of prover_ms,
                witness_prover_ms, verify_ms, proof_bytes and every numeric
                detail
  meta.json     host, CPU, kernel, start and end time and load average,
                the cpufreq governor of `cpu` (or of every CPU without
                one), GLIBC_TUNABLES as the workers inherit it (null:
                unset), upstream and repository commits, the spec, each
                case's build_info and its setup lines (PQ_INFO and the rest)
  <label>.log   each worker's full output
"""
import fcntl
import json
import os
import re
import socket
import statistics
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# One lock for the whole host, shared by every checkout of this repository
# (LFB_BENCH_LOCK overrides it).
LOCK_PATH = os.environ.get("LFB_BENCH_LOCK",
                           "/tmp/longfellow-baselines-bench.lock")


def rel(p):
    return p if p is None or os.path.isabs(p) else os.path.join(ROOT, p)


def git(*args, cwd=ROOT):
    try:
        return subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                              text=True, timeout=30).stdout.strip()
    except Exception as e:  # noqa: BLE001
        return f"unknown ({e})"


def repo_commit():
    c = git("rev-parse", "HEAD")
    dirty = subprocess.run(["git", "diff", "--quiet", "HEAD", "--", ".",
                            ":!upstream"], cwd=ROOT).returncode != 0
    return c + ("-dirty" if dirty else "")


def cpu_model():
    try:
        for line in open("/proc/cpuinfo"):
            if line.startswith("model name"):
                return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return "unknown"


def loadavg():
    try:
        return open("/proc/loadavg").read().strip()
    except OSError:
        return "unknown"


def governors(cpu):
    """The cpufreq governor of each CPU of CPU (a taskset-style list), or of
    every CPU when CPU is None, as "governor: cpus" counts."""
    if cpu is None:
        cpus = sorted(os.sched_getaffinity(0))
    else:
        cpus = sorted(parse_cpus(cpu))
    by = {}
    for c in cpus:
        try:
            g = open(f"/sys/devices/system/cpu/cpu{c}/cpufreq/"
                     "scaling_governor").read().strip()
        except OSError:
            g = "unknown"
        by.setdefault(g, []).append(c)
    return {g: len(cs) for g, cs in by.items()}


def own_pids():
    pids = {os.getpid(), os.getppid()}
    return pids


# The cores whose use counts as busy (spec "busy_cpus", default 0-127).
BUSY_CPUS = set(range(128))


def parse_cpus(text):
    """A taskset-style list such as "0-127" or "0-63,100"."""
    out = set()
    for part in str(text).split(","):
        part = part.strip()
        if "-" in part:
            a, b = part.split("-")
            out.update(range(int(a), int(b) + 1))
        elif part:
            out.add(int(part))
    return out


def on_busy_cpus(pid):
    """Whether PID may run on one of BUSY_CPUS."""
    try:
        return bool(os.sched_getaffinity(pid) & BUSY_CPUS)
    except OSError:
        return False


def cpu_hogs(threshold, mine, sample_s=2.0):
    """Processes outside MINE using more than THRESHOLD percent of one core
    over a SAMPLE_S-second window (from /proc/<pid>/stat utime + stime)."""
    t0 = proc_times(mine)
    time.sleep(sample_s)
    return hogs_between(t0, proc_times(mine), sample_s, threshold)


def host_busy_ticks():
    """CPU ticks BUSY_CPUS have spent busy (their cpuN lines of
    /proc/stat)."""
    total = 0
    for line in open("/proc/stat"):
        name = line.split(maxsplit=1)[0]
        if not (name.startswith("cpu") and name[3:].isdigit()):
            continue
        if int(name[3:]) not in BUSY_CPUS:
            continue
        v = list(map(int, line.split()[1:]))
        total += sum(v) - v[3] - v[4]
    return total


def own_ticks(pids):
    """CPU ticks (utime + stime) of PIDS, the harness and its workers."""
    total = 0
    for pid in pids:
        try:
            f = open(f"/proc/{pid}/stat").read()
            rest = f[f.rindex(")") + 2:].split()
            total += int(rest[11]) + int(rest[12])
        except (OSError, ValueError, IndexError):
            pass
    return total


def proc_times(mine):
    """CPU ticks (utime + stime) of every process outside MINE that may run
    on BUSY_CPUS."""
    out = {}
    for d in os.listdir("/proc"):
        if not d.isdigit() or int(d) in mine:
            continue
        if not on_busy_cpus(int(d)):
            continue
        try:
            f = open(f"/proc/{d}/stat").read()
            rest = f[f.rindex(")") + 2:].split()
            out[int(d)] = int(rest[11]) + int(rest[12])
        except (OSError, ValueError, IndexError):
            pass
    return out


def hogs_between(t0, t1, seconds, threshold):
    """Processes that used more than THRESHOLD percent of a core between the
    snapshots T0 and T1, SECONDS apart; processes that started in between
    count from zero."""
    tick = os.sysconf("SC_CLK_TCK")
    hits = []
    for pid, t in t1.items():
        if True:
            pct = 100.0 * (t - t0.get(pid, 0)) / tick / max(seconds, 1e-3)
            if pct > threshold:
                try:
                    cmd = open(f"/proc/{pid}/cmdline", "rb").read().replace(
                        b"\0", b" ").decode(errors="replace")[:120]
                except OSError:
                    cmd = "?"
                hits.append(f"{pid} {pct:.0f}%: {cmd}")
    return hits


def busy(prefixes, mine):
    hits = []
    for d in os.listdir("/proc"):
        if not d.isdigit() or int(d) in mine:
            continue
        try:
            exe = os.readlink(f"/proc/{d}/exe")
        except OSError:
            continue
        if any(exe.startswith(p) for p in prefixes):
            hits.append(f"{d}: {exe}")
    return hits


class Worker:
    def __init__(self, case, logdir):
        self.label = case["label"]
        env = dict(os.environ)
        env.update({k: str(v) for k, v in case.get("env", {}).items()})
        argv = list(case["argv"])
        argv[0] = rel(argv[0])
        self.log = open(os.path.join(logdir, self.label + ".log"), "w")
        self.log.write("# argv: " + " ".join(argv) + "\n")
        self.log.write("# env: " + json.dumps(case.get("env", {})) + "\n")
        self.p = subprocess.Popen(argv, cwd=rel(case.get("cwd")) or ROOT,
                                  env=env, stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, text=True,
                                  bufsize=1)
        self.setup = []

    def line(self):
        s = self.p.stdout.readline()
        if not s:
            raise RuntimeError(f"{self.label}: worker ended unexpectedly")
        self.log.write(s)
        self.log.flush()
        return s.rstrip("\n")

    def wait_ready(self):
        while True:
            s = self.line()
            if s == "PQ_READY":
                return
            if s.startswith("PQ_"):
                self.setup.append(s)

    def run(self):
        self.p.stdin.write("run\n")
        self.p.stdin.flush()
        details = {}
        while True:
            s = self.line()
            if s.startswith("PQ_DETAIL"):
                for kv in s.split()[1:]:
                    k, v = kv.split("=", 1)
                    try:
                        details[k] = float(v)
                    except ValueError:
                        details[k] = v
            elif s.startswith("PQ_RESULT"):
                f = s.split()
                commit, prove, verify = float(f[1]), float(f[2]), float(f[3])
                r = dict(commit_ms=commit, prove_ms=prove,
                         prover_ms=commit + prove, verify_ms=verify,
                         proof_bytes=int(f[4]), ok=int(f[5]) == 1,
                         details=details)
                # Witness generation + commit + prove, per trial, for a
                # driver that times its witness (the detail "witness").
                w = details.get("witness")
                if isinstance(w, float):
                    r["witness_prover_ms"] = w + commit + prove
                return r

    def stop(self):
        try:
            self.p.stdin.write("stop\n")
            self.p.stdin.close()
        except OSError:
            pass
        for s in self.p.stdout:
            self.log.write(s)
        # The worker's exit status and peak resident set (its whole life),
        # from wait4, within 600 s as Popen.wait's timeout.
        deadline = time.monotonic() + 600
        while True:
            pid, status, ru = os.wait4(self.p.pid, os.WNOHANG)
            if pid != 0:
                break
            if time.monotonic() > deadline:
                raise subprocess.TimeoutExpired(self.p.args, 600)
            time.sleep(0.05)
        rc = os.waitstatus_to_exitcode(status)
        self.p.returncode = rc
        self.maxrss_kb = ru.ru_maxrss
        self.log.write(f"# maxrss_kb {ru.ru_maxrss}\n")
        self.log.write(f"# exit {rc}\n")
        self.log.close()
        return rc


def summarize(rows, labels):
    out = ["case\tmetric\tn\tmedian\tmin\tmax"]
    for lab in labels:
        rs = [r for r in rows if r["case"] == lab]
        metrics = ["prover_ms", "witness_prover_ms", "commit_ms", "prove_ms",
                   "verify_ms", "proof_bytes"]
        dkeys = []
        for r in rs:
            for k, v in r["details"].items():
                if isinstance(v, float) and k not in dkeys:
                    dkeys.append(k)
        for m in metrics + dkeys:
            vals = [r[m] if m in r else r["details"].get(m) for r in rs]
            vals = [v for v in vals if isinstance(v, (int, float))]
            if not vals:
                continue
            out.append(f"{lab}\t{m}\t{len(vals)}\t{statistics.median(vals):.3f}"
                       f"\t{min(vals):.3f}\t{max(vals):.3f}")
    return "\n".join(out) + "\n"


def main():
    spec_path, outdir = sys.argv[1], sys.argv[2]
    spec = json.load(open(spec_path))
    os.makedirs(outdir, exist_ok=True)
    mine = own_pids()
    meta = dict(name=spec.get("name"), host=socket.getfqdn(),
                cpu=cpu_model(), kernel=os.uname().release,
                start=time.strftime("%Y-%m-%dT%H:%M:%S%z"),
                load_start=loadavg(),
                governor_start=governors(spec.get("cpu")),
                glibc_tunables=os.environ.get("GLIBC_TUNABLES"),
                upstream_commit=git("rev-parse", "HEAD", cwd=rel("upstream")),
                repo_commit=repo_commit(), spec=spec, cases={})
    prefixes = spec.get("busy_exe_prefixes") or []
    global BUSY_CPUS
    BUSY_CPUS = parse_cpus(spec.get("busy_cpus", "0-127"))
    budget = float(spec.get("busy_wait_s", 3600))

    # The repository-local lock as well, which earlier versions of this
    # harness took instead.
    local_lock = open(os.path.join(ROOT, ".bench.lock"), "a")
    fcntl.flock(local_lock, fcntl.LOCK_EX)
    lock = open(LOCK_PATH, "a")
    while True:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except OSError:
            if budget <= 0:
                raise RuntimeError("another bench run holds " + LOCK_PATH)
            print("another bench run holds " + LOCK_PATH + ", waiting 30 s",
                  flush=True)
            time.sleep(30)
            budget -= 30

    cpu_pct = spec.get("busy_cpu_pct")

    def wait_idle():
        nonlocal budget
        if not prefixes and cpu_pct is None:
            return
        while True:
            ours = mine | {w.p.pid for w in workers}
            hits = busy(prefixes, ours)
            if cpu_pct is not None:
                hits += cpu_hogs(float(cpu_pct), ours)
            if not hits:
                return
            if budget <= 0:
                raise RuntimeError("busy too long: " + "; ".join(hits))
            print("busy, waiting 30 s:", "; ".join(hits), flush=True)
            time.sleep(30)
            budget -= 30

    workers = []
    # At most setup_jobs workers build their circuits at once.
    setup_jobs = max(1, int(spec.get("setup_jobs", 4)))
    try:
        pending = []
        for c in spec["cases"]:
            if len(pending) == setup_jobs:
                w = pending.pop(0)
                w.wait_ready()
                print(f"ready {w.label}", flush=True)
            workers.append(Worker(c, outdir))
            pending.append(workers[-1])
        for w in pending:
            w.wait_ready()
            print(f"ready {w.label}", flush=True)
        if spec.get("cpu") is not None:
            for w in workers:
                subprocess.run(["taskset", "-a", "-p", "-c", str(spec["cpu"]),
                                str(w.p.pid)], check=True,
                               capture_output=True, timeout=30)
        for c, w in zip(spec["cases"], workers):
            bi = rel(c.get("build_info"))
            meta["cases"][w.label] = dict(
                setup=w.setup,
                build_info=open(bi).read() if bi and os.path.exists(bi)
                else None)
        meta["busy_exe_prefixes"] = prefixes
        meta["busy_cpu_pct"] = cpu_pct
        meta["busy_cpus"] = spec.get("busy_cpus", "0-127")
        wait_idle()
        for _ in range(int(spec.get("warmup", 1))):
            for w in workers:
                r = w.run()
                if not r["ok"]:
                    raise RuntimeError(f"{w.label}: warm-up proof failed")
        rows = []
        raw = open(os.path.join(outdir, "raw.jsonl"), "w")
        k = len(workers)
        discarded = []
        rnd = 0
        retries = 0
        while rnd < int(spec.get("trials", 9)):
            wait_idle()
            ours = mine | {w.p.pid for w in workers}
            t0 = proc_times(ours) if cpu_pct is not None else None
            h0, o0 = host_busy_ticks(), own_ticks(ours)
            start = time.time()
            got = []
            for i in range(k):
                w = workers[(rnd + i) % k]
                r = w.run()
                r.update(case=w.label, round=rnd)
                if not r["ok"]:
                    raise RuntimeError(f"{w.label}: proof failed")
                got.append(r)
            # With busy_cpu_pct, a round during which another process used
            # more than that share of a core (on average over the round) is
            # discarded and run again, at most 20 times in all.
            if t0 is not None:
                secs = time.time() - start
                tick = os.sysconf("SC_CLK_TCK")
                # Everything the host ran besides this harness and its
                # workers, exited processes included, in cores on average.
                other = ((host_busy_ticks() - h0) - (own_ticks(ours) - o0)) \
                    / tick / max(secs, 1e-3)
                hits = hogs_between(t0, proc_times(ours), secs,
                                    float(cpu_pct))
                if other > float(cpu_pct) / 100.0:
                    hits.append(f"other processes: {other:.2f} cores")
                else:
                    hits = []
                if hits:
                    retries += 1
                    discarded.append(dict(round=rnd, hits=hits))
                    print(f"round {rnd} discarded: " + "; ".join(hits),
                          flush=True)
                    if retries > 20:
                        raise RuntimeError("host too busy: 20 rounds discarded")
                    continue
            for r in got:
                rows.append(r)
                raw.write(json.dumps(r) + "\n")
                raw.flush()
                print(f"round {rnd} {r['case']} prover={r['prover_ms']:.1f} "
                      f"verify={r['verify_ms']:.1f} bytes={r['proof_bytes']}",
                      flush=True)
            rnd += 1
        meta["discarded_rounds"] = discarded
        raw.close()
        with open(os.path.join(outdir, "summary.tsv"), "w") as f:
            f.write(summarize(rows, [w.label for w in workers]))
    finally:
        for w in workers:
            if w.p.poll() is None:
                w.stop()
                meta["cases"].setdefault(w.label, {})["maxrss_kb"] = \
                    getattr(w, "maxrss_kb", None)
        meta["end"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
        meta["load_end"] = loadavg()
        meta["governor_end"] = governors(spec.get("cpu"))
        json.dump(meta, open(os.path.join(outdir, "meta.json"), "w"),
                  indent=1)
    print(open(os.path.join(outdir, "summary.tsv")).read())


if __name__ == "__main__":
    main()
