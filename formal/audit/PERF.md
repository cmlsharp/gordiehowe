# Performance gate

Every declaration of GordieHowe has a time budget: 10 s of elaboration and 5 s of kernel check.
A declaration over budget fails the gate unless `perf_allowlist.tsv` lists it with a reason.
The allowlist is sorted by cost, max(elab_s, kernel_s), descending. Its top entries are the
performance backlog: work on them first.

Certificate modules (`GordieHoweCerts*`: the generated modules and every module importing one)
are outside the budget, and so are modules outside GordieHowe's import closure.

## Running

After `lake build`, from `formal/`:

    scripts/perf_profile.sh develop -o /tmp/profile.tsv    # modules changed since develop's merge base
    scripts/perf_profile.sh GordieHowe.Model.Quantum.Interactive.BaseShiftExt   # named modules
    python3 -I scripts/perf_gate.py /tmp/profile.tsv --base audit/perf_baseline.tsv

or both in one step at the end of the check:

    scripts/check.sh --perf develop                 # a gate failure fails the check
    scripts/check.sh --perf develop --perf-report   # report only, exit status unchanged

On a 256-core host, a diff touching 8 modules profiles and gates in 9 to 12 s.

`perf_profile.sh` elaborates each module with `lean --json -Dprofiler=true` (several at once, under
the memory cap of `scripts/lake.sh`) and writes one row per declaration: declaration, module,
elab_s, kernel_s, interp_s. kernel_s is Lean's `type checking`; elab_s is everything else (header,
body, tactics, instances, attributes, linters, compilation); interp_s is the part of elab_s spent in
Lean's IR interpreter (`#eval`, evaluation-based `decide`, `native_decide`). The row
`<unattributed>` of a module holds the steps under the profiler's 1 ms threshold.

`perf_profile.sh --trace` runs `trace.profiler` instead, which shows the nested trace of a slow
declaration. Use it to diagnose one declaration, not for budgets: it inflates elaboration by up to
ten times, and its trace allocations count as heartbeats.

The gate (`perf_gate.py`) fails on

- a declaration over budget that is not allowlisted;
- an allowlisted declaration whose cost exceeds its entry's budget_s (1.25 times the recorded
  cost when seeded), i.e. one that got more than 25% slower;
- an allowlisted declaration over a budget its entry was not over (an entry for slow elaboration
  does not cover a new slow kernel check);
- a module whose profile timed out (900 s by default).

It reports, without failing, allowlisted declarations now under budget or absent from the profile
(remove or rename their entries), modules whose profile failed to elaborate, and an unsorted
allowlist. With `--base`, it prints the timing delta per declaration against a base profile:
the largest regressions and improvements. `audit/perf_baseline.tsv` is the full-library profile
(rows of 0.5 s and more); `perf_gate.py PROFILE --update-baseline` replaces the profiled
modules' rows after a merge.

Times depend on the host and its load. The budgets and the recorded figures are from a
256-core host, 24 modules at once with 4 threads each (`--all -j 24`: the 1,563 modules of
GordieHowe's closure in 289 s, 2026-11-01, develop 6fddacb3). A module profiled alone differs by
about 2% (BaseShiftExt's slowest kernel check: 61.7 s alone, 62.8 s in the full profile).
Compare profiles from one host.

## Adding an allowlist entry

An entry is a reviewed exception. Before adding one, diagnose the declaration
(`set_option diagnostics true`, `perf_profile.sh --trace`); the usual cause is Lean unfolding a
large term to compare two spellings of one type or instance, and the fix is where that type is
defined.

Add a row to `perf_allowlist.tsv` with the columns

    declaration  module  elab_s  kernel_s  budget_s  reason  fix_note

taking elab_s and kernel_s from the profile and budget_s as 1.25 times the larger, rounded up to
a tenth of a second. The reason is required (the gate refuses an entry without one): say why the
cost is accepted, e.g. `generated certificate`, `kernel check of a concrete table`. `pre-existing`
marks entries seeded from develop and is not a reason for new ones. fix_note records the known
cause or the planned fix. Then run `python3 -I scripts/perf_gate.py --sort` to restore the order.

`perf_gate.py PROFILE --seed` adds every offender of a profile with reason `pre-existing`. It
seeded the list from a full profile of develop (`perf_profile.sh --all`).

## Heartbeat ceiling while iterating

`GH_MAX_HEARTBEATS=50000 scripts/lake.sh env lean FILE` compiles with `-DmaxHeartbeats=50000`
instead of Lean's default 200000, so a slow declaration fails in seconds. Agents set it while
iterating. A `set_option maxHeartbeats` in the source overrides it, `lake build` ignores it, and
it does not bound kernel checks (the gate does).

At 50000, 159 declarations of develop (6fddacb3) fail, in 62 of the 1,563 modules: 68 in 23 of
the 162 Model/Quantum modules and 47 in 20 of the 135 Applications/Ring modules. At 100000, 88
fail, in 34 modules. A failure under the ceiling in a file you did not change is one of these;
raise the ceiling for that file, or fix the declaration.
