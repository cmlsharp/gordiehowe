# Performance gate

Every declaration of GordieHowe has a time budget: 10 s of elaboration and 5 s of kernel check.
The budgets, the allowlist's figures and the base profile's are seconds on the gate host at 16
profiler jobs with no other build running.
A declaration over budget fails the gate unless `perf_allowlist.tsv` lists it with a reason.
The allowlist is sorted by cost, max(elab_s, kernel_s), descending. Its top entries are the
performance backlog: work on them first.

The budget covers the import closures of `GordieHowe` and `GordieHoweCerts`, the hand-written
modules of the certificate library included (the applications' frontends, honest strategies and
per-program facts). Outside it are the generated modules (`GordieHoweCerts.Generated.*`) and the
certificate-check modules (`GordieHoweCheck.*`, and `Circuit.Load` and `Circuit.LoadNative`, which
define the checks): their cost is the build's (stage 0, `build_times.txt`). The rule is
`perf_exempt` in `scripts/cert_boundary.py`. Profiling a module of `GordieHoweCerts` needs that
library built: `scripts/check.sh --perf` profiles them only with `--certs`, and `perf_profile.sh`
skips them, with a note, when their oleans are missing or with `--no-certs`.

## Running

After `lake build`, from `formal/`:

    scripts/perf_profile.sh develop -o /tmp/profile.tsv    # modules changed since develop's merge base
    scripts/perf_profile.sh --dependents --roles /tmp/roles.tsv develop -o /tmp/profile.tsv
                                                           # the same with their dependents
    scripts/perf_profile.sh GordieHowe.Model.Quantum.Interactive.BaseShiftExt   # named modules
    python3 -I scripts/perf_gate.py /tmp/profile.tsv --base audit/perf_baseline.tsv --roles /tmp/roles.tsv

or both in one step at the end of the check:

    scripts/check.sh --perf develop                 # a gate failure fails the check
    scripts/check.sh --perf develop --perf-report   # report only, exit status unchanged
    scripts/check.sh --perf develop --perf-changed-only   # without the dependents

## Which modules are profiled

`check.sh --perf REF` profiles the modules whose files changed since REF's merge base and their
dependents:

- the direct importers of a changed module, and
- the transitive importers of a changed module that have a row in `perf_baseline.tsv`,

in both libraries (GordieHoweCerts' with `--certs`), less the modules outside the budget. A
declaration can slow down in a file the diff does not touch, when a definition it uses changes;
the dependents are where that shows. The set is a function of the diff, the tree's import graph and
the committed `perf_baseline.tsv`: no timing of the run enters, and two runs on one tree profile
the same modules. To see it without running Lean:

    scripts/perf_profile.sh --dependents --estimate develop

prints one line per module, sorted (role, module, distance to a changed module, the next module on
the shortest import chain, base rows, base seconds), and an estimated wall time. In a tree that is
not a git checkout, `--changed-from FILE` takes the changed files from FILE (the output of
`git diff --name-only`) in place of REF. `--roles FILE` records which profiled modules are changed
and which are dependents; `perf_gate.py --roles FILE` reads it.

## The regime

The profiler runs 16 `lean` processes at once, 4 threads each, whatever the build's
`PQ_LAKE_JOBS` (`PROFILE_JOBS` and `PROFILE_THREADS` in `scripts/perf_profile.py`). At 16 jobs a
declaration costs the same whatever is profiled with it: on the gate host (128 cores, 256
threads), the declarations of 54 modules cost within 0.6% (median; 4% at the 90th percentile) of
each other whether those modules were profiled alone, among 500 modules or among all 2,074. At
64 jobs they do not: the same declarations cost 3% more among the 54 and 11% more among the
2,074 (median; 30% at the 90th percentile), and over the library elaboration costs 8% and kernel
checks 14% more than at 16 jobs. So a budget, a base row and an entry's row are one quantity only
at a fixed job count. Wall times at 16 jobs on that host: 54 modules in 40 s (the slowest module,
`MLDSAW1H3Assembly`, takes 38 s), 500 in 174 s, the 2,074 of `--all` in 507 s.

Every profile starts with `#` lines that record its regime:

    # perf_profile 1
    # regime: jobs=16 threads=4 modules=54 selection=changed+dependents changed=13 dependents=41 base=fdaf9bf04
    # host: cpus=256 runnable_before=1 runnable_after=2 other_lean_before=0 other_lean_after=0 other_lake_before=0 other_lake_after=0 load1_before=0.42 load1_after=9.80
    # run: wall_s=38 lean=leanprover/lean4:v4.34.0 head=254eed5ff date=2026-11-12T04:31:02

`selection` is `changed`, `changed+dependents`, `all` or `named`; `base` is the revision of the
diff, or `file:NAME` with `--changed-from`; `head` is the tree's commit (`+` when a tracked file
differs from it), or `not-a-git-checkout`. `runnable_…`, `other_lean_…` and `other_lake_…` are
the runnable threads and the `lean` and `lake` processes of any user on the host, less the
profiler's own (itself, its ancestors, which include the `lake env` it runs under, and its
descendants, found by parent process and not by name), read before the first job starts and
again after the last one ends, with the 1-minute load average; the host is not named. Scripts
that read a profile skip the `#` lines; a file without them (the base profile until its next
reseed) is read as before.

- **Another job count.** `-j N` profiles at N jobs, for experiments, and the profile records it.
  `perf_gate.py` refuses a profile that is not at 16 jobs of 4 threads, and a base profile whose
  regime is not the profile's (exit 2), unless `--allow-regime-mismatch`. A file without `#`
  lines is taken as 16 jobs of 4 threads, and the gate prints that it did so.
- **A busy host.** The host is busy when more than 8 threads are runnable or any other `lean`
  or `lake` process exists (`BUSY_RUNNABLE`, `BUSY_FOREIGN_LEAN`, `BUSY_FOREIGN_LAKE`), before
  the profile starts or after it ends: either sample is enough, so a build that starts during
  the profile shows at its end. The profiler says so, the gate warns, and the gate's last line
  ends with `host busy during the profile (other lean processes B before and A after, other lake
  processes B before and A after, runnable threads B before and A after)`. The result stands;
  profile again on a quiet host before relying on a row near its budget or over the margin.
  Seen: another `lake build`, or a series of `lake env lean` compiles, alive at either sample,
  even between two of its `lean` runs, because its `lake` process is counted. Not seen: a
  compile that starts and ends inside the profile with no `lake` parent alive at either sample,
  and work that is neither `lean` nor `lake` unless it leaves more than 8 threads runnable at a
  sample.

`perf_profile.sh` elaborates each module with `lean --json -Dprofiler=true` (several at once, under
the memory cap of `scripts/lake.sh`) and writes one row per source command: declaration, module,
elab_s, kernel_s, interp_s. A command that declares a name has that name, qualified by its
namespaces; its docstring, attributes and `… in` prefixes (`omit`, `include`, `open`,
`set_option`, `variable`, `attribute`, on one line or several, stacked) are part of it. A command
that declares no name (an anonymous instance, `example`, `variable`, `local notation`, `mutual`)
is labelled `<…>` with the first 60 characters of its text, and `#2`, `#3`, … when the same label
occurs again in the module, in source order. Such a label is a key like a name: budgeted,
allowlisted, compared with the base profile and kept in it. It changes when the command's first
60 characters change, and an ordinal shifts when an identical command is added or removed before
it in the module; the gate then shows the old key as gone and the new one as having no base row.
A command starts at a line that begins in column 0, so a declaration indented under a preceding
command (`open X` followed by an indented `theorem`) takes that command's label and its time.

kernel_s is Lean's `type checking`; elab_s is everything else (header,
body, tactics, instances, attributes, linters, compilation); interp_s is the part of elab_s spent in
Lean's IR interpreter (`#eval`, evaluation-based `decide`, `native_decide`). The row
`<unattributed>` of a module holds the time no message carries (Lean's cumulative totals, less
import and initialization, minus the messages); the gate fails a module whose residual is over
budget.

The profiler runs with `profiler.threshold=0`, so every timed step is reported. Lean applies the
threshold to each step, not to each command: at 1 ms, a proof made of many sub-millisecond steps
(`norm_num` on large literals, instance search) is reported nowhere, and its declaration looks
several times cheaper than it is. At 1 ms a quarter of the library's time was unattributed
(1,421 of 5,737 s; WeightTail44's tail lemmas showed 0.13 s each for 0.6 s, and
`sqrt_add_sqrt_le_of_le` 9.7 s for 12 s); at 0 the residual is under 0.4 s per module. It costs
about 12% more wall time and up to 9 MB of raw output per module. `--threshold-ms` only sets
`--trace`'s threshold.

`perf_profile.sh --trace` runs `trace.profiler` instead, which shows the nested trace of a slow
declaration. Use it to diagnose one declaration, not for budgets: it inflates elaboration by up to
ten times, and its trace allocations count as heartbeats.

The gate (`perf_gate.py`) fails on

- a declaration over budget that is not allowlisted;
- an allowlisted declaration whose cost exceeds its entry's budget_s (1.25 times the recorded
  cost when seeded), i.e. one that got more than 25% slower;
- an allowlisted declaration over a budget its entry was not over (an entry for slow elaboration
  does not cover a new slow kernel check);
- a module whose profile timed out (900 s by default);
- a module whose `<unattributed>` residual is over budget.

The rules are the same for changed modules and dependents, with one exception: a declaration of a
dependent that is over budget and not allowlisted fails only if it is also slower than the base
profile by the margin (below). If it is not, it was at the budget before the diff, and the gate
warns: fix it or allowlist it.

It reports, without failing, allowlisted declarations now under budget or absent from the profile
(remove or rename their entries), modules whose profile failed to elaborate, and an unsorted
allowlist. With `--base`, it prints the timing delta per declaration against a base profile,
elaboration and kernel each on its own: the largest regressions and improvements (`--top` of each,
15 by default). A declaration is slower by the margin when its elaboration or its kernel check
exceeds the base's by 0.5 s and by 10% of the base's (`--margin-s`, `--margin-rel`). Every such
declaration is listed at the end of the output, those of changed modules and those of dependents
apart, none left out, and the gate's last line counts both. They are a report and do not fail the
gate: record them in the entry, or fix them. Two profiles of one tree differ by less than the
margin in GordieHowe (666 declarations of 0.5 s and more, each profiled twice at 64 jobs: at most
8.2% and 0.16 s); the kernel checks of concrete tables in GordieHoweCerts differ by up to 16%
(4 of 234 over the margin), so a line for one of those can be noise: profile it again.

`audit/perf_baseline.tsv` is the base profile (rows of 0.5 s and more; a declaration it lacks
counts as at most 0.5 s there, and its line in the list of slower declarations says `no base
row`). `perf_gate.py PROFILE --roles ROLES --update-baseline audit/perf_baseline.tsv` replaces
the profiled modules' rows, the changed modules' and the dependents', after a merge. The file is
named explicitly: the gate writes a base profile only where told, and `--estimate`, `--list` and a
comparison write nothing in the tree. A profile that fails the gate does not update the base
profile: the gate says so and writes nothing, because a base that held failing rows would excuse
them in later entries through the dependents' rule. `--allow-failures` updates it anyway, for a
deliberate reseed. The base profile keeps its `#` lines through an update, and takes those of a
full profile when it has none.

A profile of the whole library (`perf_profile.sh --all`, role `all`) has no diff. The gate prints
`full profile, no diff: every row is held to its budget, the dependents rule does not apply`, and
lists the declarations slower by the margin under `the full profile`.

Times depend on the host. The budgets and the recorded figures are from the gate host at the
regime above. The cost of GordieHoweCerts' hand-written modules is mostly kernel checks of
concrete tables (`decide +kernel` over a program's data). Compare profiles from one host.

## Adding an allowlist entry

An entry is a reviewed exception. Before adding one, diagnose the declaration
(`set_option diagnostics true`, `perf_profile.sh --trace`); the usual cause is Lean unfolding a
large term to compare two spellings of one type or instance, and the fix is where that type is
defined.

Add a row to `perf_allowlist.tsv` with the columns

    declaration  module  elab_s  kernel_s  budget_s  reason  fix_note

taking elab_s and kernel_s from the profile rounded up to a tenth of a second (a component just
over its budget stays recorded over it) and budget_s as 1.25 times the larger, rounded up to a
tenth of a second. The reason is required (the gate refuses an entry without one): say why the
cost is accepted, e.g. `generated certificate`, `kernel check of a concrete table` (a `decide +kernel`
or native check over a program's data in a hand-written certificate module: the declaration
that holds it, or the instance one of its fields does). `pre-existing` marks entries seeded from
develop and is not a reason for new ones. fix_note records the known
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
