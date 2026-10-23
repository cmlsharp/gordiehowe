#!/usr/bin/env bash
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0
#
# Exports every held-out program (heldout_export) and builds its generated
# Lean modules, one Lake build per module, recording pass, fail, timeout or
# out-of-memory with the wall time and the peak memory of each.
#
#   run_heldout.sh --lean FORMAL [--export BIN | --exports DIR] --out OUT
#                  [--jobs 2] [--timeout 600] [--mem 120G] [--only A,B]
#                  [--commit C]
#
#   --lean FORMAL   a Lean tree (the repository's formal/ with its .lake
#                   built): the exports are copied into
#                   FORMAL/GordieHowe/Generated/Heldout/, replacing what is
#                   there
#   --export BIN    the heldout_export executable (build/bench/heldout_export);
#                   the run writes OUT/export/ and OUT/export.log
#   --exports DIR   exports written earlier (a directory holding
#                   GordieHowe/Generated/Heldout/), in place of --export
#   --out OUT       the results: OUT/results.tsv (one line per module),
#                   OUT/logs/<module>.log, OUT/summary.txt
#   --jobs J        modules built at once (default 2)
#   --timeout S     each module's cap in seconds (default 600)
#   --mem M         each module's memory cap, systemd's MemoryMax (default
#                   120G; swap off)
#   --only A,B      only the Lean configuration names A, B
#                   (MerkleSha256.Depth4, ...)
#
# The modules of one configuration build in the order of their imports: a
# module starts once each generated module it imports finished, and is
# recorded as skipped when one of them did not pass, so a failure is not
# rebuilt by its dependents. Each build runs as
#   timeout -k 10 S systemd-run --user --scope -p MemoryMax=M
#     -p MemorySwapMax=0 /usr/bin/time -f '%e %M' lake build <module>
# and its status is pass (exit 0), timeout (killed at S), oom (killed at
# the memory cap, or a peak within 3% of it) or fail (the first error line
# is recorded). Lake comes from $ELAN_HOME/bin (default ~/.elan). The
# script waits only on the pids it started.

set -u
lean="" export_bin="" exports="" out="" jobs=2 tmo=600 mem=120G only="" commit=unknown
while (($#)); do
  case "$1" in
    --lean) lean=$2; shift 2 ;;
    --export) export_bin=$2; shift 2 ;;
    --exports) exports=$2; shift 2 ;;
    --out) out=$2; shift 2 ;;
    --jobs) jobs=$2; shift 2 ;;
    --timeout) tmo=$2; shift 2 ;;
    --mem) mem=$2; shift 2 ;;
    --only) only=$2; shift 2 ;;
    --commit) commit=$2; shift 2 ;;
    *) echo "unknown argument $1" >&2; exit 2 ;;
  esac
done
if [[ -z $lean || -z $out || ( -z $export_bin && -z $exports ) ]]; then
  sed -n '7,20p' "$0" >&2
  exit 2
fi
mkdir -p "$out/logs"
out=$(cd "$out" && pwd)
lean=$(cd "$lean" && pwd)

# The exports.
if [[ -n $export_bin ]]; then
  exports="$out/export"
  rm -rf "$exports"
  timeout 1800 "$export_bin" --dir "$exports" --commit "$commit" > "$out/export.log" 2>&1
  echo "export exit $?" >> "$out/export.log"
fi
src="$exports/GordieHowe/Generated/Heldout"
dst="$lean/GordieHowe/Generated/Heldout"
[[ -d $src ]] || { echo "no exports in $src" >&2; exit 1; }
rm -rf "$dst"
mkdir -p "$dst"
cp -r "$src/." "$dst/"
# Lake's outputs of earlier exports, so every module is checked afresh.
rm -rf "$lean/.lake/build/lib/lean/GordieHowe/Generated/Heldout" \
  "$lean/.lake/build/ir/GordieHowe/Generated/Heldout"

# The configurations: directories holding Program.lean.
configs=()
while IFS= read -r p; do
  d=${p%/Program.lean}
  name=${d#"$lean/GordieHowe/Generated/Heldout/"}
  name=${name//\//.}
  name=${name%.ROMParams}
  if [[ -n $only && ",$only," != *",$name,"* ]]; then continue; fi
  configs+=("$d")
done < <(find "$dst" -name Program.lean | sort)

modname() {
  local f=${1#"$lean/"}
  f=${f%.lean}
  echo "${f//\//.}"
}

results="$out/results.tsv"
printf 'module\tstatus\twall_s\tpeak_gb\tnote\n' > "$results"

# Builds module M, records its line.
build_one() {
  local m=$1 log="$out/logs/$1.log" t0 t1 rc wall peak st note
  t0=$(date +%s.%N)
  (cd "$lean" && PATH=${ELAN_HOME:-$HOME/.elan}/bin:$PATH timeout -k 10 "$tmo" \
    systemd-run --user --scope --quiet -p MemoryMax="$mem" -p MemorySwapMax=0 \
    /usr/bin/time -o "$log.time" -f '%e %M' lake build "$m") > "$log" 2>&1
  rc=$?
  t1=$(date +%s.%N)
  wall=$(echo "$t1 - $t0" | bc)
  peak=0
  [[ -f $log.time ]] && peak=$(awk 'END {printf "%.2f", $2 / 1048576}' "$log.time")
  local cap
  cap=$(echo "$mem" | sed -E 's/G$//')
  note=""
  if ((rc == 0)); then
    st=pass
  elif ((rc == 124 || rc == 137)) && (($(echo "$wall >= $tmo - 2" | bc))); then
    st=timeout
  elif grep -qE 'signal 9|Killed|out of memory|oom' "$log" ||
       (($(echo "$peak >= 0.97 * $cap" | bc))); then
    st=oom
  else
    st=fail
    note=$(grep -m1 -oE 'error: .{0,240}' "$log" | tr '\t\n' '  ')
  fi
  printf '%s\t%s\t%.1f\t%s\t%s\n' "$m" "$st" "$wall" "$peak" "$note" > "$out/logs/$m.result"
}

# The generated imports of the module file F that lie in its configuration.
imports_of() {
  grep -oE '^public import GordieHowe\.Generated\.Heldout\.[A-Za-z0-9_.]+' "$1" |
    awk '{print $3}'
}

# Builds the modules of configuration directory D in dependency order, at
# most JOBS at once: a module starts once every generated import it has in
# D finished; it is skipped when one of them did not pass.
run_config() {
  local d=$1 f m i
  local -a mods=() files=()
  local -A st=() deps=()
  while IFS= read -r f; do
    m=$(modname "$f")
    mods+=("$m")
    files+=("$f")
    st[$m]=pending
  done < <(find "$d" -name '*.lean' | sort)
  for i in "${!mods[@]}"; do
    deps[${mods[$i]}]=$(imports_of "${files[$i]}" | while read -r x; do
      [[ -n ${st[$x]+y} ]] && echo "$x"; done | tr '\n' ' ')
  done
  local -a running=()
  local left=${#mods[@]}
  while ((left > 0)); do
    local started=0
    for m in "${mods[@]}"; do
      [[ ${st[$m]} == pending ]] || continue
      local ready=1 bad=0 x
      for x in ${deps[$m]}; do
        case ${st[$x]} in
          pass) ;;
          pending|running) ready=0 ;;
          *) bad=1 ;;
        esac
      done
      if ((bad)); then
        printf '%s\tskipped\t0\t0\ta generated import did not pass\n' "$m" >> "$results"
        st[$m]=skipped
        ((left--))
        continue
      fi
      ((ready)) || continue
      ((${#running[@]} < jobs)) || continue
      build_one "$m" &
      running+=("$m:$!")
      st[$m]=running
      started=1
    done
    # Collect the finished builds; wait for one when none finished.
    local -a still=()
    local any=0 e
    for e in "${running[@]}"; do
      m=${e%%:*}
      if [[ -f $out/logs/$m.result ]]; then
        wait "${e##*:}"
        cat "$out/logs/$m.result" >> "$results"
        st[$m]=$(cut -f2 "$out/logs/$m.result")
        rm -f "$out/logs/$m.result"
        ((left--))
        any=1
      else
        still+=("$e")
      fi
    done
    running=("${still[@]}")
    if ((!any && !started && ${#running[@]} > 0)); then
      local pids=()
      for e in "${running[@]}"; do pids+=("${e##*:}"); done
      wait -n "${pids[@]}" 2>/dev/null
    fi
  done
}

for d in "${configs[@]}"; do
  echo "== $(modname "$d")" >&2
  run_config "$(dirname "$d/Program.lean")"
done

awk -F'\t' 'NR > 1 {n[$2]++} END {for (s in n) printf "%s %d\n", s, n[s]}' "$results" |
  sort > "$out/summary.txt"
cat "$out/summary.txt"
