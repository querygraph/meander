#!/bin/sh
# Benchmark the meander counters on this machine.
#
#   bench/run.sh [--rust A-B] [--oxcaml A-B] [--lean A-B] [--threads T] [--label NAME]
#
# Each implementation counts n = A, ..., B, one n per process, and every count is checked
# against the OEIS values in bench/oeis-a005316.txt. Results go to
# bench/results/<host>-<label>.tsv with wall time and peak resident memory (from
# /usr/bin/time). The Lean program prints every value up to n, so its time covers 0..n.
set -eu
ROOT=$(cd "$(dirname "$0")/.." && pwd)
HOST=$(hostname -s)
LABEL=$(date -u +%Y%m%d-%H%M)
THREADS=""
RUST="" OXCAML="" LEAN=""
while [ $# -gt 0 ]; do
  case "$1" in
    --rust) RUST=$2; shift 2 ;;
    --oxcaml) OXCAML=$2; shift 2 ;;
    --lean) LEAN=$2; shift 2 ;;
    --threads) THREADS=$2; shift 2 ;;
    --label) LABEL=$2; shift 2 ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
done
OUT="$ROOT/bench/results/$HOST-$LABEL.tsv"
CPU=$(sysctl -n machdep.cpu.brand_string 2>/dev/null || grep -m1 "model name" /proc/cpuinfo | cut -d: -f2)
CORES=$(sysctl -n hw.ncpu 2>/dev/null || nproc)
MEM=$(( $(sysctl -n hw.memsize 2>/dev/null || echo 0) / 1073741824 ))
T=${THREADS:-$CORES}
{
  echo "# host=$HOST cpu=$CPU logical_cpus=$CORES memory_gb=$MEM threads=$T date=$(date -u +%FT%TZ)"
  echo "# git=$(git -C "$ROOT" rev-parse --short HEAD 2>/dev/null || echo none) (the commit of the checkout running this script)"
  printf "impl\tn\tcount\toeis\tpeak_states\tseconds\tmax_rss_gib\n"
} > "$OUT"

expected() { awk -v n="$1" '!/^#/ && $1 == n { print $2 }' "$ROOT/bench/oeis-a005316.txt"; }

run() { # impl n command...
  impl=$1; n=$2; shift 2
  tmp=$(mktemp)
  /usr/bin/time -l "$@" > "$tmp.out" 2> "$tmp.err"
  rss=$(awk '/maximum resident set size/ { printf "%.2f", $1 / 1073741824 }' "$tmp.err")
  secs=$(awk '/ real / { print $1 }' "$tmp.err")
  line=$(grep -v '^#' "$tmp.out" | awk -v n="$n" '$1 == n' | tail -1)
  count=$(echo "$line" | cut -f2)
  peak=$(echo "$line" | cut -f3)
  exp=$(expected "$n")
  ok=$([ "$count" = "$exp" ] && echo ok || echo "MISMATCH($exp)")
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$impl" "$n" "$count" "$ok" "${peak:--}" "$secs" "$rss" | tee -a "$OUT"
  rm -f "$tmp" "$tmp.out" "$tmp.err"
}

range() { seq "${1%-*}" "${1#*-}"; }

if [ -n "$LEAN" ]; then
  for n in $(range "$LEAN"); do run lean "$n" "$ROOT/.lake/build/bin/meanders" "$n"; done
fi
if [ -n "$RUST" ]; then
  for n in $(range "$RUST"); do
    run rust "$n" "$ROOT/rust/target/release/meanders-rs" "$n" --from "$n" --threads "$T"
  done
fi
if [ -n "$OXCAML" ]; then
  for n in $(range "$OXCAML"); do
    run oxcaml "$n" "$ROOT/oxcaml/_build/default/bin/meanders_ox.exe" "$n" --from "$n" --threads "$T"
  done
fi
echo "wrote $OUT"
