#!/usr/bin/env bash
# Run a meet-in-the-middle store extension (meanders-rs or meanders_ox --store) gently.
#
#   bench/store-safe.sh BINARY STORE_DIR HORIZON [more flags, e.g. --mem-gb 48 --discard]
#
# Why: on 2026-10-08 Morrobay hung hard (no panic; logging, ssh and ping all stopped) during
# a store run on Apo, an HFS+ SoftRAID RAID 5 of four SATA SSDs in a Thunderbolt enclosure.
# The store then wrote one file per shard, thousands per layer, from 36 threads; file closes on
# Apo stopped completing, and the machine followed. The stores now write a few large files per
# layer and sync every 256 MB. This wrapper adds:
#   - fewer workers than hardware threads (default: all but 4, at most 32) and nice 10, so the
#     system keeps headroom;
#   - a free-disk floor (--min-free-gb, default 100);
#   - a watchdog that times a 1 MB write + fsync on the store's volume every 30 s, and asks
#     the run to pause (the PAUSE file; exit code 3 at the next layer boundary) if one takes
#     longer than 20 s or fails. Re-run the same command to resume.
#   - a memory guard on the kernel's pressure level (kern.memorystatus_vm_pressure_level:
#     1 normal, 2 warn, 4 critical). At warn it asks the run to pause; if pressure turns
#     critical, or stays at warn for 10 minutes, it stops the run (a restart redoes only the
#     current layer) and exits 4. (On 2026-10-10 a run with a ~94 GB footprint met the
#     nightly eigentimes Colima VM, 32-54 GB, and Morrobay swapped hard. RSS hides compressed and
#     swapped pages, so the guard watches the kernel's pressure level, not RSS.)
set -u
bin=$1 dir=$2 horizon=$3
shift 3
ncpu=$(sysctl -n hw.ncpu 2>/dev/null || nproc)
threads=${THREADS:-$(( ncpu > 8 ? ncpu - 4 : ncpu ))}
(( threads > 32 )) && threads=32
min_free=${MIN_FREE_GB:-100}
mkdir -p "$dir"
log="$dir/watchdog.log"

probe() { # seconds for a 1 MB write + fsync in the store directory, or 999 on failure
  perl -MTime::HiRes=time -MIO::Handle -e '
    my $t = time; alarm 60;
    open(my $f, ">", $ARGV[0]) or exit 1;
    print $f "x" x 1048576; $f->sync or exit 1; close $f; unlink $ARGV[0];
    printf "%.1f\n", time - $t' "$dir/.probe" 2>/dev/null || echo 999
}

watchdog() {
  local s lvl warn=0
  while kill -0 "$1" 2>/dev/null; do
    sleep 30
    lvl=$(sysctl -n kern.memorystatus_vm_pressure_level 2>/dev/null || echo 1)
    if (( lvl >= 2 )); then
      warn=$((warn + 1))
      echo "$(date '+%F %T') memory pressure level $lvl ($warn checks)" >> "$log"
      touch "$dir/PAUSE"
      if (( lvl >= 4 || warn >= 20 )); then
        echo "$(date '+%F %T') stopping the run: memory pressure" >> "$log"
        touch "$dir/MEMSTOP"
        kill "$1"
        return
      fi
    else
      warn=0
    fi
    s=$(probe)
    if awk -v s="$s" 'BEGIN { exit !(s > 20) }'; then
      echo "$(date '+%F %T') slow volume: probe took $s s" >> "$log"
      touch "$dir/PAUSE" && echo "$(date '+%F %T') asked the run to pause" >> "$log"
    fi
  done
}

rm -f "$dir/MEMSTOP"
echo "$(date '+%F %T') start: $bin --store $dir --horizon $horizon --threads $threads --min-free-gb $min_free $*" >> "$log"
nice -n 10 "$bin" --store "$dir" --horizon "$horizon" --threads "$threads" --min-free-gb "$min_free" "$@" &
pid=$!
watchdog "$pid" &
wd=$!
wait "$pid"
code=$?
[ -f "$dir/MEMSTOP" ] && code=4
{ kill "$wd" && wait "$wd"; } 2>/dev/null
echo "$(date '+%F %T') exit $code" >> "$log"
if (( code == 4 )); then
  echo "stopped for memory pressure; see $log. Lower --cap or free memory, remove $dir/PAUSE, and run the same command."
elif (( code == 3 )); then
  echo "paused; see $log. Remove $dir/PAUSE and run the same command to resume."
fi
exit $code
