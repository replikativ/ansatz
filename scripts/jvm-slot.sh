#!/usr/bin/env bash
# JVM slots on a shared machine (agreed between the sessions using /tmp/claude-1000).
#
#   /tmp/claude-1000/jvm.lock          the old global lock: held = "a big JVM runs, nothing else"
#   /tmp/claude-1000/jvm-slots/slot-N  N = 1..3, one per JVM of at most -Xmx1g (~0.75 GB RSS)
#
# A slot JVM may start only when jvm.lock is free and MemAvailable >= 2 GB. An exclusive JVM
# (anything above 1 GB, e.g. the full test suite at 3 GB) takes jvm.lock AND all three slots and
# needs MemAvailable >= 4 GB. Locks are `mkdir`s with an `owner` file (+ `pid`); a script only
# ever removes locks it created. Stale entries (dead pid) are reported, never removed.
#
# Usage:
#   scripts/jvm-slot.sh repl PORT [OWNER]   take a slot, start an nREPL (-Xmx1g) on PORT in the
#                                            current directory; the slot is released when it exits
#   scripts/jvm-slot.sh stop PORT           stop the nREPL started on PORT and release its slot
#   scripts/jvm-slot.sh exclusive -- CMD…   run CMD holding jvm.lock + all slots (waits for them)
#   scripts/jvm-slot.sh status              show who holds what
set -euo pipefail

ROOT=/tmp/claude-1000
LOCK=$ROOT/jvm.lock
SLOTS=$ROOT/jvm-slots
NSLOTS=3
mkdir -p "$SLOTS"

mem_available_kb() { awk '/MemAvailable/ {print $2}' /proc/meminfo; }

status() {
  if [ -d "$LOCK" ]; then echo "jvm.lock: $(cat "$LOCK/owner" 2>/dev/null)"; else echo "jvm.lock: free"; fi
  for i in $(seq 1 $NSLOTS); do
    d=$SLOTS/slot-$i
    if [ -d "$d" ]; then
      pid=$(cat "$d/pid" 2>/dev/null || true)
      alive=""; [ -n "$pid" ] && ! kill -0 "$pid" 2>/dev/null && alive=" (STALE: pid $pid dead)"
      echo "slot-$i: $(cat "$d/owner" 2>/dev/null)$alive"
    else echo "slot-$i: free"; fi
  done
  echo "MemAvailable: $(( $(mem_available_kb) / 1024 )) MB"
}

# Claim one free slot; prints its directory. Waits (up to $WAIT s, default 14400) for jvm.lock to be
# free, enough memory and a free slot.
claim_slot() {
  local owner=$1 waited=0 limit=${WAIT:-14400}
  while true; do
    if [ ! -d "$LOCK" ] && [ "$(mem_available_kb)" -ge $((2 * 1024 * 1024)) ]; then
      for i in $(seq 1 $NSLOTS); do
        if mkdir "$SLOTS/slot-$i" 2>/dev/null; then
          echo "$owner $(date -Is)" > "$SLOTS/slot-$i/owner"
          echo "$SLOTS/slot-$i"; return 0
        fi
      done
    fi
    [ "$waited" -ge "$limit" ] && { echo "jvm-slot: no slot within ${limit}s" >&2; status >&2; return 1; }
    sleep 10; waited=$((waited + 10))
  done
}

cmd=${1:-status}; shift || true
case "$cmd" in
  status) status ;;

  repl)
    port=${1:?port}; owner=${2:-"nREPL :$port in $PWD"}
    slot=$(claim_slot "$owner")
    log=$slot/nrepl.log
    # the subshell owns the JVM and releases the slot when it exits, however it exits
    (
      clj -J-Xmx1g -M:repl --port "$port" > "$log" 2>&1 &
      jpid=$!
      echo "$jpid" > "$slot/pid"; echo "$port" > "$slot/port"
      wait "$jpid" || true
      rm -rf "$slot"
    ) &
    for _ in $(seq 1 120); do grep -q "nREPL server started" "$log" 2>/dev/null && break; sleep 2; done
    if grep -q "nREPL server started" "$log" 2>/dev/null; then
      echo "nREPL on port $port ($slot)"
    else
      echo "jvm-slot: nREPL did not start; see $log" >&2; exit 1
    fi
    ;;

  stop)
    port=${1:?port}
    for d in "$SLOTS"/slot-*; do
      [ -f "$d/port" ] && [ "$(cat "$d/port")" = "$port" ] || continue
      pid=$(cat "$d/pid")
      # clj's java child carries the heap; stop the whole process group of the launcher
      pkill -TERM -P "$pid" 2>/dev/null || true; kill -TERM "$pid" 2>/dev/null || true
      echo "stopped nREPL :$port ($d)"; exit 0
    done
    echo "jvm-slot: no slot with port $port" >&2; exit 1
    ;;

  exclusive)
    [ "${1:-}" = "--" ] && shift
    waited=0; limit=${WAIT:-3600}
    until [ "$(mem_available_kb)" -ge $((4 * 1024 * 1024)) ] && mkdir "$LOCK" 2>/dev/null; do
      [ "$waited" -ge "$limit" ] && { echo "jvm-slot: jvm.lock not free" >&2; status >&2; exit 1; }
      sleep 10; waited=$((waited + 10))
    done
    echo "exclusive: $* (pid $$) $(date -Is)" > "$LOCK/owner"
    taken=()
    release() { for d in "${taken[@]}"; do rm -rf "$d"; done; rm -rf "$LOCK"; }
    trap release EXIT
    for i in $(seq 1 $NSLOTS); do
      until mkdir "$SLOTS/slot-$i" 2>/dev/null; do sleep 10; done
      echo "exclusive run (pid $$)" > "$SLOTS/slot-$i/owner"; taken+=("$SLOTS/slot-$i")
    done
    "$@"
    ;;

  *) echo "usage: jvm-slot.sh {status|repl PORT [OWNER]|stop PORT|exclusive -- CMD...}" >&2; exit 2 ;;
esac
