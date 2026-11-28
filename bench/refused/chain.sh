#!/usr/bin/env bash
# M18-coverage-T9 (D-0265): run queues one after the other, so that at most P runs are alive.
# usage (detached): setsid nohup bench/refused/chain.sh P QUEUE[:TL[:STOP_GIB]]... > LOG 2>&1 &
# Waits for QUEUE.done of the previous queue (if a dispatcher already runs it), then
# dispatches the next one. PID in $W/chain.pid.
set -u
P=$1; shift
D=$(cd "$(dirname "$0")" && pwd)
echo $$ > ${W:-/scratch/arthur/refused-work}/chain.pid
for spec in "$@"; do
  IFS=: read -r q tl sg <<< "$spec"
  if [ -f "$q.pid" ] && [ ! -f "$q.done" ]; then
    while [ ! -f "$q.done" ]; do sleep 20; done
    continue
  fi
  [ -f "$q.done" ] && continue
  TL=${tl:-1200} STOP_GIB=${sg:-8} "$D/dispatch.sh" "$q" "$P"
done
