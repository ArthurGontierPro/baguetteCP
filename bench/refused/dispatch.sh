#!/usr/bin/env bash
# M18-coverage-T9 (D-0265): run a queue of "ID ARM" lines, P at a time (default 24).
# Launch detached:  setsid nohup bench/refused/dispatch.sh QUEUE [P] > LOG 2>&1 &
# Writes its own PID (the process-group leader) to QUEUE.pid and QUEUE.done at the end.
# Cleanup is `kill -- -$(cat QUEUE.pid)`, the group this script leads, nothing else.
set -u
Q=$1; P=${2:-24}
D=$(cd "$(dirname "$0")" && pwd)
echo $$ > "$Q.pid"
rm -f "$Q.done"
xargs -P "$P" -L 1 "$D/run1.sh" < "$Q"
date -Is > "$Q.done"
