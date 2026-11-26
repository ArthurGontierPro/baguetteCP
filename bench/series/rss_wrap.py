#!/usr/bin/env python3
# M17-bench-series-T1: copied from M10-search-strategy-T5 (itself from m8t4): run argv[2:] as a child, write its peak RSS (ru_maxrss, KB) to argv[1],
# exit as the child did (signal re-raised), so compare_run.sh classifies exactly as without us.
# SIGTERM/SIGINT are ignored here: `timeout` signals the whole process group, the child gets it.
import os, signal, sys
out = sys.argv[1]
for s in (signal.SIGTERM, signal.SIGINT, signal.SIGXFSZ):
    signal.signal(s, signal.SIG_IGN)
pid = os.fork()
if pid == 0:
    for s in (signal.SIGTERM, signal.SIGINT, signal.SIGXFSZ):
        signal.signal(s, signal.SIG_DFL)
    os.execv(sys.argv[2], sys.argv[2:])
while True:
    try:
        _, st, ru = os.wait4(pid, 0)
        break
    except InterruptedError:
        continue
with open(out, "w") as f:
    f.write("rss_kb=%d\n" % ru.ru_maxrss)
if os.WIFSIGNALED(st):
    sig = os.WTERMSIG(st)
    signal.signal(sig, signal.SIG_DFL)
    os.kill(os.getpid(), sig)
    sys.exit(128 + sig)
sys.exit(os.WEXITSTATUS(st))
