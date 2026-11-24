# The measurements behind D-0226 (M23-inputs)

Run on `fataepyc-06`, 2026-11-24. Results kept in
`/cluster/arthur/baguette-results/inputs-20261124/`.

| file | what |
|---|---|
| `two.sh MODEL.fzn` | one `.scp` from `tools/e2e/fzn2scp.py`, a proof from `baguette --e2e` and one from `glasgow_scp_solver`, both elaborated by `veripb` against the same `cake_pb_cp` `.opb` and checked by `cake_pb_cp` (paths in the header lines). Results: `res.txt`; `r2.txt` and `r3.txt` are the GCS side replayed with `solx` rewritten to `sol` (r2 all verified, r3 the scheduling models, still refused) and `r4.txt` the 101 models replayed as `enumerate` |
| `probe.py FILE.xml.lzma` | loads an XCSP3 instance with CPMpy 1.1.1, flattens it keeping the globals cake has, and lists the flat constraint forms. One JSON line. It writes no `.scp` and runs no solver |
| `analyze.py RES.jsonl` | the tables of D-0226 section 3 |

`probe.py` needs a venv with `cpmpy` and `pycsp3`, and the XCSP25 archive from the competition page
(`instancesXCSP25.zip`, 450 instances in `COP25` and `CSP25`).
