# References cited in the code

An index of every decision record (`D-`), roadmap task (`M`) and invariant (`I-`) cited in
the comments of `lib/` and `bin/`, with one line saying what each is about, so that a reader
meeting a reference in a comment does not have to open `docs/DECISIONS.md` (2.4 MB) to know
what it refers to. The line is the record's title, the task's roadmap row or the invariant's
first line, shortened; the record itself remains the authority. "Cited" counts the mentions
in the code.

A snapshot of 2026-11-27 (M22-review-T4, D-0253). A reference added to the code since then
is not here: `grep -n '^## D-0123' docs/DECISIONS.md`, `grep -n 'M6-T22' docs/ROADMAP.md`
and `grep -n 'I-X6' docs/INVARIANTS.md` find any of them.

## Decision records (docs/DECISIONS.md)

| Id | Cited | What it is about |
|---|---|---|
| D-0003 | 3 | What "higher-order explanation" means here |
| D-0004 | 2 | all_different justification strategy |
| D-0007 | 21 | Booleans use the order encoding on [0, 1] |
| D-0008 | 5 | Backtracking uses proof levels, not per-reason deletion |
| D-0009 | 42 | A bound fact in a pol needs a constraint id, not a literal |
| D-0010 | 29 | A bound fact is a chain of order literals, not one literal |
| D-0011 | 21 | One propagator instance, one model row |
| D-0012 | 3 | A branch nogood is not RUP-derivable from the model rows alone |
| D-0013 | 52 | How a bounds conflict is justified: weaken, divide, add |
| D-0014 | 2 | Decision-free lemmas strengthen a branch nogood, but do not yet close it |
| D-0015 | 5 | Explanation gets a divisor, a named row, and a weaken-only summand |
| D-0017 | 2 | A SAT run's nogoods are checked too, so SAT proofs fail as well |
| D-0018 | 58 | A branch nogood is RUP over the branch's own logged trace |
| D-0019 | 17 | A disequality needs the order encoding, not the direct one |
| D-0020 | 2 | lin_unsat's refutation has a unit of slack, and only mutation found it |
| D-0021 | 6 | Every pruning needs a trace line, not only the ones under a decision |
| D-0022 | 13 | A root conflict is its own contradiction only if its derivation is numeric |
| D-0023 | 14 | Proof format: VeriPB 3.0, and the Rust checker of record |
| D-0024 | 8 | VeriPB 3.0 deletes the level stack, so the writer keeps the tags |
| D-0025 | 2 | The 3.0 default is on, and what the test flip actually cost |
| D-0026 | 63 | D-0003 resolved: reasons are data, justifications are cutting planes |
| D-0027 | 5 | D-0011 is a rule about naming rows, not about counting them |
| D-0028 | 34 | A justification's size is proportional to declared domain width |
| D-0029 | 41 | An arithmetic limit, enforced at compile time, and why declining to prune is not an option |
| D-0030 | 2 | A mutation lane must judge a derivation, not a grammar -- and root_unsat cannot |
| D-0031 | 1 | The order encoding's ladder stays in the .opb: lazy by red is quadratic |
| D-0033 | 11 | Division rounds toward zero as a relation and outward as a bound; dividing by zero is unsatisfiable, not an error |
| D-0034 | 3 | A wake trigger is a property of what a propagator READS, not of what it promises |
| D-0035 | 4 | An explanation must justify the bound as RECORDED, not the bound the propagator asked for |
| D-0037 | 12 | A decision is an assumption, not the model row: Trivial is deleted and the ambient row becomes unrepresentable |
| D-0038 | 3 | Should an Explanation carry the bound it concludes, so a pol can be checked against it? |
| D-0039 | 5 | A trace line is RUP in sequence, not standalone: the individual-derivability property is retired |
| D-0040 | 19 | all_different does NOT force the direct encoding; it forces an explicit derivation |
| D-0041 | 5 | A declared width limit, because a proof nobody can store is not an answer |
| D-0043 | 25 | D-0038 resolved: the conclusion is a Reason.fact, carried on justified, in reason.ml |
| D-0044 | 54 | The learned object is a PB inequality; a clause is its degenerate case |
| D-0045 | 21 | SPEC §3.4 and restarts: the question raised, with the finding it turned up |
| D-0046 | 8 | Proof format 2.0 is removed from the project entirely |
| D-0050 | 3 | to_linear_row is the right predicate being used as the wrong gate |
| D-0051 | 12 | A learned constraint has one owner, and retention is dominated by keeping everything |
| D-0052 | 19 | A clause over order literals is a WIDENING of bool_clause, not a new family — and watched literals are a separate question |
| D-0053 | 15 | Reification has two doors, and red is vacuous over a contradictory database |
| D-0054 | 22 | A proof line and a propagation explanation are different objects, and this project has been building one of them |
| D-0057 | 4 | Reification: big-M int_lin_le rows, one dispatcher, and int_eq_reif without p ∧ q |
| D-0058 | 13 | A view is a rendering onto its base's literals, not a variable with literals of its own |
| D-0059 | 3 | The consistency tag is now checked, and today it does no separating work |
| D-0060 | 5 | int_times / int_div / int_abs: the case split lives in the model, not in the proof |
| D-0061 | 6 | The Hall derivation: the ADT carried it, and the one place it could not |
| D-0062 | 1 | M2-L6's PB analysis costs an order of magnitude on width, and that is accepted |
| D-0064 | 16 | Explanation.Defining: the ADT can now ask for a constraint id, and D-0044's table breaks at nine |
| D-0065 | 6 | The hardware limits become options, defaulting off — and D-0041's objection is answered, not ignored |
| D-0066 | 4 | rup is vacuous over a contradictory database, and 26 lanes may be testing nothing |
| D-0068 | 5 | The first full corpus run: 8 proofs verified, and the blocker is not what anyone predicted |
| D-0070 | 4 | The level-0 nogood RUP defect: a decision that settles past a hole, and a filter that cannot see it |
| D-0071 | 4 | The graceful resource guard: predictive AND reactive, both defaulting to off |
| D-0072 | 10 | Set domains: the holes go in the .opb as ladder rows, and in the solver as propagators |
| D-0073 | 1 | The rup audit: none of the 26 lanes was vacuous, and D-0066's remedy was wrong |
| D-0075 | 13 | The SECOND RUP defect: a propagator that reads a HOLE and states only BOUNDS |
| D-0077 | 10 | The assignment decision: a disjunctive sibling is discharged by DERIVATION, not by resolution |
| D-0078 | 4 | A global_cardinality propagator: the counting row lives in the ORDER encoding, and the interval capacity is what the decomposition cannot reach |
| D-0079 | 2 | The wave-30 corpus run: 58 verified, 0 rejected, and the blocker is now TIME |
| D-0080 | 10 | Where the 300 s go: a stopped run is now a checked proof, and the time is in quadratic bookkeeping, not in search |
| D-0082 | 14 | Derive-ahead is a property of the PROPAGATOR (M7-T17), and a constant gcc count is a VIEW (M7-T18) |
| D-0083 | 14 | The ten corpus refusals: indomain is indomain_min, anti_first_fail is first_fail reversed, and an undomained var int gets the domain its constraints ... |
| D-0084 | 13 | The 26 corpus rejections: a derivation one propagator EMBEDS in another, in two families |
| D-0085 | 9 | D-0080's levers #3-#6 shipped as constant-factor changes: every artefact byte-identical, the learned-PB-row work is the one that moves locally |
| D-0086 | 7 | Three root-conflict defects from the sweep: the root trace is gated on a WALK, a hole has one currency, a telescope stops at the declared top |
| D-0087 | 5 | M6-T13: Search's per-node cost stops scaling with the store, Opb's name tables are string-specialised, and global_cardinality_low_up is routed to gcc ... |
| D-0088 | 9 | M6-T14: per-variable trail histories replace the support and remover scans |
| D-0090 | 5 | M6-T15: Trace.position_of from the entry's own trail position, add_fact by a reversed accumulator |
| D-0091 | 3 | M6-T8: BAGUETTE_DEBUG=1 is clean on every model; the four element fatals were the agreement check over-reading a ROOT Defining |
| D-0092 | 1 | M6-T16: Analysis merges its frontier and accumulates its antecedents in linear time |
| D-0094 | 2 | M2-T6: propagation counters under --stats, and the self-wake veto with its two guards |
| D-0095 | 7 | M4-T9: array_int_maximum / array_int_minimum as a propagator over one clause row per threshold |
| D-0096 | 16 | M4-T10: cumulative as time-table filtering over ORDER-literal capacity rows; disjunctive is its unit case |
| D-0097 | 4 | M7-T23: the counting family stays with std's decomposition; the one-value gcc route was measured and withdrawn |
| D-0098 | 7 | M6-T18: the propagation queue is seeded from what changed, and the skip is exact |
| D-0099 | 6 | M7-T24: gcc's two single-value rules, and the proof volume was in the reasons, not the derivations |
| D-0101 | 6 | M7-T25: an element conflict carries its facts under a decision, derived ahead, so 1UIP learning resolves from it |
| D-0104 | 10 | M6-T20: learned clauses are where the propagator runs go, and the answer is an ADVISOR -- two watched literals, answered in O(1) before the wake is ... |
| D-0121 | 1 | M7-T26, the sixteen editions side by side: last or next to last everywhere, and the wall is width and heap, not search |
| D-0123 | 7 | M7-T27, the wall is memory, in three places, and the objective's width is not one of them |
| D-0124 | 27 | M7-T27 (a): a Linear pruning's reason is materialised LATER, from the trail's history, not snapshotted per term at the push |
| D-0126 | 16 | M9-no-proof-T1: a solve-without-proof mode exists, as a measurement instrument |
| D-0127 | 13 | M8-bits-encoding-T0: RUP, pol and elaboration measured on the checker alone, in the order and the bits encodings |
| D-0128 | 5 | M7-T27 (d): the front end streams -- family A was the token array, and the fix is a window with one lexeme of lookahead, items built as they are ... |
| D-0130 | 54 | M8-bits-encoding-T1: the bits encoding above a threshold -- the substrate contract, the on-demand atom, the mixed row, and how a bits pruning is ... |
| D-0131 | 26 | M8-bits-encoding-T5: the order arm's ladder walks are written as rup, the root closes on its trace, and where pol stays and why |
| D-0132 | 37 | M8-bits-encoding-T2: the bits encoding for Linear -- the design as it will be built, the checker facts measured first, and what deviates from D-0130 |
| D-0134 | 48 | M8-bits-encoding-T3: the full substrate -- maxmin over bits by SELECTOR rows and one Resolve step, the checker facts measured first, and the step ... |
| D-0136 | 8 | M6-T21: the --time-limit overshoot was the stop's own sweep, quadratic in the learned constraints |
| D-0137 | 46 | M10-search-strategy-T1: restarts, phase saving and an activity heuristic, behind flags -- a restart is the backjump this solver already writes, taken ... |
| D-0138 | 16 | M6-T22: the per-node cost on the XOR codes was the engine asking every learned clause about every variable it names |
| D-0139 | 35 | M10-search-strategy-T4: retention re-measured, the learned database made evictable (Retention.gate, the lock rule, three LBD tiers), and why the ... |
| D-0140 | 45 | M11-complexity-T1: the inventory of the costs that grow with the run, measured on six instances at four node budgets, ranked, and split into the ... |
| D-0142 | 29 | M11-complexity-T3: batch 1 of the complexity pass (engine, store, propagators), and first the I-P7 alarm on integer instances, which was two debug ... |
| D-0143 | 9 | M11-complexity-T7: the setup before node 1 was the .opb's name pipeline, three lists and two string tables per term of every linear row |
| D-0144 | 15 | M11-complexity-T4 part 1: learning and PB analysis without their quadratic lists, the trail walk of falsified_before replaced by the bound history |
| D-0145 | 29 | M11-complexity-T5: batch 3 of the complexity pass, trace, justification and proof writing, profiled with frame pointers |
| D-0146 | 29 | M7-T28 first steps and M7-T29's gcc half: the closed gcc forms were never decomposed, a repeated gcc variable is copied away in the model, and ... |
| D-0148 | 6 | M7-T31: a factless pruning that settled over a hole is not a root of the decision closure |
| D-0149 | 13 | M6-T23: the --time-limit overshoot on cargo and cable was the stop never being asked, inside a PB analysis and inside a conflict's trace, and not the ... |
| D-0150 | 11 | M7-T32: the MiniZinc standard flags. tools/baguette.msc declares -i -f -n -p -r -s -t -v, each maps onto an option the CLI already had, every ... |
| D-0151 | 26 | M7-T28 continued: regular's reasons on the letters (every tail recurses into the dead flags' own lines, so a learned clause names cells and not ... |
| D-0152 | 23 | M11-complexity-T4 part 2: search, analysis and retention without their per-node and per-conflict scans |
| D-0153 | 19 | M8-bits-encoding: PB conflict analysis over rows with a bits term -- every bits block is INSTANTIATED through its atom's bridge before the analysis ... |
| D-0154 | 2 | The user's decisions of 2026-11-19: the default search stays the fixed one, as in the MiniZinc Challenge |
| D-0155 | 9 | M11-complexity-T8: Element's fact deduplication hashed and linear, and the other per-pruning scans of element.ml gone |
| D-0156 | 12 | M7-T33: all_different's two pigeonholes carry their facts under a decision, derived ahead of the conflict line, so 1UIP learning resolves from them |
| D-0157 | 14 | M11-complexity-T9: the learned PB row's arithmetic without its sorts -- Learned.combine as one merge of two sorted rows, Ladder.lift's rungs in one ... |
| D-0158 | 5 | M11-complexity-T10: the memo's identical copies cannot share an entry without changing the proof's bytes |
| D-0159 | 16 | M7-T28 continued: member native -- one selector per position as a store variable, the rows in the BOUND form (D-0151's value form measured short), ... |
| D-0161 | 14 | M9-no-proof-T4: the --no-proof audit -- what the null writer still paid for after D-0135, six guards in Search and in start_proof's root lemmas, and ... |
| D-0163 | 2 | M9-no-proof-T5: the default run keeps its proof -- ./<model>.opb and .pbp in the current directory, ./baguette-proof under MiniZinc, overwritten by ... |
| D-0164 | 1 | M11-complexity-T11: what black-hole keeps per node, and Element's foreign-hole clauses built lazily |
| D-0166 | 9 | M11-complexity-T12: what a proved run keeps once a line is written; four holders shrunk byte for byte, the largest is the user's call |
| D-0167 | 2 | The six open decisions of 2026-11-19, taken by the orchestrator on the user's delegation |
| D-0168 | 11 | M11-complexity-T13: a thunk is released once its line is written; the memo lets go of what the closure built |
| D-0170 | 6 | M7-T34: member without width-proportional rows -- b_k -> x_k = y as four bound clauses and two big-M rows over the declared overlap, the threshold ... |
| D-0172 | 13 | M11-complexity-T15: explanations as a DAG whose nodes carry their line |
| D-0173 | 10 | M11-complexity-T17: the learned clauses that "cannot prune" are SATISFIED |
| D-0174 | 2 | M14-e2e-verification-T1: the verified encoder is CakeML's cake_pb_cp, and baguette reaches it by re-deriving its own .opb at the head of its proof |
| D-0176 | 2 | M14-e2e-verification-T2: the end-to-end lane, 75 test models certified by CakeML's verified encoder and checker, with a separate translator checked ... |
| D-0178 | 3 | M14-e2e-verification-T4: the Boolean and reified families in the end-to-end lane, 105 test models certified by cake_pb_cp |
| D-0180 | 4 | M14-e2e-verification-T5: the globals in the end-to-end lane, 179 test models certified by cake_pb_cp |
| D-0182 | 3 | M14-e2e-verification-T8: objectives in the end-to-end chain, and the first measurement of cake_pb_cp on baguette's search proofs (Challenge) |
| D-0184 | 1 | M4-T6: in-proof tabulation over the order encoding. It transfers, at about five lines per pair of operand values, and two removals in three did not ... |
| D-0186 | 21 | M16-file-review-T1: the core read file by file. Three searches were quadratic in the depth of the tree, seven byte-identical levers taken (one ... |
| D-0187 | 12 | M14-e2e-verification-T3: baguette writes the end-to-end prefix itself under --e2e, off by default, against a second naming contract pinned to ... |
| D-0188 | 20 | M14-e2e-verification-T3b: T5's globals in the solver-written prefix, each row derived by one pol where the bridge needed rup |
| D-0189 | 1 | M7-T35: the member models that stopped under BAGUETTE_DEBUG. Their reasons were right and D-0026's reverse arm over-read the threshold lemmas, so the ... |
| D-0190 | 24 | M16-file-review-T2: the propagators read file by file. Ten byte-identical levers |
| D-0191 | 16 | M16-file-review-T3: learning read file by file. The cost was in hash tables (a polymorphic one per conflict, a full trail table per eviction, tables ... |
| D-0192 | 15 | M16-file-review-T4: the proof side read file by file. The cost was in hashing (a table whose hash was its key, a claim key sorted by string compare ... |
| D-0193 | 15 | M16-file-review-T5: the front end and the setup read file by file |
| D-0195 | 20 | M14-e2e-verification-T6: the far families in the end-to-end chain. regular and cumulative in, int_abs in, int_times and int_div left outside |
| D-0196 | 11 | M14-e2e-verification-T7: the bits arm in the end-to-end chain |
| D-0197 | 11 | hotfix: the "Stack overflow" on the ATSP instances (D-0194 §7) was Learned.make recursing once per term on a 32-million-term PB row |
| D-0198 | 4 | M6-T2 re-scoped: the trail and the domains are 0.5 to 4.5 % of the words allocated, so no Bigarray/Bytes move |
| D-0199 | 2 | M8-bits-encoding-T4 continuation: a middle W (64 or 100) wins back 4 of order's 14 lost complete answers and none of the 10 nfc, and loses 4 of the ... |
| D-0200 | 13 | hotfix: the M7-T8 heap budget was read only at the end of a major cycle, so a growing heap could reach the address-space limit between two readings |
| D-0201 | 4 | D-0199 applied: the default is --bits-above 0. Every eligible integer variable is on the bits encoding, and --bits-above none gives back the order ... |
| D-0202 | 1 | M10-search-strategy-T5: the codes set under -f and under BAGUETTE_RETENTION=tiered. -f solves o7k2 def (27 s against a timeout) and costs 2x on QR |
| D-0206 | 11 | M18-coverage-T1: table as a native propagator over one SELECTOR per tuple, the tuples in the .opb as one row each, every pruning one rup |
| D-0207 | 6 | M20-pernode-T1: where the factor per node goes, on five families and the same tree |
| D-0208 | 4 | M20-pernode-T4 (learned part): watching a learned PB row was measured and NOT taken; the pass exits after one walk when nothing is forceable |
| D-0209 | 9 | M20-pernode-T5: the proof text through one buffer. Integers and literal names are written in place and each variable's name prefix is rendered once |
| D-0212 | 14 | M20-pernode-T3 (arithmetic): Linear checks a row for overflow once, at make, and a row that passes runs plain +, *, / |
| D-0214 | 22 | M20-pernode-T2: an Element pruning records a FRAME, the domains it read and the trail cut (D-0124's history), and its reason and derivation are built ... |
| D-0215 | 8 | M20-pernode-T4 (rank 5 of D-0207): alldiff's Régin stage skips a pass that cannot prune |
| D-0216 | 10 | M11-complexity-T18: black-hole's root cost under native table was alldiff rebuilding its Hall derivations at every pruning, 8.3 M pairwise ... |
| D-0217 | 10 | M18-coverage-T3: circuit as a native propagator over MTZ position variables |
| D-0218 | 6 | M21-memory-T1/T2: where the heap goes. OCaml's own representation costs a factor 2.5 to 4 on record-heavy kinds and the GC's free space a factor 1.5 ... |
| D-0219 | 12 | M19-config-T10: learning that drives the search. The CDCL loop of lazy clause generation (1UIP clause, backjump to its asserting level, the clause ... |
| D-0220 | 2 | M18-coverage-T4: bin_packing_load, bin_packing_capa and bin_packing through mznlib, std's rows without the bool2int copies |
| D-0221 | 6 | M19-config-T5 (review T12): the retention default measured on the tuning set and on 42 heap refusals |
| D-0222 | 23 | M21-memory-T3 (fix 2 of D-0218): a hole set is a VERSION of a per-variable hole log, trailed by value |
| D-0223 | 6 | M21-memory-T3 (fix 4 of D-0218): what kept written explanations alive on tdtsp is not the hash-consing table but the INNER thunk of Element's ... |
| D-0224 | 7 | M19-config-T11, then T2 to T4 measured on the CDCL loop: chronological backtracking for long jumps under --cdcl (--chrono N), with the asserted ... |
| D-0225 | 10 | M6-T24: an interrupted run ends its proof. A signal or the heap budget closes it where it stands, and an optimisation run concludes BOUNDS <declared ... |
| D-0226 | 42 | M21-memory-T3 fix 1, the learned-row layout, and a PB size guard (M19-config-T5 re-measured) |
| D-0228 | 17 | M23-inputs: a relational Problem between the readers and the solver, .scp as a second input, every other language translated to .scp outside the ... |
| D-0230 | 15 | M23-inputs-T1..T5: the .scp reader, lib/scp/. What it reads, what it refuses and why, the choices D-0228 section 14 left open, and the lanes that ... |
| D-0231 | 2 | M22-review-bugs: regular with a constant letter outside its symbols no longer crashes, and cumulative's overload conflict writes the clearing of its ... |
| D-0232 | 7 | M18-coverage-T8: why regular completes so little. The census counts a satisfaction model's SAT as an incumbent (28 of 103 are complete, not 2) |
| D-0234 | 11 | M18-coverage-T11: global_cardinality's conflicts carry their facts under a decision, derived ahead, as all_different's do since D-0156, and its ... |
| D-0235 | 14 | M20-pernode-T4 on all_different: a call stops paying for what cannot have changed |
| D-0236 | 15 | M20-pernode-T4, the learning path: a name is hashed once where it was hashed per use |
| D-0237 | 1 | M22-review-bugs: a factless root conflict's derivation may mint atoms, so close_root_conflict closes the atoms after it |
| D-0238 | 5 | M18-coverage-ne: int_lin_ne's conflicts carry their fixing facts under a decision, so they learn. Measured first |
| D-0241 | 5 | M19-config-T6, clause minimisation: learned clauses lose their root-level literals (ROOT) and the literals the kept ones re-derive (RECURSIVE, ... |
| D-0242 | 11 | M20-pernode-T4 on all_different, second pass: a stage 1 pass that would move nothing is answered by counting, and the derivations a tight set ... |
| D-0243 | 11 | M20-pernode-T4 on the engine's wake path: the static wake index as flat int arrays walked without closures, the default advisor answered without its ... |
| D-0245 | 5 | M20-pernode-T4 on conflict analysis: Store.var_named answers through a direct-mapped memo of 4 096 cells, and Analysis.locate reads it as an int |
| D-0246 | 5 | M19-config-T9, propagator priorities: a cost-class queue behind BAGUETTE_PRIORITY=off\|classes (four classes, cheapest first, as Gecode and Chuffed) |
| D-0248 | 2 | M22-review-T5: a proof write that fails (Sys_error: missing directory, full disk) ends with one line on stderr and a new exit status, 6 |

## Roadmap tasks (docs/ROADMAP.md)

| Id | Cited | What it is about |
|---|---|---|
| M1-T1 | 1 | Domain with bounds + lazy holes, unit tested |
| M1-T10 | 3 | DFS search with first-fail, decisions logged in the proof |
| M1-T12 | 3 | Make the D-0013 derivation real: Combine/Weaken/Model_row + the root conflict |
| M1-T13 | 4 | The branching half of D-0013: justify a conflict reached under decisions |
| M1-T14 | 1 | Wire the CLI: .fzn in, solution + proof out |
| M1-T17 | 11 | Fix the three int_ne composition bugs M1-T16 pinned |
| M1-T18 | 4 | Adopt the Rust VeriPB 3.0.2 checker while still emitting format 2.0 |
| M1-T19 | 1 | Migrate proof emission to format 3.0 |
| M1-T21 | 1 | A bool *parameter* folded to a Const prints as 0/1, not false/true |
| M1-T22 | 3 | del range is half-open: fix Writer.wipe_level, correct PROOF-FORMAT §5 |
| M1-T23 | 19 | Checked arithmetic in Linear/Ne; cap declared domains at compile time |
| M1-T24 | 2 | Trail-cursor walk in Engine.propagate, replacing Store.trail_entries |
| M1-T26 | 4 | Move mutation knobs from proof text into the emitter; add a mandatory control lane |
| M1-T28 | 1 | Index-walk the trail in linear.ml's find_lo_reason/find_hi_reason |
| M1-T29 | 2 | The del id fallback line grows with the reasons retired at one level |
| M1-T31 | 12 | Remove the ambient model row: make Linear.make's ?row_id required, delete Justify.emit's Trivial -> ctx.model_id () arm |
| M1-T32 | 6 | State and enforce "Compile is the only door": check the arithmetic inside Encoding/Opb too |
| M1-T33 | 2 | Make I-S1's oracle genuinely independent: Model.check_assignment must not share the propagator's arithmetic |
| M1-T34 | 2 | bin/main.ml should catch Checked.Overflow and exit with a diagnostic |
| M1-T35 | 3 | A --time flag (or a library-level harness) so solve time is separable from process start-up |
| M1-T36 | 21 | A real node counter in search.ml, replacing the benchmark's lvl proxy |
| M1-T37 | 2 | The .opb header embeds the input path, so its byte count depends on where the file lives |
| M1-T39 | 1 | Delete Writer.pol_raw, or document why it stays |
| M1-T4 | 1 | Order encoding in lib/proof/lit.ml, .opb writer |
| M1-T42 | 2 | test_prop.ml's integer veripb builders hold their setup facts as .opb model rows |
| M1-T44 | 10 | A correct UNSAT answer whose proof the checker rejects (I-X7). Reproduced by the orchestrator through the CLI |
| M1-T45 | 10 | Reclaim the 0.4% of branching shapes random_order's hole guard refuses |
| M1-T47 | 8 | Separate proof *emission* time from propagation time |
| M1-T48 | 2 | --proof-comments is a no-op on all 29 models — untested by construction |
| M1-T49 | 4 | The gate cannot see "timings are off unless asked" |
| M1-T50 | 14 | linear.ml cites its own row twice when the fact came from a decision |
| M1-T51 | 7 | Nothing distinguishes a pol that derives the claimed bound from one that derives something weaker |
| M1-T53 | 3 | A bare dune runtest still bypasses the memory cap |
| M1-T54 | 9 | A width cap in Encoding.declare_int, so a wide domain is a loud refusal |
| M1-T55 | 11 | spec_order can decide at a hole; random_order deliberately will not |
| M1-T56 | 8 | trace.ml's claims writes no line for a pure hole removal |
| M1-T57 | 3 | A settle-strengthened bound makes its own trace line stronger than its facts |
| M1-T58 | 1 | bin/main.ml does not catch Encoding.Unrepresentable |
| M1-T59 | 5 | Two proofs emit a byte-identical rup twice |
| M1-T6 | 1 | FlatZinc lexer + parser for the §2.1 subset |
| M1-T63 | 2 | Two hedges for a declared hole are unreachable dead paths |
| M1-T66 | 8 | Nothing but a string match holds up M1-T55's bridge |
| M1-T7 | 1 | int_lin_le propagator + justification |
| M1-T7a | 1 | int_lin_le propagator and its explanations |
| M1-T7c | 1 | Order-encoding expansion of sum a_i x_i into a PB row |
| M1-T9 | 13 | int_lin_ne, int_ne |
| M10-T2 | 9 | Restarts and phase saving, behind flags, with partial restarts if T1 keeps them |
| M10-T3 | 6 | The activity heuristic, behind a flag, and its alternation with the annotation |
| M10-T4 | 1 | Learned-clause deletion re-measured, and LBD tiers: today's policies (keep_all, fifo, lbd) on the codes set and the editions, then glue clauses kept ... |
| M10-T5 | 2 | The measurement and the defaults: the sixteen editions in the fixed and free categories (M7-T30), the codes set, a decision record on what becomes ... |
| M10-search-strategy-T2 | 12 | Restarts and phase saving, behind flags, with partial restarts if T1 keeps them |
| M10-search-strategy-T3 | 7 | The activity heuristic, behind a flag, and its alternation with the annotation |
| M10-search-strategy-T4 | 5 | Learned-clause deletion re-measured, and LBD tiers: today's policies (keep_all, fifo, lbd) on the codes set and the editions, then glue clauses kept ... |
| M11-T2 | 1 | The lanes the pass needs, before any fix: (a) a DIFFERENTIAL lane, real instances at a fixed node budget whose stdout, node counts and proof hashes ... |
| M11-T4 | 1 | Batch 2, search, analysis, learning and retention |
| M11-T5 | 1 | Batch 3, trace, justification and proof writing |
| M11-T9 | 2 | The Learned list arithmetic on PB rows: PB analysis over bits rows (D-0153) costs up to 2.3x per node with the search unchanged at equal nodes, about ... |
| M11-complexity-T10 | 2 | The explanation memo keeps up to 388 structurally identical copies per bucket (D-0149) |
| M11-complexity-T11 | 1 | The heap per node on black-hole (D-0155 §4, D-0156 §4): 2011_black-hole_9 without --proof holds 6.3 GB RSS after 39 nodes, about 150 MB per node, and ... |
| M11-complexity-T12 | 7 | What a proved run keeps alive once a line is written (D-0164 §7): on 2011_black-hole_9 with --proof at node 40, 2.66 GB live |
| M11-complexity-T13 | 14 | Drop a forced explanation once its line is written (D-0166 §5 option B, D-0167 item 6) |
| M11-complexity-T14 | 5 | The cost per node against Gecode on the same tree (codes-cp note of 2026-11-20 in WORKLOG) |
| M11-complexity-T15 | 15 | Spike: explanations as a hash-consed DAG whose nodes carry the id of the line they wrote (D-0140 J1) |
| M11-complexity-T17 | 8 | Learned clauses that cannot prune (D-0169): on codes QR48 under the fixed search, learned clauses run 177 times per node and prune nothing (0.00 ... |
| M11-complexity-T18 | 1 | black-hole's root cost under native table (D-0206's finding: black-hole_10 4.5x more instructions at the root, black-hole_14 past --time-limit 300 by ... |
| M11-complexity-T3 | 15 | Batch 1, engine, store and propagators |
| M11-complexity-T4 | 22 | Batch 2, search, analysis, learning and retention |
| M11-complexity-T5 | 18 | Batch 3, trace, justification and proof writing |
| M11-complexity-T7 | 11 | Setup: the cost before the first node (D-0140 §8.4, item X1): openshop spends 762 G instructions (112 s) before node 1, with or without the proof, in ... |
| M11-complexity-T8 | 5 | Element.add_facts's duplicate check is quadratic: 99 % of 2011_black-hole_10's run under the native inverse (D-0151 §2), and the same on main ... |
| M11-complexity-T9 | 9 | The Learned list arithmetic on PB rows: PB analysis over bits rows (D-0153) costs up to 2.3x per node with the search unchanged at equal nodes, about ... |
| M14-e2e-verification-T3 | 8 | The bridge written by the solver, a --e2e mode in which baguette emits the prefix itself (atoms, the two halves of B = l + S, the ladder, each row's ... |
| M14-e2e-verification-T3b | 2 | --e2e for T5's globals: array_int_element, global_cardinality, array_int_maximum/minimum, member, inverse |
| M14-e2e-verification-T6 | 2 | The far families: int_times/int_div/int_abs (baguette's case-split Booleans against cake's bit products), cumulative, regular (the mznlib state flags ... |
| M14-e2e-verification-T7 | 1 | The bits arm: baguette's x_bit_i (bits of x - l, unsigned) against cake's two's-complement bits of x |
| M16-file-review-T1 | 7 | The core: store.ml, domain.ml, engine.ml, var.ml, propagator.ml, search.ml (the per-node path: trail, wakes, queue, branching, backtracking) |
| M16-file-review-T2 | 22 | The propagators: prop/linear.ml and prop/clause.ml/prop/pb.ml first (the most run), then the globals one by one (alldiff, element, gcc, cumulative, ... |
| M16-file-review-T3 | 12 | Learning: learn.ml, analysis.ml, pb_analysis.ml, learned.ml, retention.ml, ladder.ml, reduce.ml, restart.ml, phase.ml, activity.ml |
| M16-file-review-T4 | 8 | The proof side: explanation.ml, justify.ml, trace.ml, lib/proof/writer.ml, encoding.ml, opb.ml, lit.ml |
| M16-file-review-T5 | 15 | The front end and setup: lexer.ml, parser.ml, builder.ml, compile.ml, output.ml (the cost before node 1; D-0143) |
| M18-coverage-T1 | 10 | table (135 instances, 52 refused): a native GAC propagator (compact-table, as Gecode, OR-tools and Chuffed have), each pruning justified from the ... |
| M18-coverage-T11 | 7 | gcc's conflicts carry their facts, as alldiff's do since M7-T33 (D-0156) |
| M18-coverage-T3 | 10 | circuit, subcircuit (127): alldiff plus the no-subtour check (Chuffed's and Gecode's), the subtour cut justified in the proof. Design record first |
| M18-coverage-T4 | 2 | bin_packing_load, bin_packing, _capa (85, 40 refused): the load sums as linear rows plus the capacity reasoning (Shaw's propagator, or the cumulative ... |
| M19-config-T10 | 11 | Learning that drives the search (FIRST in this milestone's priority) |
| M19-config-T11 | 9 | Chronological backtracking for long jumps under the CDCL loop (Nadel and Ryvchin, SAT 2018), or trail saving |
| M19-config-T6 | 5 | Conflict analysis: recursive clause minimisation (MiniSat), Pumpkin's CPIP stopping criterion, extended nogood propagation and per-variable atom ... |
| M19-config-T9 | 2 | The propagation engine: propagator priorities (cheap first, as Gecode and Chuffed), idempotence, staged propagation |
| M2-L0 | 4 | Implement D-0043: the conclusion as a Reason.fact on justified; first caller for Writer.pol_concluding / Writer.implied |
| M2-L1 | 17 | Learned.t: the PB learned-constraint type, its runtime propagator instance, and its proof-side introduction and deletion |
| M2-L11 | 18 | The ladder chain as a row: give PB analysis the reason Linear actually uses, so a learned inequality can be non-trivial |
| M2-L12 | 51 | Make learned constraints propagate: unit clauses as level-0 bounds first, then widen bool_clause to a threshold |
| M2-L13 | 37 | The PB explanation for SOLVING: propagate a learned PB row as a PB constraint over order literals, and take to_linear_row out of the propagation path |
| M2-L15 | 21 | Backjumping on the PB row: redo the calculation M2-L13 invalidated |
| M2-L2 | 9 | Conflict-analysis scaffolding: the implication graph and the 1UIP cut, as data |
| M2-L3 | 50 | 1UIP clause learning over order literals, with backjumping and its rup derivation |
| M2-L4 | 38 | Learned-constraint deletion, the matching del, and a retention policy |
| M2-L5 | 8 | Reduction as a named, swappable component: division and roundToOne |
| M2-L6 | 52 | PB conflict analysis: eliminate the pivot by linear combination + reduction, with the M2-L3 clause path as fallback |
| M2-L7 | 5 | Saturate in Explanation.t, and saturation-based reduction as the second plug |
| M2-T1 | 3 | bool_clause, array_bool_or, array_bool_and |
| M2-T10 | 14 | Harness: per-node consistency checking against the brute-force oracle |
| M2-T11 | 3 | Fuzzer: randomise branching order from the announced seed |
| M2-T16 | 1 | Remove proof format 2.0 from the project entirely (D-0046) |
| M2-T2 | 2 | bool2int, bool_eq, bool_not channelling |
| M2-T3 | 9 | Clause learning from conflicts (1UIP), with proof steps |
| M2-T4 | 1 | Learned-clause deletion + matching proof del |
| M2-T5 | 7 | Domain.result reports change granularity; engine masks wakes by trigger kind |
| M2-T6 | 10 | Do not re-wake a propagator from its own prunings; aliased-scope veto + claim re-checker |
| M2-T7 | 22 | Record the propagator instance id on every trail entry and on Conflict |
| M2-T8 | 18 | Propagator interface v2: declarative Reason + separate Justification (D-0026) |
| M2-T9 | 8 | Literal → defining-proof-line index in Justify.ctx, populated by Trace |
| M20-pernode-T2 | 3 | Explanations on demand: under --no-proof and with proof, what keeping every Explanation costs, against building a reason only when conflict analysis ... |
| M20-pernode-T3 | 2 | Compiler and runtime: flambda with -O3, unsafe array access in the measured hot loops (with the BAGUETTE_DEBUG checks kept), the GC settings per ... |
| M20-pernode-T4 | 20 | Data structures on the hot path: domains (sparse sets or bitsets for small domains), watched literals for clauses and PB rows, the event queue, the ... |
| M20-pernode-T5 | 4 | Proof writing: its share of the time (T1), buffered output without Printf, shorter lines, and deleting dead lines earlier |
| M21-memory-T3 | 16 | The fixes the numbers point at, one per kind, each measured on the refused instances (how many become attempts at 16 GiB) |
| M22-review-T1 | 2 | An overflow in the front end's constant fold: builder.ml's lin_terms folded a constant operand of int_lin_* into the right-hand side with an ... |
| M22-review-T11 | 1 | Process-wide state into explicit values: Encoding's limits, row sink and e2e request into a configuration, the hash-consing table owned per solve ... |
| M22-review-T2 | 1 | cumulative misses an overload among fixed tasks: Cumulative.make set ground only for a row with no movable term, and pass reads only the times inside ... |
| M22-review-T5 | 7 | Three latent defects: Encoding.declare_int_gen's redeclaration check ignores holes and representation and uses raise Exit under a shadowing wrapper |
| M22-review-T6 | 1 | Comments that are false, and the header rule: the seven listed in the report corrected |
| M23-inputs-T1 | 1 | lib/scp/sexp.ml: text to a tree of atoms and lists, every node with its position |
| M23-inputs-T2 | 2 | lib/scp/reader.ml, the frame and the arithmetic: version 1, variables, decide/enumerate/minimize/maximize, lin_*, comparisons, and/or, conditions, ... |
| M23-inputs-T4 | 2 | Globals with auxiliary variables: regular, table, circuit, in on variables, multiply, divide |
| M3-T1 | 2 | red-based definitions for reified variables |
| M3-T2 | 4 | Reified linear/comparison propagators + justifications DONE 2026-09-21 (agent-reif), built through M3-T4 as this row asked |
| M3-T4 | 6 | Reification dispatcher: author supplies enforce-hold / enforce-not-hold / entailment |
| M3-T5 | 2 | Proof benchmark reporting .opb bytes, .pbp bytes and verify seconds separately |
| M4-T0 | 6 | Views (±x + k) and constants-as-variables in Var/Store |
| M4-T1 | 26 | all_different (bounds consistent) + Hall-interval justification |
| M4-T10 | 8 | cumulative (and disjunctive as its unit-capacity case): design first, then the time-table propagator — 53 + 16 corpus models |
| M4-T2 | 19 | all_different domain consistent (Régin) — proof story is research-grade |
| M4-T3 | 7 | array_int_element |
| M4-T4a | 3 | Integer interval arithmetic as a standalone, proof-free, unit-tested module |
| M4-T4b | 13 | int_times/int_div/int_abs over M4-T4a |
| M4-T7 | 11 | Let an Explanation ask for the defining id of a bound fact — close the gap M4-T1 made concrete |
| M4-T9 | 9 | array_int_maximum / array_int_minimum as a propagator, and int_max/int_min through it — 94 corpus models name maximum/minimum, all decomposed today ... |
| M5-T1 | 21 | Branch and bound, obju / o / core rules DONE 2026-09-21 (agent-bb). A branch-and-bound bound is exactly an M2-L12 global unit |
| M5-T2 | 4 | conclusion BOUNDS for proved optimality DONE 2026-09-21 (agent-bb). conclusion BOUNDS 2  |
| M6-T10 | 4 | D-0080's lever #2 and the wall clock: Justify's memo as identity buckets under a shallow hash (bench/m6t9/justify-memo.patch, costas prefix 15.32 s → ... |
| M6-T11 | 10 | D-0080's levers #3, #5, #6: Analysis.scan_support compares names as STRINGS (~60 % on prize-collecting) → Var.equal |
| M6-T12 | 2 | Two tidy-ups M6-T9 asked for: a Writer.No_conclusion verdict so Search.conclude_stopped is one call instead of a hand-written epilogue |
| M6-T13 | 6 | D-0085's two leftovers and one mznlib line: (i) Search does per-node work over ALL variables (Search.unfixed, a Hashtbl.replace per variable under ... |
| M6-T14 | 10 | The slow-node instances: Analysis.scan_support still walks the trail — on the 26 formerly-rejected corpus instances the solver does 2-20 nodes/s ... |
| M6-T15 | 9 | Trace.position_of is a linear walk over done_ by physical identity, and Trace.add_fact appends with acc @ [l] — after M6-T14, 2014_mario's 60 s ... |
| M6-T16 | 3 | Analysis builds its frontier with out @ [n] (analysis.ml:395) and add_antecedent the same way (:407) — after M6-T15, 83 % of mario's remaining ... |
| M6-T17 | 2 | Writer.wipe_level folds and sorts the whole tag table on every backtrack, and Justify.wipe_level folds the whole by_level table — 2–2.5 % of mario ... |
| M6-T18 | 13 | Seed the propagation queue from what CHANGED, not from every propagator |
| M6-T19 | 9 | One propagator pass per deduction: alldiff, cumulative, gcc and element restart the whole pass (Moved) after every single pruning |
| M6-T2 | 2 | Minor-GC pressure: move domains/trail to Bigarray/Bytes |
| M6-T20 | 15 | Learned clauses run on every bound change of every variable they name: 1299 of 3732 runs/node on racp, 1731 of 1830 on depot, under 0.2 % effectful |
| M6-T21 | 13 | --time-limit overshoots ~8 %, growing with run length (the user's request of 2026-11-17 in WORKLOG, measured on a linear-code model |
| M6-T22 | 18 | Per-node cost on XOR-heavy Boolean models (the user's request of 2026-11-18, point 1, WORKLOG "codes-cp measurements") |
| M6-T23 | 10 | The --time-limit stop still overshoots by more than 300 s with --proof (D-0137 §13.3) |
| M6-T24 | 20 | An interrupted run ends its proof (the user, 2026-11-24): SIGTERM, SIGINT, SIGXCPU and the heap budget close the proof with the strongest conclusion ... |
| M6-T8 | 1 | BAGUETTE_DEBUG=1 is not clean |
| M6-T9 | 25 | Why 273 of 436 corpus instances time out at 300 s — a --time-limit that stops cleanly and reports stats and incumbent, the config sweep on the node, ... |
| M7-T1 | 18 | Unrestrict the defaults; the limits become options |
| M7-T11 | 15 | Encode a set domain by punching its holes in the ladder, instead of refusing the model |
| M7-T12 | 20 | indomain_median, and the decision shape that cannot express it |
| M7-T13 | 3 | A SECOND RUP defect: 2012_tpp is still rejected after M7-T6 |
| M7-T16 | 12 | A global_cardinality propagator — the global M7-T15 had to decompose |
| M7-T17 | 8 | Trace.derive_ahead fires on a property of the PROPAGATOR, not of the encoding — the per-entry flag trace.ml's own comment names |
| M7-T18 | 7 | global_cardinality with CONSTANT counts — 9 corpus instances refused with *"the count at position 0 is a constant"* |
| M7-T19 | 13 | The ten front-end refusals the wave-30 run left: value choice indomain (4 instances), variable selection anti_first_fail (2), var int with no domain ... |
| M7-T2 | 10 | Honour search annotations |
| M7-T21 | 8 | 26 proofs the checker rejects, hidden until --time-limit let them be checked (D-0080): 23 are ONE shape, rup +1 ~<v>_eq_<k> >= 1  |
| M7-T22 | 5 | The root-conflict defects M7-T21's sweep found, and the sweep as a standing instrument |
| M7-T24 | 11 | gcc is bounds-only and that is why the count route lost (D-0097) |
| M7-T25 | 5 | element's conflicts carry no facts, so an element conflict never learns a clause (D-0091's finding) |
| M7-T27 | 26 | The wall is memory, in three places, and the objective's width is not one of them (D-0123). The recount of the 543 Challenge refusals |
| M7-T28 | 32 | The decomposed globals that kill the search, in payoff order (D-0122) |
| M7-T29 | 2 | Two small front-end refusals from the editions (D-0121): fzn_global_cardinality with the same variable twice (gcc.ml's tally assumption |
| M7-T31 | 5 | A branch nogood the checker refuses under restarts with phase saving and a dynamic order (first thought to be the ASSIGNMENT decision of D-0077 |
| M7-T32 | 11 | The MiniZinc standard flags, as the Challenge calls a solver: tools/baguette.msc declares "stdFlags" |
| M7-T33 | 11 | alldiff conflicts carry no facts, so nothing is learned from them |
| M7-T34 | 4 | member without width-proportional rows (D-0159 §5, D-0167 item 2) |
| M7-T35 | 1 | Six member models stop under BAGUETTE_DEBUG on the D-0026 agreement check, on main too (found by M16-file-review-T1, D-0186 §6) |
| M7-T6 | 5 | A correct answer whose proof the checker rejects — pre-existing, reproducer shipped |
| M7-T7 | 1 | Skip constants in a search array instead of refusing the model |
| M7-T8 | 21 | A graceful resource guard: an over-large encoding must diagnose, not Fatal error |
| M7-T9 | 7 | The four missing search strategies: smallest, largest, indomain_split, indomain_median |
| M8-T2 | 2 | Encoding, rows and Linear only: encoding.ml/lit.ml/opb.ml for a bits variable, expand_int_lin_le over mixed terms, linear.ml's justification through ... |
| M8-bits-encoding-T2 | 37 | Encoding, rows and Linear only: encoding.ml/lit.ml/opb.ml for a bits variable, expand_int_lin_le over mixed terms, linear.ml's justification through ... |
| M8-bits-encoding-T3 | 28 | The full substrate: Weaken, Order_reason's chains, Ladder for PB conflict analysis (or the clause fallback, measured), trace lines that today rely on ... |
| M8-bits-encoding-T5 | 13 | The cheap half (D-0127): emit the order arm's ladder-walk justifications as rup, not as the Θ(w)-token pol fold |
| M9-no-proof-T2 | 14 | Implement: Compile with the encoding half skipped (ids still counted), bin/main.ml with no Writer/Justify, --stats saying so |
| M9-no-proof-T4 | 6 | The audit: every computation that serves only the proof and still runs under --no-proof, in the code merged since D-0135 (bits atoms and PB analysis ... |
| M9-no-proof-T5 | 9 | The default keeps the proof (the user's decision, 2026-11-19) |

## Invariants (docs/INVARIANTS.md)

| Id | Cited | What it is about |
|---|---|---|
| I-D1 | 9 | lo <= hi for every unfixed variable; a domain with lo > hi is failure and |
| I-D2 | 16 | lo and hi are themselves in the domain — holes are never at the bounds. |
| I-D3 | 19 | A domain only ever shrinks within a decision level. |
| I-M1 | 1 | A failing test is information. The expected outputs in test/expected/ and the |
| I-P1 | 7 | Soundness: a propagator removes only values that cannot extend to a solution of |
| I-P2 | 31 | Fixpoint: when engine.propagate returns without failure, running any |
| I-P3 | 3 | Checking: with all variables fixed, a propagator reports failure iff the |
| I-P4 | 16 | Every change carries an explanation. Enforced by the type — the function that |
| I-P5 | 19 | *(merged into I-P4 by M2-T8 — kept for its history, which is the reason the |
| I-P6 | 13 | One snapshot, every deduction (M6-T19). A pass photographs the store once (its |
| I-P7 | 22 | An advisor answers for a wake it drops (M6-T20, D-0104). An instance's |
| I-S1 | 14 | Every solution printed satisfies every constraint — re-checked independently by |
| I-S2 | 2 | The search is complete: =====UNSATISFIABLE===== is only printed after the |
| I-S3 | 2 | Decision level on return from search equals the level on entry. |
| I-S4 | 61 | A trace line that cites a hole is supported only while that hole's own line is |
| I-T1 | 17 | backtrack_to l restores every domain to exactly its state when level l was |
| I-T2 | 12 | Trail entries are strictly ordered by level; the level marks are monotone. |
| I-T3 | 6 | Every trail entry has an explanation index that resolves. No orphan reasons. |
| I-T4 | 4 | Every trail entry names the propagator instance that made it, in entry.prop, |
| I-X10 | 38 | Every trace line a propagator emits is RUP against the .opb plus the lines |
| I-X2 | 60 | Constraint ids are deleted exactly once. Checked at conclusion time under |
| I-X3 | 12 | Proof state mirrors solver state: a reason that has been deleted from the proof |
| I-X4 | 2 | The proof is append-only and never rewound. Backtracking in the solver becomes |
| I-X5 | 11 | The .opb is written before any .pbp rule references it, and its constraint |
| I-X6 | 69 | A Deferred explanation's thunk closes over a snapshot and never reads live |
| I-X7 | 3 | What conclusion UNSAT cites is a line the checker has itself established is a |
| I-X8 | 19 | No row is committed to the .opb whose arithmetic wrapped. |
| I-X9 | 9 | An explanation justifies the bound as recorded on the trail, not the bound |
