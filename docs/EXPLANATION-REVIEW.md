# Review: the explanation mechanism against the explanation literature

Status: **report only — no code, roadmap or decision changes made.** Produced 2026-09-18 by
a session working on `~/Explanations-by-constraint-decomposition`, which had just surveyed
the CP explanation literature (LCG, explaining propagators, step-wise explanations, proof
logging) and read `lib/core/`, `docs/GCS-COMPARISON.md` and `docs/ROADMAP.md` here.

**Not built, not run.** Every claim below is read off the tree or off a roadmap row, and
labelled where that matters. `GCS-COMPARISON.md` compares against one mature solver; this
compares against the published literature on explanation, which is a different axis and
reaches a different conclusion in one place (§2).

Two findings from an earlier draft were **withdrawn after checking the roadmap**: integer
overflow (M1-T23, DONE) and the uncapped Θ(width) order encoding (M1-T25/M1-T54, DONE).
They are named here only so the next reader does not resurrect them from the GCS document,
which predates both.

---

## 0. The verdict in one line

The machinery is at or ahead of the state of the art in three specific places (§1, §5).
The **evidence** is not, because nothing hard has been explained yet (§3). baguette is
currently a high-quality *proof-logging* solver whose explanation design is unusually
principled; it is not yet an *explanation* contribution.

---

## 1. Where this is ahead of the literature — protect these

### 1.1 `concludes` is the strongest original idea in the tree, and it is under-advertised

`Reason.justified.concludes` (D-0043) answers "what did this pruning derive", checked in
`Store.apply` against the bound actually set. The failure it catches — a `pol` truncated so
it derives something strictly *weaker* than the propagator claimed, which the checker
accepts silently — is real (M1-T51 measured it) and **nothing in the explanation literature
does this**. GCS's nearest relative is `AssertRatherThanJustifying`, and their own docs say
"not a single one of them may ever be merged, and nothing in the test suite or CI will stop
you."

> ⚠️ **Warning for whoever is tempted to simplify it.** It cost 13 call sites in `lib/` and
> 46 in `test/`, it looks like ceremony, and a future session *will* propose making it a
> defaulted `?concludes`. That is the same move D-0026 already reversed once when I-P5
> collapsed into I-P4. The cost is the property. If it is ever relaxed, the relaxation
> needs a decision record arguing against this paragraph.

### 1.2 The slack-based stopping criterion is correct for the right reason

`pb_analysis.assertive_slack` stops on slack rather than counting conflict-level literals,
citing Le Berre et al. for why assertiveness gives no backjump guarantee over PB. This is a
subtle point implementations routinely get wrong, and reading Koops et al. (CP 2025) closely
enough to conclude that adjacent-weakening merging is *CakePB's* pass rather than an emitter
obligation is the difference between reading a paper and citing one.

> ⚠️ **Warning.** A future optimisation that reintroduces literal counting — because it is
> cheaper, or because it "matches the SAT solver" — reintroduces the bug the citation exists
> to prevent, and it will not show up as a wrong answer. It shows up as worse backjumps.

### 1.3 Reason/justification split, and proof mutation testing

Both are current best practice. GCS reached 1.1 only after measuring closure-valued reasons
at ~20% of runtime; here it is by design, with non-narrowability enforced by the type
(`Reason.lits` takes no store, so it *cannot* read live state). Mutation testing of the
proof is ahead of most solvers — and already caught a lane that was green as a *parse*
error rather than a derivation failure.

---

## 2. The "higher-order" claim: an argument `GCS-COMPARISON.md` §6 did not consider

§6 of that document states the open question sharply:

> we have a reified cutting-planes expression on the trail where the mature solver has a
> closure, and nobody has yet said what the reified form buys. That is evidence against (a)
> being the productive axis.

That conclusion follows only if explanations are a **solver internal**. There is an answer
from the literature side, and it is not a performance argument:

**A closure cannot be printed, diffed, compared against a published explanation, lifted into
a schema, or shipped anywhere. A reified `Combine` tree can.**

Every use of explanations *outside* a solver's own conflict analysis needs them as data:
comparing a generated explanation against Schutt et al.'s hand-written cumulative
explanation; cataloguing explanation schemas per constraint; handing a derivation to an
external justifier; step-wise explanation systems consuming solver output (Bogaerts/Guns,
and the 2025 certifying-solvers work that replaces MUS search with proof-log reading).
GCS's own "higher-order" content is a typed serialisable witness for an external justifier —
i.e. they reified it too, just at a different boundary.

> ⚠️ **Warning.** If `Deferred`/`Combine` is ever retired in favour of a closure on runtime
> grounds, that decision is only sound if the project has *also* decided explanations are
> not a research output. Those two decisions are coupled and the coupling is currently
> unrecorded. D-0003's (a)-claim should be closed by an argument about exportability, or
> explicitly abandoned — not left to be settled by a profiler.

---

## 3. The load-bearing gap: nothing hard has been explained yet

`lib/core/prop/` is seven modules, of which `int_le`, `int_lt`, `int_eq`, `lin_eq` are
aliases or specialisations of `Linear`. There is **no global constraint**. `all_different`
is M4-T1 and unstarted.

Every explanation paper in the literature exists because *globals* are hard to explain:
Schutt et al. on `cumulative`, Downing et al. on `alldifferent`, Gange et al. on MDD,
Francis & Stuckey on `circuit`, McIlree & McCreesh on smart tables. Linear rows and clauses
are the case nobody doubted.

> ⚠️ **Warning, and it is the main one.** The green suite is evidence that the explanation
> design works **for linear rows and clauses**. It is not evidence that `Combine` / `Weaken`
> / `Model_row` survive a derivation that needs them. M4-T1 is the first real test: a Hall
> justification cites many model rows in one derivation (per Hall value a recovered
> at-most-one line, per Hall variable an at-least-one line — `GCS-COMPARISON.md` §3). The
> design anticipates it, which is why `Model_row` exists; anticipation is not evidence.
>
> Concretely: **do not let M4-T1 be scheduled as "another propagator."** It is the
> experiment that decides whether the project's central claim holds. Budget it as one.

---

## 4. The PB negative result predicts something, and the prediction is not written down

The M2-L6 commit reports honestly that where the PB path succeeds it derives the empty
contradiction, and that a scene where a non-trivial learned inequality outpropagates its
clause "was looked for and NOT FOUND". The explanation given is the valuable part:

> our integer propagator is STRONGER than PB propagation on the same row. `3a+2b<=14` with
> `lo(b)=4` lets `Linear` deduce `a<=2`, but the row alone has slack 6 against pivot
> coefficient 3, because the ladder implications live in SEPARATE `.opb` rows.

> ⚠️ **Warning.** That is a *prediction*, not just a post-hoc explanation: PB learning will
> keep producing degenerate rows for as long as a reason is the model row without its ladder
> chain. It currently lives in one commit message and one module header, so whoever takes
> M2-L7 or the next PB row can reasonably re-run the same experiment and re-derive the same
> negative. It belongs in `DECISIONS.md` as a recorded prediction with a falsifier, so that
> the next attempt starts from "carry the ladder rows into the reason" rather than from zero.

---

## 5. What the test suite cannot currently see

`GCS-COMPARISON.md` §3 records that nothing checks a propagator reaches the strength its
`consistency` tag claims — the oracle checks soundness only. For **explanations** the gap is
wider: there is no analogue at all.

The entire quality metric in the explanation literature is **generality** — a shorter,
weaker-premised explanation prunes more in future states, and that is the whole reason
Schutt et al.'s window explanation beats naming every task, and why Downing et al. compare
three `alldifferent` propagators rather than picking one.

> ⚠️ **Warning.** A **sound but maximally weak** explanation — one naming every variable in
> scope — passes every test in this repository today, and VeriPB accepts it. There is no
> failing test, no oracle and no counter that would notice. That is tolerable while every
> propagator is linear, because the derivation is forced. It stops being tolerable at M4-T1,
> where the *choice* of Hall set is exactly the thing that makes the explanation good or
> useless, and where a trivially-correct maximal explanation is easy to write by accident.
>
> M2-T10 proposes per-node consistency checking against the brute-force oracle. The
> explanation-side sibling — assert something about explanation *size or generality*, even
> just recording it per model so a regression is visible — does not exist as a roadmap row.
> It should exist before M4-T1, not after.

---

## 6. M1-T44 is thesis-level, not merely highest-priority

`README.md` and `CLAUDE.md` both open with: *the proof is a primary output, not a debugging
option; every pruning the solver makes must be able to justify itself.*

M1-T44 is a correct UNSAT answer whose proof the checker rejects — the derivation lands on
`0 >= 0`, one unit short. It is already ranked highest-priority open defect, so the ranking
is not the issue.

> ⚠️ **Warning about how it is framed.** Every other open row is performance, scale, or a
> missing feature. M1-T44 is the only one where the proof layer's own *claim* is wrong
> rather than weak, and it is therefore the only open item that contradicts the sentence the
> project leads with. If it is ever deprioritised behind feature work, that trade is
> bigger than a roadmap reshuffle and deserves saying out loud.

---

## 7. Unverified / out of scope

- Nothing here was built or run; no benchmark was taken.
- §3's claim that no global constraint exists is read off `lib/core/prop/` and SPEC §2.1's
  milestone table; M4 rows are TODO.
- Whether a Hall justification actually fits `Combine`/`Weaken`/`Model_row` is **unverified**
  and is precisely what §3 says M4-T1 must find out.
- No opinion is offered on engine, search, or the FlatZinc front end; this review is scoped
  to the explanation mechanism.
