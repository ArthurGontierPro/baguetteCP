# VeriPB: a `red` without subproof in strengthening-to-core mode is never checked against earlier derived constraints, so a false UNSAT verifies

**Versions affected.** VeriPB 3.0.2, current `main` of https://gitlab.com/MIAOresearch/software/VeriPB
(`f50be28430c8d141cbdbaa7f6dfae316d150f8e4`, 2026-11-18), and the older builds `d5644ca4` (2026-09-04)
and `78db9573` (2026-06-18).

**Minimal example.** The formula has one variable and no constraint, so it is satisfiable.

`one.opb`
```
* #variable= 1 #constraint= 0
```

`one.pbp`
```
pseudo-Boolean proof version 3.0
f 0 ;
strengthening_to_core on ;
red +1 x1 >= 1 : x1 -> 1 ;
red +1 ~x1 >= 1 : x1 -> 0 ;
rup >= 1 ;
output NONE ;
conclusion UNSAT : -1 ;
end pseudo-Boolean proof ;
```

```
$ veripb one.opb one.pbp
Running VeriPB version 3.0.2
s VERIFIED UNSATISFIABLE
```

**Expected.** The second `red` must be rejected: its witness `x1 -> 0` falsifies `x1 >= 1`, derived by
the first `red`. Each `red` is sound on its own, but not both together.

**Control.** Without the line `strengthening_to_core on ;`, the same proof is rejected:
`Proofgoal 1 could not be autoproven. Please add an explicit subproof for proofgoal 1.`

**Likely cause.** In strengthening-to-core mode `red` builds its proof goals with
`add_derived_goals = !context.is_strengthening_to_core`
(`veripb-checker/src/rules/red_strengthening.rs`, line 114), so derived constraints yield no goal. But a
`red` WITHOUT a subproof keeps the default `add_constraints_to_core` (returns `false`,
`veripb-checker/src/rules.rs`, line 99), so its own constraint goes to the DERIVED set, not the core.
The next `red` therefore never checks its witness against it. (With a subproof, `add_to_core =
context.is_strengthening_to_core` is set, line 133.) Either such a `red`'s constraint should be added to
the core in this mode, or derived goals should not be skipped for it.

**Found** while prototyping certified symmetry breaking for the baguette CP solver (two `red` lines,
each with a variable swap as witness, made a satisfiable instance `x1 + x2 = 1` "UNSAT"); reduced to the
example above.
