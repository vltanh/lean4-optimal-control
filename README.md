# Optimal control in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-optimal-control/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-optimal-control/actions/workflows/lean_action_ci.yml)

Optimal control theory in Lean 4 with Mathlib: **the Pontryagin maximum principle** (free terminal
time, integral cost, mixed boundary conditions, strong local minimizers), by the argument of
Agrachev and Sachkov, and **Filippov's theorem** on the compactness of attainable sets, with the
existence of optimal controls.

Control systems have measurable controls and Carathéodory trajectories. Everything is proved: there
is no `sorry`, no `axiom` and no `native_decide`.

## Main results

| Lean | Statement | Source |
| --- | --- | --- |
| [`Pontryagin.maximum_principle`](OptimalControl/Pontryagin/MaximumPrinciple.lean#L320) | the maximum principle with free terminal time, an integral cost and mixed boundary conditions `(q(0), q(T)) ∈ N`, for strong local minimizers | Agrachev–Sachkov, Theorem 12.5 with the remark after it (free time), a case left to the reader there |
| [`Pontryagin.theorem12_1`](OptimalControl/Pontryagin/Geometric.lean#L710) | the geometric maximum principle: if the end point lies on the boundary of the attainable set, a Lipschitz covector curve with `p(t) ≠ 0` satisfies the adjoint equation and the maximum condition | Agrachev–Sachkov, Theorem 12.1 |
| [`theorem12_2`](OptimalControl/Pontryagin/FreeTime.lean#L78), [`theorem12_3`](OptimalControl/Pontryagin/IntegralCost.lean#L542), [`theorem12_4`](OptimalControl/Pontryagin/IntegralCost.lean#L608), [`theorem12_5`](OptimalControl/Pontryagin/IntegralCost.lean#L725) | free time without cost; integral cost with fixed end points, with `q(0) ∈ N₀` and `q(t₁) ∈ N₁`, and with `(q(0), q(t₁)) ∈ N` | Agrachev–Sachkov, Theorems 12.2–12.5 |
| [`Pontryagin.lemma12_1`](OptimalControl/Pontryagin/Geometric.lean#L72), [`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`](OptimalControl/Convex/Cone/Openness.lean#L70) | a map Lipschitz near the vertex `0` of a convex cone, with `F(0) = 0` and derivative mapping the cone onto the space, sends every neighbourhood of `0` in the cone to a neighbourhood of `0` | Agrachev–Sachkov, Lemma 12.1 and its Remark (1) |
| [`Pontryagin.lemma12_2`](OptimalControl/Pontryagin/Geometric.lean#L608) | if the needle vectors generate the space as a convex cone, the end point is interior to the attainable set | Agrachev–Sachkov, Lemma 12.2 |
| [`ControlSystem.isCompact_reachableSet`](OptimalControl/ODE/ControlSystem.lean#L405), [`isCompact_reachableSetLE`](OptimalControl/ODE/ControlSystem.lean#L383) | Filippov's theorem: with `F` continuous, `U` compact, convex velocity sets and bounded velocities, the attainable sets at time `T` and up to time `T` are compact | Agrachev–Sachkov, Theorem 10.1 |
| [`ControlSystem.exists_optimal_fixedTime`](OptimalControl/ODE/ControlSystem.lean#L514), [`exists_optimal_freeTime`](OptimalControl/ODE/ControlSystem.lean#L548) | optimal controls exist for integral costs whose extended velocity sets are convex, with fixed or free terminal time | Agrachev–Sachkov, Theorem 10.1, applied to the system extended by the cost |
| [`ControlSystem.isCompact_constrainedEndpoints`](OptimalControl/ODE/StateConstraint.lean#L309), [`exists_optimal_constrained`](OptimalControl/ODE/StateConstraint.lean#L378) | the same two results with a closed state constraint, a compact set of initial points, a closed endpoint relation and a window of terminal times | extends Agrachev–Sachkov, Theorem 10.1 (same argument) |
| [`MeasureTheory.exists_measurable_forall_mem_ae_eq_zero`](OptimalControl/MeasureTheory/MeasurableSelection.lean#L261) | zeros of a Carathéodory function on a compact set can be chosen measurably | Kuratowski–Ryll-Nardzewski; Filippov's lemma |

`E` (states), `V` (control values) and the parameter spaces of boundary conditions are
finite-dimensional real normed spaces; in Filippov's theorem `V` need only be a metric space. The
control set `U ⊆ V` is compact and the state constraint `Ω ⊆ E` is open.

More documentation:

- [docs/DETAILS.md](docs/DETAILS.md): the full statements and definitions in Lean, the
  Carathéodory theory beneath, measurable selection, the method of proof and every file.
- [docs/AGRACHEV_SACHKOV.md](docs/AGRACHEV_SACHKOV.md): Agrachev and Sachkov's Chapter 12 result by
  result, the readings and departures D1–D11, and the gaps found in the source.

## Lean statement of record

[`OptimalControlChallenge.lean`](OptimalControlChallenge.lean) imports only Mathlib and states,
with `sorry`, the maximum principle, Filippov's theorem and the existence of optimal controls.

[`OptimalControlSolution.lean`](OptimalControlSolution.lean) proves them from the library;
Palomar's Comparator ([`comparator.json`](comparator.json)) checks that it proves exactly these
statements with the standard axioms ([details](docs/DETAILS.md#the-statements-of-record)).

## Using it from another Lake project

Add to the `lakefile.toml` of your project, with a full commit hash of this repository in place of
the placeholder:

```toml
[[require]]
name = "OptimalControl"
git = "https://github.com/vltanh/lean4-optimal-control"
rev = "<full commit hash>"
```

and import the modules you need, for instance `public import OptimalControl.Pontryagin` in a
module, or `import OptimalControl` for everything. The package requires Lean and Mathlib
`v4.36.0-rc2` (your project should use the same versions) and depends on
[FixedPoint](https://github.com/vltanh/lean4-fixed-point) for Brouwer's fixed-point theorem.

## Building

```sh
lake exe cache get                               # Mathlib's compiled files
lake build                                       # the library, the Challenge and the Solution
lake env lean scripts/Audit.lean                 # the axioms; fails on any non-standard axiom
python3 scripts/sync_challenge_defs.py --check   # the Challenge's copy of the shared definitions
lake env lake comparator --config=comparator.json   # the Solution proves the Challenge
```

- The audit checks that the main theorems and every declaration of the library, private and
  auxiliary ones included, depend only on `propext`, `Classical.choice` and `Quot.sound`. It
  fails on any other axiom, `sorryAx` included.
- Comparator needs bubblewrap; on success it prints "Your solution is okay!".
- The library and the Solution build without warnings; the Challenge's only warnings are its
  `sorry`s.
- CI builds the library and the Solution with `--wfail`, builds the Challenge, runs the audit,
  checks that the audit imports every module, checks the Challenge's copy of the shared
  definitions, and checks that no line exceeds 100 characters.

## Layout

| Path | Content |
| --- | --- |
| [`OptimalControl/Defs.lean`](OptimalControl/Defs.lean) | the definitions that the statements of record use (shared with the Challenge) |
| [`OptimalControl/Pontryagin/`](OptimalControl/Pontryagin) | the maximum principle: Lemmas 12.1–12.2, Theorems 12.1–12.5, the free-time form |
| [`OptimalControl/ODE/`](OptimalControl/ODE) | Filippov's theorem (also with a state constraint), Carathéodory theory, needle variations, time changes |
| [`OptimalControl/Convex/Cone/`](OptimalControl/Convex/Cone) | supporting hyperplanes and finite generation of cones; openness at the vertex of a cone |
| [`OptimalControl/MeasureTheory/`](OptimalControl/MeasureTheory) | measurable selection, Lebesgue points |
| [`OptimalControlChallenge.lean`](OptimalControlChallenge.lean), [`OptimalControlSolution.lean`](OptimalControlSolution.lean), [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml) | Palomar: the statements of record, their proofs, Comparator's configuration, the metadata |
| [`scripts/`](scripts) | the axiom audit; the copy of the shared definitions into the Challenge |
| [`.github/workflows/`](.github/workflows) | CI; Palomar's mechanical verification of a commit, run only on demand |

Every module is listed in [docs/DETAILS.md](docs/DETAILS.md#files).

## Other formalizations

The Lean development [willcforte/pontryagin-lean](https://github.com/willcforte/pontryagin-lean)
("An attempt to formalize Pontryagin's Maximum Principle in Lean") states the key steps of the
proof (Carathéodory existence, the adjoint equation, the tangent cone of the attainable set, the
separation) as axioms.

No complete formal proof of the maximum principle was found. This package does not depend on that
development; its proofs follow Agrachev and Sachkov.

## References

- A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the Geometric Viewpoint*,
  Encyclopaedia of Mathematical Sciences 87, Springer, 2004 (Chapter 10, Theorem 10.1; Chapter
  12). Page numbers in the docstrings are those of the authors' draft (preface September 2003),
  posted on A. A. Agrachev's home page
  (<https://people.sissa.it/~agrachev/agrachev_files/books.html>).
- R. V. Gamkrelidze, *Principles of Optimal Control Theory*, Plenum, 1978.

## Credits

- Author of record and maintainer: The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## License

Apache-2.0; see [LICENSE](LICENSE).
