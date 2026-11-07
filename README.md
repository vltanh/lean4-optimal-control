# Optimal control in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-optimal-control/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-optimal-control/actions/workflows/lean_action_ci.yml)

Optimal control theory in Lean 4 with Mathlib: control systems with Carathéodory trajectories,
**Filippov's theorem** on the compactness of attainable sets and the existence of optimal controls,
and **the Pontryagin maximum principle**, stated and being proved by the argument of Agrachev and
Sachkov (Chapter 12 of *Control Theory from the Geometric Viewpoint*).

**Status: work in progress.** Filippov's theorem and the measurable selection it uses are proved.
The maximum principle and the Carathéodory theory beneath it are stated, with the structure of
Agrachev and Sachkov's proof, and 50 declarations still end in `sorry` (the audit lists them).
The repository is to be published once it is sorry-free.

## What is stated and proved

`E`, `V` and `Q` are finite-dimensional real normed spaces (`E` the state space, `V` the space of
control values); the control set `U ⊆ V` is compact. The declarations of the maximum principle are
in the namespace `Pontryagin`, those on control systems in `ControlSystem`.

- [`Pontryagin.maximum_principle`](OptimalControl/Pontryagin/MaximumPrinciple.lean#L83) (stated,
  proof in progress), the maximum principle with free terminal time, an integral cost and mixed
  boundary conditions, for strong local minimizers (Agrachev–Sachkov, Theorem 12.5 with its
  Remark (1)):

  ```lean
  theorem maximum_principle {Ω : Set E} (hΩ : IsOpen Ω) {U : Set V}
      (hU : IsCompact U) {f : E → V → E} (hf : IsC1On f Ω U) {φ : E → V → ℝ}
      (hφ : IsC1On φ Ω U) {N : Set (E × E)} {T : ℝ} {ũ : ℝ → V} {q : ℝ → E}
      (hmin : IsStrongLocalMinimizer f φ Ω U N T ũ q) {G : E × E → Q}
      (hG : ContDiffAt ℝ 1 G (q 0, q T)) (hGsurj : Function.Surjective (fderiv ℝ G (q 0, q T)))
      (hG0 : G (q 0, q T) = 0) (hGN : ∀ᶠ z in 𝓝 (q 0, q T), G z = 0 → z ∈ N) :
      ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), ν ≤ 0 ∧ (∃ K, LipschitzOnWith K p (Icc 0 T)) ∧
        (∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) ∧ IsAdjoint f φ ν ũ q T p ∧ IsMaximal f φ ν U ũ q T p ∧
        (∀ᵐ t ∂(volume.restrict (Icc 0 T)), controlHamiltonian f φ ν (q t) (p t) (ũ t) = 0) ∧
        ∀ v w : E, fderiv ℝ G (q 0, q T) (v, w) = 0 → -p 0 v + p T w = 0
  ```

  Here `IsC1On f Ω U` ([`ControlSystem.IsC1On`](OptimalControl/ODE/Caratheodory.lean#L70)) is
  Agrachev and Sachkov's regularity (10.2)–(10.4) with `C¹` for `C^∞`;
  [`IsStrongLocalMinimizer`](OptimalControl/Pontryagin/Defs.lean#L122) says that `(ũ, q)` is an
  admissible pair in `Ω` on `[0, T]` with `(q(0), q(T)) ∈ N` whose cost `∫₀ᵀ φ(q, ũ)` is least
  among the admissible pairs satisfying the boundary condition with terminal time and trajectory
  uniformly close; [`IsAdjoint`](OptimalControl/Pontryagin/Defs.lean#L101) is the adjoint equation
  `ṗ = -p ∘ ∂ₓf(q, ũ) - ν ∂ₓφ(q, ũ)` in integral form,
  [`IsMaximal`](OptimalControl/Pontryagin/Defs.lean#L111) the maximum condition for almost every
  `t`, and [`controlHamiltonian`](OptimalControl/Pontryagin/Defs.lean#L82) is
  `⟨p, f(q, u)⟩ + ν φ(q, u)`.
- Agrachev and Sachkov's Theorems 12.1–12.5 (stated, proofs in progress):
  [`Pontryagin.theorem12_1`](OptimalControl/Pontryagin/Geometric.lean#L161) (the geometric
  maximum principle at a boundary point of the attainable set),
  [`Pontryagin.theorem12_2`](OptimalControl/Pontryagin/FreeTime.lean#L46) (free time),
  [`Pontryagin.theorem12_3`](OptimalControl/Pontryagin/IntegralCost.lean#L64),
  [`Pontryagin.theorem12_4`](OptimalControl/Pontryagin/IntegralCost.lean#L91) and
  [`Pontryagin.theorem12_5`](OptimalControl/Pontryagin/IntegralCost.lean#L119) (integral cost,
  fixed time, with fixed end points, separated and mixed boundary conditions); their Lemmas 12.1
  ([`Pontryagin.lemma12_1`](OptimalControl/Pontryagin/Geometric.lean#L60), and on convex cones
  [`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`](OptimalControl/Convex/Cone/Openness.lean#L57))
  and 12.2 ([`Pontryagin.lemma12_2`](OptimalControl/Pontryagin/Geometric.lean#L77)); and the form
  from which the rest is derived,
  [`Pontryagin.exists_costate_of_boundary`](OptimalControl/Pontryagin/Geometric.lean#L134).
- **Filippov's theorem** (proved):
  [`ControlSystem.isCompact_reachableSet`](OptimalControl/ODE/ControlSystem.lean#L422) and
  [`ControlSystem.isCompact_reachableSetLE`](OptimalControl/ODE/ControlSystem.lean#L400): for
  `F` jointly continuous, `U` compact, convex velocity sets `F(x, U)` and velocities bounded along
  admissible trajectories, the attainable sets at time `T` and up to time `T` are compact:

  ```lean
  theorem isCompact_reachableSet (hF : Continuous fun p : E × V ↦ F p.1 p.2)
      (hU : IsCompact U) (hconv : ∀ z, Convex ℝ (F z '' U)) {x₀ : E} {T M : ℝ} (hT : 0 ≤ T)
      (hM : 0 ≤ M)
      (hbd : ∀ u x, IsAdmissible F U x₀ T u x → ∀ s ∈ Icc 0 T, ‖F (x s) (u s)‖ ≤ M) :
      IsCompact (reachableSet F U x₀ T)
  ```

  Here `V` is only a metric space with its Borel σ-algebra, and an admissible pair
  ([`ControlSystem.IsAdmissible`](OptimalControl/ODE/ControlSystem.lean#L114)) is a measurable
  control with values in `U` and a Carathéodory solution. Hence the existence of optimal controls
  for integral costs when the velocity sets extended by the cost are convex, with fixed
  ([`ControlSystem.exists_optimal_fixedTime`](OptimalControl/ODE/ControlSystem.lean#L531)) or
  free ([`ControlSystem.exists_optimal_freeTime`](OptimalControl/ODE/ControlSystem.lean#L565))
  terminal time.
- **Measurable selection** of zeros of Carathéodory functions on a compact set (proved;
  Kuratowski–Ryll-Nardzewski construction, Filippov's lemma):
  [`MeasureTheory.exists_measurable_forall_mem_ae_eq_zero`](OptimalControl/MeasureTheory/MeasurableSelection.lean#L261).

There is no `axiom` or `native_decide`. `lake env lean scripts/Audit.lean` prints the axioms of
the main theorems and checks that every declaration of the library depends only on `propext`,
`Classical.choice`, `Quot.sound` and, while the library is not sorry-free, `sorryAx`; it lists
the declarations that contain a `sorry` in a warning. Once the last `sorry` is proved, setting
`Audit.allowSorry` to `false` makes `sorryAx` fail the audit.

## Method

The maximum principle follows Agrachev and Sachkov's proof (Chapter 12). The needle variations of
a reference control at Lebesgue points give vectors `g_{τ,u}` (12.12), computed through the
resolvent of the variational equation; if they generated the whole tangent space as a convex
cone, the end point map of finitely many needles would be open at the reference (Lemma 12.2, by
Lemma 12.1, whose proof uses **Brouwer's fixed-point theorem**, taken from the
[FixedPoint](https://github.com/vltanh/lean4-fixed-point) package as `Brouwer.exists_fixedPoint`).
So at a boundary point of the attainable set a supporting covector exists, and transported back
along the trajectory it is the costate (Theorem 12.1). Free time, costs and boundary conditions are
reduced to this case by Agrachev and Sachkov's auxiliary systems (Theorems 12.2–12.5), which
[`Pontryagin.maximum_principle`](OptimalControl/Pontryagin/MaximumPrinciple.lean#L83) applies
together. The Carathéodory theory (existence, uniqueness and differentiable dependence of
solutions, the cut-off near a trajectory) is proved by Picard iteration and Gronwall's inequality.

Filippov's theorem is proved by the standard argument: the trajectories are equi-Lipschitz, a
cluster point exists by Tychonoff's theorem, its derivative lies in the convex velocity set
almost everywhere, and a measurable control realizing it is found by measurable selection.

### Readings and departures from Agrachev–Sachkov

The source is the authors' draft of the book (preface September 2003), posted on A. A.
Agrachev's home page (<https://people.sissa.it/~agrachev/agrachev_files/books.html>); page numbers
in the docstrings are the draft's. The docstrings refer to these departures:

- D1. The manifold `M` is an open subset `Ω` of a finite-dimensional real normed space `E`.
- D2. The chronological calculus (operators on `C^∞(M)`; (2.19), (2.28), (2.31), Proposition
  11.3) is read pointwise along trajectories, in coordinates.
- D3. The system and the cost are `C¹` in the state instead of `C^∞` (a generalization).
- D4. `U` is compact (the local boundedness of `f(q, u(t))` is tacit in the source); the
  auxiliary parameter sets of §§12.3–12.4 are compact intervals.
- D5. Strong local minimizers instead of optimal (globally minimizing) controls (a
  generalization).
- D6. Free time together with a cost and mixed boundary conditions, left by Agrachev and Sachkov
  as an exercise and remarks, assembled from Theorems 12.2 and 12.5.
- D7. Time scalings are measurable (bi-Lipschitz reparametrizations) where the source derives
  the formula for smooth ones.
- D8. Lemma 12.1 in the form of its Remark (1), on a convex cone, with a one-sided derivative.
- D9. One separating covector for all needle variations, by a finite subfamily, in Theorems
  12.4 and 12.5.
- D10. Brouwer's theorem, for which the source gives no reference, from the FixedPoint package.
- D11. Carathéodory well-posedness and differentiable dependence, which the source cites to
  Gamkrelidze (1978), are proved by Picard iteration and Gronwall's inequality (the cited texts
  were not consulted); a cut-off to a compact tube replaces the source's assumption that the
  vector fields are complete.

References:

- A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the Geometric Viewpoint*,
  Encyclopaedia of Mathematical Sciences 87, Springer, 2004 (Chapter 10, Theorem 10.1; Chapter
  12).
- R. V. Gamkrelidze, *Principles of Optimal Control Theory*, Plenum, 1978.

## Using it from another Lake project

Add to the `lakefile.toml` of your project:

```toml
[[require]]
name = "OptimalControl"
git = "https://github.com/vltanh/lean4-optimal-control"
rev = "<commit>"
```

and import the modules you need, for instance `public import OptimalControl.Pontryagin` in a
module, or `import OptimalControl` for everything. The package requires Mathlib `v4.36.0-rc2`
and [FixedPoint](https://github.com/vltanh/lean4-fixed-point); your project should use the same
Mathlib version.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build
lake env lean scripts/Audit.lean   # axioms, and the list of sorries
```

Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`.

## Layout

| Path | Content |
| --- | --- |
| [`OptimalControl.lean`](OptimalControl.lean) | imports the whole library |
| [`OptimalControl/Pontryagin.lean`](OptimalControl/Pontryagin.lean) | imports the maximum principle, and through it every other module |
| [`OptimalControl/MeasureTheory/MeasurableSelection.lean`](OptimalControl/MeasureTheory/MeasurableSelection.lean) | measurable selection of zeros of Carathéodory functions on a compact set; measurability of `{t \| ∃ w ∈ C, g t w = 0}` |
| [`OptimalControl/MeasureTheory/LebesguePoints.lean`](OptimalControl/MeasureTheory/LebesguePoints.lean) | Lebesgue points of a control within an interval: almost every point is one, and they are dense |
| [`OptimalControl/ODE/ControlSystem.lean`](OptimalControl/ODE/ControlSystem.lean) | control systems with Carathéodory trajectories, Filippov's theorem, existence of optimal controls; the fundamental theorem of calculus for Lipschitz curves |
| [`OptimalControl/ODE/Caratheodory.lean`](OptimalControl/ODE/Caratheodory.lean) | `C¹` control systems (`IsC1On`), existence and uniqueness of Carathéodory solutions, the flow, Gronwall's inequality, the cut-off |
| [`OptimalControl/ODE/LinearCaratheodory.lean`](OptimalControl/ODE/LinearCaratheodory.lean) | the resolvent of a linear equation with measurable coefficients, the adjoint equation |
| [`OptimalControl/ODE/FlowDerivative.lean`](OptimalControl/ODE/FlowDerivative.lean) | the derivative of the flow in the initial point is the resolvent of the variational equation |
| [`OptimalControl/ODE/VariationsFormula.lean`](OptimalControl/ODE/VariationsFormula.lean) | the variations formula along a trajectory |
| [`OptimalControl/ODE/NeedleVariation.lean`](OptimalControl/ODE/NeedleVariation.lean) | needle variations of a control and the derivative of their end point map |
| [`OptimalControl/ODE/TimeChange.lean`](OptimalControl/ODE/TimeChange.lean) | measurable changes of time |
| [`OptimalControl/Convex/Cone/Support.lean`](OptimalControl/Convex/Cone/Support.lean) | supporting hyperplanes and finite generation of convex cones |
| [`OptimalControl/Convex/Cone/Openness.lean`](OptimalControl/Convex/Cone/Openness.lean) | openness at the vertex of a cone (Lemma 12.1 with its Remark (1)), by Brouwer's theorem |
| [`OptimalControl/Pontryagin/Defs.lean`](OptimalControl/Pontryagin/Defs.lean) | admissible pairs, attainable sets, cost, Hamiltonian, needle vectors, the adjoint equation, the maximum condition, strong local minimizers |
| [`OptimalControl/Pontryagin/Geometric.lean`](OptimalControl/Pontryagin/Geometric.lean) | Lemmas 12.1, 12.2 and Theorem 12.1, and the general form `exists_costate_of_boundary` |
| [`OptimalControl/Pontryagin/FreeTime.lean`](OptimalControl/Pontryagin/FreeTime.lean) | Theorem 12.2 (free time) |
| [`OptimalControl/Pontryagin/IntegralCost.lean`](OptimalControl/Pontryagin/IntegralCost.lean) | Theorems 12.3–12.5 (integral cost, fixed time, boundary conditions) |
| [`OptimalControl/Pontryagin/MaximumPrinciple.lean`](OptimalControl/Pontryagin/MaximumPrinciple.lean) | the maximum principle with free time, cost and mixed boundary conditions |
| [`scripts/Audit.lean`](scripts/Audit.lean) | the axiom audit |
| `.github/workflows/` | CI: build, audit, line lengths |

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked the ones that are complete.

## License

Apache-2.0; see [LICENSE](LICENSE).
