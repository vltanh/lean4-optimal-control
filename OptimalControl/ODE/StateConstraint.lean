module

public import OptimalControl.ODE.ControlSystem

-- Imported directly by the library root `OptimalControl.lean`, so Mathlib's header linter would ask
-- for a copyright header, which the library's modules do not carry.
set_option linter.style.header false

/-!
# Filippov's theorem with a state constraint, a set of initial points and an endpoint relation

Filippov's theorem (`ControlSystem.isCompact_reachableSet`,
`ControlSystem.isCompact_reachableSetLE`) and the existence of optimal controls
(`ControlSystem.exists_optimal_fixedTime`, `ControlSystem.exists_optimal_freeTime`) in
`OptimalControl.ODE.ControlSystem` fix the initial point, ask the velocities to be bounded on
the whole space and the dynamics to be continuous everywhere. Many problems are posed only on part
of the space, with initial and terminal points tied by a relation. This module states the same
results for

* a *closed state constraint* `S`: the trajectories stay in `S` on `[0, τ]`, and the dynamics `F`
  and the running cost `φ` need only be continuous on `S × U`, the velocities bounded on `S × U`,
  and the velocity sets convex at the points of `S`;
* a *compact set* `K₀` of initial points;
* a *closed endpoint relation* `N ⊆ E × E`: `(x(0), x(τ)) ∈ N`;
* a *time window* `[T₀, T₁]`, `0 ≤ T₀ ≤ T₁`, for the terminal time `τ`: fixed time when
  `T₀ = T₁`, free time otherwise.

The admissible pairs are those of `ControlSystem.IsAdmissible`, from their own initial point
`x(0)`.

## Main results

* `ControlSystem.isCompact_constrainedEndpoints` (Filippov's theorem): if the velocity sets
  `F(x, U)`, `x ∈ S`, are convex, the set of pairs `(x(0), x(τ))` of the trajectories in `S` from
  `K₀` with `τ ∈ [T₀, T₁]` is compact;
* `ControlSystem.exists_optimal_constrained` (existence of optimal controls): if moreover the
  velocity sets extended by the cost, `{(F(x, u), φ(x, u)) | u ∈ U}`, are convex at the points of
  `S`, and some trajectory in `S` from `K₀` satisfies the endpoint relation with a time in
  `[T₀, T₁]`, then among all such trajectories one has the least cost `∫₀^τ φ(x, u)`.

## Proof (to be written)

The proof is the one of `OptimalControl.ODE.ControlSystem`, with three additions.

1. *Bounds.* A trajectory in `S` from `x(0) ∈ K₀` with `τ ≤ T₁` stays in the compact set
   `S ∩ cthickening (M T₁) K₀`, on which `F` and `φ` are bounded (`F` by `M`, `φ` by continuity on
   a compact subset of `S × U`).
2. *Limits.* Along a sequence of admissible pairs, pass to a subsequence along which the initial
   points (in the compact `K₀`), the times (in `[T₀, T₁]`) and the costs converge; the frozen
   trajectories (`ControlSystem.freeze`) are equi-Lipschitz with values in a compact set, and have
   a pointwise cluster point `y` along a filter finer than `atTop`
   (`IsCompact.exists_neBot_le_atTop_tendsto`, applied in a product of compact sets as in
   `ControlSystem.exists_mem_reachableSet_of_tendsto`). The limit `y` takes its values in `S`
   (`S` closed), `y(0) ∈ K₀` (`K₀` closed), and `(y(0), y(τ₀)) ∈ N` (`N` closed, and the frozen
   trajectories converge at the times `τₖ → τ₀` by equicontinuity).
3. *Closure.* `y` is an admissible trajectory: the argument of
   `ControlSystem.hasDerivAt_mem_image_of_tendsto` and
   `ControlSystem.exists_isAdmissible_of_tendsto` uses `F` only near the points `(y(t), u)`,
   `u ∈ U`, which lie in `S × U` and are approached by points of `S × U`; so continuity of `F` on
   `S × U` (uniform on the compact `{y(t)} × U` within `S × U`) and convexity of `F(y(t), U)`
   suffice. For the cost, the same argument applies to the extended system
   `ControlSystem.extend F φ`, with the cost coordinate starting at `0`
   (`ControlSystem.IsAdmissible.extend`, `ControlSystem.IsAdmissible.of_extend`), as in
   `ControlSystem.exists_optimal_freeTime`; along a minimizing sequence the limit pair has cost
   equal to the infimum.

These steps need the closure results of `OptimalControl.ODE.ControlSystem` in a form where `F` is
continuous on `S × U` only and the trajectories are confined to `S`; the existing statements assume
`F` continuous on `E × V`. A proof may either generalize them (the same proofs, with `ContinuousOn`
and the constraint carried along) or reduce to them by a continuous extension of `F|S×U` to
`E × V` (Tietze, coordinatewise) that keeps the velocity sets convex, which needs care: the
extension must keep `F(x, U)` convex at points outside `S` too, or the closure argument must only
use convexity at the points of the limit trajectory, which lie in `S` (the existing proof uses it
only there).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace V]

/-- The endpoint pairs of the constrained problem: the pairs `(x(0), x(τ))` of the admissible pairs
`(u, x)` on `[0, τ]` with `τ ∈ [T₀, T₁]`, initial point `x(0) ∈ K₀` and trajectory in `S` on
`[0, τ]`. -/
def constrainedEndpoints (F : E → V → E) (U : Set V) (S K₀ : Set E) (T₀ T₁ : ℝ) : Set (E × E) :=
  {p | ∃ τ ∈ Icc T₀ T₁, ∃ u x, IsAdmissible F U (x 0) τ u x ∧ x 0 ∈ K₀ ∧
    (∀ t ∈ Icc 0 τ, x t ∈ S) ∧ (x 0, x τ) = p}

variable [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace V] [BorelSpace V] [SecondCountableTopology V]
  {F : E → V → E} {φ : E → V → ℝ} {U : Set V} {S K₀ : Set E} {N : Set (E × E)} {T₀ T₁ M : ℝ}

/-- **Filippov's theorem with a state constraint and a compact set of initial points.** For a
control system `x' = F(x, u)`, `u ∈ U` compact, with `F` continuous on `S × U` for a closed set `S`,
velocities bounded by `M` on `S × U` and convex velocity sets `F(x, U)` at the points `x ∈ S`, the
set of endpoint pairs `(x(0), x(τ))` of the trajectories in `S` from points of a compact set `K₀`,
with terminal times `τ ∈ [T₀, T₁]`, `0 ≤ T₀`, is compact. -/
theorem isCompact_constrainedEndpoints (hU : IsCompact U) (hS : IsClosed S) (hK₀ : IsCompact K₀)
    (hF : ContinuousOn (fun p : E × V ↦ F p.1 p.2) (S ×ˢ U))
    (hconv : ∀ x ∈ S, Convex ℝ (F x '' U)) (hFM : ∀ x ∈ S, ∀ w ∈ U, ‖F x w‖ ≤ M)
    (hT₀ : 0 ≤ T₀) :
    IsCompact (constrainedEndpoints F U S K₀ T₀ T₁) := by
  sorry

/-- **Existence of optimal controls with a state constraint, a compact set of initial points and
a closed endpoint relation**, for fixed (`T₀ = T₁`) or free terminal time in `[T₀, T₁]`. Let
`x' = F(x, u)`, `u ∈ U` compact, be a control system and `φ` a running cost, both continuous on
`S × U` for a closed set `S`, with velocities bounded by `M` on `S × U`, and with convex extended
velocity sets `{(F(x, u), φ(x, u)) | u ∈ U}` at the points `x ∈ S`. Let `K₀` be compact and
`N ⊆ E × E` closed. If some admissible pair `(u, x)` on `[0, τ]`, `τ ∈ [T₀, T₁]`, has `x(0) ∈ K₀`,
`x(t) ∈ S` on `[0, τ]` and `(x(0), x(τ)) ∈ N`, then one such pair has the least cost
`∫₀^τ φ(x, u)` among all of them. -/
theorem exists_optimal_constrained (hU : IsCompact U) (hS : IsClosed S) (hK₀ : IsCompact K₀)
    (hN : IsClosed N) (hF : ContinuousOn (fun p : E × V ↦ F p.1 p.2) (S ×ˢ U))
    (hφ : ContinuousOn (fun p : E × V ↦ φ p.1 p.2) (S ×ˢ U))
    (hconv : ∀ x ∈ S, Convex ℝ ((fun w ↦ (F x w, φ x w)) '' U))
    (hFM : ∀ x ∈ S, ∀ w ∈ U, ‖F x w‖ ≤ M) (hT₀ : 0 ≤ T₀)
    (hne : ∃ τ ∈ Icc T₀ T₁, ∃ u x, IsAdmissible F U (x 0) τ u x ∧ x 0 ∈ K₀ ∧
      (∀ t ∈ Icc 0 τ, x t ∈ S) ∧ (x 0, x τ) ∈ N) :
    ∃ τ ∈ Icc T₀ T₁, ∃ u x, IsAdmissible F U (x 0) τ u x ∧ x 0 ∈ K₀ ∧
      (∀ t ∈ Icc 0 τ, x t ∈ S) ∧ (x 0, x τ) ∈ N ∧
      ∀ τ' ∈ Icc T₀ T₁, ∀ u' x', IsAdmissible F U (x' 0) τ' u' x' → x' 0 ∈ K₀ →
        (∀ t ∈ Icc 0 τ', x' t ∈ S) → (x' 0, x' τ') ∈ N →
        ∫ t in (0 : ℝ)..τ, φ (x t) (u t) ≤ ∫ t in (0 : ℝ)..τ', φ (x' t) (u' t) := by
  sorry

end ControlSystem
