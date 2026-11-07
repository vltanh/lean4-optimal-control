module

public import OptimalControl.ODE.LinearCaratheodory

/-!
# Differentiability of the flow with respect to the initial point

For a globally bounded `C¹` control system (`ControlSystem.IsBoundedC1System`) driven by a
control `u` on `[a, b]`, the flow `x ↦ P_{s → t}(x)` is differentiable, and its derivative is
the resolvent of the variational equation along the trajectory:
`D_x P_{s → t}(x) = R(s, t)` for `A(r) = ∂ₓf(P_{s → r}(x), u(r))`
(`ControlSystem.hasFDerivAt_flow`). The derivative is jointly continuous in `(s, t, x)`, and
along a trajectory the derivative from an intermediate time is the resolvent between the two
times (`ControlSystem.fderiv_flow_eq_stateTransition`).

## Source and reading

Agrachev–Sachkov (authors' draft), §2.8, formula (2.19) for the derivative of a flow (used in
the proof of Theorem 12.4 (2), p. 182: `∂F/∂q v = Φ_* P^{t₁}_* v`), and the claim of §2.4.1
that the Carathéodory solution is smooth in the initial point, cited to Gamkrelidze [8].
Read pointwise in coordinates (departure D2) and with `C¹` data (D3);
proved by the standard argument (D11).

## Proof sketch

Gronwall: `P_{s → t}(x + h) - P_{s → t}(x) - R(s, t) h` solves a linear integral equation whose
inhomogeneity is `o(‖h‖)` uniformly in `t`, because `∂ₓf` is uniformly continuous on compact
subsets of `E × U` (the trajectories from `x + h` stay in a compact tube) and `P_{s → ·}(x + h)`
is `e^{L|t - s|}‖h‖`-close to `P_{s → ·}(x)`. Joint continuity of the derivative from the
continuity of the resolvent in the coefficient `A` (Gronwall again).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {f : E → V → E} {U : Set V} {M L : ℝ≥0} {u : ℝ → V} {a b : ℝ}

/-- **Derivative of the flow** (Agrachev–Sachkov (2.19), read pointwise):
`D_x P_{s → t}(x) = R(s, t)`, the resolvent of the variational equation
`ξ' = ∂ₓf(P_{s → r}(x), u(r)) ξ`. -/
theorem hasFDerivAt_flow (hf : IsBoundedC1System f U M L) (hu : IsControlOn u U a b) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    HasFDerivAt (flow f u s t)
      (stateTransition (fun r ↦ fderiv ℝ (f · (u r)) (flow f u s r x)) s t) x := by
  sorry

/-- The flow is `C¹` in the initial point. -/
theorem contDiff_flow (hf : IsBoundedC1System f U M L) (hu : IsControlOn u U a b) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : ContDiff ℝ 1 (flow f u s t) := by
  sorry

/-- The derivative of the flow is jointly continuous in the initial time, the final time and the
initial point. -/
theorem continuousOn_fderiv_flow (hf : IsBoundedC1System f U M L) (hu : IsControlOn u U a b) :
    ContinuousOn (fun p : ℝ × ℝ × E ↦ fderiv ℝ (flow f u p.1 p.2.1) p.2.2)
      (Icc a b ×ˢ Icc a b ×ˢ univ) := by
  sorry

/-- Along the trajectory `r ↦ P_{s → r}(x₀)`, the derivative of the flow from the intermediate
time `t` to `c` is the resolvent `R(t, c)` of the variational equation along that trajectory
(from `hasFDerivAt_flow` and the cocycle property). -/
theorem fderiv_flow_eq_stateTransition (hf : IsBoundedC1System f U M L) (hu : IsControlOn u U a b)
    {s c : ℝ} (hs : s ∈ Icc a b) (hc : c ∈ Icc a b) (x₀ : E) {t : ℝ} (ht : t ∈ Icc a b) :
    fderiv ℝ (flow f u t c) (flow f u s t x₀) =
      stateTransition (fun r ↦ fderiv ℝ (f · (u r)) (flow f u s r x₀)) t c := by
  sorry

end ControlSystem
