module

public import OptimalControl.ODE.ControlSystem
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Carathéodory solutions of control systems: well-posedness and flows

For a control system `y' = f(y, u(t))` on a finite-dimensional real normed space `E`, with
controls in a finite-dimensional real normed space `V`, a compact control set `U ⊆ V` and a
control `u` that is (a.e. strongly) measurable with values in `U`, this file states:

* the *standing hypotheses* (`ControlSystem.IsLipschitzSystem`): `f` jointly continuous on
  `E × U` and `L`-Lipschitz in the state for every control value in `U`;
* the regularity of Agrachev–Sachkov's control systems (`ControlSystem.IsC1On`), conditions
  (10.2)–(10.4) of their §10.1 with `C¹` in place of `C^∞`, on an open set `Ω`, and its global
  bounded form (`ControlSystem.IsBoundedC1System`);
* existence and uniqueness of Carathéodory solutions (`ControlSystem.IsSolution`) through every
  point, forward and backward in time (`ControlSystem.exists_isSolution`,
  `ControlSystem.IsSolution.eqOn`), the integral Gronwall inequality, and the *flow*
  `ControlSystem.flow f u s t x` (the value at time `t` of the solution with value `x` at time
  `s`): its cocycle property, its Lipschitz dependence on the initial point (`e^{L|t - s|}`) and
  on the time (`M`), its continuity, and the estimate comparing the trajectories of two controls;
* the *cut-off* (`ControlSystem.IsC1On.exists_cutoff`): a `C¹` system on an open set `Ω`
  agrees, near a compact subset of `Ω`, with a globally bounded system whose state derivative is
  globally bounded.

## Source and reading

Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint* (authors' draft, §2.4.1 and
§10.1, p. 133), take these facts from "the classical Carathéodory Theorem (see e.g. [8])",
[8] = R. V. Gamkrelidze, *Principles of optimal control theory*, Plenum 1978, and assume
complete vector fields (for instance with compact support). Departure D11 (the departures from
Agrachev–Sachkov are listed in the README): the cited texts were not consulted; the facts are
proved by the standard Picard iteration and Gronwall argument, and the cut-off to a compact tube
replaces A–S's completeness assumption. The flow is defined by choice from the solution on the
interval between the two times, so that it depends only on the control there.

## Proof sketch

Picard iteration `y ↦ x + ∫ₛ f(y, u)` is a contraction on `C([a, b], E)` for the weighted norm
`sup e^{-2L|t - s|}‖y(t)‖`; uniqueness and the Lipschitz estimates follow from the integral
Gronwall inequality (`ControlSystem.le_mul_exp_of_le_add_integral`, from Mathlib's
`le_gronwallBound_of_liminf_deriv_right_le` applied to `C + L ∫ φ`). The cocycle property is
uniqueness on the subinterval. The cut-off multiplies `f` by a smooth bump function equal to `1`
on `cthickening δ K` and supported in `thickening (2δ) K ⊆ Ω`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace ControlSystem

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### Regularity of control systems -/

/-- The regularity of Agrachev–Sachkov's control systems on an open set `Ω`, conditions
(10.2)–(10.4) of their §10.1 (authors' draft, p. 133) with `C¹` in place of `C^∞` (departure D3):
`(x, u) ↦ f x u` is continuous on `Ω × U`, `x ↦ f x u` is differentiable on `Ω` for `u ∈ U`, and
`(x, u) ↦ ∂ₓf(x, u)` is continuous on `Ω × U`. The same conditions are imposed on the integrand
`φ` of a cost (`F = ℝ`). -/
structure IsC1On (f : E → V → F) (Ω : Set E) (U : Set V) : Prop where
  continuousOn : ContinuousOn (fun p : E × V ↦ f p.1 p.2) (Ω ×ˢ U)
  differentiableAt : ∀ x ∈ Ω, ∀ u ∈ U, DifferentiableAt ℝ (f · u) x
  continuousOn_fderiv : ContinuousOn (fun p : E × V ↦ fderiv ℝ (f · p.2) p.1) (Ω ×ˢ U)

/-- A globally bounded `C¹` control system: `U` is compact, `f` is `C¹` on all of `E`
(`IsC1On f univ U`), `‖f x u‖ ≤ M` and `‖∂ₓf(x, u)‖ ≤ L` for all `x` and `u ∈ U`. This is what
the cut-off (`IsC1On.exists_cutoff`) produces near a trajectory. -/
structure IsBoundedC1System (f : E → V → F) (U : Set V) (M L : ℝ≥0) : Prop where
  isCompact : IsCompact U
  isC1On : IsC1On f univ U
  norm_le : ∀ x, ∀ u ∈ U, ‖f x u‖ ≤ M
  norm_fderiv_le : ∀ x, ∀ u ∈ U, ‖fderiv ℝ (f · u) x‖ ≤ L

/-- The standing hypotheses for well-posedness: `U` is compact, `f` is jointly continuous on
`E × U`, and `f(·, u)` is `L`-Lipschitz for every `u ∈ U`. (`f` then has linear growth on
`E × U`; the linear systems `Y' = A(t) Y` of
`OptimalControl/ODE/LinearCaratheodory.lean` are of this kind.) -/
structure IsLipschitzSystem (f : E → V → E) (U : Set V) (L : ℝ≥0) : Prop where
  isCompact : IsCompact U
  continuousOn : ContinuousOn (fun p : E × V ↦ f p.1 p.2) (univ ×ˢ U)
  lipschitzWith : ∀ u ∈ U, LipschitzWith L (f · u)

/-- A control on `[a, b]`: a.e. strongly measurable on `[a, b]`, with values in `U` there. -/
structure IsControlOn (u : ℝ → V) (U : Set V) (a b : ℝ) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable u (volume.restrict (Icc a b))
  mem : ∀ t ∈ Icc a b, u t ∈ U

/-- A bounded `C¹` system satisfies the standing hypotheses, with the bound `L` on `∂ₓf` as
Lipschitz constant (mean value inequality). -/
theorem IsBoundedC1System.isLipschitzSystem {f : E → V → E} {U : Set V} {M L : ℝ≥0}
    (hf : IsBoundedC1System f U M L) : IsLipschitzSystem f U L := by
  sorry

/-- **Cut-off.** A `C¹` system on an open set `Ω` (`IsC1On`) with compact `U` agrees, on a
closed `δ`-neighbourhood of a compact `K ⊆ Ω`, with a globally bounded `C¹` system. This replaces
Agrachev–Sachkov's assumption of complete vector fields (§2.4.1; departure D11).

Proof: `g x u = χ(x) f(x, u)` with a smooth bump `χ` equal to `1` on `cthickening δ K` and
supported in `thickening (2δ) K`, where `cthickening (2δ) K ⊆ Ω`; the bounds come from the
compactness of `cthickening (2δ) K × U`. -/
theorem IsC1On.exists_cutoff {f : E → V → F} {Ω : Set E} {U : Set V} (hf : IsC1On f Ω U)
    (hΩ : IsOpen Ω) (hU : IsCompact U) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ δ > 0, cthickening δ K ⊆ Ω ∧ ∃ (g : E → V → F) (M L : ℝ≥0), IsBoundedC1System g U M L ∧
      ∀ x ∈ cthickening δ K, ∀ u ∈ U, g x u = f x u := by
  sorry

/-! ### Gronwall's inequality in integral form -/

/-- **Gronwall's inequality** in integral form: if `φ ≥ 0` is continuous on `[a, b]` and
`φ(t) ≤ C + L ∫ₐᵗ φ` there, with `L ≥ 0`, then `φ(t) ≤ C e^{L (t - a)}`. -/
theorem le_mul_exp_of_le_add_integral {φ : ℝ → ℝ} {a b C L : ℝ} (hL : 0 ≤ L)
    (hφ : ContinuousOn φ (Icc a b)) (hφ0 : ∀ t ∈ Icc a b, 0 ≤ φ t)
    (h : ∀ t ∈ Icc a b, φ t ≤ C + L * ∫ r in a..t, φ r) :
    ∀ t ∈ Icc a b, φ t ≤ C * Real.exp (L * (t - a)) := by
  sorry

/-! ### Solutions and flows -/

/-- `y` is a Carathéodory solution of `y' = f(y, u(t))` on the interval `[[a, b]]` with value
`x` at time `s`: `y` is continuous on `[[a, b]]`, `t ↦ f(y(t), u(t))` is integrable there, and
`y(t) = x + ∫ₛᵗ f(y(r), u(r)) dr` for `t ∈ [[a, b]]` (meaningful for `s ∈ [[a, b]]`). -/
def IsSolution (f : E → V → E) (u : ℝ → V) (s : ℝ) (x : E) (a b : ℝ) (y : ℝ → E) : Prop :=
  ContinuousOn y [[a, b]] ∧ IntervalIntegrable (fun r ↦ f (y r) (u r)) volume a b ∧
    ∀ t ∈ [[a, b]], y t = x + ∫ r in s..t, f (y r) (u r)

open Classical in
/-- The flow `P_{s → t}(x)` of `y' = f(y, u(t))`: the value at time `t` of the solution with value
`x` at time `s`, chosen among the solutions on `[[s, t]]` (unique under the standing hypotheses,
`IsSolution.eqOn`); `x` if there is none. Agrachev–Sachkov write it with the chronological
exponential, `P_{s,t} = exp→ ∫ₛᵗ f_{u(r)} dr` (authors' draft, §2.4). -/
noncomputable def flow (f : E → V → E) (u : ℝ → V) (s t : ℝ) (x : E) : E :=
  if h : ∃ y, IsSolution f u s x s t y then h.choose t else x

variable {f : E → V → E} {U : Set V} {L : ℝ≥0} {u w : ℝ → V} {a b : ℝ}

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The flow at the initial time is the identity. -/
theorem flow_self (f : E → V → E) (u : ℝ → V) (s : ℝ) (x : E) : flow f u s s x = x := by
  unfold flow
  split_ifs with h
  · simpa using h.choose_spec.2.2 s (by simp)
  · rfl

/-- **Carathéodory's theorem**, existence: under the standing hypotheses, for a control on
`[a, b]` and `s ∈ [a, b]`, there is a solution on `[a, b]` through `(s, x)`. -/
theorem exists_isSolution (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) {s : ℝ}
    (hs : s ∈ Icc a b) (x : E) : ∃ y, IsSolution f u s x a b y := by
  sorry

/-- **Carathéodory's theorem**, uniqueness: two solutions on `[a, b]` through the same point
`(s, x)` agree on `[a, b]` (Gronwall). -/
theorem IsSolution.eqOn (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) {s : ℝ}
    (hs : s ∈ Icc a b) {x : E} {y y' : ℝ → E} (hy : IsSolution f u s x a b y)
    (hy' : IsSolution f u s x a b y') : EqOn y y' (Icc a b) := by
  sorry

/-- A solution on `[a, b]` through `(s, x)` is the flow from `(s, x)`. -/
theorem IsSolution.flow_eq (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) {s : ℝ}
    (hs : s ∈ Icc a b) {x : E} {y : ℝ → E} (hy : IsSolution f u s x a b y) {t : ℝ}
    (ht : t ∈ Icc a b) : flow f u s t x = y t := by
  sorry

/-- The flow from `(s, x)` is a solution on `[a, b]`. -/
theorem isSolution_flow (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) {s : ℝ}
    (hs : s ∈ Icc a b) (x : E) : IsSolution f u s x a b (fun t ↦ flow f u s t x) := by
  sorry

/-- The cocycle property `P_{t → r} ∘ P_{s → t} = P_{s → r}`. -/
theorem flow_flow (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) {s t r : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hr : r ∈ Icc a b) (x : E) :
    flow f u t r (flow f u s t x) = flow f u s r x := by
  sorry

/-- Lipschitz dependence on the initial point: `‖P_{s → t}(x) - P_{s → t}(x')‖ ≤
e^{L|t - s|} ‖x - x'‖` (Gronwall). -/
theorem norm_flow_sub_flow_le (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x x' : E) :
    ‖flow f u s t x - flow f u s t x'‖ ≤ Real.exp (L * |t - s|) * ‖x - x'‖ := by
  sorry

/-- Lipschitz dependence on the time, for a bounded system: `‖P_{s → t}(x) - P_{s → t'}(x)‖ ≤
M |t - t'|`. -/
theorem norm_flow_sub_flow_time_le (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b)
    {M : ℝ} (hM : ∀ y, ∀ v ∈ U, ‖f y v‖ ≤ M) {s t t' : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (ht' : t' ∈ Icc a b) (x : E) :
    ‖flow f u s t x - flow f u s t' x‖ ≤ M * |t - t'| := by
  sorry

/-- The flow is jointly continuous in the initial time, the final time and the initial point. -/
theorem continuousOn_flow (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) :
    ContinuousOn (fun p : ℝ × ℝ × E ↦ flow f u p.1 p.2.1 p.2.2) (Icc a b ×ˢ Icc a b ×ˢ univ) := by
  sorry

/-- Comparison of the trajectories of two controls (Gronwall): with `y = P^w_{s → ·}(x')`,
`‖P^u_{s → t}(x) - P^w_{s → t}(x')‖ ≤
e^{L|t - s|} (‖x - x'‖ + |∫ₛᵗ ‖f(y(r), u(r)) - f(y(r), w(r))‖ dr|)`. For needle variations the
integral is at most `2M` times the measure of `{u ≠ w}`. -/
theorem norm_flow_sub_flow_control_le (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b)
    (hw : IsControlOn w U a b) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x x' : E) :
    ‖flow f u s t x - flow f w s t x'‖ ≤ Real.exp (L * |t - s|) *
      (‖x - x'‖ + |∫ r in s..t, ‖f (flow f w s r x') (u r) - f (flow f w s r x') (w r)‖|) := by
  sorry

/-! ### Flows and admissible pairs -/

variable [MeasurableSpace V] [BorelSpace V]

/-- The trajectory of an admissible pair (`ControlSystem.IsAdmissible`, from `x₀` at time `0`)
is the flow from `(0, x₀)`. -/
theorem IsAdmissible.eq_flow (hf : IsLipschitzSystem f U L) {x₀ : E} {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → E} (h : IsAdmissible f U x₀ T u x) : ∀ t ∈ Icc 0 T, x t = flow f u 0 t x₀ := by
  sorry

/-- A measurable control with values in `U` on `[0, T]` and the flow from `(0, x₀)` form an
admissible pair. -/
theorem isAdmissible_flow (hf : IsLipschitzSystem f U L) {T : ℝ} (hT : 0 ≤ T)
    (hum : Measurable u) (hU : ∀ t ∈ Icc 0 T, u t ∈ U) (x₀ : E) :
    IsAdmissible f U x₀ T u (fun t ↦ flow f u 0 t x₀) := by
  sorry

end ControlSystem
