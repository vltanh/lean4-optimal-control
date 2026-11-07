module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Lebesgue points of a function of one real variable

`IsLebesguePointWithin u s τ`: `τ` is a Lebesgue point of `u` relative to the set `s` (in
practice an interval `[a, b]`), in the sense of Agrachev–Sachkov (authors' draft, §12.2, p. 170):
`lim_{t → τ, t ∈ s} |t - τ|⁻¹ ∫_τ^t ‖u(θ) - u(τ)‖ dθ = 0`. The integral over the unordered
interval `Ι τ t` is used, which equals `|∫_τ^t ‖u(θ) - u(τ)‖ dθ|`. This file states:

* almost every point of `[a, b]` is a Lebesgue point of an integrable `u`
  (`ae_isLebesguePointWithin`; A–S: "The set of Lebesgue points has the full measure in the
  domain `[0, t₁]`. For details on this subject, see e.g. [146]", [146] = Segal–Kunze,
  *Integrals and operators*);
* near a Lebesgue point `τ` there are points `τ'` of any prescribed set of full measure, outside
  any prescribed finite set, with `u(τ')` close to `u(τ)` (`IsLebesguePointWithin.exists_near`);
  this is the step "we can choose points `τᵢ` distinct" of the proof of A–S's Lemma 12.2
  (p. 171), which rests on the density statement
  `meas{t' ∈ [τ, t] | |u(t') - u(τ)| ≤ ε}/|t - τ| → 1`;
* a Lebesgue point of `u` is a Lebesgue point of `z ↦ G(z, u(·))`, uniformly for `z` in a
  compact set, when `G` is continuous on `K × U` (`IsLebesguePointWithin.eventually_integral_le`);
  this is what the derivative of the needle variations at `s = 0` uses (A–S, p. 172).

## Proof sketch

The first statement is the Lebesgue differentiation theorem (Mathlib's
`MeasureTheory.Integrable.ae_tendsto_average_norm_sub` / `VitaliFamily.ae_tendsto_average_norm_sub`
for the doubling measure `volume` on `ℝ`, applied to `u` restricted to `[a, b]`), since
`|t - τ|⁻¹ ∫_{Ι τ t} ≤ 2 ⨍_{B(τ, |t - τ|)}`. The second: by Chebyshev the set of `t'` near `τ`
with `‖u(t') - u(τ)‖ ≥ ε` has small relative measure, so the set of good `t'` has positive
measure in every small interval around `τ` within `[a, b]`, and a set of positive measure is
infinite and meets every set of full measure. The third: `G` is uniformly continuous on the
compact `K × U`, so `‖G(z, v) - G(z, u(τ))‖ ≤ η/2 + (2C/δ)‖v - u(τ)‖`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped Interval

variable {V : Type*} [NormedAddCommGroup V]

/-- `τ` is a Lebesgue point of `u` relative to `s` (Agrachev–Sachkov, authors' draft, p. 170):
`|t - τ|⁻¹ ∫_{Ι τ t} ‖u(θ) - u(τ)‖ dθ → 0` as `t → τ` within `s \ {τ}`. -/
def IsLebesguePointWithin (u : ℝ → V) (s : Set ℝ) (τ : ℝ) : Prop :=
  Tendsto (fun t ↦ |t - τ|⁻¹ * ∫ θ in Ι τ t, ‖u θ - u τ‖) (𝓝[s \ {τ}] τ) (𝓝 0)

variable [NormedSpace ℝ V] {u : ℝ → V} {a b : ℝ}

/-- **Lebesgue's differentiation theorem**: almost every point of `[a, b]` is a Lebesgue point
of a function integrable on `[a, b]` (Agrachev–Sachkov, p. 171, citing Segal–Kunze). -/
theorem ae_isLebesguePointWithin (hu : IntegrableOn u (Icc a b)) :
    ∀ᵐ τ ∂(volume.restrict (Icc a b)), IsLebesguePointWithin u (Icc a b) τ := by
  sorry

/-- Near a Lebesgue point `τ ∈ [a, b]` of `u` (integrable on `[a, b]`, `a < b`) there are points
`τ'` of the open interval `(a, b)` in any prescribed set `G` of full measure in `[a, b]`, outside
any prescribed finite set `S`, with `|τ' - τ| < ε` and `‖u(τ') - u(τ)‖ < ε` (Agrachev–Sachkov,
proof of Lemma 12.2, p. 171). -/
theorem IsLebesguePointWithin.exists_near (hu : IntegrableOn u (Icc a b)) (hab : a < b)
    {τ : ℝ} (hτ : τ ∈ Icc a b) (hleb : IsLebesguePointWithin u (Icc a b) τ) {G : Set ℝ}
    (hG : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∈ G) (S : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ' ∈ G, τ' ∈ Ioo a b ∧ τ' ∉ S ∧ |τ' - τ| < ε ∧ ‖u τ' - u τ‖ < ε := by
  sorry

/-- A Lebesgue point of `u` is a Lebesgue point of `θ ↦ G(z, u(θ))`, uniformly in `z ∈ K`, when
`G` is continuous on `K × U` with `K` and `U` compact and `u` takes its values in `U` on
`[a, b]`. -/
theorem IsLebesguePointWithin.eventually_integral_le {E F : Type*} [TopologicalSpace E]
    [NormedAddCommGroup F] {G : E → V → F} {K : Set E} {U : Set V} (hK : IsCompact K)
    (hU : IsCompact U) (hG : ContinuousOn (fun p : E × V ↦ G p.1 p.2) (K ×ˢ U))
    (hu : AEStronglyMeasurable u (volume.restrict (Icc a b))) (huU : ∀ t ∈ Icc a b, u t ∈ U)
    {τ : ℝ} (hτ : τ ∈ Icc a b) (hleb : IsLebesguePointWithin u (Icc a b) τ) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ t in 𝓝[Icc a b \ {τ}] τ, ∀ z ∈ K,
      |t - τ|⁻¹ * ∫ θ in Ι τ t, ‖G z (u θ) - G z (u τ)‖ ≤ η := by
  sorry
