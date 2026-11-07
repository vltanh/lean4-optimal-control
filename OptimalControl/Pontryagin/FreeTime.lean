module

public import OptimalControl.Pontryagin.Geometric
public import OptimalControl.ODE.TimeChange

/-!
# The geometric maximum principle for free time (Agrachev–Sachkov, §12.3)

**Theorem 12.2** of A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the Geometric
Viewpoint* (authors' draft, p. 173): if `q̃(t₁) ∈ ∂(⋃_{|t - t₁| < ε} A_{q₀}(t))` for some
`ε ∈ (0, t₁)`, the conclusions of Theorem 12.1 hold together with
`h_{ũ(t)}(λ_t) = 0` (12.15) for almost all `t`. Read on an open subset `Ω` of `E` (D1).

## Proof (A–S, pp. 173–174)

Time substitution: the extended system `q' = v f_u(q)`, `(v, u) ∈ [1 - δ', 1 + δ'] × U` with
`0 < δ' < ε/t₁` (A–S take `|v - 1| < δ = ε/t₁`; a compact interval gives the same conclusion,
D4). Its admissible trajectories are reparametrized trajectories of the original system
(`ControlSystem.IsAdmissible.timeChange`; A–S derive this for a smooth time change and use it for
measurable `v`, D7), so its attainable set at time `t₁` lies in `⋃_{|t - t₁| < ε} A_{q₀}(t)` and
the reference `(1, ũ)` reaches its boundary. Theorem 12.1 (`theorem12_1`) for the extended
system gives `λ_t` with `1 · h_{ũ(t)}(λ_t) = max_{u, v} v h_u(λ_t)`; taking `u = ũ(t)` gives
`h_{ũ(t)}(λ_t) = 0`, and `v = 1` gives the maximality condition; the Hamiltonian systems of `(1, ũ)`
and of `ũ` coincide.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace Pontryagin

open ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {Ω : Set E} {U : Set V} {f : E → V → E} {t₁ : ℝ} {ũ : ℝ → V} {q : ℝ → E}

/-- **Agrachev–Sachkov, Theorem 12.2** (authors' draft, p. 173): let `ũ(·)` be an admissible
control for the control system (12.1) such that `q̃(t₁) ∈ ∂(⋃_{|t - t₁| < ε} A_{q₀}(t))` for some
`t₁ > 0` and `ε ∈ (0, t₁)`. Then there exists a Lipschitzian curve `λ_t ∈ T*_{q̃(t)}M`,
`λ_t ≠ 0`, `0 ≤ t ≤ t₁`, such that `λ̇_t = h⃗_{ũ(t)}(λ_t)`,
`h_{ũ(t)}(λ_t) = max_{u ∈ U} h_u(λ_t)` and `h_{ũ(t)}(λ_t) = 0` (12.15) for almost all
`t ∈ [0, t₁]`. (In coordinates on `Ω`, as in `theorem12_1`.) -/
theorem theorem12_2 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) {ε : ℝ} (hε : ε ∈ Ioo 0 t₁)
    (hbd : q t₁ ∈ frontier (⋃ t ∈ Ioo (t₁ - ε) (t₁ + ε), attainableSet f Ω U (q 0) t)) :
    ∃ p : ℝ → StrongDual ℝ E, (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, p t ≠ 0) ∧ IsAdjoint f 0 0 ũ q t₁ p ∧ IsMaximal f 0 0 U ũ q t₁ p ∧
      ∀ᵐ t ∂(volume.restrict (Icc 0 t₁)), controlHamiltonian f 0 0 (q t) (p t) (ũ t) = 0 := by
  sorry

end Pontryagin
