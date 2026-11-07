module

public import OptimalControl.ODE.VariationsFormula

/-!
# Needle variations

Agrachev–Sachkov's needle-like variations (authors' draft, (12.14), p. 171): for distinct times
`τ₁, …, τ_k ∈ [0, t₁)`, control values `w₁, …, w_k ∈ U` and `σ ∈ ℝᵏ₊`, the control
`u_σ = wᵢ` on `[τᵢ, τᵢ + σᵢ)` and `u_σ = ũ` elsewhere (`ControlSystem.needleControl`). Together
with a variation `ψ(a)` of the initial point (the proof of A–S's Theorem 12.4 (2), p. 181), the
end-point map `F(a, σ) = P^{u_σ}_{0 → t₁}(ψ(a))` is studied near `(a₀, 0)` on the convex cone
`L × ℝᵏ₊`. This file states the claims that A–S make about `F` in the proofs of Lemma 12.2
(p. 172: "The mapping `F` … is Lipschitzian, differentiable at `s = 0`, and
`∂F/∂sᵢ|_{s=0} = g_{τᵢ,uᵢ}(q₁)`") and Theorem 12.4 (2) (p. 182, `∂F/∂q v = Φ_* P^{t₁}_* v`):

* `u_σ` is a control on `[0, t₁]` (`ControlSystem.isControlOn_needleControl`);
* `F` is Lipschitz near `(a₀, 0)` on the cone (`ControlSystem.lipschitzOnWith_needle`);
* `F` is differentiable at `(a₀, 0)` within the cone, with derivative
  `(α, σ) ↦ D_x P_{0 → t₁}(ψ(a₀)) Dψ(a₀) α + Σᵢ σᵢ g_{τᵢ,wᵢ}(q₁)`, `q₁ = P_{0 → t₁}(ψ(a₀))`
  (`ControlSystem.hasFDerivWithinAt_needle`);
* the varied trajectories are uniformly close to the reference trajectory
  (`ControlSystem.norm_needle_trajectory_sub_lt`), so that they stay where the system is defined
  and in the neighbourhoods of strong local optimality.

The intervals are half-open, `[τᵢ, τᵢ + σᵢ)`, so that `u_0 = ũ` exactly (A–S write `[τᵢ, τᵢ + sᵢ]`;
the difference is a null set). The needle times must be Lebesgue points of `ũ`.

## Source and reading

Agrachev–Sachkov, §12.2, (12.14) and the proof of Lemma 12.2 (pp. 171–172), and the proof of
Theorem 12.4 (2) (pp. 181–182), read pointwise in coordinates (departure D2), for a globally
bounded `C¹` system (after the cut-off, D11).

## Proof sketch (A–S's route)

By the variations formula (`ControlSystem.flow_flow_eq_add_integral_variationField`) with
`g_{t,ũ(t)} = 0`, `F(a, σ) = P_{0 → t₁}(ψ(a)) + Σᵢ ∫_{τᵢ}^{τᵢ+σᵢ} g_{t,wᵢ}(y(t)) dt`, with `y` the
transported trajectory, `‖y(t) - q₁‖ = O(‖a - a₀‖ + Σσᵢ)`. At the Lebesgue point `τᵢ`,
`σᵢ⁻¹ ∫_{τᵢ}^{τᵢ+σᵢ} g_{t,wᵢ}(z) dt → g_{τᵢ,wᵢ}(z)` uniformly for `z` near `q₁`
(`IsLebesguePointWithin.eventually_integral_le`, the continuity of `D_x P` from
`ControlSystem.continuousOn_fderiv_flow`), and `D_x P_{0 → t₁}` is the derivative in `a`
(`ControlSystem.hasFDerivAt_flow`, i.e. A–S's (2.19)). Lipschitz continuity: the comparison
estimate `ControlSystem.norm_flow_sub_flow_control_le` (the controls `u_σ`, `u_σ'` differ on a
set of measure `≤ Σ|σᵢ - σ'ᵢ|`) and the Lipschitz dependence on the initial point.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

open Classical in
/-- The needle control (12.14) of Agrachev–Sachkov: `wᵢ` on `[τᵢ, τᵢ + σᵢ)` (the first such `i`
if the intervals overlap), `ũ` elsewhere. -/
noncomputable def needleControl (ũ : ℝ → V) {k : ℕ} (τ : Fin k → ℝ) (w : Fin k → V)
    (σ : Fin k → ℝ) : ℝ → V :=
  fun t ↦ if h : ∃ i, t ∈ Ico (τ i) (τ i + σ i) then w (Fin.find _ h) else ũ t

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- `u_0 = ũ`. -/
theorem needleControl_zero (ũ : ℝ → V) {k : ℕ} (τ : Fin k → ℝ) (w : Fin k → V) :
    needleControl ũ τ w 0 = ũ := by
  funext t
  simp [needleControl]

/-- The orthant `ℝᵏ₊ = {σ | ∀ i, 0 ≤ σᵢ}`. -/
def orthant (k : ℕ) : Set (Fin k → ℝ) := {σ | ∀ i, 0 ≤ σ i}

variable {f : E → V → E} {U : Set V} {M L : ℝ≥0} {ũ : ℝ → V} {t₁ : ℝ} {k : ℕ}
  {τ : Fin k → ℝ} {w : Fin k → V}

/-- A needle control is a control on `[0, t₁]` when `ũ` is and the values `wᵢ` lie in `U`. -/
theorem isControlOn_needleControl (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U)
    (σ : Fin k → ℝ) : IsControlOn (needleControl ũ τ w σ) U 0 t₁ := by
  sorry

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {ψ : P → E} {a₀ : P}

/-- The end-point map of needle variations is Lipschitz near `(a₀, 0)` on the cone `P × ℝᵏ₊`
(Agrachev–Sachkov, p. 172: "is Lipschitzian"). -/
theorem lipschitzOnWith_needle (hf : IsBoundedC1System f U M L) (ht₁ : 0 < t₁)
    (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U) (hψ : ContDiffAt ℝ 1 ψ a₀) :
    ∃ ρ > 0, ∃ K, LipschitzOnWith K
      (fun p : P × (Fin k → ℝ) ↦ flow f (needleControl ũ τ w p.2) 0 t₁ (ψ p.1))
      ((univ ×ˢ orthant k) ∩ ball (a₀, 0) ρ) := by
  sorry

/-- **Derivative of the needle variations** at `(a₀, 0)` within the cone `P × ℝᵏ₊`
(Agrachev–Sachkov, p. 172: `∂F/∂sᵢ|_{s=0} = g_{τᵢ,uᵢ}(q₁)`; p. 182: `∂F/∂q v = P^{t₁}_* v`):
`(α, σ) ↦ D_x P_{0 → t₁}(ψ(a₀)) Dψ(a₀) α + Σᵢ σᵢ g_{τᵢ,wᵢ}(q₁)`, for distinct needle times
`τᵢ ∈ [0, t₁)` that are Lebesgue points of `ũ`. -/
theorem hasFDerivWithinAt_needle (hf : IsBoundedC1System f U M L) (ht₁ : 0 < t₁)
    (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U) (hτ : ∀ i, τ i ∈ Ico 0 t₁)
    (hτinj : Function.Injective τ) (hleb : ∀ i, IsLebesguePointWithin ũ (Icc 0 t₁) (τ i))
    (hψ : ContDiffAt ℝ 1 ψ a₀) :
    HasFDerivWithinAt
      (fun p : P × (Fin k → ℝ) ↦ flow f (needleControl ũ τ w p.2) 0 t₁ (ψ p.1))
      ((fderiv ℝ (flow f ũ 0 t₁) (ψ a₀)).comp
          ((fderiv ℝ ψ a₀).comp (ContinuousLinearMap.fst ℝ P (Fin k → ℝ))) +
        ∑ i, ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ P (Fin k → ℝ))).smulRight
          (variationField f ũ t₁ (τ i) (w i) (flow f ũ 0 t₁ (ψ a₀))))
      (univ ×ˢ orthant k) (a₀, 0) := by
  sorry

/-- The trajectories of needle variations from `ψ(a)` are uniformly close to the reference
trajectory from `ψ(a₀)` for `(a, σ)` near `(a₀, 0)` in the cone. -/
theorem norm_needle_trajectory_sub_lt (hf : IsBoundedC1System f U M L) (ht₁ : 0 < t₁)
    (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U) (hψ : ContinuousAt ψ a₀) {η : ℝ}
    (hη : 0 < η) :
    ∃ ρ > 0, ∀ p ∈ (univ ×ˢ orthant k) ∩ ball (a₀, 0) ρ, ∀ t ∈ Icc 0 t₁,
      ‖flow f (needleControl ũ τ w p.2) 0 t (ψ p.1) - flow f ũ 0 t (ψ a₀)‖ < η := by
  sorry

end ControlSystem
