module

public import OptimalControl.ODE.FlowDerivative
public import OptimalControl.MeasureTheory.LebesguePoints

/-!
# The variations formula and the cotangent lift, read pointwise

Fix a reference control `ũ` and a final time `c`, and let `P_{t → c}` be the flow of
`y' = f(y, ũ(t))`. Agrachev–Sachkov's field (12.12) is
`g_{t,w} = (P_{t → c})_* (f_w - f_{ũ(t)})`, that is
`g_{t,w}(z) = D_x P_{t → c}(P_{c → t} z) (f(P_{c → t} z, w) - f(P_{c → t} z, ũ(t)))`
(`ControlSystem.variationField`); note `g_{t,ũ(t)} = 0`. This file states:

* **the variations formula (12.13), read pointwise**
  (`ControlSystem.flow_flow_eq_add_integral_variationField`): for every control `u`, the
  transported trajectory `y(t) = P_{t → c}(x(t))`, `x(t) = P^u_{s → t}(x₀)`, solves
  `y(t) = P_{s → c}(x₀) + ∫ₛᵗ g_{r,u(r)}(y(r)) dr`. With `s = 0`, `t = c` and `x₀ = q₀` this is
  A–S's `q_u(t₁) = q₁ ∘ exp→ ∫₀^{t₁} g_{τ,u(τ)} dτ`;
* **Proposition 11.3, read pointwise** (`ControlSystem.adjoint_fderiv_flow`): along the
  reference trajectory `q̃(t) = P_{s → t}(x₀)`, the covector curve
  `λ_t = λ_c ∘ D_x P_{t → c}(q̃(t))` (A–S's `λ_t = (P^{t₁}_t)^* λ_{t₁}`, p. 172) is Lipschitz
  and solves the adjoint equation `λ_t = λ_c + ∫ₜᶜ λ_r ∘ ∂ₓf(q̃(r), ũ(r)) dr`.

## Source and reading

Agrachev–Sachkov (authors' draft), the variations formula (2.27)–(2.28) of §2.7, used at p. 170
for (12.13); Proposition 11.3 (§11.5.2, p. 161), used at p. 172 for (12.4). The chronological
calculus (operators on `C^∞(M)`) is read pointwise along trajectories in coordinates (departure
D2), with `C¹` data (D3).

## Proof sketch

`y` is Lipschitz (the flow is Lipschitz in time and in the point, and `x` is Lipschitz), hence
differentiable a.e. and the integral of its derivative
(`LipschitzWith.intervalIntegral_deriv_eq_sub` in `OptimalControl/ODE/ControlSystem.lean`). At
a time `t` that is a Lebesgue point of `ũ` and of `r ↦ f(x(r), u(r))`, the cocycle property gives
`y(t + h) - y(t) = P_{t+h → c}(x(t + h)) - P_{t+h → c}(P_{t → t+h}(x(t)))`, and the derivative
of the flow (`ControlSystem.fderiv_flow_eq_stateTransition`) with the uniform Lebesgue-point
estimate (`IsLebesguePointWithin.eventually_integral_le`) gives `y'(t) = g_{t,u(t)}(y(t))`. The
second statement is `ControlSystem.fderiv_flow_eq_stateTransition` and
`ControlSystem.adjoint_stateTransition`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Agrachev–Sachkov's field (12.12), `g_{t,w} = (P_{t → c})_* (f_w - f_{ũ(t)})`, with
`P_{t → c}` the flow of the reference control `ũ`:
`g_{t,w}(z) = D_x P_{t → c}(P_{c → t} z) (f(P_{c → t} z, w) - f(P_{c → t} z, ũ(t)))`. -/
noncomputable def variationField (f : E → V → E) (ũ : ℝ → V) (c t : ℝ) (w : V) (z : E) : E :=
  fderiv ℝ (flow f ũ t c) (flow f ũ c t z) (f (flow f ũ c t z) w - f (flow f ũ c t z) (ũ t))

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- `g_{t,ũ(t)} = 0`. -/
theorem variationField_self (f : E → V → E) (ũ : ℝ → V) (c t : ℝ) (z : E) :
    variationField f ũ c t (ũ t) z = 0 := by
  simp [variationField]

variable {f : E → V → E} {U : Set V} {M L : ℝ≥0} {ũ u : ℝ → V} {a b : ℝ}

/-- **The variations formula** (Agrachev–Sachkov (12.13), read pointwise): for every control `u`
on `[a, b]`, the trajectory `x(t) = P^u_{s → t}(x₀)` transported by the reference flow,
`y(t) = P^ũ_{t → c}(x(t))`, solves `y(t) = P^ũ_{s → c}(x₀) + ∫ₛᵗ g_{r,u(r)}(y(r)) dr` on
`[a, b]`, the integrand being integrable. -/
theorem flow_flow_eq_add_integral_variationField (hf : IsBoundedC1System f U M L)
    (hũ : IsControlOn ũ U a b) (hu : IsControlOn u U a b) {s c : ℝ} (hs : s ∈ Icc a b)
    (hc : c ∈ Icc a b) (x₀ : E) :
    IntervalIntegrable (fun r ↦ variationField f ũ c r (u r) (flow f ũ r c (flow f u s r x₀)))
        volume a b ∧
      ∀ t ∈ Icc a b, flow f ũ t c (flow f u s t x₀) = flow f ũ s c x₀ +
        ∫ r in s..t, variationField f ũ c r (u r) (flow f ũ r c (flow f u s r x₀)) := by
  sorry

/-- **Proposition 11.3 of Agrachev–Sachkov, read pointwise**: along the reference trajectory
`q̃(t) = P_{s → t}(x₀)`, for a covector `λ_c`, the curve `λ_t = λ_c ∘ D_x P_{t → c}(q̃(t))` is
Lipschitz on `[a, b]` and solves the adjoint equation
`λ_t = λ_c + ∫ₜᶜ λ_r ∘ ∂ₓf(q̃(r), ũ(r)) dr`. -/
theorem adjoint_fderiv_flow (hf : IsBoundedC1System f U M L) (hũ : IsControlOn ũ U a b)
    {s c : ℝ} (hs : s ∈ Icc a b) (hc : c ∈ Icc a b) (x₀ : E) (ℓ : StrongDual ℝ E) :
    (∃ K, LipschitzOnWith K (fun t ↦ ℓ.comp (fderiv ℝ (flow f ũ t c) (flow f ũ s t x₀)))
        (Icc a b)) ∧
      ∀ t ∈ Icc a b, ℓ.comp (fderiv ℝ (flow f ũ t c) (flow f ũ s t x₀)) = ℓ +
        ∫ r in t..c, (ℓ.comp (fderiv ℝ (flow f ũ r c) (flow f ũ s r x₀))).comp
          (fderiv ℝ (f · (ũ r)) (flow f ũ s r x₀)) := by
  sorry

end ControlSystem
