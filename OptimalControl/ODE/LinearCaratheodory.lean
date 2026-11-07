module

public import OptimalControl.ODE.Caratheodory

/-!
# Linear Carathéodory equations: the resolvent and the adjoint equation

For `A : ℝ → (E →L[ℝ] E)` bounded and a.e. strongly measurable on `[a, b]`, the *resolvent*
(state-transition operator) `R(s, t) = ControlSystem.resolvent A s t` is the solution at time `t`
of `Y' = A(t) ∘ Y`, `Y(s) = id`. It is the flow (`ControlSystem.flow`) of the linear control
system `Y' = B ∘ Y` on `E →L[ℝ] E` driven by the "control" `B = A(t)` with values in the compact
ball `‖B‖ ≤ K`. This file states:

* the integral equations in the final and in the initial time,
  `R(s, t) = id + ∫ₛᵗ A(r) ∘ R(s, r) dr` and `R(t, c) = id + ∫ₜᶜ R(r, c) ∘ A(r) dr`;
* the cocycle property `R(t, r) ∘ R(s, t) = R(s, r)`, hence invertibility;
* the bound `‖R(s, t)‖ ≤ e^{K|t - s|}` and Lipschitz continuity in each time;
* the *adjoint equation*: for a covector `ℓ`, `p(t) = ℓ ∘ R(t, c)` is Lipschitz and solves
  `p(t) = ℓ + ∫ₜᶜ p(r) ∘ A(r) dr`, that is `ṗ = -p ∘ A` a.e. with `p(c) = ℓ`.

## Source and reading

Agrachev–Sachkov (authors' draft) use the linear equation through the variations formula and
Proposition 11.3 (§11.5.2, p. 161: the cotangent lift of a nonautonomous flow is the flow of the
Hamiltonian lift), read pointwise along a trajectory in coordinates (departure D2): the
cotangent lift of the flow along `q̃` acts on covectors by `ℓ ↦ ℓ ∘ R(t, c)`, which solves
`λ̇ = -λ ∘ ∂ₓf(q̃(t), ũ(t))`.

## Proof sketch

Instance of `OptimalControl/ODE/Caratheodory.lean` for `f(Y, B) = B ∘ Y` on `E →L[ℝ] E`
(`IsLipschitzSystem` with constant `K`, `U = closedBall 0 K`); the initial-time equation and the
adjoint equation follow from the cocycle property (`R(t, c) = R(s, c) ∘ R(t, s)`) and the final-time
equation for `R(t, s)`, or by checking that `t ↦ R(t, c) ∘ R(s, t)` is constant.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace ControlSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The resolvent `R(s, t)` of the linear equation `Y' = A(t) ∘ Y`: the value at time `t` of the
solution with `Y(s) = id` (the flow of the linear system `Y' = B ∘ Y` driven by `B = A(t)`). -/
noncomputable def stateTransition (A : ℝ → E →L[ℝ] E) (s t : ℝ) : E →L[ℝ] E :=
  flow (fun Y B ↦ B.comp Y) A s t (ContinuousLinearMap.id ℝ E)

omit [FiniteDimensional ℝ E] in
/-- `R(s, s) = id`. -/
theorem stateTransition_self (A : ℝ → E →L[ℝ] E) (s : ℝ) :
    stateTransition A s s = ContinuousLinearMap.id ℝ E :=
  flow_self _ _ _ _

variable {A : ℝ → E →L[ℝ] E} {a b K : ℝ}

/-- The final-time equation `R(s, t) = id + ∫ₛᵗ A(r) ∘ R(s, r) dr`, with the integrand
integrable on `[a, b]`. -/
theorem stateTransition_eq_integral (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {s : ℝ} (hs : s ∈ Icc a b) :
    IntervalIntegrable (fun r ↦ (A r).comp (stateTransition A s r)) volume a b ∧
      ∀ t ∈ Icc a b, stateTransition A s t =
        ContinuousLinearMap.id ℝ E + ∫ r in s..t, (A r).comp (stateTransition A s r) := by
  sorry

/-- Uniqueness: a continuous solution of `Y(t) = Y₀ + ∫ₛᵗ A(r) ∘ Y(r) dr` on `[a, b]` is
`R(s, t) ∘ Y₀`. -/
theorem eq_stateTransition_comp (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {s : ℝ} (hs : s ∈ Icc a b) {Y₀ : E →L[ℝ] E}
    {Y : ℝ → E →L[ℝ] E} (hY : ContinuousOn Y (Icc a b))
    (hYeq : ∀ t ∈ Icc a b, Y t = Y₀ + ∫ r in s..t, (A r).comp (Y r)) :
    ∀ t ∈ Icc a b, Y t = (stateTransition A s t).comp Y₀ := by
  sorry

/-- The cocycle property `R(t, r) ∘ R(s, t) = R(s, r)`. -/
theorem stateTransition_comp_stateTransition
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b))) (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    {s t r : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hr : r ∈ Icc a b) :
    (stateTransition A t r).comp (stateTransition A s t) = stateTransition A s r := by
  sorry

/-- The bound `‖R(s, t)‖ ≤ e^{K|t - s|}`. -/
theorem norm_stateTransition_le (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖stateTransition A s t‖ ≤ Real.exp (K * |t - s|) := by
  sorry

/-- The initial-time equation `R(t, c) = id + ∫ₜᶜ R(r, c) ∘ A(r) dr` (`∂ₜR(t, c) = -R(t, c) A(t)`),
with the integrand integrable on `[a, b]`. -/
theorem stateTransition_eq_integral_left (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {c : ℝ} (hc : c ∈ Icc a b) :
    IntervalIntegrable (fun r ↦ (stateTransition A r c).comp (A r)) volume a b ∧
      ∀ t ∈ Icc a b, stateTransition A t c =
        ContinuousLinearMap.id ℝ E + ∫ r in t..c, (stateTransition A r c).comp (A r) := by
  sorry

/-- The resolvent is Lipschitz in each time on `[a, b]`. -/
theorem lipschitzOnWith_stateTransition (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {c : ℝ} (hc : c ∈ Icc a b) :
    (∃ C, LipschitzOnWith C (fun t ↦ stateTransition A c t) (Icc a b)) ∧
      ∃ C, LipschitzOnWith C (fun t ↦ stateTransition A t c) (Icc a b) := by
  sorry

/-- **The adjoint equation** (Agrachev–Sachkov, Proposition 11.3, read pointwise; departure D2):
for a covector `ℓ`, the curve `p(t) = ℓ ∘ R(t, c)` is Lipschitz on `[a, b]` and solves
`p(t) = ℓ + ∫ₜᶜ p(r) ∘ A(r) dr`, that is `ṗ = -p ∘ A` a.e. with `p(c) = ℓ`; and `p(t) ≠ 0` for
all `t ∈ [a, b]` when `ℓ ≠ 0` (the resolvent is invertible). -/
theorem adjoint_stateTransition (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {c : ℝ} (hc : c ∈ Icc a b) (ℓ : StrongDual ℝ E) :
    (∃ C, LipschitzOnWith C (fun t ↦ ℓ.comp (stateTransition A t c)) (Icc a b)) ∧
      IntervalIntegrable (fun r ↦ (ℓ.comp (stateTransition A r c)).comp (A r)) volume a b ∧
      (∀ t ∈ Icc a b, ℓ.comp (stateTransition A t c) =
        ℓ + ∫ r in t..c, (ℓ.comp (stateTransition A r c)).comp (A r)) ∧
      (ℓ ≠ 0 → ∀ t ∈ Icc a b, ℓ.comp (stateTransition A t c) ≠ 0) := by
  sorry

/-- Uniqueness for the adjoint equation: a continuous solution of
`p(t) = p(c) + ∫ₜᶜ p(r) ∘ A(r) dr` on `[a, b]` is `p(c) ∘ R(t, c)`. In particular it vanishes
identically on `[a, b]` as soon as it vanishes at one point. -/
theorem eq_comp_stateTransition_of_adjoint (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {c : ℝ} (hc : c ∈ Icc a b) {p : ℝ → StrongDual ℝ E}
    (hp : ContinuousOn p (Icc a b))
    (hpeq : ∀ t ∈ Icc a b, p t = p c + ∫ r in t..c, (p r).comp (A r)) :
    ∀ t ∈ Icc a b, p t = (p c).comp (stateTransition A t c) := by
  sorry

end ControlSystem
