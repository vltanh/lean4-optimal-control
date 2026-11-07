module

public import OptimalControl.ODE.ControlSystem

/-!
# Measurable changes of time in control systems

Agrachev–Sachkov reduce the free-time maximum principle to the fixed-time one by a change of
time (authors' draft, §12.3, proof of Theorem 12.2, pp. 173–174): along with `q' = f_u(q)` they
consider `q' = v f_u(q)`, `|v - 1| < δ`, whose admissible trajectories "are reparametrized
admissible trajectories of the initial system". They derive the reparametrization for a smooth
new time `φ` with `φ̇ > 0`, but apply it to measurable `v`. This file states the measurable
version (departure D7): for a measurable time scaling `v` with values in
`[c₁, c₂]`, `c₁ > 0`, and the new time `θ(t) = ∫₀ᵗ v`, an admissible pair `(w, x) = ((v, u), x)` of
the time-scaled system `x' = v f(x, u)` gives the admissible pair `(u ∘ θ⁻¹, x ∘ θ⁻¹)` of the
original system on `[0, θ(t₁)]`, and the costs correspond:
`∫₀^{t₁} v φ(x, u) = ∫₀^{θ(t₁)} φ(x ∘ θ⁻¹, u ∘ θ⁻¹)`. A–S's sets `|v - 1| < δ` and `v ≥ 0` are
replaced by compact intervals (departure D4).

## Proof sketch

`θ` is strictly increasing and bi-Lipschitz (`c₁ ≤ θ' ≤ c₂` a.e.), so it has a continuous
increasing inverse, Lipschitz with constant `c₁⁻¹`; `u ∘ θ⁻¹` is measurable. The push-forward of
`v · Leb|[0, t₁]` under `θ` is `Leb|[0, θ(t₁)]` (both give `θ(b) - θ(a)` to `[a, b]`), which is
the change of variables in both integrals.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric

namespace ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- **Change of time.** An admissible pair `((v, u), x)` on `[0, t₁]` of the time-scaled system
`x' = v f(x, u)`, `(v, u) ∈ [c₁, c₂] × U`, `c₁ > 0`, is a reparametrization of an admissible
pair of `x' = f(x, u)` on `[0, θ(t₁)]`, `θ(t) = ∫₀ᵗ v`: there is a continuous monotone `θ⁻¹`,
inverse to `θ` between `[0, t₁]` and `[0, θ(t₁)]`, such that `(u ∘ θ⁻¹, x ∘ θ⁻¹)` is admissible
and `∫₀^{t₁} v φ(x, u) = ∫₀^{θ(t₁)} φ(x ∘ θ⁻¹, u ∘ θ⁻¹)` for every continuous cost `φ`. -/
theorem IsAdmissible.timeChange {f : E → V → E} {U : Set V} (hU : IsCompact U)
    (hf : ContinuousOn (fun p : E × V ↦ f p.1 p.2) (univ ×ˢ U)) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    {x₀ : E} {t₁ : ℝ} (ht₁ : 0 ≤ t₁) {w : ℝ → ℝ × V} {x : ℝ → E}
    (h : IsAdmissible (fun y p ↦ p.1 • f y p.2) (Icc c₁ c₂ ×ˢ U) x₀ t₁ w x) :
    ∃ θinv : ℝ → ℝ, Continuous θinv ∧ Monotone θinv ∧
      (∀ t ∈ Icc 0 t₁, θinv (∫ r in (0 : ℝ)..t, (w r).1) = t) ∧
      (∀ s ∈ Icc 0 (∫ r in (0 : ℝ)..t₁, (w r).1),
        θinv s ∈ Icc 0 t₁ ∧ ∫ r in (0 : ℝ)..θinv s, (w r).1 = s) ∧
      IsAdmissible f U x₀ (∫ r in (0 : ℝ)..t₁, (w r).1) (fun s ↦ (w (θinv s)).2)
        (fun s ↦ x (θinv s)) ∧
      ∀ φ : E → V → ℝ, ContinuousOn (fun p : E × V ↦ φ p.1 p.2) (univ ×ˢ U) →
        ∫ t in (0 : ℝ)..t₁, (w t).1 * φ (x t) (w t).2 =
          ∫ s in (0 : ℝ)..(∫ r in (0 : ℝ)..t₁, (w r).1), φ (x (θinv s)) (w (θinv s)).2 := by
  sorry

end ControlSystem
