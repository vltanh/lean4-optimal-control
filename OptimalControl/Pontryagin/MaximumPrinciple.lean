module

public import OptimalControl.Pontryagin.FreeTime
public import OptimalControl.Pontryagin.IntegralCost

/-!
# The Pontryagin maximum principle: free terminal time, integral cost, mixed boundary conditions

A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the Geometric Viewpoint*, Encyclopaedia
of Mathematical Sciences 87, Springer, 2004 (authors' draft, Chapter 12), prove Theorems
12.1–12.5 (fixed time; free time without cost, Theorem 12.2; cost with fixed, separated or mixed
boundary conditions, Theorems 12.3–12.5) and leave free time with a cost to the reader: after
Theorem 12.3, "(2) For the problem with free time `t₁` … necessary optimality conditions of PMP
are the same as in Theorem 12.3 plus one additional scalar equality `h^ν_{ũ(t)}(λ_t) ≡ 0`
(exercise)" (p. 177); after Theorem 12.4, "(2) The problem with free time … is reduced to the
case of fixed `t₁` in the same way as in Section 12.4" (p. 179); after Theorem 12.5, "(1)
Needless to say, if the terminal time `t₁` is free, then one should add to statements of Theorem
12.5 the additional equality `h^ν_{ũ(t)}(λ_t) ≡ 0`" (p. 184).

`Pontryagin.maximum_principle` is that statement: free terminal time, integral cost, mixed
boundary conditions `(q(0), q(T)) ∈ N` with `N` given near the end points by a `C¹` submersion
`G = 0`, for strong local minimizers. Conclusion: `ν ≤ 0`, a Lipschitz covector curve `p`,
`(ν, p(t)) ≠ 0` for every `t`, the adjoint equation, the maximum condition and `H = 0` for almost
every `t` (A–S (12.15)), and the transversality condition (12.53). The control set is compact
(D4), the data `C¹` with `∂f/∂q` jointly continuous (A–S's (10.2)–(10.4) with `C¹` for `C^∞`,
D3).

## Readings and departures (listed in the README)

* D1: `M` an open subset `Ω` of a finite-dimensional real normed space `E`.
* D2: chronological calculus read pointwise along trajectories (variations formula, derivative
  of flows, Proposition 11.3).
* D3: `C¹` instead of `C^∞`. D4: `U` compact; A–S's auxiliary parameters `|v - 1| < δ`, `v ≥ 0`
  replaced by compact intervals.
* D5: strong local minimizers instead of optimal (globally minimizing) controls.
* D6: free time with cost and mixed boundary conditions, assembled from A–S's reductions (the
  time scaling of Theorem 12.2, the cost extension of Theorem 12.3, the doubled system of
  Theorem 12.5) applied together to `exists_costate_of_boundary`.
* D7: measurable time scalings. D8: Lemma 12.1 on cones. D9: one separating covector for all
  needle variations. D10: Brouwer's theorem from the FixedPoint package. D11: Carathéodory
  well-posedness and differentiable dependence by Picard–Gronwall, with a cut-off.

## Proof sketch

The auxiliary system on `ℝ × E × E`: `ẏ = v (φ(q, u) + β)`, `ẋ = 0`, `q̇ = v f(q, u)`, controls
`(v, β, u) ∈ [1 - δ, 1 + δ] × [0, 1] × U` (time scaling, cost slack, original control), reference
`(1, 0, ũ)`, initial points `ψ(a) = (0, a, a)` (the diagonal), terminal map
`Φ̂(y, x, q) = (y, G(x, q))`. A point `(J̃ - η, 0)` of the image of the local attainable set would
give, after the change of time (`ControlSystem.IsAdmissible.timeChange`), a competitor of the
original problem that is near the reference in the sense of strong local minimizers and cheaper;
so `exists_costate_of_boundary` applies. Its costate `(ν, η, p)` has `ν, η` constant; maximality
in `β` gives `ν ≤ 0` (Theorem 12.3), in `v` gives `H = 0` (Theorem 12.2), at `(1, 0)` the
maximum condition; `λ̂(0) ∘ ψ' = 0` gives `η = -p(0)` and `λ̂(T) = ξ̂ ∘ Φ̂'` gives (12.53)
(Theorem 12.5); `λ̂(t) ≠ 0` with `η = -p(0)` and the uniqueness for the adjoint equation
(`ControlSystem.eq_comp_stateTransition_of_adjoint`) gives `(ν, p(t)) ≠ 0`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace Pontryagin

open ControlSystem

variable {E V Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- **The Pontryagin maximum principle** (Agrachev–Sachkov, Theorem 12.5 with its Remark (1),
free terminal time). Let `(ũ, q)` be a strong local minimizer of `∫₀^T φ(q, u) dt` among
admissible pairs in the open set `Ω` with free terminal time and `(q(0), q(T)) ∈ N`, where near
`(q(0), q(T))` the set `N` contains the zeros of a `C¹` map `G` with surjective derivative and
`G(q(0), q(T)) = 0`. Then there are `ν ≤ 0` and a Lipschitz covector curve `p : [0, T] → E*`
such that

* `(ν, p(t)) ≠ 0` for every `t ∈ [0, T]`;
* `ṗ = -p ∘ ∂ₓf(q, ũ) - ν ∂ₓφ(q, ũ)` (integral form);
* for almost every `t`, `H(q(t), p(t), ũ(t)) = max_{u ∈ U} H(q(t), p(t), u)` and
  `H(q(t), p(t), ũ(t)) = 0`, with `H(q, p, u) = ⟨p, f(q, u)⟩ + ν φ(q, u)`;
* `(-p(0), p(T)) ⊥ ker G'(q(0), q(T))`, i.e. `(-p(0), p(T)) ⊥ T N`. -/
theorem maximum_principle {Ω : Set E} (hΩ : IsOpen Ω) {U : Set V}
    (hU : IsCompact U) {f : E → V → E} (hf : IsC1On f Ω U) {φ : E → V → ℝ}
    (hφ : IsC1On φ Ω U) {N : Set (E × E)} {T : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    (hmin : IsStrongLocalMinimizer f φ Ω U N T ũ q) {G : E × E → Q}
    (hG : ContDiffAt ℝ 1 G (q 0, q T)) (hGsurj : Function.Surjective (fderiv ℝ G (q 0, q T)))
    (hG0 : G (q 0, q T) = 0) (hGN : ∀ᶠ z in 𝓝 (q 0, q T), G z = 0 → z ∈ N) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), ν ≤ 0 ∧ (∃ K, LipschitzOnWith K p (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) ∧ IsAdjoint f φ ν ũ q T p ∧ IsMaximal f φ ν U ũ q T p ∧
      (∀ᵐ t ∂(volume.restrict (Icc 0 T)), controlHamiltonian f φ ν (q t) (p t) (ũ t) = 0) ∧
      ∀ v w : E, fderiv ℝ G (q 0, q T) (v, w) = 0 → -p 0 v + p T w = 0 := by
  sorry

end Pontryagin
