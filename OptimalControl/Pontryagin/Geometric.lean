module

public import OptimalControl.Pontryagin.Defs
public import OptimalControl.Convex.Cone.Openness
public import OptimalControl.Convex.Cone.Support
public import OptimalControl.ODE.NeedleVariation

/-!
# The geometric maximum principle (Agrachev–Sachkov, §§12.1–12.2)

A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the Geometric Viewpoint*, Springer, 2004,
Chapter 12, read in the authors' draft (pages below are the draft's), on an open subset `Ω` of a
finite-dimensional real normed space `E` (departure D1):

* **Lemma 12.1** (p. 168), the topological lemma: `lemma12_1` (literal) and, in the form of its
  Remark (1) on convex cones, `HasFDerivWithinAt.zero_mem_interior_image_inter_cone`
  (`OptimalControl/Convex/Cone/Openness.lean`);
* **Lemma 12.2** (p. 170): if the needle vectors `g_{τ,u}(q₁)`, `τ` a Lebesgue point of `ũ`,
  `u ∈ U`, generate the tangent space as a convex cone, then `q₁ ∈ int A_{q₀}(t₁)`: `lemma12_2`;
  in the generalized form that the proof of Theorem 12.4 uses (initial points `ψ(a)` varying,
  the end point composed with a submersion `Φ`, competitors near the reference):
  `lemma12_2_local`;
* **Theorem 12.1** (p. 164): if `q̃(t₁) ∈ ∂A_{q₀}(t₁)`, there is a Lipschitzian covector curve
  `λ_t ≠ 0` with `λ̇_t = h⃗_{ũ(t)}(λ_t)` and `h_{ũ(t)}(λ_t) = max_{u ∈ U} h_u(λ_t)` for almost all
  `t`: `theorem12_1`;
* the same conclusion in the generalized form of the proof of Theorem 12.4 (pp. 179–182, the
  scheme of (12.37)–(12.48)), with the transversality conditions `λ_{t₁} = Φ^* ξ` and
  `λ₀ ⊥ T N₀`: `exists_costate_of_boundary`. Every other version of the maximum principle in
  `OptimalControl/Pontryagin/` is derived from it by A–S's reductions.

## Readings and departures (listed in the README)

D1 open subset of `E` for the manifold `M`; D2 chronological calculus read pointwise
(`g_{τ,u}(q₁)` through the resolvent of the variational equation, `needleVector`; Proposition
11.3 as the adjoint equation, `ControlSystem.adjoint_stateTransition`); D3 `C¹` data; D4 `U`
compact; D8 Lemma 12.1 on a cone with one-sided derivative; D9 one separating covector for all
needle variations (finitely many generators suffice, `exists_finset_hull_eq_top`); D10 Brouwer's
theorem from the FixedPoint package (A–S give no reference); D11 Carathéodory theory
proved by Picard–Gronwall, with a cut-off near the reference trajectory. The hypothesis "boundary
of the attainable set" is weakened to "not an interior point of the image of the local attainable
set" (`localAttainableSet`), which is what the proof uses (it holds for every neighbourhood
`O₀` in Lemma 12.1); this strengthens the theorems.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace Pontryagin

open ControlSystem

/-- **Agrachev–Sachkov, Lemma 12.1** (authors' draft, p. 168), as printed: let `F : ℝᵐ → ℝⁿ` be
Lipschitzian, `F(0) = 0`, differentiable at `0`, with `F'₀(ℝᵐ₊) = ℝⁿ`. Then for any neighbourhood
`O₀` of the origin, `0 ∈ int F(O₀ ∩ ℝᵐ₊)`.

Proof: the case `C = ℝᵐ₊` of `HasFDerivWithinAt.zero_mem_interior_image_inter_cone` (A–S's proof,
with Brouwer's fixed point theorem). -/
theorem lemma12_1 {m n : ℕ} {F : (Fin m → ℝ) → Fin n → ℝ} {F' : (Fin m → ℝ) →L[ℝ] Fin n → ℝ}
    (hlip : ∃ K, LipschitzWith K F) (h0 : F 0 = 0) (hF : HasFDerivAt F F' 0)
    (hsurj : F' '' {x | ∀ i, 0 ≤ x i} = univ) :
    ∀ O ∈ 𝓝 (0 : Fin m → ℝ), (0 : Fin n → ℝ) ∈ interior (F '' (O ∩ {x | ∀ i, 0 ≤ x i})) := by
  sorry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {Ω : Set E} {U : Set V} {f : E → V → E} {t₁ : ℝ} {ũ : ℝ → V} {q : ℝ → E}

/-- **Agrachev–Sachkov, Lemma 12.2** (authors' draft, p. 170): let `T ⊆ [0, t₁]` be the set of
Lebesgue points of the reference control `ũ`; if
`T_{q₁}M = cone{g_{τ,u}(q₁) | τ ∈ T, u ∈ U}`, then `q₁ ∈ int A_{q₀}(t₁)`. Here `q₁ = q(t₁)`
is the end point of the reference trajectory `q` (A–S's `q̃`) from `q₀ = q(0)`, and
`g_{τ,u}(q₁)` is `needleVector f ũ q t₁ τ u` (12.12).

Proof: the case `ψ` constant, `Φ = id` of `lemma12_2_local`. -/
theorem lemma12_2 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hcone : PointedCone.hull ℝ ((fun p : ℝ × V ↦ needleVector f ũ q t₁ p.1 p.2) ''
      ({τ | τ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ} ×ˢ U)) = ⊤) :
    q t₁ ∈ interior (attainableSet f Ω U (q 0) t₁) := by
  sorry

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {ψ : P → E} {a₀ : P}
  {Φ : E → Q}

/-- **Lemma 12.2 in the generalized form of the proof of Theorem 12.4** (Agrachev–Sachkov,
pp. 179–182): initial points `ψ(a)` (a `C¹` parametrization of `N₀` near `q(0)`), the end point
composed with a `C¹` map `Φ` (the submersion defining `N₁`), and competitors near the reference.
If the convex cone generated by the vectors `Φ'(R(0, t₁) ψ'(a₀) α)` (variations of the initial
point, A–S's `∂F/∂q`, (2.19)) and `Φ'(g_{τ,u}(q₁))` (needle variations at Lebesgue points `τ`,
`u ∈ U`) is the whole space, then for every `ε > 0`, `Φ(q₁)` is an interior point of the image
under `Φ` of the local attainable set.

Proof (A–S's proof of Lemma 12.2, with the changes of the proof of Theorem 12.4 (2)): by
`exists_finset_hull_eq_top`, finitely many of the vectors generate; move the needle times to
distinct Lebesgue points of `(0, t₁)` keeping the generation
(`IsLebesguePointWithin.exists_near`, `exists_forall_hull_eq_top_of_dist_lt`); cut the system off
near `q` (`IsC1On.exists_cutoff`), so that the needle end-point map
`F(a, σ) = Φ(P^{u_σ}_{0 → t₁}(ψ(a)))` is Lipschitz and differentiable at `(a₀, 0)` within
`P × ℝᵏ₊` with the derivative above (`ControlSystem.lipschitzOnWith_needle`,
`ControlSystem.hasFDerivWithinAt_needle`, `ControlSystem.fderiv_flow_eq_stateTransition`), and its
trajectories are near `q` (`ControlSystem.norm_needle_trajectory_sub_lt`); conclude with Lemma
12.1 on the cone `P × ℝᵏ₊` (`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`). -/
theorem lemma12_2_local (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) (hψ : ContDiffAt ℝ 1 ψ a₀) (hψ0 : ψ a₀ = q 0)
    (hΦ : ContDiffAt ℝ 1 Φ (q t₁))
    (hcone : PointedCone.hull ℝ
      (range (fun α : P ↦
          fderiv ℝ Φ (q t₁) (stateTransition (linearization f ũ q) 0 t₁ (fderiv ℝ ψ a₀ α))) ∪
        (fun p : ℝ × V ↦ fderiv ℝ Φ (q t₁) (needleVector f ũ q t₁ p.1 p.2)) ''
          ({τ | τ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ} ×ˢ U)) = ⊤) :
    ∀ ε > 0, Φ (q t₁) ∈ interior (Φ '' localAttainableSet f Ω U ψ a₀ q t₁ ε) := by
  sorry

/-- **The geometric maximum principle in the generalized form of the proof of Theorem 12.4**
(Agrachev–Sachkov, pp. 179–182; Theorem 12.1, p. 164, is the case `ψ` constant, `Φ = id`).
Let `(ũ, q)` be an admissible pair in `Ω` on `[0, t₁]`, `ψ` a `C¹` map with `ψ(a₀) = q(0)` and
`Φ` a `C¹` map with surjective derivative at `q(t₁)`. If for some `ε > 0`, `Φ(q(t₁))` is not an
interior point of the image under `Φ` of the local attainable set ((12.37), (12.45)), then there
are `ξ ≠ 0` and a Lipschitz covector curve `p` (A–S's `λ_t`) with `p(t₁) = ξ ∘ Φ'(q(t₁))`
((12.44)), `p(t) ≠ 0` for all `t`, the adjoint equation (12.4), the maximality condition (12.5)
for almost every `t`, and `p(0) ∘ ψ'(a₀) = 0` (`λ₀ ⊥ T_{q̃(0)}N₀`, (12.47)–(12.48)).

Proof (A–S): by `lemma12_2_local`, the cone of the vectors `Φ'(R(0, t₁)ψ'(a₀)α)` and
`Φ'(g_{τ,u}(q₁))` is not the whole space; a supporting covector `ξ ≠ 0`
(`exists_dual_ne_zero_nonpos_of_ne_top`) is `≤ 0` on it, hence `= 0` on the linear part.
Put `p(t) = ξ ∘ Φ' ∘ R(t, t₁)` (A–S's `λ_t = (P^{t₁}_t)^* λ_{t₁}`); Proposition 11.3, read
pointwise, is `ControlSystem.adjoint_stateTransition`, which also gives Lipschitz continuity and
`p(t) ≠ 0` (`ξ ∘ Φ' ≠ 0` since `Φ'` is onto); `⟨p(τ), f(q(τ), u) - f(q(τ), ũ(τ))⟩ ≤ 0` at
Lebesgue points, which have full measure (`ae_isLebesguePointWithin`), is the maximality
condition. -/
theorem exists_costate_of_boundary (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U)
    (ht₁ : 0 < t₁) (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) (hψ : ContDiffAt ℝ 1 ψ a₀)
    (hψ0 : ψ a₀ = q 0) (hΦ : ContDiffAt ℝ 1 Φ (q t₁))
    (hΦsurj : Function.Surjective (fderiv ℝ Φ (q t₁)))
    (hbd : ∃ ε > 0, Φ (q t₁) ∉ interior (Φ '' localAttainableSet f Ω U ψ a₀ q t₁ ε)) :
    ∃ (ξ : StrongDual ℝ Q) (p : ℝ → StrongDual ℝ E), ξ ≠ 0 ∧
      p t₁ = ξ.comp (fderiv ℝ Φ (q t₁)) ∧ (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, p t ≠ 0) ∧ IsAdjoint f 0 0 ũ q t₁ p ∧ IsMaximal f 0 0 U ũ q t₁ p ∧
      (p 0).comp (fderiv ℝ ψ a₀) = 0 := by
  sorry

/-- **Agrachev–Sachkov, Theorem 12.1 (PMP)** (authors' draft, p. 164): let `ũ(t)`,
`t ∈ [0, t₁]`, be an admissible control and `q̃(t) = q_ũ(t)` the corresponding solution of the
Cauchy problem (12.1), (12.2). If `q̃(t₁) ∈ ∂A_{q₀}(t₁)`, then there exists a Lipschitzian curve
`λ_t ∈ T*_{q̃(t)}M`, `0 ≤ t ≤ t₁`, such that `λ_t ≠ 0` (12.3), `λ̇_t = h⃗_{ũ(t)}(λ_t)` (12.4),
`h_{ũ(t)}(λ_t) = max_{u ∈ U} h_u(λ_t)` (12.5) for almost all `t ∈ [0, t₁]`.

In coordinates on `Ω ⊆ E` (D1): `q` is the reference trajectory (A–S's `q̃`) from `q(0) = q₀`;
the curve `p` (A–S's `λ_t`) is a Lipschitz curve in `E*`, (12.4) is the adjoint equation
`ṗ = -p ∘ ∂ₓf(q, ũ)` (`IsAdjoint` with `φ = 0`), (12.5) is `IsMaximal`; (12.3) is stated for
every `t`.

Proof (A–S, p. 172): Lemma 12.2 (`lemma12_2`) shows that the cone of needle vectors is not
the whole space; a supporting covector `λ_{t₁} ≠ 0` (`exists_dual_ne_zero_nonpos_of_ne_top`);
`λ_t = (P^{t₁}_t)^* λ_{t₁}` solves the Hamiltonian system by Proposition 11.3
(`ControlSystem.adjoint_stateTransition`), and the supporting inequality is the maximality
condition. (Equivalently, the case `ψ` constant, `Φ = id` of `exists_costate_of_boundary`.) -/
theorem theorem12_1 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hbd : q t₁ ∈ frontier (attainableSet f Ω U (q 0) t₁)) :
    ∃ p : ℝ → StrongDual ℝ E, (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, p t ≠ 0) ∧ IsAdjoint f 0 0 ũ q t₁ p ∧ IsMaximal f 0 0 U ũ q t₁ p := by
  sorry

end Pontryagin
