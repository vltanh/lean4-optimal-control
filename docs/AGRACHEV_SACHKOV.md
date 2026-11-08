# Agrachev and Sachkov's Chapter 12

How the formalization relates to its source: the results of Chapter 12 one by one, the readings
and departures D1–D11 to which the docstrings refer, and the gaps found in the source. The
[README](../README.md) has the overview; the full statements and the method are in
[DETAILS.md](DETAILS.md).

- [The source](#the-source)
- [Result by result](#result-by-result)
- [Readings and departures from Agrachev–Sachkov](#readings-and-departures-from-agrachevsachkov)
- [Gaps in Agrachev–Sachkov](#gaps-in-agrachevsachkov)

## The source

A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the Geometric Viewpoint*, Encyclopaedia
of Mathematical Sciences 87, Springer, 2004 (Chapter 10, Theorem 10.1; Chapter 12).

The source is the authors' draft of the book (preface September 2003), posted on A. A.
Agrachev's home page (<https://people.sissa.it/~agrachev/agrachev_files/books.html>). Page
numbers here and in the docstrings are the draft's.

## Result by result

| Agrachev–Sachkov (draft pages) | Lean |
| --- | --- |
| Lemma 12.1, p. 168 | [`Pontryagin.lemma12_1`](../OptimalControl/Pontryagin/Geometric.lean#L72); on any convex cone (its Remark (1)): [`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`](../OptimalControl/Convex/Cone/Openness.lean#L70) |
| Lemma 12.2, p. 170 | [`Pontryagin.lemma12_2`](../OptimalControl/Pontryagin/Geometric.lean#L608); in the form used by the proof of Theorem 12.4: [`Pontryagin.lemma12_2_local`](../OptimalControl/Pontryagin/Geometric.lean#L267) |
| Theorem 12.1, p. 164 (geometric PMP) | [`Pontryagin.theorem12_1`](../OptimalControl/Pontryagin/Geometric.lean#L710); in the form used by the proof of Theorem 12.4: [`Pontryagin.exists_costate_of_boundary`](../OptimalControl/Pontryagin/Geometric.lean#L648) |
| Theorem 12.2, p. 173 (free time) | [`Pontryagin.theorem12_2`](../OptimalControl/Pontryagin/FreeTime.lean#L78) |
| Theorem 12.3, p. 176 (cost, fixed end points) | [`Pontryagin.theorem12_3`](../OptimalControl/Pontryagin/IntegralCost.lean#L542) |
| Theorem 12.4, p. 178 (cost, `q(0) ∈ N₀`, `q(t₁) ∈ N₁`) | [`Pontryagin.theorem12_4`](../OptimalControl/Pontryagin/IntegralCost.lean#L608) |
| Theorem 12.5, p. 183 (cost, `(q(0), q(t₁)) ∈ N`) | [`Pontryagin.theorem12_5`](../OptimalControl/Pontryagin/IntegralCost.lean#L725) |
| Theorem 12.5 with free time (remark after it) | [`Pontryagin.maximum_principle`](../OptimalControl/Pontryagin/MaximumPrinciple.lean#L320) |

In these statements `q` is the reference trajectory (Agrachev and Sachkov's `q̃`) of the
reference control `ũ`, and `p` the covector curve (their `λ_t`).

The submanifolds `N₀`, `N₁` and `N` enter, as in Agrachev and Sachkov's proof, only near the end
points: `N₀` through a `C¹` parametrization `ψ`, `N₁` and `N` through `C¹` maps `Φ`, `G` with
surjective derivative whose zeros lie in them.

In `theorem12_4` the hypotheses `q(0) ∈ N₀` and `q(t₁) ∈ N₁` are Agrachev and Sachkov's (the
reference trajectory satisfies the boundary conditions). The proof does not use them, since they
follow from the hypotheses on `ψ` and `Φ`.

<details>
<summary>The statements in Lean</summary>

With the section variables `{Ω : Set E} {U : Set V} {f : E → V → E} {φ : E → V → ℝ} {t₁ : ℝ}
{ũ : ℝ → V} {q : ℝ → E}`:

```lean
theorem lemma12_1 {m n : ℕ} {F : (Fin m → ℝ) → Fin n → ℝ} {F' : (Fin m → ℝ) →L[ℝ] Fin n → ℝ}
    (hlip : ∃ K, LipschitzWith K F) (h0 : F 0 = 0) (hF : HasFDerivAt F F' 0)
    (hsurj : F' '' {x | ∀ i, 0 ≤ x i} = univ) :
    ∀ O ∈ 𝓝 (0 : Fin m → ℝ), (0 : Fin n → ℝ) ∈ interior (F '' (O ∩ {x | ∀ i, 0 ≤ x i}))

theorem HasFDerivWithinAt.zero_mem_interior_image_inter_cone {C : Set E} {Fm : E → F}
    {Fm' : E →L[ℝ] F} (hFm : HasFDerivWithinAt Fm Fm' C 0) (hC : Convex ℝ C)
    (hCcone : ∀ x ∈ C, ∀ c : ℝ, 0 ≤ c → c • x ∈ C)
    (h0 : Fm 0 = 0) (hlip : ∃ ρ > 0, ∃ K, LipschitzOnWith K Fm (C ∩ ball 0 ρ))
    (hsurj : Fm' '' C = univ) :
    ∀ O ∈ 𝓝 (0 : E), (0 : F) ∈ interior (Fm '' (O ∩ C))

theorem lemma12_2 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hcone : PointedCone.hull ℝ ((fun p : ℝ × V ↦ needleVector f ũ q t₁ p.1 p.2) ''
      ({τ | τ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ} ×ˢ U)) = ⊤) :
    q t₁ ∈ interior (attainableSet f Ω U (q 0) t₁)

theorem theorem12_1 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hbd : q t₁ ∈ frontier (attainableSet f Ω U (q 0) t₁)) :
    ∃ p : ℝ → StrongDual ℝ E, (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, p t ≠ 0) ∧ IsAdjoint f 0 0 ũ q t₁ p ∧ IsMaximal f 0 0 U ũ q t₁ p

theorem theorem12_2 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) {ε : ℝ} (hε : ε ∈ Ioo 0 t₁)
    (hbd : q t₁ ∈ frontier (⋃ t ∈ Ioo (t₁ - ε) (t₁ + ε), attainableSet f Ω U (q 0) t)) :
    ∃ p : ℝ → StrongDual ℝ E, (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, p t ≠ 0) ∧ IsAdjoint f 0 0 ũ q t₁ p ∧ IsMaximal f 0 0 U ũ q t₁ p ∧
      ∀ᵐ t ∂(volume.restrict (Icc 0 t₁)), controlHamiltonian f 0 0 (q t) (p t) (ũ t) = 0

theorem theorem12_3 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U)
    (ht₁ : 0 < t₁) (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hopt : ∀ (u : ℝ → V) (x : ℝ → E), IsAdmissibleIn f Ω U (q 0) t₁ u x → x t₁ = q t₁ →
      cost φ t₁ ũ q ≤ cost φ t₁ u x) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, (ν, p t) ≠ 0) ∧ IsAdjoint f φ ν ũ q t₁ p ∧ IsMaximal f φ ν U ũ q t₁ p ∧
      ν ≤ 0

theorem theorem12_4 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U)
    (ht₁ : 0 < t₁) {N₀ N₁ : Set E} (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (_hq₀ : q 0 ∈ N₀) (_hq₁ : q t₁ ∈ N₁)
    (hopt : ∀ (u : ℝ → V) (x : ℝ → E), IsAdmissibleIn f Ω U (x 0) t₁ u x → x 0 ∈ N₀ →
      x t₁ ∈ N₁ → cost φ t₁ ũ q ≤ cost φ t₁ u x)
    {ψ : P → E} {a₀ : P} (hψ : ContDiffAt ℝ 1 ψ a₀) (hψ0 : ψ a₀ = q 0)
    (hψN : ∀ᶠ a in 𝓝 a₀, ψ a ∈ N₀) {Φ : E → Q} (hΦ : ContDiffAt ℝ 1 Φ (q t₁))
    (hΦsurj : Function.Surjective (fderiv ℝ Φ (q t₁))) (hΦ0 : Φ (q t₁) = 0)
    (hΦN : ∀ᶠ x in 𝓝 (q t₁), Φ x = 0 → x ∈ N₁) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      IsAdjoint f φ ν ũ q t₁ p ∧ IsMaximal f φ ν U ũ q t₁ p ∧
      (∀ t ∈ Icc 0 t₁, (p t, ν) ≠ 0) ∧ ν ≤ 0 ∧
      (p 0).comp (fderiv ℝ ψ a₀) = 0 ∧ ∀ w, fderiv ℝ Φ (q t₁) w = 0 → p t₁ w = 0

theorem theorem12_5 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U)
    (ht₁ : 0 < t₁) {N : Set (E × E)} (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hqN : (q 0, q t₁) ∈ N)
    (hopt : ∀ (u : ℝ → V) (x : ℝ → E), IsAdmissibleIn f Ω U (x 0) t₁ u x → (x 0, x t₁) ∈ N →
      cost φ t₁ ũ q ≤ cost φ t₁ u x)
    {G : E × E → Q} (hG : ContDiffAt ℝ 1 G (q 0, q t₁))
    (hGsurj : Function.Surjective (fderiv ℝ G (q 0, q t₁))) (hG0 : G (q 0, q t₁) = 0)
    (hGN : ∀ᶠ z in 𝓝 (q 0, q t₁), G z = 0 → z ∈ N) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      IsAdjoint f φ ν ũ q t₁ p ∧ IsMaximal f φ ν U ũ q t₁ p ∧
      (∀ t ∈ Icc 0 t₁, (p t, ν) ≠ 0) ∧ ν ≤ 0 ∧
      ∀ v w : E, fderiv ℝ G (q 0, q t₁) (v, w) = 0 → -p 0 v + p t₁ w = 0
```

</details>

## Readings and departures from Agrachev–Sachkov

The docstrings refer to these departures:

- D1. The manifold `M` is an open subset `Ω` of a finite-dimensional real normed space `E`.
- D2. The chronological calculus (operators on `C^∞(M)`; (2.19), (2.28), (2.31), Proposition
  11.3) is read pointwise along trajectories, in coordinates: the vectors `g_{τ,u}` through the
  resolvent of the variational equation, Proposition 11.3 as the adjoint equation, the variations
  formula (12.13) as an integral equation for the transported trajectory.
- D3. The system and the cost are `C¹` in the state instead of `C^∞` (a generalization).
- D4. `U` is compact (the local boundedness of `f(q, u(t))` is tacit in the source); the
  auxiliary parameter sets of §§12.3–12.4 (`|v - 1| < δ`, `v ≥ 0`) are compact intervals.
- D5. Strong local minimizers instead of optimal (globally minimizing) controls (a
  generalization).
- D6. Free time together with a cost and mixed boundary conditions, which Agrachev and Sachkov
  leave to the reader (an exercise after Theorem 12.3, p. 177; remarks after Theorems 12.4 and
  12.5, pp. 179 and 184), is proved by applying the reductions of Theorems 12.2, 12.3 and 12.5
  through one auxiliary system.
- D7. Time changes are measurable (a forced departure). Agrachev and Sachkov derive the
  reparametrization for a smooth new time (p. 173) and apply it to measurable `v`. Here, for `v`
  measurable with values in `[c₁, c₂]`, `c₁ > 0`, and `θ(t) = ∫₀ᵗ v`, the push-forward of
  `v · Leb|[0, T]` under `θ` is `Leb|[0, θ(T)]`, which gives the change of variables in the
  integral equation and in the cost. Mathlib's substitution lemmas need a derivative at every
  point, while `θ' = v` holds only almost everywhere.
- D8. Lemma 12.1 in the form of its Remark (1), on any convex cone, with `F` Lipschitz only near
  `0` on the cone and differentiable at `0` within it.
- D9. One supporting covector for all needle variations at once, in Theorems 12.4 and 12.5 (and
  `exists_costate_of_boundary`). The proof of Theorem 12.4 takes, in (12.41), a covector for each
  finite needle variation, while the maximum condition at almost every `t` needs a single one.
- D10. Brouwer's theorem, for which the source gives no reference, comes from the
  [FixedPoint](https://github.com/vltanh/lean4-fixed-point) package.
- D11. Carathéodory well-posedness and differentiable dependence, which the source cites to
  Gamkrelidze (1978), are proved here by Picard iteration and Gronwall's inequality. A cut-off to
  a compact tube around the reference trajectory replaces the source's assumption that the vector
  fields are complete.

### Further readings

- `0 < t₁` is Agrachev and Sachkov's standing assumption ("Fix an arbitrary instant `t₁ > 0`",
  p. 163) and a hypothesis of Lemma 12.2 and of the theorems here. It is needed: for `M = ℝ`,
  `U = [-1, 1]`, `f(q, u) = u` and `ũ ≡ 0`, the vectors `g_{0,u}(q₀) = u` generate `ℝ`, but the
  attainable set at time `0` is `{q₀}`.
- The hypothesis that the end point lies on the boundary of the attainable set is weakened, in
  `lemma12_2_local` and `exists_costate_of_boundary`, to "not an interior point of the image of
  the attainable set of nearby trajectories" (`localAttainableSet`), which is what the proofs use.
- The nontriviality `(λ_t, ν) ≢ (0, 0)` of (12.32) is stated for every `t` (in Theorem 12.5
  through the uniqueness for the adjoint equation).
- The needle intervals are half-open, so that the zero variation is the reference control
  exactly.

## Gaps in Agrachev–Sachkov

- **Lemma 12.1, Remark (1).** The proof takes points in the interior of the cone, which is empty
  for a convex cone with empty interior, a case the remark allows. The proof here takes the
  points `v + L z` as combinations of points of the cone with positive coefficients, so it uses
  no interior. For the cones to which the lemma is applied (`ℝᵏ₊` and `P × ℝᵏ₊`) the source's
  step is valid as written.
- **A needle at `t₁`.** In the proof of Lemma 12.2 the set of Lebesgue points may contain `t₁`,
  and a needle at `t₁` gives no variation on `[0, t₁]`. Such a needle time is moved to a nearby
  Lebesgue point of `(0, t₁)`, as Agrachev and Sachkov move repeated times.
- **The needle map.** That the end-point map of the needle variations is Lipschitz and
  differentiable at `0`, with partial derivatives `g_{τᵢ,uᵢ}(q₁)` (p. 172), is stated without
  proof. It is proved in [`NeedleVariation.lean`](../OptimalControl/ODE/NeedleVariation.lean)
  ([`ControlSystem.lipschitzOnWith_needle`](../OptimalControl/ODE/NeedleVariation.lean#L242),
  [`ControlSystem.hasFDerivWithinAt_needle`](../OptimalControl/ODE/NeedleVariation.lean#L522)).
