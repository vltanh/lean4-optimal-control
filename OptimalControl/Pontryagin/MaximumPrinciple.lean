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

## Readings and departures (listed in `docs/AGRACHEV_SACHKOV.md`)

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

## Proof

The auxiliary system on `ℝ × E × E` (`Pontryagin.Reduction.combined`):
`ẏ = v (φ(q, u) + β)`, `ẋ = 0`, `q̇ = v f(q, u)`, controls
`(v, β, u) ∈ [1 - δ, 1 + δ] × [0, 1] × U` (time scaling, cost slack, original control), reference
`(1, 0, ũ)` with trajectory `(J, q(0), q)`, `J(t) = ∫₀ᵗ φ(q, ũ)`, initial points
`ψ(a) = (0, a, a)` (the diagonal), terminal map `Φ̂(y, x, q) = (y, G(x, q))`. The parameter `δ`
is chosen with `δ T < ε₀` and `2 δ T < ρ`, where `ε₀` is the radius of strong local optimality
and `ρ` a modulus of uniform continuity of `q` for `ε₀ / 2`; the radius of the local attainable
set is `min(ε₀ / 2, ε_G)`, with `ε_G` the radius in which the zeros of `G` lie in `N`. A point
`(J(T) - η, 0)` of the image of the local attainable set would give, after the change of time
(`ControlSystem.IsAdmissible.timeChangeOn`; the new terminal time `T'` lies in
`[(1 - δ) T, (1 + δ) T]` and `|θ⁻¹(σ T') - σ T| ≤ 2 δ T`), a competitor of the original problem
on `[0, T']` that is near the reference in the sense of strong local minimizers, satisfies the
boundary condition and has cost `∫₀ᵀ v φ ≤ J(T) - η` (the slack `β ≥ 0` only adds cost); so
`exists_costate_of_boundary` applies. Its costate `(ν, η, λ)` has `ν, η` constant
(`Pontryagin.Reduction.adjoint_combined`, by `Pontryagin.Reduction.adjoint_prod` twice);
maximality in `β` gives `ν ≤ 0` (Theorem 12.3), in `v` gives `H = 0` (Theorem 12.2), at
`(1, 0)` the maximum condition; `λ̂(0) ∘ ψ' = 0` gives `η = -λ(0)` and `λ̂(T) = ξ̂ ∘ Φ̂'` gives
(12.53) (Theorem 12.5); `λ̂(t) ≠ 0` with `η = -λ(0)` and the uniqueness for the adjoint equation
(`Pontryagin.Reduction.eq_zero_of_adjoint`, from
`ControlSystem.eq_comp_stateTransition_of_adjoint`) gives `(ν, λ(t)) ≠ 0`. The hypothesis
`(q(0), q(T)) ∈ N` of `IsStrongLocalMinimizer` is not used (it follows from `G = 0` there).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace Pontryagin

open ControlSystem

namespace Reduction

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {Ω : Set E} {U : Set V} {f : E → V → E} {φ : E → V → ℝ} {T : ℝ} {ũ : ℝ → V}
  {q : ℝ → E}

/-- The auxiliary system of the maximum principle with free time, cost and mixed boundary
conditions, on `ℝ × (M × M)`: `ẏ = v (φ(q, u) + β)`, `ẋ = 0`, `q̇ = v f(q, u)`, with the control
`(v, β, u)` (time scaling, cost slack, original control). -/
def combined (f : E → V → E) (φ : E → V → ℝ) (s : ℝ × (E × E)) (w : ℝ × (ℝ × V)) :
    ℝ × (E × E) :=
  (w.1 * (φ s.2.2 w.2.2 + w.2.1), ((0 : E), w.1 • f s.2.2 w.2.2))

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The derivative in the state of the combined system:
`(y, x, q) ↦ (v ∂_q φ q, 0, v ∂_q f q)`. -/
theorem hasFDerivAt_combined (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U) {s : ℝ × (E × E)}
    (hs : s.2.2 ∈ Ω) {w : ℝ × (ℝ × V)} (hw : w.2.2 ∈ U) :
    HasFDerivAt (fun s' ↦ combined f φ s' w)
      ((w.1 • (fderiv ℝ (φ · w.2.2) s.2.2).comp
          ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E)))).prod
        ((0 : ℝ × (E × E) →L[ℝ] E).prod (w.1 • (fderiv ℝ (f · w.2.2) s.2.2).comp
          ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E)))))) s := by
  have hS : HasFDerivAt (fun s' : ℝ × (E × E) ↦ s'.2.2)
      ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E))) s :=
    hasFDerivAt_snd.snd
  have hφs := (hφ.differentiableAt _ hs _ hw).hasFDerivAt.comp s hS
  have hfs := (hf.differentiableAt _ hs _ hw).hasFDerivAt.comp s hS
  exact ((hφs.add_const w.2.1).const_mul w.1).prodMk
    ((hasFDerivAt_const (0 : E) s).prodMk (hfs.const_smul w.1))

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The combined system has A–S's regularity (10.2)–(10.4) when `f` and `φ` have. -/
theorem isC1On_combined (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U) (C₁ C₂ : Set ℝ) :
    IsC1On (combined f φ) (univ ×ˢ (univ ×ˢ Ω)) (C₁ ×ˢ (C₂ ×ˢ U)) where
  continuousOn := by
    have hmaps : MapsTo (fun p : (ℝ × (E × E)) × (ℝ × (ℝ × V)) ↦ (p.1.2.2, p.2.2.2))
        ((univ ×ˢ (univ ×ˢ Ω)) ×ˢ (C₁ ×ˢ (C₂ ×ˢ U))) (Ω ×ˢ U) :=
      fun p hp ↦ ⟨hp.1.2.2, hp.2.2.2⟩
    have hc : Continuous fun p : (ℝ × (E × E)) × (ℝ × (ℝ × V)) ↦ (p.1.2.2, p.2.2.2) :=
      continuous_fst.snd.snd.prodMk continuous_snd.snd.snd
    exact (continuous_snd.fst.continuousOn.mul ((hφ.continuousOn.comp hc.continuousOn hmaps).add
      continuous_snd.snd.fst.continuousOn)).prodMk (continuousOn_const.prodMk
        (continuous_snd.fst.continuousOn.smul (hf.continuousOn.comp hc.continuousOn hmaps)))
  differentiableAt := fun _ hs _ hw ↦
    (hasFDerivAt_combined hf hφ hs.2.2 hw.2.2).differentiableAt
  continuousOn_fderiv := by
    have hmaps : MapsTo (fun p : (ℝ × (E × E)) × (ℝ × (ℝ × V)) ↦ (p.1.2.2, p.2.2.2))
        ((univ ×ˢ (univ ×ˢ Ω)) ×ˢ (C₁ ×ˢ (C₂ ×ˢ U))) (Ω ×ˢ U) :=
      fun p hp ↦ ⟨hp.1.2.2, hp.2.2.2⟩
    have hc : Continuous fun p : (ℝ × (E × E)) × (ℝ × (ℝ × V)) ↦ (p.1.2.2, p.2.2.2) :=
      continuous_fst.snd.snd.prodMk continuous_snd.snd.snd
    have hcont : ContinuousOn (fun p : (ℝ × (E × E)) × (ℝ × (ℝ × V)) ↦
        ((p.2.1 • fderiv ℝ (φ · p.2.2.2) p.1.2.2).comp
          ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E)))).prod
        ((0 : ℝ × (E × E) →L[ℝ] E).prod ((p.2.1 • fderiv ℝ (f · p.2.2.2) p.1.2.2).comp
          ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E))))))
        ((univ ×ˢ (univ ×ˢ Ω)) ×ˢ (C₁ ×ˢ (C₂ ×ˢ U))) :=
      continuousOn_clm_prod
        ((continuous_snd.fst.continuousOn.smul (hφ.continuousOn_fderiv.comp hc.continuousOn
          hmaps)).clm_comp continuousOn_const)
        (continuousOn_clm_prod continuousOn_const
          ((continuous_snd.fst.continuousOn.smul (hf.continuousOn_fderiv.comp hc.continuousOn
            hmaps)).clm_comp continuousOn_const))
    refine hcont.congr fun p hp ↦ ?_
    rw [(hasFDerivAt_combined hf hφ hp.1.2.2 hp.2.2.2).fderiv]
    simp only [ContinuousLinearMap.smul_comp]

/-- The reference pair `((1, 0, ũ), (J, q(0), q))` of the combined system,
`J(t) = ∫₀ᵗ φ(q, ũ)`. -/
theorem isAdmissibleIn_combined (hU : IsCompact U) (hφ : IsC1On φ Ω U) (hT : 0 ≤ T)
    (href : IsAdmissibleIn f Ω U (q 0) T ũ q) {C₁ C₂ : Set ℝ} (hC₁ : (1 : ℝ) ∈ C₁)
    (hC₂ : (0 : ℝ) ∈ C₂) :
    IsAdmissibleIn (combined f φ) (univ ×ˢ (univ ×ˢ Ω)) (C₁ ×ˢ (C₂ ×ˢ U)) (0, (q 0, q 0)) T
      (fun t ↦ (1, (0, ũ t))) (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) := by
  obtain ⟨⟨hũm, hũU, hqc, hqi, hqeq⟩, hqΩ⟩ := href
  have hφi := (TimeChange.integrand_bound hU hφ.continuousOn hT hqc hũm.aemeasurable
    fun t ht ↦ ⟨hqΩ t ht, hũU t ht⟩).2.2
  have hφc : ContinuousOn (fun t ↦ ∫ r in (0 : ℝ)..t, φ (q r) (ũ r)) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (by rw [uIcc_of_le hT]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 hφi)
    rwa [uIcc_of_le hT] at this
  have hi : IntervalIntegrable (fun s ↦ combined f φ
      (∫ r in (0 : ℝ)..s, φ (q r) (ũ r), (q 0, q s)) (1, (0, ũ s))) volume 0 T := by
    simpa [combined] using intervalIntegrable_prodMk hφi
      (intervalIntegrable_prodMk (intervalIntegrable_const (c := (0 : E))) hqi)
  refine ⟨⟨measurable_const.prodMk (measurable_const.prodMk hũm),
    fun t ht ↦ ⟨hC₁, hC₂, hũU t ht⟩, hφc.prodMk (continuousOn_const.prodMk hqc), hi,
    fun t ht ↦ ?_⟩, fun t ht ↦ ⟨mem_univ _, mem_univ _, hqΩ t ht⟩⟩
  have hit : IntervalIntegrable (fun s ↦ combined f φ
      (∫ r in (0 : ℝ)..s, φ (q r) (ũ r), (q 0, q s)) (1, (0, ũ s))) volume 0 t :=
    hi.mono_set (by rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
  have hit2 : IntervalIntegrable (fun s ↦ (combined f φ
      (∫ r in (0 : ℝ)..s, φ (q r) (ũ r), (q 0, q s)) (1, (0, ũ s))).2) volume 0 t :=
    intervalIntegrable_clm (ContinuousLinearMap.snd ℝ ℝ (E × E)) hit
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [Prod.fst_add, integral_fst hit]
    simp [combined]
  · rw [Prod.snd_add, Prod.fst_add, integral_snd hit, integral_fst hit2]
    simp [combined]
  · rw [Prod.snd_add, Prod.snd_add, integral_snd hit, integral_snd hit2]
    simpa [combined] using hqeq t ht

/-- An admissible pair of the combined system with `v ∈ [c₁, c₂]`, `c₁ > 0`, `β ∈ [0, 1]`: the
`x`-component is constant, the `q`-component is an admissible pair of the time-scaled system
`q̇ = v f(q, u)` in `Ω`, and `∫₀ᵀ v φ(q, u)` is at most the increase of the cost coordinate. -/
theorem IsAdmissibleIn.combined_proj (hU : IsCompact U) (hφ : IsC1On φ Ω U) (hT : 0 ≤ T)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) {z₀ : ℝ × (E × E)} {w : ℝ → ℝ × (ℝ × V)} {z : ℝ → ℝ × (E × E)}
    (h : IsAdmissibleIn (combined f φ) (univ ×ˢ (univ ×ˢ Ω)) (Icc c₁ c₂ ×ˢ (Icc 0 1 ×ˢ U)) z₀
      T w z) :
    (∀ t ∈ Icc 0 T, (z t).2.1 = z₀.2.1) ∧
      IsAdmissible (fun y (p : ℝ × V) ↦ p.1 • f y p.2) (Icc c₁ c₂ ×ˢ U) z₀.2.2 T
        (fun t ↦ ((w t).1, (w t).2.2)) (fun t ↦ (z t).2.2) ∧
      (∀ t ∈ Icc 0 T, (z t).2.2 ∈ Ω) ∧
      ∫ t in (0 : ℝ)..T, (w t).1 * φ (z t).2.2 (w t).2.2 ≤ (z T).1 - z₀.1 := by
  obtain ⟨⟨hwm, hwU, hzc, hzi, hzeq⟩, hzΩ⟩ := h
  have hsub : ∀ t ∈ Icc 0 T, uIcc 0 t ⊆ uIcc 0 T := fun t ht ↦ by
    rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have hzi2 : IntervalIntegrable (fun r ↦ (combined f φ (z r) (w r)).2) volume 0 T :=
    intervalIntegrable_clm (ContinuousLinearMap.snd ℝ ℝ (E × E)) hzi
  have hzc22 : ContinuousOn (fun t ↦ (z t).2.2) (Icc 0 T) :=
    continuous_snd.snd.comp_continuousOn hzc
  have hw' : Measurable fun t ↦ ((w t).1, (w t).2.2) :=
    (measurable_fst.comp hwm).prodMk (measurable_snd.snd.comp hwm)
  refine ⟨fun t ht ↦ ?_, ⟨hw', fun t ht ↦ ⟨(hwU t ht).1, (hwU t ht).2.2⟩, hzc22,
    intervalIntegrable_clm (ContinuousLinearMap.snd ℝ E E) hzi2, fun t ht ↦ ?_⟩,
    fun t ht ↦ (hzΩ t ht).2.2, ?_⟩
  · have := congrArg (fun p ↦ p.2.1) (hzeq t ht)
    simp only [Prod.snd_add, Prod.fst_add] at this
    rw [integral_snd (hzi.mono_set (hsub t ht)),
      integral_fst (hzi2.mono_set (hsub t ht))] at this
    simpa [combined] using this
  · have := congrArg (fun p ↦ p.2.2) (hzeq t ht)
    simp only [Prod.snd_add] at this
    rw [integral_snd (hzi.mono_set (hsub t ht)),
      integral_snd (hzi2.mono_set (hsub t ht))] at this
    simpa [combined] using this
  · have hφi := (TimeChange.integrand_bound (g := fun y (p : ℝ × V) ↦ p.1 * φ y p.2)
      (Ω := Ω) (U := Icc c₁ c₂ ×ˢ U) (isCompact_Icc.prod hU)
      (continuous_snd.fst.continuousOn.mul (hφ.continuousOn.comp
        (continuous_fst.prodMk continuous_snd.snd).continuousOn fun p hp ↦ ⟨hp.1, hp.2.2⟩))
      hT hzc22 hw'.aemeasurable fun t ht ↦ ⟨(hzΩ t ht).2.2, (hwU t ht).1, (hwU t ht).2.2⟩).2.2
    have h1 := congrArg Prod.fst (hzeq T ⟨hT, le_rfl⟩)
    rw [Prod.fst_add, integral_fst hzi] at h1
    rw [h1, add_sub_cancel_left]
    refine intervalIntegral.integral_mono_on hT hφi
      (intervalIntegrable_clm (ContinuousLinearMap.fst ℝ ℝ (E × E)) hzi) fun t ht ↦ ?_
    have hv : 0 < (w t).1 := hc₁.trans_le (hwU t ht).1.1
    have hβ : 0 ≤ (w t).2.1 := (hwU t ht).2.1.1
    simp only [combined]
    nlinarith

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- The Hamiltonian of the combined system with costate `λ̂ = (ν, η, λ)`:
`⟨λ̂, F_{(v, β, u)}⟩ = v (h^ν_u(λ) + ν β)`. -/
theorem controlHamiltonian_combined (p : StrongDual ℝ (ℝ × (E × E))) (s : ℝ × (E × E))
    (v β : ℝ) (u : V) :
    controlHamiltonian (combined f φ) 0 0 s p (v, (β, u)) =
      v * (controlHamiltonian f φ (p (1, 0)) s.2.2
        ((p.comp (ContinuousLinearMap.inr ℝ ℝ (E × E))).comp (ContinuousLinearMap.inr ℝ E E)) u +
        β * p (1, 0)) := by
  simp only [controlHamiltonian, combined, Pi.zero_apply, zero_mul, add_zero]
  rw [apply_prod_real, apply_prod (p.comp (ContinuousLinearMap.inr ℝ ℝ (E × E)))]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, map_smul, smul_eq_mul]
  rw [show ((0 : ℝ), ((0 : E), (0 : E))) = 0 from rfl, map_zero]
  ring

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- **The costate of the combined system**: along the reference `((1, 0, ũ), (J, q(0), q))`, a
solution `λ̂ = (ν, η, λ)` of the Hamiltonian system has `ν` and `η` constant, and `λ` solves the
adjoint equation `λ̇ = -λ ∘ ∂ₓf - ν ∂ₓφ`. -/
theorem adjoint_combined (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U) (hT : 0 ≤ T)
    (hqΩ : ∀ r ∈ Icc 0 T, q r ∈ Ω) (hũU : ∀ r ∈ Icc 0 T, ũ r ∈ U)
    {p : ℝ → StrongDual ℝ (ℝ × (E × E))}
    (hadj : IsAdjoint (combined f φ) 0 0 (fun t ↦ ((1 : ℝ), ((0 : ℝ), ũ t)))
      (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) T p) :
    (∀ t ∈ Icc 0 T, p t (1, 0) = p T (1, 0)) ∧
      (∀ t ∈ Icc 0 T, ((p t).comp (ContinuousLinearMap.inr ℝ ℝ (E × E))).comp
        (ContinuousLinearMap.inl ℝ E E) = ((p T).comp (ContinuousLinearMap.inr ℝ ℝ (E × E))).comp
          (ContinuousLinearMap.inl ℝ E E)) ∧
      IsAdjoint f φ (p T (1, 0)) ũ q T (fun t ↦ ((p t).comp
        (ContinuousLinearMap.inr ℝ ℝ (E × E))).comp (ContinuousLinearMap.inr ℝ E E)) := by
  obtain ⟨hi, heq⟩ := hadj
  obtain ⟨h1, h2, h3⟩ := adjoint_prod hT hi heq
    (α := fun r ↦ (fderiv ℝ (φ · (ũ r)) (q r)).comp (ContinuousLinearMap.snd ℝ E E))
    (β := fun r ↦ ((0 : E →L[ℝ] E).comp (ContinuousLinearMap.snd ℝ E E)).prod
      ((linearization f ũ q r).comp (ContinuousLinearMap.snd ℝ E E))) (μ := 0) fun r hr ↦ by
      have hl : linearization (combined f φ) (fun t ↦ ((1 : ℝ), ((0 : ℝ), ũ t)))
          (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) r = _ :=
        (hasFDerivAt_combined hf hφ
          (s := (∫ r' in (0 : ℝ)..r, φ (q r') (ũ r'), (q 0, q r)))
          (w := ((1 : ℝ), ((0 : ℝ), ũ r))) (hqΩ r hr) (hũU r hr)).fderiv
      rw [hl]
      have hD : ∀ x : ℝ × (E × E), ((1 : ℝ) • (fderiv ℝ (φ · (ũ r)) (q r)).comp
          ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E)))).prod
          ((0 : ℝ × (E × E) →L[ℝ] E).prod ((1 : ℝ) • (fderiv ℝ (f · (ũ r)) (q r)).comp
          ((ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ ℝ (E × E))))) x =
          ((((fderiv ℝ (φ · (ũ r)) (q r)).comp (ContinuousLinearMap.snd ℝ E E)).comp
            (ContinuousLinearMap.snd ℝ ℝ (E × E))).prod
          ((((0 : E →L[ℝ] E).comp (ContinuousLinearMap.snd ℝ E E)).prod
            ((linearization f ũ q r).comp (ContinuousLinearMap.snd ℝ E E))).comp
            (ContinuousLinearMap.snd ℝ ℝ (E × E)))) x := fun x ↦ by
        simp [linearization]
      simp only [one_smul] at hD ⊢
      rw [ContinuousLinearMap.ext hD]
      simp
  obtain ⟨h1', h2', h3'⟩ := adjoint_prod hT h2 h3 (α := fun _ ↦ 0)
    (β := linearization f ũ q) (μ := fun r ↦ p T (1, 0) • fderiv ℝ (φ · (ũ r)) (q r))
    fun r _ ↦ by
      rw [comp_real]
      simp [ContinuousLinearMap.smul_comp]
  refine ⟨fun t ht ↦ ?_, h1', ?_, fun t ht ↦ ?_⟩
  · simpa using congrArg (fun L ↦ L 1) (h1 t ht)
  · simpa using h2'
  · simpa using h3' t ht

end Reduction

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
* `(-p(0), p(T)) ⊥ ker G'(q(0), q(T))`, i.e. `(-p(0), p(T)) ⊥ T N`.

Proof: A–S's reductions of Theorems 12.2, 12.3 and 12.5 applied together to
`exists_costate_of_boundary` through one auxiliary system (module docstring; departure D6). -/
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
  obtain ⟨hT, href, -, ε₀, hε₀, hloc⟩ := hmin
  have hT' := hT.le
  have hũU := href.1.2.1
  have hqΩ := href.2
  have hqc := href.1.2.2.1
  have hTT : T ∈ Icc 0 T := ⟨hT', le_rfl⟩
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT'⟩
  /- Constants: `ε_G` for the boundary condition, `ρ` for the uniform continuity of `q`, the
  time-scaling parameter `δ` with `δ T < ε₀` and `2 δ T < ρ`, and the radius `ε` of the local
  attainable set. -/
  obtain ⟨εG, hεG, hεGN⟩ := Metric.eventually_nhds_iff.1 hGN
  obtain ⟨ρ, hρ, hρq⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hqc) (ε₀ / 2) (by positivity)
  set δ : ℝ := min (1 / 4) (min ε₀ ρ / (4 * T)) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (div_pos (lt_min hε₀ hρ) (by positivity))
  have hδ14 : δ ≤ 1 / 4 := min_le_left _ _
  have hδT : δ * T ≤ min ε₀ ρ / 4 :=
    calc δ * T ≤ min ε₀ ρ / (4 * T) * T :=
          mul_le_mul_of_nonneg_right (min_le_right (1 / 4) (min ε₀ ρ / (4 * T))) hT'
      _ = min ε₀ ρ / 4 := by field_simp
  have hδε : δ * T < ε₀ := hδT.trans_lt (by linarith [min_le_left ε₀ ρ])
  have hδρ : 2 * (δ * T) < ρ := by linarith [min_le_right ε₀ ρ]
  have hc₁ : 0 < 1 - δ := by linarith
  -- the combined system and its reference pair `((1, 0, ũ), (J, q(0), q))`
  have hF := Reduction.isC1On_combined hf hφ (Icc (1 - δ) (1 + δ)) (Icc 0 1)
  have hC : IsCompact (Icc (1 - δ) (1 + δ) ×ˢ (Icc (0 : ℝ) 1 ×ˢ U)) :=
    isCompact_Icc.prod (isCompact_Icc.prod hU)
  have hext := Reduction.isAdmissibleIn_combined hU hφ hT' href
    (C₁ := Icc (1 - δ) (1 + δ)) (C₂ := Icc 0 1) ⟨by linarith, by linarith⟩ ⟨le_rfl, zero_le_one⟩
  have h0 : (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) 0 =
      ((0 : ℝ), (q 0, q 0)) := by simp
  rw [← h0] at hext
  -- the initial points `ψ(a) = (0, a, a)` and the terminal map `Φ̂(y, x, q) = (y, G(x, q))`
  have hψ : ContDiffAt ℝ 1 (fun a : E ↦ ((0 : ℝ), (a, a))) (q 0) :=
    contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_id)
  have hψd : HasFDerivAt (fun a : E ↦ ((0 : ℝ), (a, a)))
      ((0 : E →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)))
      (q 0) :=
    (hasFDerivAt_const _ _).prodMk ((hasFDerivAt_id _).prodMk (hasFDerivAt_id _))
  have hΦ : ContDiffAt ℝ 1 (fun s : ℝ × (E × E) ↦ (s.1, G s.2))
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) T) :=
    contDiffAt_fst.prodMk (ContDiffAt.comp (g := G) (f := Prod.snd)
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) T) hG contDiffAt_snd)
  have hΦd : HasFDerivAt (fun s : ℝ × (E × E) ↦ (s.1, G s.2))
      ((ContinuousLinearMap.fst ℝ ℝ (E × E)).prod
        ((fderiv ℝ G (q 0, q T)).comp (ContinuousLinearMap.snd ℝ ℝ (E × E))))
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) T) :=
    hasFDerivAt_fst.prodMk (HasFDerivAt.comp (g := G) (f := Prod.snd)
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) T)
      (hG.differentiableAt one_ne_zero).hasFDerivAt hasFDerivAt_snd)
  have hΦsurj : Function.Surjective (fderiv ℝ (fun s : ℝ × (E × E) ↦ (s.1, G s.2))
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) T)) := by
    rw [hΦd.fderiv]
    rintro ⟨a, c⟩
    obtain ⟨b, hb⟩ := hGsurj c
    exact ⟨(a, b), by simp [hb]⟩
  /- `Φ̂(J(T), q(0), q(T)) = (J(T), 0)` is not an interior point of the image of the local
  attainable set: a point `(J(T) - η, 0)` of it would give, after the change of time, a competitor
  near `(ũ, q)` satisfying the boundary condition with a smaller cost. -/
  have hbd : ∃ ε > 0, (fun s : ℝ × (E × E) ↦ (s.1, G s.2))
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) T) ∉
        interior ((fun s : ℝ × (E × E) ↦ (s.1, G s.2)) '' localAttainableSet
          (Reduction.combined f φ) (univ ×ˢ (univ ×ˢ Ω)) (Icc (1 - δ) (1 + δ) ×ˢ (Icc 0 1 ×ˢ U))
          (fun a : E ↦ ((0 : ℝ), (a, a))) (q 0)
          (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) T ε) := by
    refine ⟨min (ε₀ / 2) εG, lt_min (by positivity) hεG, fun hint ↦ ?_⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
    obtain ⟨η, hη, hball⟩ := hint
    have hc : (fun s : ℝ × (E × E) ↦ (s.1, G s.2))
        ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), (q 0, q t))) T) = (cost φ T ũ q, 0) := by
      simp only [hG0]; rfl
    rw [hc] at hball
    obtain ⟨zT, ⟨a, w, z, ha, hz, hzq, hzT⟩, hzTΦ⟩ := hball (a := (cost φ T ũ q - η / 2, 0)) (by
      rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg]
      rw [abs_of_pos (by positivity), max_eq_left (by positivity)]
      linarith)
    have hz0 : z 0 = ((0 : ℝ), (a, a)) := ControlSystem.IsAdmissible.apply_zero hz.1 hT'
    obtain ⟨hzx, hadm, hzΩ, hcostz⟩ := Reduction.IsAdmissibleIn.combined_proj hU hφ hT' hc₁ hz
    simp only at hzx hadm hcostz
    -- the change of time `θ(t) = ∫₀ᵗ v`, `T' = θ(T)`
    obtain ⟨θinv, -, -, hθmem, hθl, hθr, hadm', hcostθ⟩ :=
      IsAdmissible.timeChangeOn hU hf.continuousOn hc₁ hT' hadm hzΩ
    simp only at hθl hθr hadm' hcostθ
    have hv : Measurable fun r ↦ (w r).1 := measurable_fst.comp hz.1.1
    have hvb : ∀ r ∈ Icc 0 T, (w r).1 ∈ Icc (1 - δ) (1 + δ) := fun r hr ↦ (hz.1.2.1 r hr).1
    have hb : ∀ t ∈ Icc 0 T, (1 - δ) * t ≤ ∫ r in (0 : ℝ)..t, (w r).1 ∧
        ∫ r in (0 : ℝ)..t, (w r).1 ≤ (1 + δ) * t := fun t ht ↦ by
      have := TimeChange.mul_le_integral_sub hT' hv hc₁ hvb h0T ht ht.1
      simpa using this
    set T' := ∫ r in (0 : ℝ)..T, (w r).1 with hT'def
    have hT'b := hb T hTT
    have hθ0 : θinv 0 = 0 := by simpa using hθl 0 h0T
    have hθT : θinv T' = T := hθl T hTT
    -- the competitor `(u ∘ θ⁻¹, q_z ∘ θ⁻¹)` on `[0, T']`
    have hT'pos : 0 < T' := by nlinarith
    have hz'0 : (z (θinv 0)).2.2 = a := by rw [hθ0, hz0]
    have hadmIn : IsAdmissibleIn f Ω U ((fun s ↦ (z (θinv s)).2.2) 0) T'
        (fun s ↦ (w (θinv s)).2.2) (fun s ↦ (z (θinv s)).2.2) := by
      refine ⟨?_, fun s _ ↦ hzΩ _ (hθmem s)⟩
      simp only [hz'0]
      exact hadm'
    have hN : ((fun s ↦ (z (θinv s)).2.2) 0, (fun s ↦ (z (θinv s)).2.2) T') ∈ N := by
      simp only [hz'0, hθT]
      have hzT2 : (z T).2 = (a, (z T).2.2) := Prod.ext (hzx T hTT) rfl
      have hzTq : dist (z T).2 (q 0, q T) < εG := by
        rw [dist_eq_norm]
        exact (norm_snd_le (z T - (∫ r in (0 : ℝ)..T, φ (q r) (ũ r), (q 0, q T)))).trans_lt
          ((hzq T hTT).trans_le (min_le_right _ _))
      rw [hzT2] at hzTq
      refine hεGN hzTq ?_
      rw [← hzT2, hzT]
      exact congrArg Prod.snd hzTΦ
    have hclose : ∀ σ ∈ Icc (0 : ℝ) 1, ‖(fun s ↦ (z (θinv s)).2.2) (σ * T') - q (σ * T)‖ < ε₀ := by
      intro σ hσ
      have hs : σ * T' ∈ Icc 0 T' := ⟨mul_nonneg hσ.1 hT'pos.le,
        mul_le_of_le_one_left hT'pos.le hσ.2⟩
      set t' := θinv (σ * T') with ht'
      have ht'I : t' ∈ Icc 0 T := hθmem _
      have hθt' : ∫ r in (0 : ℝ)..t', (w r).1 = σ * T' := hθr _ hs
      have hbt' := hb t' ht'I
      have hσT : σ * T ∈ Icc 0 T := ⟨mul_nonneg hσ.1 hT', mul_le_of_le_one_left hT' hσ.2⟩
      have h1 : ‖(z t').2.2 - q t'‖ < ε₀ / 2 := by
        have := (norm_snd_le ((z t' - (∫ r in (0 : ℝ)..t', φ (q r) (ũ r), (q 0, q t'))).2)).trans
          (norm_snd_le (z t' - (∫ r in (0 : ℝ)..t', φ (q r) (ũ r), (q 0, q t'))))
        exact this.trans_lt ((hzq t' ht'I).trans_le (min_le_left _ _))
      have h2 : ‖q t' - q (σ * T)‖ < ε₀ / 2 := by
        rw [← dist_eq_norm]
        refine hρq t' ht'I (σ * T) hσT ?_
        rw [Real.dist_eq, abs_lt]
        have e1 : δ * t' ≤ δ * T := mul_le_mul_of_nonneg_left ht'I.2 hδ0.le
        have e2 : σ * (δ * T) ≤ δ * T := mul_le_of_le_one_left (by positivity) hσ.2
        have e3 : 0 ≤ σ * (δ * T) := mul_nonneg hσ.1 (by positivity)
        have k1 : (1 - δ) * t' ≤ σ * T' := hθt' ▸ hbt'.1
        have k2 : σ * T' ≤ (1 + δ) * t' := hθt' ▸ hbt'.2
        have k3 : σ * T' ≤ σ * ((1 + δ) * T) := mul_le_mul_of_nonneg_left hT'b.2 hσ.1
        have k4 : σ * ((1 - δ) * T) ≤ σ * T' := mul_le_mul_of_nonneg_left hT'b.1 hσ.1
        constructor <;> linarith
      calc ‖(fun s ↦ (z (θinv s)).2.2) (σ * T') - q (σ * T)‖
          = ‖((z t').2.2 - q t') + (q t' - q (σ * T))‖ := by simp [ht']
        _ ≤ ‖(z t').2.2 - q t'‖ + ‖q t' - q (σ * T)‖ := norm_add_le _ _
        _ < ε₀ := by linarith
    have hTclose : |T' - T| < ε₀ := by
      rw [abs_lt]; constructor <;> nlinarith
    have hle := hloc T' _ _ hT'pos hadmIn hN hTclose hclose
    -- its cost is `∫₀ᵀ v φ(q_z, u) ≤ y(T) = J(T) - η/2`
    have hcost' : cost φ T' (fun s ↦ (w (θinv s)).2.2) (fun s ↦ (z (θinv s)).2.2) =
        ∫ t in (0 : ℝ)..T, (w t).1 * φ (z t).2.2 (w t).2.2 :=
      (hcostθ φ hφ.continuousOn).symm
    have hzT1 : (z T).1 = cost φ T ũ q - η / 2 := by rw [hzT]; exact congrArg Prod.fst hzTΦ
    rw [hzT1] at hcostz
    linarith
  obtain ⟨ξ, p, -, hpT, ⟨K, hpL⟩, hp0, hpadj, hpmax, hpψ⟩ := exists_costate_of_boundary
    (isOpen_univ.prod (isOpen_univ.prod hΩ)) hC hF hT hext hψ h0.symm hΦ hΦsurj hbd
  -- the costate `(ν, η, λ)` of the combined system
  obtain ⟨hνc, hηc, hadj⟩ := Reduction.adjoint_combined hf hφ hT' hqΩ hũU hpadj
  set Pr₁ : StrongDual ℝ (ℝ × (E × E)) →L[ℝ] StrongDual ℝ (E × E) :=
    (ContinuousLinearMap.inr ℝ ℝ (E × E)).precomp ℝ with hPr₁
  set Pr₂ : StrongDual ℝ (E × E) →L[ℝ] StrongDual ℝ E :=
    (ContinuousLinearMap.inr ℝ E E).precomp ℝ with hPr₂
  have hlamL : LipschitzOnWith (‖Pr₂‖₊ * (‖Pr₁‖₊ * K)) (fun t ↦ ((p t).comp
      (ContinuousLinearMap.inr ℝ ℝ (E × E))).comp (ContinuousLinearMap.inr ℝ E E)) (Icc 0 T) :=
    Pr₂.lipschitzWith.comp_lipschitzOnWith (Pr₁.lipschitzWith.comp_lipschitzOnWith hpL)
  -- transversality at `t = 0`: `η + λ₀ = 0`
  have hη0 : ∀ x, (((p 0).comp (ContinuousLinearMap.inr ℝ ℝ (E × E))).comp
      (ContinuousLinearMap.inl ℝ E E)) x = -(((p 0).comp (ContinuousLinearMap.inr ℝ ℝ (E × E))).comp
        (ContinuousLinearMap.inr ℝ E E)) x := fun x ↦ by
    have := congrArg (fun L ↦ L x) hpψ
    simp only [hψd.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply] at this
    rw [Reduction.apply_prod_real,
      Reduction.apply_prod ((p 0).comp (ContinuousLinearMap.inr ℝ ℝ (E × E)))] at this
    simp only [zero_mul, zero_add] at this
    exact eq_neg_of_add_eq_zero_left this
  have hηt : ∀ t ∈ Icc 0 T, ∀ x, (((p t).comp (ContinuousLinearMap.inr ℝ ℝ (E × E))).comp
      (ContinuousLinearMap.inl ℝ E E)) x = -(((p 0).comp (ContinuousLinearMap.inr ℝ ℝ (E × E))).comp
        (ContinuousLinearMap.inr ℝ E E)) x := fun t ht x ↦ by
    rw [hηc t ht, ← hηc 0 h0T, hη0]
  have hne : (ae (volume.restrict (Icc (0 : ℝ) T))).NeBot := ae_restrict_neBot.2 (by simp [hT])
  refine ⟨p T (1, 0), _, ?_, ⟨_, hlamL⟩, fun t ht h ↦ ?_, hadj, ?_, ?_, fun v w hvw ↦ ?_⟩
  · -- `ν ≤ 0`: maximality in the cost slack `β`
    obtain ⟨t, ht, htI⟩ := (hpmax.and (ae_restrict_mem measurableSet_Icc)).exists
    have := ht (1, (1, ũ t)) ⟨⟨by linarith, by linarith⟩, ⟨zero_le_one, le_rfl⟩, hũU t htI⟩
    simp only [Reduction.controlHamiltonian_combined, hνc t htI] at this
    linarith
  · -- nontriviality: if `ν = 0` and `λ_t = 0`, then `λ ≡ 0`, `η = -λ₀ = 0` and `λ̂_t = 0`
    rw [Prod.ext_iff] at h
    simp only [Prod.fst_zero, Prod.snd_zero] at h
    obtain ⟨hν0, hlam⟩ := h
    rw [hν0] at hadj
    have hlam0 := Reduction.eq_zero_of_adjoint hU hf hT' href hlamL.continuousOn hadj ht hlam
    refine hp0 t ht (ContinuousLinearMap.ext fun x ↦ ?_)
    rw [show x = (x.1, (x.2.1, x.2.2)) from rfl, Reduction.apply_prod_real,
      Reduction.apply_prod ((p t).comp (ContinuousLinearMap.inr ℝ ℝ (E × E))), hηt t ht,
      hνc t ht, hν0]
    simp only [ContinuousLinearMap.comp_apply] at hlam0 ⊢
    have h1 := congrArg (fun L ↦ L x.2.1) (hlam0 0 h0T)
    have h2 := congrArg (fun L ↦ L x.2.2) (hlam0 t ht)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      zero_apply] at h1 h2
    simp [h1, h2]
  · -- maximality: `(v, β) = (1, 0)`
    filter_upwards [hpmax, ae_restrict_mem measurableSet_Icc] with t ht htI u hu
    have := ht (1, (0, u)) ⟨⟨by linarith, by linarith⟩, ⟨le_rfl, zero_le_one⟩, hu⟩
    simp only [Reduction.controlHamiltonian_combined, hνc t htI] at this
    simpa using this
  · -- `H = 0`: maximality in the time scaling `v`, A–S (12.15)
    filter_upwards [hpmax, ae_restrict_mem measurableSet_Icc] with t ht htI
    have h1 := ht (1 + δ, (0, ũ t)) ⟨⟨by linarith, le_rfl⟩, ⟨le_rfl, zero_le_one⟩, hũU t htI⟩
    have h2 := ht (1 - δ, (0, ũ t)) ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, zero_le_one⟩, hũU t htI⟩
    simp only [Reduction.controlHamiltonian_combined, hνc t htI, zero_mul, add_zero,
      one_mul] at h1 h2
    nlinarith
  · -- transversality at `t = T`: `(η, λ_T) = (-λ₀, λ_T) ⊥ ker G'`
    have hd := hΦd.fderiv
    simp only at hd
    have := congrArg (fun L ↦ L (0, (v, w))) hpT
    simp only [hd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', hvw] at this
    rw [Reduction.apply_prod_real,
      Reduction.apply_prod ((p T).comp (ContinuousLinearMap.inr ℝ ℝ (E × E))), hηt T hTT,
      show ((0 : ℝ), (0 : Q)) = 0 from rfl, map_zero] at this
    simp only [zero_mul, zero_add, ContinuousLinearMap.comp_apply] at this ⊢
    linarith

end Pontryagin
