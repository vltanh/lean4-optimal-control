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
`δ' = ε/(2 t₁)` (A–S take `|v - 1| < δ = ε/t₁`; a compact interval gives the same conclusion,
D4). Its admissible trajectories in `Ω` are reparametrized trajectories of the original system
(`ControlSystem.IsAdmissible.timeChangeOn`, the form of `ControlSystem.IsAdmissible.timeChange`
for data continuous on `Ω × U`; A–S derive this for a smooth time change and use it for
measurable `v`, D7), the new terminal time `θ(t₁) = ∫₀^{t₁} v` lying in
`[(1 - δ') t₁, (1 + δ') t₁] ⊆ (t₁ - ε, t₁ + ε)`, so its attainable set at time `t₁` lies in
`⋃_{|t - t₁| < ε} A_{q₀}(t)` and
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

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The time-scaled system `q' = v f(q, u)`, `(v, u) ∈ [c₁, c₂] × U`, has A–S's regularity
(10.2)–(10.4) when `f` has. -/
private theorem isC1On_timeScaled (hf : IsC1On f Ω U) (c₁ c₂ : ℝ) :
    IsC1On (fun y (p : ℝ × V) ↦ p.1 • f y p.2) Ω (Icc c₁ c₂ ×ˢ U) where
  continuousOn := by
    have h1 : ContinuousOn (fun p : E × (ℝ × V) ↦ f p.1 p.2.2) (Ω ×ˢ (Icc c₁ c₂ ×ˢ U)) :=
      hf.continuousOn.comp (continuous_fst.prodMk continuous_snd.snd).continuousOn
        fun p hp ↦ ⟨hp.1, hp.2.2⟩
    exact continuous_snd.fst.continuousOn.smul h1
  differentiableAt := fun x hx p hp ↦ (hf.differentiableAt x hx p.2 hp.2).const_smul p.1
  continuousOn_fderiv := by
    have h1 : ContinuousOn (fun p : E × (ℝ × V) ↦ fderiv ℝ (f · p.2.2) p.1)
        (Ω ×ˢ (Icc c₁ c₂ ×ˢ U)) :=
      hf.continuousOn_fderiv.comp (continuous_fst.prodMk continuous_snd.snd).continuousOn
        fun p hp ↦ ⟨hp.1, hp.2.2⟩
    refine (continuous_snd.fst.continuousOn.smul h1).congr fun p hp ↦ ?_
    exact fderiv_const_smul (hf.differentiableAt p.1 hp.1 p.2.2 hp.2.2) p.2.1

/-- **Agrachev–Sachkov, Theorem 12.2** (authors' draft, p. 173): let `ũ(·)` be an admissible
control for the control system (12.1) such that `q̃(t₁) ∈ ∂(⋃_{|t - t₁| < ε} A_{q₀}(t))` for some
`t₁ > 0` and `ε ∈ (0, t₁)`. Then there exists a Lipschitzian curve `λ_t ∈ T*_{q̃(t)}M`,
`λ_t ≠ 0`, `0 ≤ t ≤ t₁`, such that `λ̇_t = h⃗_{ũ(t)}(λ_t)`,
`h_{ũ(t)}(λ_t) = max_{u ∈ U} h_u(λ_t)` and `h_{ũ(t)}(λ_t) = 0` (12.15) for almost all
`t ∈ [0, t₁]`. (In coordinates on `Ω`, as in `theorem12_1`.)

Proof (A–S, pp. 173–174): the time-scaled system `q' = v f(q, u)`,
`(v, u) ∈ [1 - δ, 1 + δ] × U`, `δ = ε / (2 t₁)` (A–S: `|v - 1| < ε / t₁`, D4). By the change of
time (`ControlSystem.IsAdmissible.timeChangeOn`, D7) its attainable set at time `t₁` lies in
`⋃_{|t - t₁| < ε} A_{q₀}(t)`, and it contains `q̃(t₁)` (reference `(1, ũ)`), so `q̃(t₁)` is on its
boundary; Theorem 12.1 (`theorem12_1`) for it gives `λ_t` with
`v h_u(λ_t) ≤ h_{ũ(t)}(λ_t)` for `(v, u) ∈ [1 - δ, 1 + δ] × U`; `u = ũ(t)`, `v = 1 ± δ` give
`h_{ũ(t)}(λ_t) = 0`, and `v = 1` the maximality condition. The Hamiltonian systems of `(1, ũ)` and
of `ũ` coincide (the linearizations are equal). -/
theorem theorem12_2 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) {ε : ℝ} (hε : ε ∈ Ioo 0 t₁)
    (hbd : q t₁ ∈ frontier (⋃ t ∈ Ioo (t₁ - ε) (t₁ + ε), attainableSet f Ω U (q 0) t)) :
    ∃ p : ℝ → StrongDual ℝ E, (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, p t ≠ 0) ∧ IsAdjoint f 0 0 ũ q t₁ p ∧ IsMaximal f 0 0 U ũ q t₁ p ∧
      ∀ᵐ t ∂(volume.restrict (Icc 0 t₁)), controlHamiltonian f 0 0 (q t) (p t) (ũ t) = 0 := by
  obtain ⟨hε0, hεt⟩ := hε
  set δ : ℝ := ε / (2 * t₁) with hδ
  have hδ0 : 0 < δ := div_pos hε0 (by linarith)
  have hδt : δ * t₁ = ε / 2 := by rw [hδ]; field_simp
  have hδ1 : δ < 1 := by
    rw [hδ, div_lt_one (by linarith)]
    linarith
  have hc₁ : 0 < 1 - δ := by linarith
  have hŨ : IsCompact (Icc (1 - δ) (1 + δ) ×ˢ U) := isCompact_Icc.prod hU
  have hF := isC1On_timeScaled hf (1 - δ) (1 + δ)
  obtain ⟨⟨hũm, hũU, hqc, hqi, hqeq⟩, hqΩ⟩ := href
  have h1mem : (1 : ℝ) ∈ Icc (1 - δ) (1 + δ) := ⟨by linarith, by linarith⟩
  -- the reference pair `(1, ũ)` of the time-scaled system
  have hw : IsAdmissibleIn (fun y (p : ℝ × V) ↦ p.1 • f y p.2) Ω (Icc (1 - δ) (1 + δ) ×ˢ U)
      (q 0) t₁ (fun t ↦ ((1 : ℝ), ũ t)) q := by
    refine ⟨⟨measurable_const.prodMk hũm, fun t ht ↦ ⟨h1mem, hũU t ht⟩, hqc, ?_, ?_⟩, hqΩ⟩
    · simpa only [one_smul] using hqi
    · simpa only [one_smul] using hqeq
  -- its attainable set at time `t₁` lies in the union of the attainable sets near `t₁`
  have hsub : attainableSet (fun y (p : ℝ × V) ↦ p.1 • f y p.2) Ω (Icc (1 - δ) (1 + δ) ×ˢ U)
      (q 0) t₁ ⊆ ⋃ t ∈ Ioo (t₁ - ε) (t₁ + ε), attainableSet f Ω U (q 0) t := by
    rintro y ⟨w, x, ⟨hadm, hxΩ⟩, rfl⟩
    obtain ⟨θinv, -, -, hθmem, hθl, -, hadm', -⟩ :=
      IsAdmissible.timeChangeOn hU hf.continuousOn hc₁ ht₁.le hadm hxΩ
    have hv : Measurable fun r ↦ (w r).1 := measurable_fst.comp hadm.1
    have hb := TimeChange.mul_le_integral_sub ht₁.le hv hc₁ (fun r hr ↦ (hadm.2.1 r hr).1)
      ⟨le_rfl, ht₁.le⟩ ⟨ht₁.le, le_rfl⟩ ht₁.le
    rw [intervalIntegral.integral_same, sub_zero, sub_zero] at hb
    refine mem_iUnion₂.2 ⟨∫ r in (0 : ℝ)..t₁, (w r).1, ⟨?_, ?_⟩, fun s ↦ (w (θinv s)).2,
      fun s ↦ x (θinv s), ⟨hadm', fun s _ ↦ hxΩ _ (hθmem s)⟩, ?_⟩
    · nlinarith [hb.1]
    · nlinarith [hb.2]
    · simp only [hθl t₁ ⟨ht₁.le, le_rfl⟩]
  have hfr : q t₁ ∈ frontier (attainableSet (fun y (p : ℝ × V) ↦ p.1 • f y p.2) Ω
      (Icc (1 - δ) (1 + δ) ×ˢ U) (q 0) t₁) :=
    ⟨subset_closure ⟨_, q, hw, rfl⟩, fun hint ↦ hbd.2 (interior_mono hsub hint)⟩
  obtain ⟨p, hpL, hp0, hpadj, hpmax⟩ := theorem12_1 hΩ hŨ hF ht₁ hw hfr
  have hlin : ∀ r, linearization (fun y (p : ℝ × V) ↦ p.1 • f y p.2) (fun t ↦ ((1 : ℝ), ũ t))
      q r = linearization f ũ q r := fun r ↦ by
    simp only [linearization, one_smul]
  refine ⟨p, hpL, hp0, ?_, ?_, ?_⟩
  · simpa only [IsAdjoint, hlin, zero_smul, add_zero] using hpadj
  · filter_upwards [hpmax] with t ht u hu
    have := ht (1, u) ⟨h1mem, hu⟩
    simpa only [controlHamiltonian, one_smul, Pi.zero_apply, zero_mul, add_zero] using this
  · filter_upwards [hpmax, ae_restrict_mem measurableSet_Icc] with t ht htI
    have h1 := ht (1 + δ, ũ t) ⟨⟨by linarith, le_rfl⟩, hũU t htI⟩
    have h2 := ht (1 - δ, ũ t) ⟨⟨le_rfl, by linarith⟩, hũU t htI⟩
    simp only [controlHamiltonian, one_smul, map_smul, smul_eq_mul, Pi.zero_apply, zero_mul,
      add_zero] at h1 h2 ⊢
    nlinarith

end Pontryagin
