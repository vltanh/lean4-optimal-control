module

public import OptimalControl.MeasureTheory.MeasurableSelection
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Integral.IntervalAverage
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Control systems: compactness of attainable sets and existence of optimal controls (Filippov)

A *control system* `x' = F(x, u)`, `u ∈ U`, on a finite-dimensional real normed space `E`, with
controls in a metric space `V` (for instance `ℝᵐ`): `F : E → V → E` is jointly continuous and
`U ⊆ V` is compact. An *admissible pair* on `[0, T]` from `x₀` (`ControlSystem.IsAdmissible`) is a
measurable control `u` with values in `U` on `[0, T]` and a trajectory `x`, continuous on `[0, T]`,
with `x(t) = x₀ + ∫₀ᵗ F(x(s), u(s)) ds` (a Carathéodory solution). The *attainable* (reachable) sets
are `reachableSet F U x₀ T`, the endpoints `x(T)`, and `reachableSetLE F U x₀ T`, their union over
the times `τ ∈ [0, T]`.

**Filippov's theorem**: if the velocity sets `F(x, U)` are convex and the velocities are bounded
along admissible trajectories, the attainable sets are compact (`isCompact_reachableSet`,
`isCompact_reachableSetLE`). Applied to the system extended by a cost coordinate
(`ControlSystem.extend`), this gives the existence of optimal controls for integral costs
`∫ φ(x, u)` when the extended velocity sets `{(F(x, u), φ(x, u)) | u ∈ U}` are convex, for fixed
(`exists_optimal_fixedTime`) and free (`exists_optimal_freeTime`) terminal time.

The proof is the standard one (for the statement, see Agrachev–Sachkov, *Control Theory from the
Geometric Viewpoint*, Theorem 10.1):
1. along a sequence of admissible pairs with times `τₖ ∈ [0, T]`, the trajectories, frozen outside
   `[0, τₖ]` (`ControlSystem.freeze`), are equi-Lipschitz and bounded; by Tychonoff's theorem they
   have a pointwise cluster point `y` along a filter finer than `atTop`
   (`exists_isAdmissible_of_tendsto` takes such a filter);
2. `y` is Lipschitz, hence differentiable almost everywhere (Rademacher), and at a point of
   differentiability `t` its derivative lies in `F(y(t), U)`: the difference quotients of the
   approximating trajectories near `t` are averages of velocities in `F(B(y(t), δ), U)`, which lies
   in the closed convex set `cthickening ε (F(y(t), U))` for `δ` small (uniform continuity of `F`
   on `{y(t)} × U`, convexity of `F(y(t), U)`); see `hasDerivAt_mem_image_of_tendsto`;
3. a measurable control realizing these velocities exists by measurable selection
   (`MeasureTheory.exists_measurable_forall_mem_ae_eq_zero`, Filippov's lemma), and `y` is the
   integral of its derivative (`LipschitzWith.intervalIntegral_deriv_eq_sub`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal

/-! ### Fundamental theorem of calculus for Lipschitz curves -/

section LipschitzFTC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The derivative of a Lipschitz curve in a finite-dimensional space is interval integrable. -/
theorem LipschitzWith.intervalIntegrable_deriv {f : ℝ → E} {K : ℝ≥0} (hf : LipschitzWith K f)
    (a b : ℝ) : IntervalIntegrable (deriv f) volume a b := by
  refine (intervalIntegrable_const (c := (K : ℝ))).mono_fun
    (measurable_deriv f).aestronglyMeasurable (Eventually.of_forall fun s ↦ ?_)
  simpa using norm_deriv_le_of_lipschitz (x₀ := s) hf

/-- **Fundamental theorem of calculus** for Lipschitz curves in a finite-dimensional space:
`∫ s in a..b, f' s = f b - f a`. -/
theorem LipschitzWith.intervalIntegral_deriv_eq_sub {f : ℝ → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) : ∫ s in a..b, deriv f s = f b - f a := by
  have hint := hf.intervalIntegrable_deriv a b
  rw [← sub_eq_zero]
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ℓ ↦ ?_
  rw [map_sub, ← ContinuousLinearMap.intervalIntegral_comp_comm ℓ hint, map_sub]
  have hlip : LipschitzWith (‖ℓ‖₊ * K) (fun s ↦ ℓ (f s)) := ℓ.lipschitzWith.comp hf
  have hac := (hlip.lipschitzOnWith (s := uIcc a b)).absolutelyContinuousOnInterval
  rw [← hac.integral_deriv_eq_sub, sub_eq_zero]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hf.ae_differentiableAt_real] with s hs _
  exact ((ℓ.hasFDerivAt.comp_hasDerivAt s hs.hasDerivAt).deriv).symm

end LipschitzFTC

/-- The average over `[a, b]` of an integrable function with values in a closed convex set lies in
that set. -/
theorem smul_intervalIntegral_mem_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) {a b : ℝ}
    (hab : a < b) (hg : IntervalIntegrable g volume a b) (hgC : ∀ r ∈ Ioc a b, g r ∈ C) :
    (b - a)⁻¹ • ∫ r in a..b, g r ∈ C := by
  rw [← interval_average_eq, uIoc_of_le hab.le]
  refine hC.set_average_mem hCc ?_ ?_ ?_ ?_
  · simp [hab]
  · simp
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hgC)
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).1 hg

/-- A sequence in a compact set has a cluster point: it converges along a filter finer than
`atTop`. -/
theorem IsCompact.exists_neBot_le_atTop_tendsto {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {g : ℕ → X} (hg : ∀ k, g k ∈ K) :
    ∃ 𝒢 : Filter ℕ, 𝒢.NeBot ∧ 𝒢 ≤ atTop ∧ ∃ p ∈ K, Tendsto g 𝒢 (𝓝 p) := by
  obtain ⟨p, hpK, hp⟩ := hK (f := map g atTop) (tendsto_principal.2 (Eventually.of_forall hg))
  refine ⟨atTop ⊓ comap g (𝓝 p), ?_, inf_le_left, p, hpK, tendsto_comap.mono_left inf_le_right⟩
  refine NeBot.of_map (m := g) ?_
  rw [Filter.push_pull, inf_comm]
  exact hp

namespace ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace V]

/-- An admissible pair on `[0, T]` from `x₀` for the control system `x' = F(x, u)`, `u ∈ U`: a
measurable control `u` with values in `U` on `[0, T]` and a trajectory `x`, continuous on
`[0, T]`, with `t ↦ F(x(t), u(t))` integrable and `x(t) = x₀ + ∫₀ᵗ F(x(s), u(s)) ds` on
`[0, T]`. -/
def IsAdmissible (F : E → V → E) (U : Set V) (x₀ : E) (T : ℝ) (u : ℝ → V) (x : ℝ → E) : Prop :=
  Measurable u ∧ (∀ t ∈ Icc 0 T, u t ∈ U) ∧ ContinuousOn x (Icc 0 T) ∧
    IntervalIntegrable (fun s ↦ F (x s) (u s)) volume 0 T ∧
    ∀ t ∈ Icc 0 T, x t = x₀ + ∫ s in (0 : ℝ)..t, F (x s) (u s)

/-- The attainable set at time `T`: the endpoints `x(T)` of the admissible trajectories on
`[0, T]` from `x₀`. -/
def reachableSet (F : E → V → E) (U : Set V) (x₀ : E) (T : ℝ) : Set E :=
  {p | ∃ u x, IsAdmissible F U x₀ T u x ∧ x T = p}

/-- The attainable set for times at most `T`: the union of the `reachableSet F U x₀ τ`,
`τ ∈ [0, T]`. -/
def reachableSetLE (F : E → V → E) (U : Set V) (x₀ : E) (T : ℝ) : Set E :=
  ⋃ τ ∈ Icc 0 T, reachableSet F U x₀ τ

/-- A curve frozen outside `[0, τ]`: `freeze x τ t = x (max 0 (min t τ))`. -/
def freeze (x : ℝ → E) (τ : ℝ) : ℝ → E := fun t ↦ x (max 0 (min t τ))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem freeze_of_mem {x : ℝ → E} {τ t : ℝ} (ht : t ∈ Icc 0 τ) : freeze x τ t = x t := by
  simp [freeze, min_eq_left ht.2, max_eq_right ht.1]

theorem max_zero_min_mem {τ : ℝ} (hτ : 0 ≤ τ) (t : ℝ) : max 0 (min t τ) ∈ Icc 0 τ :=
  ⟨le_max_left _ _, max_le hτ (min_le_right _ _)⟩

theorem abs_max_zero_min_sub_le (τ s t : ℝ) :
    |max 0 (min s τ) - max 0 (min t τ)| ≤ |s - t| := by
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

section Basic

variable {F : E → V → E} {U : Set V} {x₀ : E} {T : ℝ} {u : ℝ → V} {x : ℝ → E}

theorem IsAdmissible.intervalIntegrable_of_mem (h : IsAdmissible F U x₀ T u x) {a b : ℝ}
    (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) :
    IntervalIntegrable (fun s ↦ F (x s) (u s)) volume a b :=
  h.2.2.2.1.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc ha) (Icc_subset_uIcc hb))

theorem IsAdmissible.apply_zero (h : IsAdmissible F U x₀ T u x) (hT : 0 ≤ T) : x 0 = x₀ := by
  simpa using h.2.2.2.2 0 ⟨le_rfl, hT⟩

theorem IsAdmissible.sub_eq_integral (h : IsAdmissible F U x₀ T u x) {a b : ℝ}
    (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) : x b - x a = ∫ s in a..b, F (x s) (u s) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ha.1.trans ha.2⟩
  rw [h.2.2.2.2 b hb, h.2.2.2.2 a ha, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (h.intervalIntegrable_of_mem h0 hb)
      (h.intervalIntegrable_of_mem h0 ha)]

/-- Trajectories with velocities bounded by `M` are `M`-Lipschitz. -/
theorem IsAdmissible.norm_sub_le (h : IsAdmissible F U x₀ T u x) {M : ℝ}
    (hM : ∀ s ∈ Icc 0 T, ‖F (x s) (u s)‖ ≤ M) {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) :
    ‖x b - x a‖ ≤ M * |b - a| := by
  rw [h.sub_eq_integral ha hb]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦
    hM s (uIcc_subset_Icc ha hb (uIoc_subset_uIcc hs))

/-- The frozen trajectory is `M`-Lipschitz. -/
theorem IsAdmissible.norm_freeze_sub_le (h : IsAdmissible F U x₀ T u x) (hT : 0 ≤ T) {M : ℝ}
    (hM : ∀ s ∈ Icc 0 T, ‖F (x s) (u s)‖ ≤ M) (s t : ℝ) :
    ‖freeze x T s - freeze x T t‖ ≤ M * |s - t| := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  exact (h.norm_sub_le hM (max_zero_min_mem hT t) (max_zero_min_mem hT s)).trans
    (mul_le_mul_of_nonneg_left (abs_max_zero_min_sub_le T s t) hM0)

/-- The frozen trajectory stays within `M * T` of `x₀`. -/
theorem IsAdmissible.norm_freeze_sub_le_mul (h : IsAdmissible F U x₀ T u x) (hT : 0 ≤ T)
    {M : ℝ} (hM : ∀ s ∈ Icc 0 T, ‖F (x s) (u s)‖ ≤ M) (t : ℝ) :
    ‖freeze x T t - x₀‖ ≤ M * T := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hc := max_zero_min_mem hT t
  have := h.norm_sub_le hM ⟨le_rfl, hT⟩ hc
  rw [h.apply_zero hT, sub_zero, abs_of_nonneg hc.1] at this
  exact this.trans (mul_le_mul_of_nonneg_left hc.2 hM0)

/-- Endpoints of trajectories with velocities bounded by `M` stay within `M * T` of `x₀`. -/
theorem IsAdmissible.norm_sub_le_mul (h : IsAdmissible F U x₀ T u x) (hT : 0 ≤ T)
    {M : ℝ} (hM : ∀ s ∈ Icc 0 T, ‖F (x s) (u s)‖ ≤ M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖x t - x₀‖ ≤ M * T := by
  have := h.norm_freeze_sub_le_mul hT hM t
  rwa [freeze_of_mem ht] at this

variable [TopologicalSpace V] [TopologicalSpace.PseudoMetrizableSpace V]
  [SecondCountableTopology V] [OpensMeasurableSpace V]

/-- For a continuous `G`, `s ↦ G(x(s), u(s))` is integrable along an admissible pair. -/
theorem IsAdmissible.intervalIntegrable_comp (h : IsAdmissible F U x₀ T u x) (hU : IsCompact U)
    (hT : 0 ≤ T) {W : Type*} [NormedAddCommGroup W] {G : E → V → W}
    (hG : Continuous fun p : E × V ↦ G p.1 p.2) :
    IntervalIntegrable (fun s ↦ G (x s) (u s)) volume 0 T := by
  have hK : IsCompact ((x '' Icc 0 T) ×ˢ U) :=
    (isCompact_Icc.image_of_continuousOn h.2.2.1).prod hU
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  refine Integrable.of_bound ?_ C ?_
  · exact hG.comp_aestronglyMeasurable
      ((h.2.2.1.aestronglyMeasurable measurableSet_Icc).prodMk h.1.aestronglyMeasurable)
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs ↦ ?_)
    exact hC (x s, u s) ⟨mem_image_of_mem _ hs, h.2.1 s hs⟩

end Basic

/-! ### Limits of admissible trajectories -/

section Closure

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace V] [BorelSpace V]
  {F : E → V → E} {U : Set V}

omit [MeasurableSpace E] [BorelSpace E] [BorelSpace V] in
/-- **Velocities of a limit trajectory** (the convex-hull argument): if trajectories with
velocities bounded by `M`, frozen outside `[0, τₖ]`, converge pointwise to `y` along a filter and
`τₖ → τ₀`, then at every `t ∈ (0, τ₀)` where `y` is differentiable its derivative lies in the
(convex) velocity set `F(y(t), U)`. -/
theorem hasDerivAt_mem_image_of_tendsto {ι : Type*} {𝒢 : Filter ι} [𝒢.NeBot]
    (hF : Continuous fun p : E × V ↦ F p.1 p.2) (hU : IsCompact U)
    (hconv : ∀ z, Convex ℝ (F z '' U)) {x₀ : E} {M : ℝ} (hM : 0 ≤ M) {τ : ι → ℝ}
    {u : ι → ℝ → V} {x : ι → ℝ → E} {τ₀ : ℝ} {y : ℝ → E}
    (hadm : ∀ k, IsAdmissible F U x₀ (τ k) (u k) (x k))
    (hbd : ∀ k, ∀ s ∈ Icc 0 (τ k), ‖F (x k s) (u k s)‖ ≤ M) (hτ₀ : Tendsto τ 𝒢 (𝓝 τ₀))
    (hy : ∀ t, Tendsto (fun k ↦ freeze (x k) (τ k) t) 𝒢 (𝓝 (y t))) {t : ℝ} (ht : t ∈ Ioo 0 τ₀)
    {v : E} (hv : HasDerivAt y v t) : v ∈ F (y t) '' U := by
  set C := F (y t) '' U with hC_def
  have hFt : Continuous (F (y t)) :=
    hF.comp (continuous_const.prodMk continuous_id :  Continuous fun w : V ↦ (y t, w))
  have hC : IsCompact C := hU.image hFt
  rw [← hC.isClosed.closure_eq, Metric.closure_eq_iInter_cthickening]
  simp only [mem_iInter]
  intro ε hε
  -- uniform continuity of `F` on `{y t} × U`
  have hev : ∀ᶠ z in 𝓝 (y t), ∀ w ∈ U, dist (F z w) (F (y t) w) < ε := by
    refine hU.eventually_forall_of_forall_eventually fun w₀ _ ↦ ?_
    have h1 : ∀ᶠ p : E × V in 𝓝 (y t, w₀), dist (F p.1 p.2) (F (y t) w₀) < ε / 2 :=
      Metric.tendsto_nhds.1 hF.continuousAt.tendsto _ (half_pos hε)
    have h2 : ∀ᶠ p : E × V in 𝓝 (y t, w₀), dist (F (y t) p.2) (F (y t) w₀) < ε / 2 :=
      Metric.tendsto_nhds.1 ((hFt.comp continuous_snd).tendsto (y t, w₀)) _ (half_pos hε)
    filter_upwards [h1, h2] with p hp1 hp2
    calc dist (F p.1 p.2) (F (y t) p.2)
        ≤ dist (F p.1 p.2) (F (y t) w₀) + dist (F (y t) p.2) (F (y t) w₀) :=
          dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hp1 hp2
      _ = ε := add_halves ε
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.1 hev
  have hslope : Tendsto (slope y t) (𝓝[>] t) (𝓝 v) :=
    (hasDerivAt_iff_tendsto_slope.1 hv).mono_left (nhdsWithin_mono _ fun s hs ↦ ne_of_gt hs)
  refine isClosed_cthickening.mem_of_tendsto hslope ?_
  set h₀ := min (τ₀ - t) (δ / (2 * (M + 1))) with hh₀_def
  have hh₀ : 0 < h₀ := lt_min (sub_pos.2 ht.2) (by positivity)
  have hh₀δ : M * h₀ < δ / 2 := by
    calc M * h₀ ≤ M * (δ / (2 * (M + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM
      _ < δ / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  filter_upwards [Ioo_mem_nhdsGT (show t < t + h₀ by linarith)] with s hs
  rw [slope_def_module]
  have hsτ : s < τ₀ := by linarith [hs.2, min_le_left (τ₀ - t) (δ / (2 * (M + 1)))]
  have hlim : Tendsto (fun k ↦ (s - t)⁻¹ • (freeze (x k) (τ k) s - freeze (x k) (τ k) t)) 𝒢
      (𝓝 ((s - t)⁻¹ • (y s - y t))) := ((hy s).sub (hy t)).const_smul _
  refine isClosed_cthickening.mem_of_tendsto hlim ?_
  have hτs : ∀ᶠ k in 𝒢, s < τ k := hτ₀.eventually_const_lt hsτ
  have hyt : ∀ᶠ k in 𝒢, dist (freeze (x k) (τ k) t) (y t) < δ / 2 :=
    Metric.tendsto_nhds.1 (hy t) _ (half_pos hδ)
  filter_upwards [hτs, hyt] with k hk hkt
  have ht' : t ∈ Icc 0 (τ k) := ⟨ht.1.le, by linarith [hs.1]⟩
  have hs' : s ∈ Icc 0 (τ k) := ⟨by linarith [ht.1, hs.1], hk.le⟩
  rw [freeze_of_mem ht'] at hkt
  rw [freeze_of_mem hs', freeze_of_mem ht', (hadm k).sub_eq_integral ht' hs']
  refine smul_intervalIntegral_mem_of_convex ((hconv (y t)).cthickening ε) isClosed_cthickening
    hs.1 ((hadm k).intervalIntegrable_of_mem ht' hs') fun r hr ↦ ?_
  have hr' : r ∈ Icc 0 (τ k) := ⟨by linarith [ht.1, hr.1], hr.2.trans hk.le⟩
  have hu : u k r ∈ U := (hadm k).2.1 r hr'
  refine Metric.mem_cthickening_of_dist_le _ (F (y t) (u k r)) ε C ⟨u k r, hu, rfl⟩ ?_
  refine (hδF ?_ (u k r) hu).le
  calc dist (x k r) (y t) ≤ dist (x k r) (x k t) + dist (x k t) (y t) := dist_triangle _ _ _
    _ ≤ M * |r - t| + dist (x k t) (y t) := by
        gcongr
        rw [dist_eq_norm]
        exact (hadm k).norm_sub_le (hbd k) ht' hr'
    _ ≤ M * h₀ + dist (x k t) (y t) := by
        gcongr
        rw [abs_of_nonneg (by linarith [hr.1])]
        linarith [hr.2, hs.2]
    _ < δ / 2 + δ / 2 := add_lt_add hh₀δ hkt
    _ = δ := add_halves δ

/-- **Closure of admissible trajectories** (Filippov): if trajectories with velocities bounded by
`M`, frozen outside `[0, τₖ]`, converge pointwise to `y` along a filter, and `τₖ → τ₀`, then `y`
is an admissible trajectory on `[0, τ₀]` for some control. -/
theorem exists_isAdmissible_of_tendsto {ι : Type*} {𝒢 : Filter ι} [𝒢.NeBot]
    (hF : Continuous fun p : E × V ↦ F p.1 p.2) (hU : IsCompact U)
    (hconv : ∀ z, Convex ℝ (F z '' U)) {x₀ : E} {M : ℝ} (hM : 0 ≤ M) {τ : ι → ℝ}
    {u : ι → ℝ → V} {x : ι → ℝ → E} {τ₀ : ℝ} {y : ℝ → E} (hτ : ∀ k, 0 ≤ τ k)
    (hadm : ∀ k, IsAdmissible F U x₀ (τ k) (u k) (x k))
    (hbd : ∀ k, ∀ s ∈ Icc 0 (τ k), ‖F (x k s) (u k s)‖ ≤ M) (hτ₀ : Tendsto τ 𝒢 (𝓝 τ₀))
    (hy : ∀ t, Tendsto (fun k ↦ freeze (x k) (τ k) t) 𝒢 (𝓝 (y t))) :
    ∃ v : ℝ → V, IsAdmissible F U x₀ τ₀ v y := by
  have hlip : LipschitzWith ⟨M, hM⟩ y := by
    refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    rw [dist_eq_norm, Real.dist_eq]
    exact le_of_tendsto ((hy s).sub (hy t)).norm
      (Eventually.of_forall fun k ↦ (hadm k).norm_freeze_sub_le (hτ k) (hbd k) s t)
  have hτ₀0 : 0 ≤ τ₀ := ge_of_tendsto hτ₀ (Eventually.of_forall hτ)
  have hy0 : y 0 = x₀ := by
    refine tendsto_nhds_unique (hy 0) (tendsto_const_nhds.congr fun k ↦ ?_)
    rw [freeze_of_mem ⟨le_rfl, hτ k⟩, (hadm k).apply_zero (hτ k)]
  obtain ⟨k₀⟩ := Filter.nonempty_of_neBot 𝒢
  have hUne : U.Nonempty := ⟨u k₀ 0, (hadm k₀).2.1 0 ⟨le_rfl, hτ k₀⟩⟩
  -- the derivative of `y` is almost everywhere a velocity
  have hae : ∀ᵐ s ∂(volume.restrict (Ioc 0 τ₀)), ∃ w ∈ U, F (y s) w - deriv y s = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hlip.ae_differentiableAt_real, (countable_singleton τ₀).ae_notMem volume]
      with s hd hne hs
    have hs' : s ∈ Ioo 0 τ₀ := ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩
    obtain ⟨w, hw, hFw⟩ := hasDerivAt_mem_image_of_tendsto hF hU hconv hM hadm hbd hτ₀ hy hs'
      hd.hasDerivAt
    exact ⟨w, hw, by rw [hFw, sub_self]⟩
  -- measurable selection of a control
  obtain ⟨σ, hσm, hσU, hσ⟩ := MeasureTheory.exists_measurable_forall_mem_ae_eq_zero
    (μ := volume.restrict (Ioc 0 τ₀)) (g := fun s w ↦ F (y s) w - deriv y s) hU hUne
    (fun w _ ↦ ((hF.comp (hlip.continuous.prodMk continuous_const :
      Continuous fun s ↦ (y s, w))).measurable).sub (measurable_deriv y))
    (fun s ↦ ((hF.comp (continuous_const.prodMk continuous_id :
      Continuous fun w : V ↦ (y s, w))).sub continuous_const).continuousOn) hae
  have hσ' : ∀ᵐ s ∂volume, s ∈ Ioc 0 τ₀ → F (y s) (σ s) = deriv y s := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hσ] with s hs hs'
    exact sub_eq_zero.1 (hs hs')
  refine ⟨σ, hσm, fun s _ ↦ hσU s, hlip.continuous.continuousOn, ?_, fun t ht ↦ ?_⟩
  · refine (hlip.intervalIntegrable_deriv 0 τ₀).congr_ae ?_
    rw [uIoc_of_le hτ₀0, EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hσ'] with s hs hs'
    exact (hs hs').symm
  · rw [intervalIntegral.integral_congr_ae (g := deriv y) ?_,
      hlip.intervalIntegral_deriv_eq_sub, hy0, add_sub_cancel]
    rw [uIoc_of_le ht.1]
    filter_upwards [hσ'] with s hs hs'
    exact hs ⟨hs'.1, hs'.2.trans ht.2⟩

/-- **Closedness of the attainable sets** (Filippov): if `pₖ = xₖ(τₖ)` are endpoints of admissible
trajectories with times `τₖ ∈ [0, T]` and velocities bounded by `M`, and `pₖ → p`, then `p` is
attained at a cluster point `τ₀ ∈ [0, T]` of the times (`τ₀ = c` if all `τₖ = c`). -/
theorem exists_mem_reachableSet_of_tendsto (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hU : IsCompact U) (hconv : ∀ z, Convex ℝ (F z '' U)) {x₀ : E} {T M : ℝ} (hM : 0 ≤ M)
    {τ : ℕ → ℝ} (hτ : ∀ k, τ k ∈ Icc 0 T) {u : ℕ → ℝ → V} {x : ℕ → ℝ → E}
    (hadm : ∀ k, IsAdmissible F U x₀ (τ k) (u k) (x k))
    (hbd : ∀ k, ∀ s ∈ Icc 0 (τ k), ‖F (x k s) (u k s)‖ ≤ M) {p : E}
    (hp : Tendsto (fun k ↦ x k (τ k)) atTop (𝓝 p)) :
    ∃ τ₀ ∈ Icc 0 T, (∀ c, (∀ k, τ k = c) → τ₀ = c) ∧ p ∈ reachableSet F U x₀ τ₀ := by
  set K : Set ((ℝ → E) × ℝ) := (univ.pi fun _ ↦ closedBall x₀ (M * T)) ×ˢ Icc 0 T
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ ↦ isCompact_closedBall _ _).prod isCompact_Icc
  have hg : ∀ k, (freeze (x k) (τ k), τ k) ∈ K := by
    intro k
    refine ⟨fun t _ ↦ ?_, hτ k⟩
    rw [mem_closedBall, dist_eq_norm]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hbd k 0 ⟨le_rfl, (hτ k).1⟩)
    exact ((hadm k).norm_freeze_sub_le_mul (hτ k).1 (hbd k) t).trans
      (mul_le_mul_of_nonneg_left (hτ k).2 hM0)
  obtain ⟨𝒢, h𝒢, h𝒢le, ⟨y, τ₀⟩, ⟨-, hτ₀T⟩, hlim⟩ := hK.exists_neBot_le_atTop_tendsto hg
  have hτlim : Tendsto τ 𝒢 (𝓝 τ₀) := (continuous_snd.tendsto _).comp hlim
  have hylim : ∀ t, Tendsto (fun k ↦ freeze (x k) (τ k) t) 𝒢 (𝓝 (y t)) :=
    tendsto_pi_nhds.1 ((continuous_fst.tendsto _).comp hlim)
  obtain ⟨v, hv⟩ := exists_isAdmissible_of_tendsto hF hU hconv hM (fun k ↦ (hτ k).1) hadm hbd
    hτlim hylim
  refine ⟨τ₀, hτ₀T, fun c hc ↦ ?_, v, y, hv, ?_⟩
  · have : τ = fun _ ↦ c := funext hc
    rw [this] at hτlim
    exact tendsto_nhds_unique hτlim tendsto_const_nhds
  · have h1 : Tendsto (fun k ↦ freeze (x k) (τ k) (τ k)) 𝒢 (𝓝 p) := by
      refine (hp.mono_left h𝒢le).congr fun k ↦ ?_
      rw [freeze_of_mem ⟨(hτ k).1, le_rfl⟩]
    have h2 : Tendsto (fun k ↦ freeze (x k) (τ k) τ₀) 𝒢 (𝓝 p) := by
      refine h1.congr_dist (squeeze_zero (g := fun k ↦ M * |τ k - τ₀|) (fun _ ↦ dist_nonneg)
        (fun k ↦ ?_) ?_)
      · rw [dist_eq_norm]
        exact (hadm k).norm_freeze_sub_le (hτ k).1 (hbd k) (τ k) τ₀
      · have : Tendsto (fun k ↦ M * |τ k - τ₀|) 𝒢 (𝓝 (M * |τ₀ - τ₀|)) :=
          ((hτlim.sub_const τ₀).abs).const_mul M
        simpa using this
    exact tendsto_nhds_unique (hylim τ₀) h2

/-- **Filippov's theorem**, free terminal time: if the velocity sets are convex and the velocities
along admissible trajectories with times in `[0, T]` are bounded by `M`, the attainable set for
times at most `T` is compact. -/
theorem isCompact_reachableSetLE (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hU : IsCompact U) (hconv : ∀ z, Convex ℝ (F z '' U)) {x₀ : E} {T M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ τ ∈ Icc 0 T, ∀ u x, IsAdmissible F U x₀ τ u x → ∀ s ∈ Icc 0 τ, ‖F (x s) (u s)‖ ≤ M) :
    IsCompact (reachableSetLE F U x₀ T) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_of_closure_subset fun p hp ↦ ?_)
    (isBounded_closedBall (x := x₀) (r := M * T) |>.subset ?_)
  · obtain ⟨q, hqA, hq⟩ := mem_closure_iff_seq_limit.1 hp
    simp only [reachableSetLE, reachableSet, mem_iUnion, mem_ofPred_eq, exists_prop] at hqA
    choose τ hτ u x hadm hxq using hqA
    obtain ⟨τ₀, hτ₀, -, hpτ₀⟩ := exists_mem_reachableSet_of_tendsto hF hU hconv hM hτ hadm
      (fun k ↦ hbd _ (hτ k) _ _ (hadm k)) (by simpa [hxq] using hq)
    exact mem_biUnion hτ₀ hpτ₀
  · intro p hp
    simp only [reachableSetLE, reachableSet, mem_iUnion, mem_ofPred_eq, exists_prop] at hp
    obtain ⟨τ, hτ, u, x, hadm, rfl⟩ := hp
    rw [mem_closedBall, dist_eq_norm]
    exact ((hadm.norm_sub_le_mul hτ.1 (hbd τ hτ u x hadm) ⟨hτ.1, le_rfl⟩)).trans
      (mul_le_mul_of_nonneg_left hτ.2 hM)

/-- **Filippov's theorem**, fixed terminal time: if the velocity sets are convex and the velocities
along admissible trajectories on `[0, T]` are bounded by `M`, the attainable set at time `T` is
compact. -/
theorem isCompact_reachableSet (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hU : IsCompact U) (hconv : ∀ z, Convex ℝ (F z '' U)) {x₀ : E} {T M : ℝ} (hT : 0 ≤ T)
    (hM : 0 ≤ M)
    (hbd : ∀ u x, IsAdmissible F U x₀ T u x → ∀ s ∈ Icc 0 T, ‖F (x s) (u s)‖ ≤ M) :
    IsCompact (reachableSet F U x₀ T) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_of_closure_subset fun p hp ↦ ?_)
    (isBounded_closedBall (x := x₀) (r := M * T) |>.subset ?_)
  · obtain ⟨q, hqA, hq⟩ := mem_closure_iff_seq_limit.1 hp
    simp only [reachableSet, mem_ofPred_eq] at hqA
    choose u x hadm hxq using hqA
    obtain ⟨τ₀, -, hτ₀, hpτ₀⟩ := exists_mem_reachableSet_of_tendsto (τ := fun _ ↦ T) hF hU hconv
      hM (fun _ ↦ ⟨hT, le_rfl⟩) hadm (fun k ↦ hbd _ _ (hadm k)) (by simpa [hxq] using hq)
    rwa [hτ₀ T fun _ ↦ rfl] at hpτ₀
  · rintro p ⟨u, x, hadm, rfl⟩
    rw [mem_closedBall, dist_eq_norm]
    exact hadm.norm_sub_le_mul hT (hbd u x hadm) ⟨hT, le_rfl⟩

end Closure

/-! ### Integral costs: the extended system -/

section Cost

/-- The control system extended by the cost coordinate: `(x, c)' = (F(x, u), φ(x, u))`. -/
def extend (F : E → V → E) (φ : E → V → ℝ) : E × ℝ → V → E × ℝ := fun z w ↦ (F z.1 w, φ z.1 w)

variable [CompleteSpace E] {F : E → V → E} {φ : E → V → ℝ} {U : Set V} {x₀ : E} {T : ℝ}

/-- The first component of an admissible pair of the extended system is admissible, and the second
is the accumulated cost. -/
theorem IsAdmissible.of_extend {c₀ : ℝ} {u : ℝ → V} {z : ℝ → E × ℝ}
    (h : IsAdmissible (extend F φ) U (x₀, c₀) T u z) :
    IsAdmissible F U x₀ T u (fun t ↦ (z t).1) ∧
      ∀ t ∈ Icc 0 T, (z t).2 = c₀ + ∫ s in (0 : ℝ)..t, φ (z s).1 (u s) := by
  have hT : ∀ t ∈ Icc 0 T, IntervalIntegrable (fun s ↦ extend F φ (z s) (u s)) volume 0 t :=
    fun t ht ↦ h.intervalIntegrable_of_mem ⟨le_rfl, ht.1.trans ht.2⟩ ht
  have hint : IntervalIntegrable (fun s ↦ extend F φ (z s) (u s)) volume 0 T := h.2.2.2.1
  refine ⟨⟨h.1, h.2.1, continuous_fst.comp_continuousOn h.2.2.1,
    ⟨(ContinuousLinearMap.fst ℝ E ℝ).integrable_comp hint.1,
      (ContinuousLinearMap.fst ℝ E ℝ).integrable_comp hint.2⟩, fun t ht ↦ ?_⟩, fun t ht ↦ ?_⟩
  · have := congrArg Prod.fst (h.2.2.2.2 t ht)
    change (z t).1 = x₀ + ∫ s in (0 : ℝ)..t, F (z s).1 (u s)
    rw [this, Prod.fst_add]
    congr 1
    exact ((ContinuousLinearMap.fst ℝ E ℝ).intervalIntegral_comp_comm (hT t ht)).symm
  · have := congrArg Prod.snd (h.2.2.2.2 t ht)
    rw [this, Prod.snd_add]
    congr 1
    exact ((ContinuousLinearMap.snd ℝ E ℝ).intervalIntegral_comp_comm (hT t ht)).symm

variable [MetricSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- An admissible pair, with its accumulated cost, is an admissible pair of the extended
system. -/
theorem IsAdmissible.extend {u : ℝ → V} {x : ℝ → E} (h : IsAdmissible F U x₀ T u x)
    (hU : IsCompact U) (hT : 0 ≤ T) (hφ : Continuous fun p : E × V ↦ φ p.1 p.2) :
    IsAdmissible (extend F φ) U (x₀, 0) T u (fun t ↦ (x t, ∫ s in (0 : ℝ)..t, φ (x s) (u s))) := by
  have hφi := h.intervalIntegrable_comp hU hT hφ
  have hFi := h.2.2.2.1
  have hpair : IntervalIntegrable (fun s ↦ ControlSystem.extend F φ
      (x s, ∫ r in (0 : ℝ)..s, φ (x r) (u r)) (u s)) volume 0 T :=
    ⟨hFi.1.prodMk hφi.1, hFi.2.prodMk hφi.2⟩
  refine ⟨h.1, h.2.1, h.2.2.1.prodMk ?_, hpair, fun t ht ↦ ?_⟩
  · have := intervalIntegral.continuousOn_primitive_interval' hφi (left_mem_uIcc (a := 0) (b := T))
    rwa [uIcc_of_le hT] at this
  · have hpt := hpair.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ht))
    refine Prod.ext ?_ ?_
    · have := (ContinuousLinearMap.fst ℝ E ℝ).intervalIntegral_comp_comm hpt
      simp only [ContinuousLinearMap.coe_fst'] at this
      rw [Prod.fst_add, ← this]
      exact h.2.2.2.2 t ht
    · have := (ContinuousLinearMap.snd ℝ E ℝ).intervalIntegral_comp_comm hpt
      simp only [ContinuousLinearMap.coe_snd'] at this
      rw [Prod.snd_add, ← this, zero_add]
      rfl

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace V] [SecondCountableTopology V] [MeasurableSpace E] [BorelSpace E] in
/-- Velocities of the extended system are bounded along its admissible trajectories from
`(x₀, 0)` with times in `[0, T]`, if those of `F` are bounded on `E × U`. -/
theorem exists_bound_extend (hU : IsCompact U) (hφ : Continuous fun p : E × V ↦ φ p.1 p.2)
    {M : ℝ} (hFM : ∀ z, ∀ w ∈ U, ‖F z w‖ ≤ M) (hM : 0 ≤ M) (T : ℝ) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ τ ∈ Icc 0 T, ∀ u z, IsAdmissible (extend F φ) U (x₀, 0) τ u z →
      ∀ s ∈ Icc 0 τ, ‖extend F φ (z s) (u s)‖ ≤ M' := by
  obtain ⟨Mφ, hMφ⟩ := ((isCompact_closedBall x₀ (M * T)).prod hU).exists_bound_of_continuousOn
    hφ.continuousOn
  refine ⟨max M Mφ, hM.trans (le_max_left _ _), fun τ hτ u z hz s hs ↦ ?_⟩
  have hz1 := hz.of_extend.1
  have hw : u s ∈ U := hz.2.1 s hs
  refine norm_prod_le_iff.2 ⟨(hFM _ _ hw).trans (le_max_left _ _), ?_⟩
  refine (hMφ ((z s).1, u s) ⟨?_, hw⟩).trans (le_max_right _ _)
  rw [mem_closedBall, dist_eq_norm]
  exact (hz1.norm_sub_le_mul hτ.1 (fun r hr ↦ hFM _ _ (hz1.2.1 r hr)) hs).trans
    (mul_le_mul_of_nonneg_left hτ.2 hM)

omit [NormedSpace ℝ E] [MeasurableSpace V] [CompleteSpace E] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The extended system is continuous. -/
theorem continuous_extend (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hφ : Continuous fun p : E × V ↦ φ p.1 p.2) :
    Continuous fun p : (E × ℝ) × V ↦ extend F φ p.1 p.2 :=
  (hF.comp (continuous_fst.fst.prodMk continuous_snd)).prodMk
    (hφ.comp (continuous_fst.fst.prodMk continuous_snd))

/-- **Existence of optimal controls**, fixed terminal time: for a control system with bounded
velocities and a continuous running cost `φ` whose extended velocity sets
`{(F(x, u), φ(x, u)) | u ∈ U}` are convex, among the admissible pairs on `[0, T]` from `x₀` to an
attainable `x₁`, one has the least cost `∫₀ᵀ φ(x, u)`. -/
theorem exists_optimal_fixedTime (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hU : IsCompact U) (hφ : Continuous fun p : E × V ↦ φ p.1 p.2)
    (hconv : ∀ z, Convex ℝ ((fun w ↦ (F z w, φ z w)) '' U)) {M : ℝ}
    (hFM : ∀ z, ∀ w ∈ U, ‖F z w‖ ≤ M) (hT : 0 ≤ T) {x₁ : E}
    (h₁ : x₁ ∈ reachableSet F U x₀ T) :
    ∃ u x, IsAdmissible F U x₀ T u x ∧ x T = x₁ ∧
      ∀ u' x', IsAdmissible F U x₀ T u' x' → x' T = x₁ →
        ∫ t in (0 : ℝ)..T, φ (x t) (u t) ≤ ∫ t in (0 : ℝ)..T, φ (x' t) (u' t) := by
  obtain ⟨u₁, y₁, hy₁, rfl⟩ := h₁
  have hM : 0 ≤ M := (norm_nonneg _).trans (hFM (y₁ 0) (u₁ 0) (hy₁.2.1 0 ⟨le_rfl, hT⟩))
  obtain ⟨M', hM', hbd⟩ := exists_bound_extend (x₀ := x₀) hU hφ hFM hM T
  set A := reachableSet (extend F φ) U (x₀, 0) T
  have hA : IsCompact A := isCompact_reachableSet (continuous_extend hF hφ) hU
    (fun z ↦ hconv z.1) hT hM' (fun u z hz ↦ hbd T ⟨hT, le_rfl⟩ u z hz)
  set S := {c : ℝ | (y₁ T, c) ∈ A}
  have hS : IsCompact S :=
    (hA.image continuous_snd).of_isClosed_subset
      (hA.isClosed.preimage (continuous_const.prodMk continuous_id))
      (fun c hc ↦ ⟨(y₁ T, c), hc, rfl⟩)
  have hSne : S.Nonempty := ⟨_, _, _, hy₁.extend hU hT hφ, rfl⟩
  obtain ⟨c, ⟨u, z, hz, hzT⟩, hc⟩ := hS.exists_isLeast hSne
  obtain ⟨hz1, hz2⟩ := hz.of_extend
  refine ⟨u, fun t ↦ (z t).1, hz1, congrArg Prod.fst hzT, fun u' x' h' hx' ↦ ?_⟩
  have hcost : ∫ t in (0 : ℝ)..T, φ (z t).1 (u t) = c := by
    have := hz2 T ⟨hT, le_rfl⟩
    rw [hzT, zero_add] at this
    exact this.symm
  rw [hcost]
  exact hc ⟨u', _, h'.extend hU hT hφ, by rw [hx']⟩

/-- **Existence of optimal controls**, free terminal time: for a control system with bounded
velocities and a continuous running cost `φ` whose extended velocity sets
`{(F(x, u), φ(x, u)) | u ∈ U}` are convex, among the admissible pairs from `x₀` to `x₁` on
`[0, τ]` with `τ ∈ [0, T]` (if any), one has the least cost `∫₀^τ φ(x, u)`. -/
theorem exists_optimal_freeTime (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hU : IsCompact U) (hφ : Continuous fun p : E × V ↦ φ p.1 p.2)
    (hconv : ∀ z, Convex ℝ ((fun w ↦ (F z w, φ z w)) '' U)) {M : ℝ}
    (hFM : ∀ z, ∀ w ∈ U, ‖F z w‖ ≤ M) {x₁ : E} (h₁ : x₁ ∈ reachableSetLE F U x₀ T) :
    ∃ τ ∈ Icc 0 T, ∃ u x, IsAdmissible F U x₀ τ u x ∧ x τ = x₁ ∧
      ∀ τ' ∈ Icc 0 T, ∀ u' x', IsAdmissible F U x₀ τ' u' x' → x' τ' = x₁ →
        ∫ t in (0 : ℝ)..τ, φ (x t) (u t) ≤ ∫ t in (0 : ℝ)..τ', φ (x' t) (u' t) := by
  simp only [reachableSetLE, reachableSet, mem_iUnion, mem_ofPred_eq, exists_prop] at h₁
  obtain ⟨τ₁, hτ₁, u₁, y₁, hy₁, rfl⟩ := h₁
  have hM : 0 ≤ M := (norm_nonneg _).trans (hFM (y₁ 0) (u₁ 0) (hy₁.2.1 0 ⟨le_rfl, hτ₁.1⟩))
  obtain ⟨M', hM', hbd⟩ := exists_bound_extend (x₀ := x₀) hU hφ hFM hM T
  set A := reachableSetLE (extend F φ) U (x₀, 0) T
  have hA : IsCompact A := isCompact_reachableSetLE (continuous_extend hF hφ) hU
    (fun z ↦ hconv z.1) hM' hbd
  set S := {c : ℝ | (y₁ τ₁, c) ∈ A}
  have hS : IsCompact S :=
    (hA.image continuous_snd).of_isClosed_subset
      (hA.isClosed.preimage (continuous_const.prodMk continuous_id))
      (fun c hc ↦ ⟨(y₁ τ₁, c), hc, rfl⟩)
  have hSne : S.Nonempty := ⟨_, mem_biUnion hτ₁ ⟨_, _, hy₁.extend hU hτ₁.1 hφ, rfl⟩⟩
  obtain ⟨c, hcS, hc⟩ := hS.exists_isLeast hSne
  simp only [S, A, reachableSetLE, reachableSet, mem_iUnion, mem_ofPred_eq, exists_prop]
    at hcS
  obtain ⟨τ, hτ, u, z, hz, hzT⟩ := hcS
  obtain ⟨hz1, hz2⟩ := hz.of_extend
  refine ⟨τ, hτ, u, fun t ↦ (z t).1, hz1, congrArg Prod.fst hzT, fun τ' hτ' u' x' h' hx' ↦ ?_⟩
  have hcost : ∫ t in (0 : ℝ)..τ, φ (z t).1 (u t) = c := by
    have := hz2 τ ⟨hτ.1, le_rfl⟩
    rw [hzT, zero_add] at this
    exact this.symm
  rw [hcost]
  exact hc (mem_biUnion hτ' ⟨u', _, h'.extend hU hτ'.1 hφ, by rw [hx']⟩)

end Cost

end ControlSystem
