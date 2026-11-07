module

public import OptimalControl.ODE.ControlSystem

-- Imported directly by the library root `OptimalControl.lean`, so Mathlib's header linter would ask
-- for a copyright header, which the library's modules do not carry.
set_option linter.style.header false

/-!
# Filippov's theorem with a state constraint, a set of initial points and an endpoint relation

Filippov's theorem (`ControlSystem.isCompact_reachableSet`,
`ControlSystem.isCompact_reachableSetLE`) and the existence of optimal controls
(`ControlSystem.exists_optimal_fixedTime`, `ControlSystem.exists_optimal_freeTime`) in
`OptimalControl.ODE.ControlSystem` fix the initial point, ask the velocities to be bounded on
the whole space and the dynamics to be continuous everywhere. Many problems are posed only on part
of the space, with initial and terminal points tied by a relation. This module proves the same
results for

* a *closed state constraint* `S`: the trajectories stay in `S` on `[0, τ]`, and the dynamics `F`
  and the running cost `φ` need only be continuous on `S × U`, the velocities bounded on `S × U`,
  and the velocity sets convex at the points of `S`;
* a *compact set* `K₀` of initial points;
* a *closed endpoint relation* `N ⊆ E × E`: `(x(0), x(τ)) ∈ N`;
* a *time window* `[T₀, T₁]`, `0 ≤ T₀ ≤ T₁`, for the terminal time `τ`: fixed time when
  `T₀ = T₁`, free time otherwise.

The admissible pairs are those of `ControlSystem.IsAdmissible`, from their own initial point
`x(0)`.

## Main results

* `ControlSystem.isCompact_constrainedEndpoints` (Filippov's theorem): if the velocity sets
  `F(x, U)`, `x ∈ S`, are convex, the set of pairs `(x(0), x(τ))` of the trajectories in `S` from
  `K₀` with `τ ∈ [T₀, T₁]` is compact;
* `ControlSystem.exists_optimal_constrained` (existence of optimal controls): if moreover the
  velocity sets extended by the cost, `{(F(x, u), φ(x, u)) | u ∈ U}`, are convex at the points of
  `S`, and some trajectory in `S` from `K₀` satisfies the endpoint relation with a time in
  `[T₀, T₁]`, then among all such trajectories one has the least cost `∫₀^τ φ(x, u)`.

## Proof

The proof is the one of `OptimalControl.ODE.ControlSystem`, with three additions.

1. *Bounds.* A trajectory in `S` from `x(0) ∈ K₀` with `τ ≤ T₁` has velocities bounded by `M`, so
   it stays in the compact set `cthickening (M T₁) K₀`; its endpoint pairs lie in the compact set
   `K₀ × cthickening (M T₁) K₀`, and it suffices to show that they form a closed set.
2. *Limits.* Along a sequence of admissible pairs whose endpoint pairs converge, the frozen
   trajectories (`ControlSystem.freeze`) are equi-Lipschitz with values in
   `cthickening (M T₁) K₀`, and the times lie in `[T₀, T₁]`; by Tychonoff's theorem they have a
   pointwise cluster point `(y, τ₀)` along a filter finer than `atTop`
   (`IsCompact.exists_neBot_le_atTop_tendsto`). The limit `y` takes its values in `S` (`S` is
   closed and the frozen trajectories take their values in `S`), `y(0) ∈ K₀` (`K₀` is closed),
   and the endpoint pairs converge to `(y(0), y(τ₀))` (the frozen trajectories converge at the
   times `τₖ → τ₀` by equicontinuity).
3. *Closure.* `y` is an admissible trajectory from `y(0)`: the convex-hull argument of
   `ControlSystem.hasDerivAt_mem_image_of_tendsto` and the measurable selection of
   `ControlSystem.exists_isAdmissible_of_tendsto` use `F` only near the points `(y(t), u)`,
   `u ∈ U`, of `S × U`, approached by points `(xₖ(r), u)` of `S × U`. Continuity of `F` on `S × U`
   (uniform on `{y(t)} × U` within `S × U`, by compactness of `U`) and convexity of `F(y(t), U)`
   at the points `y(t) ∈ S` suffice; the private lemmas `hasDerivAt_mem_image_of_tendsto_of_mem`
   and `exists_isAdmissible_of_tendsto_of_mem` are those two results with `F` continuous on
   `S × U` only, trajectories confined to `S` and initial points that vary along the sequence.

For the existence of optimal controls, the same applies to the system extended by the cost,
`ControlSystem.extend F φ`, with the state constraint `S' × ℝ`, `S' = S ∩ cthickening (M T₁) K₀`,
and the initial set `K₀ × {0}`: on the compact set `S' × U` the running cost `φ` is bounded, so the
extended velocities are bounded, and every trajectory in `S` from `K₀` with `τ ≤ T₁` stays in
`S'`. The endpoint pairs of the extended system form a compact set, those satisfying the endpoint
relation a compact subset, and their costs a compact set of reals, whose least element is the
cost of an optimal pair (`ControlSystem.IsAdmissible.of_extend`). The cost `φ(x, u)` along an
admissible pair in `S` is integrable since `φ` is continuous on `S × U`, so that every
competitor lifts to the extended system.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace V]

/-- The endpoint pairs of the constrained problem: the pairs `(x(0), x(τ))` of the admissible pairs
`(u, x)` on `[0, τ]` with `τ ∈ [T₀, T₁]`, initial point `x(0) ∈ K₀` and trajectory in `S` on
`[0, τ]`. -/
def constrainedEndpoints (F : E → V → E) (U : Set V) (S K₀ : Set E) (T₀ T₁ : ℝ) : Set (E × E) :=
  {p | ∃ τ ∈ Icc T₀ T₁, ∃ u x, IsAdmissible F U (x 0) τ u x ∧ x 0 ∈ K₀ ∧
    (∀ t ∈ Icc 0 τ, x t ∈ S) ∧ (x 0, x τ) = p}

/-! ### Limits of trajectories in a closed set -/

section Closure

variable [FiniteDimensional ℝ E] [MetricSpace V] {F : E → V → E} {U : Set V} {S : Set E}

/-- **Velocities of a limit trajectory in a closed set** (the convex-hull argument of
`ControlSystem.hasDerivAt_mem_image_of_tendsto`, with `F` continuous on `S × U` only): if
trajectories in `S`, with velocities bounded by `M`, frozen outside `[0, τₖ]`, converge pointwise
to `y` along a filter and `τₖ → τ₀`, then at every `t ∈ (0, τ₀)` with `y(t) ∈ S` where `y` is
differentiable, its derivative lies in the (convex) velocity set `F(y(t), U)`. The initial points
may vary along the filter. -/
private theorem hasDerivAt_mem_image_of_tendsto_of_mem {ι : Type*} {𝒢 : Filter ι} [𝒢.NeBot]
    (hF : ContinuousOn (fun p : E × V ↦ F p.1 p.2) (S ×ˢ U)) (hU : IsCompact U)
    (hconv : ∀ z ∈ S, Convex ℝ (F z '' U)) {M : ℝ} (hM : 0 ≤ M) {x₀ : ι → E} {τ : ι → ℝ}
    {u : ι → ℝ → V} {x : ι → ℝ → E} {τ₀ : ℝ} {y : ℝ → E}
    (hadm : ∀ k, IsAdmissible F U (x₀ k) (τ k) (u k) (x k))
    (hxS : ∀ k, ∀ s ∈ Icc 0 (τ k), x k s ∈ S)
    (hbd : ∀ k, ∀ s ∈ Icc 0 (τ k), ‖F (x k s) (u k s)‖ ≤ M) (hτ₀ : Tendsto τ 𝒢 (𝓝 τ₀))
    (hy : ∀ t, Tendsto (fun k ↦ freeze (x k) (τ k) t) 𝒢 (𝓝 (y t))) {t : ℝ} (ht : t ∈ Ioo 0 τ₀)
    (hyt : y t ∈ S) {v : E} (hv : HasDerivAt y v t) : v ∈ F (y t) '' U := by
  set C := F (y t) '' U with hC_def
  have hFt : ContinuousOn (F (y t)) U :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn fun w hw ↦ ⟨hyt, hw⟩
  have hC : IsCompact C := hU.image_of_continuousOn hFt
  rw [← hC.isClosed.closure_eq, Metric.closure_eq_iInter_cthickening]
  simp only [mem_iInter]
  intro ε hε
  -- uniform continuity of `F` on `{y t} × U`, within `S × U`
  have hev : ∀ᶠ z in 𝓝 (y t), ∀ w ∈ U, w ∈ U → z ∈ S → dist (F z w) (F (y t) w) < ε := by
    refine hU.eventually_forall_of_forall_eventually
      (P := fun z w ↦ w ∈ U → z ∈ S → dist (F z w) (F (y t) w) < ε) fun w₀ hw₀ ↦ ?_
    have hmem : (y t, w₀) ∈ S ×ˢ U := ⟨hyt, hw₀⟩
    have h1 : ∀ᶠ p : E × V in 𝓝[S ×ˢ U] (y t, w₀), dist (F p.1 p.2) (F (y t) w₀) < ε / 2 :=
      Metric.tendsto_nhds.1 (hF _ hmem).tendsto _ (half_pos hε)
    have h2 : ∀ᶠ p : E × V in 𝓝[S ×ˢ U] (y t, w₀), dist (F (y t) p.2) (F (y t) w₀) < ε / 2 :=
      Metric.tendsto_nhds.1 ((hFt w₀ hw₀).tendsto.comp
        (continuous_snd.continuousWithinAt.tendsto_nhdsWithin
          fun (p : E × V) (hp : p ∈ S ×ˢ U) ↦ hp.2)) _ (half_pos hε)
    rw [eventually_nhdsWithin_iff] at h1 h2
    filter_upwards [h1, h2] with p hp1 hp2 hpU hpS
    have hp : p ∈ S ×ˢ U := ⟨hpS, hpU⟩
    calc dist (F p.1 p.2) (F (y t) p.2)
        ≤ dist (F p.1 p.2) (F (y t) w₀) + dist (F (y t) p.2) (F (y t) w₀) :=
          dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hp1 hp) (hp2 hp)
      _ = ε := add_halves ε
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.1 hev
  have hslope : Tendsto (slope y t) (𝓝[>] t) (𝓝 v) :=
    (hasDerivAt_iff_tendsto_slope.1 hv).mono_left (nhdsWithin_mono _ fun s hs ↦ ne_of_gt hs)
  refine Metric.isClosed_cthickening.mem_of_tendsto hslope ?_
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
  refine Metric.isClosed_cthickening.mem_of_tendsto hlim ?_
  have hτs : ∀ᶠ k in 𝒢, s < τ k := hτ₀.eventually_const_lt hsτ
  have hyt' : ∀ᶠ k in 𝒢, dist (freeze (x k) (τ k) t) (y t) < δ / 2 :=
    Metric.tendsto_nhds.1 (hy t) _ (half_pos hδ)
  filter_upwards [hτs, hyt'] with k hk hkt
  have ht' : t ∈ Icc 0 (τ k) := ⟨ht.1.le, by linarith [hs.1]⟩
  have hs' : s ∈ Icc 0 (τ k) := ⟨by linarith [ht.1, hs.1], hk.le⟩
  rw [freeze_of_mem ht'] at hkt
  rw [freeze_of_mem hs', freeze_of_mem ht', (hadm k).sub_eq_integral ht' hs']
  refine smul_intervalIntegral_mem_of_convex ((hconv (y t) hyt).cthickening ε)
    Metric.isClosed_cthickening hs.1 ((hadm k).intervalIntegrable_of_mem ht' hs') fun r hr ↦ ?_
  have hr' : r ∈ Icc 0 (τ k) := ⟨by linarith [ht.1, hr.1], hr.2.trans hk.le⟩
  have hu : u k r ∈ U := (hadm k).2.1 r hr'
  refine Metric.mem_cthickening_of_dist_le _ (F (y t) (u k r)) ε C ⟨u k r, hu, rfl⟩ ?_
  refine (hδF ?_ (u k r) hu hu (hxS k r hr')).le
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

variable [MeasurableSpace E] [BorelSpace E] [BorelSpace V]

/-- **Closure of trajectories in a closed set** (`ControlSystem.exists_isAdmissible_of_tendsto`,
with `F` continuous on `S × U` only and initial points varying along the filter): if trajectories
in the closed set `S`, with velocities bounded by `M`, frozen outside `[0, τₖ]`, converge
pointwise to `y` along a filter, and `τₖ → τ₀`, then `y` takes its values in `S` and is an
admissible trajectory from `y(0)` on `[0, τ₀]` for some control. -/
private theorem exists_isAdmissible_of_tendsto_of_mem {ι : Type*} {𝒢 : Filter ι} [𝒢.NeBot]
    (hS : IsClosed S) (hF : ContinuousOn (fun p : E × V ↦ F p.1 p.2) (S ×ˢ U)) (hU : IsCompact U)
    (hconv : ∀ z ∈ S, Convex ℝ (F z '' U)) {M : ℝ} (hM : 0 ≤ M) {x₀ : ι → E} {τ : ι → ℝ}
    {u : ι → ℝ → V} {x : ι → ℝ → E} {τ₀ : ℝ} {y : ℝ → E} (hτ : ∀ k, 0 ≤ τ k)
    (hadm : ∀ k, IsAdmissible F U (x₀ k) (τ k) (u k) (x k))
    (hxS : ∀ k, ∀ s ∈ Icc 0 (τ k), x k s ∈ S)
    (hbd : ∀ k, ∀ s ∈ Icc 0 (τ k), ‖F (x k s) (u k s)‖ ≤ M) (hτ₀ : Tendsto τ 𝒢 (𝓝 τ₀))
    (hy : ∀ t, Tendsto (fun k ↦ freeze (x k) (τ k) t) 𝒢 (𝓝 (y t))) :
    (∀ t, y t ∈ S) ∧ ∃ v : ℝ → V, IsAdmissible F U (y 0) τ₀ v y := by
  have hyS : ∀ t, y t ∈ S := fun t ↦ hS.mem_of_tendsto (hy t)
    (Eventually.of_forall fun k ↦ hxS k _ (max_zero_min_mem (hτ k) t))
  refine ⟨hyS, ?_⟩
  have hlip : LipschitzWith ⟨M, hM⟩ y := by
    refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    rw [dist_eq_norm, Real.dist_eq]
    exact le_of_tendsto ((hy s).sub (hy t)).norm
      (Eventually.of_forall fun k ↦ (hadm k).norm_freeze_sub_le (hτ k) (hbd k) s t)
  have hτ₀0 : 0 ≤ τ₀ := ge_of_tendsto hτ₀ (Eventually.of_forall hτ)
  obtain ⟨k₀⟩ := Filter.nonempty_of_neBot 𝒢
  have hUne : U.Nonempty := ⟨u k₀ 0, (hadm k₀).2.1 0 ⟨le_rfl, hτ k₀⟩⟩
  -- the derivative of `y` is almost everywhere a velocity
  have hae : ∀ᵐ s ∂(volume.restrict (Ioc 0 τ₀)), ∃ w ∈ U, F (y s) w - deriv y s = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hlip.ae_differentiableAt_real, (countable_singleton τ₀).ae_notMem volume]
      with s hd hne hs
    have hs' : s ∈ Ioo 0 τ₀ := ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩
    obtain ⟨w, hw, hFw⟩ := hasDerivAt_mem_image_of_tendsto_of_mem hF hU hconv hM hadm hxS hbd
      hτ₀ hy hs' (hyS s) hd.hasDerivAt
    exact ⟨w, hw, by rw [hFw, sub_self]⟩
  -- measurable selection of a control
  obtain ⟨σ, hσm, hσU, hσ⟩ := MeasureTheory.exists_measurable_forall_mem_ae_eq_zero
    (μ := volume.restrict (Ioc 0 τ₀)) (g := fun s w ↦ F (y s) w - deriv y s) hU hUne
    (fun w hw ↦ ((hF.comp_continuous (hlip.continuous.prodMk continuous_const :
      Continuous fun s ↦ (y s, w)) fun s ↦ ⟨hyS s, hw⟩).measurable).sub (measurable_deriv y))
    (fun s ↦ (hF.comp (continuous_const.prodMk continuous_id :
      Continuous fun w : V ↦ (y s, w)).continuousOn fun w hw ↦ ⟨hyS s, hw⟩).sub
        continuousOn_const)
    hae
  have hσ' : ∀ᵐ s ∂volume, s ∈ Ioc 0 τ₀ → F (y s) (σ s) = deriv y s := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hσ] with s hs hs'
    exact sub_eq_zero.1 (hs hs')
  refine ⟨σ, hσm, fun s _ ↦ hσU s, hlip.continuous.continuousOn, ?_, fun t ht ↦ ?_⟩
  · refine (hlip.intervalIntegrable_deriv 0 τ₀).congr_ae ?_
    rw [uIoc_of_le hτ₀0, EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hσ'] with s hs hs'
    exact (hs hs').symm
  · rw [intervalIntegral.integral_congr_ae (g := deriv y) ?_,
      hlip.intervalIntegral_deriv_eq_sub, add_sub_cancel]
    rw [uIoc_of_le ht.1]
    filter_upwards [hσ'] with s hs hs'
    exact hs ⟨hs'.1, hs'.2.trans ht.2⟩

variable [SecondCountableTopology V]

/-- For `G` continuous on `S × U`, `s ↦ G(x(s), u(s))` is integrable along an admissible pair in
`S`. -/
private theorem intervalIntegrable_comp_of_mem {x₀ : E} {T : ℝ} {u : ℝ → V} {x : ℝ → E}
    (h : IsAdmissible F U x₀ T u x) (hU : IsCompact U) (hT : 0 ≤ T)
    (hxS : ∀ t ∈ Icc 0 T, x t ∈ S) {W : Type*} [NormedAddCommGroup W] {G : E → V → W}
    (hG : ContinuousOn (fun p : E × V ↦ G p.1 p.2) (S ×ˢ U)) :
    IntervalIntegrable (fun s ↦ G (x s) (u s)) volume 0 T := by
  set K : Set (E × V) := (x '' Icc 0 T) ×ˢ U
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn h.2.2.1).prod hU
  have hKS : K ⊆ S ×ˢ U := prod_mono (image_subset_iff.2 hxS) subset_rfl
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hG.mono hKS)
  set μ := volume.restrict (Icc (0 : ℝ) T)
  have hg : AEMeasurable (fun s ↦ (x s, u s)) μ :=
    ((h.2.2.1.aestronglyMeasurable measurableSet_Icc).prodMk
      h.1.aestronglyMeasurable).aemeasurable
  have hgK : ∀ᵐ s ∂μ, (x s, u s) ∈ K :=
    (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun s hs ↦ ⟨mem_image_of_mem _ hs, h.2.1 s hs⟩)
  have hGm : AEStronglyMeasurable (fun p : E × V ↦ G p.1 p.2) (μ.map fun s ↦ (x s, u s)) := by
    have := (hG.mono hKS).aestronglyMeasurable (μ := μ.map fun s ↦ (x s, u s)) hK.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem ((ae_map_iff hg hK.measurableSet).2 hgK)] at this
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
  refine Integrable.of_bound (hGm.comp_aemeasurable hg) C ?_
  filter_upwards [hgK] with s hs
  exact hC _ hs

omit [FiniteDimensional ℝ E] [MetricSpace V] [MeasurableSpace E] [BorelSpace E] [BorelSpace V]
  [SecondCountableTopology V] in
/-- An admissible pair along which the running cost `φ` is integrable, with its accumulated cost,
is an admissible pair of the extended system (`ControlSystem.IsAdmissible.extend`, with the
integrability of the cost as a hypothesis). -/
private theorem isAdmissible_extend_of_intervalIntegrable [CompleteSpace E] {φ : E → V → ℝ}
    {x₀ : E} {T : ℝ} {u : ℝ → V} {x : ℝ → E} (h : IsAdmissible F U x₀ T u x) (hT : 0 ≤ T)
    (hφi : IntervalIntegrable (fun s ↦ φ (x s) (u s)) volume 0 T) :
    IsAdmissible (extend F φ) U (x₀, 0) T u (fun t ↦ (x t, ∫ s in (0 : ℝ)..t, φ (x s) (u s))) := by
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

end Closure

variable [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace V] [BorelSpace V] [SecondCountableTopology V]
  {F : E → V → E} {φ : E → V → ℝ} {U : Set V} {S K₀ : Set E} {N : Set (E × E)} {T₀ T₁ M : ℝ}

-- The two theorems share their instance arguments; the compactness theorem does not use
-- `[CompleteSpace E]` (implied by `[FiniteDimensional ℝ E]`) nor `[SecondCountableTopology V]`.
set_option linter.unusedSectionVars false in
/-- **Filippov's theorem with a state constraint and a compact set of initial points.** For a
control system `x' = F(x, u)`, `u ∈ U` compact, with `F` continuous on `S × U` for a closed set `S`,
velocities bounded by `M` on `S × U` and convex velocity sets `F(x, U)` at the points `x ∈ S`, the
set of endpoint pairs `(x(0), x(τ))` of the trajectories in `S` from points of a compact set `K₀`,
with terminal times `τ ∈ [T₀, T₁]`, `0 ≤ T₀`, is compact. -/
theorem isCompact_constrainedEndpoints (hU : IsCompact U) (hS : IsClosed S) (hK₀ : IsCompact K₀)
    (hF : ContinuousOn (fun p : E × V ↦ F p.1 p.2) (S ×ˢ U))
    (hconv : ∀ x ∈ S, Convex ℝ (F x '' U)) (hFM : ∀ x ∈ S, ∀ w ∈ U, ‖F x w‖ ≤ M)
    (hT₀ : 0 ≤ T₀) :
    IsCompact (constrainedEndpoints F U S K₀ T₀ T₁) := by
  -- velocities bounded by `Mp = max M 0 ≥ 0` along trajectories in `S`
  set Mp := max M 0 with hMp_def
  have hMp : 0 ≤ Mp := le_max_right _ _
  have hbd : ∀ {τ : ℝ} {u : ℝ → V} {x : ℝ → E}, IsAdmissible F U (x 0) τ u x →
      (∀ t ∈ Icc 0 τ, x t ∈ S) → ∀ s ∈ Icc 0 τ, ‖F (x s) (u s)‖ ≤ Mp :=
    fun h hxS s hs ↦ (hFM _ (hxS s hs) _ (h.2.1 s hs)).trans (le_max_left _ _)
  set R := Mp * T₁
  -- the endpoint pairs lie in the compact set `K₀ × cthickening R K₀`
  have hsub : constrainedEndpoints F U S K₀ T₀ T₁ ⊆ K₀ ×ˢ Metric.cthickening R K₀ := by
    rintro _ ⟨τ, hτ, u, x, hadm, hx0, hxS, rfl⟩
    have hτ0 : 0 ≤ τ := hT₀.trans hτ.1
    refine ⟨hx0, Metric.mem_cthickening_of_dist_le _ (x 0) _ _ hx0 ?_⟩
    rw [dist_eq_norm]
    exact (hadm.norm_sub_le_mul hτ0 (hbd hadm hxS) ⟨hτ0, le_rfl⟩).trans
      (mul_le_mul_of_nonneg_left hτ.2 hMp)
  refine (hK₀.prod hK₀.cthickening).of_isClosed_subset
    (isClosed_of_closure_subset fun p hp ↦ ?_) hsub
  -- closedness: a limit of endpoint pairs is an endpoint pair
  obtain ⟨q, hqP, hq⟩ := mem_closure_iff_seq_limit.1 hp
  simp only [constrainedEndpoints, mem_ofPred_eq] at hqP
  choose τ hτ u x hadm hx0 hxS hxq using hqP
  have hτ0 : ∀ k, 0 ≤ τ k := fun k ↦ hT₀.trans (hτ k).1
  have hbdk : ∀ k, ∀ s ∈ Icc 0 (τ k), ‖F (x k s) (u k s)‖ ≤ Mp := fun k ↦ hbd (hadm k) (hxS k)
  set K : Set ((ℝ → E) × ℝ) := (univ.pi fun _ ↦ Metric.cthickening R K₀) ×ˢ Icc T₀ T₁
  have hK : IsCompact K := (isCompact_univ_pi fun _ ↦ hK₀.cthickening).prod isCompact_Icc
  have hg : ∀ k, (freeze (x k) (τ k), τ k) ∈ K := by
    intro k
    refine ⟨fun t _ ↦ Metric.mem_cthickening_of_dist_le _ (x k 0) _ _ (hx0 k) ?_, hτ k⟩
    rw [dist_eq_norm]
    exact ((hadm k).norm_freeze_sub_le_mul (hτ0 k) (hbdk k) t).trans
      (mul_le_mul_of_nonneg_left (hτ k).2 hMp)
  obtain ⟨𝒢, h𝒢, h𝒢le, ⟨y, τ₀⟩, ⟨-, hτ₀T⟩, hlim⟩ := hK.exists_neBot_le_atTop_tendsto hg
  have hτlim : Tendsto τ 𝒢 (𝓝 τ₀) := (continuous_snd.tendsto _).comp hlim
  have hylim : ∀ t, Tendsto (fun k ↦ freeze (x k) (τ k) t) 𝒢 (𝓝 (y t)) :=
    tendsto_pi_nhds.1 ((continuous_fst.tendsto _).comp hlim)
  obtain ⟨hyS, v, hv⟩ := exists_isAdmissible_of_tendsto_of_mem hS hF hU hconv hMp hτ0 hadm hxS
    hbdk hτlim hylim
  have hy0 : Tendsto (fun k ↦ x k 0) 𝒢 (𝓝 (y 0)) :=
    (hylim 0).congr fun k ↦ freeze_of_mem ⟨le_rfl, hτ0 k⟩
  -- the endpoints converge, by equicontinuity
  have hyτ : Tendsto (fun k ↦ x k (τ k)) 𝒢 (𝓝 (y τ₀)) := by
    have h2 : Tendsto (fun k ↦ freeze (x k) (τ k) (τ k)) 𝒢 (𝓝 (y τ₀)) := by
      refine (hylim τ₀).congr_dist (squeeze_zero (g := fun k ↦ Mp * |τ₀ - τ k|)
        (fun _ ↦ dist_nonneg) (fun k ↦ ?_) ?_)
      · rw [dist_eq_norm]
        exact (hadm k).norm_freeze_sub_le (hτ0 k) (hbdk k) τ₀ (τ k)
      · have : Tendsto (fun k ↦ Mp * |τ₀ - τ k|) 𝒢 (𝓝 (Mp * |τ₀ - τ₀|)) :=
          ((hτlim.const_sub τ₀).abs).const_mul Mp
        simpa using this
    exact h2.congr fun k ↦ freeze_of_mem ⟨hτ0 k, le_rfl⟩
  have hp' : p = (y 0, y τ₀) :=
    tendsto_nhds_unique (hq.mono_left h𝒢le) ((hy0.prodMk_nhds hyτ).congr hxq)
  rw [hp']
  exact ⟨τ₀, hτ₀T, v, y, hv, hK₀.isClosed.mem_of_tendsto hy0 (Eventually.of_forall hx0),
    fun t _ ↦ hyS t, rfl⟩

/-- **Existence of optimal controls with a state constraint, a compact set of initial points and
a closed endpoint relation**, for fixed (`T₀ = T₁`) or free terminal time in `[T₀, T₁]`. Let
`x' = F(x, u)`, `u ∈ U` compact, be a control system and `φ` a running cost, both continuous on
`S × U` for a closed set `S`, with velocities bounded by `M` on `S × U`, and with convex extended
velocity sets `{(F(x, u), φ(x, u)) | u ∈ U}` at the points `x ∈ S`. Let `K₀` be compact and
`N ⊆ E × E` closed. If some admissible pair `(u, x)` on `[0, τ]`, `τ ∈ [T₀, T₁]`, has `x(0) ∈ K₀`,
`x(t) ∈ S` on `[0, τ]` and `(x(0), x(τ)) ∈ N`, then one such pair has the least cost
`∫₀^τ φ(x, u)` among all of them. -/
theorem exists_optimal_constrained (hU : IsCompact U) (hS : IsClosed S) (hK₀ : IsCompact K₀)
    (hN : IsClosed N) (hF : ContinuousOn (fun p : E × V ↦ F p.1 p.2) (S ×ˢ U))
    (hφ : ContinuousOn (fun p : E × V ↦ φ p.1 p.2) (S ×ˢ U))
    (hconv : ∀ x ∈ S, Convex ℝ ((fun w ↦ (F x w, φ x w)) '' U))
    (hFM : ∀ x ∈ S, ∀ w ∈ U, ‖F x w‖ ≤ M) (hT₀ : 0 ≤ T₀)
    (hne : ∃ τ ∈ Icc T₀ T₁, ∃ u x, IsAdmissible F U (x 0) τ u x ∧ x 0 ∈ K₀ ∧
      (∀ t ∈ Icc 0 τ, x t ∈ S) ∧ (x 0, x τ) ∈ N) :
    ∃ τ ∈ Icc T₀ T₁, ∃ u x, IsAdmissible F U (x 0) τ u x ∧ x 0 ∈ K₀ ∧
      (∀ t ∈ Icc 0 τ, x t ∈ S) ∧ (x 0, x τ) ∈ N ∧
      ∀ τ' ∈ Icc T₀ T₁, ∀ u' x', IsAdmissible F U (x' 0) τ' u' x' → x' 0 ∈ K₀ →
        (∀ t ∈ Icc 0 τ', x' t ∈ S) → (x' 0, x' τ') ∈ N →
        ∫ t in (0 : ℝ)..τ, φ (x t) (u t) ≤ ∫ t in (0 : ℝ)..τ', φ (x' t) (u' t) := by
  obtain ⟨τ₁, hτ₁, u₁, x₁, hx₁, hx₁0, hx₁S, hx₁N⟩ := hne
  have hτ₁0 : 0 ≤ τ₁ := hT₀.trans hτ₁.1
  have hM : 0 ≤ M :=
    (norm_nonneg _).trans (hFM _ (hx₁S 0 ⟨le_rfl, hτ₁0⟩) _ (hx₁.2.1 0 ⟨le_rfl, hτ₁0⟩))
  -- the trajectories in `S` from `K₀` with times at most `T₁` stay in the compact set `S'`
  set S' := S ∩ Metric.cthickening (M * T₁) K₀ with hS'_def
  have hS'cl : IsClosed S' := hS.inter Metric.isClosed_cthickening
  have hS'c : IsCompact S' := hK₀.cthickening.of_isClosed_subset hS'cl inter_subset_right
  have hmemS' : ∀ {τ : ℝ} {u : ℝ → V} {x : ℝ → E}, τ ∈ Icc T₀ T₁ →
      IsAdmissible F U (x 0) τ u x → x 0 ∈ K₀ → (∀ t ∈ Icc 0 τ, x t ∈ S) →
      ∀ t ∈ Icc 0 τ, x t ∈ S' := by
    intro τ u x hτ h hx0 hxS t ht
    have hτ0 : 0 ≤ τ := hT₀.trans hτ.1
    refine ⟨hxS t ht, Metric.mem_cthickening_of_dist_le _ (x 0) _ _ hx0 ?_⟩
    rw [dist_eq_norm]
    exact (h.norm_sub_le_mul hτ0 (fun s hs ↦ hFM _ (hxS s hs) _ (h.2.1 s hs)) ht).trans
      (mul_le_mul_of_nonneg_left hτ.2 hM)
  -- the extended system, constrained to `S' × ℝ`, from `K₀ × {0}`
  obtain ⟨Mφ, hMφ⟩ := (hS'c.prod hU).exists_bound_of_continuousOn
    (hφ.mono (prod_mono inter_subset_left subset_rfl))
  have hmaps : MapsTo (fun p : (E × ℝ) × V ↦ (p.1.1, p.2)) ((S' ×ˢ univ) ×ˢ U) (S ×ˢ U) :=
    fun p hp ↦ ⟨hp.1.1.1, hp.2⟩
  have hcont : ContinuousOn (fun p : (E × ℝ) × V ↦ extend F φ p.1 p.2) ((S' ×ˢ univ) ×ˢ U) :=
    (hF.comp (continuous_fst.fst.prodMk continuous_snd).continuousOn hmaps).prodMk
      (hφ.comp (continuous_fst.fst.prodMk continuous_snd).continuousOn hmaps)
  have hconv' : ∀ z ∈ S' ×ˢ (univ : Set ℝ), Convex ℝ (extend F φ z '' U) :=
    fun z hz ↦ hconv z.1 hz.1.1
  have hbd' : ∀ z ∈ S' ×ˢ (univ : Set ℝ), ∀ w ∈ U, ‖extend F φ z w‖ ≤ max M Mφ :=
    fun z hz w hw ↦ norm_prod_le_iff.2 ⟨(hFM _ hz.1.1 _ hw).trans (le_max_left _ _),
      (hMφ (z.1, w) ⟨hz.1, hw⟩).trans (le_max_right _ _)⟩
  have hA := isCompact_constrainedEndpoints hU (hS'cl.prod isClosed_univ)
    (hK₀.prod (isCompact_singleton (x := (0 : ℝ)))) hcont hconv' hbd' hT₀ (T₁ := T₁)
  set A := constrainedEndpoints (extend F φ) U (S' ×ˢ univ) (K₀ ×ˢ {0}) T₀ T₁
  -- the costs of the extended endpoint pairs satisfying the endpoint relation
  set B := (fun a : (E × ℝ) × (E × ℝ) ↦ a.2.2) ''
    (A ∩ (fun a : (E × ℝ) × (E × ℝ) ↦ (a.1.1, a.2.1)) ⁻¹' N)
  have hB : IsCompact B :=
    (hA.inter_right (hN.preimage (continuous_fst.fst.prodMk continuous_snd.fst))).image
      continuous_snd.snd
  -- every competitor lifts to the extended system
  have hmemB : ∀ τ' ∈ Icc T₀ T₁, ∀ u' x', IsAdmissible F U (x' 0) τ' u' x' → x' 0 ∈ K₀ →
      (∀ t ∈ Icc 0 τ', x' t ∈ S) → (x' 0, x' τ') ∈ N →
      ∫ t in (0 : ℝ)..τ', φ (x' t) (u' t) ∈ B := by
    intro τ' hτ' u' x' h' hx0 hxS hxN
    have hτ0 : 0 ≤ τ' := hT₀.trans hτ'.1
    have hφi : IntervalIntegrable (fun s ↦ φ (x' s) (u' s)) volume 0 τ' :=
      intervalIntegrable_comp_of_mem h' hU hτ0 hxS hφ
    have hz := isAdmissible_extend_of_intervalIntegrable h' hτ0 hφi
    set z : ℝ → E × ℝ := fun t ↦ (x' t, ∫ s in (0 : ℝ)..t, φ (x' s) (u' s)) with hz_def
    have hz0 : z 0 = (x' 0, 0) := by simp [z]
    have hS'm := hmemS' hτ' h' hx0 hxS
    refine ⟨(z 0, z τ'), ⟨⟨τ', hτ', u', z, by rw [hz0]; exact hz, ?_, fun t ht ↦ ?_, rfl⟩,
      hxN⟩, rfl⟩
    · rw [hz0]
      exact ⟨hx0, rfl⟩
    · exact ⟨hS'm t ht, mem_univ _⟩
  have hBne : B.Nonempty := ⟨_, hmemB τ₁ hτ₁ u₁ x₁ hx₁ hx₁0 hx₁S hx₁N⟩
  -- a least cost, and an optimal pair realizing it
  obtain ⟨c, hcB, hc⟩ := hB.exists_isLeast hBne
  obtain ⟨a, ⟨haA, haN⟩, rfl⟩ := hcB
  obtain ⟨τ, hτ, u, z, hz, hz0, hzS, rfl⟩ := haA
  have hτ0 : 0 ≤ τ := hT₀.trans hτ.1
  have hzeq : z 0 = ((z 0).1, 0) := Prod.ext rfl hz0.2
  rw [hzeq] at hz
  obtain ⟨hx, hcost⟩ := hz.of_extend
  refine ⟨τ, hτ, u, fun t ↦ (z t).1, hx, hz0.1, fun t ht ↦ (hzS t ht).1.1, haN,
    fun τ' hτ' u' x' h' hx0' hxS' hxN' ↦ ?_⟩
  have hcτ : ∫ t in (0 : ℝ)..τ, φ (z t).1 (u t) = (z τ).2 := by
    rw [hcost τ ⟨hτ0, le_rfl⟩, zero_add]
  change ∫ t in (0 : ℝ)..τ, φ (z t).1 (u t) ≤ _
  rw [hcτ]
  exact hc (hmemB τ' hτ' u' x' h' hx0' hxS' hxN')

end ControlSystem
