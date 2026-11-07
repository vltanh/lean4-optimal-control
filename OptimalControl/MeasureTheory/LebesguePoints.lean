module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Lebesgue points of a function of one real variable

`IsLebesguePointWithin u s τ`: `τ` is a Lebesgue point of `u` relative to the set `s` (in
practice an interval `[a, b]`), in the sense of Agrachev–Sachkov (authors' draft, §12.2, p. 170):
`lim_{t → τ, t ∈ s} |t - τ|⁻¹ ∫_τ^t ‖u(θ) - u(τ)‖ dθ = 0`. The integral over the unordered
interval `Ι τ t` is used, which equals `|∫_τ^t ‖u(θ) - u(τ)‖ dθ|`. This file states:

* almost every point of `[a, b]` is a Lebesgue point of an integrable `u`
  (`ae_isLebesguePointWithin`; A–S: "The set of Lebesgue points has the full measure in the
  domain `[0, t₁]`. For details on this subject, see e.g. [146]", [146] = Segal–Kunze,
  *Integrals and operators*);
* near a Lebesgue point `τ` there are points `τ'` of any prescribed set of full measure, outside
  any prescribed finite set, with `u(τ')` close to `u(τ)` (`IsLebesguePointWithin.exists_near`);
  this is the step "we can choose points `τᵢ` distinct" of the proof of A–S's Lemma 12.2
  (p. 171), which rests on the density statement
  `meas{t' ∈ [τ, t] | |u(t') - u(τ)| ≤ ε}/|t - τ| → 1`;
* a Lebesgue point of `u` is a Lebesgue point of `z ↦ G(z, u(·))`, uniformly for `z` in a
  compact set, when `G` is continuous on `K × U` (`IsLebesguePointWithin.eventually_integral_le`);
  this is what the derivative of the needle variations at `s = 0` uses (A–S, p. 172).

## Proof sketch

The first statement is the Lebesgue differentiation theorem (Mathlib's
`IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub` for the doubling measure `volume` on `ℝ`,
applied to the indicator of `[a, b]` times `u`), since `|t - τ|⁻¹ ∫_{Ι τ t} ≤ 2 ⨍_{B(τ, |t - τ|)}`.
The second: by Chebyshev's inequality the set of `t'` between `τ` and `t` with
`‖u(t') - u(τ)‖ ≥ ε` has measure less than `|t - τ| / 2` when the mean oscillation on `Ι τ t` is
less than `ε / 2`, so the good set has positive measure, and a set of positive measure meets every
set of full measure outside any null set. The third: by the tube lemma for the compact set `K`,
there is `δ > 0` with `‖G(z, v) - G(z, u(τ))‖ < η/2` for `z ∈ K`, `v ∈ U`, `‖v - u(τ)‖ < δ`;
with a bound `C` of `‖G‖` on `K × U`, `‖G(z, v) - G(z, u(τ))‖ ≤ η/2 + (2C/δ)‖v - u(τ)‖`, which
is integrated over `Ι τ t`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped Interval

variable {V : Type*} [NormedAddCommGroup V]

/-- `τ` is a Lebesgue point of `u` relative to `s` (Agrachev–Sachkov, authors' draft, p. 170):
`|t - τ|⁻¹ ∫_{Ι τ t} ‖u(θ) - u(τ)‖ dθ → 0` as `t → τ` within `s \ {τ}`. -/
def IsLebesguePointWithin (u : ℝ → V) (s : Set ℝ) (τ : ℝ) : Prop :=
  Tendsto (fun t ↦ |t - τ|⁻¹ * ∫ θ in Ι τ t, ‖u θ - u τ‖) (𝓝[s \ {τ}] τ) (𝓝 0)

variable {u : ℝ → V} {a b : ℝ}

/-- **Lebesgue's differentiation theorem**: almost every point of `[a, b]` is a Lebesgue point
of a function integrable on `[a, b]` (Agrachev–Sachkov, p. 171, citing Segal–Kunze). -/
theorem ae_isLebesguePointWithin (hu : IntegrableOn u (Icc a b)) :
    ∀ᵐ τ ∂(volume.restrict (Icc a b)), IsLebesguePointWithin u (Icc a b) τ := by
  set g : ℝ → V := (Icc a b).indicator u with hg_def
  have hgi : Integrable g volume := hu.integrable_indicator measurableSet_Icc
  have H := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hgi.locallyIntegrable 1
  filter_upwards [ae_restrict_of_ae H, ae_restrict_mem measurableSet_Icc] with τ hτ hτI
  have hδ : Tendsto (fun t ↦ |t - τ|) (𝓝[Icc a b \ {τ}] τ) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t ↦ |t - τ|) (𝓝 τ) (𝓝 |τ - τ|) :=
        ((continuous_sub_right τ).abs.tendsto τ)
      rw [sub_self, abs_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact abs_pos.2 (sub_ne_zero.2 ht.2)
  have hlim := hτ (fun _ ↦ τ) (fun t ↦ |t - τ|) hδ
    (Eventually.of_forall fun t ↦ mem_closedBall_self (by positivity))
  have h2 : Tendsto (fun t ↦ 2 * ⨍ y in closedBall τ |t - τ|, ‖g y - g τ‖)
      (𝓝[Icc a b \ {τ}] τ) (𝓝 0) := by
    simpa using hlim.const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun t ↦ ?_) ?_ h2
  · exact mul_nonneg (inv_nonneg.2 (abs_nonneg _)) (integral_nonneg fun _ ↦ norm_nonneg _)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hr : 0 < |t - τ| := abs_pos.2 (sub_ne_zero.2 ht.2)
  have hsub : Ι τ t ⊆ Icc a b := uIoc_subset_uIcc.trans (uIcc_subset_Icc hτI ht.1)
  have hball : Ι τ t ⊆ closedBall τ |t - τ| := by
    intro θ hθ
    rw [mem_closedBall, Real.dist_eq]
    exact abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hθ)
  have hgτ : g τ = u τ := by simp [hg_def, hτI]
  have heq : ∫ θ in Ι τ t, ‖u θ - u τ‖ = ∫ θ in Ι τ t, ‖g θ - g τ‖ := by
    refine setIntegral_congr_fun measurableSet_uIoc fun θ hθ ↦ ?_
    rw [hgτ]
    simp [hg_def, hsub hθ]
  have hint : IntegrableOn (fun θ ↦ ‖g θ - g τ‖) (closedBall τ |t - τ|) volume :=
    (hgi.integrableOn.sub (integrableOn_const measure_closedBall_lt_top.ne)).norm
  have hle : ∫ θ in Ι τ t, ‖g θ - g τ‖ ≤ ∫ θ in closedBall τ |t - τ|, ‖g θ - g τ‖ :=
    setIntegral_mono_set hint (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (Eventually.of_forall hball)
  have hvol : volume.real (closedBall τ |t - τ|) = 2 * |t - τ| := by
    rw [measureReal_def, Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
  rw [setAverage_eq, hvol, smul_eq_mul, heq]
  calc |t - τ|⁻¹ * ∫ θ in Ι τ t, ‖g θ - g τ‖
      ≤ |t - τ|⁻¹ * ∫ θ in closedBall τ |t - τ|, ‖g θ - g τ‖ :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hr.le)
    _ = 2 * ((2 * |t - τ|)⁻¹ * ∫ θ in closedBall τ |t - τ|, ‖g θ - g τ‖) := by
        field_simp

/-- Near a Lebesgue point `τ ∈ [a, b]` of `u` (integrable on `[a, b]`, `a < b`) there are points
`τ'` of the open interval `(a, b)` in any prescribed set `G` of full measure in `[a, b]`, outside
any prescribed finite set `S`, with `|τ' - τ| < ε` and `‖u(τ') - u(τ)‖ < ε` (Agrachev–Sachkov,
proof of Lemma 12.2, p. 171). -/
theorem IsLebesguePointWithin.exists_near (hu : IntegrableOn u (Icc a b)) (hab : a < b)
    {τ : ℝ} (hτ : τ ∈ Icc a b) (hleb : IsLebesguePointWithin u (Icc a b) τ) {G : Set ℝ}
    (hG : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∈ G) (S : Finset ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ' ∈ G, τ' ∈ Ioo a b ∧ τ' ∉ S ∧ |τ' - τ| < ε ∧ ‖u τ' - u τ‖ < ε := by
  -- the filter of `t → τ` in `[a, b] \ {τ}` is nontrivial
  have hne : (𝓝[Icc a b \ {τ}] τ).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    rcases eq_or_lt_of_le hτ.2 with hτb | hτb
    · have : Ioo a τ ⊆ Icc a b \ {τ} := fun x hx ↦
        ⟨⟨hx.1.le, hx.2.le.trans hτb.le⟩, hx.2.ne⟩
      refine closure_mono this ?_
      rw [closure_Ioo (by linarith [hτb])]
      exact ⟨by linarith [hτb], le_rfl⟩
    · have : Ioo τ b ⊆ Icc a b \ {τ} := fun x hx ↦ ⟨⟨hτ.1.trans hx.1.le, hx.2.le⟩, hx.1.ne'⟩
      refine closure_mono this ?_
      rw [closure_Ioo hτb.ne]
      exact ⟨le_rfl, hτb.le⟩
  -- a point `t` with `|t - τ| < ε` and a small mean oscillation on `Ι τ t`
  have hclose : ∀ᶠ t in 𝓝[Icc a b \ {τ}] τ, |t - τ| < ε := by
    have : ∀ᶠ t in 𝓝 τ, |t - τ| < ε := by
      have h := (continuous_sub_right τ).abs.tendsto τ
      rw [sub_self, abs_zero] at h
      exact h (gt_mem_nhds hε)
    exact this.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ⟨htI, htτ⟩, ht1, ht2⟩ :=
    (Filter.Eventually.and (p := fun t ↦ t ∈ Icc a b \ {τ}) self_mem_nhdsWithin
      (hclose.and (hleb (gt_mem_nhds (half_pos hε))))).exists
  have hr : 0 < |t - τ| := abs_pos.2 (sub_ne_zero.2 htτ)
  have hsub : Ι τ t ⊆ Icc a b := uIoc_subset_uIcc.trans (uIcc_subset_Icc hτ htI)
  set μ := volume.restrict (Ι τ t) with hμ
  have hμuniv : μ.real univ = |t - τ| := by
    rw [hμ, measureReal_restrict_apply_univ, measureReal_def, Real.volume_uIoc,
      ENNReal.toReal_ofReal (abs_nonneg _)]
  have hint : Integrable (fun θ ↦ ‖u θ - u τ‖) μ :=
    ((hu.mono_set hsub).sub (integrableOn_const (by rw [Real.volume_uIoc]; simp))).norm
  -- Chebyshev: the set where `‖u - u(τ)‖ ≥ ε` has measure `< |t - τ| / 2`
  have hM := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
    hint ε
  have ht2' : ∫ θ, ‖u θ - u τ‖ ∂μ < ε / 2 * |t - τ| := by
    have := ht2
    rw [mem_ofPred_eq, inv_mul_lt_iff₀ hr] at this
    linarith
  have hbad : μ.real {θ | ε ≤ ‖u θ - u τ‖} < |t - τ| / 2 := by
    by_contra h
    have h' := not_lt.1 h
    nlinarith
  -- so the good set has positive measure
  have hgood : μ {θ | ‖u θ - u τ‖ < ε} ≠ 0 := by
    intro h0
    have h0' : μ.real {θ | ‖u θ - u τ‖ < ε} = 0 := by simp [measureReal_def, h0]
    have hU : μ.real univ ≤ μ.real {θ | ‖u θ - u τ‖ < ε} + μ.real {θ | ε ≤ ‖u θ - u τ‖} := by
      refine le_trans (le_of_eq ?_) (measureReal_union_le _ _)
      congr 1
      ext θ
      simp [lt_or_ge]
    linarith
  -- almost every point of `Ι τ t` is in `G ∩ (a, b)` and outside `S`
  have hfin : ∀ᵐ θ ∂μ, θ ∉ (S : Set ℝ) ∪ {a, b} := by
    refine ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 ?_)
    exact (S.finite_toSet.union (toFinite _)).measure_zero _
  have hae : ∀ᵐ θ ∂μ, θ ∈ G ∧ θ ∈ Ι τ t ∧ θ ∉ (S : Set ℝ) ∪ {a, b} := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hG,
      ae_restrict_mem measurableSet_uIoc, hfin] with θ h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨θ, hθε, hθG, hθI, hθS⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hgood (ae_restrict_of_ae hae)
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, Finset.mem_coe, not_or] at hθS
  refine ⟨θ, hθG, ⟨lt_of_le_of_ne (hsub hθI).1 (Ne.symm hθS.2.1),
    lt_of_le_of_ne (hsub hθI).2 hθS.2.2⟩, hθS.1, ?_, hθε⟩
  exact (abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hθI)).trans_lt ht1

/-- A Lebesgue point of `u` is a Lebesgue point of `θ ↦ G(z, u(θ))`, uniformly in `z ∈ K`, when
`G` is continuous on `K × U` with `K` and `U` compact and `u` takes its values in `U` on
`[a, b]`. -/
theorem IsLebesguePointWithin.eventually_integral_le {E F : Type*} [TopologicalSpace E]
    [NormedAddCommGroup F] {G : E → V → F} {K : Set E} {U : Set V} (hK : IsCompact K)
    (hU : IsCompact U) (hG : ContinuousOn (fun p : E × V ↦ G p.1 p.2) (K ×ˢ U))
    (hu : AEStronglyMeasurable u (volume.restrict (Icc a b))) (huU : ∀ t ∈ Icc a b, u t ∈ U)
    {τ : ℝ} (hτ : τ ∈ Icc a b) (hleb : IsLebesguePointWithin u (Icc a b) τ) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ t in 𝓝[Icc a b \ {τ}] τ, ∀ z ∈ K,
      |t - τ|⁻¹ * ∫ θ in Ι τ t, ‖G z (u θ) - G z (u τ)‖ ≤ η := by
  have huτ : u τ ∈ U := huU τ hτ
  -- uniform continuity in the second variable at `u τ`, uniformly for `z ∈ K` (tube lemma)
  obtain ⟨δ, hδ, hδG⟩ : ∃ δ > 0, ∀ z ∈ K, ∀ v ∈ U, ‖v - u τ‖ < δ →
      ‖G z v - G z (u τ)‖ < η / 2 := by
    set W : Set (E × V) := {p | p ∈ K ×ˢ U → ‖G p.1 p.2 - G p.1 (u τ)‖ < η / 2}
    have hW : ∀ z ∈ K, W ∈ 𝓝 z ×ˢ 𝓝 (u τ) := by
      intro z hz
      rw [← nhds_prod_eq]
      have hzU : (z, u τ) ∈ K ×ˢ U := ⟨hz, huτ⟩
      have h1 : Tendsto (fun p : E × V ↦ G p.1 p.2) (𝓝[K ×ˢ U] (z, u τ)) (𝓝 (G z (u τ))) :=
        hG _ hzU
      have h2 : Tendsto (fun p : E × V ↦ G p.1 (u τ)) (𝓝[K ×ˢ U] (z, u τ))
          (𝓝 (G z (u τ))) := by
        have hc : ContinuousWithinAt (fun p : E × V ↦ (p.1, u τ)) (K ×ˢ U) (z, u τ) :=
          (continuous_fst.prodMk continuous_const).continuousWithinAt
        exact ContinuousWithinAt.comp (x := (z, u τ)) (f := fun p : E × V ↦ (p.1, u τ))
          (hG _ hzU) hc (fun p hp ↦ ⟨hp.1, huτ⟩)
      have h3 := (h1.sub h2).norm
      rw [sub_self, norm_zero] at h3
      have h4 := h3 (gt_mem_nhds (half_pos hη))
      rw [Filter.mem_map, mem_nhdsWithin_iff_eventually] at h4
      filter_upwards [h4] with p hp hpKU using hp hpKU
    obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.1 (hK.mem_nhdsSet_prod_of_forall hW)
    obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.1 hB
    refine ⟨δ, hδ, fun z hz v hv hvδ ↦ ?_⟩
    have : (z, v) ∈ W := hAB ⟨subset_of_mem_nhdsSet hA hz, hδB (by simpa [dist_eq_norm])⟩
    exact this ⟨hz, hv⟩
  -- a bound for `G` on `K × U`
  obtain ⟨C, hC0, hC⟩ : ∃ C, 0 ≤ C ∧ ∀ z ∈ K, ∀ v ∈ U, ‖G z v‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hK.prod hU).exists_bound_of_continuousOn hG
    exact ⟨max C 0, le_max_right _ _, fun z hz v hv ↦ (hC (z, v) ⟨hz, hv⟩).trans
      (le_max_left _ _)⟩
  -- the pointwise bound `‖G(z, v) - G(z, u(τ))‖ ≤ η/2 + (2C/δ) ‖v - u(τ)‖`
  have hpt : ∀ z ∈ K, ∀ v ∈ U,
      ‖G z v - G z (u τ)‖ ≤ η / 2 + 2 * C / δ * ‖v - u τ‖ := by
    intro z hz v hv
    rcases lt_or_ge ‖v - u τ‖ δ with h | h
    · have := hδG z hz v hv h
      have : 0 ≤ 2 * C / δ * ‖v - u τ‖ := by positivity
      linarith
    · calc ‖G z v - G z (u τ)‖ ≤ ‖G z v‖ + ‖G z (u τ)‖ := norm_sub_le _ _
        _ ≤ 2 * C := by linarith [hC z hz v hv, hC z hz _ huτ]
        _ = 2 * C / δ * δ := by field_simp
        _ ≤ 2 * C / δ * ‖v - u τ‖ := by gcongr
        _ ≤ η / 2 + 2 * C / δ * ‖v - u τ‖ := by linarith
  -- the Lebesgue point
  have hev : ∀ᶠ t in 𝓝[Icc a b \ {τ}] τ,
      2 * C / δ * (|t - τ|⁻¹ * ∫ θ in Ι τ t, ‖u θ - u τ‖) < η / 2 := by
    have := (hleb.const_mul (2 * C / δ))
    rw [mul_zero] at this
    exact this (gt_mem_nhds (half_pos hη))
  filter_upwards [hev, self_mem_nhdsWithin] with t ht htI z hz
  have hr : 0 < |t - τ| := abs_pos.2 (sub_ne_zero.2 htI.2)
  have hsub : Ι τ t ⊆ Icc a b := uIoc_subset_uIcc.trans (uIcc_subset_Icc hτ htI.1)
  have hfin : volume (Ι τ t) ≠ ⊤ := by rw [Real.volume_uIoc]; simp
  -- `‖u - u(τ)‖` is integrable on `Ι τ t` (bounded and measurable)
  obtain ⟨R, hR⟩ := hU.isBounded.exists_norm_le
  have hint : IntegrableOn (fun θ ↦ ‖u θ - u τ‖) (Ι τ t) := by
    have : IsFiniteMeasure (volume.restrict (Ι τ t)) := isFiniteMeasure_restrict.2 hfin
    refine Integrable.of_bound (C := R + ‖u τ‖) ?_ ?_
    · exact ((hu.mono_set hsub).sub aestronglyMeasurable_const).norm
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with θ hθ
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith [hR _ (huU θ (hsub hθ))])
  have hle : ∫ θ in Ι τ t, ‖G z (u θ) - G z (u τ)‖ ≤
      ∫ θ in Ι τ t, (η / 2 + 2 * C / δ * ‖u θ - u τ‖) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
      ((integrableOn_const hfin).add (hint.const_mul _)) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with θ hθ
    exact hpt z hz _ (huU θ (hsub hθ))
  rw [integral_add (integrableOn_const hfin) (hint.const_mul _), integral_const_mul,
    setIntegral_const, measureReal_def, Real.volume_uIoc, ENNReal.toReal_ofReal (abs_nonneg _),
    smul_eq_mul] at hle
  calc |t - τ|⁻¹ * ∫ θ in Ι τ t, ‖G z (u θ) - G z (u τ)‖
      ≤ |t - τ|⁻¹ * (|t - τ| * (η / 2) + 2 * C / δ * ∫ θ in Ι τ t, ‖u θ - u τ‖) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hr.le)
    _ = η / 2 + 2 * C / δ * (|t - τ|⁻¹ * ∫ θ in Ι τ t, ‖u θ - u τ‖) := by
        field_simp
    _ ≤ η := by linarith
