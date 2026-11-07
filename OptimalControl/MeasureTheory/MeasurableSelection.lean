module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Measurable selection of zeros of Carathéodory functions on a compact set

Let `U` be a compact subset of a metric space `V` with its Borel σ-algebra, and let
`g : α → V → E` be a *Carathéodory function*: `t ↦ g t w` is measurable for every `w ∈ U` and
`w ↦ g t w` is continuous on `U` for every `t`. If `g t` has a zero in `U` for every `t`, then a
zero can be chosen measurably: there is a measurable `σ : α → V` with `σ t ∈ U` and
`g t (σ t) = 0` for all `t` (a special case of the Kuratowski–Ryll-Nardzewski selection theorem,
for the closed-valued map `t ↦ {w ∈ U | g t w = 0}`; Mathlib has no measurable selection theorem).
This is the measurable-selection step of *Filippov's lemma* in control theory.

The proof is the Kuratowski–Ryll-Nardzewski construction: with `d` a dense sequence in `U` and
`D` a bound for the diameter of `U`, choose `σ₀ = d 0` and let `σⱼ₊₁(t) = d i` for the least `i`
with `dist (d i) (σⱼ t) < D / 2ʲ` and `d i` within `D / 2ʲ⁺¹` of a zero of `g t`; the sequence
`σⱼ(t)` is Cauchy, its limit is a zero of `g t`, and each `σⱼ` is measurable since
`{t | ∃ w ∈ U, dist c w < r ∧ g t w = 0}` is measurable (compactness of `U`).

## Main statements

* `MeasureTheory.measurableSet_setOf_exists_mem_eq_zero`: for compact `C`,
  `{t | ∃ w ∈ C, g t w = 0}` is measurable;
* `MeasureTheory.exists_measurable_forall_mem_and_eq_zero`: the measurable selection;
* `MeasureTheory.exists_measurable_forall_mem_ae_eq_zero`: the almost-everywhere version (zeros
  exist for almost every `t`; the selection is a zero for almost every `t`).
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace MeasureTheory

variable {α V E : Type*} [MeasurableSpace α] [MetricSpace V] [NormedAddCommGroup E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- For a Carathéodory function `g` and a compact set `C`, the set of parameters `t` for which
`g t` has a zero in `C` is measurable. -/
theorem measurableSet_setOf_exists_mem_eq_zero {C : Set V} (hC : IsCompact C) {g : α → V → E}
    (hmeas : ∀ w ∈ C, Measurable fun t ↦ g t w) (hcont : ∀ t, ContinuousOn (g t) C) :
    MeasurableSet {t | ∃ w ∈ C, g t w = 0} := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  have : Nonempty C := hne.to_subtype
  have : SeparableSpace C := hC.isSeparable.separableSpace
  obtain ⟨d, hd⟩ := exists_dense_seq C
  have key : {t | ∃ w ∈ C, g t w = 0} =
      ⋂ j : ℕ, ⋃ i : ℕ, {t | ‖g t (d i)‖ < 1 / ((j : ℝ) + 1)} := by
    ext t
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · rintro ⟨w, hwC, hw⟩ j
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hcont t w hwC)
        (1 / ((j : ℝ) + 1)) (by positivity)
      obtain ⟨i, hy⟩ := hd.exists_dist_lt ⟨w, hwC⟩ hδ
      refine ⟨i, ?_⟩
      have := hball (d i).2 (by rw [dist_comm]; exact hy)
      rwa [hw, dist_zero_right] at this
    · intro h
      choose i hi using h
      obtain ⟨w, hwC, φ, hφ, hlim⟩ := hC.tendsto_subseq (fun j ↦ (d (i j)).2)
      refine ⟨w, hwC, ?_⟩
      have h1 : Tendsto (fun j ↦ g t (d (i (φ j)))) atTop (𝓝 (g t w)) :=
        (hcont t w hwC).tendsto.comp
          (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun j ↦ (d _).2⟩)
      have h2 : Tendsto (fun j ↦ g t (d (i (φ j)))) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun j ↦ (hi (φ j)).le) ?_
        exact (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
      exact tendsto_nhds_unique h1 h2
  rw [key]
  refine MeasurableSet.iInter fun j ↦ MeasurableSet.iUnion fun i ↦ ?_
  exact measurableSet_lt (hmeas _ (d i).2).norm measurable_const

/-- For a Carathéodory function `g` on a compact set `U`, the set of parameters `t` for which
`g t` has a zero in `U` within distance `r` of `c` is measurable. -/
theorem measurableSet_setOf_exists_mem_dist_lt_and_eq_zero {U : Set V} (hU : IsCompact U)
    {g : α → V → E} (hmeas : ∀ w ∈ U, Measurable fun t ↦ g t w)
    (hcont : ∀ t, ContinuousOn (g t) U) (c : V) (r : ℝ) :
    MeasurableSet {t | ∃ w ∈ U, dist c w < r ∧ g t w = 0} := by
  have key : {t | ∃ w ∈ U, dist c w < r ∧ g t w = 0} =
      ⋃ k : ℕ, {t | ∃ w ∈ U ∩ Metric.closedBall c (r - 1 / ((k : ℝ) + 1)), g t w = 0} := by
    ext t
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, Metric.mem_closedBall]
    constructor
    · rintro ⟨w, hwU, hwr, hw⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hwr)
      exact ⟨k, w, ⟨hwU, by rw [dist_comm]; linarith⟩, hw⟩
    · rintro ⟨k, w, ⟨hwU, hwr⟩, hw⟩
      refine ⟨w, hwU, ?_, hw⟩
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      rw [dist_comm]; linarith
  rw [key]
  refine MeasurableSet.iUnion fun k ↦ ?_
  exact measurableSet_setOf_exists_mem_eq_zero (hU.inter_right Metric.isClosed_closedBall)
    (fun w hw ↦ hmeas w hw.1) (fun t ↦ (hcont t).mono inter_subset_left)

private theorem msel_exists_or (p : ℕ → Prop) : ∃ i, p i ∨ ¬ ∃ i', p i' := by
  by_cases h : ∃ i', p i'
  · obtain ⟨i, hi⟩ := h
    exact ⟨i, Or.inl hi⟩
  · exact ⟨0, Or.inr h⟩

/-- The predicate defining one step of the Kuratowski–Ryll-Nardzewski construction. -/
private def mselPred (U : Set V) (g : α → V → E) (d : ℕ → V) (D : ℝ) (j : ℕ) (s : α → V)
    (t : α) (i : ℕ) : Prop :=
  dist (d i) (s t) < D * (1 / 2) ^ j ∧ ∃ w ∈ U, dist (d i) w < D * (1 / 2) ^ (j + 1) ∧ g t w = 0

open Classical in
/-- One step of the Kuratowski–Ryll-Nardzewski construction. -/
private noncomputable def mselStep (U : Set V) (g : α → V → E) (d : ℕ → V) (D : ℝ) (j : ℕ)
    (s : α → V) : α → V :=
  fun t ↦ d (Nat.find (msel_exists_or (mselPred U g d D j s t)))

/-- The sequence of approximate selections. -/
private noncomputable def mselSeq (U : Set V) (g : α → V → E) (d : ℕ → V) (D : ℝ) :
    ℕ → α → V
  | 0 => fun _ ↦ d 0
  | j + 1 => mselStep U g d D j (mselSeq U g d D j)

section Construction

variable {U : Set V} {g : α → V → E} {d : ℕ → V} {D : ℝ}

omit [MeasurableSpace α] [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem mselStep_spec (hd : ∀ w ∈ U, ∀ ε > 0, ∃ i, dist (d i) w < ε) (j : ℕ)
    (s : α → V) (t : α) (w : V) (hwU : w ∈ U) (hw : dist (s t) w < D * (1 / 2) ^ j)
    (hgw : g t w = 0) :
    dist (mselStep U g d D j s t) (s t) < D * (1 / 2) ^ j ∧
      ∃ w' ∈ U, dist (mselStep U g d D j s t) w' < D * (1 / 2) ^ (j + 1) ∧ g t w' = 0 := by
  classical
  have hD : 0 < D * (1 / 2) ^ (j + 1) := by
    have : 0 < D * (1 / 2) ^ j := lt_of_le_of_lt dist_nonneg hw
    rw [pow_succ, ← mul_assoc]; positivity
  have hex : ∃ i, mselPred U g d D j s t i := by
    obtain ⟨i, hi⟩ := hd w hwU (min (D * (1 / 2) ^ (j + 1)) (D * (1 / 2) ^ j - dist (s t) w))
      (lt_min hD (sub_pos.2 hw))
    refine ⟨i, ?_, w, hwU, lt_of_lt_of_le hi (min_le_left _ _), hgw⟩
    calc dist (d i) (s t) ≤ dist (d i) w + dist w (s t) := dist_triangle _ _ _
      _ < (D * (1 / 2) ^ j - dist (s t) w) + dist (s t) w := by
          rw [dist_comm w]; exact add_lt_add_of_lt_of_le (lt_of_lt_of_le hi (min_le_right _ _))
            le_rfl
      _ = D * (1 / 2) ^ j := by ring
  have hspec := Nat.find_spec (msel_exists_or (mselPred U g d D j s t))
  rcases hspec with h | h
  · exact h
  · exact absurd hex h

omit [MeasurableSpace α] [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem mselSeq_spec (hd : ∀ w ∈ U, ∀ ε > 0, ∃ i, dist (d i) w < ε)
    (hdU : ∀ i, d i ∈ U) (hdiam : ∀ a ∈ U, ∀ b ∈ U, dist a b < D)
    (hex : ∀ t, ∃ w ∈ U, g t w = 0) (j : ℕ) (t : α) :
    ∃ w ∈ U, dist (mselSeq U g d D j t) w < D * (1 / 2) ^ j ∧ g t w = 0 := by
  induction j with
  | zero =>
    obtain ⟨w, hwU, hw⟩ := hex t
    exact ⟨w, hwU, by simpa [mselSeq] using hdiam _ (hdU 0) _ hwU, hw⟩
  | succ j ih =>
    obtain ⟨w, hwU, hw, hgw⟩ := ih
    exact (mselStep_spec hd j _ t w hwU hw hgw).2

omit [MeasurableSpace α] [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem mselSeq_mem (hdU : ∀ i, d i ∈ U) (j : ℕ) (t : α) : mselSeq U g d D j t ∈ U := by
  cases j with
  | zero => exact hdU 0
  | succ j => exact hdU _

omit [MeasurableSpace α] [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem dist_mselSeq_succ (hd : ∀ w ∈ U, ∀ ε > 0, ∃ i, dist (d i) w < ε)
    (hdU : ∀ i, d i ∈ U) (hdiam : ∀ a ∈ U, ∀ b ∈ U, dist a b < D)
    (hex : ∀ t, ∃ w ∈ U, g t w = 0) (j : ℕ) (t : α) :
    dist (mselSeq U g d D (j + 1) t) (mselSeq U g d D j t) < D * (1 / 2) ^ j := by
  obtain ⟨w, hwU, hw, hgw⟩ := mselSeq_spec hd hdU hdiam hex j t
  exact (mselStep_spec hd j _ t w hwU hw hgw).1

variable [MeasurableSpace V] [OpensMeasurableSpace V]

private theorem measurable_mselSeq (hU : IsCompact U) (hmeas : ∀ w ∈ U, Measurable fun t ↦ g t w)
    (hcont : ∀ t, ContinuousOn (g t) U) (j : ℕ) : Measurable (mselSeq U g d D j) := by
  classical
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    change Measurable fun t ↦
      d (Nat.find (msel_exists_or (mselPred U g d D j (mselSeq U g d D j) t)))
    refine measurable_from_nat.comp (measurable_find _ fun i ↦ ?_)
    have hP : ∀ i, MeasurableSet {t | mselPred U g d D j (mselSeq U g d D j) t i} := by
      intro i
      simp only [mselPred, ofPred_and]
      refine MeasurableSet.inter ?_ ?_
      · exact measurableSet_lt
          ((continuous_const.dist continuous_id).measurable.comp ih) measurable_const
      · exact measurableSet_setOf_exists_mem_dist_lt_and_eq_zero hU hmeas hcont (d i) _
    rw [ofPred_or]
    refine (hP i).union ?_
    have : {t | ¬ ∃ i', mselPred U g d D j (mselSeq U g d D j) t i'} =
        (⋃ i', {t | mselPred U g d D j (mselSeq U g d D j) t i'})ᶜ := by
      ext t; simp
    rw [this]
    exact (MeasurableSet.iUnion hP).compl

end Construction

variable [MeasurableSpace V] [BorelSpace V]

/-- **Measurable selection** (Kuratowski–Ryll-Nardzewski, for zero sets of Carathéodory
functions on a compact set): if `t ↦ g t w` is measurable for `w ∈ U`, `g t` is continuous on
the compact set `U` and has a zero in `U` for every `t`, then there is a measurable `σ` with
`σ t ∈ U` and `g t (σ t) = 0` for all `t`. -/
theorem exists_measurable_forall_mem_and_eq_zero {U : Set V} (hU : IsCompact U) {g : α → V → E}
    (hmeas : ∀ w ∈ U, Measurable fun t ↦ g t w) (hcont : ∀ t, ContinuousOn (g t) U)
    (hex : ∀ t, ∃ w ∈ U, g t w = 0) :
    ∃ σ : α → V, Measurable σ ∧ ∀ t, σ t ∈ U ∧ g t (σ t) = 0 := by
  rcases U.eq_empty_or_nonempty with rfl | hne
  · have : IsEmpty α := ⟨fun t ↦ by obtain ⟨w, hw, -⟩ := hex t; exact hw⟩
    exact ⟨fun t ↦ isEmptyElim t, Subsingleton.measurable, fun t ↦ isEmptyElim t⟩
  have : Nonempty U := hne.to_subtype
  have : SeparableSpace U := hU.isSeparable.separableSpace
  obtain ⟨d₀, hd₀⟩ := exists_dense_seq U
  set d : ℕ → V := fun i ↦ (d₀ i : V) with hd_def
  have hdU : ∀ i, d i ∈ U := fun i ↦ (d₀ i).2
  have hd : ∀ w ∈ U, ∀ ε > 0, ∃ i, dist (d i) w < ε := by
    intro w hw ε hε
    obtain ⟨i, hy⟩ := hd₀.exists_dist_lt ⟨w, hw⟩ hε
    exact ⟨i, by rw [dist_comm]; exact hy⟩
  obtain ⟨D₀, hD₀⟩ := Metric.isBounded_iff.1 hU.isBounded
  set D := D₀ + 1
  have hdiam : ∀ a ∈ U, ∀ b ∈ U, dist a b < D := fun a ha b hb ↦
    lt_of_le_of_lt (hD₀ ha hb) (lt_add_one _)
  set σ := mselSeq U g d D with hσ_def
  have hcauchy : ∀ t, ∃ v ∈ U, Tendsto (fun j ↦ σ j t) atTop (𝓝 v) := by
    intro t
    refine cauchySeq_tendsto_of_isComplete hU.isComplete (fun j ↦ mselSeq_mem hdU j t) ?_
    refine cauchySeq_of_le_geometric_two (C := 2 * D) fun j ↦ ?_
    rw [dist_comm]
    refine (dist_mselSeq_succ hd hdU hdiam hex j t).le.trans (le_of_eq ?_)
    rw [one_div_pow]; field_simp
  choose v hvU hv using hcauchy
  refine ⟨v, ?_, fun t ↦ ⟨hvU t, ?_⟩⟩
  · exact measurable_of_tendsto_metrizable (fun j ↦ measurable_mselSeq hU hmeas hcont j)
      (tendsto_pi_nhds.2 hv)
  · choose w hwU hw hgw using mselSeq_spec hd hdU hdiam hex
    have hclosed : IsClosed (U ∩ g t ⁻¹' {0}) :=
      (hcont t).preimage_isClosed_of_isClosed hU.isClosed isClosed_singleton
    have hlim : Tendsto (fun j ↦ w j t) atTop (𝓝 (v t)) := by
      refine (hv t).congr_dist ?_
      refine squeeze_zero (fun _ ↦ dist_nonneg) (fun j ↦ (hw j t).le) ?_
      have : Tendsto (fun j : ℕ ↦ D * (1 / 2 : ℝ) ^ j) atTop (𝓝 (D * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul D
      simpa using this
    exact (hclosed.mem_of_tendsto hlim (Eventually.of_forall fun j ↦ ⟨hwU j t, hgw j t⟩)).2

/-- **Measurable selection**, almost-everywhere version: if `g t` has a zero in the nonempty
compact set `U` for almost every `t`, there is a measurable `σ` with values in `U` such that
`g t (σ t) = 0` for almost every `t`. -/
theorem exists_measurable_forall_mem_ae_eq_zero {μ : Measure α} {U : Set V} (hU : IsCompact U)
    (hUne : U.Nonempty) {g : α → V → E} (hmeas : ∀ w ∈ U, Measurable fun t ↦ g t w)
    (hcont : ∀ t, ContinuousOn (g t) U) (hex : ∀ᵐ t ∂μ, ∃ w ∈ U, g t w = 0) :
    ∃ σ : α → V, Measurable σ ∧ (∀ t, σ t ∈ U) ∧ ∀ᵐ t ∂μ, g t (σ t) = 0 := by
  classical
  set G := {t | ∃ w ∈ U, g t w = 0} with hG_def
  have hG : MeasurableSet G := measurableSet_setOf_exists_mem_eq_zero hU hmeas hcont
  obtain ⟨σ, hσm, hσ⟩ := exists_measurable_forall_mem_and_eq_zero (g := fun t w ↦
      if t ∈ G then g t w else 0) hU
    (fun w hw ↦ Measurable.ite hG (hmeas w hw) measurable_const)
    (fun t ↦ by
      by_cases ht : t ∈ G
      · simpa [ht] using hcont t
      · simpa [ht] using continuousOn_const)
    (fun t ↦ by
      by_cases ht : t ∈ G
      · obtain ⟨w, hwU, hw⟩ := ht
        exact ⟨w, hwU, by simp [show t ∈ G from ⟨w, hwU, hw⟩, hw]⟩
      · obtain ⟨w, hwU⟩ := hUne
        exact ⟨w, hwU, by simp [ht]⟩)
  refine ⟨σ, hσm, fun t ↦ (hσ t).1, ?_⟩
  filter_upwards [hex] with t ht
  have := (hσ t).2
  simpa [show t ∈ G from ht] using this

end MeasureTheory
