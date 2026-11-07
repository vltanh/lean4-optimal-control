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

* `ControlSystem.IsAdmissible.timeChange`: the statement for `f` continuous on `E × U`;
* `ControlSystem.IsAdmissible.timeChangeOn`: the same for `f` and the cost continuous on
  `Ω × U` only, the trajectory staying in `Ω` (the form the maximum principle uses, where the
  data are given on an open set `Ω`);
* `ControlSystem.TimeChange.integral_comp_integral`: the change of variables
  `∫₀^{θ(T)} G = ∫₀ᵀ v · G ∘ θ` behind both.

## Proof

`θ` is strictly increasing and bi-Lipschitz (`c₁ (b - a) ≤ θ(b) - θ(a) ≤ c₂ (b - a)`,
`ControlSystem.TimeChange.mul_le_integral_sub`), so it has a continuous increasing inverse
(through the order isomorphism `[0, t₁] ≃o [0, θ(t₁)]`, `ControlSystem.TimeChange.exists_inverse`);
`u ∘ θ⁻¹` is measurable. The push-forward of `v · Leb|[0, T]` under `θ` is `Leb|[0, θ(T)]` (both
give `min(a, θ(T))` to `(-∞, a]`, `a ≥ 0`, by the intermediate value theorem), which is the change
of variables in both the integral equation and the cost. The substitution formula is proved
through this push-forward of measures because `θ' = v` holds only almost everywhere (A–S's
controls, hence `v`, are only measurable), while Mathlib's change-of-variables lemmas need a
derivative at every point of the interval.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace ControlSystem

namespace TimeChange

/-- A function continuous on a measurable set `s`, composed with an a.e.-measurable map with
values in `s` almost everywhere, is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_comp {X F : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X] [TopologicalSpace F]
    [TopologicalSpace.PseudoMetrizableSpace F] {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : X → F} {s : Set X} (hg : ContinuousOn g s) (hs : MeasurableSet s) {h : α → X}
    (hh : AEMeasurable h μ) (hmem : ∀ᵐ t ∂μ, h t ∈ s) :
    AEStronglyMeasurable (fun t ↦ g (h t)) μ := by
  have : (μ.map h).restrict s = μ.map h :=
    Measure.restrict_eq_self_of_ae_mem ((ae_map_iff hh hs).2 hmem)
  exact (this ▸ hg.aestronglyMeasurable hs).comp_aemeasurable hh

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup F]

/-- Along a curve `x` continuous on `[a, b]` and a measurable control `u`, with `(x(t), u(t))` in
`Ω × U` on `[a, b]`, `U` compact, a function `g` continuous on `Ω × U` gives an a.e.-strongly
measurable, bounded and integrable integrand `t ↦ g(x(t), u(t))` on `[a, b]`. -/
theorem integrand_bound {g : E → V → F} {Ω : Set E} {U : Set V} (hU : IsCompact U)
    (hg : ContinuousOn (fun p : E × V ↦ g p.1 p.2) (Ω ×ˢ U)) {x : ℝ → E} {u : ℝ → V} {a b : ℝ}
    (hab : a ≤ b) (hx : ContinuousOn x (Icc a b)) (hu : AEMeasurable u (volume.restrict (Icc a b)))
    (hmem : ∀ t ∈ Icc a b, x t ∈ Ω ∧ u t ∈ U) :
    AEStronglyMeasurable (fun t ↦ g (x t) (u t)) (volume.restrict (Icc a b)) ∧
      (∃ C, ∀ t ∈ Icc a b, ‖g (x t) (u t)‖ ≤ C) ∧
      IntervalIntegrable (fun t ↦ g (x t) (u t)) volume a b := by
  borelize E
  have hK : IsCompact ((x '' Icc a b) ×ˢ U) := (isCompact_Icc.image_of_continuousOn hx).prod hU
  have hKΩ : (x '' Icc a b) ×ˢ U ⊆ Ω ×ˢ U := fun p hp ↦ by
    obtain ⟨t, ht, hpt⟩ := hp.1
    exact ⟨hpt ▸ (hmem t ht).1, hp.2⟩
  have hgK := hg.mono hKΩ
  have hmeas : AEStronglyMeasurable (fun t ↦ g (x t) (u t)) (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_comp (g := fun p : E × V ↦ g p.1 p.2) hgK hK.measurableSet
      ((hx.aemeasurable measurableSet_Icc).prodMk hu)
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht ↦
        ⟨mem_image_of_mem x ht, (hmem t ht).2⟩))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hgK
  have hbd : ∀ t ∈ Icc a b, ‖g (x t) (u t)‖ ≤ C := fun t ht ↦
    hC (x t, u t) ⟨mem_image_of_mem x ht, (hmem t ht).2⟩
  refine ⟨hmeas, ⟨C, hbd⟩, ?_⟩
  have : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  refine IntegrableOn.intervalIntegrable ?_
  rw [uIcc_of_le hab]
  exact Integrable.of_bound hmeas C ((ae_restrict_iff' measurableSet_Icc).2
    (Eventually.of_forall hbd))

/-- A measurable time scaling with values in `[c₁, c₂]`, `c₁ > 0`, on `[0, T]` is integrable
on every subinterval. -/
theorem intervalIntegrable_of_mem_Icc {v : ℝ → ℝ} {T c₁ c₂ : ℝ} (hv : Measurable v)
    (hc₁ : 0 < c₁) (hvb : ∀ r ∈ Icc 0 T, v r ∈ Icc c₁ c₂) {a b : ℝ} (ha : a ∈ Icc 0 T)
    (hb : b ∈ Icc 0 T) : IntervalIntegrable v volume a b := by
  have : IntegrableOn v (Icc 0 T) := by
    have : IsFiniteMeasure (volume.restrict (Icc 0 T)) :=
      isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
    refine Integrable.of_bound hv.aestronglyMeasurable c₂ ((ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun r hr ↦ ?_))
    rw [Real.norm_eq_abs, abs_of_pos (hc₁.trans_le (hvb r hr).1)]
    exact (hvb r hr).2
  exact (this.mono_set (uIcc_subset_Icc ha hb)).intervalIntegrable

/-- The time `θ(t) = ∫₀ᵗ v` of a time scaling `v ∈ [c₁, c₂]` satisfies
`c₁ (b - a) ≤ θ(b) - θ(a) ≤ c₂ (b - a)` for `0 ≤ a ≤ b ≤ T`. -/
theorem mul_le_integral_sub {v : ℝ → ℝ} {T c₁ c₂ : ℝ} (hT : 0 ≤ T) (hv : Measurable v)
    (hc₁ : 0 < c₁) (hvb : ∀ r ∈ Icc 0 T, v r ∈ Icc c₁ c₂) {a b : ℝ} (ha : a ∈ Icc 0 T)
    (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
    c₁ * (b - a) ≤ (∫ r in (0 : ℝ)..b, v r) - ∫ r in (0 : ℝ)..a, v r ∧
      (∫ r in (0 : ℝ)..b, v r) - (∫ r in (0 : ℝ)..a, v r) ≤ c₂ * (b - a) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  rw [intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_of_mem_Icc hv hc₁ hvb h0 hb)
    (intervalIntegrable_of_mem_Icc hv hc₁ hvb h0 ha)]
  have hi := intervalIntegrable_of_mem_Icc hv hc₁ hvb ha hb
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha.1 hb.2
  constructor
  · have := intervalIntegral.integral_mono_on hab intervalIntegrable_const hi
      (fun r hr ↦ (hvb r (hsub hr)).1)
    simpa [mul_comm] using this
  · have := intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
      (fun r hr ↦ (hvb r (hsub hr)).2)
    simpa [mul_comm] using this

/-- The time `θ(t) = ∫₀ᵗ v` is continuous on `[0, T]`. -/
theorem continuousOn_integral {v : ℝ → ℝ} {T c₁ c₂ : ℝ} (hT : 0 ≤ T) (hv : Measurable v)
    (hc₁ : 0 < c₁) (hvb : ∀ r ∈ Icc 0 T, v r ∈ Icc c₁ c₂) :
    ContinuousOn (fun t ↦ ∫ r in (0 : ℝ)..t, v r) (Icc 0 T) := by
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
    (f := v) ?_
  · rwa [uIcc_of_le hT] at this
  · rw [uIcc_of_le hT]
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1
      (intervalIntegrable_of_mem_Icc hv hc₁ hvb h0 ⟨hT, le_rfl⟩)

/-- **Change of variables for a time scaling.** For a measurable `v` with values in `[c₁, c₂]`,
`c₁ > 0`, on `[0, T]` and `θ(t) = ∫₀ᵗ v`: `∫₀^{θ(T)} G(s) ds = ∫₀ᵀ v(r) G(θ(r)) dr` for every
`G` a.e.-strongly measurable on `[0, θ(T)]`.

Proof: the push-forward under `θ` of the measure `v · Leb` on `(0, T]` is `Leb` on `(0, θ(T)]`
(they agree on the half-lines `(-∞, a]`). -/
theorem integral_comp_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : ℝ → ℝ} {T c₁ c₂ : ℝ} (hT : 0 ≤ T) (hv : Measurable v) (hc₁ : 0 < c₁)
    (hvb : ∀ r ∈ Icc 0 T, v r ∈ Icc c₁ c₂) {G : ℝ → F}
    (hG : AEStronglyMeasurable G (volume.restrict (Ioc 0 (∫ r in (0 : ℝ)..T, v r)))) :
    ∫ s in (0 : ℝ)..(∫ r in (0 : ℝ)..T, v r), G s =
      ∫ r in (0 : ℝ)..T, v r • G (∫ r' in (0 : ℝ)..r, v r') := by
  set θ : ℝ → ℝ := fun t ↦ ∫ r in (0 : ℝ)..t, v r with hθdef
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hθ0 : θ 0 = 0 := intervalIntegral.integral_same
  have hθc : ContinuousOn θ (Icc 0 T) := continuousOn_integral hT hv hc₁ hvb
  have hbd := fun {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b) ↦
    mul_le_integral_sub hT hv hc₁ hvb ha hb hab
  have hθmono : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a ≤ b → θ a ≤ θ b := fun a ha b hb hab ↦ by
    have := (hbd ha hb hab).1
    nlinarith
  have hθsmono : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a < b → θ a < θ b := fun a ha b hb hab ↦ by
    have := (hbd ha hb hab.le).1
    nlinarith
  have hθT : 0 ≤ θ T := hθ0 ▸ hθmono 0 h0 T ⟨hT, le_rfl⟩ hT
  set μ : Measure ℝ := (volume.restrict (Ioc 0 T)).withDensity
    (fun r ↦ (((v r).toNNReal : ℝ≥0) : ℝ≥0∞)) with hμ
  have hθm : AEMeasurable θ μ :=
    ((hθc.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hmap : μ.map θ = volume.restrict (Ioc 0 (θ T)) := by
    have : IsFiniteMeasure (volume.restrict (Ioc 0 (θ T))) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    refine (Measure.ext_of_Iic _ _ fun a ↦ ?_).symm
    rw [Measure.map_apply_of_aemeasurable hθm measurableSet_Iic, hμ, withDensity_apply',
      Measure.restrict_restrict' measurableSet_Ioc, Measure.restrict_apply measurableSet_Iic]
    rcases lt_or_ge a 0 with ha | ha
    · have h1 : Iic a ∩ Ioc 0 (θ T) = ∅ :=
        eq_empty_of_forall_notMem fun s hs ↦ by linarith [hs.1, hs.2.1, mem_Iic.1 hs.1]
      have h2 : θ ⁻¹' Iic a ∩ Ioc 0 T = ∅ := eq_empty_of_forall_notMem fun r hr ↦ by
        have := hθsmono 0 h0 r ⟨hr.2.1.le, hr.2.2⟩ hr.2.1
        have : θ r ≤ a := hr.1
        linarith
      simp [h1, h2]
    · obtain ⟨t', ht', hθt'⟩ : min a (θ T) ∈ θ '' Icc 0 T :=
        intermediate_value_Icc hT hθc ⟨by simp [hθ0, ha, hθT], by simp⟩
      have h1 : Iic a ∩ Ioc 0 (θ T) = Ioc 0 (min a (θ T)) := by
        ext s; simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]; tauto
      have h2 : θ ⁻¹' Iic a ∩ Ioc 0 T = Ioc 0 t' := by
        ext r
        simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨hr, h0r, hrT⟩
          refine ⟨h0r, not_lt.1 fun hlt ↦ ?_⟩
          have h3 := hθsmono t' ht' r ⟨h0r.le, hrT⟩ hlt
          have h4 := hθmono r ⟨h0r.le, hrT⟩ T ⟨hT, le_rfl⟩ hrT
          have h5 : θ r ≤ min a (θ T) := le_min hr h4
          linarith
        · rintro ⟨h0r, hrt'⟩
          refine ⟨?_, h0r, hrt'.trans ht'.2⟩
          exact (hθmono r ⟨h0r.le, hrt'.trans ht'.2⟩ t' ht' hrt').trans
            (hθt'.symm ▸ min_le_left _ _)
      rw [h1, h2, Real.volume_Ioc, sub_zero]
      have hi : IntegrableOn v (Ioc 0 t') :=
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht'.1).1
          (intervalIntegrable_of_mem_Icc hv hc₁ hvb h0 ht'))
      have := ofReal_integral_eq_lintegral_ofReal hi
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr ↦
          (hc₁.trans_le (hvb r ⟨hr.1.le, hr.2.trans ht'.2⟩).1).le))
      rw [← intervalIntegral.integral_of_le ht'.1] at this
      change ENNReal.ofReal (min a (θ T)) = ∫⁻ r in Ioc 0 t', ENNReal.ofReal (v r)
      rw [← this, ← hθt']
  have hG' : AEStronglyMeasurable G (μ.map θ) := hmap ▸ hG
  rw [intervalIntegral.integral_of_le hθT, intervalIntegral.integral_of_le hT, ← hmap,
    integral_map hθm hG', hμ, integral_withDensity_eq_integral_smul hv.real_toNNReal]
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr ↦ ?_
  simp only [NNReal.smul_def]
  rw [Real.coe_toNNReal _ (hc₁.trans_le (hvb r (Ioc_subset_Icc_self hr)).1).le]

/-- A continuous strictly increasing `θ` on `[0, T]` with `θ(0) = 0` has a continuous monotone
inverse `θ⁻¹ : ℝ → [0, T]` (constant outside `[0, θ(T)]`). -/
theorem exists_inverse {θ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hθ0 : θ 0 = 0)
    (hθc : ContinuousOn θ (Icc 0 T)) (hθsmono : StrictMonoOn θ (Icc 0 T)) :
    ∃ θinv : ℝ → ℝ, Continuous θinv ∧ Monotone θinv ∧ (∀ s, θinv s ∈ Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, θinv (θ t) = t) ∧ (∀ s ∈ Icc 0 (θ T), θ (θinv s) = s) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hTT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hmem : ∀ t ∈ Icc 0 T, θ t ∈ Icc 0 (θ T) := fun t ht ↦
    ⟨hθ0 ▸ hθsmono.monotoneOn h0 ht ht.1, hθsmono.monotoneOn ht hTT ht.2⟩
  have hθT : 0 ≤ θ T := (hmem T hTT).1
  let e : Icc 0 T → Icc 0 (θ T) := fun t ↦ ⟨θ t, hmem t t.2⟩
  have he : StrictMono e := fun a b hab ↦ hθsmono a.2 b.2 hab
  have hes : Function.Surjective e := fun s ↦ by
    have hs : (s : ℝ) ∈ Icc (θ 0) (θ T) := by rw [hθ0]; exact s.2
    obtain ⟨t, ht, hts⟩ := intermediate_value_Icc hT hθc hs
    exact ⟨⟨t, ht⟩, Subtype.ext hts⟩
  let iso := StrictMono.orderIsoOfSurjective e he hes
  refine ⟨fun s ↦ (iso.symm (projIcc 0 (θ T) hθT s) : ℝ),
    continuous_subtype_val.comp (iso.symm.continuous.comp continuous_projIcc),
    fun a b hab ↦ Subtype.mono_coe _ (iso.symm.monotone (monotone_projIcc _ hab)),
    fun s ↦ (iso.symm _).2, fun t ht ↦ ?_, fun s hs ↦ ?_⟩
  · have : projIcc 0 (θ T) hθT (θ t) = e ⟨t, ht⟩ := projIcc_of_mem _ (hmem t ht)
    simp only [this, iso, StrictMono.orderIsoOfSurjective_symm_apply_self]
  · have := iso.apply_symm_apply (projIcc 0 (θ T) hθT s)
    rw [projIcc_of_mem _ hs] at this
    change θ (iso.symm (projIcc 0 (θ T) hθT s) : ℝ) = s
    rw [projIcc_of_mem _ hs]
    exact congrArg Subtype.val this

end TimeChange

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The integrands along the reparametrized pair `(u ∘ θ⁻¹, x ∘ θ⁻¹)`: measurability,
boundedness and the change of variables `∫₀^{θ(t)} g(x ∘ θ⁻¹, u ∘ θ⁻¹) = ∫₀ᵗ v g(x, u)`. -/
private theorem timeChange_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set E} {U : Set V} (hU : IsCompact U) {g : E → V → F}
    (hg : ContinuousOn (fun p : E × V ↦ g p.1 p.2) (Ω ×ˢ U)) {c₁ c₂ t₁ : ℝ} (hc₁ : 0 < c₁)
    {w : ℝ → ℝ × V} {x : ℝ → E} (hwm : Measurable w)
    (hwU : ∀ t ∈ Icc 0 t₁, w t ∈ Icc c₁ c₂ ×ˢ U) (hxc : ContinuousOn x (Icc 0 t₁))
    (hxΩ : ∀ t ∈ Icc 0 t₁, x t ∈ Ω) {θinv : ℝ → ℝ} (hθc : Continuous θinv)
    (hθmem : ∀ s, θinv s ∈ Icc 0 t₁)
    (hθl : ∀ t ∈ Icc 0 t₁, θinv (∫ r in (0 : ℝ)..t, (w r).1) = t) :
    (∀ μ : Measure ℝ, AEStronglyMeasurable (fun s ↦ g (x (θinv s)) (w (θinv s)).2) μ) ∧
      (∃ C, ∀ s, ‖g (x (θinv s)) (w (θinv s)).2‖ ≤ C) ∧
      ∀ t ∈ Icc 0 t₁,
        ∫ s in (0 : ℝ)..(∫ r in (0 : ℝ)..t, (w r).1), g (x (θinv s)) (w (θinv s)).2 =
          ∫ r in (0 : ℝ)..t, (w r).1 • g (x r) (w r).2 := by
  borelize E
  have hv : Measurable fun r ↦ (w r).1 := measurable_fst.comp hwm
  have hvb : ∀ r ∈ Icc 0 t₁, (w r).1 ∈ Icc c₁ c₂ := fun r hr ↦ (hwU r hr).1
  have hxθ : Continuous fun s ↦ x (θinv s) := hxc.comp_continuous hθc hθmem
  have huθ : Measurable fun s ↦ (w (θinv s)).2 := (measurable_snd.comp hwm).comp hθc.measurable
  have hK : IsCompact ((x '' Icc 0 t₁) ×ˢ U) := (isCompact_Icc.image_of_continuousOn hxc).prod hU
  have hKΩ : (x '' Icc 0 t₁) ×ˢ U ⊆ Ω ×ˢ U := fun p hp ↦ by
    obtain ⟨t, ht, hpt⟩ := hp.1
    exact ⟨hpt ▸ hxΩ t ht, hp.2⟩
  have hKmem : ∀ s, (x (θinv s), (w (θinv s)).2) ∈ (x '' Icc 0 t₁) ×ˢ U := fun s ↦
    ⟨mem_image_of_mem x (hθmem s), (hwU _ (hθmem s)).2⟩
  have hmeas : ∀ μ : Measure ℝ,
      AEStronglyMeasurable (fun s ↦ g (x (θinv s)) (w (θinv s)).2) μ := fun μ ↦
    TimeChange.aestronglyMeasurable_comp (g := fun p : E × V ↦ g p.1 p.2) (hg.mono hKΩ)
      hK.measurableSet (hxθ.measurable.prodMk huθ).aemeasurable (Eventually.of_forall hKmem)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hg.mono hKΩ)
  refine ⟨hmeas, ⟨C, fun s ↦ hC _ (hKmem s)⟩, fun t ht ↦ ?_⟩
  refine (TimeChange.integral_comp_integral (G := fun s ↦ g (x (θinv s)) (w (θinv s)).2)
    ht.1 hv hc₁ (fun r hr ↦ hvb r ⟨hr.1, hr.2.trans ht.2⟩) (hmeas _)).trans
    (intervalIntegral.integral_congr fun r hr ↦ ?_)
  rw [uIcc_of_le ht.1] at hr
  simp only [hθl r ⟨hr.1, hr.2.trans ht.2⟩]

/-- **Change of time, on an open set** (the form of `IsAdmissible.timeChange` that the maximum
principle uses). An admissible pair `((v, u), x)` on `[0, t₁]` of the time-scaled system
`x' = v f(x, u)`, `(v, u) ∈ [c₁, c₂] × U`, `c₁ > 0`, with `x` in `Ω` and `f` continuous on
`Ω × U`, is a reparametrization of an admissible pair of `x' = f(x, u)` on `[0, θ(t₁)]`,
`θ(t) = ∫₀ᵗ v`: there is a continuous monotone `θ⁻¹ : ℝ → [0, t₁]`, inverse to `θ` between
`[0, t₁]` and `[0, θ(t₁)]`, such that `(u ∘ θ⁻¹, x ∘ θ⁻¹)` is admissible and
`∫₀^{t₁} v φ(x, u) = ∫₀^{θ(t₁)} φ(x ∘ θ⁻¹, u ∘ θ⁻¹)` for every cost `φ` continuous on `Ω × U`. -/
theorem IsAdmissible.timeChangeOn {f : E → V → E} {Ω : Set E} {U : Set V} (hU : IsCompact U)
    (hf : ContinuousOn (fun p : E × V ↦ f p.1 p.2) (Ω ×ˢ U)) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    {x₀ : E} {t₁ : ℝ} (ht₁ : 0 ≤ t₁) {w : ℝ → ℝ × V} {x : ℝ → E}
    (h : IsAdmissible (fun y p ↦ p.1 • f y p.2) (Icc c₁ c₂ ×ˢ U) x₀ t₁ w x)
    (hxΩ : ∀ t ∈ Icc 0 t₁, x t ∈ Ω) :
    ∃ θinv : ℝ → ℝ, Continuous θinv ∧ Monotone θinv ∧ (∀ s, θinv s ∈ Icc 0 t₁) ∧
      (∀ t ∈ Icc 0 t₁, θinv (∫ r in (0 : ℝ)..t, (w r).1) = t) ∧
      (∀ s ∈ Icc 0 (∫ r in (0 : ℝ)..t₁, (w r).1), ∫ r in (0 : ℝ)..θinv s, (w r).1 = s) ∧
      IsAdmissible f U x₀ (∫ r in (0 : ℝ)..t₁, (w r).1) (fun s ↦ (w (θinv s)).2)
        (fun s ↦ x (θinv s)) ∧
      ∀ φ : E → V → ℝ, ContinuousOn (fun p : E × V ↦ φ p.1 p.2) (Ω ×ˢ U) →
        ∫ t in (0 : ℝ)..t₁, (w t).1 * φ (x t) (w t).2 =
          ∫ s in (0 : ℝ)..(∫ r in (0 : ℝ)..t₁, (w r).1), φ (x (θinv s)) (w (θinv s)).2 := by
  obtain ⟨hwm, hwU, hxc, -, hxeq⟩ := h
  have hv : Measurable fun r ↦ (w r).1 := measurable_fst.comp hwm
  have hvb : ∀ r ∈ Icc 0 t₁, (w r).1 ∈ Icc c₁ c₂ := fun r hr ↦ (hwU r hr).1
  have h0 : (0 : ℝ) ∈ Icc 0 t₁ := ⟨le_rfl, ht₁⟩
  have hθc := TimeChange.continuousOn_integral ht₁ hv hc₁ hvb
  have hθs : StrictMonoOn (fun t ↦ ∫ r in (0 : ℝ)..t, (w r).1) (Icc 0 t₁) :=
    fun a ha b hb hab ↦ by
      have := (TimeChange.mul_le_integral_sub ht₁ hv hc₁ hvb ha hb hab.le).1
      simp only
      nlinarith
  have hθT : 0 ≤ ∫ r in (0 : ℝ)..t₁, (w r).1 := by
    have := (TimeChange.mul_le_integral_sub ht₁ hv hc₁ hvb h0 ⟨ht₁, le_rfl⟩ ht₁).1
    rw [intervalIntegral.integral_same, sub_zero] at this
    nlinarith
  obtain ⟨θinv, hθc', hθm, hθmem, hθl, hθr⟩ :=
    TimeChange.exists_inverse ht₁ intervalIntegral.integral_same hθc hθs
  obtain ⟨hmeasf, ⟨C, hC⟩, hcvf⟩ :=
    timeChange_comp hU hf hc₁ hwm hwU hxc hxΩ hθc' hθmem hθl
  have hxθ : Continuous fun s ↦ x (θinv s) := hxc.comp_continuous hθc' hθmem
  have huθ : Measurable fun s ↦ (w (θinv s)).2 := (measurable_snd.comp hwm).comp hθc'.measurable
  refine ⟨θinv, hθc', hθm, hθmem, hθl, hθr,
    ⟨huθ, fun s _ ↦ (hwU _ (hθmem s)).2, hxθ.continuousOn, ?_, fun s hs ↦ ?_⟩, fun φ hφ ↦ ?_⟩
  · have : IsFiniteMeasure (volume.restrict (Icc 0 (∫ r in (0 : ℝ)..t₁, (w r).1))) :=
      isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
    refine IntegrableOn.intervalIntegrable ?_
    rw [uIcc_of_le hθT]
    exact Integrable.of_bound (hmeasf _) C (Eventually.of_forall hC)
  · have ht := hθmem s
    simp only at hxeq ⊢
    rw [hxeq _ ht, ← hcvf _ ht, hθr s hs]
  · rw [(timeChange_comp hU hφ hc₁ hwm hwU hxc hxΩ hθc' hθmem hθl).2.2 t₁ ⟨ht₁, le_rfl⟩]
    simp only [smul_eq_mul]

/-- **Change of time.** An admissible pair `((v, u), x)` on `[0, t₁]` of the time-scaled system
`x' = v f(x, u)`, `(v, u) ∈ [c₁, c₂] × U`, `c₁ > 0`, is a reparametrization of an admissible
pair of `x' = f(x, u)` on `[0, θ(t₁)]`, `θ(t) = ∫₀ᵗ v`: there is a continuous monotone `θ⁻¹`,
inverse to `θ` between `[0, t₁]` and `[0, θ(t₁)]`, such that `(u ∘ θ⁻¹, x ∘ θ⁻¹)` is admissible
and `∫₀^{t₁} v φ(x, u) = ∫₀^{θ(t₁)} φ(x ∘ θ⁻¹, u ∘ θ⁻¹)` for every continuous cost `φ`.

Proof: the case `Ω = E` of `IsAdmissible.timeChangeOn`. -/
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
  obtain ⟨θinv, hc, hm, hmem, hl, hr, hadm, hcost⟩ :=
    h.timeChangeOn hU hf hc₁ ht₁ fun _ _ ↦ mem_univ _
  exact ⟨θinv, hc, hm, hl, fun s hs ↦ ⟨hmem s, hr s hs⟩, hadm, hcost⟩

end ControlSystem
