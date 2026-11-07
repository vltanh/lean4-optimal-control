module

public import OptimalControl.ODE.VariationsFormula

/-!
# Needle variations

Agrachev–Sachkov's needle-like variations (authors' draft, (12.14), p. 171): for distinct times
`τ₁, …, τ_k ∈ [0, t₁)`, control values `w₁, …, w_k ∈ U` and `σ ∈ ℝᵏ₊`, the control
`u_σ = wᵢ` on `[τᵢ, τᵢ + σᵢ)` and `u_σ = ũ` elsewhere (`ControlSystem.needleControl`). Together
with a variation `ψ(a)` of the initial point (the proof of A–S's Theorem 12.4 (2), p. 181), the
end-point map `F(a, σ) = P^{u_σ}_{0 → t₁}(ψ(a))` is studied near `(a₀, 0)` on the convex cone
`L × ℝᵏ₊`. This file states the claims that A–S make about `F` in the proofs of Lemma 12.2
(p. 172: "The mapping `F` … is Lipschitzian, differentiable at `s = 0`, and
`∂F/∂sᵢ|_{s=0} = g_{τᵢ,uᵢ}(q₁)`") and Theorem 12.4 (2) (p. 182, `∂F/∂q v = Φ_* P^{t₁}_* v`):

* `u_σ` is a control on `[0, t₁]` (`ControlSystem.isControlOn_needleControl`);
* `F` is Lipschitz near `(a₀, 0)` on the cone (`ControlSystem.lipschitzOnWith_needle`);
* `F` is differentiable at `(a₀, 0)` within the cone, with derivative
  `(α, σ) ↦ D_x P_{0 → t₁}(ψ(a₀)) Dψ(a₀) α + Σᵢ σᵢ g_{τᵢ,wᵢ}(q₁)`, `q₁ = P_{0 → t₁}(ψ(a₀))`
  (`ControlSystem.hasFDerivWithinAt_needle`);
* the varied trajectories are uniformly close to the reference trajectory
  (`ControlSystem.norm_needle_trajectory_sub_lt`), so that they stay where the system is defined
  and in the neighbourhoods of strong local optimality.

The intervals are half-open, `[τᵢ, τᵢ + σᵢ)`, so that `u_0 = ũ` exactly (A–S write `[τᵢ, τᵢ + sᵢ]`;
the difference is a null set). The needle times must be Lebesgue points of `ũ`.

## Source and reading

Agrachev–Sachkov, §12.2, (12.14) and the proof of Lemma 12.2 (pp. 171–172), and the proof of
Theorem 12.4 (2) (pp. 181–182), read pointwise in coordinates (departure D2), for a globally
bounded `C¹` system (after the cut-off, D11).

## Proof (A–S's route)

A–S state the three properties of `F` without proof (p. 172). The proofs here:

* by the variations formula (`ControlSystem.flow_flow_eq_add_integral_variationField`) with
  `g_{t,ũ(t)} = 0`, for `σ ∈ ℝᵏ₊` small (the intervals disjoint and in `[0, t₁)`),
  `F(a, σ) = P_{0 → t₁}(ψ(a)) + Σᵢ ∫_{τᵢ}^{τᵢ+σᵢ} g_{t,wᵢ}(y(t)) dt`, with `y` the transported
  trajectory (A–S's formula for `q_{u_s}(t₁)`, p. 171);
* the first term has derivative `D_x P_{0 → t₁}(ψ(a₀)) Dψ(a₀)` (`ControlSystem.contDiff_flow`,
  A–S's (2.19)); in the `i`-th integral, `g_{t,wᵢ}(z) = G(t, z, ũ(t))` with `G` continuous on
  `[0, t₁] × E × U` (`ControlSystem.continuousOn_flow`, `ControlSystem.continuousOn_fderiv_flow`),
  hence uniformly continuous near `(τᵢ, q₁)`; `y(t)` is close to `q₁`
  (`ControlSystem.norm_needle_trajectory_sub_lt`); and at the Lebesgue point `τᵢ`,
  `σᵢ⁻¹ ∫_{τᵢ}^{τᵢ+σᵢ} ‖G(τᵢ, q₁, ũ(t)) - G(τᵢ, q₁, ũ(τᵢ))‖ dt → 0`
  (`IsLebesguePointWithin.eventually_integral_le`). So the `i`-th integral is
  `σᵢ g_{τᵢ,wᵢ}(q₁) + o(σᵢ)`;
* Lipschitz continuity and closeness: the comparison estimate
  `ControlSystem.norm_flow_sub_flow_control_le`, since the controls `u_σ`, `u_σ'` differ only on
  `⋃ᵢ [τᵢ + min(σᵢ, σ'ᵢ), τᵢ + max(σᵢ, σ'ᵢ))`, of measure `≤ Σᵢ |σᵢ - σ'ᵢ|`, and `ψ` is
  Lipschitz near `a₀` (`C¹`) or continuous at `a₀`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V]

open Classical in
/-- The needle control (12.14) of Agrachev–Sachkov: `wᵢ` on `[τᵢ, τᵢ + σᵢ)` (the first such `i`
if the intervals overlap), `ũ` elsewhere. -/
noncomputable def needleControl (ũ : ℝ → V) {k : ℕ} (τ : Fin k → ℝ) (w : Fin k → V)
    (σ : Fin k → ℝ) : ℝ → V :=
  fun t ↦ if h : ∃ i, t ∈ Ico (τ i) (τ i + σ i) then w (Fin.find _ h) else ũ t

omit [NormedAddCommGroup V] in
/-- `u_0 = ũ`. -/
theorem needleControl_zero (ũ : ℝ → V) {k : ℕ} (τ : Fin k → ℝ) (w : Fin k → V) :
    needleControl ũ τ w 0 = ũ := by
  funext t
  simp [needleControl]

/-- The orthant `ℝᵏ₊ = {σ | ∀ i, 0 ≤ σᵢ}`. -/
def orthant (k : ℕ) : Set (Fin k → ℝ) := {σ | ∀ i, 0 ≤ σ i}

variable {f : E → V → E} {U : Set V} {M L : ℝ≥0} {ũ : ℝ → V} {t₁ : ℝ} {k : ℕ}
  {τ : Fin k → ℝ} {w : Fin k → V}

omit [NormedAddCommGroup V] in
/-- At a time `t` of the `i`-th interval and of no earlier one, `u_σ(t) = wᵢ`. -/
private theorem needleControl_eq_of_mem {σ : Fin k → ℝ} {t : ℝ} {i : Fin k}
    (hi : t ∈ Ico (τ i) (τ i + σ i)) (hmin : ∀ j < i, t ∉ Ico (τ j) (τ j + σ j)) :
    needleControl ũ τ w σ t = w i := by
  have h : ∃ j, t ∈ Ico (τ j) (τ j + σ j) := ⟨i, hi⟩
  simp only [needleControl, dite_eq_left h]
  exact congrArg w ((Fin.find_eq_iff h).2 ⟨hi, hmin⟩)

omit [NormedAddCommGroup V] in
/-- Outside the intervals, `u_σ(t) = ũ(t)`. -/
private theorem needleControl_eq_of_forall_notMem {σ : Fin k → ℝ} {t : ℝ}
    (h : ∀ i, t ∉ Ico (τ i) (τ i + σ i)) : needleControl ũ τ w σ t = ũ t := by
  have h' : ¬ ∃ i, t ∈ Ico (τ i) (τ i + σ i) := fun ⟨i, hi⟩ ↦ h i hi
  simp only [needleControl, dite_eq_right h']

omit [NormedAddCommGroup V] in
/-- `u_σ(t) = u_σ'(t)` when `t` lies in the same intervals for `σ` and `σ'`. -/
private theorem needleControl_eq_of_forall_iff {σ σ' : Fin k → ℝ} {t : ℝ}
    (h : ∀ i, t ∈ Ico (τ i) (τ i + σ i) ↔ t ∈ Ico (τ i) (τ i + σ' i)) :
    needleControl ũ τ w σ t = needleControl ũ τ w σ' t := by
  classical
  by_cases hex : ∃ i, t ∈ Ico (τ i) (τ i + σ i)
  · have hi := Fin.find_spec hex
    have hmin : ∀ j < Fin.find _ hex, t ∉ Ico (τ j) (τ j + σ j) := fun j hj ↦ Fin.find_min hex hj
    rw [needleControl_eq_of_mem hi hmin,
      needleControl_eq_of_mem ((h _).1 hi) fun j hj ↦ by rw [← h j]; exact hmin j hj]
  · simp only [not_exists] at hex
    rw [needleControl_eq_of_forall_notMem hex,
      needleControl_eq_of_forall_notMem fun i hi ↦ hex i ((h i).2 hi)]

omit [NormedAddCommGroup V] in
/-- `u_σ` and `u_σ'` agree outside `⋃ᵢ [τᵢ + min(σᵢ, σ'ᵢ), τᵢ + max(σᵢ, σ'ᵢ))`. -/
private theorem needleControl_eq_of_notMem {σ σ' : Fin k → ℝ} {t : ℝ}
    (ht : t ∉ ⋃ i, Ico (τ i + min (σ i) (σ' i)) (τ i + max (σ i) (σ' i))) :
    needleControl ũ τ w σ t = needleControl ũ τ w σ' t := by
  refine needleControl_eq_of_forall_iff fun i ↦ ?_
  simp only [mem_iUnion, not_exists, mem_Ico, not_and, not_lt] at ht
  have hti := ht i
  simp only [mem_Ico]
  rcases le_total (σ i) (σ' i) with h | h
  · rw [min_eq_left h, max_eq_right h] at hti
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_not_ge fun h3 ↦ (hti h3).not_gt h2⟩
  · rw [min_eq_right h, max_eq_left h] at hti
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_not_ge fun h3 ↦ (hti h3).not_gt h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

omit [NormedAddCommGroup V] in
private theorem needleControl_mem (hw : ∀ i, w i ∈ U) {σ : Fin k → ℝ} {t : ℝ} (ht : ũ t ∈ U) :
    needleControl ũ τ w σ t ∈ U := by
  unfold needleControl
  split_ifs
  exacts [hw _, ht]

/-- A needle control is a control on `[0, t₁]` when `ũ` is and the values `wᵢ` lie in `U`. -/
theorem isControlOn_needleControl (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U)
    (σ : Fin k → ℝ) : IsControlOn (needleControl ũ τ w σ) U 0 t₁ := by
  classical
  refine ⟨?_, fun t ht ↦ needleControl_mem hw (hũ.mem t ht)⟩
  -- `u_σ = ũ + Σᵢ 1_{Aᵢ} (wᵢ - ũ)`, `Aᵢ` the times of the `i`-th interval and of no earlier one
  set A : Fin k → Set ℝ := fun i ↦
    Ico (τ i) (τ i + σ i) ∩ ⋂ j, ⋂ (_ : j < i), (Ico (τ j) (τ j + σ j))ᶜ with hAdef
  have hA : ∀ i, MeasurableSet (A i) := fun i ↦ measurableSet_Ico.inter
    (MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun _ ↦ measurableSet_Ico.compl)
  have hmemA : ∀ i t, t ∈ A i ↔ t ∈ Ico (τ i) (τ i + σ i) ∧ ∀ j < i, t ∉ Ico (τ j) (τ j + σ j) :=
    fun i t ↦ by simp [hAdef, -mem_Ico]
  have heq : needleControl ũ τ w σ = fun t ↦ ũ t + ∑ i, (A i).indicator (fun t ↦ w i - ũ t) t := by
    funext t
    by_cases hex : ∃ i, t ∈ Ico (τ i) (τ i + σ i)
    · have hi := Fin.find_spec hex
      have hmin : ∀ j < Fin.find _ hex, t ∉ Ico (τ j) (τ j + σ j) :=
        fun j hj ↦ Fin.find_min hex hj
      rw [needleControl_eq_of_mem hi hmin, Finset.sum_eq_single (Fin.find _ hex)]
      · rw [indicator_of_mem ((hmemA _ t).2 ⟨hi, hmin⟩)]
        abel
      · intro j _ hj
        refine indicator_of_notMem (fun hjA ↦ ?_) _
        obtain ⟨hjt, hjmin⟩ := (hmemA j t).1 hjA
        rcases lt_or_gt_of_ne hj with hlt | hgt
        · exact hmin j hlt hjt
        · exact hjmin _ hgt hi
      · simp
    · simp only [not_exists] at hex
      rw [needleControl_eq_of_forall_notMem hex, Finset.sum_eq_zero, add_zero]
      exact fun i _ ↦ indicator_of_notMem (fun h ↦ hex i ((hmemA i t).1 h).1) _
  rw [heq]
  exact hũ.aestronglyMeasurable.add (Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
    (aestronglyMeasurable_const.sub hũ.aestronglyMeasurable).indicator (hA i))

omit [FiniteDimensional ℝ E] in
/-- The velocities of two needle controls along any curve `y` differ by at most `2M` on a set of
measure at most `Σᵢ |σᵢ - σ'ᵢ|`. -/
private theorem integral_norm_needle_sub_le (hf : IsBoundedC1System f U M L)
    (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U) (σ σ' : Fin k → ℝ) (y : ℝ → E) {t : ℝ}
    (ht : t ∈ Icc 0 t₁) :
    ∫ r in 0..t, ‖f (y r) (needleControl ũ τ w σ r) - f (y r) (needleControl ũ τ w σ' r)‖ ≤
      2 * M * ∑ i, |σ i - σ' i| := by
  set D := ⋃ i, Ico (τ i + min (σ i) (σ' i)) (τ i + max (σ i) (σ' i)) with hDdef
  have hDm : MeasurableSet D := MeasurableSet.iUnion fun i ↦ measurableSet_Ico
  have hvol : volume D ≤ ENNReal.ofReal (∑ i, |σ i - σ' i|) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ abs_nonneg _]
    refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [Real.volume_Ico, add_sub_add_left_eq_sub, max_sub_min_eq_abs, abs_sub_comm]
  rw [intervalIntegral.integral_of_le ht.1]
  calc ∫ r in Ioc 0 t,
        ‖f (y r) (needleControl ũ τ w σ r) - f (y r) (needleControl ũ τ w σ' r)‖
      ≤ ∫ r in Ioc 0 t, D.indicator (fun _ ↦ 2 * (M : ℝ)) r := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun r ↦ norm_nonneg _)
          ((integrable_const _).indicator hDm) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun r hr ↦ ?_)
        have hrI : r ∈ Icc 0 t₁ := ⟨hr.1.le, hr.2.trans ht.2⟩
        by_cases hrD : r ∈ D
        · rw [indicator_of_mem hrD]
          calc ‖f (y r) (needleControl ũ τ w σ r) - f (y r) (needleControl ũ τ w σ' r)‖
              ≤ ‖f (y r) (needleControl ũ τ w σ r)‖ + ‖f (y r) (needleControl ũ τ w σ' r)‖ :=
                norm_sub_le _ _
            _ ≤ M + M := add_le_add (hf.norm_le _ _ (needleControl_mem hw (hũ.mem r hrI)))
                (hf.norm_le _ _ (needleControl_mem hw (hũ.mem r hrI)))
            _ = 2 * M := by ring
        · dsimp only
          rw [indicator_of_notMem hrD, needleControl_eq_of_notMem hrD, sub_self, norm_zero]
    _ = (volume.restrict (Ioc 0 t)).real D * (2 * M) := by
        rw [integral_indicator_const _ hDm, smul_eq_mul]
    _ ≤ (∑ i, |σ i - σ' i|) * (2 * M) := by
        gcongr
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal (by positivity)
          ((Measure.restrict_apply_le _ _).trans hvol)
    _ = 2 * M * ∑ i, |σ i - σ' i| := by ring

/-- Comparison of the trajectories of two needle controls:
`‖P^{u_σ}_{0 → t}(x) - P^{u_σ'}_{0 → t}(x')‖ ≤ e^{L t₁} (‖x - x'‖ + 2M Σᵢ |σᵢ - σ'ᵢ|)`. -/
private theorem norm_flow_needle_sub_le (hf : IsBoundedC1System f U M L)
    (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U) (σ σ' : Fin k → ℝ) (x x' : E) {t : ℝ}
    (ht : t ∈ Icc 0 t₁) :
    ‖flow f (needleControl ũ τ w σ) 0 t x - flow f (needleControl ũ τ w σ') 0 t x'‖ ≤
      Real.exp (L * t₁) * (‖x - x'‖ + 2 * M * ∑ i, |σ i - σ' i|) := by
  have h0 : (0 : ℝ) ∈ Icc 0 t₁ := ⟨le_rfl, ht.1.trans ht.2⟩
  refine (norm_flow_sub_flow_control_le hf.isLipschitzSystem (isControlOn_needleControl hũ hw σ)
    (isControlOn_needleControl hũ hw σ') h0 ht x x').trans ?_
  rw [sub_zero, abs_of_nonneg ht.1,
    abs_of_nonneg (intervalIntegral.integral_nonneg ht.1 fun r _ ↦ norm_nonneg _)]
  refine mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 L.2))
    (add_le_add le_rfl (integral_norm_needle_sub_le hf hũ hw σ σ' _ ht))
    (add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg ht.1 fun r _ ↦ norm_nonneg _))
    (Real.exp_pos _).le

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ψ : P → E} {a₀ : P}

/-- The end-point map of needle variations is Lipschitz near `(a₀, 0)` on the cone `P × ℝᵏ₊`
(Agrachev–Sachkov, p. 172: "is Lipschitzian"). -/
theorem lipschitzOnWith_needle (hf : IsBoundedC1System f U M L) (ht₁ : 0 < t₁)
    (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U) (hψ : ContDiffAt ℝ 1 ψ a₀) :
    ∃ ρ > 0, ∃ K, LipschitzOnWith K
      (fun p : P × (Fin k → ℝ) ↦ flow f (needleControl ũ τ w p.2) 0 t₁ (ψ p.1))
      ((univ ×ˢ orthant k) ∩ ball (a₀, 0) ρ) := by
  obtain ⟨K, T, hT, hK⟩ := hψ.exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hρT⟩ := Metric.mem_nhds_iff.1 hT
  refine ⟨ρ, hρ, Real.toNNReal (Real.exp (L * t₁) * (K + 2 * M * k)),
    LipschitzOnWith.of_dist_le' fun p hp p' hp' ↦ ?_⟩
  have hmem : ∀ q ∈ (univ ×ˢ orthant k) ∩ ball ((a₀, 0) : P × (Fin k → ℝ)) ρ, q.1 ∈ T := by
    intro q hq
    refine hρT ?_
    have := hq.2
    rw [mem_ball, Prod.dist_eq] at this
    exact mem_ball.2 ((le_max_left _ _).trans_lt this)
  have h1 : ‖ψ p.1 - ψ p'.1‖ ≤ K * dist p p' := by
    rw [← dist_eq_norm]
    exact (hK.dist_le_mul _ (hmem p hp) _ (hmem p' hp')).trans
      (mul_le_mul_of_nonneg_left (by rw [Prod.dist_eq]; exact le_max_left _ _) K.2)
  have h2 : ∑ i, |p.2 i - p'.2 i| ≤ k * dist p p' := by
    have : ∀ i, |p.2 i - p'.2 i| ≤ dist p p' := fun i ↦ by
      rw [← Real.dist_eq]
      exact (dist_le_pi_dist p.2 p'.2 i).trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
    calc ∑ i, |p.2 i - p'.2 i| ≤ ∑ _i : Fin k, dist p p' := Finset.sum_le_sum fun i _ ↦ this i
      _ = k * dist p p' := by simp
  rw [dist_eq_norm]
  refine (norm_flow_needle_sub_le hf hũ hw p.2 p'.2 _ _ ⟨ht₁.le, le_rfl⟩).trans ?_
  calc Real.exp (L * t₁) * (‖ψ p.1 - ψ p'.1‖ + 2 * M * ∑ i, |p.2 i - p'.2 i|)
      ≤ Real.exp (L * t₁) * (K * dist p p' + 2 * M * (k * dist p p')) := by gcongr
    _ = Real.exp (L * t₁) * (K + 2 * M * k) * dist p p' := by ring

omit [NormedSpace ℝ P] in
/-- The trajectories of needle variations from `ψ(a)` are uniformly close to the reference
trajectory from `ψ(a₀)` for `(a, σ)` near `(a₀, 0)` in the cone. -/
theorem norm_needle_trajectory_sub_lt (hf : IsBoundedC1System f U M L)
    (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U) (hψ : ContinuousAt ψ a₀) {η : ℝ}
    (hη : 0 < η) :
    ∃ ρ > 0, ∀ p ∈ (univ ×ˢ orthant k) ∩ ball (a₀, 0) ρ, ∀ t ∈ Icc 0 t₁,
      ‖flow f (needleControl ũ τ w p.2) 0 t (ψ p.1) - flow f ũ 0 t (ψ a₀)‖ < η := by
  set C := Real.exp (L * t₁) with hCdef
  have hC : 0 < C := Real.exp_pos _
  obtain ⟨ρ₁, hρ₁, hψρ⟩ := Metric.continuousAt_iff.1 hψ (η / (2 * C)) (by positivity)
  refine ⟨min ρ₁ (η / (2 * C * (2 * M * k + 1))), by positivity, fun p hp t ht ↦ ?_⟩
  have hpb := hp.2
  rw [mem_ball, Prod.dist_eq, max_lt_iff, lt_min_iff, lt_min_iff] at hpb
  have h := norm_flow_needle_sub_le (τ := τ) (w := w) hf hũ hw p.2 0 (ψ p.1) (ψ a₀) ht
  rw [needleControl_zero] at h
  simp only [Pi.zero_apply, sub_zero] at h
  have h1 : ‖ψ p.1 - ψ a₀‖ < η / (2 * C) := by rw [← dist_eq_norm]; exact hψρ hpb.1.1
  have h2 : 2 * M * ∑ i, |p.2 i| ≤ η / (2 * C) := by
    have hσ : ‖p.2‖ < η / (2 * C * (2 * M * k + 1)) := by
      rw [← dist_zero_right]; exact hpb.2.2
    have : ∑ i, |p.2 i| ≤ k * ‖p.2‖ := by
      calc ∑ i, |p.2 i| ≤ ∑ _i : Fin k, ‖p.2‖ :=
            Finset.sum_le_sum fun i _ ↦ by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm p.2 i
        _ = k * ‖p.2‖ := by simp
    calc 2 * M * ∑ i, |p.2 i| ≤ 2 * M * (k * ‖p.2‖) := by gcongr
      _ ≤ (2 * M * k + 1) * ‖p.2‖ := by nlinarith [norm_nonneg p.2]
      _ ≤ (2 * M * k + 1) * (η / (2 * C * (2 * M * k + 1))) := by gcongr
      _ = η / (2 * C) := by field_simp
  calc ‖flow f (needleControl ũ τ w p.2) 0 t (ψ p.1) - flow f ũ 0 t (ψ a₀)‖
      ≤ C * (‖ψ p.1 - ψ a₀‖ + 2 * M * ∑ i, |p.2 i|) := h
    _ < C * (η / (2 * C) + η / (2 * C)) := mul_lt_mul_of_pos_left (add_lt_add_of_lt_of_le h1 h2) hC
    _ = η := by field_simp; ring

/-- For `0 ≤ σⱼ < |τⱼ - τₗ|` (`j ≠ l`), the needle intervals are disjoint. -/
private theorem notMem_Ico_of_mem_Ico (hτinj : Function.Injective τ) {σ : Fin k → ℝ}
    (hD : ∀ j l, j ≠ l → σ j < |τ j - τ l|) {i j : Fin k} (hij : i ≠ j) {r : ℝ}
    (hri : r ∈ Ico (τ i) (τ i + σ i)) : r ∉ Ico (τ j) (τ j + σ j) := by
  intro hrj
  rcases lt_or_gt_of_ne (hτinj.ne hij) with h | h
  · have := hD i j hij
    rw [abs_of_neg (sub_neg.2 h)] at this
    linarith [hri.2, hrj.1]
  · have := hD j i hij.symm
    rw [abs_of_neg (sub_neg.2 h)] at this
    linarith [hrj.2, hri.1]

/-- For small `σ ∈ ℝᵏ₊`, the end point of the needle variation is that of the reference control
plus the integrals of `g_{t,wᵢ}` over the needle intervals (Agrachev–Sachkov, p. 171: the
variations formula (12.13) with `g_{t,ũ(t)} = 0`). -/
private theorem flow_needle_sub_eq_sum (hf : IsBoundedC1System f U M L) (ht₁ : 0 < t₁)
    (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U) (hτ : ∀ i, τ i ∈ Ico 0 t₁)
    (hτinj : Function.Injective τ) {σ : Fin k → ℝ} (hσ : σ ∈ orthant k)
    (hT : ∀ j, σ j < t₁ - τ j) (hD : ∀ j l, j ≠ l → σ j < |τ j - τ l|) (x : E) :
    flow f (needleControl ũ τ w σ) 0 t₁ x - flow f ũ 0 t₁ x =
      ∑ i, ∫ r in τ i..τ i + σ i, variationField f ũ t₁ r (needleControl ũ τ w σ r)
        (flow f ũ r t₁ (flow f (needleControl ũ τ w σ) 0 r x)) := by
  have h0 : (0 : ℝ) ∈ Icc 0 t₁ := ⟨le_rfl, ht₁.le⟩
  have h1 : t₁ ∈ Icc 0 t₁ := ⟨ht₁.le, le_rfl⟩
  obtain ⟨hint, heq⟩ := flow_flow_eq_add_integral_variationField hf hũ
    (isControlOn_needleControl hũ hw σ) h0 h1 x
  have h := heq t₁ h1
  rw [flow_self] at h
  rw [h, add_sub_cancel_left, intervalIntegral.integral_of_le ht₁.le]
  have hsub : (⋃ i, Ioo (τ i) (τ i + σ i)) ⊆ Ioc 0 t₁ := by
    intro r hr
    obtain ⟨i, hri⟩ := mem_iUnion.1 hr
    exact ⟨(hτ i).1.trans_lt hri.1, by linarith [hri.2, hT i]⟩
  have hae : ∀ᵐ r, r ∈ Ioc 0 t₁ \ ⋃ i, Ioo (τ i) (τ i + σ i) →
      variationField f ũ t₁ r (needleControl ũ τ w σ r)
        (flow f ũ r t₁ (flow f (needleControl ũ τ w σ) 0 r x)) = 0 := by
    filter_upwards [ae_all_iff.2 fun i ↦ Measure.ae_ne volume (τ i)] with r hr hrI
    have hnot : ∀ i, r ∉ Ico (τ i) (τ i + σ i) := fun i hri ↦
      hrI.2 (mem_iUnion.2 ⟨i, lt_of_le_of_ne hri.1 (hr i).symm, hri.2⟩)
    rw [needleControl_eq_of_forall_notMem hnot, variationField_self]
  have hdisj : Pairwise (Function.onFun Disjoint fun i ↦ Ioo (τ i) (τ i + σ i)) := fun i j hij ↦
    Set.disjoint_left.2 fun r hri hrj ↦
      notMem_Ico_of_mem_Ico hτinj hD hij (Ioo_subset_Ico_self hri) (Ioo_subset_Ico_self hrj)
  have hintOn := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht₁.le).1 hint
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioc.nullMeasurableSet hsub hae,
    integral_iUnion_fintype (fun i ↦ measurableSet_Ioo) hdisj
      (fun i ↦ hintOn.mono_set ((subset_iUnion (fun i ↦ Ioo (τ i) (τ i + σ i)) i).trans hsub))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hσi : 0 ≤ σ i := hσ i
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]

omit [NormedSpace ℝ P] in
/-- The estimate at one needle: for `(a, σ)` near `(a₀, 0)` in the cone,
`‖∫_{τᵢ}^{τᵢ+σᵢ} g_{t,wᵢ}(y(t)) dt - σᵢ g_{τᵢ,wᵢ}(q₁)‖ ≤ ε σᵢ`, by the continuity of
`(t, z, v) ↦ D_x P_{t → t₁}(P_{t₁ → t} z)(f(P_{t₁ → t} z, wᵢ) - f(P_{t₁ → t} z, v))`, the
closeness of `y(t)` to `q₁`, and the Lebesgue point `τᵢ` of `ũ` (Agrachev–Sachkov, p. 172:
`∂F/∂sᵢ|_{s=0} = g_{τᵢ,uᵢ}(q₁)`). -/
private theorem needle_integral_estimate (hf : IsBoundedC1System f U M L) (ht₁ : 0 < t₁)
    (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U) (hτ : ∀ i, τ i ∈ Ico 0 t₁)
    (hτinj : Function.Injective τ) (i : Fin k)
    (hleb : IsLebesguePointWithin ũ (Icc 0 t₁) (τ i)) (hψ : ContinuousAt ψ a₀) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ p in 𝓝[univ ×ˢ orthant k] ((a₀, 0) : P × (Fin k → ℝ)), (∀ j, p.2 j < t₁ - τ j) →
      (∀ j l, j ≠ l → p.2 j < |τ j - τ l|) →
      ‖(∫ r in τ i..τ i + p.2 i, variationField f ũ t₁ r (needleControl ũ τ w p.2 r)
          (flow f ũ r t₁ (flow f (needleControl ũ τ w p.2) 0 r (ψ p.1)))) -
        p.2 i • variationField f ũ t₁ (τ i) (w i) (flow f ũ 0 t₁ (ψ a₀))‖ ≤ ε * p.2 i := by
  have hL := hf.isLipschitzSystem
  have h0 : (0 : ℝ) ∈ Icc 0 t₁ := ⟨le_rfl, ht₁.le⟩
  have h1 : t₁ ∈ Icc 0 t₁ := ⟨ht₁.le, le_rfl⟩
  have hτI : τ i ∈ Icc 0 t₁ := Ico_subset_Icc_self (hτ i)
  set q₁ := flow f ũ 0 t₁ (ψ a₀) with hq₁
  -- `g_{r,wᵢ}(z) = G(r, z, ũ(r))`, with `G` continuous on `[0, t₁] × E × U`
  set G : ℝ × E × V → E := fun q ↦ fderiv ℝ (flow f ũ q.1 t₁) (flow f ũ t₁ q.1 q.2.1)
    (f (flow f ũ t₁ q.1 q.2.1) (w i) - f (flow f ũ t₁ q.1 q.2.1) q.2.2) with hGdef
  have hGc : ContinuousOn G (Icc 0 t₁ ×ˢ univ ×ˢ U) := by
    have hξ : ContinuousOn (fun q : ℝ × E × V ↦ flow f ũ t₁ q.1 q.2.1)
        (Icc 0 t₁ ×ˢ univ ×ˢ U) :=
      (continuousOn_flow hL hũ).comp
        (by fun_prop : Continuous fun q : ℝ × E × V ↦ (t₁, q.1, q.2.1)).continuousOn
        fun q hq ↦ ⟨h1, hq.1, mem_univ _⟩
    have hD : ContinuousOn
        (fun q : ℝ × E × V ↦ fderiv ℝ (flow f ũ q.1 t₁) (flow f ũ t₁ q.1 q.2.1))
        (Icc 0 t₁ ×ˢ univ ×ˢ U) :=
      (continuousOn_fderiv_flow hf hũ).comp
        (continuousOn_fst.prodMk (continuousOn_const.prodMk hξ))
        fun q hq ↦ ⟨hq.1, h1, mem_univ _⟩
    have hf1 : ContinuousOn (fun q : ℝ × E × V ↦ f (flow f ũ t₁ q.1 q.2.1) (w i))
        (Icc 0 t₁ ×ˢ univ ×ˢ U) :=
      hf.isC1On.continuousOn.comp (hξ.prodMk continuousOn_const)
        fun q _ ↦ ⟨mem_univ _, hw i⟩
    have hf2 : ContinuousOn (fun q : ℝ × E × V ↦ f (flow f ũ t₁ q.1 q.2.1) q.2.2)
        (Icc 0 t₁ ×ˢ univ ×ˢ U) :=
      hf.isC1On.continuousOn.comp (hξ.prodMk (continuous_snd.comp continuous_snd).continuousOn)
        fun q hq ↦ ⟨mem_univ _, hq.2.2⟩
    exact hD.clm_apply (hf1.sub hf2)
  -- uniform continuity of `G` on `[0, t₁] × B(q₁, 1) × U`
  set K := Icc 0 t₁ ×ˢ closedBall q₁ 1 ×ˢ U with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod ((isCompact_closedBall q₁ 1).prod hf.isCompact)
  have hKsub : K ⊆ Icc 0 t₁ ×ˢ univ ×ˢ U := prod_mono le_rfl (prod_mono (subset_univ _) le_rfl)
  obtain ⟨δ₁, hδ₁, hGu⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous (hGc.mono hKsub)) (ε / 2) (half_pos hε)
  -- the Lebesgue point `τᵢ`
  have hGv : ContinuousOn (fun v ↦ G (τ i, q₁, v)) U :=
    hGc.comp (by fun_prop : Continuous fun v : V ↦ (τ i, q₁, v)).continuousOn
      fun v hv ↦ ⟨hτI, mem_univ _, hv⟩
  have hH : ContinuousOn (fun q : E × V ↦ G (τ i, q.1, q.2)) ({q₁} ×ˢ U) :=
    hGc.comp (by fun_prop : Continuous fun q : E × V ↦ (τ i, q.1, q.2)).continuousOn
      fun q hq ↦ ⟨hτI, mem_univ _, hq.2⟩
  have hlebG := hleb.eventually_integral_le (G := fun z v ↦ G (τ i, z, v)) isCompact_singleton
    hf.isCompact hH hũ.aestronglyMeasurable hũ.mem hτI (half_pos hε)
  obtain ⟨δ₂, hδ₂, hlebδ⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hlebG)
  obtain ⟨CH, hCH⟩ := hf.isCompact.exists_bound_of_continuousOn hGv
  have hHint : IntegrableOn (fun θ ↦ ‖G (τ i, q₁, ũ θ) - G (τ i, q₁, ũ (τ i))‖) (Icc 0 t₁) := by
    refine Integrable.of_bound ?_ (2 * CH) ?_
    · exact ContinuousOn.comp_aestronglyMeasurable_of_isClosed
        (G := fun v ↦ ‖G (τ i, q₁, v) - G (τ i, q₁, ũ (τ i))‖) (hGv.sub continuousOn_const).norm
        hf.isCompact.isClosed hũ.aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hũ.mem))
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun θ hθ ↦ ?_)
      rw [norm_norm]
      exact (norm_sub_le _ _).trans ((add_le_add (hCH _ (hũ.mem θ hθ))
        (hCH _ (hũ.mem (τ i) hτI))).trans_eq (by ring))
  -- the varied trajectories stay close to the reference one
  set η := min δ₁ 1 / (2 * Real.exp (L * t₁)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨ρ₃, hρ₃, hclose⟩ := norm_needle_trajectory_sub_lt (τ := τ) (w := w) hf hũ hw hψ hη
  have hball : ∀ ρ > 0, ∀ᶠ p in 𝓝[univ ×ˢ orthant k] ((a₀, 0) : P × (Fin k → ℝ)),
      p ∈ ball ((a₀, 0) : P × (Fin k → ℝ)) ρ :=
    fun ρ hρ ↦ eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds _ hρ)
  filter_upwards [self_mem_nhdsWithin, hball _ hρ₃, hball _ (lt_min hδ₁ hδ₂)] with
    p hpS hp3 hp12 hT hD
  have hσi : 0 ≤ p.2 i := hpS.2 i
  have hσlt : p.2 i < min δ₁ δ₂ := by
    rw [mem_ball, Prod.dist_eq] at hp12
    have := (dist_le_pi_dist p.2 0 i).trans_lt ((le_max_right _ _).trans_lt hp12)
    rw [Real.dist_eq, Pi.zero_apply, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  rcases hσi.eq_or_lt with hzero | hpos
  · rw [← hzero]
    simp
  set τ' := τ i + p.2 i with hτ'
  have hτ'I : τ' ∈ Icc 0 t₁ := ⟨by linarith [(hτ i).1], by linarith [hT i]⟩
  have hsubI : uIcc (τ i) τ' ⊆ Icc 0 t₁ := uIcc_subset_Icc hτI hτ'I
  have hφint := ((flow_flow_eq_add_integral_variationField hf hũ
    (isControlOn_needleControl (τ := τ) hũ hw p.2) h0 h1 (ψ p.1)).1).mono_set
      (show uIcc (τ i) τ' ⊆ uIcc 0 t₁ by rw [uIcc_of_le ht₁.le]; exact hsubI)
  have hconst : ∫ _ in τ i..τ', variationField f ũ t₁ (τ i) (w i) q₁ =
      p.2 i • variationField f ũ t₁ (τ i) (w i) q₁ := by
    rw [intervalIntegral.integral_const, hτ', add_sub_cancel_left]
  rw [← hconst, ← intervalIntegral.integral_sub hφint intervalIntegrable_const]
  have hbound : ∀ᵐ r, r ∈ Ioc (τ i) τ' →
      ‖variationField f ũ t₁ r (needleControl ũ τ w p.2 r)
          (flow f ũ r t₁ (flow f (needleControl ũ τ w p.2) 0 r (ψ p.1))) -
        variationField f ũ t₁ (τ i) (w i) q₁‖ ≤
      ε / 2 + ‖G (τ i, q₁, ũ r) - G (τ i, q₁, ũ (τ i))‖ := by
    filter_upwards [Measure.ae_ne volume τ'] with r hrne hr
    have hrI : r ∈ Icc 0 t₁ := hsubI (Icc_subset_uIcc (Ioc_subset_Icc_self hr))
    have hrIco : r ∈ Ico (τ i) (τ i + p.2 i) := ⟨hr.1.le, lt_of_le_of_ne hr.2 hrne⟩
    have hu : needleControl ũ τ w p.2 r = w i :=
      needleControl_eq_of_mem hrIco fun j hj ↦ notMem_Ico_of_mem_Ico hτinj hD hj.ne' hrIco
    set Y := flow f ũ r t₁ (flow f (needleControl ũ τ w p.2) 0 r (ψ p.1)) with hYdef
    have hY : ‖Y - q₁‖ < min δ₁ 1 := by
      have hq : q₁ = flow f ũ r t₁ (flow f ũ 0 r (ψ a₀)) := (flow_flow hL hũ h0 hrI h1 _).symm
      rw [hq, hYdef]
      calc ‖flow f ũ r t₁ (flow f (needleControl ũ τ w p.2) 0 r (ψ p.1)) -
            flow f ũ r t₁ (flow f ũ 0 r (ψ a₀))‖
          ≤ Real.exp (L * |t₁ - r|) *
              ‖flow f (needleControl ũ τ w p.2) 0 r (ψ p.1) - flow f ũ 0 r (ψ a₀)‖ :=
            norm_flow_sub_flow_le hL hũ hrI h1 _ _
        _ ≤ Real.exp (L * t₁) * η := by
            refine mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ L.2))
              (hclose p ⟨hpS, hp3⟩ r hrI).le (norm_nonneg _) (Real.exp_pos _).le
            rw [abs_le]; constructor <;> linarith [hrI.1, hrI.2]
        _ = min δ₁ 1 / 2 := by rw [hηdef]; field_simp
        _ < min δ₁ 1 := half_lt_self (by positivity)
    have hφr : variationField f ũ t₁ r (needleControl ũ τ w p.2 r) Y = G (r, Y, ũ r) := by
      rw [hu]; rfl
    rw [hφr]
    have hK1 : (r, Y, ũ r) ∈ K :=
      ⟨hrI, mem_closedBall.2 (by rw [dist_eq_norm]; exact hY.le.trans (min_le_right _ _)),
        hũ.mem r hrI⟩
    have hK2 : (τ i, q₁, ũ r) ∈ K := ⟨hτI, mem_closedBall_self zero_le_one, hũ.mem r hrI⟩
    have hd : dist (r, Y, ũ r) (τ i, q₁, ũ r) < δ₁ := by
      simp only [Prod.dist_eq, dist_self, Real.dist_eq]
      refine max_lt ?_ (max_lt ?_ hδ₁)
      · rw [abs_of_nonneg (by linarith [hr.1])]
        linarith [hr.2, hσlt, min_le_left δ₁ δ₂]
      · rw [dist_eq_norm]; exact hY.trans_le (min_le_left _ _)
    have hGd := hGu _ hK1 _ hK2 hd
    rw [dist_eq_norm] at hGd
    calc ‖G (r, Y, ũ r) - variationField f ũ t₁ (τ i) (w i) q₁‖
        ≤ ‖G (r, Y, ũ r) - G (τ i, q₁, ũ r)‖ + ‖G (τ i, q₁, ũ r) - G (τ i, q₁, ũ (τ i))‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε / 2 + ‖G (τ i, q₁, ũ r) - G (τ i, q₁, ũ (τ i))‖ := by gcongr
  have hHint' : IntervalIntegrable (fun θ ↦ ‖G (τ i, q₁, ũ θ) - G (τ i, q₁, ũ (τ i))‖) volume
      (τ i) τ' := (hHint.mono_set hsubI).intervalIntegrable
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith) hbound
    (intervalIntegrable_const.add hHint')).trans ?_
  rw [intervalIntegral.integral_add intervalIntegrable_const hHint',
    intervalIntegral.integral_const, smul_eq_mul, hτ', add_sub_cancel_left]
  have hleb' := hlebδ (show dist τ' (τ i) < δ₂ by
      rw [Real.dist_eq, hτ', add_sub_cancel_left, abs_of_pos hpos]
      exact hσlt.trans_le (min_le_right _ _))
    ⟨hτ'I, (show τ i < τ' by linarith).ne'⟩ q₁ rfl
  rw [hτ', uIoc_of_le (by linarith), add_sub_cancel_left, abs_of_pos hpos,
    inv_mul_le_iff₀ hpos] at hleb'
  rw [intervalIntegral.integral_of_le (by linarith)]
  linarith

/-- **Derivative of the needle variations** at `(a₀, 0)` within the cone `P × ℝᵏ₊`
(Agrachev–Sachkov, p. 172: `∂F/∂sᵢ|_{s=0} = g_{τᵢ,uᵢ}(q₁)`; p. 182: `∂F/∂q v = P^{t₁}_* v`):
`(α, σ) ↦ D_x P_{0 → t₁}(ψ(a₀)) Dψ(a₀) α + Σᵢ σᵢ g_{τᵢ,wᵢ}(q₁)`, for distinct needle times
`τᵢ ∈ [0, t₁)` that are Lebesgue points of `ũ`. -/
theorem hasFDerivWithinAt_needle (hf : IsBoundedC1System f U M L) (ht₁ : 0 < t₁)
    (hũ : IsControlOn ũ U 0 t₁) (hw : ∀ i, w i ∈ U) (hτ : ∀ i, τ i ∈ Ico 0 t₁)
    (hτinj : Function.Injective τ) (hleb : ∀ i, IsLebesguePointWithin ũ (Icc 0 t₁) (τ i))
    (hψ : ContDiffAt ℝ 1 ψ a₀) :
    HasFDerivWithinAt
      (fun p : P × (Fin k → ℝ) ↦ flow f (needleControl ũ τ w p.2) 0 t₁ (ψ p.1))
      ((fderiv ℝ (flow f ũ 0 t₁) (ψ a₀)).comp
          ((fderiv ℝ ψ a₀).comp (ContinuousLinearMap.fst ℝ P (Fin k → ℝ))) +
        ∑ i, ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ P (Fin k → ℝ))).smulRight
          (variationField f ũ t₁ (τ i) (w i) (flow f ũ 0 t₁ (ψ a₀))))
      (univ ×ˢ orthant k) (a₀, 0) := by
  set z₀ : P × (Fin k → ℝ) := (a₀, 0) with hz₀
  have h0 : (0 : ℝ) ∈ Icc 0 t₁ := ⟨le_rfl, ht₁.le⟩
  have h1 : t₁ ∈ Icc 0 t₁ := ⟨ht₁.le, le_rfl⟩
  set S : Set (P × (Fin k → ℝ)) := univ ×ˢ orthant k with hS
  set g : Fin k → E := fun i ↦ variationField f ũ t₁ (τ i) (w i) (flow f ũ 0 t₁ (ψ a₀))
    with hg
  -- the end-point map of the reference control from `ψ(a)`: A–S's (2.19)
  have hP : HasFDerivAt (fun p : P × (Fin k → ℝ) ↦ flow f ũ 0 t₁ (ψ p.1))
      ((fderiv ℝ (flow f ũ 0 t₁) (ψ a₀)).comp
        ((fderiv ℝ ψ a₀).comp (ContinuousLinearMap.fst ℝ P (Fin k → ℝ)))) z₀ := by
    have hfl : HasFDerivAt (flow f ũ 0 t₁) (fderiv ℝ (flow f ũ 0 t₁) (ψ a₀)) (ψ a₀) :=
      ((contDiff_flow hf hũ h0 h1).differentiable one_ne_zero _).hasFDerivAt
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ a₀) z₀.1 := (hψ.differentiableAt one_ne_zero).hasFDerivAt
    have hfst : HasFDerivAt (Prod.fst : P × (Fin k → ℝ) → P)
        (ContinuousLinearMap.fst ℝ P (Fin k → ℝ)) z₀ := hasFDerivAt_fst
    exact hfl.comp z₀ (hψd.comp z₀ hfst)
  -- small parameters: the needle intervals lie in `[0, t₁)` and are disjoint
  have hcoord : ∀ r > 0, ∀ᶠ p in 𝓝[S] ((a₀, 0) : P × (Fin k → ℝ)), ∀ i, p.2 i < r := by
    intro r hr
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds ((a₀, 0) : P × (Fin k → ℝ)) hr)] with p hp i
    rw [Prod.dist_eq] at hp
    have := (dist_le_pi_dist p.2 0 i).trans_lt ((le_max_right _ _).trans_lt hp)
    rw [Real.dist_eq, Pi.zero_apply, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hT : ∀ᶠ p in 𝓝[S] ((a₀, 0) : P × (Fin k → ℝ)), ∀ j, p.2 j < t₁ - τ j :=
    eventually_all.2 fun j ↦ (hcoord _ (sub_pos.2 (hτ j).2)).mono fun p hp ↦ hp j
  have hD : ∀ᶠ p in 𝓝[S] ((a₀, 0) : P × (Fin k → ℝ)), ∀ j l, j ≠ l → p.2 j < |τ j - τ l| := by
    refine eventually_all.2 fun j ↦ eventually_all.2 fun l ↦ ?_
    by_cases hjl : j = l
    · exact Eventually.of_forall fun _ h ↦ (h hjl).elim
    · exact (hcoord _ (abs_pos.2 (sub_ne_zero.2 (hτinj.ne hjl)))).mono fun p hp _ ↦ hp j
  -- the needles: `F(a, σ) - P_{0 → t₁}(ψ(a)) = Σᵢ σᵢ g_{τᵢ,wᵢ}(q₁) + o(σ)`
  have hR : HasFDerivWithinAt
      (fun p : P × (Fin k → ℝ) ↦
        flow f (needleControl ũ τ w p.2) 0 t₁ (ψ p.1) - flow f ũ 0 t₁ (ψ p.1))
      (∑ i, ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ P (Fin k → ℝ))).smulRight (g i)) S (a₀, 0) := by
    rw [hasFDerivWithinAt_iff_isLittleO]
    refine Asymptotics.isLittleO_iff.2 fun c hc ↦ ?_
    have hε : 0 < c / (k + 1) := by positivity
    have hest := eventually_all.2 fun i ↦
      needle_integral_estimate hf ht₁ hũ hw hτ hτinj i (hleb i) hψ.continuousAt hε
    filter_upwards [self_mem_nhdsWithin, hT, hD, hest] with p hpS hpT hpD hpE
    rw [needleControl_zero, sub_self, sub_zero,
      flow_needle_sub_eq_sum hf ht₁ hũ hw hτ hτinj hpS.2 hpT hpD]
    simp only [_root_.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.coe_snd', Prod.snd_sub, sub_zero]
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ i, p.2 i ≤ ‖p - (a₀, 0)‖ := fun i ↦ by
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      refine (norm_le_pi_norm p.2 i).trans ?_
      have := norm_snd_le (p - z₀)
      simpa [hz₀] using this
    have hk : (k : ℝ) * (c / (k + 1)) ≤ c := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    calc ∑ i, ‖(∫ r in τ i..τ i + p.2 i, variationField f ũ t₁ r (needleControl ũ τ w p.2 r)
            (flow f ũ r t₁ (flow f (needleControl ũ τ w p.2) 0 r (ψ p.1)))) - p.2 i • g i‖
        ≤ ∑ i, c / (k + 1) * p.2 i := Finset.sum_le_sum fun i _ ↦ hpE i hpT hpD
      _ ≤ ∑ _i : Fin k, c / (k + 1) * ‖p - (a₀, 0)‖ :=
          Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hle i) hε.le
      _ = k * (c / (k + 1)) * ‖p - (a₀, 0)‖ := by simp [mul_assoc]
      _ ≤ c * ‖p - (a₀, 0)‖ := mul_le_mul_of_nonneg_right hk (norm_nonneg _)
  convert hP.hasFDerivWithinAt.add hR using 1
  funext p
  simp

end ControlSystem
