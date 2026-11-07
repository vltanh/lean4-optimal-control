module

public import OptimalControl.ODE.Caratheodory
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Linear Carathéodory equations: the resolvent and the adjoint equation

For `A : ℝ → (E →L[ℝ] E)` bounded and a.e. strongly measurable on `[a, b]`, the *resolvent*
(state-transition operator) `R(s, t) = ControlSystem.stateTransition A s t` is the solution at
time `t` of `Y' = A(t) ∘ Y`, `Y(s) = id`. It is the flow (`ControlSystem.flow`) of the linear
control system `Y' = B ∘ Y` on `E →L[ℝ] E` driven by the "control" `B = A(t)` with values in the
compact ball `‖B‖ ≤ K`. This file proves:

* the integral equations in the final and in the initial time,
  `R(s, t) = id + ∫ₛᵗ A(r) ∘ R(s, r) dr` and `R(t, c) = id + ∫ₜᶜ R(r, c) ∘ A(r) dr`, and
  uniqueness for the first;
* the cocycle property `R(t, r) ∘ R(s, t) = R(s, r)`, hence invertibility;
* the bound `‖R(s, t)‖ ≤ e^{K|t - s|}` and Lipschitz continuity in each time, with explicit
  constants (`ControlSystem.lipschitzOnWith_stateTransition_right`, `_left`);
* the *adjoint equation*: for a covector `ℓ`, `p(t) = ℓ ∘ R(t, c)` is Lipschitz and solves
  `p(t) = ℓ + ∫ₜᶜ p(r) ∘ A(r) dr`, that is `ṗ = -p ∘ A` a.e. with `p(c) = ℓ`, and uniqueness for
  it;
* the dependence on the coefficient: `R` depends only on `A` on `[a, b]`
  (`ControlSystem.stateTransition_congr`), continuously
  (`ControlSystem.norm_stateTransition_sub_stateTransition_le`).

## Source and reading

Agrachev–Sachkov (authors' draft) use the linear equation through the variations formula and
Proposition 11.3 (§11.5.2, p. 161: the cotangent lift of a nonautonomous flow is the flow of the
Hamiltonian lift), read pointwise along a trajectory in coordinates (departure D2): the
cotangent lift of the flow along `q̃` acts on covectors by `ℓ ↦ ℓ ∘ R(t, c)`, which solves
`λ̇ = -λ ∘ ∂ₓf(q̃(t), ũ(t))`. A–S prove Proposition 11.3 in the chronological calculus (operator
identities for `exp→`); read pointwise it is a statement on the linear equation, proved here by the
standard ODE arguments (departure D11).

## Proof sketch

Instance of `OptimalControl/ODE/Caratheodory.lean` for `f(Y, B) = B ∘ Y` on `E →L[ℝ] E`
(`IsLipschitzSystem` with constant `K`, `U = closedBall 0 K`): the final-time equation is
`isSolution_flow`, uniqueness `IsSolution.flow_eq` (applied to `t ↦ R(s, t) ∘ Y₀`), the cocycle
property `flow_flow`, the bound `norm_flow_sub_flow_le` (comparison with the zero solution) and
the dependence on the coefficient `norm_flow_sub_flow_control_le`. Initial-time equation: `R(·, c)`
is the inverse `R(c, ·)⁻¹` (cocycle property), so at almost every `t` (Lebesgue's differentiation
theorem for the final-time equation) it has derivative `-R(c, t)⁻¹ A(t) R(c, t) R(c, t)⁻¹ =
-R(t, c) A(t)` (derivative of `Ring.inverse`); hence `R(t, c) + ∫ₖᵗ R(r, c) A(r) dr` is
Lipschitz with derivative `0` almost everywhere, so constant
(`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`). The adjoint equation is `ℓ ∘` the
initial-time equation; its uniqueness is uniqueness for the system `p' = -p ∘ B` on covectors.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace ControlSystem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The resolvent `R(s, t)` of the linear equation `Y' = A(t) ∘ Y`: the value at time `t` of the
solution with `Y(s) = id` (the flow of the linear system `Y' = B ∘ Y` driven by `B = A(t)`). -/
noncomputable def stateTransition (A : ℝ → E →L[ℝ] E) (s t : ℝ) : E →L[ℝ] E :=
  flow (fun Y B ↦ B.comp Y) A s t (ContinuousLinearMap.id ℝ E)

omit [FiniteDimensional ℝ E] in
/-- `R(s, s) = id`. -/
theorem stateTransition_self (A : ℝ → E →L[ℝ] E) (s : ℝ) :
    stateTransition A s s = ContinuousLinearMap.id ℝ E :=
  flow_self _ _ _ _

variable {A : ℝ → E →L[ℝ] E} {a b K : ℝ}

/-! ### The linear system and its solutions -/

/-- The linear system `Y' = B ∘ Y` on `E →L[ℝ] E`, with "controls" `B` in the closed ball of
radius `K`, satisfies the standing hypotheses with Lipschitz constant `K`. -/
private theorem isLipschitzSystem_comp (K : ℝ) :
    IsLipschitzSystem (fun (Y B : E →L[ℝ] E) ↦ B.comp Y) (closedBall 0 K) K.toNNReal where
  isCompact := isCompact_closedBall 0 K
  continuousOn := (continuous_snd.clm_comp continuous_fst).continuousOn
  lipschitzWith B hB := by
    refine LipschitzWith.of_dist_le_mul fun Y Y' ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
    exact (B.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_right
      ((mem_closedBall_zero_iff.1 hB).trans (Real.le_coe_toNNReal K)) (norm_nonneg _))

/-- The adjoint system `p' = -p ∘ B` on covectors satisfies the standing hypotheses. -/
private theorem isLipschitzSystem_dual (K : ℝ) :
    IsLipschitzSystem (fun (p : StrongDual ℝ E) (B : E →L[ℝ] E) ↦ -(p.comp B)) (closedBall 0 K)
      K.toNNReal where
  isCompact := isCompact_closedBall 0 K
  continuousOn := (continuous_fst.clm_comp continuous_snd).neg.continuousOn
  lipschitzWith B hB := by
    refine LipschitzWith.of_dist_le_mul fun p p' ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, neg_sub_neg, ← neg_sub, norm_neg,
      ← ContinuousLinearMap.sub_comp]
    refine ((p - p').opNorm_comp_le B).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right
      ((mem_closedBall_zero_iff.1 hB).trans (Real.le_coe_toNNReal K)) (norm_nonneg _)

omit [FiniteDimensional ℝ E] in
private theorem isControlOn_closedBall (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) : IsControlOn A (closedBall 0 K) a b :=
  ⟨hA, fun t ht ↦ mem_closedBall_zero_iff.2 (hK t ht)⟩

/-- A bounded function, a.e. strongly measurable on `[a, b]`, is interval integrable. -/
private theorem intervalIntegrable_of_norm_le {F : Type*} [NormedAddCommGroup F] {g : ℝ → F}
    (hab : a ≤ b) (hg : AEStronglyMeasurable g (volume.restrict (Icc a b))) {C : ℝ}
    (hC : ∀ t ∈ Icc a b, ‖g t‖ ≤ C) : IntervalIntegrable g volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
    (IntegrableOn.of_bound measure_Icc_lt_top hg C (ae_restrict_of_forall_mem measurableSet_Icc hC))

private theorem intervalIntegrable_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (Λ : F →L[ℝ] G) {g : ℝ → F}
    (hg : IntervalIntegrable g volume a b) : IntervalIntegrable (fun r ↦ Λ (g r)) volume a b :=
  ⟨Λ.integrable_comp hg.1, Λ.integrable_comp hg.2⟩

/-- `t ↦ ∫ₖᵗ g` is Lipschitz on `[a, b]` for `g` bounded by `C` there. -/
private theorem lipschitzOnWith_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} (hg : IntervalIntegrable g volume a b) {C : ℝ} (hC : ∀ t ∈ Icc a b, ‖g t‖ ≤ C)
    {c : ℝ} (hc : c ∈ Icc a b) :
    LipschitzOnWith C.toNNReal (fun t ↦ ∫ r in c..t, g r) (Icc a b) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hab : a ≤ b := hc.1.trans hc.2
  have hsub : ∀ z ∈ Icc a b, [[c, z]] ⊆ [[a, b]] := fun z hz ↦ by
    rw [uIcc_of_le hab]; exact uIcc_subset_Icc hc hz
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left (hg.mono_set (hsub x hx))
    (hg.mono_set (hsub y hy)), Real.dist_eq]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦
    hC r (uIcc_subset_Icc hy hx (uIoc_subset_uIcc hr))).trans ?_
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (abs_nonneg _)

omit [FiniteDimensional ℝ E] in
private theorem nonneg_of_norm_le (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {s : ℝ} (hs : s ∈ Icc a b) :
    0 ≤ K :=
  (norm_nonneg _).trans (hK s hs)

/-- `R(s, ·)` is the solution of the linear equation through `(s, id)`. -/
private theorem isSolution_stateTransition
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b))) (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    {s : ℝ} (hs : s ∈ Icc a b) :
    IsSolution (fun (Y B : E →L[ℝ] E) ↦ B.comp Y) A s (ContinuousLinearMap.id ℝ E) a b
      (fun t ↦ stateTransition A s t) :=
  isSolution_flow (isLipschitzSystem_comp K) (isControlOn_closedBall hA hK) hs _

/-- The final-time equation `R(s, t) = id + ∫ₛᵗ A(r) ∘ R(s, r) dr`, with the integrand
integrable on `[a, b]`. -/
theorem stateTransition_eq_integral (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {s : ℝ} (hs : s ∈ Icc a b) :
    IntervalIntegrable (fun r ↦ (A r).comp (stateTransition A s r)) volume a b ∧
      ∀ t ∈ Icc a b, stateTransition A s t =
        ContinuousLinearMap.id ℝ E + ∫ r in s..t, (A r).comp (stateTransition A s r) := by
  have hR := isSolution_stateTransition hA hK hs
  refine ⟨hR.2.1, fun t ht ↦ hR.2.2 t ?_⟩
  rwa [uIcc_of_le (hs.1.trans hs.2)]

/-- Uniqueness: a continuous solution of `Y(t) = Y₀ + ∫ₛᵗ A(r) ∘ Y(r) dr` on `[a, b]` is
`R(s, t) ∘ Y₀`. -/
theorem eq_stateTransition_comp (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {s : ℝ} (hs : s ∈ Icc a b) {Y₀ : E →L[ℝ] E}
    {Y : ℝ → E →L[ℝ] E} (hY : ContinuousOn Y (Icc a b))
    (hYeq : ∀ t ∈ Icc a b, Y t = Y₀ + ∫ r in s..t, (A r).comp (Y r)) :
    ∀ t ∈ Icc a b, Y t = (stateTransition A s t).comp Y₀ := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hK0 : 0 ≤ K := nonneg_of_norm_le hK hs
  have hsys := isLipschitzSystem_comp (E := E) K
  have hctl := isControlOn_closedBall hA hK
  obtain ⟨CY, hCY⟩ := isCompact_Icc.exists_bound_of_continuousOn hY
  have hYsol : IsSolution (fun (Y B : E →L[ℝ] E) ↦ B.comp Y) A s Y₀ a b Y := by
    refine ⟨by rwa [uIcc_of_le hab], ?_, fun t ht ↦ hYeq t (by rwa [uIcc_of_le hab] at ht)⟩
    refine intervalIntegrable_of_norm_le hab ?_ (C := K * CY) fun t ht ↦ ?_
    · exact (continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
        (hA.prodMk (hY.aestronglyMeasurable measurableSet_Icc))
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hK t ht) (hCY t ht) (norm_nonneg _) hK0)
  have hR := isSolution_stateTransition hA hK hs
  let Λ : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := (ContinuousLinearMap.compL ℝ E E E).flip Y₀
  have hΛ : ∀ X, Λ X = X.comp Y₀ := fun X ↦ rfl
  have hZsol : IsSolution (fun (Y B : E →L[ℝ] E) ↦ B.comp Y) A s Y₀ a b
      (fun t ↦ (stateTransition A s t).comp Y₀) := by
    refine ⟨Λ.continuous.comp_continuousOn hR.1, ?_, fun t ht ↦ ?_⟩
    · simpa only [hΛ, ContinuousLinearMap.comp_assoc] using intervalIntegrable_clm Λ hR.2.1
    · have hint := hR.2.1.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc hs) ht)
      have h := hR.2.2 t ht
      simp only at h ⊢
      rw [h, ContinuousLinearMap.add_comp, ContinuousLinearMap.id_comp, ← hΛ,
        ← Λ.intervalIntegral_comp_comm hint]
      simp only [hΛ, ContinuousLinearMap.comp_assoc]
  intro t ht
  rw [← IsSolution.flow_eq hsys hctl hs hYsol ht, IsSolution.flow_eq hsys hctl hs hZsol ht]

/-- The flow of the linear system from `Y₀` is `R(s, t) ∘ Y₀`. -/
private theorem flow_comp_eq (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (Y₀ : E →L[ℝ] E) :
    flow (fun (Y B : E →L[ℝ] E) ↦ B.comp Y) A s t Y₀ = (stateTransition A s t).comp Y₀ := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hsol := isSolution_flow (isLipschitzSystem_comp K) (isControlOn_closedBall hA hK) hs Y₀
  refine eq_stateTransition_comp hA hK hs
    (Y := fun t ↦ flow (fun (Y B : E →L[ℝ] E) ↦ B.comp Y) A s t Y₀) ?_ ?_ t ht
  · rw [← uIcc_of_le hab]; exact hsol.1
  · intro t ht; exact hsol.2.2 t (by rwa [uIcc_of_le hab])

/-- The cocycle property `R(t, r) ∘ R(s, t) = R(s, r)`. -/
theorem stateTransition_comp_stateTransition
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b))) (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    {s t r : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hr : r ∈ Icc a b) :
    (stateTransition A t r).comp (stateTransition A s t) = stateTransition A s r := by
  rw [← flow_comp_eq hA hK ht hr]
  exact flow_flow (isLipschitzSystem_comp K) (isControlOn_closedBall hA hK) hs ht hr _

/-- The bound `‖R(s, t)‖ ≤ e^{K|t - s|}`. -/
theorem norm_stateTransition_le (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖stateTransition A s t‖ ≤ Real.exp (K * |t - s|) := by
  have h := norm_flow_sub_flow_le (isLipschitzSystem_comp K) (isControlOn_closedBall hA hK) hs ht
    (ContinuousLinearMap.id ℝ E) 0
  rw [flow_comp_eq hA hK hs ht 0, ContinuousLinearMap.comp_zero, sub_zero, sub_zero,
    Real.coe_toNNReal K (nonneg_of_norm_le hK hs)] at h
  exact h.trans (mul_le_of_le_one_right (Real.exp_pos _).le ContinuousLinearMap.norm_id_le)

/-- The uniform bound `‖R(s, t)‖ ≤ e^{K(b - a)}` on `[a, b]`. -/
theorem norm_stateTransition_le_exp (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖stateTransition A s t‖ ≤ Real.exp (K * (b - a)) := by
  refine (norm_stateTransition_le hA hK hs ht).trans (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_left ?_ (nonneg_of_norm_le hK hs)))
  exact abs_sub_le_iff.2 ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩

/-- Lipschitz continuity in the final time, with an explicit constant:
`‖R(c, t) - R(c, t')‖ ≤ K e^{K(b - a)} |t - t'|`. -/
theorem lipschitzOnWith_stateTransition_right
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b))) (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    {c : ℝ} (hc : c ∈ Icc a b) :
    LipschitzOnWith (K * Real.exp (K * (b - a))).toNNReal (fun t ↦ stateTransition A c t)
      (Icc a b) := by
  obtain ⟨hint, heq⟩ := stateTransition_eq_integral hA hK hc
  have hlip := lipschitzOnWith_integral hint (C := K * Real.exp (K * (b - a))) (fun t ht ↦
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hK t ht)
      (norm_stateTransition_le_exp hA hK hc ht) (norm_nonneg _) (nonneg_of_norm_le hK hc))) hc
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  rw [heq x hx, heq y hy, dist_add_left]
  exact hlip.dist_le_mul x hx y hy

/-- Lipschitz continuity in the initial time, with an explicit constant:
`‖R(t, c) - R(t', c)‖ ≤ e^{K(b - a)} K e^{K(b - a)} |t - t'|`. -/
theorem lipschitzOnWith_stateTransition_left
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b))) (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    {c : ℝ} (hc : c ∈ Icc a b) :
    LipschitzOnWith (Real.exp (K * (b - a)) * (K * Real.exp (K * (b - a)))).toNNReal
      (fun t ↦ stateTransition A t c) (Icc a b) := by
  have hK0 : 0 ≤ K := nonneg_of_norm_le hK hc
  refine LipschitzOnWith.of_dist_le_mul fun t ht t' ht' ↦ ?_
  have hR := (lipschitzOnWith_stateTransition_right hA hK ht).dist_le_mul t' ht' t ht
  rw [Real.coe_toNNReal _ (by positivity)] at hR
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm,
    ← stateTransition_comp_stateTransition hA hK ht ht' hc]
  calc ‖(stateTransition A t' c).comp (stateTransition A t t') - stateTransition A t' c‖
      = ‖(stateTransition A t' c).comp (stateTransition A t t' - stateTransition A t t)‖ := by
        rw [ContinuousLinearMap.comp_sub, stateTransition_self, ContinuousLinearMap.comp_id]
    _ ≤ ‖stateTransition A t' c‖ * ‖stateTransition A t t' - stateTransition A t t‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.exp (K * (b - a)) * (K * Real.exp (K * (b - a)) * dist t' t) := by
        rw [← dist_eq_norm]
        exact mul_le_mul (norm_stateTransition_le_exp hA hK ht' hc) hR dist_nonneg
          (Real.exp_pos _).le
    _ = Real.exp (K * (b - a)) * (K * Real.exp (K * (b - a))) * dist t t' := by
        rw [dist_comm]; ring

/-- `R(c, t)` is invertible, with inverse `R(t, c)`: `Ring.inverse (R(c, t)) = R(t, c)`, and a
unit with these values. -/
private theorem exists_unit_stateTransition
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b))) (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    {c t : ℝ} (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∃ w : (E →L[ℝ] E)ˣ, (w : E →L[ℝ] E) = stateTransition A c t ∧
      ((w⁻¹ : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) = stateTransition A t c :=
  ⟨⟨stateTransition A c t, stateTransition A t c,
    by rw [ContinuousLinearMap.mul_def, stateTransition_comp_stateTransition hA hK ht hc ht,
      stateTransition_self, ContinuousLinearMap.one_def],
    by rw [ContinuousLinearMap.mul_def, stateTransition_comp_stateTransition hA hK hc ht hc,
      stateTransition_self, ContinuousLinearMap.one_def]⟩, rfl, rfl⟩

/-- The initial-time equation `R(t, c) = id + ∫ₜᶜ R(r, c) ∘ A(r) dr` (`∂ₜR(t, c) = -R(t, c) A(t)`),
with the integrand integrable on `[a, b]`. -/
theorem stateTransition_eq_integral_left (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {c : ℝ} (hc : c ∈ Icc a b) :
    IntervalIntegrable (fun r ↦ (stateTransition A r c).comp (A r)) volume a b ∧
      ∀ t ∈ Icc a b, stateTransition A t c =
        ContinuousLinearMap.id ℝ E + ∫ r in t..c, (stateTransition A r c).comp (A r) := by
  have hab : a ≤ b := hc.1.trans hc.2
  have hK0 : 0 ≤ K := nonneg_of_norm_le hK hc
  set C := Real.exp (K * (b - a)) with hCdef
  have hlip := lipschitzOnWith_stateTransition_left hA hK hc
  have hcont : ContinuousOn (fun t ↦ stateTransition A t c) (Icc a b) := hlip.continuousOn
  have hkC : ∀ t ∈ Icc a b, ‖(stateTransition A t c).comp (A t)‖ ≤ C * K := fun t ht ↦
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_stateTransition_le_exp hA hK ht hc) (hK t ht) (norm_nonneg _)
        (Real.exp_pos _).le)
  have hk : IntervalIntegrable (fun r ↦ (stateTransition A r c).comp (A r)) volume a b :=
    intervalIntegrable_of_norm_le hab
      ((continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
        ((hcont.aestronglyMeasurable measurableSet_Icc).prodMk hA)) hkC
  refine ⟨hk, fun t ht ↦ ?_⟩
  -- the derivative of `R(c, ·)`, almost everywhere
  obtain ⟨hh, hheq⟩ := stateTransition_eq_integral hA hK hc
  have hcI : c ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hc
  have hΦ : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun t ↦ stateTransition A c t)
      ((A x).comp (stateTransition A c x)) x := by
    filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hh] with x hx hxab
    have hxI : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact Ioo_subset_Icc_self hxab
    refine ((hx hxI c hcI).const_add (ContinuousLinearMap.id ℝ E)).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hxab.1 hxab.2] with t ht
    exact hheq t (Ioo_subset_Icc_self ht)
  -- the derivative of `R(·, c) = R(c, ·)⁻¹`, almost everywhere
  have hΨ : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt (fun t ↦ stateTransition A t c)
      (-(stateTransition A x c).comp (A x)) x := by
    filter_upwards [hΦ] with x hx hxab
    have hxI := Ioo_subset_Icc_self hxab
    obtain ⟨w, hw, hw'⟩ := exists_unit_stateTransition hA hK hc hxI
    have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) w
    rw [hw] at hinv
    have h1 := hinv.comp_hasDerivAt x (hx hxab)
    have h2 : (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) ↑w⁻¹ ↑w⁻¹)
        ((A x).comp (stateTransition A c x)) = -(stateTransition A x c).comp (A x) := by
      rw [neg_apply, ContinuousLinearMap.mulLeftRight_apply, hw',
        ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.comp_assoc, stateTransition_comp_stateTransition hA hK hxI hc hxI,
        stateTransition_self, ContinuousLinearMap.comp_id]
    rw [h2] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hxab.1 hxab.2] with t ht
    obtain ⟨w', hw'1, hw'2⟩ := exists_unit_stateTransition hA hK hc (Ioo_subset_Icc_self ht)
    simp only [Function.comp_apply]
    rw [← hw'1, Ring.inverse_unit, hw'2]
  -- `g(t) = R(t, c) + ∫ₖᵗ R(r, c) A(r) dr` is constant
  set g : ℝ → E →L[ℝ] E :=
    fun t ↦ stateTransition A t c + ∫ r in c..t, (stateTransition A r c).comp (A r) with hgdef
  have hgac : AbsolutelyContinuousOnInterval g a b := by
    have h := hlip.add (lipschitzOnWith_integral hk hkC hc)
    rw [← uIcc_of_le hab] at h
    exact h.absolutelyContinuousOnInterval
  have hg0 : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt g 0 x := by
    have ha : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
    have hb : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [hΨ, IntervalIntegrable.ae_hasDerivAt_integral hk, ha, hb]
      with x hΨx hkx hxa hxb hx
    have hx' : x ∈ Icc a b := by rwa [uIcc_of_le hab] at hx
    have hxab : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx'.1 (Ne.symm hxa), lt_of_le_of_ne hx'.2 hxb⟩
    have h := (hΨx hxab).add (hkx hx c hcI)
    rw [neg_add_cancel] at h
    exact h
  obtain ⟨C', hC'⟩ := hgac.const_of_ae_hasDerivAt_zero hg0
  have htI : t ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ht
  have hgt : g t = ContinuousLinearMap.id ℝ E := by
    rw [hC' t htI, ← hC' c hcI, hgdef]
    simp [stateTransition_self]
  rw [intervalIntegral.integral_symm, ← sub_eq_add_neg]
  exact eq_sub_of_add_eq hgt

/-- The resolvent is Lipschitz in each time on `[a, b]`. -/
theorem lipschitzOnWith_stateTransition (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {c : ℝ} (hc : c ∈ Icc a b) :
    (∃ C, LipschitzOnWith C (fun t ↦ stateTransition A c t) (Icc a b)) ∧
      ∃ C, LipschitzOnWith C (fun t ↦ stateTransition A t c) (Icc a b) :=
  ⟨⟨_, lipschitzOnWith_stateTransition_right hA hK hc⟩,
    ⟨_, lipschitzOnWith_stateTransition_left hA hK hc⟩⟩

/-- **The adjoint equation** (Agrachev–Sachkov, Proposition 11.3, read pointwise; departure D2):
for a covector `ℓ`, the curve `p(t) = ℓ ∘ R(t, c)` is Lipschitz on `[a, b]` and solves
`p(t) = ℓ + ∫ₜᶜ p(r) ∘ A(r) dr`, that is `ṗ = -p ∘ A` a.e. with `p(c) = ℓ`; and `p(t) ≠ 0` for
all `t ∈ [a, b]` when `ℓ ≠ 0` (the resolvent is invertible).

Departure from the source (D2): A–S prove Proposition 11.3 in the chronological calculus; read
pointwise it is `ℓ ∘` the initial-time equation `stateTransition_eq_integral_left`. -/
theorem adjoint_stateTransition (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {c : ℝ} (hc : c ∈ Icc a b) (ℓ : StrongDual ℝ E) :
    (∃ C, LipschitzOnWith C (fun t ↦ ℓ.comp (stateTransition A t c)) (Icc a b)) ∧
      IntervalIntegrable (fun r ↦ (ℓ.comp (stateTransition A r c)).comp (A r)) volume a b ∧
      (∀ t ∈ Icc a b, ℓ.comp (stateTransition A t c) =
        ℓ + ∫ r in t..c, (ℓ.comp (stateTransition A r c)).comp (A r)) ∧
      (ℓ ≠ 0 → ∀ t ∈ Icc a b, ℓ.comp (stateTransition A t c) ≠ 0) := by
  have hab : a ≤ b := hc.1.trans hc.2
  obtain ⟨hk, hkeq⟩ := stateTransition_eq_integral_left hA hK hc
  let Λ : (E →L[ℝ] E) →L[ℝ] StrongDual ℝ E := ContinuousLinearMap.compL ℝ E E ℝ ℓ
  have hΛ : ∀ X, Λ X = ℓ.comp X := fun X ↦ rfl
  refine ⟨⟨_, Λ.lipschitzWith.comp_lipschitzOnWith (lipschitzOnWith_stateTransition_left hA hK hc)⟩,
    ?_, fun t ht ↦ ?_, fun hℓ t ht h0 ↦ hℓ ?_⟩
  · simpa only [hΛ, ContinuousLinearMap.comp_assoc] using intervalIntegrable_clm Λ hk
  · have hint : IntervalIntegrable (fun r ↦ (stateTransition A r c).comp (A r)) volume t c :=
      hk.mono_set (by rw [uIcc_of_le hab]; exact uIcc_subset_Icc ht hc)
    rw [hkeq t ht, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_id, ← hΛ,
      ← Λ.intervalIntegral_comp_comm hint]
    simp only [hΛ, ContinuousLinearMap.comp_assoc]
  · have h := congrArg (fun p : StrongDual ℝ E ↦ p.comp (stateTransition A c t)) h0
    simpa [ContinuousLinearMap.comp_assoc, stateTransition_comp_stateTransition hA hK hc ht hc,
      stateTransition_self] using h

/-- Uniqueness for the adjoint equation: a continuous solution of
`p(t) = p(c) + ∫ₜᶜ p(r) ∘ A(r) dr` on `[a, b]` is `p(c) ∘ R(t, c)`. In particular it vanishes
identically on `[a, b]` as soon as it vanishes at one point. -/
theorem eq_comp_stateTransition_of_adjoint (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {c : ℝ} (hc : c ∈ Icc a b) {p : ℝ → StrongDual ℝ E}
    (hp : ContinuousOn p (Icc a b))
    (hpeq : ∀ t ∈ Icc a b, p t = p c + ∫ r in t..c, (p r).comp (A r)) :
    ∀ t ∈ Icc a b, p t = (p c).comp (stateTransition A t c) := by
  have hab : a ≤ b := hc.1.trans hc.2
  have hK0 : 0 ≤ K := nonneg_of_norm_le hK hc
  have hsys := isLipschitzSystem_dual (E := E) K
  have hctl := isControlOn_closedBall hA hK
  obtain ⟨Cp, hCp⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  have hpsol : IsSolution (fun (p : StrongDual ℝ E) (B : E →L[ℝ] E) ↦ -(p.comp B)) A c (p c)
      a b p := by
    refine ⟨by rwa [uIcc_of_le hab], ?_, fun t ht ↦ ?_⟩
    · refine intervalIntegrable_of_norm_le hab ?_ (C := Cp * K) fun t ht ↦ ?_
      · exact (continuous_fst.clm_comp continuous_snd).neg.comp_aestronglyMeasurable
          ((hp.aestronglyMeasurable measurableSet_Icc).prodMk hA)
      · rw [norm_neg]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hCp t ht) (hK t ht) (norm_nonneg _) ((norm_nonneg _).trans (hCp t ht)))
    · rw [uIcc_of_le hab] at ht
      rw [intervalIntegral.integral_neg, ← intervalIntegral.integral_symm]
      exact hpeq t ht
  obtain ⟨⟨C, hlip⟩, hint, heq, -⟩ := adjoint_stateTransition hA hK hc (p c)
  have hqsol : IsSolution (fun (p : StrongDual ℝ E) (B : E →L[ℝ] E) ↦ -(p.comp B)) A c (p c)
      a b (fun t ↦ (p c).comp (stateTransition A t c)) := by
    refine ⟨by rw [uIcc_of_le hab]; exact hlip.continuousOn, hint.neg, fun t ht ↦ ?_⟩
    rw [uIcc_of_le hab] at ht
    rw [intervalIntegral.integral_neg, ← intervalIntegral.integral_symm]
    exact heq t ht
  exact fun t ht ↦ IsSolution.eqOn hsys hctl hc hpsol hqsol ht

/-- The resolvent depends only on the coefficient on `[a, b]`. -/
theorem stateTransition_congr (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K) {B : ℝ → E →L[ℝ] E} (hAB : EqOn A B (Icc a b)) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    stateTransition A s t = stateTransition B s t := by
  have hB : AEStronglyMeasurable B (volume.restrict (Icc a b)) :=
    hA.congr (ae_restrict_of_forall_mem measurableSet_Icc hAB)
  have hKB : ∀ t ∈ Icc a b, ‖B t‖ ≤ K := fun t ht ↦ hAB ht ▸ hK t ht
  obtain ⟨-, heq⟩ := stateTransition_eq_integral hB hKB hs
  have h := eq_stateTransition_comp hA hK hs (Y₀ := ContinuousLinearMap.id ℝ E)
    (lipschitzOnWith_stateTransition_right hB hKB hs).continuousOn (fun r hr ↦ by
      rw [heq r hr]
      congr 1
      refine intervalIntegral.integral_congr fun q hq ↦ ?_
      simp only [hAB (uIcc_subset_Icc hs hr hq)]) t ht
  rw [h, ContinuousLinearMap.comp_id]

/-- **Continuity of the resolvent in the coefficient**: if `‖A(r) - B(r)‖ ≤ η` on `[a, b]`, then
`‖R_A(s, t) - R_B(s, t)‖ ≤ e^{K(b - a)} e^{K(b - a)} η (b - a)` (Gronwall, through
`ControlSystem.norm_flow_sub_flow_control_le`). -/
theorem norm_stateTransition_sub_stateTransition_le
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b))) (hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ K)
    {B : ℝ → E →L[ℝ] E} (hB : AEStronglyMeasurable B (volume.restrict (Icc a b)))
    (hKB : ∀ t ∈ Icc a b, ‖B t‖ ≤ K) {η : ℝ} (hη : ∀ t ∈ Icc a b, ‖A t - B t‖ ≤ η) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖stateTransition A s t - stateTransition B s t‖ ≤
      Real.exp (K * (b - a)) * (Real.exp (K * (b - a)) * η * (b - a)) := by
  have hK0 : 0 ≤ K := nonneg_of_norm_le hK hs
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη s hs)
  have hts : |t - s| ≤ b - a :=
    abs_sub_le_iff.2 ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  have h := norm_flow_sub_flow_control_le (isLipschitzSystem_comp K)
    (isControlOn_closedBall hA hK) (isControlOn_closedBall hB hKB) hs ht
    (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
  rw [sub_self, norm_zero, zero_add, Real.coe_toNNReal K hK0] at h
  refine h.trans (mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hts hK0)) ?_
    (abs_nonneg _) (Real.exp_pos _).le)
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_).trans
    (mul_le_mul_of_nonneg_left hts (by positivity))
  have hr' : r ∈ Icc a b := uIcc_subset_Icc hs ht (uIoc_subset_uIcc hr)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), ← ContinuousLinearMap.sub_comp, mul_comm]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hη r hr')
    (norm_stateTransition_le_exp hB hKB hs hr') (norm_nonneg _) hη0)

end ControlSystem
