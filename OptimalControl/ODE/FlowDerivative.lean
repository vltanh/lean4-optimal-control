module

public import OptimalControl.ODE.LinearCaratheodory

/-!
# Differentiability of the flow with respect to the initial point

For a globally bounded `C¹` control system (`ControlSystem.IsBoundedC1System`) driven by a
control `u` on `[a, b]`, the flow `x ↦ P_{s → t}(x)` is differentiable, and its derivative is
the resolvent of the variational equation along the trajectory:
`D_x P_{s → t}(x) = R(s, t)` for `A(r) = ∂ₓf(P_{s → r}(x), u(r))`
(`ControlSystem.hasFDerivAt_flow`). The derivative is jointly continuous in `(s, t, x)`, and
along a trajectory the derivative from an intermediate time is the resolvent between the two
times (`ControlSystem.fderiv_flow_eq_stateTransition`).

## Source and reading

Agrachev–Sachkov (authors' draft), §2.8, formula (2.19) for the derivative of a flow (used in
the proof of Theorem 12.4 (2), p. 182: `∂F/∂q v = Φ_* P^{t₁}_* v`), and the claim of §2.4.1
that the Carathéodory solution is smooth in the initial point, cited to Gamkrelidze [8].
Read pointwise in coordinates (departure D2) and with `C¹` data (D3);
proved by the standard argument (D11).

## Proof sketch

Gronwall: `w(t) = P_{s → t}(x + h) - P_{s → t}(x)` and `R(s, t) h` solve the affine equation
`z' = A(r) z + v(r)` from `h`, with `v = ρ_h` the first-order remainder
`f(P_{s → r}(x + h), u(r)) - f(P_{s → r}(x), u(r)) - A(r) w(r)` and with `v = 0` respectively.
The remainder is `≤ ε e^{L(b - a)} ‖h‖` for small `h`, uniformly in `r`, by the mean value
inequality, because `∂ₓf` is uniformly continuous on the compact
`cthickening 1 (P_{s → ·}(x) '' [a, b]) × U` and `‖w(r)‖ ≤ e^{L(b - a)} ‖h‖`; the comparison of
the two "controls" `(A, ρ_h)` and `(A, 0)` (`ControlSystem.norm_flow_sub_flow_control_le`)
then gives `‖w(t) - R(s, t) h‖ ≤ e^{L(b - a)} (b - a) sup ‖ρ_h‖ = o(‖h‖)`. Joint continuity of
the derivative: `R_A(s, t)` is Lipschitz in `s` and in `t`, and continuous in the coefficient
(`ControlSystem.norm_stateTransition_sub_stateTransition_le`), and the coefficients along
`P_{s' → ·}(x')` and `P_{s → ·}(x) = P_{s' → ·}(P_{s → s'}(x))` are uniformly close for
`(s', x')` near `(s, x)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {f : E → V → E} {U : Set V} {M L : ℝ≥0} {u : ℝ → V} {a b : ℝ}

/-! ### Auxiliary facts -/

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- `r ↦ G(z(r), u(r))` is a.e. strongly measurable on `[a, b]` for `G` continuous on `E × U`
(`U` closed), `z` continuous on `[a, b]` and `u` a control. -/
private theorem aestronglyMeasurable_comp_control {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] {G : E → V → W}
    (hG : ContinuousOn (fun p : E × V ↦ G p.1 p.2) (univ ×ˢ U)) (hU : IsClosed U)
    {z : ℝ → E} (hz : ContinuousOn z (Icc a b)) (hu : IsControlOn u U a b) :
    AEStronglyMeasurable (fun r ↦ G (z r) (u r)) (volume.restrict (Icc a b)) := by
  classical
  let : MeasurableSpace (E × V) := borel _
  have : BorelSpace (E × V) := ⟨rfl⟩
  let : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hS : MeasurableSet (univ ×ˢ U : Set (E × V)) := (isClosed_univ.prod hU).measurableSet
  have hp : AEStronglyMeasurable (fun r ↦ (z r, u r)) (volume.restrict (Icc a b)) :=
    (hz.aestronglyMeasurable measurableSet_Icc).prodMk hu.aestronglyMeasurable
  have hmeas : Measurable ((univ ×ˢ U).piecewise (fun p : E × V ↦ G p.1 p.2) fun _ ↦ 0) :=
    hG.measurable_piecewise continuousOn_const hS
  refine (hmeas.comp_aemeasurable hp.aemeasurable).aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  simp [Set.piecewise, hu.mem r hr]

/-- The coefficient `A(r) = ∂ₓf(P_{s → r}(x), u(r))` of the variational equation along the
trajectory from `(s, x)`. -/
private noncomputable def lin (f : E → V → E) (u : ℝ → V) (s : ℝ) (x : E) (r : ℝ) : E →L[ℝ] E :=
  fderiv ℝ (f · (u r)) (flow f u s r x)

private theorem continuousOn_flow_right (hf : IsBoundedC1System f U M L)
    (hu : IsControlOn u U a b) {s : ℝ} (hs : s ∈ Icc a b) (x : E) :
    ContinuousOn (fun r ↦ flow f u s r x) (Icc a b) := by
  have h := (isSolution_flow hf.isLipschitzSystem hu hs x).1
  rwa [uIcc_of_le (hs.1.trans hs.2)] at h

private theorem aestronglyMeasurable_lin (hf : IsBoundedC1System f U M L)
    (hu : IsControlOn u U a b) {s : ℝ} (hs : s ∈ Icc a b) (x : E) :
    AEStronglyMeasurable (lin f u s x) (volume.restrict (Icc a b)) :=
  aestronglyMeasurable_comp_control (G := fun z v ↦ fderiv ℝ (f · v) z)
    hf.isC1On.continuousOn_fderiv hf.isCompact.isClosed (continuousOn_flow_right hf hu hs x) hu

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private theorem norm_lin_le (hf : IsBoundedC1System f U M L) (hu : IsControlOn u U a b)
    {s : ℝ} {x : E} {r : ℝ} (hr : r ∈ Icc a b) : ‖lin f u s x r‖ ≤ L :=
  hf.norm_fderiv_le _ _ (hu.mem r hr)

private theorem norm_flow_sub_le_exp (hf : IsBoundedC1System f U M L)
    (hu : IsControlOn u U a b) {s r : ℝ} (hs : s ∈ Icc a b) (hr : r ∈ Icc a b) (x x' : E) :
    ‖flow f u s r x' - flow f u s r x‖ ≤ Real.exp (L * (b - a)) * ‖x' - x‖ :=
  (norm_flow_sub_flow_le hf.isLipschitzSystem hu hs hr x' x).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
      (abs_sub_le_iff.2 ⟨by linarith [hs.1, hr.2], by linarith [hs.2, hr.1]⟩) L.2))
      (norm_nonneg _))

/-- The affine system `z' = B z + v` driven by `(B, v)` in a product of closed balls. -/
private theorem isLipschitzSystem_affine (L : ℝ≥0) (ρ : ℝ) :
    IsLipschitzSystem (fun (z : E) (p : (E →L[ℝ] E) × E) ↦ p.1 z + p.2)
      (closedBall (0 : E →L[ℝ] E) L ×ˢ closedBall (0 : E) ρ) L where
  isCompact := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  continuousOn :=
    ((continuous_snd.fst.clm_apply continuous_fst).add continuous_snd.snd).continuousOn
  lipschitzWith p hp := by
    refine LipschitzWith.of_dist_le_mul fun z z' ↦ ?_
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub]
    exact p.1.le_of_opNorm_le (mem_closedBall_zero_iff.1 hp.1) _

/-- Uniform continuity of `∂ₓf` near the trajectory from `(s, x)`: for `ε > 0` there is
`δ ∈ (0, 1]` with `‖∂ₓf(z, v) - ∂ₓf(P_{s → r}(x), v)‖ < ε` for `r ∈ [a, b]`, `v ∈ U` and
`‖z - P_{s → r}(x)‖ < δ` (`∂ₓf` is uniformly continuous on the compact
`cthickening 1 (P_{s → ·}(x) '' [a, b]) × U`). -/
private theorem exists_delta_fderiv (hf : IsBoundedC1System f U M L)
    (hu : IsControlOn u U a b) {s : ℝ} (hs : s ∈ Icc a b) (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ r ∈ Icc a b, ∀ v ∈ U, ∀ z, ‖z - flow f u s r x‖ < δ →
      ‖fderiv ℝ (f · v) z - fderiv ℝ (f · v) (flow f u s r x)‖ < ε := by
  have hy := continuousOn_flow_right hf hu hs x
  have hK : IsCompact (cthickening 1 ((fun r ↦ flow f u s r x) '' Icc a b)) :=
    (isCompact_Icc.image_of_continuousOn hy).cthickening
  have hG := (hK.prod hf.isCompact).uniformContinuousOn_of_continuous
    (hf.isC1On.continuousOn_fderiv.mono (prod_mono (subset_univ _) subset_rfl))
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff.1 hG ε hε
  refine ⟨min δ 1, by positivity, min_le_right _ _, fun r hr v hv z hz ↦ ?_⟩
  have hyr : flow f u s r x ∈ (fun r ↦ flow f u s r x) '' Icc a b := mem_image_of_mem _ hr
  have hzK := mem_cthickening_of_dist_le z _ 1 _ hyr
    (by rw [dist_eq_norm]; exact hz.le.trans (min_le_right _ _))
  have h := hδG (z, v) ⟨hzK, hv⟩ (flow f u s r x, v) ⟨self_subset_cthickening _ hyr, hv⟩
    (by rw [Prod.dist_eq, dist_self, dist_eq_norm]
        exact max_lt (hz.trans_le (min_le_left _ _)) hδ)
  rwa [dist_eq_norm] at h

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The first-order remainder of `f(·, v)` at `y`, by the mean value inequality:
`‖f(y + w, v) - f(y, v) - ∂ₓf(y, v) w‖ ≤ ε ‖w‖` if `‖∂ₓf(z, v) - ∂ₓf(y, v)‖ ≤ ε` on the closed
ball of radius `‖w‖` around `y`. -/
private theorem norm_remainder_le (hf : IsBoundedC1System f U M L) {y w : E} {v : V}
    (hv : v ∈ U) {ε : ℝ}
    (hε : ∀ z, ‖z - y‖ ≤ ‖w‖ → ‖fderiv ℝ (f · v) z - fderiv ℝ (f · v) y‖ ≤ ε) :
    ‖f (y + w) v - f y v - fderiv ℝ (f · v) y w‖ ≤ ε * ‖w‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z ↦ f z v - fderiv ℝ (f · v) y z)
    (f' := fun z ↦ fderiv ℝ (f · v) z - fderiv ℝ (f · v) y)
    (s := closedBall y ‖w‖) (x := y) (y := y + w) (C := ε)
    (fun z _ ↦ ((hf.isC1On.differentiableAt z (mem_univ _) v hv).hasFDerivAt.sub
      (fderiv ℝ (f · v) y).hasFDerivAt).hasFDerivWithinAt)
    (fun z hz ↦ hε z (by rw [← dist_eq_norm]; exact hz))
    (convex_closedBall _ _) (mem_closedBall_self (norm_nonneg _))
    (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left])
  rw [add_sub_cancel_left, map_add] at h
  convert h using 2
  abel

/-! ### The derivative of the flow -/

/-- **Derivative of the flow** (Agrachev–Sachkov (2.19), read pointwise):
`D_x P_{s → t}(x) = R(s, t)`, the resolvent of the variational equation
`ξ' = ∂ₓf(P_{s → r}(x), u(r)) ξ`.

Departure from the source (D2, D11): A–S obtain (2.19) in the chronological calculus, for smooth
complete fields; here it is proved by Gronwall's inequality (see the module docstring). -/
theorem hasFDerivAt_flow (hf : IsBoundedC1System f U M L) (hu : IsControlOn u U a b) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    HasFDerivAt (flow f u s t)
      (stateTransition (fun r ↦ fderiv ℝ (f · (u r)) (flow f u s r x)) s t) x := by
  change HasFDerivAt (flow f u s t) (stateTransition (lin f u s x) s t) x
  have hab : a ≤ b := hs.1.trans hs.2
  have hlip := hf.isLipschitzSystem
  have hAm := aestronglyMeasurable_lin hf hu hs x
  have hAK : ∀ r ∈ Icc a b, ‖lin f u s x r‖ ≤ (L : ℝ) := fun r hr ↦ norm_lin_le hf hu hr
  set C₀ := Real.exp (L * (b - a)) with hC₀def
  have hC₀ : 0 < C₀ := Real.exp_pos _
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  set ε' := ε / (C₀ * C₀ * (b - a + 1)) with hε'def
  have hba : 0 < b - a + 1 := by linarith
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ, hδ, -, hδf⟩ := exists_delta_fderiv hf hu hs x hε'
  filter_upwards [Metric.ball_mem_nhds (0 : E) (div_pos hδ hC₀)] with h hh
  rw [mem_ball_zero_iff, lt_div_iff₀' hC₀] at hh
  -- the remainder `ρ` and its bound
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ → E, ρ = fun r ↦ f (flow f u s r (x + h)) (u r) -
      f (flow f u s r x) (u r) - lin f u s x r (flow f u s r (x + h) - flow f u s r x) :=
    ⟨_, rfl⟩
  set Rb := ε' * (C₀ * ‖h‖) with hRb
  have hRb0 : 0 ≤ Rb := by positivity
  have hw : ∀ r ∈ Icc a b, ‖flow f u s r (x + h) - flow f u s r x‖ ≤ C₀ * ‖h‖ := fun r hr ↦ by
    simpa using norm_flow_sub_le_exp hf hu hs hr x (x + h)
  have hρ : ∀ r ∈ Icc a b, ‖ρ r‖ ≤ Rb := by
    intro r hr
    have h1 := norm_remainder_le hf (hu.mem r hr) (y := flow f u s r x)
      (w := flow f u s r (x + h) - flow f u s r x) (ε := ε') (fun z hz ↦
        (hδf r hr (u r) (hu.mem r hr) z (hz.trans_lt ((hw r hr).trans_lt hh))).le)
    rw [add_sub_cancel] at h1
    rw [hρdef]
    exact h1.trans (mul_le_mul_of_nonneg_left (hw r hr) hε'.le)
  have hfm : ∀ x', AEStronglyMeasurable (fun r ↦ f (flow f u s r x') (u r))
      (volume.restrict (Icc a b)) := fun x' ↦
    aestronglyMeasurable_comp_control hf.isC1On.continuousOn hf.isCompact.isClosed
      (continuousOn_flow_right hf hu hs x') hu
  have hρm : AEStronglyMeasurable ρ (volume.restrict (Icc a b)) := by
    rw [hρdef]
    exact ((hfm (x + h)).sub (hfm x)).sub ((continuous_fst.clm_apply
      continuous_snd).comp_aestronglyMeasurable (hAm.prodMk
        (((continuousOn_flow_right hf hu hs (x + h)).sub
          (continuousOn_flow_right hf hu hs x)).aestronglyMeasurable measurableSet_Icc)))
  -- the affine system `z' = A(r) z + v(r)`, driven by `(A, ρ)` and by `(A, 0)`
  have hsys := isLipschitzSystem_affine (E := E) L Rb
  have hc₁ : IsControlOn (fun r ↦ (lin f u s x r, ρ r)) (closedBall 0 L ×ˢ closedBall 0 Rb) a b :=
    ⟨hAm.prodMk hρm, fun r hr ↦
      ⟨mem_closedBall_zero_iff.2 (hAK r hr), mem_closedBall_zero_iff.2 (hρ r hr)⟩⟩
  have hc₂ : IsControlOn (fun r ↦ (lin f u s x r, (0 : E))) (closedBall 0 L ×ˢ closedBall 0 Rb)
      a b :=
    ⟨hAm.prodMk aestronglyMeasurable_const, fun r hr ↦
      ⟨mem_closedBall_zero_iff.2 (hAK r hr), mem_closedBall_self hRb0⟩⟩
  -- `P_{s → ·}(x + h) - P_{s → ·}(x)` solves the first, `R(s, ·) h` the second
  have hsol_h := isSolution_flow hlip hu hs (x + h)
  have hsol_0 := isSolution_flow hlip hu hs x
  have hfun : ∀ r, lin f u s x r (flow f u s r (x + h) - flow f u s r x) + ρ r =
      f (flow f u s r (x + h)) (u r) - f (flow f u s r x) (u r) := fun r ↦ by
    rw [hρdef]; exact add_sub_cancel _ _
  have hW : IsSolution (fun (z : E) (p : (E →L[ℝ] E) × E) ↦ p.1 z + p.2)
      (fun r ↦ (lin f u s x r, ρ r)) s h a b
      (fun r ↦ flow f u s r (x + h) - flow f u s r x) := by
    refine ⟨hsol_h.1.sub hsol_0.1, ?_, fun r hr ↦ ?_⟩
    · simp only [hfun]
      exact hsol_h.2.1.sub hsol_0.2.1
    · have hsr : [[s, r]] ⊆ [[a, b]] := uIcc_subset_uIcc (Icc_subset_uIcc hs) hr
      simp only [hfun]
      rw [intervalIntegral.integral_sub (hsol_h.2.1.mono_set hsr) (hsol_0.2.1.mono_set hsr)]
      have e1 := hsol_h.2.2 r hr
      have e0 := hsol_0.2.2 r hr
      simp only at e1 e0
      rw [e1, e0]
      abel
  obtain ⟨hint, heq⟩ := stateTransition_eq_integral hAm hAK hs
  have hRc : ContinuousOn (fun r ↦ stateTransition (lin f u s x) s r) (Icc a b) :=
    (lipschitzOnWith_stateTransition_right hAm hAK hs).continuousOn
  have hR : IsSolution (fun (z : E) (p : (E →L[ℝ] E) × E) ↦ p.1 z + p.2)
      (fun r ↦ (lin f u s x r, (0 : E))) s h a b
      (fun r ↦ stateTransition (lin f u s x) s r h) := by
    refine ⟨?_, ?_, fun r hr ↦ ?_⟩
    · rw [uIcc_of_le hab]; exact hRc.clm_apply continuousOn_const
    · simp only [add_zero, IntervalIntegrable, IntegrableOn]
      exact ⟨by simpa using (ContinuousLinearMap.apply ℝ E h).integrable_comp hint.1,
        by simpa using (ContinuousLinearMap.apply ℝ E h).integrable_comp hint.2⟩
    · have hsr : [[s, r]] ⊆ [[a, b]] := uIcc_subset_uIcc (Icc_subset_uIcc hs) hr
      rw [uIcc_of_le hab] at hr
      simp only [add_zero]
      rw [heq r hr, add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.intervalIntegral_apply (hint.mono_set hsr)]
      rfl
  -- Gronwall, through the comparison of the two controls
  have hcmp := norm_flow_sub_flow_control_le hsys hc₁ hc₂ hs ht h h
  rw [IsSolution.flow_eq hsys hc₁ hs hW ht, IsSolution.flow_eq hsys hc₂ hs hR ht, sub_self,
    norm_zero, zero_add] at hcmp
  have hts : |t - s| ≤ b - a :=
    abs_sub_le_iff.2 ⟨by linarith [hs.1, ht.2], by linarith [hs.2, ht.1]⟩
  have key : ‖flow f u s t (x + h) - flow f u s t x - stateTransition (lin f u s x) s t h‖ ≤
      Real.exp (L * |t - s|) * (Rb * |t - s|) := by
    refine hcmp.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦ ?_
    have hr' : r ∈ Icc a b := uIcc_subset_Icc hs ht (uIoc_subset_uIcc hr)
    simpa using hρ r hr'
  calc ‖flow f u s t (x + h) - flow f u s t x - stateTransition (lin f u s x) s t h‖
      ≤ Real.exp (L * |t - s|) * (Rb * |t - s|) := key
    _ ≤ C₀ * (Rb * (b - a + 1)) :=
        mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hts L.2))
          (mul_le_mul_of_nonneg_left (by linarith) hRb0) (by positivity) hC₀.le
    _ = ε * ‖h‖ := by
        rw [hRb, hε'def]
        field_simp

/-- The derivative of the flow is jointly continuous in the initial time, the final time and the
initial point. -/
theorem continuousOn_fderiv_flow (hf : IsBoundedC1System f U M L) (hu : IsControlOn u U a b) :
    ContinuousOn (fun p : ℝ × ℝ × E ↦ fderiv ℝ (flow f u p.1 p.2.1) p.2.2)
      (Icc a b ×ˢ Icc a b ×ˢ univ) := by
  have hlip := hf.isLipschitzSystem
  refine ContinuousOn.congr (f := fun p : ℝ × ℝ × E ↦ stateTransition (lin f u p.1 p.2.2) p.1 p.2.1)
    ?_ fun p hp ↦ (hasFDerivAt_flow hf hu hp.1 hp.2.1 p.2.2).fderiv
  rintro ⟨s, t, x⟩ ⟨hs, ht, -⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hab : a ≤ b := hs.1.trans hs.2
  set C := Real.exp (L * (b - a)) with hCdef
  have hC1 : 1 ≤ C := Real.one_le_exp (mul_nonneg L.2 (by linarith))
  have hC0 : 0 < C := by linarith
  set C₁ := C * (L * C) with hC₁def
  have hC₁0 : 0 ≤ C₁ := by positivity
  set C₂ := C * C * (b - a + 1) with hC₂def
  have hC₂0 : 0 ≤ C₂ := mul_nonneg (by positivity) (by linarith)
  set ε' := ε / (4 * (C₂ + 1)) with hε'def
  obtain ⟨δ, hδ, -, hδf⟩ := exists_delta_fderiv hf hu hs x (ε := ε') (by positivity)
  set δ₀ := min (ε / (4 * (C₁ + 1))) (δ / (2 * (C * (M + 1)))) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (by positivity) (by positivity)
  refine ⟨δ₀, hδ₀, ?_⟩
  rintro ⟨s', t', x'⟩ ⟨hs', ht', -⟩ hdist
  rw [Prod.dist_eq, Prod.dist_eq] at hdist
  simp only [dist_eq_norm, max_lt_iff] at hdist
  obtain ⟨hds, hdt, hdx⟩ := hdist
  have hds1 : |s' - s| ≤ ε / (4 * (C₁ + 1)) := hds.le.trans (min_le_left _ _)
  have hdt1 : |t' - t| ≤ ε / (4 * (C₁ + 1)) := hdt.le.trans (min_le_left _ _)
  have hds2 : |s' - s| ≤ δ / (2 * (C * (M + 1))) := hds.le.trans (min_le_right _ _)
  have hdx2 : ‖x' - x‖ ≤ δ / (2 * (C * (M + 1))) := hdx.le.trans (min_le_right _ _)
  have hAm := aestronglyMeasurable_lin hf hu hs x
  have hBm := aestronglyMeasurable_lin hf hu hs' x'
  have hAK : ∀ r ∈ Icc a b, ‖lin f u s x r‖ ≤ (L : ℝ) := fun r hr ↦ norm_lin_le hf hu hr
  have hBK : ∀ r ∈ Icc a b, ‖lin f u s' x' r‖ ≤ (L : ℝ) := fun r hr ↦ norm_lin_le hf hu hr
  -- the trajectories from `(s, x)` and `(s', x')` are `δ`-close
  have hclose : ∀ r ∈ Icc a b, ‖flow f u s' r x' - flow f u s r x‖ < δ := by
    intro r hr
    rw [← flow_flow hlip hu hs hs' hr x]
    have h1 := norm_flow_sub_le_exp hf hu hs' hr (flow f u s s' x) x'
    have h2 := norm_flow_sub_flow_time_le hlip hu (M := M) (fun y v hv ↦ hf.norm_le y v hv)
      hs hs hs' x
    rw [flow_self] at h2
    have h3 : ‖x' - flow f u s s' x‖ ≤ ‖x' - x‖ + M * |s' - s| := by
      calc ‖x' - flow f u s s' x‖ = ‖(x' - x) + (x - flow f u s s' x)‖ := by abel_nf
        _ ≤ ‖x' - x‖ + ‖x - flow f u s s' x‖ := norm_add_le _ _
        _ ≤ ‖x' - x‖ + M * |s' - s| := by rw [abs_sub_comm]; gcongr
    have hM : (0 : ℝ) ≤ M := M.2
    calc ‖flow f u s' r x' - flow f u s' r (flow f u s s' x)‖
        ≤ C * ‖x' - flow f u s s' x‖ := h1
      _ ≤ C * (‖x' - x‖ + M * |s' - s|) := by gcongr
      _ ≤ C * (δ / (2 * (C * (M + 1))) + M * (δ / (2 * (C * (M + 1))))) := by gcongr
      _ = δ / 2 := by field_simp; ring
      _ < δ := half_lt_self hδ
  have hη : ∀ r ∈ Icc a b, ‖lin f u s' x' r - lin f u s x r‖ ≤ ε' := fun r hr ↦
    (hδf r hr (u r) (hu.mem r hr) _ (hclose r hr)).le
  -- the three terms
  have T1 : ‖stateTransition (lin f u s' x') s' t' - stateTransition (lin f u s' x') s' t‖ ≤
      C₁ * |t' - t| := by
    have h := (lipschitzOnWith_stateTransition_right hBm hBK hs').dist_le_mul t' ht' t ht
    rw [dist_eq_norm, Real.coe_toNNReal _ (by positivity), Real.dist_eq] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
    rw [hC₁def]
    nlinarith [L.2]
  have T2 := norm_stateTransition_sub_stateTransition_le hBm hBK hAm hAK hη hs' ht
  have T3 : ‖stateTransition (lin f u s x) s' t - stateTransition (lin f u s x) s t‖ ≤
      C₁ * |s' - s| := by
    have h := (lipschitzOnWith_stateTransition_left hAm hAK ht).dist_le_mul s' hs' s hs
    rwa [dist_eq_norm, Real.coe_toNNReal _ (by positivity), Real.dist_eq] at h
  have e1 : C₁ * |t' - t| ≤ ε / 4 := by
    calc C₁ * |t' - t| ≤ C₁ * (ε / (4 * (C₁ + 1))) := mul_le_mul_of_nonneg_left hdt1 hC₁0
      _ ≤ ε / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have e3 : C₁ * |s' - s| ≤ ε / 4 := by
    calc C₁ * |s' - s| ≤ C₁ * (ε / (4 * (C₁ + 1))) := mul_le_mul_of_nonneg_left hds1 hC₁0
      _ ≤ ε / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have e2 : C * (C * ε' * (b - a)) ≤ ε / 4 := by
    calc C * (C * ε' * (b - a)) ≤ C₂ * ε' := by
          rw [hC₂def]
          have : 0 ≤ C * C * ε' := by positivity
          nlinarith
      _ ≤ ε / 4 := by
        rw [hε'def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  rw [dist_eq_norm]
  calc ‖stateTransition (lin f u s' x') s' t' - stateTransition (lin f u s x) s t‖
      = ‖(stateTransition (lin f u s' x') s' t' - stateTransition (lin f u s' x') s' t) +
          (stateTransition (lin f u s' x') s' t - stateTransition (lin f u s x) s' t) +
          (stateTransition (lin f u s x) s' t - stateTransition (lin f u s x) s t)‖ := by
        congr 1; abel
    _ ≤ _ := norm_add₃_le
    _ ≤ C₁ * |t' - t| + C * (C * ε' * (b - a)) + C₁ * |s' - s| := by gcongr
    _ < ε := by linarith

/-- The flow is `C¹` in the initial point. -/
theorem contDiff_flow (hf : IsBoundedC1System f U M L) (hu : IsControlOn u U a b) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : ContDiff ℝ 1 (flow f u s t) := by
  refine contDiff_one_iff_fderiv.2
    ⟨fun x ↦ (hasFDerivAt_flow hf hu hs ht x).differentiableAt, ?_⟩
  rw [← continuousOn_univ]
  exact (continuousOn_fderiv_flow hf hu).comp
    (continuousOn_const.prodMk (continuousOn_const.prodMk continuousOn_id))
    fun x _ ↦ ⟨hs, ht, mem_univ x⟩

/-- Along the trajectory `r ↦ P_{s → r}(x₀)`, the derivative of the flow from the intermediate
time `t` to `c` is the resolvent `R(t, c)` of the variational equation along that trajectory
(from `hasFDerivAt_flow` and the cocycle property). -/
theorem fderiv_flow_eq_stateTransition (hf : IsBoundedC1System f U M L) (hu : IsControlOn u U a b)
    {s c : ℝ} (hs : s ∈ Icc a b) (hc : c ∈ Icc a b) (x₀ : E) {t : ℝ} (ht : t ∈ Icc a b) :
    fderiv ℝ (flow f u t c) (flow f u s t x₀) =
      stateTransition (fun r ↦ fderiv ℝ (f · (u r)) (flow f u s r x₀)) t c := by
  rw [(hasFDerivAt_flow hf hu ht hc (flow f u s t x₀)).fderiv]
  refine stateTransition_congr (aestronglyMeasurable_lin hf hu ht _)
    (fun r hr ↦ norm_lin_le hf hu hr) (fun r hr ↦ ?_) ht hc
  change fderiv ℝ (f · (u r)) (flow f u t r (flow f u s t x₀)) =
    fderiv ℝ (f · (u r)) (flow f u s r x₀)
  rw [flow_flow hf.isLipschitzSystem hu hs ht hr]

end ControlSystem
