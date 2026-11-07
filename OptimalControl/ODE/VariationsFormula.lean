module

public import OptimalControl.ODE.FlowDerivative
public import OptimalControl.MeasureTheory.LebesguePoints
public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The variations formula and the cotangent lift, read pointwise

Fix a reference control `ũ` and a final time `c`, and let `P_{t → c}` be the flow of
`y' = f(y, ũ(t))`. Agrachev–Sachkov's field (12.12) is
`g_{t,w} = (P_{t → c})_* (f_w - f_{ũ(t)})`, that is
`g_{t,w}(z) = D_x P_{t → c}(P_{c → t} z) (f(P_{c → t} z, w) - f(P_{c → t} z, ũ(t)))`
(`ControlSystem.variationField`); note `g_{t,ũ(t)} = 0`. This file states:

* **the variations formula (12.13), read pointwise**
  (`ControlSystem.flow_flow_eq_add_integral_variationField`): for every control `u`, the
  transported trajectory `y(t) = P_{t → c}(x(t))`, `x(t) = P^u_{s → t}(x₀)`, solves
  `y(t) = P_{s → c}(x₀) + ∫ₛᵗ g_{r,u(r)}(y(r)) dr`. With `s = 0`, `t = c` and `x₀ = q₀` this is
  A–S's `q_u(t₁) = q₁ ∘ exp→ ∫₀^{t₁} g_{τ,u(τ)} dτ`;
* **Proposition 11.3, read pointwise** (`ControlSystem.adjoint_fderiv_flow`): along the
  reference trajectory `q̃(t) = P_{s → t}(x₀)`, the covector curve
  `λ_t = λ_c ∘ D_x P_{t → c}(q̃(t))` (A–S's `λ_t = (P^{t₁}_t)^* λ_{t₁}`, p. 172) is Lipschitz
  and solves the adjoint equation `λ_t = λ_c + ∫ₜᶜ λ_r ∘ ∂ₓf(q̃(r), ũ(r)) dr`.

## Source and reading

Agrachev–Sachkov (authors' draft), the variations formula (2.27)–(2.28) of §2.7, used at p. 170
for (12.13); Proposition 11.3 (§11.5.2, p. 161), used at p. 172 for (12.4). The chronological
calculus (operators on `C^∞(M)`) is read pointwise along trajectories in coordinates (departure
D2), with `C¹` data (D3).

## Proof

A–S derive (2.27)–(2.28) by the variation of parameters: the perturbed flow is written as a
flow `C_t` composed with the reference flow, and `C_t` is differentiated. Read pointwise, `C_t`
is `y(t) = P_{t → c}(x(t))`:

* `y` is Lipschitz on `[a, b]`: `y(t) - y(t') = P_{t' → c}(P_{t → t'}(x(t))) - P_{t' → c}(x(t'))`
  (cocycle), and the flow is Lipschitz in the point and in the time;
* at almost every `t ∈ (a, b)`, namely where `r ↦ f(x(r), u(r))` and `r ↦ f(x(r), ũ(r))` are the
  derivatives of their integrals (Lebesgue's differentiation theorem,
  `IntervalIntegrable.ae_hasDerivAt_integral`), `y(t') - y(t) = P_{t' → c}(x(t')) -
  P_{t' → c}(z(t'))` with `z(t') = P_{t → t'}(x(t))`; `x - z` has derivative
  `f(x(t), u(t)) - f(x(t), ũ(t))` at `t` (for `z` up to `∫ₜ^{t'} ‖f(z, ũ) - f(x, ũ)‖ =
  O(|t' - t|²)`), and the mean value inequality with the continuity of
  `(t', ξ) ↦ D_x P_{t' → c}(ξ)` (`ControlSystem.continuousOn_fderiv_flow`) gives
  `y'(t) = D_x P_{t → c}(x(t)) (f(x(t), u(t)) - f(x(t), ũ(t))) = g_{t,u(t)}(y(t))`;
* extended to `ℝ` by `t ↦ y(max a (min b t))`, `y` is the integral of its derivative
  (`LipschitzWith.intervalIntegral_deriv_eq_sub` in `OptimalControl/ODE/ControlSystem.lean`),
  which also gives the integrability of `r ↦ g_{r,u(r)}(y(r))`.

The second statement is `ControlSystem.fderiv_flow_eq_stateTransition` and
`ControlSystem.adjoint_stateTransition`; the coefficient `r ↦ ∂ₓf(q̃(r), ũ(r))` is measurable
because `∂ₓf`, continuous on `E × U`, extends continuously to `E × V` (Tietze;
`ContinuousOn.comp_aestronglyMeasurable_of_isClosed`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

/-- A function continuous on a closed set `S` of a normal space, composed with an a.e. strongly
measurable map with values in `S` almost everywhere, is a.e. strongly measurable (extend it to the
whole space by Tietze's theorem). -/
theorem ContinuousOn.comp_aestronglyMeasurable_of_isClosed {α X F : Type*} [MeasurableSpace α]
    {μ : Measure α} [TopologicalSpace X] [NormalSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {G : X → F} {S : Set X} (hG : ContinuousOn G S)
    (hS : IsClosed S) {g : α → X} (hg : AEStronglyMeasurable g μ)
    (hgS : ∀ᵐ x ∂μ, g x ∈ S) : AEStronglyMeasurable (fun x ↦ G (g x)) μ := by
  obtain ⟨G', hG'⟩ := ContinuousMap.exists_restrict_eq hS ⟨S.domRestrict G, hG.domRestrict⟩
  refine (G'.continuous.comp_aestronglyMeasurable hg).congr ?_
  filter_upwards [hgS] with x hx
  exact congrArg (fun φ : C(S, F) ↦ φ ⟨g x, hx⟩) hG'

namespace ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V]

/-- Agrachev–Sachkov's field (12.12), `g_{t,w} = (P_{t → c})_* (f_w - f_{ũ(t)})`, with
`P_{t → c}` the flow of the reference control `ũ`:
`g_{t,w}(z) = D_x P_{t → c}(P_{c → t} z) (f(P_{c → t} z, w) - f(P_{c → t} z, ũ(t)))`. -/
noncomputable def variationField (f : E → V → E) (ũ : ℝ → V) (c t : ℝ) (w : V) (z : E) : E :=
  fderiv ℝ (flow f ũ t c) (flow f ũ c t z) (f (flow f ũ c t z) w - f (flow f ũ c t z) (ũ t))

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] in
/-- `g_{t,ũ(t)} = 0`. -/
theorem variationField_self (f : E → V → E) (ũ : ℝ → V) (c t : ℝ) (z : E) :
    variationField f ũ c t (ũ t) z = 0 := by
  simp [variationField]

variable {f : E → V → E} {U : Set V} {M L : ℝ≥0} {ũ u : ℝ → V} {a b : ℝ}

/-- **The variations formula** (Agrachev–Sachkov (12.13), read pointwise): for every control `u`
on `[a, b]`, the trajectory `x(t) = P^u_{s → t}(x₀)` transported by the reference flow,
`y(t) = P^ũ_{t → c}(x(t))`, solves `y(t) = P^ũ_{s → c}(x₀) + ∫ₛᵗ g_{r,u(r)}(y(r)) dr` on
`[a, b]`, the integrand being integrable. -/
theorem flow_flow_eq_add_integral_variationField (hf : IsBoundedC1System f U M L)
    (hũ : IsControlOn ũ U a b) (hu : IsControlOn u U a b) {s c : ℝ} (hs : s ∈ Icc a b)
    (hc : c ∈ Icc a b) (x₀ : E) :
    IntervalIntegrable (fun r ↦ variationField f ũ c r (u r) (flow f ũ r c (flow f u s r x₀)))
        volume a b ∧
      ∀ t ∈ Icc a b, flow f ũ t c (flow f u s t x₀) = flow f ũ s c x₀ +
        ∫ r in s..t, variationField f ũ c r (u r) (flow f ũ r c (flow f u s r x₀)) := by
  borelize E
  have hL := hf.isLipschitzSystem
  have hab : a ≤ b := hs.1.trans hs.2
  have hM : ∀ y, ∀ v ∈ U, ‖f y v‖ ≤ (M : ℝ) := hf.norm_le
  have hM0 : (0 : ℝ) ≤ M := M.2
  have hL0 : (0 : ℝ) ≤ L := L.2
  set x : ℝ → E := fun t ↦ flow f u s t x₀ with hxdef
  set y : ℝ → E := fun t ↦ flow f ũ t c (x t) with hydef
  set g' : ℝ → E := fun r ↦ fderiv ℝ (flow f ũ r c) (x r) (f (x r) (u r) - f (x r) (ũ r))
    with hg'def
  have hxsol := isSolution_flow hL hu hs x₀
  have hxt : ∀ t ∈ Icc a b, ∀ t' ∈ Icc a b, ‖x t - x t'‖ ≤ M * |t - t'| :=
    fun t ht t' ht' ↦ norm_flow_sub_flow_time_le hL hu hM hs ht ht' x₀
  /- along the trajectory, `g_{r,u(r)}(y(r)) = D_x P_{r → c}(x(r)) (f(x(r), u(r)) - f(x(r), ũ(r)))`,
  since `P_{c → r}(y(r)) = x(r)` -/
  have hgg' : ∀ r ∈ Icc a b, variationField f ũ c r (u r) (y r) = g' r := by
    intro r hr
    have : flow f ũ c r (y r) = x r := by
      simp only [hydef]
      rw [flow_flow hL hũ hr hc hr, flow_self]
    simp only [variationField, this, hg'def]
  /- `y` is Lipschitz on `[a, b]`: `y(t) = P_{t' → c}(P_{t → t'}(x(t)))` -/
  have hlip : ∀ t ∈ Icc a b, ∀ t' ∈ Icc a b,
      ‖y t - y t'‖ ≤ Real.exp (L * (b - a)) * (2 * M) * |t - t'| := by
    intro t ht t' ht'
    have h1 : y t = flow f ũ t' c (flow f ũ t t' (x t)) := (flow_flow hL hũ ht ht' hc _).symm
    have h2 : ‖flow f ũ t t' (x t) - x t'‖ ≤ 2 * M * |t - t'| := by
      have h3 := norm_flow_sub_flow_time_le hL hũ hM ht ht' ht (x t)
      rw [flow_self, abs_sub_comm] at h3
      calc ‖flow f ũ t t' (x t) - x t'‖ ≤ ‖flow f ũ t t' (x t) - x t‖ + ‖x t - x t'‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ M * |t - t'| + M * |t - t'| := add_le_add h3 (hxt t ht t' ht')
        _ = 2 * M * |t - t'| := by ring
    have hexp : Real.exp (L * |c - t'|) ≤ Real.exp (L * (b - a)) := by
      gcongr
      rw [abs_le]
      constructor <;> linarith [hc.1, hc.2, ht'.1, ht'.2]
    rw [h1]
    calc ‖flow f ũ t' c (flow f ũ t t' (x t)) - flow f ũ t' c (x t')‖
        ≤ Real.exp (L * |c - t'|) * ‖flow f ũ t t' (x t) - x t'‖ :=
          norm_flow_sub_flow_le hL hũ ht' hc _ _
      _ ≤ Real.exp (L * (b - a)) * (2 * M * |t - t'|) :=
          mul_le_mul hexp h2 (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (L * (b - a)) * (2 * M) * |t - t'| := by ring
  /- the key step: `y' = g'` at almost every `t` -/
  have hderiv : ∀ᵐ t, t ∈ Ioo a b → HasDerivAt y (g' t) t := by
    have hφ₁ : IntervalIntegrable (fun r ↦ f (x r) (u r)) volume a b := hxsol.2.1
    have hxcont : ContinuousOn x (Icc a b) := by simpa [uIcc_of_le hab] using hxsol.1
    have hφ₂ : IntervalIntegrable (fun r ↦ f (x r) (ũ r)) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
      refine Integrable.of_bound ?_ M ?_
      · exact ContinuousOn.comp_aestronglyMeasurable_of_isClosed (G := fun p : E × V ↦ f p.1 p.2)
          hf.isC1On.continuousOn (isClosed_univ.prod hf.isCompact.isClosed)
          ((hxcont.aestronglyMeasurable measurableSet_Icc).prodMk hũ.aestronglyMeasurable)
          ((ae_restrict_iff' measurableSet_Icc).2
            (Eventually.of_forall fun r hr ↦ ⟨mem_univ _, hũ.mem r hr⟩))
      · exact (ae_restrict_iff' measurableSet_Icc).2
          (Eventually.of_forall fun r hr ↦ hM _ _ (hũ.mem r hr))
    filter_upwards [IntervalIntegrable.ae_hasDerivAt_integral hφ₁,
      IntervalIntegrable.ae_hasDerivAt_integral hφ₂] with t h₁ h₂ ht
    have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have htu : t ∈ uIcc a b := by rwa [uIcc_of_le hab]
    have hsu : s ∈ uIcc a b := by rwa [uIcc_of_le hab]
    have hnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    -- `x' = f(x, u)` at `t`
    have hxd : HasDerivAt x (f (x t) (u t)) t := by
      refine ((h₁ htu s hsu).const_add x₀).congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with t' ht'
      exact hxsol.2.2 t' (by rwa [uIcc_of_le hab])
    -- the reference trajectory `z` from `(t, x(t))`, and `z' = f(x(t), ũ(t))` at `t`
    set z : ℝ → E := fun t' ↦ flow f ũ t t' (x t) with hzdef
    have hzsol := isSolution_flow hL hũ htI (x t)
    have hzt : ∀ t' ∈ Icc a b, ‖z t' - x t‖ ≤ M * |t' - t| := by
      intro t' ht'
      have h3 := norm_flow_sub_flow_time_le hL hũ hM htI ht' htI (x t)
      rwa [flow_self] at h3
    have hzd : HasDerivAt z (f (x t) (ũ t)) t := by
      have he : HasDerivAt (fun t' ↦ ∫ r in t..t', (f (z r) (ũ r) - f (x r) (ũ r))) 0 t := by
        rw [hasDerivAt_iff_isLittleO]
        simp only [intervalIntegral.integral_same, sub_zero, smul_zero]
        refine Asymptotics.isLittleO_iff.2 fun ε hε ↦ ?_
        have hδ : 0 < ε / (2 * L * M + 1) := by positivity
        filter_upwards [hnhds, Metric.ball_mem_nhds t hδ] with t' ht' ht'b
        rw [mem_ball, Real.dist_eq] at ht'b
        have hbound : ∀ r ∈ Ι t t', ‖f (z r) (ũ r) - f (x r) (ũ r)‖ ≤ 2 * L * M * |t' - t| := by
          intro r hr
          have hr' : r ∈ uIcc t t' := uIoc_subset_uIcc hr
          have hrI : r ∈ Icc a b := uIcc_subset_Icc htI ht' hr'
          have hrt : |r - t| ≤ |t' - t| := abs_sub_left_of_mem_uIcc hr'
          have hlipf := (hL.lipschitzWith (ũ r) (hũ.mem r hrI)).dist_le_mul (z r) (x r)
          rw [dist_eq_norm, dist_eq_norm] at hlipf
          calc ‖f (z r) (ũ r) - f (x r) (ũ r)‖ ≤ L * ‖z r - x r‖ := hlipf
            _ ≤ L * (M * |r - t| + M * |t - r|) := by
                gcongr
                exact (norm_sub_le_norm_sub_add_norm_sub _ (x t) _).trans
                  (add_le_add (hzt r hrI) (hxt t htI r hrI))
            _ ≤ L * (M * |t' - t| + M * |t' - t|) := by
                rw [abs_sub_comm t r]; gcongr
            _ = 2 * L * M * |t' - t| := by ring
        calc ‖∫ r in t..t', (f (z r) (ũ r) - f (x r) (ũ r))‖
            ≤ 2 * L * M * |t' - t| * |t' - t| :=
              intervalIntegral.norm_integral_le_of_norm_le_const hbound
          _ ≤ ε * ‖t' - t‖ := by
              rw [Real.norm_eq_abs]
              have : 2 * L * M * |t' - t| ≤ ε := by
                calc 2 * L * M * |t' - t| ≤ (2 * L * M + 1) * (ε / (2 * L * M + 1)) := by
                      gcongr; linarith
                  _ = ε := by field_simp
              gcongr
      have hsum := (h₂ htu t htu).add he
      rw [add_zero] at hsum
      refine (hsum.const_add (x t)).congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with t' ht'
      have hI1 : IntervalIntegrable (fun r ↦ f (x r) (ũ r)) volume t t' :=
        hφ₂.mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab]))
      have hI2 : IntervalIntegrable (fun r ↦ f (z r) (ũ r) - f (x r) (ũ r)) volume t t' :=
        (hzsol.2.1.sub hφ₂).mono_set
          (uIcc_subset_uIcc (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab]))
      have hz' : z t' = x t + ∫ r in t..t', f (z r) (ũ r) :=
        hzsol.2.2 t' (by rwa [uIcc_of_le hab])
      simp only [Pi.add_apply]
      rw [← intervalIntegral.integral_add hI1 hI2, hz']
      congr 1
      refine intervalIntegral.integral_congr fun r _ ↦ ?_
      simp only [hzdef]
      abel
    -- `y(t') - y(t) = P_{t' → c}(x(t')) - P_{t' → c}(z(t'))`; the mean value inequality
    set A : E →L[ℝ] E := fderiv ℝ (flow f ũ t c) (x t) with hAdef
    have hz0 : z t = x t := flow_self _ _ _ _
    set R : ℝ → E := fun t' ↦ y t' - y t - A (x t' - z t') with hRdef
    have hR : HasDerivAt R 0 t := by
      rw [hasDerivAt_iff_isLittleO]
      have hR0 : R t = 0 := by simp [hRdef, hz0]
      simp only [hR0, sub_zero, smul_zero]
      refine Asymptotics.isLittleO_iff.2 fun ε hε ↦ ?_
      have hε₁ : 0 < ε / (2 * M + 1) := by positivity
      obtain ⟨δ, hδ, hδc⟩ := Metric.continuousOn_iff.1 (continuousOn_fderiv_flow hf hũ)
        (t, c, x t) ⟨htI, hc, mem_univ _⟩ _ hε₁
      have hδ' : 0 < δ / (M + 1) := by positivity
      filter_upwards [hnhds, Metric.ball_mem_nhds t hδ, Metric.ball_mem_nhds t hδ'] with
        t' ht' ht'δ ht'δ'
      rw [mem_ball, Real.dist_eq] at ht'δ ht'δ'
      have hMδ : (M : ℝ) * |t' - t| < δ := by
        calc (M : ℝ) * |t' - t| ≤ M * (δ / (M + 1)) := by gcongr
          _ < (M + 1) * (δ / (M + 1)) := by gcongr; linarith
          _ = δ := by field_simp
      have hxB : x t' ∈ ball (x t) δ := by
        rw [mem_ball, dist_eq_norm]
        exact (hxt t' ht' t htI).trans_lt hMδ
      have hzB : z t' ∈ ball (x t) δ := by
        rw [mem_ball, dist_eq_norm]
        exact (hzt t' ht').trans_lt hMδ
      have hbound : ∀ ξ ∈ ball (x t) δ, ‖fderiv ℝ (flow f ũ t' c) ξ - A‖ ≤ ε / (2 * M + 1) := by
        intro ξ hξ
        rw [← dist_eq_norm]
        refine (hδc (t', c, ξ) ⟨ht', hc, mem_univ _⟩ ?_).le
        rw [mem_ball] at hξ
        simp only [Prod.dist_eq, dist_self, Real.dist_eq]
        exact max_lt ht'δ (max_lt hδ hξ)
      have hdiff : ∀ ξ ∈ ball (x t) δ, DifferentiableAt ℝ (flow f ũ t' c) ξ :=
        fun ξ _ ↦ (contDiff_flow hf hũ ht' hc).differentiable one_ne_zero ξ
      have hmv := (convex_ball (x t) δ).norm_image_sub_le_of_norm_fderiv_le' hdiff hbound hzB hxB
      have hyt : y t = flow f ũ t' c (z t') := (flow_flow hL hũ htI ht' hc (x t)).symm
      have hxz : ‖x t' - z t'‖ ≤ 2 * M * |t' - t| := by
        calc ‖x t' - z t'‖ ≤ ‖x t' - x t‖ + ‖z t' - x t‖ :=
              (norm_sub_le_norm_sub_add_norm_sub _ (x t) _).trans_eq
                (by rw [norm_sub_rev (x t) (z t')])
          _ ≤ M * |t' - t| + M * |t' - t| := add_le_add (hxt t' ht' t htI) (hzt t' ht')
          _ = 2 * M * |t' - t| := by ring
      calc ‖R t'‖ = ‖flow f ũ t' c (x t') - flow f ũ t' c (z t') - A (x t' - z t')‖ := by
            rw [hRdef, hyt]
        _ ≤ ε / (2 * M + 1) * ‖x t' - z t'‖ := hmv
        _ ≤ ε / (2 * M + 1) * (2 * M * |t' - t|) := by gcongr
        _ ≤ ε * ‖t' - t‖ := by
            rw [Real.norm_eq_abs]
            have : ε / (2 * M + 1) * (2 * M) ≤ ε := by
              rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
              nlinarith
            calc ε / (2 * M + 1) * (2 * M * |t' - t|) = ε / (2 * M + 1) * (2 * M) * |t' - t| := by
                  ring
              _ ≤ ε * |t' - t| := by gcongr
    have hAD : HasDerivAt (fun t' ↦ A (x t' - z t')) (A (f (x t) (u t) - f (x t) (ũ t))) t :=
      A.hasFDerivAt.comp_hasDerivAt t (hxd.sub hzd)
    have hsum := ((hasDerivAt_const t (y t)).add hAD).add hR
    rw [zero_add, add_zero] at hsum
    convert hsum using 1
    funext t'
    simp only [Pi.add_apply, hRdef]
    abel
  /- extend `y` to a Lipschitz function on `ℝ` and apply the fundamental theorem of calculus -/
  set ŷ : ℝ → E := fun t ↦ y (max a (min b t)) with hŷdef
  have hproj : ∀ t, max a (min b t) ∈ Icc a b := fun t ↦
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hŷlip : LipschitzWith (Real.toNNReal (Real.exp (L * (b - a)) * (2 * M))) ŷ := by
    refine LipschitzWith.of_dist_le' fun t t' ↦ ?_
    rw [dist_eq_norm, Real.dist_eq]
    refine (hlip _ (hproj t) _ (hproj t')).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [max_comm a, max_comm a]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    exact abs_min_sub_min_le_max _ _ _ _ |>.trans (by simp)
  have hŷeq : ∀ t ∈ Icc a b, ŷ t = y t := fun t ht ↦ by
    simp only [hŷdef, min_eq_right ht.2, max_eq_right ht.1]
  have hae : ∀ t₀ ∈ Icc a b, ∀ t ∈ Icc a b,
      ∀ᵐ r, r ∈ Ι t₀ t → deriv ŷ r = variationField f ũ c r (u r) (y r) := by
    intro t₀ ht₀ t ht
    filter_upwards [hderiv, Measure.ae_ne volume a, Measure.ae_ne volume b] with r hr hra hrb hrI
    have hrI' : r ∈ Icc a b := uIcc_subset_Icc ht₀ ht (uIoc_subset_uIcc hrI)
    have hrab : r ∈ Ioo a b := ⟨lt_of_le_of_ne hrI'.1 hra.symm, lt_of_le_of_ne hrI'.2 hrb⟩
    rw [hgg' r hrI']
    refine ((hr hrab).congr_of_eventuallyEq ?_).deriv
    filter_upwards [Ioo_mem_nhds hrab.1 hrab.2] with t' ht'
    exact hŷeq t' (Ioo_subset_Icc_self ht')
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  refine ⟨(hŷlip.intervalIntegrable_deriv a b).congr_ae
    ((ae_restrict_iff' measurableSet_uIoc).2 (hae a haI b hbI)), fun t ht ↦ ?_⟩
  have hftc := hŷlip.intervalIntegral_deriv_eq_sub s t
  rw [intervalIntegral.integral_congr_ae (hae s hs t ht), hŷeq t ht, hŷeq s hs] at hftc
  change y t = _
  rw [hftc]
  simp only [hydef, hxdef, flow_self]
  abel

/-- **Proposition 11.3 of Agrachev–Sachkov, read pointwise**: along the reference trajectory
`q̃(t) = P_{s → t}(x₀)`, for a covector `λ_c`, the curve `λ_t = λ_c ∘ D_x P_{t → c}(q̃(t))` is
Lipschitz on `[a, b]` and solves the adjoint equation
`λ_t = λ_c + ∫ₜᶜ λ_r ∘ ∂ₓf(q̃(r), ũ(r)) dr`. -/
theorem adjoint_fderiv_flow (hf : IsBoundedC1System f U M L) (hũ : IsControlOn ũ U a b)
    {s c : ℝ} (hs : s ∈ Icc a b) (hc : c ∈ Icc a b) (x₀ : E) (ℓ : StrongDual ℝ E) :
    (∃ K, LipschitzOnWith K (fun t ↦ ℓ.comp (fderiv ℝ (flow f ũ t c) (flow f ũ s t x₀)))
        (Icc a b)) ∧
      ∀ t ∈ Icc a b, ℓ.comp (fderiv ℝ (flow f ũ t c) (flow f ũ s t x₀)) = ℓ +
        ∫ r in t..c, (ℓ.comp (fderiv ℝ (flow f ũ r c) (flow f ũ s r x₀))).comp
          (fderiv ℝ (f · (ũ r)) (flow f ũ s r x₀)) := by
  have hL := hf.isLipschitzSystem
  have hab : a ≤ b := hs.1.trans hs.2
  set A : ℝ → E →L[ℝ] E := fun r ↦ fderiv ℝ (f · (ũ r)) (flow f ũ s r x₀) with hAdef
  have hcont : ContinuousOn (fun r ↦ flow f ũ s r x₀) (Icc a b) := by
    simpa [uIcc_of_le hab] using (isSolution_flow hL hũ hs x₀).1
  have hA : AEStronglyMeasurable A (volume.restrict (Icc a b)) :=
    ContinuousOn.comp_aestronglyMeasurable_of_isClosed
      (G := fun p : E × V ↦ fderiv ℝ (f · p.2) p.1) hf.isC1On.continuousOn_fderiv
      (isClosed_univ.prod hf.isCompact.isClosed)
      ((hcont.aestronglyMeasurable measurableSet_Icc).prodMk hũ.aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Icc).2
        (Eventually.of_forall fun r hr ↦ ⟨mem_univ _, hũ.mem r hr⟩))
  have hK : ∀ t ∈ Icc a b, ‖A t‖ ≤ (L : ℝ) := fun t ht ↦ hf.norm_fderiv_le _ _ (hũ.mem t ht)
  obtain ⟨⟨C, hC⟩, -, heq, -⟩ := adjoint_stateTransition hA hK hc ℓ
  have hfd : ∀ t ∈ Icc a b, fderiv ℝ (flow f ũ t c) (flow f ũ s t x₀) = stateTransition A t c :=
    fun t ht ↦ fderiv_flow_eq_stateTransition hf hũ hs hc x₀ ht
  refine ⟨⟨C, fun t ht t' ht' ↦ ?_⟩, fun t ht ↦ ?_⟩
  · simpa only [hfd t ht, hfd t' ht'] using hC ht ht'
  · rw [hfd t ht, heq t ht]
    congr 1
    refine intervalIntegral.integral_congr fun r hr ↦ ?_
    rw [hfd r (uIcc_subset_Icc ht hc hr)]

end ControlSystem
