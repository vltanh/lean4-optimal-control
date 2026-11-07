module

public import OptimalControl.ODE.ControlSystem
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Carathéodory solutions of control systems: well-posedness and flows

For a control system `y' = f(y, u(t))` on a finite-dimensional real normed space `E`, with
controls in a finite-dimensional real normed space `V`, a compact control set `U ⊆ V` and a
control `u` that is (a.e. strongly) measurable with values in `U`, this file states:

* the *standing hypotheses* (`ControlSystem.IsLipschitzSystem`): `f` jointly continuous on
  `E × U` and `L`-Lipschitz in the state for every control value in `U`;
* the regularity of Agrachev–Sachkov's control systems (`ControlSystem.IsC1On`), conditions
  (10.2)–(10.4) of their §10.1 with `C¹` in place of `C^∞`, on an open set `Ω`, and its global
  bounded form (`ControlSystem.IsBoundedC1System`);
* existence and uniqueness of Carathéodory solutions (`ControlSystem.IsSolution`) through every
  point, forward and backward in time (`ControlSystem.exists_isSolution`,
  `ControlSystem.IsSolution.eqOn`), the integral Gronwall inequality, and the *flow*
  `ControlSystem.flow f u s t x` (the value at time `t` of the solution with value `x` at time
  `s`): its cocycle property, its Lipschitz dependence on the initial point (`e^{L|t - s|}`) and
  on the time (`M`), its continuity, and the estimate comparing the trajectories of two controls;
* the *cut-off* (`ControlSystem.IsC1On.exists_cutoff`): a `C¹` system on an open set `Ω`
  agrees, near a compact subset of `Ω`, with a globally bounded system whose state derivative is
  globally bounded.

## Source and reading

Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint* (authors' draft, §2.4.1 and
§10.1, p. 133), take these facts from "the classical Carathéodory Theorem (see e.g. [8])",
[8] = R. V. Gamkrelidze, *Principles of optimal control theory*, Plenum 1978, and assume
complete vector fields (for instance with compact support). Departure D11 (the departures from
Agrachev–Sachkov are listed in the README): the cited texts were not consulted; the facts are
proved by the standard Picard iteration and Gronwall argument, and the cut-off to a compact tube
replaces A–S's completeness assumption. The flow is defined by choice from the solution on the
interval between the two times, so that it depends only on the control there.

## Proof sketch

Picard's operator `y ↦ x + ∫ₛ f(y, u)` is a contraction for the weighted norm
`sup e^{-λ|t - s|}‖y(t)‖`, `λ = 2L + 1`; we write it as the operator
`z ↦ e^{-λ|· - s|} (x + ∫ₛ f(e^{λ|· - s|} z, u))` on `C([a, b], E)` with its sup norm, a
contraction with constant `1/2`, and take its fixed point (`ContractingWith.fixedPoint`).
Measurability of `t ↦ f(y(t), u(t))` comes from a continuous (Tietze) extension of `f` off
`E × U`. Uniqueness and the Lipschitz estimates follow from the integral Gronwall inequality
(`ControlSystem.le_mul_exp_of_le_add_integral`, from Mathlib's
`norm_le_gronwallBound_of_norm_deriv_right_le` applied to `C + L ∫ φ`), used forward and, after
the reflection `t ↦ -t`, backward in time. The cocycle property is uniqueness on the
subinterval. The cut-off multiplies `f` by a smooth function equal to `1` on `cthickening δ K`
and supported in `thickening (2δ) K`, where `cthickening (2δ) K ⊆ Ω`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace ControlSystem

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-! ### Regularity of control systems -/

/-- The regularity of Agrachev–Sachkov's control systems on an open set `Ω`, conditions
(10.2)–(10.4) of their §10.1 (authors' draft, p. 133) with `C¹` in place of `C^∞` (departure D3):
`(x, u) ↦ f x u` is continuous on `Ω × U`, `x ↦ f x u` is differentiable on `Ω` for `u ∈ U`, and
`(x, u) ↦ ∂ₓf(x, u)` is continuous on `Ω × U`. The same conditions are imposed on the integrand
`φ` of a cost (`F = ℝ`). -/
structure IsC1On (f : E → V → F) (Ω : Set E) (U : Set V) : Prop where
  continuousOn : ContinuousOn (fun p : E × V ↦ f p.1 p.2) (Ω ×ˢ U)
  differentiableAt : ∀ x ∈ Ω, ∀ u ∈ U, DifferentiableAt ℝ (f · u) x
  continuousOn_fderiv : ContinuousOn (fun p : E × V ↦ fderiv ℝ (f · p.2) p.1) (Ω ×ˢ U)

/-- A globally bounded `C¹` control system: `U` is compact, `f` is `C¹` on all of `E`
(`IsC1On f univ U`), `‖f x u‖ ≤ M` and `‖∂ₓf(x, u)‖ ≤ L` for all `x` and `u ∈ U`. This is what
the cut-off (`IsC1On.exists_cutoff`) produces near a trajectory. -/
structure IsBoundedC1System (f : E → V → F) (U : Set V) (M L : ℝ≥0) : Prop where
  isCompact : IsCompact U
  isC1On : IsC1On f univ U
  norm_le : ∀ x, ∀ u ∈ U, ‖f x u‖ ≤ M
  norm_fderiv_le : ∀ x, ∀ u ∈ U, ‖fderiv ℝ (f · u) x‖ ≤ L

/-- The standing hypotheses for well-posedness: `U` is compact, `f` is jointly continuous on
`E × U`, and `f(·, u)` is `L`-Lipschitz for every `u ∈ U`. (`f` then has linear growth on
`E × U`; the linear systems `Y' = A(t) Y` of
`OptimalControl/ODE/LinearCaratheodory.lean` are of this kind.) -/
structure IsLipschitzSystem (f : E → V → E) (U : Set V) (L : ℝ≥0) : Prop where
  isCompact : IsCompact U
  continuousOn : ContinuousOn (fun p : E × V ↦ f p.1 p.2) (univ ×ˢ U)
  lipschitzWith : ∀ u ∈ U, LipschitzWith L (f · u)

/-- A control on `[a, b]`: a.e. strongly measurable on `[a, b]`, with values in `U` there. -/
structure IsControlOn (u : ℝ → V) (U : Set V) (a b : ℝ) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable u (volume.restrict (Icc a b))
  mem : ∀ t ∈ Icc a b, u t ∈ U

set_option linter.unusedSectionVars false in
/-- A bounded `C¹` system satisfies the standing hypotheses, with the bound `L` on `∂ₓf` as
Lipschitz constant (mean value inequality). -/
theorem IsBoundedC1System.isLipschitzSystem {f : E → V → E} {U : Set V} {M L : ℝ≥0}
    (hf : IsBoundedC1System f U M L) : IsLipschitzSystem f U L where
  isCompact := hf.isCompact
  continuousOn := hf.isC1On.continuousOn
  lipschitzWith u hu := lipschitzWith_of_nnnorm_fderiv_le
    (fun x ↦ hf.isC1On.differentiableAt x (mem_univ x) u hu)
    (fun x ↦ by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hf.norm_fderiv_le x u hu)

/-- A function continuous on `Ω × U` (`Ω` open) that vanishes at the points `p` with `p.1`
outside a closed set `T ⊆ Ω` is continuous on `E × U`. -/
private lemma continuousOn_univ_prod_of_vanish {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [Zero Z] {Ω T : Set X} {U : Set Y}
    {G : X × Y → Z} (hΩ : IsOpen Ω) (hT : IsClosed T) (hTΩ : T ⊆ Ω)
    (hG : ContinuousOn G (Ω ×ˢ U)) (hG0 : ∀ p : X × Y, p.1 ∉ T → G p = 0) :
    ContinuousOn G (univ ×ˢ U) := by
  intro p hp
  by_cases h : p.1 ∈ Ω
  · refine (hG p ⟨h, hp.2⟩).mono_of_mem_nhdsWithin ?_
    refine mem_nhdsWithin.2 ⟨Ω ×ˢ univ, hΩ.prod isOpen_univ, ⟨h, trivial⟩, ?_⟩
    rintro q ⟨⟨hq1, -⟩, -, hq2⟩
    exact ⟨hq1, hq2⟩
  · have hpT : p.1 ∉ T := fun h' ↦ h (hTΩ h')
    have hev : G =ᶠ[𝓝 p] fun _ ↦ 0 := by
      have hopen : IsOpen (Tᶜ ×ˢ (univ : Set Y)) := hT.isOpen_compl.prod isOpen_univ
      filter_upwards [hopen.mem_nhds ⟨hpT, trivial⟩] with q hq
      exact hG0 q hq.1
    exact (continuousAt_const.congr hev.symm).continuousWithinAt

set_option linter.unusedSectionVars false in
/-- **Cut-off.** A `C¹` system on an open set `Ω` (`IsC1On`) with compact `U` agrees, on a
closed `δ`-neighbourhood of a compact `K ⊆ Ω`, with a globally bounded `C¹` system. This replaces
Agrachev–Sachkov's assumption of complete vector fields (§2.4.1; departure D11).

Proof: `g x u = χ(x) f(x, u)` with a smooth bump `χ` equal to `1` on `cthickening δ K` and
supported in `thickening (2δ) K`, where `cthickening (2δ) K ⊆ Ω`; the bounds come from the
compactness of `cthickening (2δ) K × U`. -/
theorem IsC1On.exists_cutoff {f : E → V → F} {Ω : Set E} {U : Set V} (hf : IsC1On f Ω U)
    (hΩ : IsOpen Ω) (hU : IsCompact U) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ δ > 0, cthickening δ K ⊆ Ω ∧ ∃ (g : E → V → F) (M L : ℝ≥0), IsBoundedC1System g U M L ∧
      ∀ x ∈ cthickening δ K, ∀ u ∈ U, g x u = f x u := by
  obtain ⟨δ₀, hδ₀, hδ₀Ω⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  set C := cthickening δ₀ K with hC_def
  have hCc : IsCompact C := hK.cthickening
  obtain ⟨χ, hχd, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1)
    (isOpen_thickening (δ := δ₀) (E := K)) (isClosed_cthickening (δ := δ₀ / 2) (E := K))
    (cthickening_subset_thickening' hδ₀ (half_lt_self hδ₀) K)
  have hχT : tsupport χ ⊆ C := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening _ _
  have hTΩ : tsupport χ ⊆ Ω := hχT.trans hδ₀Ω
  have hχc : Continuous χ := hχd.continuous
  have hχdiff : Differentiable ℝ χ := hχd.differentiable (by simp)
  have hχ'c : Continuous (fderiv ℝ χ) := hχd.continuous_fderiv (by simp)
  have hχ01 : ∀ x, χ x ∈ Icc (0 : ℝ) 1 := fun x ↦ hχr (mem_range_self x)
  have hχ0 : ∀ x, x ∉ tsupport χ → χ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hχ'0 : ∀ x, x ∉ tsupport χ → fderiv ℝ χ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_fderiv_subset ℝ h)
  set g : E → V → F := fun x u ↦ χ x • f x u with hg_def
  have hgev : ∀ x, x ∉ tsupport χ → ∀ u, (fun y ↦ g y u) =ᶠ[𝓝 x] fun _ ↦ 0 := by
    intro x hx u
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
    simp only [g, hy, Pi.zero_apply, zero_smul]
  have hgdiff : ∀ x, ∀ u ∈ U, DifferentiableAt ℝ (fun y ↦ g y u) x := by
    intro x u hu
    by_cases hx : x ∈ Ω
    · exact (hχdiff x).smul (hf.differentiableAt x hx u hu)
    · exact (differentiableAt_const (0 : F)).congr_of_eventuallyEq
        (hgev x (fun h ↦ hx (hTΩ h)) u)
  set D : E × V → E →L[ℝ] F :=
    fun p ↦ χ p.1 • fderiv ℝ (f · p.2) p.1 + (fderiv ℝ χ p.1).smulRight (f p.1 p.2) with hD_def
  have hD : ∀ x, ∀ u ∈ U, fderiv ℝ (fun y ↦ g y u) x = D (x, u) := by
    intro x u hu
    by_cases hx : x ∈ Ω
    · exact ((hχdiff x).hasFDerivAt.smul (hf.differentiableAt x hx u hu).hasFDerivAt).fderiv
    · have hxT : x ∉ tsupport χ := fun h ↦ hx (hTΩ h)
      rw [(hgev x hxT u).fderiv_eq]
      simp [D, hχ0 x hxT, hχ'0 x hxT]
  have hDc : ContinuousOn D (Ω ×ˢ U) := by
    refine ((hχc.comp continuous_fst).continuousOn.smul hf.continuousOn_fderiv).add ?_
    have h1 : Continuous fun p : E × V ↦ ContinuousLinearMap.smulRightL ℝ E F (fderiv ℝ χ p.1) :=
      (ContinuousLinearMap.smulRightL ℝ E F).continuous.comp (hχ'c.comp continuous_fst)
    simpa using h1.continuousOn.clm_apply hf.continuousOn
  have hgc : ContinuousOn (fun p : E × V ↦ g p.1 p.2) (Ω ×ˢ U) :=
    (hχc.comp continuous_fst).continuousOn.smul hf.continuousOn
  -- bounds on the compact set `C × U`
  have hCΩU : C ×ˢ U ⊆ Ω ×ˢ U := prod_mono hδ₀Ω subset_rfl
  obtain ⟨Mf, hMf⟩ := (hCc.prod hU).exists_bound_of_continuousOn (hf.continuousOn.mono hCΩU)
  obtain ⟨Lf, hLf⟩ :=
    (hCc.prod hU).exists_bound_of_continuousOn (hf.continuousOn_fderiv.mono hCΩU)
  obtain ⟨Dχ, hDχ⟩ := hCc.exists_bound_of_continuousOn hχ'c.continuousOn
  have hχle : ∀ x, ‖χ x‖ ≤ 1 := fun x ↦ by
    rw [Real.norm_of_nonneg (hχ01 x).1]; exact (hχ01 x).2
  refine ⟨δ₀ / 2, half_pos hδ₀, (cthickening_mono (half_le_self hδ₀.le) K).trans hδ₀Ω, g,
    Mf.toNNReal, (Lf + Dχ * Mf).toNNReal, ⟨hU, ⟨?_, fun x _ u hu ↦ hgdiff x u hu, ?_⟩, ?_, ?_⟩,
    ?_⟩
  · refine continuousOn_univ_prod_of_vanish hΩ (isClosed_tsupport χ) hTΩ hgc fun p hp ↦ ?_
    simp [g, hχ0 p.1 hp]
  · refine (continuousOn_univ_prod_of_vanish hΩ (isClosed_tsupport χ) hTΩ hDc
      fun p hp ↦ ?_).congr fun p hp ↦ hD p.1 p.2 hp.2
    simp [D, hχ0 p.1 hp, hχ'0 p.1 hp]
  · intro x u hu
    by_cases hx : x ∈ C
    · refine le_trans ?_ (Real.le_coe_toNNReal _)
      calc ‖g x u‖ = ‖χ x‖ * ‖f x u‖ := norm_smul _ _
        _ ≤ 1 * Mf := mul_le_mul (hχle x) (hMf (x, u) ⟨hx, hu⟩) (norm_nonneg _) zero_le_one
        _ = Mf := one_mul _
    · simp [g, hχ0 x fun h ↦ hx (hχT h)]
  · intro x u hu
    rw [hD x u hu]
    by_cases hx : x ∈ C
    · refine le_trans ?_ (Real.le_coe_toNNReal _)
      have hM0 : 0 ≤ Mf := (norm_nonneg _).trans (hMf (x, u) ⟨hx, hu⟩)
      have hD0 : 0 ≤ Dχ := (norm_nonneg _).trans (hDχ x hx)
      calc ‖D (x, u)‖ ≤ ‖χ x • fderiv ℝ (f · u) x‖ + ‖(fderiv ℝ χ x).smulRight (f x u)‖ :=
            norm_add_le _ _
        _ = ‖χ x‖ * ‖fderiv ℝ (f · u) x‖ + ‖fderiv ℝ χ x‖ * ‖f x u‖ := by
            rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
        _ ≤ 1 * Lf + Dχ * Mf := by
            gcongr
            · exact hχle x
            · exact hLf (x, u) ⟨hx, hu⟩
            · exact hDχ x hx
            · exact hMf (x, u) ⟨hx, hu⟩
        _ = Lf + Dχ * Mf := by rw [one_mul]
    · have hxT : x ∉ tsupport χ := fun h ↦ hx (hχT h)
      simp [D, hχ0 x hxT, hχ'0 x hxT]
  · intro x hx u _
    simp [g, (hχ1 x).1 hx]

/-! ### Gronwall's inequality in integral form -/

/-- **Gronwall's inequality** in integral form: if `φ ≥ 0` is continuous on `[a, b]` and
`φ(t) ≤ C + L ∫ₐᵗ φ` there, with `L ≥ 0`, then `φ(t) ≤ C e^{L (t - a)}`. -/
theorem le_mul_exp_of_le_add_integral {φ : ℝ → ℝ} {a b C L : ℝ} (hL : 0 ≤ L)
    (hφ : ContinuousOn φ (Icc a b)) (hφ0 : ∀ t ∈ Icc a b, 0 ≤ φ t)
    (h : ∀ t ∈ Icc a b, φ t ≤ C + L * ∫ r in a..t, φ r) :
    ∀ t ∈ Icc a b, φ t ≤ C * Real.exp (L * (t - a)) := by
  intro t ht
  have hab : a ≤ b := ht.1.trans ht.2
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  set φ' : ℝ → ℝ := fun r ↦ φ (projIcc a b hab r) with hφ'_def
  have hφ'c : Continuous φ' :=
    hφ.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun r ↦ (projIcc a b hab r).2
  have hφ'eq : ∀ r ∈ Icc a b, φ' r = φ r := fun r hr ↦ by simp [φ', projIcc_of_mem hab hr]
  have hint : ∀ r ∈ Icc a b, ∫ q in a..r, φ' q = ∫ q in a..r, φ q := fun r hr ↦
    intervalIntegral.integral_congr fun q hq ↦ hφ'eq q (uIcc_subset_Icc ha hr hq)
  set Ψ : ℝ → ℝ := fun r ↦ C + L * ∫ q in a..r, φ' q with hΨ_def
  have hΨ : ∀ r, HasDerivAt Ψ (L * φ' r) r := fun r ↦
    ((hφ'c.integral_hasStrictDerivAt a r).hasDerivAt.const_mul L).const_add C
  have hC : 0 ≤ C := by
    have := h a ha
    simp only [intervalIntegral.integral_same, mul_zero, add_zero] at this
    exact (hφ0 a ha).trans this
  have hφΨ : ∀ r ∈ Icc a b, φ r ≤ Ψ r := fun r hr ↦ by
    simp only [Ψ, hint r hr]
    exact h r hr
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := Ψ) (f' := fun r ↦ L * φ' r)
    (δ := C) (K := L) (ε := 0) (a := a) (b := b)
    (continuous_iff_continuousAt.2 fun r ↦ (hΨ r).continuousAt).continuousOn
    (fun r _ ↦ (hΨ r).hasDerivWithinAt) (by simp [Ψ, abs_of_nonneg hC])
    (fun r hr ↦ by
      have hr' : r ∈ Icc a b := Ico_subset_Icc_self hr
      rw [hφ'eq r hr', add_zero, norm_mul, Real.norm_of_nonneg hL,
        Real.norm_of_nonneg (hφ0 r hr')]
      exact mul_le_mul_of_nonneg_left ((hφΨ r hr').trans (Real.le_norm_self _)) hL) t ht
  rw [gronwallBound_ε0] at key
  exact (hφΨ t ht).trans ((Real.le_norm_self _).trans key)

/-- Gronwall's inequality forward and backward from `s ∈ [c, d]`: if `φ ≥ 0` is continuous on
`[c, d]` and `φ(t) ≤ C + L |∫ₛᵗ φ|` there, then `φ(t) ≤ C e^{L|t - s|}`. -/
private lemma le_mul_exp_abs_of_le_add_abs_integral {φ : ℝ → ℝ} {c d s C L : ℝ} (hL : 0 ≤ L)
    (hs : s ∈ Icc c d) (hφ : ContinuousOn φ (Icc c d)) (hφ0 : ∀ t ∈ Icc c d, 0 ≤ φ t)
    (h : ∀ t ∈ Icc c d, φ t ≤ C + L * |∫ r in s..t, φ r|) :
    ∀ t ∈ Icc c d, φ t ≤ C * Real.exp (L * |t - s|) := by
  intro t ht
  rcases le_total s t with hst | hts
  · have hsub : Icc s d ⊆ Icc c d := Icc_subset_Icc_left hs.1
    have := le_mul_exp_of_le_add_integral (a := s) (b := d) hL (hφ.mono hsub)
      (fun r hr ↦ hφ0 r (hsub hr)) (fun r hr ↦ by
        have hnn : 0 ≤ ∫ q in s..r, φ q := intervalIntegral.integral_nonneg hr.1
          fun q hq ↦ hφ0 q ⟨hs.1.trans hq.1, hq.2.trans hr.2⟩
        simpa [abs_of_nonneg hnn] using h r (hsub hr)) t ⟨hst, ht.2⟩
    rwa [abs_of_nonneg (sub_nonneg.2 hst)]
  · have hmem : ∀ r ∈ Icc (-s) (-c), -r ∈ Icc c d := fun r hr ↦
      ⟨by linarith [hr.2], by linarith [hr.1, hs.2]⟩
    have := le_mul_exp_of_le_add_integral (φ := fun r ↦ φ (-r)) (a := -s) (b := -c) hL
      (hφ.comp continuous_neg.continuousOn hmem) (fun r hr ↦ hφ0 _ (hmem r hr))
      (fun r hr ↦ by
        have h1 := h (-r) (hmem r hr)
        have hnn : 0 ≤ ∫ q in -r..s, φ q := intervalIntegral.integral_nonneg
          (by linarith [hr.1]) fun q hq ↦ hφ0 q ⟨(hmem r hr).1.trans hq.1, hq.2.trans hs.2⟩
        rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg hnn] at h1
        rw [intervalIntegral.integral_comp_neg, neg_neg]
        exact h1) (-t) ⟨neg_le_neg hts, neg_le_neg ht.1⟩
    rw [abs_of_nonpos (sub_nonpos.2 hts)]
    simp only [neg_neg] at this
    convert this using 3
    ring

/-! ### Solutions and flows -/

/-- `y` is a Carathéodory solution of `y' = f(y, u(t))` on the interval `[[a, b]]` with value
`x` at time `s`: `y` is continuous on `[[a, b]]`, `t ↦ f(y(t), u(t))` is integrable there, and
`y(t) = x + ∫ₛᵗ f(y(r), u(r)) dr` for `t ∈ [[a, b]]` (meaningful for `s ∈ [[a, b]]`). -/
def IsSolution (f : E → V → E) (u : ℝ → V) (s : ℝ) (x : E) (a b : ℝ) (y : ℝ → E) : Prop :=
  ContinuousOn y [[a, b]] ∧ IntervalIntegrable (fun r ↦ f (y r) (u r)) volume a b ∧
    ∀ t ∈ [[a, b]], y t = x + ∫ r in s..t, f (y r) (u r)

open Classical in
/-- The flow `P_{s → t}(x)` of `y' = f(y, u(t))`: the value at time `t` of the solution with value
`x` at time `s`, chosen among the solutions on `[[s, t]]` (unique under the standing hypotheses,
`IsSolution.eqOn`); `x` if there is none. Agrachev–Sachkov write it with the chronological
exponential, `P_{s,t} = exp→ ∫ₛᵗ f_{u(r)} dr` (authors' draft, §2.4). -/
noncomputable def flow (f : E → V → E) (u : ℝ → V) (s t : ℝ) (x : E) : E :=
  if h : ∃ y, IsSolution f u s x s t y then h.choose t else x

variable {f : E → V → E} {U : Set V} {L : ℝ≥0} {u w : ℝ → V} {a b : ℝ}

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The flow at the initial time is the identity. -/
theorem flow_self (f : E → V → E) (u : ℝ → V) (s : ℝ) (x : E) : flow f u s s x = x := by
  unfold flow
  split_ifs with h
  · simpa using h.choose_spec.2.2 s (by simp)
  · rfl

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private lemma isControlOn_mono {c d : ℝ} (hu : IsControlOn u U a b) (h : Icc c d ⊆ Icc a b) :
    IsControlOn u U c d :=
  ⟨hu.1.mono_set h, fun t ht ↦ hu.2 t (h ht)⟩

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private lemma isSolution_mono {s : ℝ} {x : E} {y : ℝ → E} {c d : ℝ}
    (hy : IsSolution f u s x a b y) (h : [[c, d]] ⊆ [[a, b]]) : IsSolution f u s x c d y :=
  ⟨hy.1.mono h, hy.2.1.mono_set h, fun t ht ↦ hy.2.2 t (h ht)⟩

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
private lemma isSolution_congr {s : ℝ} {x : E} {y y' : ℝ → E} (hy : IsSolution f u s x a b y)
    (h : EqOn y' y [[a, b]]) (hs : s ∈ [[a, b]]) : IsSolution f u s x a b y' := by
  refine ⟨hy.1.congr h, hy.2.1.congr fun r hr ↦ ?_, fun t ht ↦ ?_⟩
  · simp only [h (uIoc_subset_uIcc hr)]
  · rw [h ht, hy.2.2 t ht]
    congr 1
    refine intervalIntegral.integral_congr fun r hr ↦ ?_
    simp only [h (uIcc_subset_uIcc hs ht hr)]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Along a continuous curve, `t ↦ f(y(t), u(t))` is integrable on `[a, b]`: it is bounded, and
measurable by composing a continuous (Tietze) extension of `f` off `E × U` with `(y, u)`. -/
private lemma intervalIntegrable_comp_control (hf : IsLipschitzSystem f U L)
    (hu : IsControlOn u U a b) (hab : a ≤ b) {y : ℝ → E} (hy : ContinuousOn y (Icc a b)) :
    IntervalIntegrable (fun r ↦ f (y r) (u r)) volume a b := by
  have hcl : IsClosed ((univ : Set E) ×ˢ U) := isClosed_univ.prod hf.isCompact.isClosed
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq (Y := E) hcl
    ⟨((univ : Set E) ×ˢ U).domRestrict (fun p : E × V ↦ f p.1 p.2), hf.continuousOn.domRestrict⟩
  have hGf : ∀ p ∈ (univ : Set E) ×ˢ U, G p = f p.1 p.2 := fun p hp ↦ by
    have := congrArg (fun k : C((univ : Set E) ×ˢ U, E) ↦ k ⟨p, hp⟩) hG
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk, Set.domRestrict_apply] at this
    exact this
  have hK : IsCompact ((y '' Icc a b) ×ˢ U) :=
    (isCompact_Icc.image_of_continuousOn hy).prod hf.isCompact
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (hf.continuousOn.mono (prod_mono (subset_univ _) subset_rfl))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  refine Integrable.of_bound ?_ B ?_
  · refine (G.continuous.comp_aestronglyMeasurable
      ((hy.aestronglyMeasurable measurableSet_Icc).prodMk hu.aestronglyMeasurable)).congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr ↦ ?_)
    exact hGf _ ⟨mem_univ _, hu.mem r hr⟩
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr ↦ ?_)
    exact hB (y r, u r) ⟨mem_image_of_mem _ hr, hu.mem r hr⟩

/-- `|∫ₛᵗ e^{λ|r - s|} dr| ≤ e^{λ|t - s|} / λ` for `λ > 0`, when `s ≤ t`. -/
private lemma abs_integral_exp_abs_le_of_le {lam : ℝ} (hlam : 0 < lam) {s t : ℝ} (hst : s ≤ t) :
    |∫ r in s..t, Real.exp (lam * |r - s|)| ≤ Real.exp (lam * |t - s|) / lam := by
  have h1 : ∫ r in s..t, Real.exp (lam * |r - s|) = ∫ r in s..t, Real.exp (lam * r - lam * s) := by
    refine intervalIntegral.integral_congr fun r hr ↦ ?_
    rw [uIcc_of_le hst] at hr
    simp only [abs_of_nonneg (sub_nonneg.2 hr.1), mul_sub]
  rw [h1, intervalIntegral.integral_comp_mul_sub (fun r ↦ Real.exp r) hlam.ne', integral_exp,
    sub_self, Real.exp_zero, smul_eq_mul, abs_of_nonneg (sub_nonneg.2 hst), mul_sub lam t s]
  have hpos : 1 ≤ Real.exp (lam * t - lam * s) := Real.one_le_exp (by nlinarith)
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 hlam.le) (by linarith)), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hlam.le)

/-- `|∫ₛᵗ e^{λ|r - s|} dr| ≤ e^{λ|t - s|} / λ` for `λ > 0`. -/
private lemma abs_integral_exp_abs_le {lam : ℝ} (hlam : 0 < lam) (s t : ℝ) :
    |∫ r in s..t, Real.exp (lam * |r - s|)| ≤ Real.exp (lam * |t - s|) / lam := by
  rcases le_total s t with hst | hts
  · exact abs_integral_exp_abs_le_of_le hlam hst
  · have h := abs_integral_exp_abs_le_of_le hlam (neg_le_neg hts)
    have e : ∫ r in s..t, Real.exp (lam * |r - s|) =
        -∫ r in -s..-t, Real.exp (lam * |r - -s|) := by
      rw [← intervalIntegral.integral_symm, ← intervalIntegral.integral_comp_neg]
      refine intervalIntegral.integral_congr fun r _ ↦ ?_
      rw [show -r - -s = -(r - s) by ring, abs_neg]
    rw [e, abs_neg]
    rwa [show -t - -s = -(t - s) by ring, abs_neg] at h

set_option linter.unusedSectionVars false in
/-- **Carathéodory's theorem**, existence: under the standing hypotheses, for a control on
`[a, b]` and `s ∈ [a, b]`, there is a solution on `[a, b]` through `(s, x)`.

Proof: with `ρ(t) = e^{λ|t - s|}`, `λ = 2L + 1`, the map
`z ↦ ρ⁻¹ (x + ∫ₛ f(ρ z, u))` is a contraction with constant `1/2` on `C([a, b], E)`; `y = ρ z`
for its fixed point `z`. -/
theorem exists_isSolution (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) {s : ℝ}
    (hs : s ∈ Icc a b) (x : E) : ∃ y, IsSolution f u s x a b y := by
  have hab : a ≤ b := hs.1.trans hs.2
  set lam : ℝ := 2 * L + 1 with hlam_def
  have hlam : 0 < lam := by positivity
  set ρ : ℝ → ℝ := fun r ↦ Real.exp (lam * |r - s|) with hρ_def
  have hρc : Continuous ρ := by fun_prop
  have hρ0 : ∀ r, 0 < ρ r := fun r ↦ Real.exp_pos _
  set ext : C(Icc a b, E) → ℝ → E := fun z r ↦ ρ r • IccExtend hab z r with hext_def
  have hext : ∀ z, Continuous (ext z) := fun z ↦ hρc.smul z.continuous.Icc_extend'
  have hint : ∀ z, IntervalIntegrable (fun r ↦ f (ext z r) (u r)) volume a b := fun z ↦
    intervalIntegrable_comp_control hf hu hab (hext z).continuousOn
  have hsab : s ∈ [[a, b]] := by rwa [uIcc_of_le hab]
  have hprim : ∀ z, ContinuousOn (fun t ↦ ∫ r in s..t, f (ext z r) (u r)) (Icc a b) := fun z ↦ by
    simpa [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval' (hint z) hsab
  let Q : C(Icc a b, E) → C(Icc a b, E) := fun z ↦
    ⟨fun t ↦ (ρ t)⁻¹ • (x + ∫ r in s..t, f (ext z r) (u r)),
      ((hρc.comp continuous_subtype_val).inv₀ fun t : Icc a b ↦ (hρ0 t.1).ne').smul
        (continuous_const.add (hprim z).domRestrict)⟩
  have hQ : ContractingWith (1 / 2 : ℝ≥0) Q := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun z z' ↦ ?_⟩
    rw [ContinuousMap.dist_le (by positivity)]
    intro t
    have ht : (t : ℝ) ∈ Icc a b := t.2
    have hst : [[s, (t : ℝ)]] ⊆ [[a, b]] := by
      rw [uIcc_of_le hab]; exact uIcc_subset_Icc hs ht
    set d := dist z z'
    have hpt : ∀ r ∈ Ι s (t : ℝ),
        ‖f (ext z r) (u r) - f (ext z' r) (u r)‖ ≤ L * d * ρ r := by
      intro r hr
      have hr' : r ∈ Icc a b := by
        rw [← uIcc_of_le hab]; exact hst (uIoc_subset_uIcc hr)
      calc ‖f (ext z r) (u r) - f (ext z' r) (u r)‖ ≤ L * ‖ext z r - ext z' r‖ :=
            (hf.lipschitzWith (u r) (hu.mem r hr')).norm_sub_le _ _
        _ = L * (ρ r * ‖IccExtend hab z r - IccExtend hab z' r‖) := by
            simp only [ext, ← smul_sub, norm_smul, Real.norm_of_nonneg (hρ0 r).le]
        _ ≤ L * (ρ r * d) := by
            gcongr
            rw [← dist_eq_norm]
            exact ContinuousMap.dist_apply_le_dist _
        _ = L * d * ρ r := by ring
    have hbound : ‖∫ r in s..(t : ℝ), (f (ext z r) (u r) - f (ext z' r) (u r))‖ ≤
        L * d * (ρ t / lam) := by
      refine (intervalIntegral.norm_integral_le_abs_of_norm_le
        ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall hpt))
        ((hρc.const_mul _).intervalIntegrable _ _)).trans ?_
      rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (abs_integral_exp_abs_le hlam s t) (by positivity)
    simp only [Q, ContinuousMap.coe_mk, dist_eq_norm]
    rw [← smul_sub, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
      ((hint z).mono_set hst) ((hint z').mono_set hst), norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 (hρ0 t).le)]
    calc (ρ t)⁻¹ * ‖∫ r in s..(t : ℝ), (f (ext z r) (u r) - f (ext z' r) (u r))‖
        ≤ (ρ t)⁻¹ * (L * d * (ρ t / lam)) :=
          mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 (hρ0 t).le)
      _ = L / lam * d := by field_simp [(hρ0 t).ne', hlam.ne']
      _ ≤ ((1 / 2 : ℝ≥0) : ℝ) * d := by
          gcongr
          rw [div_le_iff₀ hlam]; push_cast; linarith
  have : Nonempty C(Icc a b, E) := ⟨0⟩
  set z := ContractingWith.fixedPoint Q hQ
  have hz : Q z = z := hQ.fixedPoint_isFixedPt
  refine ⟨ext z, (hext z).continuousOn, hint z, fun t ht ↦ ?_⟩
  rw [uIcc_of_le hab] at ht
  have h1 : ext z t = ρ t • z ⟨t, ht⟩ := by simp [ext, IccExtend_of_mem hab z ht]
  have h2 : z ⟨t, ht⟩ = (ρ t)⁻¹ • (x + ∫ r in s..t, f (ext z r) (u r)) := by
    conv_lhs => rw [← hz]
    rfl
  rw [h1, h2, smul_inv_smul₀ (hρ0 t).ne']

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The comparison estimate behind uniqueness and the Lipschitz estimates: a solution `y` for
the control `u` through `(s, x)` and a solution `z` for the control `w` through `(s, x')`
satisfy `‖y(t) - z(t)‖ ≤ e^{L|t - s|} (‖x - x'‖ + |∫ₛᵗ ‖f(z, u) - f(z, w)‖|)` (Gronwall on the
interval between `s` and `t`). -/
private lemma norm_sub_le_of_isSolution (hf : IsLipschitzSystem f U L)
    (hu : IsControlOn u U a b) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {x x' : E} {y z : ℝ → E} (hy : IsSolution f u s x a b y)
    (hz : IsSolution f w s x' a b z) :
    ‖y t - z t‖ ≤ Real.exp (L * |t - s|) *
      (‖x - x'‖ + |∫ r in s..t, ‖f (z r) (u r) - f (z r) (w r)‖|) := by
  have hab : a ≤ b := hs.1.trans hs.2
  obtain ⟨hyc, hyi, hye⟩ := hy
  obtain ⟨hzc, hzi, hze⟩ := hz
  rw [uIcc_of_le hab] at hyc hye hzc hze
  have hzu : IntervalIntegrable (fun r ↦ f (z r) (u r)) volume a b :=
    intervalIntegrable_comp_control hf hu hab hzc
  set g : ℝ → ℝ := fun r ↦ ‖f (z r) (u r) - f (z r) (w r)‖ with hg_def
  have hsub : [[s, t]] ⊆ Icc a b := uIcc_subset_Icc hs ht
  have hgi : IntervalIntegrable g volume s t :=
    ((hzu.sub hzi).norm).mono_set (by rw [uIcc_of_le hab]; exact hsub)
  set φ : ℝ → ℝ := fun r ↦ ‖y r - z r‖ with hφ_def
  have hφc : ContinuousOn φ (Icc a b) := (hyc.sub hzc).norm
  have key := le_mul_exp_abs_of_le_add_abs_integral (c := s ⊓ t) (d := s ⊔ t) (s := s)
    (C := ‖x - x'‖ + |∫ r in s..t, g r|) L.2 left_mem_uIcc (hφc.mono hsub)
    (fun _ _ ↦ norm_nonneg _) ?_ t right_mem_uIcc
  · simpa [mul_comm] using key
  intro τ hτ
  replace hτ : τ ∈ [[s, t]] := hτ
  have hτ' : τ ∈ Icc a b := hsub hτ
  have hsτ : [[s, τ]] ⊆ [[a, b]] := by rw [uIcc_of_le hab]; exact uIcc_subset_Icc hs hτ'
  have hyi' := hyi.mono_set hsτ
  have hzi' := hzi.mono_set hsτ
  have hzu' := hzu.mono_set hsτ
  have e : y τ - z τ = (x - x') + (∫ r in s..τ, (f (y r) (u r) - f (z r) (u r))) +
      ∫ r in s..τ, (f (z r) (u r) - f (z r) (w r)) := by
    rw [hye τ hτ', hze τ hτ', intervalIntegral.integral_sub hyi' hzu',
      intervalIntegral.integral_sub hzu' hzi']
    abel
  have h1 : ‖∫ r in s..τ, (f (y r) (u r) - f (z r) (u r))‖ ≤ L * |∫ r in s..τ, φ r| := by
    refine (intervalIntegral.norm_integral_le_abs_of_norm_le (g := fun r ↦ L * φ r)
      ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun r hr ↦ ?_))
      ((hφc.mono (by rw [← uIcc_of_le hab]; exact hsτ)).intervalIntegrable.const_mul _)).trans ?_
    · have hr' : r ∈ Icc a b := by
        rw [← uIcc_of_le hab]; exact hsτ (uIoc_subset_uIcc hr)
      exact (hf.lipschitzWith (u r) (hu.mem r hr')).norm_sub_le _ _
    · rw [intervalIntegral.integral_const_mul, abs_mul, NNReal.abs_eq]
  have h2 : ‖∫ r in s..τ, (f (z r) (u r) - f (z r) (w r))‖ ≤ |∫ r in s..t, g r| := by
    refine intervalIntegral.norm_integral_le_abs_integral_norm.trans ?_
    rcases le_total s t with hst | hts
    · rw [uIcc_of_le hst] at hτ
      rw [abs_of_nonneg (intervalIntegral.integral_nonneg hτ.1 fun _ _ ↦ norm_nonneg _),
        abs_of_nonneg (intervalIntegral.integral_nonneg hst fun _ _ ↦ norm_nonneg _)]
      exact intervalIntegral.integral_mono_interval le_rfl hτ.1 hτ.2
        (Eventually.of_forall fun _ ↦ norm_nonneg _) hgi
    · rw [uIcc_of_ge hts] at hτ
      rw [intervalIntegral.integral_symm, abs_neg, intervalIntegral.integral_symm t s, abs_neg,
        abs_of_nonneg (intervalIntegral.integral_nonneg hτ.2 fun _ _ ↦ norm_nonneg _),
        abs_of_nonneg (intervalIntegral.integral_nonneg hts fun _ _ ↦ norm_nonneg _)]
      exact intervalIntegral.integral_mono_interval hτ.1 hτ.2 le_rfl
        (Eventually.of_forall fun _ ↦ norm_nonneg _) hgi.symm
  calc φ τ = ‖(x - x') + (∫ r in s..τ, (f (y r) (u r) - f (z r) (u r))) +
        ∫ r in s..τ, (f (z r) (u r) - f (z r) (w r))‖ := by
          change ‖y τ - z τ‖ = _
          rw [e]
    _ ≤ ‖x - x'‖ + ‖∫ r in s..τ, (f (y r) (u r) - f (z r) (u r))‖ +
        ‖∫ r in s..τ, (f (z r) (u r) - f (z r) (w r))‖ := norm_add₃_le
    _ ≤ ‖x - x'‖ + L * |∫ r in s..τ, φ r| + |∫ r in s..t, g r| := by gcongr
    _ = ‖x - x'‖ + |∫ r in s..t, g r| + L * |∫ r in s..τ, φ r| := by ring

set_option linter.unusedSectionVars false in
/-- **Carathéodory's theorem**, uniqueness: two solutions on `[a, b]` through the same point
`(s, x)` agree on `[a, b]` (Gronwall). -/
theorem IsSolution.eqOn (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) {s : ℝ}
    (hs : s ∈ Icc a b) {x : E} {y y' : ℝ → E} (hy : IsSolution f u s x a b y)
    (hy' : IsSolution f u s x a b y') : EqOn y y' (Icc a b) := fun t ht ↦ by
  have := norm_sub_le_of_isSolution hf hu hs ht hy hy'
  simpa [sub_eq_zero] using this

/-- A solution on `[a, b]` through `(s, x)` is the flow from `(s, x)`. -/
theorem IsSolution.flow_eq (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) {s : ℝ}
    (hs : s ∈ Icc a b) {x : E} {y : ℝ → E} (hy : IsSolution f u s x a b y) {t : ℝ}
    (ht : t ∈ Icc a b) : flow f u s t x = y t := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hst : [[s, t]] ⊆ [[a, b]] := by rw [uIcc_of_le hab]; exact uIcc_subset_Icc hs ht
  have hex : ∃ y', IsSolution f u s x s t y' := ⟨y, isSolution_mono hy hst⟩
  rw [flow, dite_eq_left hex]
  have hI : [[s ⊓ t, s ⊔ t]] ⊆ [[s, t]] := by rw [uIcc_of_le inf_le_sup]; exact subset_rfl
  exact IsSolution.eqOn (a := s ⊓ t) (b := s ⊔ t) hf
    (isControlOn_mono hu (uIcc_subset_Icc hs ht)) left_mem_uIcc
    (isSolution_mono hex.choose_spec hI) (isSolution_mono hy (hI.trans hst)) right_mem_uIcc

/-- The flow from `(s, x)` is a solution on `[a, b]`. -/
theorem isSolution_flow (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) {s : ℝ}
    (hs : s ∈ Icc a b) (x : E) : IsSolution f u s x a b (fun t ↦ flow f u s t x) := by
  have hab : a ≤ b := hs.1.trans hs.2
  obtain ⟨y, hy⟩ := exists_isSolution hf hu hs x
  refine isSolution_congr hy (fun t ht ↦ ?_) (by rwa [uIcc_of_le hab])
  rw [uIcc_of_le hab] at ht
  exact hy.flow_eq hf hu hs ht

/-- The cocycle property `P_{t → r} ∘ P_{s → t} = P_{s → r}`. -/
theorem flow_flow (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) {s t r : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hr : r ∈ Icc a b) (x : E) :
    flow f u t r (flow f u s t x) = flow f u s r x := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hY := isSolution_flow hf hu hs x
  have htab : t ∈ [[a, b]] := by rwa [uIcc_of_le hab]
  have hsab : s ∈ [[a, b]] := by rwa [uIcc_of_le hab]
  have hY' : IsSolution f u t (flow f u s t x) a b (fun τ ↦ flow f u s τ x) := by
    refine ⟨hY.1, hY.2.1, fun τ hτ ↦ ?_⟩
    change flow f u s τ x = flow f u s t x + ∫ q in t..τ, f (flow f u s q x) (u q)
    have e1 : flow f u s τ x = x + ∫ q in s..τ, f (flow f u s q x) (u q) := hY.2.2 τ hτ
    have e2 : flow f u s t x = x + ∫ q in s..t, f (flow f u s q x) (u q) := hY.2.2 t htab
    rw [e1, e2, add_assoc, intervalIntegral.integral_add_adjacent_intervals
      (hY.2.1.mono_set (uIcc_subset_uIcc hsab htab)) (hY.2.1.mono_set (uIcc_subset_uIcc htab hτ))]
  exact hY'.flow_eq hf hu ht hr

/-- Lipschitz dependence on the initial point: `‖P_{s → t}(x) - P_{s → t}(x')‖ ≤
e^{L|t - s|} ‖x - x'‖` (Gronwall). -/
theorem norm_flow_sub_flow_le (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x x' : E) :
    ‖flow f u s t x - flow f u s t x'‖ ≤ Real.exp (L * |t - s|) * ‖x - x'‖ := by
  have := norm_sub_le_of_isSolution hf hu hs ht (isSolution_flow hf hu hs x)
    (isSolution_flow hf hu hs x')
  simpa using this

/-- Lipschitz dependence on the time, for a bounded system: `‖P_{s → t}(x) - P_{s → t'}(x)‖ ≤
M |t - t'|`. -/
theorem norm_flow_sub_flow_time_le (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b)
    {M : ℝ} (hM : ∀ y, ∀ v ∈ U, ‖f y v‖ ≤ M) {s t t' : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (ht' : t' ∈ Icc a b) (x : E) :
    ‖flow f u s t x - flow f u s t' x‖ ≤ M * |t - t'| := by
  have hab : a ≤ b := hs.1.trans hs.2
  have hY := isSolution_flow hf hu hs x
  have hsab : s ∈ [[a, b]] := by rwa [uIcc_of_le hab]
  have htab : t ∈ [[a, b]] := by rwa [uIcc_of_le hab]
  have ht'ab : t' ∈ [[a, b]] := by rwa [uIcc_of_le hab]
  have e1 : flow f u s t x = x + ∫ q in s..t, f (flow f u s q x) (u q) := hY.2.2 t htab
  have e2 : flow f u s t' x = x + ∫ q in s..t', f (flow f u s q x) (u q) := hY.2.2 t' ht'ab
  rw [e1, e2, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
    (hY.2.1.mono_set (uIcc_subset_uIcc hsab htab)) (hY.2.1.mono_set (uIcc_subset_uIcc hsab ht'ab))]
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun r hr ↦
    hM _ _ (hu.mem r (uIcc_subset_Icc ht' ht (uIoc_subset_uIcc hr)))

/-- The flow is jointly continuous in the initial time, the final time and the initial point. -/
theorem continuousOn_flow (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b) :
    ContinuousOn (fun p : ℝ × ℝ × E ↦ flow f u p.1 p.2.1 p.2.2) (Icc a b ×ˢ Icc a b ×ˢ univ) := by
  rintro ⟨s₀, t₀, x₀⟩ ⟨hs₀, ht₀, -⟩
  have hab : a ≤ b := hs₀.1.trans hs₀.2
  set Y₀ : ℝ → E := fun τ ↦ flow f u s₀ τ x₀ with hY₀_def
  have hY₀ : ContinuousOn Y₀ (Icc a b) := by
    simpa [uIcc_of_le hab] using (isSolution_flow hf hu hs₀ x₀).1
  set S : Set (ℝ × ℝ × E) := Icc a b ×ˢ Icc a b ×ˢ univ with hS_def
  set G : ℝ × ℝ × E → ℝ := fun p ↦
    Real.exp (L * |p.2.1 - p.1|) * ‖p.2.2 - Y₀ p.1‖ + ‖Y₀ p.2.1 - Y₀ t₀‖ with hG_def
  have hbound : ∀ p ∈ S, ‖flow f u p.1 p.2.1 p.2.2 - flow f u s₀ t₀ x₀‖ ≤ G p := by
    rintro ⟨s, t, x⟩ ⟨hs, ht, -⟩
    have h1 : flow f u s t (Y₀ s) = Y₀ t := flow_flow hf hu hs₀ hs ht x₀
    calc ‖flow f u s t x - flow f u s₀ t₀ x₀‖ =
          ‖(flow f u s t x - flow f u s t (Y₀ s)) + (Y₀ t - Y₀ t₀)‖ := by
          rw [h1, sub_add_sub_cancel]
      _ ≤ ‖flow f u s t x - flow f u s t (Y₀ s)‖ + ‖Y₀ t - Y₀ t₀‖ := norm_add_le _ _
      _ ≤ G (s, t, x) :=
          add_le_add_left (norm_flow_sub_flow_le hf hu hs ht x (Y₀ s)) _
  have hc1 : ContinuousWithinAt (Y₀ ∘ Prod.fst) S (s₀, t₀, x₀) :=
    (hY₀ s₀ hs₀).comp continuousWithinAt_fst fun p (hp : p ∈ S) ↦ hp.1
  have hc2 : ContinuousWithinAt (Y₀ ∘ (Prod.fst ∘ Prod.snd)) S (s₀, t₀, x₀) :=
    (hY₀ t₀ ht₀).comp (continuous_fst.comp continuous_snd).continuousWithinAt
      fun p (hp : p ∈ S) ↦ hp.2.1
  have hGc : ContinuousWithinAt G S (s₀, t₀, x₀) := by
    have hexp : Continuous fun p : ℝ × ℝ × E ↦ Real.exp (L * |p.2.1 - p.1|) := by fun_prop
    exact (hexp.continuousWithinAt.mul
      ((continuous_snd.comp continuous_snd).continuousWithinAt.sub hc1).norm).add
      (hc2.sub continuousWithinAt_const).norm
  have hG0 : G (s₀, t₀, x₀) = 0 := by simp [G, Y₀, flow_self]
  have hGt : Tendsto G (𝓝[S] (s₀, t₀, x₀)) (𝓝 0) := by
    simpa [ContinuousWithinAt, hG0] using hGc
  change Tendsto _ (𝓝[S] (s₀, t₀, x₀)) (𝓝 (flow f u s₀ t₀ x₀))
  exact tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall
    fun _ ↦ norm_nonneg _) (eventually_nhdsWithin_of_forall hbound) hGt)

/-- Comparison of the trajectories of two controls (Gronwall): with `y = P^w_{s → ·}(x')`,
`‖P^u_{s → t}(x) - P^w_{s → t}(x')‖ ≤
e^{L|t - s|} (‖x - x'‖ + |∫ₛᵗ ‖f(y(r), u(r)) - f(y(r), w(r))‖ dr|)`. For needle variations the
integral is at most `2M` times the measure of `{u ≠ w}`. -/
theorem norm_flow_sub_flow_control_le (hf : IsLipschitzSystem f U L) (hu : IsControlOn u U a b)
    (hw : IsControlOn w U a b) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x x' : E) :
    ‖flow f u s t x - flow f w s t x'‖ ≤ Real.exp (L * |t - s|) *
      (‖x - x'‖ + |∫ r in s..t, ‖f (flow f w s r x') (u r) - f (flow f w s r x') (w r)‖|) :=
  norm_sub_le_of_isSolution hf hu hs ht (isSolution_flow hf hu hs x)
    (isSolution_flow hf hw hs x')

/-! ### Flows and admissible pairs -/

variable [MeasurableSpace V] [BorelSpace V]

/-- The trajectory of an admissible pair (`ControlSystem.IsAdmissible`, from `x₀` at time `0`)
is the flow from `(0, x₀)`. -/
theorem IsAdmissible.eq_flow (hf : IsLipschitzSystem f U L) {x₀ : E} {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ → E} (h : IsAdmissible f U x₀ T u x) : ∀ t ∈ Icc 0 T, x t = flow f u 0 t x₀ := by
  intro t ht
  have hu : IsControlOn u U 0 T := ⟨h.1.aestronglyMeasurable, h.2.1⟩
  have hsol : IsSolution f u 0 x₀ 0 T x := by
    refine ⟨by rw [uIcc_of_le hT]; exact h.2.2.1, h.2.2.2.1, fun τ hτ ↦ ?_⟩
    rw [uIcc_of_le hT] at hτ
    exact h.2.2.2.2 τ hτ
  exact (hsol.flow_eq hf hu ⟨le_rfl, hT⟩ ht).symm

/-- A measurable control with values in `U` on `[0, T]` and the flow from `(0, x₀)` form an
admissible pair. -/
theorem isAdmissible_flow (hf : IsLipschitzSystem f U L) {T : ℝ} (hT : 0 ≤ T)
    (hum : Measurable u) (hU : ∀ t ∈ Icc 0 T, u t ∈ U) (x₀ : E) :
    IsAdmissible f U x₀ T u (fun t ↦ flow f u 0 t x₀) := by
  have hu : IsControlOn u U 0 T := ⟨hum.aestronglyMeasurable, hU⟩
  have hsol := isSolution_flow hf hu ⟨le_rfl, hT⟩ x₀
  refine ⟨hum, hU, ?_, hsol.2.1, fun t ht ↦ hsol.2.2 t (by rwa [uIcc_of_le hT])⟩
  simpa [uIcc_of_le hT] using hsol.1

end ControlSystem
