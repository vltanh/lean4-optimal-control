module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.EMetricSpace.Lipschitz
-- Brouwer's fixed-point theorem, for the proof (A–S use it in the proof of Lemma 12.1).
import FixedPoint.Brouwer.Convex
-- Equicontinuity and pointwise convergence give uniform convergence (Ascoli).
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Openness at the vertex of a cone (Agrachev–Sachkov's Lemma 12.1)

If a map `F` with `F(0) = 0` is Lipschitz near `0` on a convex cone `C`, differentiable at `0`
within `C`, and its derivative maps `C` onto the target, then `F` maps every neighbourhood of `0`
in `C` onto a neighbourhood of `0` (`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`).

## Source and reading

Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint* (authors' draft, §12.2,
Lemma 12.1, p. 168): "Let a vector-function `F : ℝᵐ → ℝⁿ` be Lipschitzian, `F(0) = 0`, and
differentiable at 0 … Assume that `F'₀(ℝᵐ₊) = ℝⁿ`. Then for any neighborhood of the origin
`O₀ ⊂ ℝᵐ`, `0 ∈ int F(O₀ ∩ ℝᵐ₊)`", with Remark (1): "The statement of this lemma holds if the
orthant `ℝᵐ₊` is replaced by an arbitrary convex cone `C ⊂ ℝᵐ`. In this case the proof given
below works without any changes." The literal statement is `Pontryagin.lemma12_1`.

Reading (departure D8): the lemma is stated in the form of Remark (1), for any convex cone, which
is the form used (the needle map is defined only on `ℝᵏ₊`, and on `N₀ × ℝᵏ₊` in the proof of
Theorem 12.4 (2)): `F` is Lipschitz only on `C ∩ B(0, ρ)` and differentiable at `0` within `C`.

Gap in A–S (Remark (1)): the proof takes the preimages `vᵢ` in `int C` and a ball `B_δ ⊆ W` with
`v + B_δ ⊆ int C`; a convex cone may have empty interior, and then these points do not exist.
Departure, which repairs Remark (1) for such cones: the `vᵢ` are only taken in `C`, and the points
used are `v + L z`, `z` in a small ball `B` of the target, which are combinations of the `vᵢ` with
positive coefficients and so lie in `C`; the proof uses no interior, relative or not. For the cones
to which the lemma is applied, `ℝᵏ₊` and `P × ℝᵏ₊`, which have interior points, A–S's step is
valid as written.

## Proof (A–S's)

Choose `y₀, …, yₙ` spanning a simplex centred at `0` (here `yⱼ₊₁ = eⱼ` for a basis `e` of the
target and `y₀ = -Σ eⱼ`) and `vᵢ ∈ C` with `F'vᵢ = yᵢ`; `v = mean(vᵢ)` has `F'v = 0`, the span
`W` of the `vᵢ - v` is `n`-dimensional and `F' : W → ℝⁿ` is invertible, with inverse
`L(eⱼ) = vⱼ₊₁ - v`. The set `L(B) ⊆ W` plays the role of A–S's ball `B_δ`, and `B = G₀(L(B))`
that of `G₀(B_δ)`, where `G_α(w) = α⁻¹F(α(v + w))` and `G₀ = F'`. The maps
`G_α ∘ G₀⁻¹ : z ↦ α⁻¹F(α(v + L z))` on `B`, `0 < α < α₀`, are Lipschitz with a common constant
(`F` is Lipschitz near `0` on `C`), hence equicontinuous, and tend to the identity pointwise by
(12.11) (`HasFDerivWithinAt.lim`), hence uniformly on the compact set `B` (Mathlib's
`Equicontinuous.tendsto_uniformFun_iff_pi`). For `x̃` small, `Id - G_α ∘ G₀⁻¹ + x̃` maps the
compact convex set `B` into itself; **Brouwer's fixed point theorem** gives
`G_α ∘ G₀⁻¹(z) = x̃`. Hence
`0 ∈ int F(α(v + L(B)))` for small `α > 0`. Brouwer's theorem is the only topological input of
the whole proof of the maximum principle; it comes from the FixedPoint package,
`Brouwer.exists_fixedPoint` (no source is given by A–S; departure D10).
-/

@[expose] public section

open Set Filter Topology Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- **Agrachev–Sachkov, Lemma 12.1 with Remark (1)** (authors' draft, p. 168). Let `C` be a convex
cone, and `Fm` a map with `Fm 0 = 0`, Lipschitz on `C ∩ B(0, ρ)`, differentiable at `0` within
`C` with a derivative `Fm'` that maps `C` onto the target. Then for every neighbourhood `O` of
`0`, `0 ∈ int Fm(O ∩ C)`. -/
theorem HasFDerivWithinAt.zero_mem_interior_image_inter_cone {C : Set E} {Fm : E → F}
    {Fm' : E →L[ℝ] F} (hFm : HasFDerivWithinAt Fm Fm' C 0) (hC : Convex ℝ C)
    (hCcone : ∀ x ∈ C, ∀ c : ℝ, 0 ≤ c → c • x ∈ C)
    (h0 : Fm 0 = 0) (hlip : ∃ ρ > 0, ∃ K, LipschitzOnWith K Fm (C ∩ ball 0 ρ))
    (hsurj : Fm' '' C = univ) :
    ∀ O ∈ 𝓝 (0 : E), (0 : F) ∈ interior (Fm '' (O ∩ C)) := by
  classical
  intro O hO
  have hpre : ∀ w : F, ∃ c ∈ C, Fm' c = w := fun w ↦ by
    have : w ∈ Fm' '' C := by rw [hsurj]; trivial
    exact this
  -- `C` as a pointed cone: it contains the nonnegative combinations of its points
  obtain ⟨x₀, hx₀, -⟩ := hpre 0
  let K : PointedCone ℝ E :=
    { carrier := C
      add_mem' := fun {x y} hx hy ↦ by
        have h := hCcone _ (hC hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)) 2 (by norm_num)
        convert h using 1
        module
      zero_mem' := by simpa using hCcone x₀ hx₀ 0 le_rfl
      smul_mem' := fun c x hx ↦ by
        simpa [← Nonneg.coe_smul] using hCcone x hx c c.2 }
  have hKC : ∀ x, x ∈ K ↔ x ∈ C := fun _ ↦ Iff.rfl
  -- (A–S) points `y₀, …, yₙ` that generate an `n`-dimensional simplex centred at the origin
  let b := Module.finBasis ℝ F
  let y : Fin (Module.finrank ℝ F + 1) → F := Fin.cons (-∑ j, b j) b
  have hy : ∑ i, y i = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [y, Fin.cons_zero, Fin.cons_succ]
    exact neg_add_cancel _
  -- their preimages `vᵢ ∈ C` and the mean `v`, with `F'v = 0`
  choose c hcC hcy using fun i ↦ hpre (y i)
  set m : ℝ := Module.finrank ℝ F + 1 with hm
  have hm0 : 0 < m := by positivity
  let v : E := m⁻¹ • ∑ i, c i
  have hv0 : Fm' v = 0 := by simp [v, map_sum, hcy, hy]
  -- the inverse `L : F → W` of `F'` on `W = span{vᵢ - v}`
  let L : F →L[ℝ] E :=
    LinearMap.toContinuousLinearMap (b.constr ℝ fun j ↦ c j.succ - v)
  have hL : ∀ z, Fm' (L z) = z := by
    intro z
    have : Fm' (L z) = ∑ j, b.equivFun z j • b j := by
      simp [L, Module.Basis.constr_apply_fintype, map_sum, map_sub, hcy, hv0, y]
    rw [this, b.sum_equivFun]
  -- a ball `B` in `F` with `v + L(B) ⊆ C` (A–S: a ball `B_δ ⊆ W` with `v + B_δ ⊆ int C`)
  obtain ⟨r, hr, hrC⟩ : ∃ r > 0, ∀ z ∈ closedBall (0 : F) r, v + L z ∈ C := by
    have hev : ∀ᶠ z in 𝓝 (0 : F), ∀ j, |b.equivFun z j| < 1 / (2 * m) := by
      refine Filter.eventually_all.2 fun j ↦ ?_
      have hc : Continuous fun z ↦ b.equivFun z j :=
        ((LinearMap.proj j).comp b.equivFun.toLinearMap).continuous_of_finiteDimensional
      have h := (hc.abs).tendsto 0
      simp only [map_zero, Pi.zero_apply, abs_zero] at h
      exact h (gt_mem_nhds (by positivity))
    obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨ε / 2, half_pos hε, fun z hz ↦ ?_⟩
    have hη := hεball (lt_of_le_of_lt (mem_closedBall.1 hz) (half_lt_self hε))
    set η := b.equivFun z
    set S := ∑ j, η j
    set A := ∑ j : Fin (Module.finrank ℝ F), c j.succ
    set P := ∑ j, η j • c j.succ
    have hS : |S| ≤ Module.finrank ℝ F * (1 / (2 * m)) := by
      calc |S| ≤ ∑ j, |η j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin (Module.finrank ℝ F), 1 / (2 * m) :=
            Finset.sum_le_sum fun j _ ↦ (hη j).le
        _ = Module.finrank ℝ F * (1 / (2 * m)) := by simp
    have hS' : S ≤ 1 / 2 := by
      have : (Module.finrank ℝ F : ℝ) * (1 / (2 * m)) ≤ 1 / 2 := by
        rw [hm]; field_simp; linarith
      linarith [le_abs_self S]
    have hLz : L z = P - S • v := by
      simp [L, Module.Basis.constr_apply_fintype, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul,
        P, S, η]
    have hv : v = m⁻¹ • (c 0 + A) := by simp [v, Fin.sum_univ_succ, A]
    have hsum : ∑ j, ((1 - S) / m + η j) • c j.succ = ((1 - S) / m) • A + P := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ add_smul _ _ _
    have key : v + L z = ((1 - S) / m) • c 0 + ∑ j, ((1 - S) / m + η j) • c j.succ := by
      rw [hsum, hLz, hv]
      module
    rw [key, ← hKC]
    have hcoef : 0 ≤ (1 - S) / m := div_nonneg (by linarith) hm0.le
    refine K.add_mem (K.smul_mem hcoef (hcC 0)) (K.sum_mem fun j _ ↦ K.smul_mem ?_ (hcC _))
    have h1 : 1 / (2 * m) ≤ (1 - S) / m := by
      rw [div_le_div_iff₀ (by positivity) hm0]; nlinarith
    linarith [neg_abs_le (η j), hη j]
  obtain ⟨ρ, hρ, Kl, hKl⟩ := hlip
  obtain ⟨εO, hεO, hεOO⟩ := Metric.mem_nhds_iff.1 hO
  set R := ‖v‖ + ‖L‖ * r with hR
  have hR0 : 0 ≤ R := by positivity
  have hvLz : ∀ z ∈ closedBall (0 : F) r, ‖v + L z‖ ≤ R := by
    intro z hz
    calc ‖v + L z‖ ≤ ‖v‖ + ‖L z‖ := norm_add_le _ _
      _ ≤ ‖v‖ + ‖L‖ * r := by
          gcongr
          exact (L.le_opNorm z).trans (by gcongr; exact mem_closedBall_zero_iff.1 hz)
  -- for `0 < α < α₀`, the points `α (v + L z)`, `z ∈ B`, lie in `O ∩ C ∩ B(0, ρ)`
  set α₀ := min ρ εO / (R + 1) with hα₀
  have hα₀0 : 0 < α₀ := by positivity
  have hxbd : ∀ α ∈ Ioo 0 α₀, ∀ z ∈ closedBall (0 : F) r, ‖α • (v + L z)‖ < min ρ εO := by
    intro α hα z hz
    rw [norm_smul, Real.norm_of_nonneg hα.1.le]
    calc α * ‖v + L z‖ ≤ α₀ * R := mul_le_mul hα.2.le (hvLz z hz) (norm_nonneg _) hα₀0.le
      _ < α₀ * (R + 1) := mul_lt_mul_of_pos_left (by linarith) hα₀0
      _ = min ρ εO := by rw [hα₀]; field_simp
  have hxC : ∀ α : ℝ, 0 ≤ α → ∀ z ∈ closedBall (0 : F) r, α • (v + L z) ∈ C :=
    fun α hα z hz ↦ hCcone _ (hrC z hz) α hα
  have hxρ : ∀ α ∈ Ioo 0 α₀, ∀ z ∈ closedBall (0 : F) r, α • (v + L z) ∈ C ∩ ball 0 ρ :=
    fun α hα z hz ↦ ⟨hxC α hα.1.le z hz,
      mem_ball_zero_iff.2 ((hxbd α hα z hz).trans_le (min_le_left _ _))⟩
  -- A–S's maps `G_α ∘ G₀⁻¹ : z ↦ α⁻¹ F(α(v + L z))` on the compact ball `B`, `0 < α < α₀`
  let B := closedBall (0 : F) r
  have : CompactSpace B := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 r)
  let G : Ioo (0 : ℝ) α₀ → B → F := fun α z ↦ (α : ℝ)⁻¹ • Fm ((α : ℝ) • (v + L z))
  -- (A–S) "Since the mapping `F` is Lipschitzian, all mappings `G_α` are Lipschitzian with a
  -- common constant. Thus the family `G_α` is equicontinuous."
  have hGlip : ∀ α, LipschitzWith (Kl * ‖L‖₊) (G α) := by
    intro α
    have hα0 : 0 < (α : ℝ) := α.2.1
    refine LipschitzWith.of_dist_le_mul fun z z' ↦ ?_
    calc dist (G α z) (G α z')
        = (α : ℝ)⁻¹ * dist (Fm ((α : ℝ) • (v + L z))) (Fm ((α : ℝ) • (v + L z'))) := by
          simp only [G, dist_smul₀, norm_inv, Real.norm_of_nonneg hα0.le]
      _ ≤ (α : ℝ)⁻¹ * (Kl * dist ((α : ℝ) • (v + L z)) ((α : ℝ) • (v + L z'))) :=
          mul_le_mul_of_nonneg_left
            (hKl.dist_le_mul _ (hxρ α α.2 z z.2) _ (hxρ α α.2 z' z'.2)) (inv_nonneg.2 hα0.le)
      _ = Kl * ‖L ((z : F) - z')‖ := by
          rw [dist_smul₀, Real.norm_of_nonneg hα0.le, dist_eq_norm, add_sub_add_left_eq_sub,
            ← map_sub]
          field_simp
      _ ≤ Kl * (‖L‖ * dist z z') := by
          gcongr
          rw [Subtype.dist_eq, dist_eq_norm]
          exact L.le_opNorm _
      _ = ↑(Kl * ‖L‖₊) * dist z z' := by push_cast; ring
  have hGeq : Equicontinuous G := (LipschitzWith.uniformEquicontinuous G _ hGlip).equicontinuous
  -- the limit `α → 0+`
  let ℱ : Filter (Ioo (0 : ℝ) α₀) := comap Subtype.val (𝓝[>] 0)
  have : ℱ.NeBot := NeBot.comap_of_range_mem inferInstance
    (by rw [Subtype.range_coe]; exact Ioo_mem_nhdsGT hα₀0)
  -- (12.11): `α⁻¹ F(α(v + L z)) = F'₀(v + L z) + o(1) = z` as `α → 0+`, for every `z`
  have hpt : Tendsto G ℱ (𝓝 fun z : B ↦ (z : F)) := by
    rw [tendsto_pi_nhds]
    intro z
    have hd : Tendsto (fun a : ℝ ↦ a • (v + L z)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun a : ℝ ↦ a • (v + L z)) (𝓝 0) (𝓝 ((0 : ℝ) • (v + L z))) :=
        (continuous_id.smul continuous_const).tendsto 0
      rw [zero_smul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hdC : ∀ᶠ a in 𝓝[>] (0 : ℝ), (0 : E) + a • (v + L z) ∈ C := by
      filter_upwards [self_mem_nhdsWithin] with a ha
      rw [zero_add]
      exact hxC a (mem_Ioi.1 ha).le z z.2
    have hcd : Tendsto (fun a : ℝ ↦ a⁻¹ • a • (v + L z)) (𝓝[>] 0) (𝓝 (v + L z)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with a ha
      exact (inv_smul_smul₀ (mem_Ioi.1 ha).ne' _).symm
    have hlim := hFm.lim (c := fun a : ℝ ↦ a⁻¹) hd hdC hcd
    simp only [zero_add, h0, sub_zero, map_add, hv0, hL] at hlim
    exact hlim.comp tendsto_comap
  -- (A–S) "… pointwise, thus uniformly" (Ascoli)
  have hunif : TendstoUniformly G (fun z : B ↦ (z : F)) ℱ :=
    UniformFun.tendsto_iff_tendstoUniformly.1 ((hGeq.tendsto_uniformFun_iff_pi ℱ _).2 hpt)
  obtain ⟨α, hα⟩ := (Metric.tendstoUniformly_iff.1 hunif (r / 2) (by positivity)).exists
  set a : ℝ := α.1 with ha
  have ha0 : 0 < a := α.2.1
  -- `G_α ∘ G₀⁻¹` is uniformly `r/2`-close to the identity
  have hG : ∀ z ∈ closedBall (0 : F) r, ‖a⁻¹ • Fm (a • (v + L z)) - z‖ ≤ r / 2 := by
    intro z hz
    have h := hα ⟨z, hz⟩
    rw [dist_comm, dist_eq_norm] at h
    exact h.le
  -- continuity of `G_α ∘ G₀⁻¹` on the ball (`F` is Lipschitz on `C ∩ B(0, ρ)`)
  have hGcont : ContinuousOn (fun z ↦ a⁻¹ • Fm (a • (v + L z))) (closedBall (0 : F) r) :=
    (hKl.continuousOn.comp (by fun_prop) fun z hz ↦ hxρ a α.2 z hz).const_smul _
  -- Brouwer: for `x̃` small, `Id - G_α ∘ G₀⁻¹ + x̃` has a fixed point in the ball
  have hsol : ∀ w ∈ closedBall (0 : F) (r / 2), ∃ z ∈ closedBall (0 : F) r,
      a⁻¹ • Fm (a • (v + L z)) = w := by
    intro w hw
    have hmaps : MapsTo (fun z ↦ z - a⁻¹ • Fm (a • (v + L z)) + w) (closedBall (0 : F) r)
        (closedBall (0 : F) r) := by
      intro z hz
      rw [mem_closedBall_zero_iff]
      calc ‖z - a⁻¹ • Fm (a • (v + L z)) + w‖
          ≤ ‖a⁻¹ • Fm (a • (v + L z)) - z‖ + ‖w‖ := by
            rw [← norm_neg (a⁻¹ • Fm (a • (v + L z)) - z), neg_sub]; exact norm_add_le _ _
        _ ≤ r / 2 + r / 2 := add_le_add (hG z hz) (mem_closedBall_zero_iff.1 hw)
        _ = r := by ring
    obtain ⟨z, hz, hfix⟩ := Brouwer.exists_fixedPoint (convex_closedBall 0 r)
      (isCompact_closedBall 0 r) (nonempty_closedBall.2 hr.le) hmaps
      ((continuousOn_id.sub hGcont).add continuousOn_const)
    refine ⟨z, hz, ?_⟩
    have : z - a⁻¹ • Fm (a • (v + L z)) + w - z = 0 := by rw [hfix, sub_self]
    linear_combination (norm := module) -this
  -- hence `F(α(v + B)) ⊇ α B(0, r/2)`, a neighbourhood of `0`
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset (closedBall_mem_nhds (0 : F) (by positivity : 0 < a * (r / 2))) ?_
  intro w hw
  have hw' : a⁻¹ • w ∈ closedBall (0 : F) (r / 2) := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg ha0.le]
    rw [inv_mul_le_iff₀ ha0]
    exact mem_closedBall_zero_iff.1 hw
  obtain ⟨z, hz, hzw⟩ := hsol _ hw'
  refine ⟨a • (v + L z), ⟨hεOO ?_, hxC a ha0.le z hz⟩, ?_⟩
  · exact mem_ball_zero_iff.2 ((hxbd a α.2 z hz).trans_le (min_le_right _ _))
  · rw [← smul_inv_smul₀ ha0.ne' (Fm _), hzw, smul_inv_smul₀ ha0.ne']
