module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.EMetricSpace.Lipschitz
-- Brouwer's fixed-point theorem, for the proof (A–S use it in the proof of Lemma 12.1).
import FixedPoint.Brouwer.Convex

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

Gap in A–S: the proof picks points of `int C`, which is empty for a cone with empty interior
(Remark (1) allows any convex cone). For such cones read `int` as the interior relative to
`span C`: the points `v + w` used below are combinations of the `vᵢ ∈ C` with positive
coefficients, so they lie in `C` whether or not `C` has interior points.

## Proof (A–S's)

Choose `y₀, …, yₙ` spanning a simplex centred at `0` (here `yⱼ₊₁ = eⱼ` for a basis `e` of the
target and `y₀ = -Σ eⱼ`) and `vᵢ ∈ C` with `F'vᵢ = yᵢ`; `v = mean(vᵢ)` has `F'v = 0`, the span
`W` of the `vᵢ - v` is `n`-dimensional and `F' : W → ℝⁿ` is invertible, with inverse
`L(eⱼ) = vⱼ₊₁ - v`. A ball `B` around `0` in the target with `v + L(B) ⊆ C` plays the role of
A–S's `G₀(B_δ)`: `v + L(z)` is a combination of the `vᵢ` with coefficients near `1/(n+1)`. The
maps `G_α(z) = α⁻¹F(α(v + L z))` tend to `G₀ = id` uniformly on `B` (12.11). For `x̃` small,
`Id - G_α + x̃` maps the compact convex set `B` into itself; **Brouwer's fixed point theorem**
gives `G_α(z) = x̃`. Hence `0 ∈ int F(α(v + L(B)))` for small `α > 0`. Brouwer's theorem is the
only topological input of the whole proof of the maximum principle; it comes from the
FixedPoint package, `Brouwer.exists_fixedPoint` (no source is given by A–S; departure D10).

Departure from the source (D8): the uniform convergence `G_α → G₀` is read off (12.11) directly,
since `F(x) = F'x + o(‖x‖)` within `C` and `‖α(v + L z)‖ ≤ α (‖v‖ + ‖L‖ r)` on `B`, so the `o(1)`
of (12.11) is uniform in `z`; A–S derive it from pointwise convergence and the equicontinuity of
the `G_α` (a common Lipschitz constant). The Lipschitz hypothesis is used for the continuity of
`G_α`, which Brouwer's theorem needs.
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
  -- (12.11) uniformly on the ball: `F(x) = F'x + o(x)` within `C`
  have hlo : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ C, ‖x‖ < δ → ‖Fm x - Fm' x‖ ≤ ε * ‖x‖ := by
    intro ε hε
    have h := hFm.isLittleO.def hε
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
    obtain ⟨δ, hδ, h⟩ := h
    refine ⟨δ, hδ, fun x hx hxδ ↦ ?_⟩
    have := h (by simpa using hxδ) hx
    simpa [h0] using this
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
  obtain ⟨δ, hδ, hδlo⟩ := hlo (r / (2 * (R + 1))) (by positivity)
  set α := min δ (min ρ εO) / (2 * (R + 1)) with hα
  have hα0 : 0 < α := by positivity
  -- the points `α (v + L z)`, `z ∈ B`, lie in `O ∩ C ∩ B(0, ρ)` and have norm `< δ`
  have hxbd : ∀ z ∈ closedBall (0 : F) r, ‖α • (v + L z)‖ < min δ (min ρ εO) := by
    intro z hz
    have hz' : ‖v + L z‖ ≤ R := hvLz z hz
    rw [norm_smul, Real.norm_of_nonneg hα0.le]
    calc α * ‖v + L z‖ ≤ α * R := mul_le_mul_of_nonneg_left hz' hα0.le
      _ < α * (2 * (R + 1)) := mul_lt_mul_of_pos_left (by linarith) hα0
      _ = min δ (min ρ εO) := by rw [hα]; field_simp
  have hxC : ∀ z ∈ closedBall (0 : F) r, α • (v + L z) ∈ C := fun z hz ↦
    hCcone _ (hrC z hz) α hα0.le
  -- `G_α(z) = α⁻¹ F(α(v + L z))` is uniformly `r/2`-close to `G₀ = id`
  have hG : ∀ z ∈ closedBall (0 : F) r, ‖α⁻¹ • Fm (α • (v + L z)) - z‖ ≤ r / 2 := by
    intro z hz
    have hlin : Fm' (α • (v + L z)) = α • z := by rw [map_smul, map_add, hv0, hL, zero_add]
    have hx := hxbd z hz
    have h1 := hδlo _ (hxC z hz) (hx.trans_le (min_le_left _ _))
    have heq : α⁻¹ • Fm (α • (v + L z)) - z =
        α⁻¹ • (Fm (α • (v + L z)) - Fm' (α • (v + L z))) := by
      rw [hlin, smul_sub, inv_smul_smul₀ hα0.ne']
    have hz' : ‖v + L z‖ ≤ R := hvLz z hz
    rw [heq, norm_smul, norm_inv, Real.norm_of_nonneg hα0.le]
    rw [norm_smul, Real.norm_of_nonneg hα0.le] at h1
    calc α⁻¹ * ‖Fm (α • (v + L z)) - Fm' (α • (v + L z))‖
        ≤ α⁻¹ * (r / (2 * (R + 1)) * (α * ‖v + L z‖)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hα0.le)
      _ = r / (2 * (R + 1)) * ‖v + L z‖ := by field_simp
      _ ≤ r / (2 * (R + 1)) * R := mul_le_mul_of_nonneg_left hz' (by positivity)
      _ ≤ r / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  -- continuity of `G_α` on the ball (`F` is Lipschitz on `C ∩ B(0, ρ)`)
  have hGcont : ContinuousOn (fun z ↦ α⁻¹ • Fm (α • (v + L z))) (closedBall (0 : F) r) := by
    refine (hKl.continuousOn.comp (by fun_prop) fun z hz ↦ ⟨hxC z hz, ?_⟩).const_smul _
    exact mem_ball_zero_iff.2 ((hxbd z hz).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  -- Brouwer: for `x̃` small, `Id - G_α + x̃` has a fixed point in the ball
  have hsol : ∀ w ∈ closedBall (0 : F) (r / 2), ∃ z ∈ closedBall (0 : F) r,
      α⁻¹ • Fm (α • (v + L z)) = w := by
    intro w hw
    have hmaps : MapsTo (fun z ↦ z - α⁻¹ • Fm (α • (v + L z)) + w) (closedBall (0 : F) r)
        (closedBall (0 : F) r) := by
      intro z hz
      rw [mem_closedBall_zero_iff]
      calc ‖z - α⁻¹ • Fm (α • (v + L z)) + w‖
          ≤ ‖α⁻¹ • Fm (α • (v + L z)) - z‖ + ‖w‖ := by
            rw [← norm_neg (α⁻¹ • Fm (α • (v + L z)) - z), neg_sub]; exact norm_add_le _ _
        _ ≤ r / 2 + r / 2 := add_le_add (hG z hz) (mem_closedBall_zero_iff.1 hw)
        _ = r := by ring
    obtain ⟨z, hz, hfix⟩ := Brouwer.exists_fixedPoint (convex_closedBall 0 r)
      (isCompact_closedBall 0 r) (nonempty_closedBall.2 hr.le) hmaps
      ((continuousOn_id.sub hGcont).add continuousOn_const)
    refine ⟨z, hz, ?_⟩
    have : z - α⁻¹ • Fm (α • (v + L z)) + w - z = 0 := by rw [hfix, sub_self]
    linear_combination (norm := module) -this
  -- hence `F(α(v + B)) ⊇ α B(0, r/2)`, a neighbourhood of `0`
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset (closedBall_mem_nhds (0 : F) (by positivity : 0 < α * (r / 2))) ?_
  intro w hw
  have hw' : α⁻¹ • w ∈ closedBall (0 : F) (r / 2) := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hα0.le]
    rw [inv_mul_le_iff₀ hα0]
    exact mem_closedBall_zero_iff.1 hw
  obtain ⟨z, hz, hzw⟩ := hsol _ hw'
  refine ⟨α • (v + L z), ⟨hεOO ?_, hxC z hz⟩, ?_⟩
  · exact mem_ball_zero_iff.2 ((hxbd z hz).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  · rw [← smul_inv_smul₀ hα0.ne' (Fm _), hzw, smul_inv_smul₀ hα0.ne']
