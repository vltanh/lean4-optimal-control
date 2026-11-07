module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.EMetricSpace.Lipschitz
-- Brouwer's fixed-point theorem, for the proof (A–S use it in the proof of Lemma 12.1).
import FixedPoint.Brouwer.Convex

/-!
# Openness at the vertex of a cone (Agrachev–Sachkov's Lemma 12.1)

If a map `F` with `F(0) = 0` is Lipschitz near `0` on a convex cone `C` with nonempty interior,
differentiable at `0` within `C`, and its derivative maps `C` onto the target, then `F` maps every
neighbourhood of `0` in `C` onto a neighbourhood of `0`
(`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`).

## Source and reading

Agrachev–Sachkov, *Control Theory from the Geometric Viewpoint* (authors' draft, §12.2,
Lemma 12.1, p. 168): "Let a vector-function `F : ℝᵐ → ℝⁿ` be Lipschitzian, `F(0) = 0`, and
differentiable at 0 … Assume that `F'₀(ℝᵐ₊) = ℝⁿ`. Then for any neighborhood of the origin
`O₀ ⊂ ℝᵐ`, `0 ∈ int F(O₀ ∩ ℝᵐ₊)`", with Remark (1): "The statement of this lemma holds if the
orthant `ℝᵐ₊` is replaced by an arbitrary convex cone `C ⊂ ℝᵐ`. In this case the proof given
below works without any changes." The literal statement is `Pontryagin.lemma12_1`.

Reading (departure D8): the lemma is stated in the form of Remark (1), which
is the form used (the needle map is defined only on `ℝᵏ₊`, and on `N₀ × ℝᵏ₊` in the proof of
Theorem 12.4 (2)): `F` is Lipschitz only on `C ∩ B(0, ρ)` and differentiable at `0` within `C`.
The proof picks points `vᵢ` in the interior of the cone, so the cone is assumed to have nonempty
interior (true for `ℝᵐ₊` and for `ℝˡ ⊕ ℝᵏ₊`; for a cone with empty interior the proof needs the
relative interior).

## Proof sketch (A–S's)

Choose `y₀, …, yₙ` spanning a simplex centred at `0` and `vᵢ ∈ int C` with `F'vᵢ = yᵢ` (the image
of `int C` is open, convex and dense, hence everything); `v = mean(vᵢ)` has `F'v = 0`, the span
`W` of the `vᵢ - v` is `n`-dimensional and `F' : W → ℝⁿ` is invertible; take a ball `B_δ ⊂ W`
with `v + B_δ ⊂ int C`. The maps `G_α(w) = α⁻¹F(α(v + w))` on `B_δ` are equi-Lipschitz and tend
to `G₀ = F'|_W` pointwise (12.11), hence uniformly. For `x̃` small, `Id - G_α ∘ G₀⁻¹ + x̃` maps
the compact convex set `G₀(B_δ)` into itself; **Brouwer's fixed point theorem** gives
`G_α(G₀⁻¹ x) = x̃`. Hence `0 ∈ int F(α(v + B_δ))` for small `α > 0`. Brouwer's theorem is the
only topological input of the whole proof of the maximum principle; it comes from the
FixedPoint package, `Brouwer.exists_fixedPoint` (no source is given by A–S; departure D10).
-/

@[expose] public section

open Set Filter Topology Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Agrachev–Sachkov, Lemma 12.1 with Remark (1)** (authors' draft, p. 168). Let `C` be a convex
cone with nonempty interior, and `Fm` a map with `Fm 0 = 0`, Lipschitz on `C ∩ B(0, ρ)`,
differentiable at `0` within `C` with a derivative `Fm'` that maps `C` onto the target. Then for
every neighbourhood `O` of `0`, `0 ∈ int Fm(O ∩ C)`. -/
theorem HasFDerivWithinAt.zero_mem_interior_image_inter_cone {C : Set E} {Fm : E → F}
    {Fm' : E →L[ℝ] F} (hFm : HasFDerivWithinAt Fm Fm' C 0) (hC : Convex ℝ C)
    (hCcone : ∀ x ∈ C, ∀ c : ℝ, 0 ≤ c → c • x ∈ C) (hCint : (interior C).Nonempty)
    (h0 : Fm 0 = 0) (hlip : ∃ ρ > 0, ∃ K, LipschitzOnWith K Fm (C ∩ ball 0 ρ))
    (hsurj : Fm' '' C = univ) :
    ∀ O ∈ 𝓝 (0 : E), (0 : F) ∈ interior (Fm '' (O ∩ C)) := by
  sorry
