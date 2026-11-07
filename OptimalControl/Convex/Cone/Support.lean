module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Supporting hyperplanes and finite generation of convex cones

Three facts about convex cones in a finite-dimensional real normed space, which the proof of the
Pontryagin maximum principle of Agrachev–Sachkov (authors' draft, §12.2) uses without comment:

* a convex cone other than the whole space has a supporting hyperplane through the origin: a
  covector `ξ ≠ 0` with `ξ ≤ 0` on the cone (`exists_dual_ne_zero_nonpos_of_ne_top`; A–S,
  proof of Theorem 12.1, p. 172: "this set has a hyperplane of support at the origin");
* if the cone hull of a set is the whole space, so is the cone hull of a finite subset
  (`exists_finset_hull_eq_top`; A–S, proof of Lemma 12.2, p. 171: "We can choose vectors …
  `i = 1, …, k`, that generate the whole tangent space as a positive convex cone"; also the step
  that gives one separating covector for all needle variations in the proof of Theorem 12.4,
  departure D9);
* a finite family whose cone hull is the whole space keeps this property under small
  perturbations (`exists_forall_hull_eq_top_of_dist_lt`; A–S, p. 171: the vectors are moved to
  distinct Lebesgue points).

## Proof sketch

(1) In finite dimension a convex set whose closure is the whole space is the whole space, so a
point lies outside the closure; separate it (`geometric_hahn_banach_point_closed`) and use the
cone property. (2) Write `±eᵢ` for a basis as finite nonnegative combinations. (3) The minimum of
`max_i ξ(vᵢ)` over the unit sphere of the dual is positive (otherwise (1) applied to the hull
gives a contradiction), and it depends continuously on the `vᵢ`.
-/

@[expose] public section

open Set Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A (pointed) convex cone other than the whole space lies in a closed half-space through the
origin: there is a covector `ξ ≠ 0` with `ξ x ≤ 0` on the cone. -/
theorem exists_dual_ne_zero_nonpos_of_ne_top {C : PointedCone ℝ E} (hC : C ≠ ⊤) :
    ∃ ξ : StrongDual ℝ E, ξ ≠ 0 ∧ ∀ x ∈ C, ξ x ≤ 0 := by
  sorry

/-- If the cone hull of a set `S` is the whole space, so is the cone hull of a finite subset. -/
theorem exists_finset_hull_eq_top {S : Set E} (hS : PointedCone.hull ℝ S = ⊤) :
    ∃ s : Finset E, ↑s ⊆ S ∧ PointedCone.hull ℝ (s : Set E) = ⊤ := by
  sorry

/-- If the cone hull of `v₁, …, v_k` is the whole space, the same holds for every family
`v'` close enough to `v`. -/
theorem exists_forall_hull_eq_top_of_dist_lt {k : ℕ} {v : Fin k → E}
    (hv : PointedCone.hull ℝ (range v) = ⊤) :
    ∃ ε > 0, ∀ v' : Fin k → E, (∀ i, ‖v' i - v i‖ < ε) → PointedCone.hull ℝ (range v') = ⊤ := by
  sorry
