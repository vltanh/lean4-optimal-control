module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Convex.Topology

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

(1) In finite dimension a convex set whose closure is the whole space is the whole space (its
affine span is closed, so it has interior points, and every point is the midpoint of an interior
point and a point of the closure), so a point lies outside the closure; separate it
(`geometric_hahn_banach_closed_point`) and use the cone property. (2) Write `±eᵢ` for a basis as
finite nonnegative combinations. (3) The minimum of `h(ξ) = Σᵢ max(ξ(vᵢ), 0)` over the unit
sphere of the dual is positive (a unit covector with `h(ξ) = 0` is `≤ 0` on the hull, that is
everywhere); if `‖v'ᵢ - vᵢ‖ < min h / (k + 1)` and the hull of the `v'ᵢ` were not everything, the
unit covector of (1) would have `h(ξ) < min h`.
-/

@[expose] public section

open Set Filter Topology Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A (pointed) convex cone other than the whole space lies in a closed half-space through the
origin: there is a covector `ξ ≠ 0` with `ξ x ≤ 0` on the cone. -/
theorem exists_dual_ne_zero_nonpos_of_ne_top {C : PointedCone ℝ E} (hC : C ≠ ⊤) :
    ∃ ξ : StrongDual ℝ E, ξ ≠ 0 ∧ ∀ x ∈ C, ξ x ≤ 0 := by
  have hconv : Convex ℝ (closure (C : Set E)) := C.convex.closure
  by_cases hcl : closure (C : Set E) = univ
  · -- a dense convex set in finite dimension is everything
    exfalso
    apply hC
    have haff : affineSpan ℝ (C : Set E) = ⊤ := by
      have hsub : closure (C : Set E) ⊆ affineSpan ℝ (C : Set E) :=
        closure_minimal (subset_affineSpan ℝ _)
          (AffineSubspace.closed_of_finiteDimensional _)
      refine eq_top_iff.2 fun x _ ↦ hsub ?_
      rw [hcl]
      trivial
    obtain ⟨y, hy⟩ := C.convex.interior_nonempty_iff_affineSpan_eq_top.2 haff
    rw [eq_top_iff]
    intro x _
    have hz : (2 : ℝ) • x - y ∈ closure (C : Set E) := by rw [hcl]; trivial
    have hseg : x ∈ openSegment ℝ y ((2 : ℝ) • x - y) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
    exact interior_subset (C.convex.openSegment_interior_closure_subset_interior hy hz hseg)
  · obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).1 hcl
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hconv isClosed_closure hx
    have hu0 : 0 < u := by simpa using hfu 0 (subset_closure C.zero_mem)
    refine ⟨f, fun hf ↦ ?_, fun a ha ↦ ?_⟩
    · rw [hf, zero_apply] at hux
      linarith
    · by_contra hfa
      push Not at hfa
      have hc : 0 ≤ u / f a := (div_pos hu0 hfa).le
      have hmem : (u / f a) • a ∈ C := by
        exact C.smul_mem hc ha
      have := hfu _ (subset_closure hmem)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfa.ne'] at this
      exact lt_irrefl _ this

/-- If the cone hull of a set `S` is the whole space, so is the cone hull of a finite subset. -/
theorem exists_finset_hull_eq_top {S : Set E} (hS : PointedCone.hull ℝ S = ⊤) :
    ∃ s : Finset E, ↑s ⊆ S ∧ PointedCone.hull ℝ (s : Set E) = ⊤ := by
  classical
  let b := Module.finBasis ℝ E
  -- `± bᵢ` are finite nonnegative combinations of elements of `S`
  have hfin : ∀ v : E, ∃ T : Finset E, ↑T ⊆ S ∧ v ∈ PointedCone.hull ℝ (T : Set E) := by
    intro v
    have hv : v ∈ PointedCone.hull ℝ S := by rw [hS]; trivial
    exact Submodule.mem_span_finite_of_mem_span hv
  choose T hTS hT using hfin
  let s : Finset E := Finset.univ.biUnion fun i ↦ T (b i) ∪ T (-b i)
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    simp only [s, Finset.coe_biUnion, Finset.coe_union, mem_iUnion, mem_union] at hx
    obtain ⟨i, -, hx | hx⟩ := hx
    exacts [hTS _ hx, hTS _ hx]
  -- every real multiple of `bᵢ` is in the hull, hence every vector
  have hmono : ∀ v ∈ ({b i | i} ∪ {-b i | i} : Set E), v ∈ PointedCone.hull ℝ (s : Set E) := by
    rintro v (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine Submodule.span_mono ?_ (hT (b i))
      intro x hx
      simp only [s, Finset.coe_biUnion, Finset.coe_union, mem_iUnion, mem_union]
      exact ⟨i, Finset.mem_coe.2 (Finset.mem_univ _), Or.inl hx⟩
    · refine Submodule.span_mono ?_ (hT (-b i))
      intro x hx
      simp only [s, Finset.coe_biUnion, Finset.coe_union, mem_iUnion, mem_union]
      exact ⟨i, Finset.mem_coe.2 (Finset.mem_univ _), Or.inr hx⟩
  have hsmul : ∀ (i) (c : ℝ), c • b i ∈ PointedCone.hull ℝ (s : Set E) := by
    intro i c
    rcases le_total 0 c with hc | hc
    · exact PointedCone.smul_mem _ hc (hmono _ (Or.inl ⟨i, rfl⟩))
    · have := PointedCone.smul_mem _ (neg_nonneg.2 hc) (hmono _ (Or.inr ⟨i, rfl⟩))
      simpa using this
  rw [eq_top_iff]
  intro x _
  rw [← b.sum_repr x]
  exact Submodule.sum_mem _ fun i _ ↦ hsmul i _

/-- If the cone hull of `v₁, …, v_k` is the whole space, the same holds for every family
`v'` close enough to `v`. -/
theorem exists_forall_hull_eq_top_of_dist_lt {k : ℕ} {v : Fin k → E}
    (hv : PointedCone.hull ℝ (range v) = ⊤) :
    ∃ ε > 0, ∀ v' : Fin k → E, (∀ i, ‖v' i - v i‖ < ε) → PointedCone.hull ℝ (range v') = ⊤ := by
  -- a family that does not generate has a unit covector `≤ 0` on it
  have hsupp : ∀ v' : Fin k → E, PointedCone.hull ℝ (range v') ≠ ⊤ →
      ∃ ξ : StrongDual ℝ E, ξ ∈ sphere (0 : StrongDual ℝ E) 1 ∧ ∀ i, ξ (v' i) ≤ 0 := by
    intro v' hv'
    obtain ⟨ξ, hξ0, hξ⟩ := exists_dual_ne_zero_nonpos_of_ne_top hv'
    refine ⟨‖ξ‖⁻¹ • ξ, ?_, fun i ↦ ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ0)]
    · rw [smul_apply, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _))
        (hξ _ (PointedCone.subset_hull ⟨i, rfl⟩))
  by_cases hS : (sphere (0 : StrongDual ℝ E) 1).Nonempty
  swap
  · refine ⟨1, one_pos, fun v' _ ↦ ?_⟩
    by_contra hne
    obtain ⟨ξ, hξ, -⟩ := hsupp v' hne
    exact hS ⟨ξ, hξ⟩
  -- `h(ξ) = Σᵢ max(ξ(vᵢ), 0)` has a positive minimum on the unit sphere of the dual
  let h : StrongDual ℝ E → ℝ := fun ξ ↦ ∑ i, max (ξ (v i)) 0
  have hcont : Continuous h := continuous_finsetSum _ fun i _ ↦
    ((ContinuousLinearMap.apply ℝ ℝ (v i)).continuous).max continuous_const
  obtain ⟨ξ₀, hξ₀S, hmin⟩ := (isCompact_sphere (0 : StrongDual ℝ E) 1).exists_isMinOn hS
    hcont.continuousOn
  have hpos : 0 < h ξ₀ := by
    by_contra hle
    have hle' : h ξ₀ ≤ 0 := not_lt.1 hle
    -- then `ξ₀ ≤ 0` on every `vᵢ`, hence on the whole space, so `ξ₀ = 0`
    have hvi : ∀ i, ξ₀ (v i) ≤ 0 := by
      intro i
      have h0 : ∀ j ∈ Finset.univ, 0 ≤ max (ξ₀ (v j)) 0 := fun j _ ↦ le_max_right _ _
      have := (Finset.sum_eq_zero_iff_of_nonneg h0).1 (le_antisymm hle'
        (Finset.sum_nonneg h0)) i (Finset.mem_univ _)
      exact (le_max_left _ _).trans this.le
    have hall : ∀ x, ξ₀ x ≤ 0 := by
      intro x
      have hx : x ∈ PointedCone.hull ℝ (range v) := by rw [hv]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hvi i
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; linarith
      | smul c x _ hx =>
        rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos c.2 hx
    have : ξ₀ = 0 := by
      ext x
      exact le_antisymm (hall x) (by simpa using hall (-x))
    rw [this, mem_sphere_zero_iff_norm, norm_zero] at hξ₀S
    exact zero_ne_one hξ₀S
  refine ⟨h ξ₀ / (k + 1), by positivity, fun v' hv' ↦ ?_⟩
  by_contra hne
  obtain ⟨ξ, hξS, hξ⟩ := hsupp v' hne
  have hξn : ‖ξ‖ = 1 := mem_sphere_zero_iff_norm.1 hξS
  -- `h(ξ) < h(ξ₀)`, a contradiction
  have hterm : ∀ i ∈ Finset.univ, max (ξ (v i)) 0 ≤ h ξ₀ / (k + 1) := by
    intro i _
    refine max_le ?_ (by positivity)
    have : ξ (v i) = ξ (v' i) + ξ (v i - v' i) := by rw [map_sub]; ring
    rw [this]
    have h1 := (ξ.le_opNorm (v i - v' i)).trans (le_of_eq (by rw [hξn, one_mul]))
    have h2 := (le_abs_self _).trans (h1.trans_eq' (Real.norm_eq_abs _).symm)
    have h3 : ‖v i - v' i‖ < h ξ₀ / (k + 1) := by rw [norm_sub_rev]; exact hv' i
    linarith [hξ i]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hlt : (k : ℝ) * (h ξ₀ / (k + 1)) < h ξ₀ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  exact absurd (hmin hξS) (not_le.2 (hsum.trans_lt hlt))
