module

public import OptimalControl.Pontryagin.Defs
public import OptimalControl.Convex.Cone.Openness
public import OptimalControl.Convex.Cone.Support
public import OptimalControl.ODE.NeedleVariation
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Tietze

/-!
# The geometric maximum principle (Agrachev–Sachkov, §§12.1–12.2)

A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the Geometric Viewpoint*, Springer, 2004,
Chapter 12, read in the authors' draft (pages below are the draft's), on an open subset `Ω` of a
finite-dimensional real normed space `E` (departure D1):

* **Lemma 12.1** (p. 168), the topological lemma: `lemma12_1` (literal) and, in the form of its
  Remark (1) on convex cones, `HasFDerivWithinAt.zero_mem_interior_image_inter_cone`
  (`OptimalControl/Convex/Cone/Openness.lean`);
* **Lemma 12.2** (p. 170): if the needle vectors `g_{τ,u}(q₁)`, `τ` a Lebesgue point of `ũ`,
  `u ∈ U`, generate the tangent space as a convex cone, then `q₁ ∈ int A_{q₀}(t₁)`: `lemma12_2`;
  in the generalized form that the proof of Theorem 12.4 uses (initial points `ψ(a)` varying,
  the end point composed with a submersion `Φ`, competitors near the reference):
  `lemma12_2_local`;
* **Theorem 12.1** (p. 164): if `q̃(t₁) ∈ ∂A_{q₀}(t₁)`, there is a Lipschitzian covector curve
  `λ_t ≠ 0` with `λ̇_t = h⃗_{ũ(t)}(λ_t)` and `h_{ũ(t)}(λ_t) = max_{u ∈ U} h_u(λ_t)` for almost all
  `t`: `theorem12_1`;
* the same conclusion in the generalized form of the proof of Theorem 12.4 (pp. 179–182, the
  scheme of (12.37)–(12.48)), with the transversality conditions `λ_{t₁} = Φ^* ξ` and
  `λ₀ ⊥ T N₀`: `exists_costate_of_boundary`. Every other version of the maximum principle in
  `OptimalControl/Pontryagin/` is derived from it by A–S's reductions.

## Readings and departures (listed in the README)

D1 open subset of `E` for the manifold `M`; D2 chronological calculus read pointwise
(`g_{τ,u}(q₁)` through the resolvent of the variational equation, `needleVector`; Proposition
11.3 as the adjoint equation, `ControlSystem.adjoint_stateTransition`); D3 `C¹` data; D4 `U`
compact; D8 Lemma 12.1 on a cone with one-sided derivative; D9 one separating covector for all
needle variations (finitely many generators suffice, `exists_finset_hull_eq_top`); D10 Brouwer's
theorem from the FixedPoint package (A–S give no reference); D11 Carathéodory theory
proved by Picard–Gronwall, with a cut-off near the reference trajectory. The hypothesis "boundary
of the attainable set" is weakened to "not an interior point of the image of the local attainable
set" (`localAttainableSet`), which is what the proof uses (it holds for every neighbourhood
`O₀` in Lemma 12.1); this strengthens the theorems.

Reading: `0 < t₁` in Lemma 12.2 and Theorem 12.1. A–S's literal Lemma 12.2 is false at
`t₁ = 0`: for `M = ℝ`, `U = [-1, 1]`, `f(q, u) = u` and `ũ ≡ 0`, the needle vectors
`g_{0,u}(q₀) = u` generate `ℝ`, but the attainable set at time `0` is `{q₀}`.

Gap in A–S (proof of Lemma 12.2, p. 171): a needle time `τᵢ = t₁` (a Lebesgue point of `[0, t₁]`)
gives no variation on `[0, t₁]`. Here every needle time is moved to a nearby Lebesgue point of
the open interval `(0, t₁)`, distinct from the others, by the perturbation argument that A–S use
for repeated times; positive generation survives small perturbations
(`exists_forall_hull_eq_top_of_dist_lt`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace Pontryagin

open ControlSystem

/-- **Agrachev–Sachkov, Lemma 12.1** (authors' draft, p. 168), as printed: let `F : ℝᵐ → ℝⁿ` be
Lipschitzian, `F(0) = 0`, differentiable at `0`, with `F'₀(ℝᵐ₊) = ℝⁿ`. Then for any neighbourhood
`O₀` of the origin, `0 ∈ int F(O₀ ∩ ℝᵐ₊)`.

Proof: the case `C = ℝᵐ₊` of `HasFDerivWithinAt.zero_mem_interior_image_inter_cone` (A–S's proof,
with Brouwer's fixed point theorem). -/
theorem lemma12_1 {m n : ℕ} {F : (Fin m → ℝ) → Fin n → ℝ} {F' : (Fin m → ℝ) →L[ℝ] Fin n → ℝ}
    (hlip : ∃ K, LipschitzWith K F) (h0 : F 0 = 0) (hF : HasFDerivAt F F' 0)
    (hsurj : F' '' {x | ∀ i, 0 ≤ x i} = univ) :
    ∀ O ∈ 𝓝 (0 : Fin m → ℝ), (0 : Fin n → ℝ) ∈ interior (F '' (O ∩ {x | ∀ i, 0 ≤ x i})) := by
  obtain ⟨K, hK⟩ := hlip
  refine hF.hasFDerivWithinAt.zero_mem_interior_image_inter_cone ?_ ?_ h0
    ⟨1, one_pos, K, hK.lipschitzOnWith⟩ hsurj
  · intro x hx y hy a b ha hb _ i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  · intro x hx c hc i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hc (hx i)

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {Ω : Set E} {U : Set V} {f : E → V → E} {t₁ : ℝ} {ũ : ℝ → V} {q : ℝ → E}

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- A map continuous on a closed set `K ⊆ E × V`, composed with an a.e. strongly measurable curve
with values in `K` almost everywhere, is a.e. strongly measurable (Tietze extension). -/
private lemma aestronglyMeasurable_comp_of_continuousOn {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W] {μ : Measure ℝ} {H : E × V → W}
    {K : Set (E × V)} (hK : IsClosed K) (hH : ContinuousOn H K) {g : ℝ → E × V}
    (hg : AEStronglyMeasurable g μ) (hgK : ∀ᵐ t ∂μ, g t ∈ K) :
    AEStronglyMeasurable (fun t ↦ H (g t)) μ := by
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hK ⟨K.domRestrict H, hH.domRestrict⟩
  refine (G.continuous.comp_aestronglyMeasurable hg).congr ?_
  filter_upwards [hgK] with t ht
  exact congrArg (fun F : C(K, W) ↦ F ⟨g t, ht⟩) hG

/-- Along an admissible pair in `Ω`, the linearization `∂ₓf(q(t), ũ(t))` is a.e. strongly
measurable and bounded on `[0, t₁]`. -/
private lemma linearization_bound (hU : IsCompact U) (hf : IsC1On f Ω U)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) :
    AEStronglyMeasurable (linearization f ũ q) (volume.restrict (Icc 0 t₁)) ∧
      ∃ K, ∀ t ∈ Icc 0 t₁, ‖linearization f ũ q t‖ ≤ K := by
  obtain ⟨⟨hũm, hũU, hqc, -, -⟩, hqΩ⟩ := href
  have hKc : IsCompact ((q '' Icc 0 t₁) ×ˢ U) :=
    (isCompact_Icc.image_of_continuousOn hqc).prod hU
  have hKΩ : (q '' Icc 0 t₁) ×ˢ U ⊆ Ω ×ˢ U := by
    rintro ⟨x, v⟩ ⟨⟨t, ht, rfl⟩, hv⟩
    exact ⟨hqΩ t ht, hv⟩
  have hH := hf.continuousOn_fderiv.mono hKΩ
  refine ⟨?_, ?_⟩
  · have hg : AEStronglyMeasurable (fun t ↦ (q t, ũ t)) (volume.restrict (Icc 0 t₁)) :=
      (hqc.aestronglyMeasurable measurableSet_Icc).prodMk hũm.aestronglyMeasurable
    refine aestronglyMeasurable_comp_of_continuousOn hKc.isClosed hH hg ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ⟨⟨t, ht, rfl⟩, hũU t ht⟩
  · obtain ⟨K, hK⟩ := hKc.exists_bound_of_continuousOn hH
    exact ⟨K, fun t ht ↦ hK (q t, ũ t) ⟨⟨t, ht, rfl⟩, hũU t ht⟩⟩

omit [FiniteDimensional ℝ E] in
/-- The reference control is integrable on `[0, t₁]` (measurable with values in a compact set). -/
private lemma integrableOn_control (hU : IsCompact U) (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) :
    IntegrableOn ũ (Icc 0 t₁) := by
  obtain ⟨R, hR⟩ := hU.isBounded.exists_norm_le
  refine Measure.integrableOn_of_bounded (M := R) (by simp) href.1.1.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hR _ (href.1.2.1 t ht)

/-- The costate of the proof of Theorem 12.1 (Agrachev–Sachkov, p. 172): if `λ_{t₁} ≠ 0` is
`≤ 0` on the needle vectors `g_{τ,u}(q₁)` at the Lebesgue points `τ` of `ũ` and `u ∈ U`, then
`λ_t = (P^{t₁}_t)^* λ_{t₁}`, read as `λ_{t₁} ∘ R(t, t₁)` (D2), is Lipschitz, nowhere zero, solves
the Hamiltonian system (Proposition 11.3, `ControlSystem.adjoint_stateTransition`) and satisfies
the maximality condition (the supporting inequality rewritten through (12.12)), since the
Lebesgue points have full measure. -/
private lemma costate_of_supporting (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) {ℓ : StrongDual ℝ E} (hℓ : ℓ ≠ 0)
    (hℓg : ∀ τ ∈ Icc 0 t₁, IsLebesguePointWithin ũ (Icc 0 t₁) τ → ∀ u ∈ U,
      ℓ (needleVector f ũ q t₁ τ u) ≤ 0) :
    (∃ K, LipschitzOnWith K (fun t ↦ ℓ.comp (stateTransition (linearization f ũ q) t t₁))
        (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, ℓ.comp (stateTransition (linearization f ũ q) t t₁) ≠ 0) ∧
      IsAdjoint f 0 0 ũ q t₁ (fun t ↦ ℓ.comp (stateTransition (linearization f ũ q) t t₁)) ∧
      IsMaximal f 0 0 U ũ q t₁ (fun t ↦ ℓ.comp (stateTransition (linearization f ũ q) t t₁)) := by
  set R := stateTransition (linearization f ũ q)
  obtain ⟨hAm, K, hK⟩ := linearization_bound hU hf href
  have ht₁I : t₁ ∈ Icc 0 t₁ := ⟨ht₁.le, le_rfl⟩
  obtain ⟨hlip, hint, hadj, hnz⟩ := adjoint_stateTransition hAm hK ht₁I ℓ
  have hpt₁ : ℓ.comp (R t₁ t₁) = ℓ := by
    simp only [R, stateTransition_self, ContinuousLinearMap.comp_id]
  refine ⟨hlip, hnz hℓ, ⟨?_, fun t ht ↦ ?_⟩, ?_⟩
  · simpa using hint
  · simpa [hpt₁] using hadj t ht
  · filter_upwards [ae_isLebesguePointWithin (integrableOn_control hU href),
      ae_restrict_mem measurableSet_Icc] with τ hleb hτ u hu
    have := hℓg τ hτ hleb u hu
    simp only [needleVector, map_sub] at this
    simp only [controlHamiltonian, Pi.zero_apply, mul_zero, add_zero,
      ContinuousLinearMap.comp_apply, R]
    linarith

/-- The flow depends only on the control between the two times. -/
private lemma flow_congr_control {E' V' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {h : E' → V' → E'} {u u' : ℝ → V'} {s t : ℝ} (hu : EqOn u u' [[s, t]]) (x : E') :
    flow h u s t x = flow h u' s t x := by
  have key : IsSolution h u s x s t = IsSolution h u' s x s t := by
    funext y
    have hEq : EqOn (fun r ↦ h (y r) (u r)) (fun r ↦ h (y r) (u' r)) [[s, t]] :=
      fun r hr ↦ by simp only [hu hr]
    have hEq' : EqOn (fun r ↦ h (y r) (u r)) (fun r ↦ h (y r) (u' r)) (Ι s t) :=
      hEq.mono uIoc_subset_uIcc
    apply propext
    simp only [IsSolution]
    refine and_congr Iff.rfl (and_congr ⟨fun hi ↦ hi.congr hEq', fun hi ↦ hi.congr hEq'.symm⟩
      (forall₂_congr fun r hr ↦ ?_))
    rw [intervalIntegral.integral_congr (hEq.mono (uIcc_subset_uIcc_left hr))]
  unfold flow
  rw [key]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A needle control of a measurable control is measurable. -/
private lemma measurable_needleControl (hũ : Measurable ũ) {k : ℕ} (τ : Fin k → ℝ)
    (w : Fin k → V) (σ : Fin k → ℝ) : Measurable (needleControl ũ τ w σ) := by
  classical
  intro B hB
  set I : Fin k → Set ℝ := fun i ↦ Ico (τ i) (τ i + σ i) with hI
  have : needleControl ũ τ w σ ⁻¹' B =
      (⋃ i ∈ {i | w i ∈ B}, (I i \ ⋃ j ∈ {j | j < i}, I j)) ∪ ((⋃ j, I j)ᶜ ∩ ũ ⁻¹' B) := by
    ext t
    simp only [needleControl, mem_preimage, mem_union, mem_iUnion, mem_ofPred_eq, mem_inter_iff,
      mem_compl_iff, Set.mem_sdiff, exists_prop, not_exists, not_and, hI]
    split_ifs with h
    · constructor
      · intro hB'
        exact Or.inl ⟨_, hB', Fin.find_spec h, fun j hj ↦ Fin.find_min h hj⟩
      · rintro (⟨i, hi, hti, hj⟩ | ⟨h', -⟩)
        · rwa [(Fin.find_eq_iff h).2 ⟨hti, fun j hji ↦ hj j hji⟩]
        · exact absurd h (fun ⟨j, hj⟩ ↦ h' j hj)
    · constructor
      · intro hB'
        exact Or.inr ⟨fun j hj ↦ h ⟨j, hj⟩, hB'⟩
      · rintro (⟨i, -, hti, -⟩ | ⟨-, hB'⟩)
        · exact absurd ⟨i, hti⟩ h
        · exact hB'
  rw [this]
  refine (MeasurableSet.biUnion (to_countable _) fun i _ ↦ ?_).union
    ((MeasurableSet.iUnion fun j ↦ measurableSet_Ico).compl.inter (hũ hB))
  exact measurableSet_Ico.diff (MeasurableSet.biUnion (to_countable _) fun j _ ↦ measurableSet_Ico)

/-- Distinct representatives: if each `C i` meets the complement of every finite set, one can
choose `τ i ∈ C i` pairwise distinct. -/
private lemma exists_injective_forall_mem {k : ℕ} (C : Fin k → Set ℝ)
    (hC : ∀ i (S : Finset ℝ), ∃ x ∈ C i, x ∉ S) :
    ∃ τ : Fin k → ℝ, Function.Injective τ ∧ ∀ i, τ i ∈ C i := by
  classical
  induction k with
  | zero => exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ k ih =>
    obtain ⟨τ, hτinj, hτC⟩ := ih (fun i ↦ C i.castSucc) (fun i S ↦ hC _ S)
    obtain ⟨x, hxC, hxS⟩ := hC (Fin.last k) (Finset.univ.image τ)
    refine ⟨Fin.snoc (α := fun _ ↦ ℝ) τ x, Fin.snoc_injective_of_injective hτinj ?_, fun i ↦ ?_⟩
    · rintro ⟨j, rfl⟩
      exact hxS (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    · induction i using Fin.lastCases with
      | last => simpa using hxC
      | cast j => simpa using hτC j

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {ψ : P → E} {a₀ : P}
  {Φ : E → Q}

/-- **Lemma 12.2 in the generalized form of the proof of Theorem 12.4** (Agrachev–Sachkov,
pp. 179–182): initial points `ψ(a)` (a `C¹` parametrization of `N₀` near `q(0)`), the end point
composed with a `C¹` map `Φ` (the submersion defining `N₁`), and competitors near the reference.
If the convex cone generated by the vectors `Φ'(R(0, t₁) ψ'(a₀) α)` (variations of the initial
point, A–S's `∂F/∂q`, (2.19)) and `Φ'(g_{τ,u}(q₁))` (needle variations at Lebesgue points `τ`,
`u ∈ U`) is the whole space, then for every `ε > 0`, `Φ(q₁)` is an interior point of the image
under `Φ` of the local attainable set.

Proof (A–S's proof of Lemma 12.2, with the changes of the proof of Theorem 12.4 (2)): by
`exists_finset_hull_eq_top`, finitely many of the vectors generate (D9); move the needle times to
distinct Lebesgue points of `(0, t₁)` keeping the generation
(`IsLebesguePointWithin.exists_near`, the continuity of `τ ↦ g_{τ,u}(q₁)` at Lebesgue points
along points where `ũ` is close to `ũ(τ)`, and `exists_forall_hull_eq_top_of_dist_lt`); cut the
system off near `q` (`IsC1On.exists_cutoff`, D11), so that the needle end-point map
`F(a, σ) = Φ(P^{u_σ}_{0 → t₁}(ψ(a)))` is Lipschitz and differentiable at `(a₀, 0)` within
`P × ℝᵏ₊` with the derivative `(α, σ) ↦ Φ'(R(0, t₁)ψ'(a₀)α + Σ σᵢ g_{τᵢ,uᵢ}(q₁))`
(`ControlSystem.lipschitzOnWith_needle`, `ControlSystem.hasFDerivWithinAt_needle`,
`ControlSystem.hasFDerivAt_flow`, `ControlSystem.fderiv_flow_eq_stateTransition`; the cut-off
system has the same linearization along `q`), its trajectories are near `q`
(`ControlSystem.norm_needle_trajectory_sub_lt`) and hence admissible for `f` in `Ω`; the
derivative maps `P × ℝᵏ₊` onto the cone generated by the (perturbed) generators, that is onto
everything; conclude with Lemma 12.1 on the cone `P × ℝᵏ₊`
(`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`). -/
theorem lemma12_2_local (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) (hψ : ContDiffAt ℝ 1 ψ a₀) (hψ0 : ψ a₀ = q 0)
    (hΦ : ContDiffAt ℝ 1 Φ (q t₁))
    (hcone : PointedCone.hull ℝ
      (range (fun α : P ↦
          fderiv ℝ Φ (q t₁) (stateTransition (linearization f ũ q) 0 t₁ (fderiv ℝ ψ a₀ α))) ∪
        (fun p : ℝ × V ↦ fderiv ℝ Φ (q t₁) (needleVector f ũ q t₁ p.1 p.2)) ''
          ({τ | τ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ} ×ˢ U)) = ⊤) :
    ∀ ε > 0, Φ (q t₁) ∈ interior (Φ '' localAttainableSet f Ω U ψ a₀ q t₁ ε) := by
  classical
  intro ε hε
  set Φ' := fderiv ℝ Φ (q t₁) with hΦ'
  set R := stateTransition (linearization f ũ q) with hR
  set Lin : Set Q := range (fun α : P ↦ Φ' (R 0 t₁ (fderiv ℝ ψ a₀ α))) with hLin
  have hũc : IsControlOn ũ U 0 t₁ := ⟨href.1.1.aestronglyMeasurable, href.1.2.1⟩
  have hũint := integrableOn_control hU href
  have hqc : ContinuousOn q (Icc 0 t₁) := href.1.2.2.1
  have ht₁I : t₁ ∈ Icc 0 t₁ := ⟨ht₁.le, le_rfl⟩
  have h0I : (0 : ℝ) ∈ Icc 0 t₁ := ⟨le_rfl, ht₁.le⟩
  obtain ⟨hAm, KA, hKA⟩ := linearization_bound hU hf href
  /- Step 1 (A–S: "We can choose vectors `g_{τᵢ,uᵢ}(q₁)` … that generate the whole tangent
  space as a positive convex cone"): finitely many of the vectors generate (D9). -/
  obtain ⟨s, hsS, hs⟩ := exists_finset_hull_eq_top hcone
  set sN := s.filter (· ∉ Lin) with hsN
  let e : Fin sN.card ≃ sN := sN.equivFin.symm
  have hNdl : ∀ i : Fin sN.card, ∃ τ₀ w, (τ₀ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ₀) ∧
      w ∈ U ∧ Φ' (needleVector f ũ q t₁ τ₀ w) = (e i : Q) := by
    intro i
    have h1 : (e i : Q) ∈ s ∧ (e i : Q) ∉ Lin := Finset.mem_filter.1 (e i).2
    rcases hsS h1.1 with h | ⟨⟨τ₀, w⟩, ⟨hτ₀, hw⟩, heq⟩
    · exact absurd h h1.2
    · exact ⟨τ₀, w, hτ₀, hw, heq⟩
  choose τ₀ w hτ₀ hw hτ₀w using hNdl
  -- the generators survive small perturbations
  let v : Fin s.card → Q := fun j ↦ (s.equivFin.symm j : Q)
  have hv : PointedCone.hull ℝ (range v) = ⊤ := by
    have : range v = (s : Set Q) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact (s.equivFin.symm j).2
      · intro hx
        exact ⟨s.equivFin ⟨x, hx⟩, by simp [v]⟩
    rw [this, hs]
  obtain ⟨η, hη, hηv⟩ := exists_forall_hull_eq_top_of_dist_lt hv
  /- Step 2 (A–S, p. 171): the needle times can be taken distinct, at Lebesgue points close to the
  given ones, keeping the needle vectors close. -/
  have hnear : ∀ τ₁ : ℝ, (τ₁ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ₁) →
      ∀ w₁ ∈ U, ∀ S : Finset ℝ, ∃ t ∈ {t | t ∈ Ioo 0 t₁ ∧
        IsLebesguePointWithin ũ (Icc 0 t₁) t ∧
        ‖Φ' (needleVector f ũ q t₁ t w₁) - Φ' (needleVector f ũ q t₁ τ₁ w₁)‖ < η}, t ∉ S := by
    intro τ₁ hτ₁ w₁ hw₁ S
    obtain ⟨-, CR, hCR⟩ := lipschitzOnWith_stateTransition hAm hKA ht₁I
    have hτ₁I := hτ₁.1
    have hfst : ContinuousWithinAt (fun p : ℝ × V ↦ p.1) (Icc 0 t₁ ×ˢ U) (τ₁, ũ τ₁) :=
      continuousWithinAt_fst
    have hfstm : MapsTo (fun p : ℝ × V ↦ p.1) (Icc 0 t₁ ×ˢ U) (Icc 0 t₁) :=
      fun p hp ↦ (mem_prod.1 hp).1
    have h1 : ContinuousWithinAt (fun p : ℝ × V ↦ R p.1 t₁) (Icc 0 t₁ ×ˢ U) (τ₁, ũ τ₁) :=
      ContinuousWithinAt.comp (g := fun t ↦ R t t₁) (hCR.continuousOn τ₁ hτ₁I) hfst hfstm
    have hq1 : ContinuousWithinAt (fun p : ℝ × V ↦ q p.1) (Icc 0 t₁ ×ˢ U) (τ₁, ũ τ₁) :=
      ContinuousWithinAt.comp (g := q) (hqc τ₁ hτ₁I) hfst hfstm
    have h2 : ContinuousWithinAt (fun p : ℝ × V ↦ f (q p.1) w₁) (Icc 0 t₁ ×ˢ U) (τ₁, ũ τ₁) :=
      ContinuousWithinAt.comp (t := Ω ×ˢ U) (g := fun z : E × V ↦ f z.1 z.2)
        (f := fun p : ℝ × V ↦ (q p.1, w₁))
        (hf.continuousOn (q τ₁, w₁) ⟨href.2 τ₁ hτ₁I, hw₁⟩) (hq1.prodMk continuousWithinAt_const)
        (fun p hp ↦ ⟨href.2 _ (mem_prod.1 hp).1, hw₁⟩)
    have h3 : ContinuousWithinAt (fun p : ℝ × V ↦ f (q p.1) p.2) (Icc 0 t₁ ×ˢ U) (τ₁, ũ τ₁) :=
      ContinuousWithinAt.comp (t := Ω ×ˢ U) (g := fun z : E × V ↦ f z.1 z.2)
        (f := fun p : ℝ × V ↦ (q p.1, p.2))
        (hf.continuousOn (q τ₁, ũ τ₁) ⟨href.2 τ₁ hτ₁I, href.1.2.1 τ₁ hτ₁I⟩)
        (hq1.prodMk continuousWithinAt_snd)
        (fun p hp ↦ ⟨href.2 _ (mem_prod.1 hp).1, (mem_prod.1 hp).2⟩)
    have hΓ : ContinuousWithinAt (fun p : ℝ × V ↦ Φ' (R p.1 t₁ (f (q p.1) w₁ - f (q p.1) p.2)))
        (Icc 0 t₁ ×ˢ U) (τ₁, ũ τ₁) :=
      Φ'.continuous.continuousAt.comp_continuousWithinAt (h1.clm_apply (h2.sub h3))
    obtain ⟨θ, hθ, hθΓ⟩ := Metric.continuousWithinAt_iff.1 hΓ η hη
    obtain ⟨t, htG, htI, htS, ht1, ht2⟩ :=
      hτ₁.2.exists_near (G := {t | IsLebesguePointWithin ũ (Icc 0 t₁) t}) hũint ht₁ hτ₁I
        (ae_isLebesguePointWithin hũint) S hθ
    refine ⟨t, ⟨htI, htG, ?_⟩, htS⟩
    have := hθΓ (x := (t, ũ t)) ⟨Ioo_subset_Icc_self htI, href.1.2.1 t (Ioo_subset_Icc_self htI)⟩
      (by rw [Prod.dist_eq]; exact max_lt (by rwa [Real.dist_eq]) (by rwa [dist_eq_norm]))
    rw [dist_eq_norm] at this
    simpa [needleVector, R] using this
  obtain ⟨τ, hτinj, hτC⟩ := exists_injective_forall_mem _ fun i S ↦ hnear _ (hτ₀ i) _ (hw i) S
  set gN : Fin sN.card → Q := fun i ↦ Φ' (needleVector f ũ q t₁ (τ i) (w i)) with hgN
  have hgen : PointedCone.hull ℝ (Lin ∪ range gN) = ⊤ := by
    let v' : Fin s.card → Q := fun j ↦ if h : v j ∈ sN then gN (e.symm ⟨v j, h⟩) else v j
    have hv' : ∀ j, ‖v' j - v j‖ < η := by
      intro j
      by_cases h : v j ∈ sN
      · have hej : (e (e.symm ⟨v j, h⟩) : Q) = v j := by simp
        have := (hτC (e.symm ⟨v j, h⟩)).2.2
        rw [hτ₀w, hej] at this
        simpa [v', h] using this
      · simpa [v', h] using hη
    rw [eq_top_iff, ← hηv v' hv']
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    by_cases h : v j ∈ sN
    · simp only [v', h, dite_true]
      exact Or.inr ⟨_, rfl⟩
    · simp only [v', h, dite_false]
      have hjs : v j ∈ s := (s.equivFin.symm j).2
      left
      by_contra hL
      exact h (Finset.mem_filter.2 ⟨hjs, hL⟩)
  /- Step 3: cut-off near the reference trajectory (D11), so that the needle variations are
  defined by the flows of a globally bounded `C¹` system. -/
  have hK₀ : IsCompact (q '' Icc 0 t₁) := isCompact_Icc.image_of_continuousOn hqc
  have hK₀Ω : q '' Icc 0 t₁ ⊆ Ω := by
    rintro _ ⟨t, ht, rfl⟩
    exact href.2 t ht
  obtain ⟨δ, hδ, hδΩ, g, M, Lg, hg, hgf⟩ := hf.exists_cutoff hΩ hU hK₀ hK₀Ω
  have hgL := hg.isLipschitzSystem
  have hball : ∀ t ∈ Icc 0 t₁, ball (q t) δ ⊆ cthickening δ (q '' Icc 0 t₁) := fun t ht ↦
    (ball_subset_thickening (mem_image_of_mem q ht) δ).trans (thickening_subset_cthickening _ _)
  have hqK : ∀ t ∈ Icc 0 t₁, q t ∈ cthickening δ (q '' Icc 0 t₁) := fun t ht ↦
    self_subset_cthickening _ (mem_image_of_mem q ht)
  have hqflow : ∀ t ∈ Icc 0 t₁, flow g ũ 0 t (q 0) = q t := by
    have hEq : EqOn (fun r ↦ g (q r) (ũ r)) (fun r ↦ f (q r) (ũ r)) (Icc 0 t₁) := fun r hr ↦
      hgf _ (hqK r hr) _ (href.1.2.1 r hr)
    have hsol : IsSolution g ũ 0 (q 0) 0 t₁ q := by
      rw [IsSolution, uIcc_of_le ht₁.le]
      refine ⟨hqc, href.1.2.2.2.1.congr ((hEq.mono ?_).symm), fun t ht ↦ ?_⟩
      · rw [uIoc_of_le ht₁.le]
        exact Ioc_subset_Icc_self
      · rw [href.1.2.2.2.2 t ht, intervalIntegral.integral_congr (hEq.symm.mono ?_)]
        rw [uIcc_of_le ht.1]
        exact Icc_subset_Icc_right ht.2
    exact fun t ht ↦ hsol.flow_eq hgL hũc h0I ht
  -- the linearizations of `f` and of the cut-off system agree along the reference
  have hAeq : ∀ s₀ ∈ Icc 0 t₁,
      stateTransition (fun r ↦ fderiv ℝ (g · (ũ r)) (flow g ũ 0 r (q 0))) s₀ t₁ = R s₀ t₁ := by
    intro s₀ hs₀
    refine flow_congr_control (fun r hr ↦ ?_) _
    have hr' : r ∈ Icc 0 t₁ := uIcc_subset_Icc hs₀ ht₁I hr
    simp only [linearization]
    rw [hqflow r hr']
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [ball_mem_nhds (q r) hδ] with x hx
    exact hgf x (hball r hr' hx) _ (href.1.2.1 r hr')
  have hvf : ∀ τ' ∈ Icc 0 t₁, ∀ w' ∈ U,
      variationField g ũ t₁ τ' w' (q t₁) = needleVector f ũ q t₁ τ' w' := by
    intro τ' hτ' w' hw'
    have hback : flow g ũ t₁ τ' (q t₁) = q τ' := by
      rw [← hqflow t₁ ht₁I, flow_flow hgL hũc h0I ht₁I hτ', hqflow τ' hτ']
    have hD : fderiv ℝ (flow g ũ τ' t₁) (q τ') = R τ' t₁ := by
      have := fderiv_flow_eq_stateTransition hg hũc h0I ht₁I (q 0) hτ'
      rw [hqflow τ' hτ'] at this
      rw [this, hAeq τ' hτ']
    simp only [variationField, needleVector, hback, hD, hgf _ (hqK τ' hτ') w' hw',
      hgf _ (hqK τ' hτ') _ (href.1.2.1 τ' hτ')]
    rfl
  /- Step 4: the needle-like variations (12.14) and the end-point map `F(a, σ)`, Lipschitz and
  differentiable at `(a₀, 0)` within the cone `P × ℝᵏ₊`. -/
  have hτI : ∀ i, τ i ∈ Ico 0 t₁ := fun i ↦ ⟨(hτC i).1.1.le, (hτC i).1.2⟩
  have hleb : ∀ i, IsLebesguePointWithin ũ (Icc 0 t₁) (τ i) := fun i ↦ (hτC i).2.1
  set N : P × (Fin sN.card → ℝ) → E := fun p ↦ flow g (needleControl ũ τ w p.2) 0 t₁ (ψ p.1)
    with hNdef
  have hN0 : N (a₀, 0) = q t₁ := by simp [hNdef, needleControl_zero, hψ0, hqflow t₁ ht₁I]
  set D : P × (Fin sN.card → ℝ) →L[ℝ] E :=
    (fderiv ℝ (flow g ũ 0 t₁) (ψ a₀)).comp
        ((fderiv ℝ ψ a₀).comp (ContinuousLinearMap.fst ℝ P (Fin sN.card → ℝ))) +
      ∑ i, ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ P (Fin sN.card → ℝ))).smulRight
          (variationField g ũ t₁ (τ i) (w i) (flow g ũ 0 t₁ (ψ a₀))) with hDdef
  have hND : HasFDerivWithinAt N D (univ ×ˢ orthant sN.card) (a₀, 0) :=
    hasFDerivWithinAt_needle hg ht₁ hũc hw hτI hτinj hleb hψ
  have hflowD : fderiv ℝ (flow g ũ 0 t₁) (ψ a₀) = R 0 t₁ := by
    rw [hψ0, (hasFDerivAt_flow hg hũc h0I ht₁I (q 0)).fderiv, hAeq 0 h0I]
  have hDapply : ∀ α σ, D (α, σ) = R 0 t₁ (fderiv ℝ ψ a₀ α) +
      ∑ i, σ i • needleVector f ũ q t₁ (τ i) (w i) := by
    intro α σ
    rw [hDdef, add_apply, sum_apply, hflowD, hψ0,
      hqflow t₁ ht₁I]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ContinuousLinearMap.smulRight_apply, hvf _ (Ico_subset_Icc_self (hτI i)) _ (hw i)]
    rfl
  -- composed with `Φ` (A–S's `F = Φ̂ ∘ G`, (12.39)), and moved to the origin
  have hΦd : HasFDerivAt Φ Φ' (N (a₀, 0)) := by
    rw [hN0]
    exact (hΦ.differentiableAt (by norm_num)).hasFDerivAt
  have hΦN : HasFDerivWithinAt (Φ ∘ N) (Φ'.comp D) (univ ×ˢ orthant sN.card) (a₀, 0) :=
    hΦd.comp_hasFDerivWithinAt (a₀, 0) hND
  set C : Set (P × (Fin sN.card → ℝ)) := univ ×ˢ orthant sN.card with hCdef
  set c₀ : P × (Fin sN.card → ℝ) := (a₀, 0) with hc₀
  set Fm : P × (Fin sN.card → ℝ) → Q := fun p ↦ Φ (N (c₀ + p)) - Φ (q t₁) with hFmdef
  have hCtrans : ∀ p ∈ C, c₀ + p ∈ C := fun p hp ↦ ⟨trivial, by simpa [c₀] using hp.2⟩
  have hCcone : ∀ x ∈ C, ∀ c : ℝ, 0 ≤ c → c • x ∈ C := fun x hx c hc ↦
    ⟨trivial, fun i ↦ by simpa using mul_nonneg hc (hx.2 i)⟩
  have hCconv : Convex ℝ C := by
    refine convex_univ.prod fun x hx y hy a b ha hb _ i ↦ ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  have hFm : HasFDerivWithinAt Fm (Φ'.comp D) C 0 := by
    have h1 : HasFDerivWithinAt (fun p ↦ c₀ + p) (ContinuousLinearMap.id ℝ _) C 0 :=
      ((hasFDerivAt_id (0 : P × (Fin sN.card → ℝ))).const_add c₀).hasFDerivWithinAt
    have h3 : HasFDerivWithinAt (Φ ∘ N) (Φ'.comp D) C (c₀ + 0) := by
      rw [add_zero]
      exact hΦN
    have := (h3.comp (0 : P × (Fin sN.card → ℝ)) h1 hCtrans).sub_const (Φ (q t₁))
    simpa [hFmdef] using this
  have hFm0 : Fm 0 = 0 := by
    change Φ (N (c₀ + 0)) - Φ (q t₁) = 0
    rw [add_zero, hc₀, hN0, sub_self]
  -- `F` is Lipschitz near `0` on the cone
  have hlipFm : ∃ ρ > 0, ∃ K, LipschitzOnWith K Fm (C ∩ ball 0 ρ) := by
    obtain ⟨ρ₁, hρ₁, KN, hKN⟩ := lipschitzOnWith_needle (τ := τ) hg ht₁ hũc hw hψ
    obtain ⟨KΦ, T, hT, hKΦ⟩ := hΦ.exists_lipschitzOnWith
    obtain ⟨r₁, hr₁, hr₁T⟩ := Metric.mem_nhds_iff.1 hT
    obtain ⟨ρ₂, hρ₂, hρ₂N⟩ := norm_needle_trajectory_sub_lt (τ := τ) hg ht₁ hũc hw
      hψ.continuousAt hr₁
    refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, KΦ * KN, LipschitzOnWith.of_dist_le_mul ?_⟩
    have hmem : ∀ p ∈ C ∩ ball 0 (min ρ₁ ρ₂), c₀ + p ∈ C ∩ ball c₀ ρ₁ ∧
        c₀ + p ∈ C ∩ ball c₀ ρ₂ ∧ N (c₀ + p) ∈ T := by
      intro p hp
      have hd : dist (c₀ + p) c₀ = ‖p‖ := by rw [dist_eq_norm, add_sub_cancel_left]
      have h1 : c₀ + p ∈ C ∩ ball c₀ ρ₁ := ⟨hCtrans p hp.1, by
        rw [mem_ball, hd]; exact (mem_ball_zero_iff.1 hp.2).trans_le (min_le_left _ _)⟩
      have h2 : c₀ + p ∈ C ∩ ball c₀ ρ₂ := ⟨hCtrans p hp.1, by
        rw [mem_ball, hd]; exact (mem_ball_zero_iff.1 hp.2).trans_le (min_le_right _ _)⟩
      refine ⟨h1, h2, hr₁T ?_⟩
      have := hρ₂N _ h2 t₁ ht₁I
      rw [hψ0, hqflow t₁ ht₁I] at this
      rw [mem_ball, dist_eq_norm]
      exact this
    intro p hp p' hp'
    obtain ⟨h1, -, h3⟩ := hmem p hp
    obtain ⟨h1', -, h3'⟩ := hmem p' hp'
    calc dist (Fm p) (Fm p') = dist (Φ (N (c₀ + p))) (Φ (N (c₀ + p'))) := by
          simp only [hFmdef, dist_sub_right]
      _ ≤ KΦ * dist (N (c₀ + p)) (N (c₀ + p')) := hKΦ.dist_le_mul _ h3 _ h3'
      _ ≤ KΦ * (KN * dist (c₀ + p) (c₀ + p')) :=
          mul_le_mul_of_nonneg_left (hKN.dist_le_mul _ h1 _ h1') (by positivity)
      _ = ↑(KΦ * KN) * dist p p' := by rw [dist_add_left]; push_cast; ring
  -- its derivative maps the cone onto the whole space (A–S: `F'₀(ℝᵏ₊) = ℝⁿ`)
  have hsurj : (Φ'.comp D) '' C = univ := by
    refine eq_univ_of_forall fun y ↦ ?_
    have hy : y ∈ PointedCone.hull ℝ (Lin ∪ range gN) := by rw [hgen]; trivial
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨α, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨(α, 0), ⟨trivial, fun _ ↦ le_rfl⟩, by simp [hDapply]⟩
      · refine ⟨(0, Pi.single i 1), ⟨trivial, fun j ↦ ?_⟩, ?_⟩
        · by_cases hij : j = i
          · subst hij; simp
          · simp [hij]
        · simp [hDapply, hgN, Pi.single_apply]
    | zero => exact ⟨0, ⟨trivial, fun _ ↦ le_rfl⟩, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨p', hp', rfl⟩ := hy
      exact ⟨p + p', ⟨trivial, fun i ↦ add_nonneg (hp.2 i) (hp'.2 i)⟩, map_add _ _ _⟩
    | smul c x _ hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      exact ⟨(c : ℝ) • p, hCcone p hp c c.2, by rw [map_smul, Nonneg.coe_smul]⟩
  /- Step 5: Lemma 12.1 on the cone `P × ℝᵏ₊` (Remark (1)); the varied trajectories are
  admissible for the original system and near the reference. -/
  have hint := HasFDerivWithinAt.zero_mem_interior_image_inter_cone hFm hCconv hCcone hFm0
    hlipFm hsurj
  obtain ⟨ρ₃, hρ₃, hρ₃N⟩ := norm_needle_trajectory_sub_lt (τ := τ) hg ht₁ hũc hw
    hψ.continuousAt (lt_min hε hδ)
  have h1 := hint _ (ball_mem_nhds (0 : P × (Fin sN.card → ℝ)) (lt_min hε hρ₃))
  have hsub : Fm '' (ball 0 (min ε ρ₃) ∩ C) ⊆
      (fun z ↦ z + Φ (q t₁)) ⁻¹' (Φ '' localAttainableSet f Ω U ψ a₀ q t₁ ε) := by
    rintro _ ⟨p, ⟨hpO, hpC⟩, rfl⟩
    simp only [mem_preimage, hFmdef, sub_add_cancel]
    refine ⟨N (c₀ + p), ?_, rfl⟩
    set a := a₀ + p.1 with ha
    set u := needleControl ũ τ w p.2 with hu
    have hcp : c₀ + p = (a, p.2) := by ext <;> simp [hc₀, ha]
    have hpn : ‖p‖ < min ε ρ₃ := mem_ball_zero_iff.1 hpO
    have hpball : c₀ + p ∈ C ∩ ball c₀ ρ₃ := ⟨hCtrans p hpC, by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact hpn.trans_le (min_le_right _ _)⟩
    have hclose : ∀ t ∈ Icc 0 t₁, ‖flow g u 0 t (ψ a) - q t‖ < min ε δ := by
      intro t ht
      have := hρ₃N _ hpball t ht
      rwa [hcp, hψ0, hqflow t ht] at this
    have huc : IsControlOn u U 0 t₁ := isControlOn_needleControl hũc hw p.2
    have hsol := isSolution_flow hgL huc h0I (ψ a)
    rw [IsSolution, uIcc_of_le ht₁.le] at hsol
    have hxK : ∀ t ∈ Icc 0 t₁, flow g u 0 t (ψ a) ∈ cthickening δ (q '' Icc 0 t₁) :=
      fun t ht ↦ hball t ht (by
        rw [mem_ball, dist_eq_norm]; exact (hclose t ht).trans_le (min_le_right _ _))
    have hEq : EqOn (fun r ↦ g (flow g u 0 r (ψ a)) (u r)) (fun r ↦ f (flow g u 0 r (ψ a)) (u r))
        (Icc 0 t₁) := fun r hr ↦ hgf _ (hxK r hr) _ (huc.mem r hr)
    refine ⟨a, u, fun t ↦ flow g u 0 t (ψ a), ?_, ⟨⟨measurable_needleControl href.1.1 τ w p.2,
      huc.mem, hsol.1, hsol.2.1.congr (hEq.mono ?_), fun t ht ↦ ?_⟩,
      fun t ht ↦ hδΩ (hxK t ht)⟩, fun t ht ↦ (hclose t ht).trans_le (min_le_left _ _), ?_⟩
    · rw [ha, add_sub_cancel_left]
      exact (norm_fst_le p).trans_lt (hpn.trans_le (min_le_left _ _))
    · rw [uIoc_of_le ht₁.le]
      exact Ioc_subset_Icc_self
    · beta_reduce
      rw [hsol.2.2 t ht, intervalIntegral.integral_congr (hEq.mono ?_)]
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc_right ht.2
    · change flow g u 0 t₁ (ψ a) = N (c₀ + p)
      rw [hcp]
  have h2 : (fun z ↦ z + Φ (q t₁)) ⁻¹' (Φ '' localAttainableSet f Ω U ψ a₀ q t₁ ε) ∈ 𝓝 0 :=
    mem_interior_iff_mem_nhds.1 (interior_mono hsub h1)
  rw [mem_interior_iff_mem_nhds]
  have hc : ContinuousAt (fun z : Q ↦ z - Φ (q t₁)) (Φ (q t₁)) :=
    (continuous_sub_right _).continuousAt
  have := hc.preimage_mem_nhds (by rw [sub_self]; exact h2)
  rw [preimage_preimage] at this
  simpa only [sub_add_cancel, preimage_id'] using this

/-- **Agrachev–Sachkov, Lemma 12.2** (authors' draft, p. 170): let `T ⊆ [0, t₁]` be the set of
Lebesgue points of the reference control `ũ`; if
`T_{q₁}M = cone{g_{τ,u}(q₁) | τ ∈ T, u ∈ U}`, then `q₁ ∈ int A_{q₀}(t₁)`. Here `q₁ = q(t₁)`
is the end point of the reference trajectory `q` (A–S's `q̃`) from `q₀ = q(0)`, and
`g_{τ,u}(q₁)` is `needleVector f ũ q t₁ τ u` (12.12).

Reading: `0 < t₁` (A–S's literal statement is false at `t₁ = 0`, see the module docstring).

Proof: the case `ψ` constant, `Φ = id` of `lemma12_2_local` (A–S's proof). -/
theorem lemma12_2 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hcone : PointedCone.hull ℝ ((fun p : ℝ × V ↦ needleVector f ũ q t₁ p.1 p.2) ''
      ({τ | τ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ} ×ˢ U)) = ⊤) :
    q t₁ ∈ interior (attainableSet f Ω U (q 0) t₁) := by
  have hcone' : PointedCone.hull ℝ
      (range (fun α : ℝ ↦ fderiv ℝ id (q t₁) (stateTransition (linearization f ũ q) 0 t₁
          (fderiv ℝ (fun _ : ℝ ↦ q 0) 0 α))) ∪
        (fun p : ℝ × V ↦ fderiv ℝ id (q t₁) (needleVector f ũ q t₁ p.1 p.2)) ''
          ({τ | τ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ} ×ˢ U)) = ⊤ := by
    rw [eq_top_iff, ← hcone]
    refine Submodule.span_mono fun x hx ↦ Or.inr ?_
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, hp, by simp⟩
  have h := lemma12_2_local (ψ := fun _ : ℝ ↦ q 0) (a₀ := 0) (Φ := id) hΩ hU hf ht₁ href
    contDiffAt_const rfl contDiffAt_id hcone' 1 one_pos
  rw [image_id] at h
  refine interior_mono ?_ h
  rintro y ⟨a, u, x, -, hx, -, rfl⟩
  exact ⟨u, x, hx, rfl⟩

/-- **The geometric maximum principle in the generalized form of the proof of Theorem 12.4**
(Agrachev–Sachkov, pp. 179–182; Theorem 12.1, p. 164, is the case `ψ` constant, `Φ = id`).
Let `(ũ, q)` be an admissible pair in `Ω` on `[0, t₁]`, `ψ` a `C¹` map with `ψ(a₀) = q(0)` and
`Φ` a `C¹` map with surjective derivative at `q(t₁)`. If for some `ε > 0`, `Φ(q(t₁))` is not an
interior point of the image under `Φ` of the local attainable set ((12.37), (12.45)), then there
are `ξ ≠ 0` and a Lipschitz covector curve `p` (A–S's `λ_t`) with `p(t₁) = ξ ∘ Φ'(q(t₁))`
((12.44)), `p(t) ≠ 0` for all `t`, the adjoint equation (12.4), the maximality condition (12.5)
for almost every `t`, and `p(0) ∘ ψ'(a₀) = 0` (`λ₀ ⊥ T_{q̃(0)}N₀`, (12.47)–(12.48)).

Proof (A–S): by `lemma12_2_local`, the cone of the vectors `Φ'(R(0, t₁)ψ'(a₀)α)` and
`Φ'(g_{τ,u}(q₁))` is not the whole space; a supporting covector `ξ ≠ 0`
(`exists_dual_ne_zero_nonpos_of_ne_top`) is `≤ 0` on it, hence `= 0` on the linear part.
Put `p(t) = ξ ∘ Φ' ∘ R(t, t₁)` (A–S's `λ_t = (P^{t₁}_t)^* λ_{t₁}`); Proposition 11.3, read
pointwise, is `ControlSystem.adjoint_stateTransition`, which also gives Lipschitz continuity and
`p(t) ≠ 0` (`ξ ∘ Φ' ≠ 0` since `Φ'` is onto); `⟨p(τ), f(q(τ), u) - f(q(τ), ũ(τ))⟩ ≤ 0` at
Lebesgue points, which have full measure (`ae_isLebesguePointWithin`), is the maximality
condition. -/
theorem exists_costate_of_boundary (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U)
    (ht₁ : 0 < t₁) (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) (hψ : ContDiffAt ℝ 1 ψ a₀)
    (hψ0 : ψ a₀ = q 0) (hΦ : ContDiffAt ℝ 1 Φ (q t₁))
    (hΦsurj : Function.Surjective (fderiv ℝ Φ (q t₁)))
    (hbd : ∃ ε > 0, Φ (q t₁) ∉ interior (Φ '' localAttainableSet f Ω U ψ a₀ q t₁ ε)) :
    ∃ (ξ : StrongDual ℝ Q) (p : ℝ → StrongDual ℝ E), ξ ≠ 0 ∧
      p t₁ = ξ.comp (fderiv ℝ Φ (q t₁)) ∧ (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, p t ≠ 0) ∧ IsAdjoint f 0 0 ũ q t₁ p ∧ IsMaximal f 0 0 U ũ q t₁ p ∧
      (p 0).comp (fderiv ℝ ψ a₀) = 0 := by
  obtain ⟨ε, hε, hεbd⟩ := hbd
  set Φ' := fderiv ℝ Φ (q t₁)
  set R := stateTransition (linearization f ũ q)
  -- by Lemma 12.2, the cone of the variations is not the whole space (D9 is inside Lemma 12.2)
  have hne : PointedCone.hull ℝ
      (range (fun α : P ↦ Φ' (R 0 t₁ (fderiv ℝ ψ a₀ α))) ∪
        (fun p : ℝ × V ↦ Φ' (needleVector f ũ q t₁ p.1 p.2)) ''
          ({τ | τ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ} ×ˢ U)) ≠ ⊤ :=
    fun h ↦ hεbd (lemma12_2_local hΩ hU hf ht₁ href hψ hψ0 hΦ h ε hε)
  -- a supporting covector `ξ ≠ 0` (12.41), `= 0` on the linear part (12.47)
  obtain ⟨ξ, hξ0, hξ⟩ := exists_dual_ne_zero_nonpos_of_ne_top hne
  have hξlin : ∀ α, ξ (Φ' (R 0 t₁ (fderiv ℝ ψ a₀ α))) = 0 := by
    intro α
    have h1 := hξ _ (PointedCone.subset_hull (Or.inl ⟨α, rfl⟩))
    have h2 := hξ _ (PointedCone.subset_hull (Or.inl ⟨-α, rfl⟩))
    simp only [map_neg] at h2
    linarith
  have hξneedle : ∀ τ ∈ Icc 0 t₁, IsLebesguePointWithin ũ (Icc 0 t₁) τ → ∀ u ∈ U,
      ξ (Φ' (needleVector f ũ q t₁ τ u)) ≤ 0 := fun τ hτ hleb u hu ↦
    hξ _ (PointedCone.subset_hull (Or.inr ⟨(τ, u), ⟨⟨hτ, hleb⟩, hu⟩, rfl⟩))
  -- `λ_{t₁} = Φ^* ξ ≠ 0` (12.44), since `Φ'` is onto
  set ℓ : StrongDual ℝ E := ξ.comp Φ'
  have hℓ : ℓ ≠ 0 := by
    intro h
    apply hξ0
    ext w
    obtain ⟨x, rfl⟩ := hΦsurj w
    exact congrArg (fun L : StrongDual ℝ E ↦ L x) h
  -- `λ_t = (P^{t₁}_t)^* λ_{t₁}`: the Hamiltonian system and the maximality condition
  obtain ⟨hlip, hnz, hadj, hmax⟩ := costate_of_supporting hU hf ht₁ href hℓ hξneedle
  refine ⟨ξ, fun t ↦ ℓ.comp (R t t₁), hξ0, ?_, hlip, hnz, hadj, hmax, ?_⟩
  · simp only [R, stateTransition_self, ContinuousLinearMap.comp_id, ℓ]
  · -- the transversality condition at the initial point (12.47)–(12.48)
    ext α
    simpa [ℓ] using hξlin α

/-- **Agrachev–Sachkov, Theorem 12.1 (PMP)** (authors' draft, p. 164): let `ũ(t)`,
`t ∈ [0, t₁]`, be an admissible control and `q̃(t) = q_ũ(t)` the corresponding solution of the
Cauchy problem (12.1), (12.2). If `q̃(t₁) ∈ ∂A_{q₀}(t₁)`, then there exists a Lipschitzian curve
`λ_t ∈ T*_{q̃(t)}M`, `0 ≤ t ≤ t₁`, such that `λ_t ≠ 0` (12.3), `λ̇_t = h⃗_{ũ(t)}(λ_t)` (12.4),
`h_{ũ(t)}(λ_t) = max_{u ∈ U} h_u(λ_t)` (12.5) for almost all `t ∈ [0, t₁]`.

In coordinates on `Ω ⊆ E` (D1): `q` is the reference trajectory (A–S's `q̃`) from `q(0) = q₀`;
the curve `p` (A–S's `λ_t`) is a Lipschitz curve in `E*`, (12.4) is the adjoint equation
`ṗ = -p ∘ ∂ₓf(q, ũ)` (`IsAdjoint` with `φ = 0`), (12.5) is `IsMaximal`; (12.3) is stated for
every `t`. Reading: `0 < t₁` (see the module docstring).

Proof (A–S, p. 172): Lemma 12.2 (`lemma12_2`) shows that the cone of needle vectors is not
the whole space; a supporting covector `λ_{t₁} ≠ 0` (`exists_dual_ne_zero_nonpos_of_ne_top`);
`λ_t = (P^{t₁}_t)^* λ_{t₁}` solves the Hamiltonian system by Proposition 11.3
(`ControlSystem.adjoint_stateTransition`), and the supporting inequality is the maximality
condition. (Equivalently, the case `ψ` constant, `Φ = id` of `exists_costate_of_boundary`.) -/
theorem theorem12_1 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hbd : q t₁ ∈ frontier (attainableSet f Ω U (q 0) t₁)) :
    ∃ p : ℝ → StrongDual ℝ E, (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, p t ≠ 0) ∧ IsAdjoint f 0 0 ũ q t₁ p ∧ IsMaximal f 0 0 U ũ q t₁ p := by
  -- by Lemma 12.2, the cone of the needle vectors is not the whole tangent space
  have hne : PointedCone.hull ℝ ((fun p : ℝ × V ↦ needleVector f ũ q t₁ p.1 p.2) ''
      ({τ | τ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ} ×ˢ U)) ≠ ⊤ :=
    fun h ↦ hbd.2 (lemma12_2 hΩ hU hf ht₁ href h)
  -- so it has a hyperplane of support at the origin: `λ_{t₁} ≠ 0`, `⟨λ_{t₁}, g_{t,u}(q₁)⟩ ≤ 0`
  obtain ⟨ℓ, hℓ0, hℓ⟩ := exists_dual_ne_zero_nonpos_of_ne_top hne
  obtain ⟨hlip, hnz, hadj, hmax⟩ := costate_of_supporting hU hf ht₁ href hℓ0
    fun τ hτ hleb u hu ↦ hℓ _ (PointedCone.subset_hull ⟨(τ, u), ⟨⟨hτ, hleb⟩, hu⟩, rfl⟩)
  exact ⟨_, hlip, hnz, hadj, hmax⟩

end Pontryagin
