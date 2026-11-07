module

public import OptimalControl.Pontryagin.Geometric
public import OptimalControl.ODE.TimeChange
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The maximum principle for optimal control problems (Agrachev–Sachkov, §§12.4–12.5)

Theorems 12.3, 12.4 and 12.5 of A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the
Geometric Viewpoint* (authors' draft, pp. 174–184), for fixed terminal time and an integral cost
`J(u) = ∫₀^{t₁} φ(q(t), u(t)) dt` with `φ` as regular as `f` (§10.1, p. 134; here
`ControlSystem.IsC1On φ Ω U`), read on an open subset `Ω` of `E` (D1):

* **Theorem 12.3** (p. 176), fixed end points `q(0) = q₀`, `q(t₁) = q₁`: `theorem12_3`;
* **Theorem 12.4** (p. 178), boundary conditions `q(0) ∈ N₀`, `q(t₁) ∈ N₁` and the transversality
  conditions `λ₀ ⊥ T_{q̃(0)}N₀`, `λ_{t₁} ⊥ T_{q̃(t₁)}N₁` (12.34): `theorem12_4`;
* **Theorem 12.5** (p. 183), mixed boundary conditions `(q(0), q(t₁)) ∈ N ⊆ M × M` and the
  transversality condition `(-λ₀, λ_{t₁}) ⊥ T_{(q̃(0), q̃(t₁))}N` (12.53): `theorem12_5`.

The Hamiltonian is `h^ν_u(λ) = ⟨λ, f_u(q)⟩ + ν φ(q, u)` (`controlHamiltonian`); the Hamiltonian
system `λ̇ = h⃗^ν_{ũ(t)}(λ)` is, in coordinates, the adjoint equation
`ṗ = -p ∘ ∂ₓf(q̃, ũ) - ν ∂ₓφ(q̃, ũ)` (`IsAdjoint`).

## Readings

The immersed submanifolds `N₀`, `N₁ ⊆ M` and `N ⊆ M × M` enter only near the end points of the
reference trajectory, as in A–S's proof (p. 180: "Choose a submersion `Φ : O_{q̃(t₁)} → ℝᵖ` …
so that `Φ⁻¹(0) = N₁ ∩ O_{q̃(t₁)}`"): `N₀` through a `C¹` parametrization `ψ` of a neighbourhood
of `q̃(0)` (then `T_{q̃(0)}N₀ = range ψ'(a₀)` and `λ₀ ⊥ T N₀` reads `λ₀ ∘ ψ'(a₀) = 0`), `N₁` and
`N` through `C¹` maps `Φ`, `G` with surjective derivative whose zero sets near the end points lie
in `N₁`, `N` (then `T N₁ = ker Φ'`, `T N = ker G'`). A–S's nontriviality (12.32),
`(λ_t, ν) ≢ (0, 0)`, `t ∈ [0, t₁]`, is stated pointwise, `(λ_t, ν) ≠ (0, 0)` for every `t`, which
is what the proof gives (and is equivalent, `λ` solving a linear equation). A–S's auxiliary sets
`v ≥ 0` are replaced by `[0, 1]` (D4); the costate is the Lipschitzian curve of Theorem 12.1.

## The auxiliary systems (namespace `Pontryagin.Reduction`)

A–S's reductions are carried out on explicit auxiliary systems, with their regularity, reference
pairs, the projection of their admissible pairs to admissible pairs of `f`, and the decomposition
of their costates (`Pontryagin.Reduction.adjoint_prod`: on a product state space `A × B` with
dynamics independent of the `A`-coordinate, the `A`-part of the costate is constant and the
`B`-part solves the adjoint equation of the `B`-system, A–S's "`ν = const`" (p. 176) and
"`η̇ = 0`" (12.56)):

* `Pontryagin.Reduction.costExt`, the cost-extended system (12.23) `ẏ = φ(q, u) + v`,
  `q̇ = f(q, u)` of Theorems 12.3 and 12.4;
* `Pontryagin.Reduction.doubled`, `Pontryagin.Reduction.doubledCost`, the system `ẋ = 0`,
  `q̇ = f(q, u)` on `M × M` with cost `φ(q, u)` of the proof of Theorem 12.5.

The pointwise nontriviality `(λ_t, ν) ≠ 0` of Theorem 12.5 is obtained from the pointwise
nontriviality of the costate `(η, λ)` of the doubled system given by Theorem 12.4 through the
uniqueness for the adjoint equation (`Pontryagin.Reduction.eq_zero_of_adjoint`): if `λ_t = 0` and
`ν = 0`, then `λ ≡ 0`, so `η = -λ₀ = 0` (A–S: "All required statements of PMP obviously
follow").
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace Pontryagin

open ControlSystem

namespace Reduction

section Prod

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
  [NormedSpace ℝ B]

/-- A covector on `A × B` is the sum of its restrictions to the factors. -/
theorem apply_prod (p : StrongDual ℝ (A × B)) (a : A) (b : B) :
    p (a, b) = p.comp (ContinuousLinearMap.inl ℝ A B) a +
      p.comp (ContinuousLinearMap.inr ℝ A B) b := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← map_add]
  simp

/-- A covector on `ℝ` composed with a real-valued map is a multiple of that map. -/
theorem comp_real (c : StrongDual ℝ ℝ) (D : B →L[ℝ] ℝ) : c.comp D = c 1 • D := by
  ext b
  have : c (D b) = c (D b • 1) := by rw [smul_eq_mul, mul_one]
  rw [ContinuousLinearMap.comp_apply, this, map_smul]
  simp [mul_comm]

/-- A covector `λ̂` on `ℝ × B`: `λ̂(a, b) = a λ̂(1, 0) + λ̂(0, b)`. -/
theorem apply_prod_real (p : StrongDual ℝ (ℝ × B)) (a : ℝ) (b : B) :
    p (a, b) = a * p (1, 0) + p.comp (ContinuousLinearMap.inr ℝ ℝ B) b := by
  rw [apply_prod]
  congr 1
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    show ((a, 0) : ℝ × B) = a • ((1 : ℝ), (0 : B)) by simp, map_smul, smul_eq_mul]

/-- A continuous linear map preserves interval integrability. -/
theorem intervalIntegrable_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : ℝ → F} {a b : ℝ}
    (h : IntervalIntegrable f volume a b) : IntervalIntegrable (fun r ↦ L (f r)) volume a b :=
  ⟨L.integrable_comp h.1, L.integrable_comp h.2⟩

/-- The product `(f x).prod (g x)` of continuous families of continuous linear maps is
continuous. -/
theorem continuousOn_clm_prod {X F G : Type*} [TopologicalSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {s : Set X}
    {f : X → A →L[ℝ] F} {g : X → A →L[ℝ] G} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x ↦ (f x).prod (g x)) s :=
  (ContinuousLinearMap.prodL ℝ).continuous.comp_continuousOn (hf.prodMk hg)

/-- **The costate of a product system.** On a product state space `A × B`, let the linearization
along the reference be `(α ∘ snd, β ∘ snd)` (the dynamics do not depend on the `A`-coordinate)
and let `p` solve the adjoint equation `p(t) = p(T) + ∫ₜᵀ (p ∘ (α ∘ snd, β ∘ snd) + μ ∘ snd)`.
Then the `A`-part `p ∘ inl` is constant on `[0, T]`, and the `B`-part `p ∘ inr` solves the
adjoint equation of the `B`-system, `p_B(t) = p_B(T) + ∫ₜᵀ (p_B ∘ β + p_A ∘ α + μ)`.
(A–S's "`ν = const`", p. 176, and "`η̇ = 0`", (12.56).) -/
theorem adjoint_prod {T : ℝ} (hT : 0 ≤ T) {p X : ℝ → StrongDual ℝ (A × B)}
    (hXi : IntervalIntegrable X volume 0 T) (hp : ∀ t ∈ Icc 0 T, p t = p T + ∫ r in t..T, X r)
    {α : ℝ → B →L[ℝ] A} {β : ℝ → B →L[ℝ] B} {μ : ℝ → StrongDual ℝ B}
    (hX : ∀ r ∈ Icc 0 T, X r = (p r).comp (((α r).comp (ContinuousLinearMap.snd ℝ A B)).prod
      ((β r).comp (ContinuousLinearMap.snd ℝ A B))) + (μ r).comp (ContinuousLinearMap.snd ℝ A B)) :
    (∀ t ∈ Icc 0 T, (p t).comp (ContinuousLinearMap.inl ℝ A B) =
      (p T).comp (ContinuousLinearMap.inl ℝ A B)) ∧
    IntervalIntegrable (fun r ↦ ((p r).comp (ContinuousLinearMap.inr ℝ A B)).comp (β r) +
      (((p T).comp (ContinuousLinearMap.inl ℝ A B)).comp (α r) + μ r)) volume 0 T ∧
    ∀ t ∈ Icc 0 T, (p t).comp (ContinuousLinearMap.inr ℝ A B) =
      (p T).comp (ContinuousLinearMap.inr ℝ A B) + ∫ r in t..T,
        (((p r).comp (ContinuousLinearMap.inr ℝ A B)).comp (β r) +
          (((p T).comp (ContinuousLinearMap.inl ℝ A B)).comp (α r) + μ r)) := by
  set Pl : StrongDual ℝ (A × B) →L[ℝ] StrongDual ℝ A :=
    (ContinuousLinearMap.inl ℝ A B).precomp ℝ
  set Pr : StrongDual ℝ (A × B) →L[ℝ] StrongDual ℝ B :=
    (ContinuousLinearMap.inr ℝ A B).precomp ℝ
  have hsub : ∀ t ∈ Icc 0 T, uIcc t T ⊆ Icc 0 T := fun t ht ↦ uIcc_subset_Icc ht ⟨hT, le_rfl⟩
  have hXi' : ∀ t ∈ Icc 0 T, IntervalIntegrable X volume t T := fun t ht ↦
    hXi.mono_set (by rw [uIcc_of_le hT]; exact hsub t ht)
  have hl0 : ∀ r ∈ Icc 0 T, (X r).comp (ContinuousLinearMap.inl ℝ A B) = 0 := by
    intro r hr
    rw [hX r hr]
    ext a
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_apply,
      add_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.coe_snd', map_zero, zero_apply, add_zero]
    exact map_zero (p r)
  have h1 : ∀ t ∈ Icc 0 T, (p t).comp (ContinuousLinearMap.inl ℝ A B) =
      (p T).comp (ContinuousLinearMap.inl ℝ A B) := by
    intro t ht
    have := congrArg Pl (hp t ht)
    rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm Pl (hXi' t ht)] at this
    simp only [Pl, ContinuousLinearMap.precomp_apply] at this
    rw [this, intervalIntegral.integral_congr (g := fun _ ↦ 0)
      (fun r hr ↦ hl0 r (hsub t ht hr)), intervalIntegral.integral_zero, add_zero]
  have h2 : ∀ r ∈ Icc 0 T, (X r).comp (ContinuousLinearMap.inr ℝ A B) =
      ((p r).comp (ContinuousLinearMap.inr ℝ A B)).comp (β r) +
        (((p T).comp (ContinuousLinearMap.inl ℝ A B)).comp (α r) + μ r) := by
    intro r hr
    rw [hX r hr, ← h1 r hr]
    ext b
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_snd']
    rw [apply_prod]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    abel
  refine ⟨h1, ?_, fun t ht ↦ ?_⟩
  · refine (intervalIntegrable_clm Pr hXi).congr fun r hr ↦ ?_
    rw [uIoc_of_le hT] at hr
    simpa [Pr] using h2 r (Ioc_subset_Icc_self hr)
  · have := congrArg Pr (hp t ht)
    rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm Pr (hXi' t ht)] at this
    simp only [Pr, ContinuousLinearMap.precomp_apply] at this
    rw [this, intervalIntegral.integral_congr fun r hr ↦ h2 r (hsub t ht hr)]

end Prod

/-- The first component of an interval integral of pairs. -/
theorem integral_fst {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {g : ℝ → F × G} {a b : ℝ}
    (h : IntervalIntegrable g volume a b) : (∫ r in a..b, g r).1 = ∫ r in a..b, (g r).1 :=
  ((ContinuousLinearMap.fst ℝ F G).intervalIntegral_comp_comm h).symm

/-- The second component of an interval integral of pairs. -/
theorem integral_snd {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {g : ℝ → F × G} {a b : ℝ}
    (h : IntervalIntegrable g volume a b) : (∫ r in a..b, g r).2 = ∫ r in a..b, (g r).2 :=
  ((ContinuousLinearMap.snd ℝ F G).intervalIntegral_comp_comm h).symm

/-- A pair of interval integrable functions is interval integrable. -/
theorem intervalIntegrable_prodMk {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {g₁ : ℝ → F} {g₂ : ℝ → G} {a b : ℝ} (h₁ : IntervalIntegrable g₁ volume a b)
    (h₂ : IntervalIntegrable g₂ volume a b) :
    IntervalIntegrable (fun r ↦ (g₁ r, g₂ r)) volume a b :=
  ⟨h₁.1.prodMk h₂.1, h₁.2.prodMk h₂.2⟩

/-- A nonzero covector `λ̂` on `ℝ × B` has `(λ̂(1, 0), λ̂ ∘ inr) ≠ 0`. -/
theorem prod_ne_zero_of_ne_zero {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {p : StrongDual ℝ (ℝ × B)} (h : p ≠ 0) :
    (p (1, 0), p.comp (ContinuousLinearMap.inr ℝ ℝ B)) ≠ 0 := by
  intro h0
  rw [Prod.ext_iff] at h0
  simp only [Prod.fst_zero, Prod.snd_zero] at h0
  apply h
  refine ContinuousLinearMap.ext fun x ↦ ?_
  rw [show x = (x.1, x.2) from rfl, apply_prod_real, h0.1, h0.2]
  simp

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {Ω : Set E} {U : Set V} {f : E → V → E} {φ : E → V → ℝ} {T : ℝ} {ũ : ℝ → V}
  {q : ℝ → E}

/-- Along an admissible pair in `Ω`, the linearization `∂ₓf(q(t), ũ(t))` is a.e.-strongly
measurable and bounded on `[0, T]`. -/
theorem linearization_bound (hU : IsCompact U) (hf : IsC1On f Ω U) (hT : 0 ≤ T)
    (href : IsAdmissibleIn f Ω U (q 0) T ũ q) :
    AEStronglyMeasurable (linearization f ũ q) (volume.restrict (Icc 0 T)) ∧
      ∃ K, ∀ t ∈ Icc 0 T, ‖linearization f ũ q t‖ ≤ K := by
  obtain ⟨h1, ⟨K, hK⟩, -⟩ := TimeChange.integrand_bound (g := fun x u ↦ fderiv ℝ (f · u) x) hU
    hf.continuousOn_fderiv hT href.1.2.2.1 href.1.1.aemeasurable
    (fun t ht ↦ ⟨href.2 t ht, href.1.2.1 t ht⟩)
  exact ⟨h1, K, hK⟩

/-- **Uniqueness for the adjoint equation** with `ν = 0`: a continuous solution vanishing at one
time vanishes on `[0, T]` (`ControlSystem.eq_comp_stateTransition_of_adjoint`). -/
theorem eq_zero_of_adjoint (hU : IsCompact U) (hf : IsC1On f Ω U) (hT : 0 ≤ T)
    (href : IsAdmissibleIn f Ω U (q 0) T ũ q) {p : ℝ → StrongDual ℝ E}
    (hp : ContinuousOn p (Icc 0 T)) (hadj : IsAdjoint f φ 0 ũ q T p) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 T) (h0 : p t₀ = 0) : ∀ t ∈ Icc 0 T, p t = 0 := by
  obtain ⟨hA, K, hK⟩ := linearization_bound hU hf hT href
  obtain ⟨hint, heq⟩ := hadj
  simp only [zero_smul, add_zero] at hint heq
  have hi : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T,
      IntervalIntegrable (fun r ↦ (p r).comp (linearization f ũ q r)) volume a b :=
    fun a ha b hb ↦ hint.mono_set (by rw [uIcc_of_le hT]; exact uIcc_subset_Icc ha hb)
  have hpeq : ∀ t ∈ Icc 0 T, p t = p t₀ + ∫ r in t..t₀, (p r).comp (linearization f ũ q r) := by
    intro t ht
    rw [heq t ht, heq t₀ ht₀, ← intervalIntegral.integral_add_adjacent_intervals
      (hi t ht t₀ ht₀) (hi t₀ ht₀ T ⟨hT, le_rfl⟩)]
    abel
  intro t ht
  rw [eq_comp_stateTransition_of_adjoint hA hK ht₀ hp hpeq t ht, h0,
    ContinuousLinearMap.zero_comp]

/-! ### The cost-extended system -/

/-- Agrachev–Sachkov's cost-extended system (12.23), p. 175: `ẏ = φ(q, u) + v`, `q̇ = f(q, u)` on
`ℝ × M`, with the control `(v, u)`. -/
def costExt (f : E → V → E) (φ : E → V → ℝ) (z : ℝ × E) (w : ℝ × V) : ℝ × E :=
  (φ z.2 w.2 + w.1, f z.2 w.2)

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The derivative in the state of the cost-extended system: `(y, x) ↦ (∂ₓφ x, ∂ₓf x)`. -/
theorem hasFDerivAt_costExt (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U) {z : ℝ × E} (hz : z.2 ∈ Ω)
    {w : ℝ × V} (hw : w.2 ∈ U) :
    HasFDerivAt (fun z' ↦ costExt f φ z' w)
      (((fderiv ℝ (φ · w.2) z.2).comp (ContinuousLinearMap.snd ℝ ℝ E)).prod
        ((fderiv ℝ (f · w.2) z.2).comp (ContinuousLinearMap.snd ℝ ℝ E))) z :=
  (((hφ.differentiableAt _ hz _ hw).hasFDerivAt.comp z hasFDerivAt_snd).add_const w.1).prodMk
    ((hf.differentiableAt _ hz _ hw).hasFDerivAt.comp z hasFDerivAt_snd)

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The cost-extended system has A–S's regularity (10.2)–(10.4) when `f` and `φ` have. -/
theorem isC1On_costExt (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U) (C : Set ℝ) :
    IsC1On (costExt f φ) (univ ×ˢ Ω) (C ×ˢ U) where
  continuousOn := by
    have hmaps : MapsTo (fun p : (ℝ × E) × (ℝ × V) ↦ (p.1.2, p.2.2))
        ((univ ×ˢ Ω) ×ˢ (C ×ˢ U)) (Ω ×ˢ U) := fun p hp ↦ ⟨hp.1.2, hp.2.2⟩
    have hc : Continuous fun p : (ℝ × E) × (ℝ × V) ↦ (p.1.2, p.2.2) :=
      continuous_fst.snd.prodMk continuous_snd.snd
    exact ((hφ.continuousOn.comp hc.continuousOn hmaps).add
      continuous_snd.fst.continuousOn).prodMk (hf.continuousOn.comp hc.continuousOn hmaps)
  differentiableAt := fun _ hz _ hw ↦ (hasFDerivAt_costExt hf hφ hz.2 hw.2).differentiableAt
  continuousOn_fderiv := by
    have hmaps : MapsTo (fun p : (ℝ × E) × (ℝ × V) ↦ (p.1.2, p.2.2))
        ((univ ×ˢ Ω) ×ˢ (C ×ˢ U)) (Ω ×ˢ U) := fun p hp ↦ ⟨hp.1.2, hp.2.2⟩
    have hc : Continuous fun p : (ℝ × E) × (ℝ × V) ↦ (p.1.2, p.2.2) :=
      continuous_fst.snd.prodMk continuous_snd.snd
    refine (continuousOn_clm_prod
      ((hφ.continuousOn_fderiv.comp hc.continuousOn hmaps).clm_comp continuousOn_const)
      ((hf.continuousOn_fderiv.comp hc.continuousOn hmaps).clm_comp continuousOn_const)).congr
      fun p hp ↦ (hasFDerivAt_costExt hf hφ hp.1.2 hp.2.2).fderiv

/-- The reference pair `((0, ũ), (J, q))` of the cost-extended system, `J(t) = ∫₀ᵗ φ(q, ũ)`. -/
theorem isAdmissibleIn_costExt (hU : IsCompact U) (hφ : IsC1On φ Ω U) (hT : 0 ≤ T)
    (href : IsAdmissibleIn f Ω U (q 0) T ũ q) {C : Set ℝ} (hC : (0 : ℝ) ∈ C) :
    IsAdmissibleIn (costExt f φ) (univ ×ˢ Ω) (C ×ˢ U) (0, q 0) T (fun t ↦ (0, ũ t))
      (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) := by
  obtain ⟨⟨hũm, hũU, hqc, hqi, hqeq⟩, hqΩ⟩ := href
  have hφi := (TimeChange.integrand_bound hU hφ.continuousOn hT hqc hũm.aemeasurable
    fun t ht ↦ ⟨hqΩ t ht, hũU t ht⟩).2.2
  have hφc : ContinuousOn (fun t ↦ ∫ r in (0 : ℝ)..t, φ (q r) (ũ r)) (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (by rw [uIcc_of_le hT]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 hφi)
    rwa [uIcc_of_le hT] at this
  have hi : IntervalIntegrable (fun s ↦ costExt f φ (∫ r in (0 : ℝ)..s, φ (q r) (ũ r), q s)
      (0, ũ s)) volume 0 T := by
    simpa [costExt] using intervalIntegrable_prodMk hφi hqi
  refine ⟨⟨measurable_const.prodMk hũm, fun t ht ↦ ⟨hC, hũU t ht⟩, hφc.prodMk hqc, hi,
    fun t ht ↦ ?_⟩, fun t ht ↦ ⟨mem_univ _, hqΩ t ht⟩⟩
  have hit : IntervalIntegrable (fun s ↦ costExt f φ (∫ r in (0 : ℝ)..s, φ (q r) (ũ r), q s)
      (0, ũ s)) volume 0 t :=
    hi.mono_set (by rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, integral_fst hit]
    simp [costExt]
  · rw [Prod.snd_add, integral_snd hit]
    simpa [costExt] using hqeq t ht

/-- An admissible pair of the cost-extended system with `v ≥ 0` projects to an admissible pair of
the original system, whose cost is at most the increase of the cost coordinate. -/
theorem IsAdmissibleIn.costExt_proj (hU : IsCompact U) (hφ : IsC1On φ Ω U) (hT : 0 ≤ T)
    {C : Set ℝ} (hC : C ⊆ Ici 0) {z₀ : ℝ × E} {w : ℝ → ℝ × V} {z : ℝ → ℝ × E}
    (h : IsAdmissibleIn (costExt f φ) (univ ×ˢ Ω) (C ×ˢ U) z₀ T w z) :
    IsAdmissibleIn f Ω U z₀.2 T (fun t ↦ (w t).2) (fun t ↦ (z t).2) ∧
      cost φ T (fun t ↦ (w t).2) (fun t ↦ (z t).2) ≤ (z T).1 - z₀.1 := by
  obtain ⟨⟨hwm, hwU, hzc, hzi, hzeq⟩, hzΩ⟩ := h
  have hfi : IntervalIntegrable (fun s ↦ f (z s).2 (w s).2) volume 0 T :=
    intervalIntegrable_clm (ContinuousLinearMap.snd ℝ ℝ E) hzi
  have hsub : ∀ t ∈ Icc 0 T, uIcc 0 t ⊆ uIcc 0 T := fun t ht ↦ by
    rw [uIcc_of_le hT, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have hzc2 : ContinuousOn (fun t ↦ (z t).2) (Icc 0 T) := continuous_snd.comp_continuousOn hzc
  have hwm2 : Measurable fun t ↦ (w t).2 := measurable_snd.comp hwm
  refine ⟨⟨⟨hwm2, fun t ht ↦ (hwU t ht).2, hzc2, hfi, fun t ht ↦ ?_⟩,
    fun t ht ↦ (hzΩ t ht).2⟩, ?_⟩
  · have := congrArg Prod.snd (hzeq t ht)
    rw [Prod.snd_add, integral_snd (hzi.mono_set (hsub t ht))] at this
    exact this
  · have hφi := (TimeChange.integrand_bound hU hφ.continuousOn hT hzc2 hwm2.aemeasurable
      fun t ht ↦ ⟨(hzΩ t ht).2, (hwU t ht).2⟩).2.2
    have h1 := congrArg Prod.fst (hzeq T ⟨hT, le_rfl⟩)
    rw [Prod.fst_add, integral_fst hzi] at h1
    rw [h1, add_sub_cancel_left, cost]
    refine intervalIntegral.integral_mono_on hT hφi
      (intervalIntegrable_clm (ContinuousLinearMap.fst ℝ ℝ E) hzi) fun t ht ↦ ?_
    have : 0 ≤ (w t).1 := hC (hwU t ht).1
    simp only [costExt]
    linarith

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- The Hamiltonian of the cost-extended system: `⟨λ̂, f̂_{(v, u)}⟩ = h^ν_u(λ) + ν v` with
`λ̂ = (ν, λ)`. -/
theorem controlHamiltonian_costExt (p : StrongDual ℝ (ℝ × E)) (z : ℝ × E) (v : ℝ) (u : V) :
    controlHamiltonian (costExt f φ) 0 0 z p (v, u) =
      controlHamiltonian f φ (p (1, 0)) z.2 (p.comp (ContinuousLinearMap.inr ℝ ℝ E)) u +
        v * p (1, 0) := by
  simp only [controlHamiltonian, costExt, Pi.zero_apply, zero_mul, add_zero]
  rw [apply_prod_real]
  ring

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- **The costate of the cost-extended system** (A–S, (12.24), p. 176): along a reference pair
whose `E`-components are `(ũ, q)`, a solution `λ̂ = (ν, λ)` of the Hamiltonian system of the
extended system has `ν` constant, and `λ` solves `λ̇ = -λ ∘ ∂ₓf - ν ∂ₓφ`. -/
theorem adjoint_costExt (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U) (hT : 0 ≤ T)
    (hqΩ : ∀ r ∈ Icc 0 T, q r ∈ Ω) (hũU : ∀ r ∈ Icc 0 T, ũ r ∈ U) {wh : ℝ → ℝ × V}
    {qh : ℝ → ℝ × E} (hwh : ∀ r, (wh r).2 = ũ r) (hqh : ∀ r, (qh r).2 = q r)
    {p : ℝ → StrongDual ℝ (ℝ × E)} (hadj : IsAdjoint (costExt f φ) 0 0 wh qh T p) :
    (∀ t ∈ Icc 0 T, p t (1, 0) = p T (1, 0)) ∧
      IsAdjoint f φ (p T (1, 0)) ũ q T (fun t ↦ (p t).comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
  obtain ⟨hi, heq⟩ := hadj
  obtain ⟨h1, h2, h3⟩ := adjoint_prod hT hi heq (α := fun r ↦ fderiv ℝ (φ · (ũ r)) (q r))
    (β := linearization f ũ q) (μ := 0) fun r hr ↦ by
      have hl : linearization (costExt f φ) wh qh r = _ :=
        (hasFDerivAt_costExt hf hφ (by rw [hqh]; exact hqΩ r hr)
          (by rw [hwh]; exact hũU r hr)).fderiv
      rw [hl]
      simp [hwh, hqh, linearization]
  have hc : ∀ r, ((p T).comp (ContinuousLinearMap.inl ℝ ℝ E)).comp
      (fderiv ℝ (φ · (ũ r)) (q r)) + (0 : ℝ → StrongDual ℝ E) r =
      p T (1, 0) • fderiv ℝ (φ · (ũ r)) (q r) := fun r ↦ by
    rw [comp_real]
    simp
  refine ⟨fun t ht ↦ ?_, ?_, fun t ht ↦ ?_⟩
  · simpa using congrArg (fun L ↦ L 1) (h1 t ht)
  · simpa only [hc] using h2
  · simpa only [hc] using h3 t ht

/-! ### The doubled system of the proof of Theorem 12.5 -/

/-- Agrachev–Sachkov's auxiliary system of the proof of Theorem 12.5, p. 183: `ẋ = 0`,
`q̇ = f(q, u)` on `M × M`. -/
def doubled (f : E → V → E) (z : E × E) (u : V) : E × E :=
  (0, f z.2 u)

/-- The cost of the doubled system, `φ(q, u)`. -/
def doubledCost (φ : E → V → ℝ) (z : E × E) (u : V) : ℝ :=
  φ z.2 u

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The derivative in the state of the doubled system: `(x, q) ↦ (0, ∂_q f q)`. -/
theorem hasFDerivAt_doubled (hf : IsC1On f Ω U) {z : E × E} (hz : z.2 ∈ Ω) {u : V}
    (hu : u ∈ U) :
    HasFDerivAt (fun z' ↦ doubled f z' u)
      (((0 : E →L[ℝ] E).comp (ContinuousLinearMap.snd ℝ E E)).prod
        ((fderiv ℝ (f · u) z.2).comp (ContinuousLinearMap.snd ℝ E E))) z := by
  have := (hasFDerivAt_const (0 : E) z).prodMk
    ((hf.differentiableAt _ hz _ hu).hasFDerivAt.comp z hasFDerivAt_snd)
  simpa [doubled, Function.comp_def] using this

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The derivative in the state of the cost of the doubled system: `(x, q) ↦ ∂_q φ q`. -/
theorem hasFDerivAt_doubledCost (hφ : IsC1On φ Ω U) {z : E × E} (hz : z.2 ∈ Ω) {u : V}
    (hu : u ∈ U) :
    HasFDerivAt (fun z' ↦ doubledCost φ z' u)
      ((fderiv ℝ (φ · u) z.2).comp (ContinuousLinearMap.snd ℝ E E)) z :=
  (hφ.differentiableAt _ hz _ hu).hasFDerivAt.comp z hasFDerivAt_snd

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The doubled system has A–S's regularity (10.2)–(10.4) when `f` has. -/
theorem isC1On_doubled (hf : IsC1On f Ω U) : IsC1On (doubled f) (univ ×ˢ Ω) U where
  continuousOn := by
    have hmaps : MapsTo (fun p : (E × E) × V ↦ (p.1.2, p.2)) ((univ ×ˢ Ω) ×ˢ U) (Ω ×ˢ U) :=
      fun p hp ↦ ⟨hp.1.2, hp.2⟩
    exact continuousOn_const.prodMk (hf.continuousOn.comp
      (continuous_fst.snd.prodMk continuous_snd).continuousOn hmaps)
  differentiableAt := fun _ hz _ hu ↦ (hasFDerivAt_doubled hf hz.2 hu).differentiableAt
  continuousOn_fderiv := by
    have hmaps : MapsTo (fun p : (E × E) × V ↦ (p.1.2, p.2)) ((univ ×ˢ Ω) ×ˢ U) (Ω ×ˢ U) :=
      fun p hp ↦ ⟨hp.1.2, hp.2⟩
    refine (continuousOn_clm_prod continuousOn_const
      ((hf.continuousOn_fderiv.comp (continuous_fst.snd.prodMk continuous_snd).continuousOn
        hmaps).clm_comp continuousOn_const)).congr
      fun p hp ↦ (hasFDerivAt_doubled hf hp.1.2 hp.2).fderiv

omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The cost of the doubled system has A–S's regularity (10.2)–(10.4) when `φ` has. -/
theorem isC1On_doubledCost (hφ : IsC1On φ Ω U) : IsC1On (doubledCost φ) (univ ×ˢ Ω) U where
  continuousOn := by
    have hmaps : MapsTo (fun p : (E × E) × V ↦ (p.1.2, p.2)) ((univ ×ˢ Ω) ×ˢ U) (Ω ×ˢ U) :=
      fun p hp ↦ ⟨hp.1.2, hp.2⟩
    exact hφ.continuousOn.comp (continuous_fst.snd.prodMk continuous_snd).continuousOn hmaps
  differentiableAt := fun _ hz _ hu ↦ (hasFDerivAt_doubledCost hφ hz.2 hu).differentiableAt
  continuousOn_fderiv := by
    have hmaps : MapsTo (fun p : (E × E) × V ↦ (p.1.2, p.2)) ((univ ×ˢ Ω) ×ˢ U) (Ω ×ˢ U) :=
      fun p hp ↦ ⟨hp.1.2, hp.2⟩
    refine ((hφ.continuousOn_fderiv.comp (continuous_fst.snd.prodMk continuous_snd).continuousOn
        hmaps).clm_comp continuousOn_const).congr
      fun p hp ↦ (hasFDerivAt_doubledCost hφ hp.1.2 hp.2).fderiv

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- An admissible pair of the doubled system: the first component is constant, the second is an
admissible pair of the original system. -/
theorem IsAdmissibleIn.doubled_proj {z₀ : E × E} {u : ℝ → V} {z : ℝ → E × E}
    (h : IsAdmissibleIn (doubled f) (univ ×ˢ Ω) U z₀ T u z) :
    (∀ t ∈ Icc 0 T, (z t).1 = z₀.1) ∧ IsAdmissibleIn f Ω U z₀.2 T u (fun t ↦ (z t).2) := by
  obtain ⟨⟨hum, huU, hzc, hzi, hzeq⟩, hzΩ⟩ := h
  have hsub : ∀ t ∈ Icc 0 T, uIcc 0 t ⊆ uIcc 0 T := fun t ht ↦ by
    rw [uIcc_of_le (ht.1.trans ht.2), uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  refine ⟨fun t ht ↦ ?_, ⟨⟨hum, huU, continuous_snd.comp_continuousOn hzc,
    intervalIntegrable_clm (ContinuousLinearMap.snd ℝ E E) hzi, fun t ht ↦ ?_⟩,
    fun t ht ↦ (hzΩ t ht).2⟩⟩
  · have := congrArg Prod.fst (hzeq t ht)
    rw [Prod.fst_add, integral_fst (hzi.mono_set (hsub t ht))] at this
    simpa [doubled] using this
  · have := congrArg Prod.snd (hzeq t ht)
    rw [Prod.snd_add, integral_snd (hzi.mono_set (hsub t ht))] at this
    exact this

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The reference pair `(ũ, (q(0), q))` of the doubled system. -/
theorem isAdmissibleIn_doubled (href : IsAdmissibleIn f Ω U (q 0) T ũ q) :
    IsAdmissibleIn (doubled f) (univ ×ˢ Ω) U (q 0, q 0) T ũ (fun t ↦ (q 0, q t)) := by
  obtain ⟨⟨hũm, hũU, hqc, hqi, hqeq⟩, hqΩ⟩ := href
  have hi : IntervalIntegrable (fun s ↦ doubled f (q 0, q s) (ũ s)) volume 0 T :=
    intervalIntegrable_prodMk intervalIntegrable_const hqi
  refine ⟨⟨hũm, hũU, continuousOn_const.prodMk hqc, hi, fun t ht ↦ ?_⟩,
    fun t ht ↦ ⟨mem_univ _, hqΩ t ht⟩⟩
  have hit : IntervalIntegrable (fun s ↦ doubled f (q 0, q s) (ũ s)) volume 0 t :=
    hi.mono_set (by rw [uIcc_of_le (ht.1.trans ht.2), uIcc_of_le ht.1]
                    exact Icc_subset_Icc le_rfl ht.2)
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, integral_fst hit]
    simp [doubled]
  · rw [Prod.snd_add, integral_snd hit]
    simpa [doubled] using hqeq t ht

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- The Hamiltonian of the doubled system with costate `(η, λ)` is that of the original system
with costate `λ`. -/
theorem controlHamiltonian_doubled (ν : ℝ) (p : StrongDual ℝ (E × E)) (z : E × E) (u : V) :
    controlHamiltonian (doubled f) (doubledCost φ) ν z p u =
      controlHamiltonian f φ ν z.2 (p.comp (ContinuousLinearMap.inr ℝ E E)) u := by
  simp only [controlHamiltonian, doubled, doubledCost]
  rw [apply_prod]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, add_left_inj]
  exact add_eq_right.2 (map_zero p)


omit [FiniteDimensional ℝ E] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **From the costate of the cost-extended system to the conclusions of Theorem 12.3** (A–S,
p. 176): for a costate `λ̂ = (ν, λ)` of the cost-extended system with `v ∈ [0, 1]` along the
reference `((0, ũ), (J, q))`, `λ` is Lipschitz, `(ν, λ_t) ≠ 0`, `λ` solves the adjoint equation
with `ν`, the maximality condition holds for `h^ν`, and `ν ≤ 0` (maximality in `v`). -/
theorem costExt_costate (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U) (hT : 0 < T)
    (href : IsAdmissibleIn f Ω U (q 0) T ũ q) {p : ℝ → StrongDual ℝ (ℝ × E)} {K : ℝ≥0}
    (hpL : LipschitzOnWith K p (Icc 0 T)) (hp0 : ∀ t ∈ Icc 0 T, p t ≠ 0)
    (hpadj : IsAdjoint (costExt f φ) 0 0 (fun t ↦ (0, ũ t))
      (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) T p)
    (hpmax : IsMaximal (costExt f φ) 0 0 (Icc 0 1 ×ˢ U) (fun t ↦ (0, ũ t))
      (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) T p) :
    (∃ K, LipschitzOnWith K (fun t ↦ (p t).comp (ContinuousLinearMap.inr ℝ ℝ E)) (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (p T (1, 0), (p t).comp (ContinuousLinearMap.inr ℝ ℝ E)) ≠ 0) ∧
      IsAdjoint f φ (p T (1, 0)) ũ q T (fun t ↦ (p t).comp (ContinuousLinearMap.inr ℝ ℝ E)) ∧
      IsMaximal f φ (p T (1, 0)) U ũ q T (fun t ↦ (p t).comp (ContinuousLinearMap.inr ℝ ℝ E)) ∧
      p T (1, 0) ≤ 0 := by
  have hũU := href.1.2.1
  obtain ⟨hνc, hadj⟩ := adjoint_costExt hf hφ hT.le href.2 hũU (fun r ↦ rfl) (fun r ↦ rfl) hpadj
  set Pr : StrongDual ℝ (ℝ × E) →L[ℝ] StrongDual ℝ E :=
    (ContinuousLinearMap.inr ℝ ℝ E).precomp ℝ with hPr
  refine ⟨⟨‖Pr‖₊ * K, Pr.lipschitzWith.comp_lipschitzOnWith hpL⟩, fun t ht ↦ ?_, hadj, ?_, ?_⟩
  · rw [← hνc t ht]
    exact prod_ne_zero_of_ne_zero (hp0 t ht)
  · filter_upwards [hpmax, ae_restrict_mem measurableSet_Icc] with t ht htI u hu
    have := ht (0, u) ⟨⟨le_rfl, zero_le_one⟩, hu⟩
    simp only [controlHamiltonian_costExt, hνc t htI] at this
    simpa using this
  · have : (ae (volume.restrict (Icc (0 : ℝ) T))).NeBot :=
      ae_restrict_neBot.2 (by simp [hT])
    obtain ⟨t, ht, htI⟩ := (hpmax.and (ae_restrict_mem measurableSet_Icc)).exists
    have := ht (1, ũ t) ⟨⟨zero_le_one, le_rfl⟩, hũU t htI⟩
    simp only [controlHamiltonian_costExt, hνc t htI] at this
    linarith

end Reduction

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {Ω : Set E} {U : Set V} {f : E → V → E} {φ : E → V → ℝ} {t₁ : ℝ} {ũ : ℝ → V}
  {q : ℝ → E}

/-- **Agrachev–Sachkov, Theorem 12.3** (authors' draft, p. 176): let `ũ(t)`, `t ∈ [0, t₁]`, be an
optimal control for problem (12.17)–(12.21), `J(ũ) = min{J(u) | q_u(t₁) = q₁}`. Then there
exists a nontrivial pair `(ν, λ_t) ≠ 0`, `ν ∈ ℝ`, `λ_t ∈ T*_{q̃(t)}M`, such that
`λ̇_t = h⃗^ν_{ũ(t)}(λ_t)`, `h^ν_{ũ(t)}(λ_t) = max_{u ∈ U} h^ν_u(λ_t)` for a.e. `t ∈ [0, t₁]`, and
`ν ≤ 0`.

In coordinates: `q` is the optimal trajectory (A–S's `q̃`) from `q₀ = q(0)` to `q₁ = q(t₁)`;
optimality is among the admissible pairs in `Ω` on `[0, t₁]` from `q(0)` ending at `q(t₁)`.

Proof (A–S, pp. 175–176): the extended system `ẏ = φ(q, u) + v`, `q̇ = f_u(q)`, `v ∈ [0, 1]`
(A–S: `v ≥ 0`) on `ℝ × Ω`; the reference `(0, ũ)` reaches the boundary of its attainable set at
`(J(ũ), q₁)` (a point `(J(ũ) - η, q₁)` would be reached by a cheaper control); Theorem 12.1
(`theorem12_1`) on `ℝ × Ω` gives `(ν, λ_t)`, `ν` constant since nothing depends on `y`, and
maximality over `v ≥ 0` forces `ν ≤ 0`. -/
theorem theorem12_3 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U)
    (ht₁ : 0 < t₁) (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hopt : ∀ (u : ℝ → V) (x : ℝ → E), IsAdmissibleIn f Ω U (q 0) t₁ u x → x t₁ = q t₁ →
      cost φ t₁ ũ q ≤ cost φ t₁ u x) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, (ν, p t) ≠ 0) ∧ IsAdjoint f φ ν ũ q t₁ p ∧ IsMaximal f φ ν U ũ q t₁ p ∧
      ν ≤ 0 := by
  have hT := ht₁.le
  -- the cost-extended system `ẏ = φ(q, u) + v`, `q̇ = f(q, u)`, `v ∈ [0, 1]`, and its reference
  -- pair `((0, ũ), (J, q))`, `J(t) = ∫₀ᵗ φ(q, ũ)`
  have hext := Reduction.isAdmissibleIn_costExt hU hφ hT href (C := Icc 0 1) ⟨le_rfl, zero_le_one⟩
  have h0 : (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) 0 = ((0 : ℝ), q 0) := by simp
  rw [← h0] at hext
  -- `(J(t₁), q(t₁))` is on the boundary of the attainable set: a point `(J(t₁) - η, q(t₁))` would
  -- be reached by a cheaper admissible pair
  have hbd : (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) t₁ ∈ frontier
      (attainableSet (Reduction.costExt f φ) (univ ×ˢ Ω) (Icc 0 1 ×ˢ U)
        ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) 0) t₁) := by
    refine ⟨subset_closure ⟨_, _, hext, rfl⟩, fun hint ↦ ?_⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
    obtain ⟨η, hη, hball⟩ := hint
    have hc : (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) t₁ = (cost φ t₁ ũ q, q t₁) := rfl
    rw [hc] at hball
    have hmem := hball (a := (cost φ t₁ ũ q - η / 2, q t₁)) (by
      rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg]
      rw [abs_of_pos (by positivity), max_eq_left (by positivity)]
      linarith)
    obtain ⟨w, z, hz, hzT⟩ := hmem
    rw [h0] at hz
    obtain ⟨hadm, hcost⟩ := Reduction.IsAdmissibleIn.costExt_proj hU hφ hT
      Icc_subset_Ici_self hz
    have := hopt _ _ hadm (by simp only [hzT])
    rw [hzT] at hcost
    simp only at hcost
    linarith
  obtain ⟨p, ⟨K, hpL⟩, hp0, hpadj, hpmax⟩ := theorem12_1 (isOpen_univ.prod hΩ)
    (isCompact_Icc.prod hU) (Reduction.isC1On_costExt hf hφ _) ht₁ hext hbd
  obtain ⟨hL, hne, hadj, hmax, hν⟩ :=
    Reduction.costExt_costate hf hφ ht₁ href hpL hp0 hpadj hpmax
  exact ⟨_, _, hL, hne, hadj, hmax, hν⟩

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- **Agrachev–Sachkov, Theorem 12.4** (authors' draft, p. 178): let `ũ(t)`, `t ∈ [0, t₁]`, be an
optimal control in problem (12.26)–(12.29) (`q(0) ∈ N₀`, `q(t₁) ∈ N₁`, `t₁` fixed,
`J(u) → min`). Then there exist a Lipschitzian curve `λ_t ∈ T*_{q̃(t)}M` and `ν ∈ ℝ` with
`λ̇_t = h⃗^ν_{ũ(t)}(λ_t)` (12.30), `h^ν_{ũ(t)}(λ_t) = max_{u ∈ U} h^ν_u(λ_t)` (12.31),
`(λ_t, ν) ≢ (0, 0)`, `t ∈ [0, t₁]` (12.32), `ν ≤ 0` (12.33), and
`λ₀ ⊥ T_{q̃(0)}N₀`, `λ_{t₁} ⊥ T_{q̃(t₁)}N₁` (12.34).

In coordinates, `N₀` near `q(0)` through a `C¹` parametrization `ψ` (`ψ(a₀) = q(0)`, `ψ(a) ∈ N₀`
for `a` near `a₀`), `N₁` near `q(t₁)` through a `C¹` submersion `Φ` (`Φ(q(t₁)) = 0`,
`Φ⁻¹(0) ⊆ N₁` near `q(t₁)`); (12.34) reads `λ₀ ∘ ψ'(a₀) = 0` and `λ_{t₁} = 0` on `ker Φ'`.

Proof (A–S, pp. 179–182): the cost-extended system `ẏ = φ + v`, `q̇ = f_u(q)`, `v ∈ [0, 1]`; with
`ψ̂(a) = (0, ψ(a))` and `Φ̂(y, q) = (y, Φ(q))`, optimality gives (12.37)/(12.45), and
`exists_costate_of_boundary` gives `λ̂_{t₁} = Φ̂^* ξ̂ = (ν, λ_{t₁})` (12.44), hence
`λ_{t₁} = Φ^* ξ ⊥ ker Φ'`, and `λ₀ ∘ ψ' = 0` (12.47)–(12.48); the rest as in Theorem 12.3. -/
theorem theorem12_4 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U)
    (ht₁ : 0 < t₁) {N₀ N₁ : Set E} (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hq₀ : q 0 ∈ N₀) (hq₁ : q t₁ ∈ N₁)
    (hopt : ∀ (u : ℝ → V) (x : ℝ → E), IsAdmissibleIn f Ω U (x 0) t₁ u x → x 0 ∈ N₀ →
      x t₁ ∈ N₁ → cost φ t₁ ũ q ≤ cost φ t₁ u x)
    {ψ : P → E} {a₀ : P} (hψ : ContDiffAt ℝ 1 ψ a₀) (hψ0 : ψ a₀ = q 0)
    (hψN : ∀ᶠ a in 𝓝 a₀, ψ a ∈ N₀) {Φ : E → Q} (hΦ : ContDiffAt ℝ 1 Φ (q t₁))
    (hΦsurj : Function.Surjective (fderiv ℝ Φ (q t₁))) (hΦ0 : Φ (q t₁) = 0)
    (hΦN : ∀ᶠ x in 𝓝 (q t₁), Φ x = 0 → x ∈ N₁) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      IsAdjoint f φ ν ũ q t₁ p ∧ IsMaximal f φ ν U ũ q t₁ p ∧
      (∀ t ∈ Icc 0 t₁, (p t, ν) ≠ 0) ∧ ν ≤ 0 ∧
      (p 0).comp (fderiv ℝ ψ a₀) = 0 ∧ ∀ w, fderiv ℝ Φ (q t₁) w = 0 → p t₁ w = 0 := by
  -- `q(0) ∈ N₀` and `q(t₁) ∈ N₁` also follow from the hypotheses on `ψ` and `Φ`; not used
  have _h : q 0 ∈ N₀ ∧ q t₁ ∈ N₁ := ⟨hq₀, hq₁⟩
  have hT := ht₁.le
  have hext := Reduction.isAdmissibleIn_costExt hU hφ hT href (C := Icc 0 1) ⟨le_rfl, zero_le_one⟩
  have h0 : (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) 0 = ((0 : ℝ), q 0) := by simp
  rw [← h0] at hext
  -- `ψ̂(a) = (0, ψ(a))` and `Φ̂(y, x) = (y, Φ(x))`
  have hψh : ContDiffAt ℝ 1 (fun a ↦ ((0 : ℝ), ψ a)) a₀ := contDiffAt_const.prodMk hψ
  have hψh0 : ((0 : ℝ), ψ a₀) = (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) 0 := by
    simp [hψ0]
  have hψhd : HasFDerivAt (fun a ↦ ((0 : ℝ), ψ a)) ((0 : P →L[ℝ] ℝ).prod (fderiv ℝ ψ a₀)) a₀ :=
    (hasFDerivAt_const _ _).prodMk (hψ.differentiableAt one_ne_zero).hasFDerivAt
  have hΦh : ContDiffAt ℝ 1 (fun z : ℝ × E ↦ (z.1, Φ z.2))
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) t₁) :=
    contDiffAt_fst.prodMk (ContDiffAt.comp (g := Φ) (f := Prod.snd)
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) t₁) hΦ contDiffAt_snd)
  have hΦhd : HasFDerivAt (fun z : ℝ × E ↦ (z.1, Φ z.2))
      ((ContinuousLinearMap.fst ℝ ℝ E).prod
        ((fderiv ℝ Φ (q t₁)).comp (ContinuousLinearMap.snd ℝ ℝ E)))
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) t₁) :=
    hasFDerivAt_fst.prodMk (HasFDerivAt.comp (g := Φ) (f := Prod.snd)
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) t₁)
      (hΦ.differentiableAt one_ne_zero).hasFDerivAt hasFDerivAt_snd)
  have hΦhsurj : Function.Surjective (fderiv ℝ (fun z : ℝ × E ↦ (z.1, Φ z.2))
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) t₁)) := by
    rw [hΦhd.fderiv]
    rintro ⟨a, c⟩
    obtain ⟨b, hb⟩ := hΦsurj c
    exact ⟨(a, b), by simp [hb]⟩
  -- (12.37), (12.45): `Φ̂(J(t₁), q(t₁)) = (J(t₁), 0)` is not an interior point of the image of
  -- the local attainable set, or a cheaper admissible pair would satisfy the boundary conditions
  obtain ⟨ε₁, hε₁, hε₁N⟩ := Metric.eventually_nhds_iff.1 hψN
  obtain ⟨ε₂, hε₂, hε₂N⟩ := Metric.eventually_nhds_iff.1 hΦN
  have hbd : ∃ ε > 0, (fun z : ℝ × E ↦ (z.1, Φ z.2))
      ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) t₁) ∉
        interior ((fun z : ℝ × E ↦ (z.1, Φ z.2)) '' localAttainableSet (Reduction.costExt f φ)
          (univ ×ˢ Ω) (Icc 0 1 ×ˢ U) (fun a ↦ ((0 : ℝ), ψ a)) a₀
          (fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) t₁ ε) := by
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun hint ↦ ?_⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
    obtain ⟨η, hη, hball⟩ := hint
    have hc : (fun z : ℝ × E ↦ (z.1, Φ z.2))
        ((fun t ↦ (∫ r in (0 : ℝ)..t, φ (q r) (ũ r), q t)) t₁) = (cost φ t₁ ũ q, 0) := by
      simp only [hΦ0]; rfl
    rw [hc] at hball
    obtain ⟨zT, ⟨a, w, z, ha, hz, hzq, hzT⟩, hzTΦ⟩ := hball (a := (cost φ t₁ ũ q - η / 2, 0)) (by
      rw [mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg]
      rw [abs_of_pos (by positivity), max_eq_left (by positivity)]
      linarith)
    obtain ⟨hadm, hcost⟩ := Reduction.IsAdmissibleIn.costExt_proj hU hφ hT
      Icc_subset_Ici_self hz
    have hx0 : (z 0).2 = ψ a := by
      simpa using ControlSystem.IsAdmissible.apply_zero hadm.1 hT
    have hzT1 : (z t₁).1 = cost φ t₁ ũ q - η / 2 := by rw [hzT]; exact congrArg Prod.fst hzTΦ
    have hzT2 : Φ (z t₁).2 = 0 := by rw [hzT]; exact congrArg Prod.snd hzTΦ
    have h0N : (z 0).2 ∈ N₀ := by
      rw [hx0]
      exact hε₁N (by rw [dist_eq_norm]; exact ha.trans_le (min_le_left _ _))
    have h1N : (z t₁).2 ∈ N₁ := by
      refine hε₂N ?_ hzT2
      rw [dist_eq_norm]
      exact (norm_snd_le (z t₁ - (∫ r in (0 : ℝ)..t₁, φ (q r) (ũ r), q t₁))).trans_lt
        ((hzq t₁ ⟨hT, le_rfl⟩).trans_le (min_le_right _ _))
    have hadm' : IsAdmissibleIn f Ω U ((fun t ↦ (z t).2) 0) t₁ (fun t ↦ (w t).2)
        (fun t ↦ (z t).2) := by
      simp only [hx0]
      exact hadm
    have := hopt _ _ hadm' h0N h1N
    rw [hzT1] at hcost
    simp only at hcost
    linarith
  obtain ⟨ξ, p, -, hpT, ⟨K, hpL⟩, hp0, hpadj, hpmax, hpψ⟩ := exists_costate_of_boundary
    (isOpen_univ.prod hΩ) (isCompact_Icc.prod hU) (Reduction.isC1On_costExt hf hφ _) ht₁ hext
    hψh hψh0 hΦh hΦhsurj hbd
  obtain ⟨hL, hne, hadj, hmax, hν⟩ :=
    Reduction.costExt_costate hf hφ ht₁ href hpL hp0 hpadj hpmax
  refine ⟨_, _, hL, hadj, hmax, fun t ht h ↦ hne t ht ?_, hν, ?_, fun w hw ↦ ?_⟩
  · rw [Prod.ext_iff] at h ⊢
    exact ⟨h.2, h.1⟩
  · ext α
    have := congrArg (fun L ↦ L α) hpψ
    simpa [hψhd.fderiv] using this
  · have hd := hΦhd.fderiv
    simp only at hd
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, hpT, hd,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      hw]
    exact map_zero ξ

/-- **Agrachev–Sachkov, Theorem 12.5** (authors' draft, p. 183): let `ũ` be an optimal control
in problem (12.49)–(12.52) (`(q(0), q(t₁)) ∈ N ⊆ M × M`, `t₁` fixed, `J(u) → min`). Then all
statements of Theorem 12.4 hold, except its transversality condition (12.34), which is replaced
by `(-λ₀, λ_{t₁}) ⊥ T_{(q̃(0), q̃(t₁))}N` (12.53).

In coordinates, `N` near `(q(0), q(t₁))` through a `C¹` submersion `G` (`G(q(0), q(t₁)) = 0`,
`G⁻¹(0) ⊆ N` near the end points); (12.53) reads `-λ₀(v) + λ_{t₁}(w) = 0` whenever
`G'(v, w) = 0`. (A–S's periodic case is `N = Δ`, giving `λ₀ = λ_{t₁}`.)

Proof (A–S, pp. 183–184): the auxiliary problem on `M × M`, `ẋ = 0`, `q̇ = f_u(q)`, with
`(x(0), q(0)) ∈ Δ` and `(x(t₁), q(t₁)) ∈ N`; Theorem 12.4 (`theorem12_4`, with `ψ(a) = (a, a)`
and `Φ = G`) gives the costate `(η, λ)` with `η̇ = 0`, `η + λ₀ = 0` at `t = 0`, and
`(η_{t₁}, λ_{t₁}) = (-λ₀, λ_{t₁}) ⊥ T N` at `t = t₁`. The pointwise `(λ_t, ν) ≠ 0` comes from
`(η, λ_t, ν) ≠ 0` and the uniqueness for the adjoint equation (if `λ_t = 0 = ν`, then `λ ≡ 0`
and `η = -λ₀ = 0`). -/
theorem theorem12_5 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U)
    (ht₁ : 0 < t₁) {N : Set (E × E)} (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hqN : (q 0, q t₁) ∈ N)
    (hopt : ∀ (u : ℝ → V) (x : ℝ → E), IsAdmissibleIn f Ω U (x 0) t₁ u x → (x 0, x t₁) ∈ N →
      cost φ t₁ ũ q ≤ cost φ t₁ u x)
    {G : E × E → Q} (hG : ContDiffAt ℝ 1 G (q 0, q t₁))
    (hGsurj : Function.Surjective (fderiv ℝ G (q 0, q t₁))) (hG0 : G (q 0, q t₁) = 0)
    (hGN : ∀ᶠ z in 𝓝 (q 0, q t₁), G z = 0 → z ∈ N) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      IsAdjoint f φ ν ũ q t₁ p ∧ IsMaximal f φ ν U ũ q t₁ p ∧
      (∀ t ∈ Icc 0 t₁, (p t, ν) ≠ 0) ∧ ν ≤ 0 ∧
      ∀ v w : E, fderiv ℝ G (q 0, q t₁) (v, w) = 0 → -p 0 v + p t₁ w = 0 := by
  have hT := ht₁.le
  have hũU := href.1.2.1
  have hqΩ := href.2
  -- Theorem 12.4 for the doubled system `ẋ = 0`, `q̇ = f(q, u)` on `E × E`, with
  -- `(x(0), q(0)) ∈ Δ` (parametrized by `a ↦ (a, a)`) and `(x(t₁), q(t₁)) ∈ N` (given by `G`)
  obtain ⟨ν, p, ⟨K, hpL⟩, hpadj, hpmax, hp0, hν, hpψ, hpG⟩ :=
    theorem12_4 (N₀ := {z : E × E | z.1 = z.2}) (N₁ := N) (q := fun t ↦ (q 0, q t))
      (isOpen_univ.prod hΩ) hU (Reduction.isC1On_doubled hf) (Reduction.isC1On_doubledCost hφ)
      ht₁ (Reduction.isAdmissibleIn_doubled href) rfl hqN
      (fun u z hz hz0 hzN ↦ by
        obtain ⟨hc, hadm⟩ := Reduction.IsAdmissibleIn.doubled_proj hz
        have h1 : (z t₁).1 = (z 0).2 := (hc t₁ ⟨hT, le_rfl⟩).trans hz0
        exact hopt u (fun t ↦ (z t).2) hadm (by rw [← h1]; exact hzN))
      (ψ := fun a : E ↦ (a, a)) (a₀ := q 0) (contDiffAt_id.prodMk contDiffAt_id) rfl
      (Eventually.of_forall fun a ↦ rfl) (Φ := G) hG hGsurj hG0 hGN
  -- the costate `(η, λ)` of the doubled system: `η` constant, `λ` the costate of the original one
  obtain ⟨hint, heq⟩ := hpadj
  obtain ⟨h1, h2, h3⟩ := Reduction.adjoint_prod hT hint heq (α := fun _ ↦ 0)
    (β := linearization f ũ q) (μ := fun r ↦ ν • fderiv ℝ (φ · (ũ r)) (q r)) fun r hr ↦ by
      have hl : linearization (Reduction.doubled f) ũ (fun t ↦ (q 0, q t)) r = _ :=
        (Reduction.hasFDerivAt_doubled hf (z := (q 0, q r)) (hqΩ r hr) (hũU r hr)).fderiv
      have hc : fderiv ℝ (Reduction.doubledCost φ · (ũ r)) (q 0, q r) = _ :=
        (Reduction.hasFDerivAt_doubledCost hφ (z := (q 0, q r)) (hqΩ r hr) (hũU r hr)).fderiv
      rw [hl]
      simp only [hc, linearization, ContinuousLinearMap.smul_comp]
  set Pr : StrongDual ℝ (E × E) →L[ℝ] StrongDual ℝ E :=
    (ContinuousLinearMap.inr ℝ E E).precomp ℝ with hPr
  have hadj : IsAdjoint f φ ν ũ q t₁ (fun t ↦ (p t).comp (ContinuousLinearMap.inr ℝ E E)) := by
    refine ⟨?_, fun t ht ↦ ?_⟩
    · simpa using h2
    · simpa using h3 t ht
  -- transversality at `t = 0`: `η + λ₀ = 0`
  have hψd : fderiv ℝ (fun a : E ↦ (a, a)) (q 0) =
      (ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E) :=
    ((hasFDerivAt_id (q 0)).prodMk (hasFDerivAt_id (q 0))).fderiv
  have hη0 : ∀ a, (p 0).comp (ContinuousLinearMap.inl ℝ E E) a =
      -(p 0).comp (ContinuousLinearMap.inr ℝ E E) a := fun a ↦ by
    have := congrArg (fun L ↦ L a) hpψ
    simp only [hψd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, zero_apply] at this
    rw [Reduction.apply_prod] at this
    exact eq_neg_of_add_eq_zero_left this
  refine ⟨ν, fun t ↦ (p t).comp (ContinuousLinearMap.inr ℝ E E),
    ⟨‖Pr‖₊ * K, Pr.lipschitzWith.comp_lipschitzOnWith hpL⟩, hadj, ?_, fun t ht h ↦ ?_, hν,
    fun v w hvw ↦ ?_⟩
  · filter_upwards [hpmax] with t ht u hu
    simpa only [Reduction.controlHamiltonian_doubled] using ht u hu
  · -- nontriviality: if `λ_t = 0` and `ν = 0`, then `λ ≡ 0` (uniqueness), `η = -λ₀ = 0`, so the
    -- costate `(η, λ_t)` of the doubled system vanishes together with `ν`
    rw [Prod.ext_iff] at h
    simp only [Prod.fst_zero, Prod.snd_zero] at h
    obtain ⟨hlam, hν0⟩ := h
    rw [hν0] at hadj
    have hcont : ContinuousOn (fun t ↦ (p t).comp (ContinuousLinearMap.inr ℝ E E)) (Icc 0 t₁) :=
      (Pr.lipschitzWith.comp_lipschitzOnWith hpL).continuousOn
    have hlam0 := Reduction.eq_zero_of_adjoint hU hf hT href hcont hadj ht hlam
    refine hp0 t ht (Prod.ext ?_ hν0)
    refine ContinuousLinearMap.ext fun x ↦ ?_
    rw [show x = (x.1, x.2) from rfl, Reduction.apply_prod, h1 t ht,
      ← h1 0 ⟨le_rfl, hT⟩, hη0, hlam0 0 ⟨le_rfl, hT⟩, hlam0 t ht]
    simp
  · -- transversality at `t = t₁`: `(η, λ_{t₁}) = (-λ₀, λ_{t₁}) ⊥ ker G'`
    have := hpG (v, w) hvw
    rw [Reduction.apply_prod, h1 t₁ ⟨hT, le_rfl⟩, ← h1 0 ⟨le_rfl, hT⟩, hη0] at this
    simp only
    linarith

end Pontryagin
