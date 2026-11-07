module

public import OptimalControl

/-!
# Solution

Restates the theorems of `OptimalControlChallenge.lean` word for word and proves them from the
library: `Pontryagin.maximum_principle`, Filippov's theorem (`ControlSystem.isCompact_reachableSet`,
`ControlSystem.isCompact_reachableSetLE`) and the existence of optimal controls
(`ControlSystem.exists_optimal_fixedTime`, `ControlSystem.exists_optimal_freeTime`). The library
states the last four with a Borel σ-algebra on `E`, and Filippov's theorem with a bound `M ≥ 0`;
the proofs below supply the σ-algebra, and an empty attainable set when `M < 0`. Palomar's
Comparator checks that these are the Challenge's statements and that their proofs use only the
standard axioms (`comparator.json`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace OptimalControlChallenge

open ControlSystem Pontryagin

/-- **The Pontryagin maximum principle** (Agrachev–Sachkov, Theorem 12.5 with its Remark (1):
free terminal time, integral cost, mixed boundary conditions; for strong local minimizers). If
`(ũ, q)` is a strong local minimizer of `∫₀^T φ(q, u) dt` with free terminal time and
`(q(0), q(T)) ∈ N`, where near `(q(0), q(T))` the set `N` contains the zeros of a `C¹` map `G`
with surjective derivative and `G(q(0), q(T)) = 0`, then there are `ν ≤ 0` and a Lipschitz covector
curve `p` with `(ν, p(t)) ≠ 0` for every `t`, the adjoint equation, the maximum condition and
`H = 0` for almost every `t`, and the transversality condition
`(-p(0), p(T)) ⊥ ker G'(q(0), q(T))`. -/
theorem maximum_principle {E V Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [FiniteDimensional ℝ Q] {Ω : Set E} (hΩ : IsOpen Ω) {U : Set V}
    (hU : IsCompact U) {f : E → V → E} (hf : IsC1On f Ω U) {φ : E → V → ℝ}
    (hφ : IsC1On φ Ω U) {N : Set (E × E)} {T : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    (hmin : IsStrongLocalMinimizer f φ Ω U N T ũ q) {G : E × E → Q}
    (hG : ContDiffAt ℝ 1 G (q 0, q T)) (hGsurj : Function.Surjective (fderiv ℝ G (q 0, q T)))
    (hG0 : G (q 0, q T) = 0) (hGN : ∀ᶠ z in 𝓝 (q 0, q T), G z = 0 → z ∈ N) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), ν ≤ 0 ∧ (∃ K, LipschitzOnWith K p (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) ∧ IsAdjoint f φ ν ũ q T p ∧ IsMaximal f φ ν U ũ q T p ∧
      (∀ᵐ t ∂(volume.restrict (Icc 0 T)), controlHamiltonian f φ ν (q t) (p t) (ũ t) = 0) ∧
      ∀ v w : E, fderiv ℝ G (q 0, q T) (v, w) = 0 → -p 0 v + p T w = 0 :=
  Pontryagin.maximum_principle hΩ hU hf hφ hmin hG hGsurj hG0 hGN

/-- **Filippov's theorem**, fixed terminal time (Agrachev–Sachkov, Theorem 10.1): if `F` is
jointly continuous, `U` is compact, the velocity sets `F(x, U)` are convex and the velocities
along the admissible pairs from `x₀` on `[0, T]` are bounded, the attainable set at time `T ≥ 0`
is compact. -/
theorem isCompact_reachableSet {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MetricSpace V] [MeasurableSpace V] [BorelSpace V]
    {F : E → V → E} {U : Set V} (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hU : IsCompact U) (hconv : ∀ z, Convex ℝ (F z '' U)) {x₀ : E} {T M : ℝ} (hT : 0 ≤ T)
    (hbd : ∀ u x, IsAdmissible F U x₀ T u x → ∀ s ∈ Icc 0 T, ‖F (x s) (u s)‖ ≤ M) :
    IsCompact (reachableSet F U x₀ T) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  rcases le_or_gt 0 M with hM | hM
  · exact ControlSystem.isCompact_reachableSet hF hU hconv hT hM hbd
  · -- With `M < 0` there is no admissible pair: the bound fails at `s = 0`.
    convert isCompact_empty
    refine eq_empty_iff_forall_notMem.2 fun y ⟨u, x, hadm, _⟩ ↦ ?_
    exact (norm_nonneg _).not_gt ((hbd u x hadm 0 ⟨le_rfl, hT⟩).trans_lt hM)

/-- **Filippov's theorem**, times up to `T` (Agrachev–Sachkov, Theorem 10.1): under the same
hypotheses, with the velocities bounded along the admissible pairs from `x₀` on `[0, τ]` for every
`τ ∈ [0, T]`, the union of the attainable sets at the times `τ ∈ [0, T]` is compact. -/
theorem isCompact_reachableSetLE {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MetricSpace V] [MeasurableSpace V] [BorelSpace V]
    {F : E → V → E} {U : Set V} (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hU : IsCompact U) (hconv : ∀ z, Convex ℝ (F z '' U)) {x₀ : E} {T M : ℝ}
    (hbd : ∀ τ ∈ Icc 0 T, ∀ u x, IsAdmissible F U x₀ τ u x → ∀ s ∈ Icc 0 τ,
      ‖F (x s) (u s)‖ ≤ M) :
    IsCompact (reachableSetLE F U x₀ T) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  rcases le_or_gt 0 M with hM | hM
  · exact ControlSystem.isCompact_reachableSetLE hF hU hconv hM hbd
  · -- With `M < 0` there is no admissible pair: the bound fails at `s = 0`.
    convert isCompact_empty
    refine eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
    simp only [reachableSetLE, reachableSet, mem_iUnion, mem_ofPred_eq, exists_prop] at hy
    obtain ⟨τ, hτ, u, x, hadm, _⟩ := hy
    exact (norm_nonneg _).not_gt ((hbd τ hτ u x hadm 0 ⟨le_rfl, hτ.1⟩).trans_lt hM)

/-- **Existence of optimal controls**, fixed terminal time: if `F` and the running cost `φ` are
jointly continuous, `U` is compact, `‖F‖ ≤ M` on `E × U` and the extended velocity sets
`{(F(x, u), φ(x, u)) | u ∈ U}` are convex, then among the admissible pairs on `[0, T]` from `x₀`
to an attainable point `x₁`, one has the least cost `∫₀ᵀ φ(x, u)`. -/
theorem exists_optimal_fixedTime {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MetricSpace V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] {F : E → V → E} {φ : E → V → ℝ} {U : Set V} {x₀ : E} {T : ℝ}
    (hF : Continuous fun p : E × V ↦ F p.1 p.2) (hU : IsCompact U)
    (hφ : Continuous fun p : E × V ↦ φ p.1 p.2)
    (hconv : ∀ z, Convex ℝ ((fun w ↦ (F z w, φ z w)) '' U)) {M : ℝ}
    (hFM : ∀ z, ∀ w ∈ U, ‖F z w‖ ≤ M) (hT : 0 ≤ T) {x₁ : E}
    (h₁ : x₁ ∈ reachableSet F U x₀ T) :
    ∃ u x, IsAdmissible F U x₀ T u x ∧ x T = x₁ ∧
      ∀ u' x', IsAdmissible F U x₀ T u' x' → x' T = x₁ →
        ∫ t in (0 : ℝ)..T, φ (x t) (u t) ≤ ∫ t in (0 : ℝ)..T, φ (x' t) (u' t) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact ControlSystem.exists_optimal_fixedTime hF hU hφ hconv hFM hT h₁

/-- **Existence of optimal controls**, free terminal time: under the hypotheses of
`exists_optimal_fixedTime`, among the admissible pairs from `x₀` to `x₁` on `[0, τ]` with
`τ ∈ [0, T]` (if there is one), one has the least cost `∫₀^τ φ(x, u)`. -/
theorem exists_optimal_freeTime {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MetricSpace V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] {F : E → V → E} {φ : E → V → ℝ} {U : Set V} {x₀ : E} {T : ℝ}
    (hF : Continuous fun p : E × V ↦ F p.1 p.2) (hU : IsCompact U)
    (hφ : Continuous fun p : E × V ↦ φ p.1 p.2)
    (hconv : ∀ z, Convex ℝ ((fun w ↦ (F z w, φ z w)) '' U)) {M : ℝ}
    (hFM : ∀ z, ∀ w ∈ U, ‖F z w‖ ≤ M) {x₁ : E} (h₁ : x₁ ∈ reachableSetLE F U x₀ T) :
    ∃ τ ∈ Icc 0 T, ∃ u x, IsAdmissible F U x₀ τ u x ∧ x τ = x₁ ∧
      ∀ τ' ∈ Icc 0 T, ∀ u' x', IsAdmissible F U x₀ τ' u' x' → x' τ' = x₁ →
        ∫ t in (0 : ℝ)..τ, φ (x t) (u t) ≤ ∫ t in (0 : ℝ)..τ', φ (x' t) (u' t) := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact ControlSystem.exists_optimal_freeTime hF hU hφ hconv hFM h₁

end OptimalControlChallenge

end
