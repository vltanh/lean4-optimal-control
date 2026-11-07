module

public import OptimalControl.Pontryagin.Geometric

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
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace Pontryagin

open ControlSystem

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
  sorry

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
  sorry

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
`(η_{t₁}, λ_{t₁}) = (-λ₀, λ_{t₁}) ⊥ T N` at `t = t₁`. -/
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
  sorry

end Pontryagin
