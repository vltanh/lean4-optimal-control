# Sussmann's Noether theorem

How the formalization of Noether's theorem for optimal control relates to its source: the paper's
definitions and results one by one, the readings and departures S1–S8 to which the docstrings
refer, the gaps found in the paper, and the hypotheses of its Theorem 4.1 that the proof does not
use. The [README](../README.md) has the overview; the statement of record and the definitions it
uses are in [DETAILS.md](DETAILS.md#noethers-theorem).

- [The source](#the-source)
- [Result by result](#result-by-result)
- [Readings and departures from Sussmann](#readings-and-departures-from-sussmann)
- [Gaps in Sussmann](#gaps-in-sussmann)
- [Hypotheses of Theorem 4.1 that the proof does not use](#hypotheses-of-theorem-41-that-the-proof-does-not-use)

## The source

H. J. Sussmann, *Symmetries and integrals of motion in optimal control*, in *Geometry in Nonlinear
Control and Differential Inclusions*, Banach Center Publications 32, Institute of Mathematics,
Polish Academy of Sciences, Warszawa, 1995, pp. 379–393 (<https://eudml.org/doc/262687>).

Its Theorem 4.1 (p. 389) is a control version of Noether's theorem: if a Lie algebra acts on the
state space by symmetries of an optimal control system, the momentum map is constant along every
biextremal. The proof (pp. 389–390) applies Theorems 3.1–3.2 (pp. 385–387), on minimizing
trajectories of Hamiltonian families on a symplectic manifold.

Page numbers here and in the docstrings are those of the published paper.

## Result by result

| Sussmann | Lean |
| --- | --- |
| Optimal control system `P = (M, U, f, f⁰)` of class `C¹`, p. 387 | `(Ω, U, f, φ)` with the hypotheses `hΩ`, `hf`, `hφ` of [`Pontryagin.noether`](../OptimalControl/Pontryagin/Noether.lean#L690) |
| The flow `e^{tX}` and its domain, p. 381 | [`Pontryagin.flowMap`](../OptimalControl/Defs.lean#L181), [`Pontryagin.flowDomain`](../OptimalControl/Defs.lean#L174), through [`Pontryagin.IsIntegralCurveIn`](../OptimalControl/Defs.lean#L167); uniqueness: [`Pontryagin.flowMap_eq_of_isIntegralCurveIn`](../OptimalControl/Pontryagin/Noether.lean#L304) |
| Symmetry of `P`, conditions (i)–(ii), p. 389 | [`Pontryagin.IsSymmetry`](../OptimalControl/Defs.lean#L198), [`Pontryagin.PermutesFamily`](../OptimalControl/Defs.lean#L189) |
| The fields `τ(X)`, every `e^{tτ(X)}` of which is a symmetry, p. 389 | [`Pontryagin.IsInfinitesimalSymmetry`](../OptimalControl/Defs.lean#L212); for a field with an explicit flow: [`Pontryagin.isInfinitesimalSymmetry_of_flow`](../OptimalControl/Pontryagin/Noether.lean#L499) |
| Infinitesimal group of symmetries, p. 389 | [`Pontryagin.IsInfinitesimalGroupOfSymmetries`](../OptimalControl/Pontryagin/Noether.lean#L817) |
| `h_X(x, z) = ⟨z, X(x)⟩`, p. 384; the momentum map `μ^τ`, p. 389 | [`Pontryagin.momentum`](../OptimalControl/Defs.lean#L220), [`Pontryagin.momentumMap`](../OptimalControl/Pontryagin/Noether.lean#L824) |
| The Hamiltonian `H^{c,P}_u`, (4.2), p. 388 | [`Pontryagin.controlHamiltonian`](../OptimalControl/Defs.lean#L115), with the sign of S6 |
| Controlled `c`-biextremal, (EAV1)–(EAV3), pp. 388–389 | [`Pontryagin.IsBiextremal`](../OptimalControl/Pontryagin/Noether.lean#L887) |
| Proof of Theorem 3.1, (3.3)–(3.4), pp. 385–386, for the cotangent lift of a symmetry | [`Pontryagin.IsSymmetry.controlHamiltonian_cotangentLift`](../OptimalControl/Pontryagin/Noether.lean#L576), [`Pontryagin.IsInfinitesimalSymmetry.bracket_eq_zero`](../OptimalControl/Pontryagin/Noether.lean#L609) |
| Theorem 4.1, p. 389 | [`Pontryagin.sussmann_theorem4_1`](../OptimalControl/Pontryagin/Noether.lean#L919); for one vector field and any extremal: [`Pontryagin.noether`](../OptimalControl/Pontryagin/Noether.lean#L690) (the statement of record) and [`Pontryagin.noether_momentumMap`](../OptimalControl/Pontryagin/Noether.lean#L840) |
| Theorem 4.1 with the maximum principle, which produces biextremals (p. 389) | [`Pontryagin.maximum_principle_noether`](../OptimalControl/Pontryagin/Noether.lean#L943) |
| An example, not in the paper: rotations of the plane | [`Pontryagin.isInfinitesimalSymmetry_rotation`](../OptimalControl/Pontryagin/Noether.lean#L970), [`Pontryagin.noether_rotation`](../OptimalControl/Pontryagin/Noether.lean#L1006) |

Sections 2–3 of the paper (Noether's theorem for Hamiltonians and for Hamiltonian families on a
symplectic manifold, Theorems 3.1–3.2) are not formalized as such. The proof applies their
argument directly to the cotangent lift of a symmetry (S4). Section 5 (shortest paths with a
curvature bound) is not formalized.

The example is the system `ż = a z + u` on `ℂ ≅ ℝ²`, with `|u| ≤ 1` and the cost
`‖z‖² + ‖u‖²`. The rotations `z ↦ e^{is} z` are symmetries that permute the controls
(`u₁ = e^{is} u`, `u₂ = e^{-is} u`), and the angular momentum `p(i q)` is conserved.

<details>
<summary>The statements in Lean</summary>

With the section variables `{f : E → V → E} {φ : E → V → ℝ} {Ω : Set E} {U : Set V}` and
`{L : Type*} [LieRing L] [LieAlgebra ℝ L]`. The definitions that `noether` uses are in
[DETAILS.md](DETAILS.md#noethers-theorem).

```lean
structure IsInfinitesimalGroupOfSymmetries (f : E → V → E) (φ : E → V → ℝ) (Ω : Set E)
    (U : Set V) (τ : L →ₗ[ℝ] E → E) : Prop where
  map_lie : ∀ X X' : L, ∀ x ∈ Ω, τ ⁅X, X'⁆ x = VectorField.lieBracket ℝ (τ X) (τ X') x
  isInfinitesimalSymmetry : ∀ X : L, IsInfinitesimalSymmetry f φ Ω U (τ X)

def momentumMap (τ : L →ₗ[ℝ] E → E) (x : E) (p : StrongDual ℝ E) : Module.Dual ℝ L :=
  (p : E →ₗ[ℝ] ℝ) ∘ₗ LinearMap.proj x ∘ₗ τ

structure IsBiextremal (f : E → V → E) (φ : E → V → ℝ) (Ω : Set E) (U : Set V) (T : ℝ)
    (ũ : ℝ → V) (q : ℝ → E) (c : ℝ) (ζ : ℝ → StrongDual ℝ E) : Prop where
  isAdmissibleIn : IsAdmissibleIn f Ω U (q 0) T ũ q
  nonneg : 0 ≤ c
  isAdjoint : IsAdjoint f φ c ũ q T ζ
  isMinimal : ∀ᵐ t ∂(volume.restrict (Icc 0 T)), ∀ u ∈ U,
    controlHamiltonian f φ c (q t) (ζ t) (ũ t) ≤ controlHamiltonian f φ c (q t) (ζ t) u
  const : ∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Icc 0 T)),
    controlHamiltonian f φ c (q t) (ζ t) (ũ t) = C
  ne_zero : ∀ t ∈ Icc 0 T, (ζ t, c) ≠ 0

theorem noether_momentumMap (hΩ : IsOpen Ω) (hf : ∀ u ∈ U, ContDiffOn ℝ 1 (f · u) Ω)
    (hφ : ∀ u ∈ U, ContDiffOn ℝ 1 (φ · u) Ω) {τ : L →ₗ[ℝ] E → E}
    (hτ : IsInfinitesimalGroupOfSymmetries f φ Ω U τ) {T ν : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    {p : ℝ → StrongDual ℝ E} (href : IsAdmissibleIn f Ω U (q 0) T ũ q)
    (hadj : IsAdjoint f φ ν ũ q T p) (hmax : IsMaximal f φ ν U ũ q T p) :
    ∀ t ∈ Icc 0 T, momentumMap τ (q t) (p t) = momentumMap τ (q 0) (p 0)

theorem sussmann_theorem4_1 {L : Type*} [LieRing L] [LieAlgebra ℝ L] (hΩ : IsOpen Ω)
    (hf : ∀ u ∈ U, ContDiffOn ℝ 1 (f · u) Ω) (hφ : ∀ u ∈ U, ContDiffOn ℝ 1 (φ · u) Ω)
    {τ : L →ₗ[ℝ] E → E} (hτ : IsInfinitesimalGroupOfSymmetries f φ Ω U τ) {T c : ℝ}
    {ũ : ℝ → V} {q : ℝ → E} {ζ : ℝ → StrongDual ℝ E} (hΞ : IsBiextremal f φ Ω U T ũ q c ζ) :
    ∀ t ∈ Icc 0 T, momentumMap τ (q t) (ζ t) = momentumMap τ (q 0) (ζ 0)

theorem maximum_principle_noether {Ω : Set E} (hΩ : IsOpen Ω) {U : Set V}
    (hU : IsCompact U) {f : E → V → E} (hf : IsC1On f Ω U) {φ : E → V → ℝ}
    (hφ : IsC1On φ Ω U) {N : Set (E × E)} {T : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    (hmin : IsStrongLocalMinimizer f φ Ω U N T ũ q) {G : E × E → Q}
    (hG : ContDiffAt ℝ 1 G (q 0, q T)) (hGsurj : Function.Surjective (fderiv ℝ G (q 0, q T)))
    (hG0 : G (q 0, q T) = 0) (hGN : ∀ᶠ z in 𝓝 (q 0, q T), G z = 0 → z ∈ N) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), ν ≤ 0 ∧ (∃ K, LipschitzOnWith K p (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) ∧ IsAdjoint f φ ν ũ q T p ∧ IsMaximal f φ ν U ũ q T p ∧
      (∀ᵐ t ∂(volume.restrict (Icc 0 T)), controlHamiltonian f φ ν (q t) (p t) (ũ t) = 0) ∧
      (∀ v w : E, fderiv ℝ G (q 0, q T) (v, w) = 0 → -p 0 v + p T w = 0) ∧
      ∀ Y : E → E, IsInfinitesimalSymmetry f φ Ω U Y →
        ∀ t ∈ Icc 0 T, momentum Y (q t) (p t) = momentum Y (q 0) (p 0)
```

</details>

## Readings and departures from Sussmann

The docstrings refer to these readings and departures.

- S1. Coordinates, as D1 of [AGRACHEV_SACHKOV.md](AGRACHEV_SACHKOV.md). The manifold `M` is an
  open set `Ω` of a finite-dimensional real normed space `E`, and `T*M = Ω × E*`. Vector fields
  are maps `E → E` and covectors are elements of `StrongDual ℝ E`. The adjoint equation (4.3) is
  read as Hamilton's equations `ẋ = ∂H/∂z = f_u(x)`, `ż = -∂H/∂x`, in the integral form
  `IsAdjoint`; the state part is the control system.
- S2. Regularity (a generalization). The diffeomorphisms `σ` and the vector fields `τ(X)` are
  `C¹` instead of `C^∞`. The system keeps Sussmann's class `C¹`: `f(·, u)` and `φ(·, u)` are `C¹`
  on `Ω` for each `u ∈ U`. `U` need not be compact, unlike in the maximum principle. The
  package's regularity `IsC1On` implies class `C¹`
  ([`ControlSystem.IsC1On.contDiffOn`](../OptimalControl/Pontryagin/Noether.lean#L205)).
- S3. Flows. `e^{sY}` is defined through the integral curves of `Y` in `Ω` on the interval
  between `0` and `s`, in Carathéodory form. Its domain `D_s` is the set of their initial
  points, and its value is chosen among them. For `Y` of class `C¹` they agree
  (`flowMap_eq_of_isIntegralCurveIn`): near the curves, `Y` equals a globally bounded `C¹`
  field, whose solutions are unique.
- S4. The route of the proof (a departure). Sussmann applies Theorems 3.1–3.2 to the Hamiltonian
  vector field of `h_{τ(X)}`, whose flow is the cotangent lift of `e^{sτ(X)}`. For a `C¹` field
  `Y` that Hamiltonian field `(x, z) ↦ (Y(x), -z ∘ DY(x))` is only continuous. Its flow is still
  unique, since the system is triangular, and it is the cotangent lift; the route through it is
  not taken because of its cost. The proof differentiates the cotangent lift
  `ρ_s(x, z) = (e^{sY}(x), z ∘ (De^{sY}(x))⁻¹)` itself, with Sussmann's steps:
  `H_u ∘ ρ_s = H_{u₂}`, a maximum at `s = 0` ((3.3)), a vanishing derivative ((3.4)), and
  `d/dt h_Y(Ξ(t)) = {H_u, h_Y}(Ξ(t)) = 0`.
- S5. Biextremals (a generalization). `noether` assumes only the adjoint equation and the
  maximum condition, for any real multiplier `ν`. Neither `c ≥ 0`, nor the constancy of the
  minimized Hamiltonian in (4.4), nor the nontriviality (EAV3), nor optimality is used, and the
  time may be fixed or free. Sussmann's statement, with his biextremals, is
  `sussmann_theorem4_1`.
- S6. Sign convention. Sussmann minimizes `H^c_u = ⟨z, f_u⟩ + c f⁰_u` with `c ≥ 0`; the package
  maximizes `H^ν_u = ⟨p, f_u⟩ + ν φ_u` with `ν ≤ 0`. The change `(p, ν) = (-ζ, -c)` translates
  one into the other (`controlHamiltonian_neg`, `IsAdjoint.neg`, `IsBiextremal.isMaximal_neg`)
  and changes the sign of the momentum (`momentumMap_neg`).
- S7. Admissibility. Sussmann's `P`-admissible controls (p. 388) are read as the package's
  admissible pairs on `[0, T]` (`IsAdmissibleIn`: measurable controls with values in `U`,
  Carathéodory trajectories in `Ω`); the system is autonomous, so the interval may start at `0`.
  In `noether` and `sussmann_theorem4_1` the control values form any type `V` with a σ-algebra.
  With the trivial σ-algebra `⊥` every control is measurable, so Sussmann's arbitrary set `U` and
  arbitrary controls are covered. The reading drops his Lipschitz–Carathéodory condition on
  `F^η` (a generalization): the only uniqueness the proof uses is that of the integral curves of
  `Y`. `maximum_principle_noether` keeps the setting of the maximum principle (`V`
  finite-dimensional with its Borel σ-algebra, `U` compact).
- S8. The Lie algebra. `L` is any real Lie algebra (finite-dimensional or not, as in Sussmann),
  `L*` its algebraic dual `Module.Dual ℝ L`, and `τ : L →ₗ[ℝ] (E → E)` satisfies
  `τ⁅X, X'⁆ = [τ X, τ X']` on `Ω`, with Mathlib's bracket `VectorField.lieBracket`
  (`[V, W] = DW · V - DV · W`). With this bracket the natural action `τ(A)x = Ax` of a Lie
  algebra of matrices is an anti-homomorphism, and `τ(A)x = -Ax` satisfies the condition. The
  condition is Sussmann's and is not used: the theorem is the one-field form applied to each
  `τ(X)`, and the linearity of `τ` makes `μ^τ` take values in `L*`.

### Further readings

- Sussmann asks, for every `u ∈ U`, for `u₁, u₂ ∈ U` with (i) and (ii). `PermutesFamily` asks for
  `u₁` and for `u₂` separately, which is the same condition.
- The inverse of a symmetry `σ : V₁ → V₂` is `Function.invFunOn σ V₁`, which is the inverse of
  `σ` on `V₂`.
- The constant minimum of (4.4) is read as a constant `C` with `H = C` for almost every `t`.
- The invariance of the cost, condition (ii), cannot be dropped. Take `M = ℝ`, `U = [-1, 1]`,
  `f_u(x) = u`, `f⁰_u(x) = x` and the translations `x ↦ x + s`, which satisfy (i) with
  `u₁ = u₂ = u` but not (ii). The minimizer of `∫₀² x dt` with `x(0) = x(2) = 1` is
  `x(t) = |1 - t|`. With `c = 1` and `ζ(t) = 1 - t` it is a biextremal (the minimized
  Hamiltonian is `0`), and its momentum `ζ(t)` is not constant. (Checked by hand, not in Lean.)

## Gaps in Sussmann

- **p. 390, the proof of Theorem 4.1.** It asserts without proof ("it is easy to see") that
  `T*(τ)` is an infinitesimal group of symmetries of `H^c(P)`. That is: the flow of the
  Hamiltonian field of `h_{τ(X)}` is the cotangent lift `ρ_s` of `e^{sτ(X)}`, and every `ρ_s`
  is a symmetry of the Hamiltonian family (`H_u ∘ ρ_s = H_{u₂}` and `H_{u₁} ∘ ρ_s = H_u`). The
  formalization proves the half that the theorem uses: `H_u ∘ ρ_s = H_{u₂}`, from the `u₂`
  halves of (i)–(ii)
  ([`IsSymmetry.controlHamiltonian_cotangentLift`](../OptimalControl/Pontryagin/Noether.lean#L576)),
  and the derivative of `ρ_s` at `s = 0`
  ([`hasDerivAt_fderiv_flowMap_zero`](../OptimalControl/Pontryagin/Noether.lean#L427)). It
  neither identifies `ρ_s` with the flow of the Hamiltonian field (S4) nor proves the `u₁` half.
- **pp. 380–381 and 388, the symplectic form.** The symplectic form of `T*M` is not specified.
  With `Ω(H⃗, X) = ⟨dH, X⟩`, the state part of (4.3) is `γ̇ = f_u(γ)` only for
  `Ω = Σ dxᵢ ∧ dzᵢ`. The formalization reads (4.3) as Hamilton's equations (S1).
- **Typos.** On p. 384, "`µ(x, z) = ⟨z, θ(X)(x)⟩`" should read "`µ(x, z)(X) = ⟨z, τ(X)(x)⟩`"
  (`θ(X)` is a field on `T*M`). On p. 385, the sets `H⃗(x)` and `H⃗_min(x)` lie in `T_x N`, not
  in `T_x M`.

## Hypotheses of Theorem 4.1 that the proof does not use

- `c ≥ 0`, the constancy of the minimized Hamiltonian in (4.4) and the nontriviality (EAV3)
  (pp. 388–389; S5).
- The smoothness of `τ(X)` and of the symmetries beyond `C¹` (S2).
- The bracket condition on the action, `τ⁅X, X'⁆ = [τ X, τ X']` (S8).
- The `u₁` halves of conditions (i)–(ii): only the `u₂` halves enter the cotangent lift.
- The measurability of the controls and the Lipschitz–Carathéodory condition (S7).
