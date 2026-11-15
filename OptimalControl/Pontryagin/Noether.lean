module

public import OptimalControl.Pontryagin.MaximumPrinciple
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Symmetries and integrals of motion: Noether's theorem for optimal control

H. J. Sussmann, *Symmetries and integrals of motion in optimal control*, in *Geometry in
Nonlinear Control and Differential Inclusions*, Banach Center Publications 32, Institute of
Mathematics, Polish Academy of Sciences, Warszawa, 1995, pp. 379–393. Its Theorem 4.1 (p. 389),
the control-theoretic Noether theorem: if a Lie algebra acts on the state space by infinitesimal
symmetries of an optimal control system, the momentum map is constant along every biextremal.
Page numbers are those of the published paper.

Every statement is proved: no `sorry`, and no axiom beyond Lean's standard ones.

## Sussmann's objects (§4, pp. 387–389) and their forms here

An optimal control system `P = (M, U, f, f⁰)` is a family of vector fields `f_u` and functions
(a Lagrangian) `f⁰_u` on `M`, indexed by a set `U`. Here `M` is an open subset `Ω` of a
finite-dimensional real normed space `E`, `U ⊆ V` is any set of control values, `f : E → V → E`
and `φ : E → V → ℝ` (`φ = f⁰`).

* A **symmetry** (`IsSymmetry`, p. 389) is a diffeomorphism `σ : V₁ → V₂` of open subsets of `M`
  such that for every `u ∈ U` there are `u₁, u₂ ∈ U` with (i) `dσ(x) f_u(x) = f_{u₁}(σ(x))` and
  `dσ(x) f_{u₂}(x) = f_u(σ(x))` for `x ∈ V₁`, and (ii) `f⁰_{u₁} ∘ σ = f⁰_u` and
  `f⁰_u ∘ σ = f⁰_{u₂}`. So `σ` and `σ⁻¹` map the family `{(f_u, f⁰_u) | u ∈ U}` into itself,
  possibly permuting the controls (`PermutesFamily`), and the cost is invariant.
* The **flow** `e^{sY} : D_s → D_{-s}` of a vector field `Y` on `Ω` (`flowMap`, `flowDomain`),
  through integral curves in `Ω` (`IsIntegralCurveIn`).
* An **infinitesimal symmetry** (`IsInfinitesimalSymmetry`; the vector fields `τ(X)` of p. 389) is
  a vector field `Y` every `e^{sY}`, `s ∈ ℝ`, of which is a symmetry.
* An **infinitesimal group of symmetries** (`IsInfinitesimalGroupOfSymmetries`, p. 389) is a
  smooth action `τ : L → Γ^∞(TM)` of a real Lie algebra `L` (a Lie algebra homomorphism, p. 380)
  every `τ(X)` of which is an infinitesimal symmetry.
* The **momentum map** (`momentumMap`, p. 389) `μ^τ : T*M → L*`, `μ^τ(x, z)(X) = ⟨z, τ(X)(x)⟩`;
  for one vector field, the function `h_Y(x, z) = ⟨z, Y(x)⟩` (`momentum`, p. 384).
* A **controlled `c`-biextremal** (`IsBiextremal`, (EAV1)–(EAV3), pp. 388–389): an admissible
  pair `(γ, η)` with a multiplier `(ζ, c)`, `c ≥ 0`, satisfying the adjoint equation (4.3), the
  minimization condition (4.4) with a constant minimum, and `(ζ(t), c) ≠ (0, 0)`.

## Main statements

* `Pontryagin.noether` (one vector field): along every pair `(q, p)` with the adjoint equation and
  the maximum condition of the maximum principle (`IsAdjoint`, `IsMaximal`, any multiplier `ν`),
  `t ↦ ⟨p(t), Y(q(t))⟩` is constant, for every infinitesimal symmetry `Y`.
* `Pontryagin.noether_momentumMap`: the momentum map `μ^τ(q(t), p(t))` is constant.
* `Pontryagin.sussmann_theorem4_1`: Sussmann's Theorem 4.1 as he states it, for biextremals.
* `Pontryagin.maximum_principle_noether`: the multiplier of `Pontryagin.maximum_principle` can be
  taken with every momentum `⟨p(t), Y(q(t))⟩` constant.
* `Pontryagin.isInfinitesimalSymmetry_of_flow`, the form of the definition that applications
  use: a field `Y` with an explicit global flow `Φ` on `Ω` whose maps satisfy (i)–(ii) is an
  infinitesimal symmetry. Example: the rotations of the plane
  (`Pontryagin.isInfinitesimalSymmetry_rotation`), which permute the controls, and the
  conservation of the angular momentum `⟨p, i q⟩` (`Pontryagin.noether_rotation`). A bridge from
  (i)–(ii) alone, for the local flow of an arbitrary `C¹` field (the diffeomorphism clauses of
  `IsSymmetry` on `D_s`), is a possible extension.

## Readings and departures from Sussmann

* S1 (coordinates, as D1 of the package). `M` is an open set `Ω ⊆ E`, `T*M = Ω × E*`, vector fields
  are maps `E → E`, covectors are `StrongDual ℝ E`. The adjoint equation (4.3) is read as
  Hamilton's equations `ẋ = ∂H/∂z = f_u(x)`, `ż = -∂H/∂x` (the state part is the control system),
  in the integral form `IsAdjoint`.
* S2 (regularity; a generalization). Sussmann's "smooth" (`C^∞`) is replaced by `C¹` for the
  diffeomorphisms `σ` and the vector fields `τ(X)` (his vector fields are in `Γ^∞(TM)`). The
  system keeps his class `C¹`: `f(·, u)` and `φ(·, u)` are `C¹` on `Ω` for each `u ∈ U`. `U` is
  any subset of `V` (no compactness, unlike the maximum principle). The package's regularity
  `ControlSystem.IsC1On` implies class `C¹` (`ControlSystem.IsC1On.contDiffOn`).
* S3 (flows). `e^{sY}` is defined through the integral curves of `Y` in `Ω` on the interval
  between `0` and `s`, in the Carathéodory form of `ControlSystem.IsSolution`
  (`isIntegralCurveIn_iff_isSolution`); its domain `D_s` is the set of initial points of such
  curves, and the value is chosen among them. For `Y` of class `C¹` they agree
  (`flowMap_eq_of_isIntegralCurveIn`): near the curves `Y` equals a globally bounded `C¹` field
  (`ControlSystem.IsC1On.exists_cutoff`), whose solutions are unique
  (`ControlSystem.IsSolution.eqOn`).
* S4 (the route of the proof; a departure). Sussmann derives Theorem 4.1 from Theorems 3.1–3.2 on
  Hamiltonian families on a symplectic manifold, applied to the Hamiltonian vector field of
  `h_{τ(X)}`, whose flow is the cotangent lift of `e^{sτ(X)}`. For a `C¹` field `Y` that
  Hamiltonian field `(x, z) ↦ (Y(x), -z ∘ DY(x))` is only continuous, but its flow is still
  unique, since the system is triangular (`ẋ = Y(x)` has unique solutions, and then
  `ż = -z ∘ DY(x(t))` is linear with continuous coefficients), and it is the cotangent lift. The
  route through it is therefore possible; it is not taken because of its cost (the existence,
  uniqueness and identification of a second flow). The proof differentiates the cotangent lift
  `ρ_s(x, z) = (e^{sY}(x), z ∘ (De^{sY}(x))⁻¹)` itself. The steps are Sussmann's:
  `H_u ∘ ρ_s = H_{u₂}` (the symmetry of the Hamiltonian family), a maximum at `s = 0` ((3.3)),
  the vanishing derivative ((3.4)), and `d/dt h_Y(Ξ(t)) = {H_u, h_Y}(Ξ(t)) = 0`.
* S5 (biextremals; a generalization). `noether` assumes only the adjoint equation and the maximum
  condition, for any real multiplier: neither `c ≥ 0`, nor the constancy of the minimized
  Hamiltonian in (4.4), nor the nontriviality (EAV3), nor optimality is used, and the time may be
  fixed or free. Sussmann's statement with his definition of biextremals is
  `sussmann_theorem4_1`.
* S6 (sign convention). Sussmann minimizes `H^c_u = ⟨z, f_u⟩ + c f⁰_u` with `c ≥ 0`, the package
  maximizes `H^ν_u = ⟨p, f_u⟩ + ν φ_u` with `ν ≤ 0`; `(p, ν) = (-ζ, -c)` translates one into the
  other (`controlHamiltonian_neg`, `IsAdjoint.neg`, `IsBiextremal.isMaximal_neg`) and changes the
  sign of the momentum (`momentumMap_neg`).
* S7 (admissibility). Sussmann's `P`-admissible controls (p. 388) are read as the package's
  admissible pairs (`IsAdmissibleIn`: measurable controls with values in `U`, Carathéodory
  trajectories in `Ω`) on `[0, T]` (the system is autonomous, so the interval `[a, b]` may start
  at `0`). This reading restricts Sussmann's arbitrary set `U` to a subset of a
  finite-dimensional space `V` and the controls `ũ` to Borel-measurable ones, a restriction that
  the proof does not use (it uses only that `q` is a Carathéodory solution in `Ω` with
  `ũ(t) ∈ U`). It drops his Lipschitz–Carathéodory condition on `F^η` (measurable in `t`,
  locally Lipschitz in `x`, with local integrable bounds), a generalization: the only uniqueness
  the proof uses is that of the integral curves of `Y`.
* S8 (the Lie algebra). `L` is any real Lie algebra (not necessarily finite-dimensional, as in
  Sussmann), `L*` its algebraic dual `Module.Dual ℝ L`, and `τ : L →ₗ[ℝ] (E → E)` satisfies
  `τ⁅X, X'⁆ = [τ X, τ X']` on `Ω`, with Mathlib's bracket `VectorField.lieBracket`
  (`[V, W] = DW · V - DV · W`). With this bracket the natural action `τ(A)x = Ax` of a Lie algebra
  of matrices (`⁅A, B⁆ = AB - BA`) is an anti-homomorphism, `τ⁅A, B⁆ = -[τ A, τ B]`; the action
  `τ(A)x = -Ax` satisfies `map_lie`. The bracket condition `map_lie` is Sussmann's and is not
  used: the theorem is the one-vector-field form applied to each `τ(X)`, and the linearity of `τ`
  makes `μ^τ` `L*`-valued.

## Proof (Sussmann, Theorem 3.1, p. 385, and Theorem 4.1, p. 389), in coordinates

Fix an infinitesimal symmetry `Y`, `σ_s = e^{sY}`, and a pair `(q, p)` with the adjoint equation
and the maximum condition, for a multiplier `ν`.

1. Cotangent lift (`IsSymmetry.controlHamiltonian_cotangentLift`; the half of Sussmann's "it is
   easy to see that `T*(τ)` is an infinitesimal group of symmetries of `H^c(P)`", p. 390, that the
   theorem uses). For a symmetry `σ` and `u ∈ U`, the `u₂` of (i)–(ii) gives
   `H(σ(x), p ∘ dσ(x)⁻¹, u) = H(x, p, u₂)` on `V₁`, for every covector `p`; `dσ(x)` is invertible
   (`IsSymmetry.isUnit_fderiv`).
2. The flow at `s = 0` (`eventually_mem_flowDomain`, `hasDerivAt_flowMap_zero`,
   `hasDerivAt_fderiv_flowMap_zero`). Near `x ∈ Ω`, `Y` equals a globally bounded `C¹` field `g`
   (`ControlSystem.IsC1On.exists_cutoff`), whose flow `P_{0 → s}` is, for `s` near `0` and near
   `x`, an integral curve of `Y` in `Ω`, hence `e^{sY}` (`flowMap_eq_of_isIntegralCurveIn`). So
   `x ∈ D_s` for `s` near `0`, `σ_s(x) = x + ∫₀ˢ g(P_{0 → r}(x)) dr` has derivative `Y(x)` at
   `s = 0`, and `Dσ_s(x)` is the resolvent of the variational equation
   (`ControlSystem.hasFDerivAt_flow`), with derivative `DY(x)` at `s = 0`
   (`ControlSystem.stateTransition_eq_integral`).
3. The infinitesimal identity ((3.3)–(3.4); `IsInfinitesimalSymmetry.bracket_eq_zero`): if `u`
   maximizes `H(x, p, ·)` on `U`, then `s ↦ H(σ_s(x), p ∘ Dσ_s(x)⁻¹, u) = H(x, p, u₂(s))` has a
   maximum at `s = 0`, so its derivative `⟨p, [Y, f_u](x)⟩ + ν Dφ_u(x) Y(x)` vanishes (step 2 and
   the derivative `-DY(x)` of the inverse at `id`). This is the Poisson bracket `{h_Y, H_u}(x, p)`.
4. Integral of motion (`noether`): `g(t) = ⟨p(t), Y(q(t))⟩` is absolutely continuous on `[0, T]`,
   its increments being dominated by those of `∫ (M ‖ṗ‖ + B L ‖q̇‖)`, with `M` and `L` a bound and
   a Lipschitz constant of `Y` on `q([0, T])` (from a cut-off) and `B` a bound of `p`. At almost
   every `t` (where `q̇ = f(q, ũ)`, `ṗ = -p ∘ ∂ₓf(q, ũ) - ν ∂ₓφ(q, ũ)` and the maximum condition
   holds), `ġ(t) = -(⟨p, [Y, f_{ũ(t)}](q)⟩ + ν Dφ_{ũ(t)}(q) Y(q)) = 0` by step 3. So `g` is
   constant (`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`).

The Lie-algebra form, Sussmann's form and the corollary of the maximum principle follow
(`noether_momentumMap`, `sussmann_theorem4_1`, `maximum_principle_noether`).

## Gaps in Sussmann

* p. 390: the proof of Theorem 4.1 asserts without proof ("it is easy to see") that `T*(τ)` is an
  infinitesimal group of symmetries of `H^c(P)`: that the flow of the Hamiltonian field of
  `h_{τ(X)}` is the cotangent lift `ρ_s` of `e^{sτ(X)}`, and that every `ρ_s` is a symmetry of the
  Hamiltonian family (`H_u ∘ ρ_s = H_{u₂}` and `H_{u₁} ∘ ρ_s = H_u`, from the two halves of (i)
  and (ii)). Steps 1–2 prove the half that the theorem uses: `H_u ∘ ρ_s = H_{u₂}`, from the `u₂`
  halves of (i)–(ii), and the derivative of `ρ_s` at `s = 0`. They neither identify `ρ_s` with the
  flow of the Hamiltonian field (S4) nor prove the `u₁` half.
* pp. 380–381, 388: the symplectic form of `T*M` is not specified; with `Ω(H⃗, X) = ⟨dH, X⟩` the
  state part of (4.3) is `γ̇ = f_u(γ)` for `Ω = Σ dxᵢ ∧ dzᵢ` only. Read as Hamilton's equations
  (S1).
* p. 384: "`µ(x, z) = ⟨z, θ(X)(x)⟩`" should read "`µ(x, z)(X) = ⟨z, τ(X)(x)⟩`" (`θ(X)` is a field
  on `T*M`); p. 385: the sets `H⃗(x)`, `H⃗_min(x)` lie in `T_x N`, not `T_x M`.

## Hypotheses of Theorem 4.1 that the proof does not use

* `c ≥ 0`, the constancy of the minimized Hamiltonian in (4.4) and the nontriviality (EAV3)
  (pp. 388–389; S5);
* the smoothness of `τ(X)` and of the symmetries beyond `C¹` (S2);
* the bracket condition on the action `τ`, `τ⁅X, X'⁆ = [τ X, τ X']` (S8).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped Interval NNReal

namespace ControlSystem

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Bridge from the package's regularity to Sussmann's class `C¹` (S2): on an open set, a system
with A–S's regularity (`IsC1On`) has `f(·, u)` of class `C¹` for every `u ∈ U`.

Proof: `contDiffOn_succ_iff_fderiv_of_isOpen`, with the derivative continuous along
`x ↦ (x, u)` (`IsC1On.continuousOn_fderiv`). -/
theorem IsC1On.contDiffOn {f : E → V → F} {Ω : Set E} {U : Set V} (hf : IsC1On f Ω U)
    (hΩ : IsOpen Ω) {u : V} (hu : u ∈ U) : ContDiffOn ℝ 1 (f · u) Ω := by
  rw [← zero_add (1 : WithTop ℕ∞), contDiffOn_succ_iff_fderiv_of_isOpen hΩ, contDiffOn_zero]
  refine ⟨fun x hx ↦ (hf.differentiableAt x hx u hu).differentiableWithinAt, by simp, ?_⟩
  exact hf.continuousOn_fderiv.comp (continuousOn_id.prodMk continuousOn_const) fun x hx ↦
    ⟨hx, hu⟩

end ControlSystem

namespace Pontryagin

open ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

omit [FiniteDimensional ℝ E] in
/-- A field `Y` of class `C¹` on an open set, read as a control system `(y, v) ↦ Y y` that does
not depend on the control, has A–S's regularity `IsC1On` (so that the package's cut-off
`IsC1On.exists_cutoff` and flow theory apply to it). -/
private theorem isC1On_of_contDiffOn {W : Type*} [NormedAddCommGroup W] {Y : E → E}
    {Ω : Set E} (hΩ : IsOpen Ω) (hY : ContDiffOn ℝ 1 Y Ω) (U : Set W) :
    IsC1On (fun x (_ : W) ↦ Y x) Ω U where
  continuousOn := hY.continuousOn.comp continuousOn_fst fun _ hp ↦ hp.1
  differentiableAt _ hx _ _ := (hY.contDiffAt (hΩ.mem_nhds hx)).differentiableAt one_ne_zero
  continuousOn_fderiv :=
    (hY.continuousOn_fderiv_of_isOpen hΩ le_rfl).comp continuousOn_fst fun _ hp ↦ hp.1

/-! ### Flows of vector fields on `Ω` -/

section Flow

/-- An integral curve of the vector field `Y` in `Ω` from `x` on the interval between `0` and `s`,
in the Carathéodory form of `ControlSystem.IsSolution` for the autonomous system `y' = Y(y)`:
`γ` is continuous on `[[0, s]]`, `r ↦ Y(γ(r))` is integrable there,
`γ(r) = x + ∫₀ʳ Y(γ(ρ)) dρ` and `γ(r) ∈ Ω` for `r ∈ [[0, s]]`. For `Y` continuous on `Ω` these
are the classical integral curves (`γ` is `C¹` with `γ' = Y ∘ γ`). -/
def IsIntegralCurveIn (Y : E → E) (Ω : Set E) (x : E) (s : ℝ) (γ : ℝ → E) : Prop :=
  ContinuousOn γ [[0, s]] ∧ IntervalIntegrable (fun r ↦ Y (γ r)) volume 0 s ∧
    (∀ r ∈ [[0, s]], γ r = x + ∫ ρ in (0 : ℝ)..r, Y (γ ρ)) ∧ ∀ r ∈ [[0, s]], γ r ∈ Ω

/-- The domain `D_s` of the time-`s` map `e^{sY}` of the flow of `Y` on `Ω` (Sussmann, p. 381:
"the domain of `e^{tX}` ..., which need not be the whole manifold"): the points of `Ω` from which
an integral curve of `Y` in `Ω` runs on the interval between `0` and `s` (S3). -/
def flowDomain (Y : E → E) (Ω : Set E) (s : ℝ) : Set E :=
  {x | ∃ γ, IsIntegralCurveIn Y Ω x s γ}

open Classical in
/-- The time-`s` map `e^{sY}` of the flow of `Y` on `Ω` (S3): the value at time `s` of an integral
curve of `Y` in `Ω` from `x`, chosen among them (they agree for `Y` of class `C¹`,
`flowMap_eq_of_isIntegralCurveIn`); `x` itself outside `flowDomain Y Ω s`. -/
noncomputable def flowMap (Y : E → E) (Ω : Set E) (s : ℝ) (x : E) : E :=
  if h : ∃ γ, IsIntegralCurveIn Y Ω x s γ then h.choose s else x

variable {Y : E → E} {Ω : Set E}

omit [FiniteDimensional ℝ E] in
/-- An integral curve of `Y` in `Ω` is a Carathéodory solution (`ControlSystem.IsSolution`) of
the system `y' = Y(y)`, read with any control `u` (on which it does not depend), that stays in
`Ω`. This is what lets the package's flow theory apply to `flowMap`. -/
theorem isIntegralCurveIn_iff_isSolution {W : Type*} (u : ℝ → W) {x : E} {s : ℝ}
    {γ : ℝ → E} :
    IsIntegralCurveIn Y Ω x s γ ↔
      IsSolution (fun y (_ : W) ↦ Y y) u 0 x 0 s γ ∧ ∀ r ∈ [[0, s]], γ r ∈ Ω := by
  simp only [IsIntegralCurveIn, IsSolution, and_assoc]

omit [FiniteDimensional ℝ E] in
private theorem IsIntegralCurveIn.apply_zero {x : E} {s : ℝ} {γ : ℝ → E}
    (h : IsIntegralCurveIn Y Ω x s γ) : γ 0 = x := by
  simpa using h.2.2.1 0 left_mem_uIcc

omit [FiniteDimensional ℝ E] in
/-- `D_s ⊆ Ω`: an integral curve starts at `γ(0) = x ∈ Ω`. -/
theorem flowDomain_subset (Y : E → E) (Ω : Set E) (s : ℝ) : flowDomain Y Ω s ⊆ Ω :=
  fun _ ⟨_, hγ⟩ ↦ hγ.apply_zero ▸ hγ.2.2.2 0 left_mem_uIcc

omit [FiniteDimensional ℝ E] in
/-- `e^{0 · Y}` is the identity, everywhere: on `[[0, 0]] = {0}` every integral curve from `x`
has `γ(0) = x`, and outside `flowDomain` the value is `x` by definition. -/
theorem flowMap_zero (Y : E → E) (Ω : Set E) : flowMap Y Ω 0 = id := by
  funext x
  rw [flowMap]
  split_ifs with h
  · exact h.choose_spec.apply_zero
  · rfl

omit [FiniteDimensional ℝ E] in
/-- `D_0 = Ω`: the constant curve `x` is an integral curve on `[[0, 0]]`. -/
theorem flowDomain_zero (Y : E → E) (Ω : Set E) : flowDomain Y Ω 0 = Ω := by
  refine (flowDomain_subset Y Ω 0).antisymm fun x hx ↦ ⟨fun _ ↦ x, continuousOn_const,
    IntervalIntegrable.refl, fun r hr ↦ ?_, fun _ _ ↦ hx⟩
  rw [uIcc_self, mem_singleton_iff] at hr
  simp [hr]

omit [FiniteDimensional ℝ E] in
private theorem isSolution_restrict {W : Type*} {g : E → W → E} {u : ℝ → W} {s a b c d : ℝ}
    {x : E} {γ : ℝ → E} (h : IsSolution g u s x a b γ) (hcd : [[c, d]] ⊆ [[a, b]]) :
    IsSolution g u s x c d γ :=
  ⟨h.1.mono hcd, h.2.1.mono_set hcd, fun t ht ↦ h.2.2 t (hcd ht)⟩

omit [FiniteDimensional ℝ E] in
/-- A solution of `y' = g(y, 0)` from time `0` is a solution of `y' = h(y, 0)` if `g` and `h`
agree along it. -/
private theorem isSolution_congr_field {g h : E → ℝ → E} {a b : ℝ} {x : E} {γ : ℝ → E}
    (hγ : IsSolution g (fun _ ↦ 0) 0 x a b γ) (hgh : ∀ r ∈ [[a, b]], g (γ r) 0 = h (γ r) 0)
    (h0 : (0 : ℝ) ∈ [[a, b]]) : IsSolution h (fun _ ↦ 0) 0 x a b γ := by
  refine ⟨hγ.1, hγ.2.1.congr fun r hr ↦ hgh r (uIoc_subset_uIcc hr), fun t ht ↦ ?_⟩
  rw [hγ.2.2 t ht]
  congr 1
  exact intervalIntegral.integral_congr fun r hr ↦ hgh r (uIcc_subset_uIcc h0 ht hr)

/-- **Uniqueness**: for `Y` of class `C¹` on the open set `Ω`, the chosen value `e^{sY}(x)` is
the value at `s` of every integral curve of `Y` in `Ω` from `x` on `[[0, s]]`. (This is what makes
the definition by choice the flow; it is also how an explicit flow is identified,
`isInfinitesimalSymmetry_of_flow`.)

Proof: cut `Y` off near the compact union `K` of the images of the chosen curve and of `γ`
(`ControlSystem.IsC1On.exists_cutoff` for `(y, v) ↦ Y y`, `U = {0}`); both curves are solutions
of the cut-off system (`isIntegralCurveIn_iff_isSolution`), which has unique solutions
(`ControlSystem.IsSolution.eqOn`). -/
theorem flowMap_eq_of_isIntegralCurveIn (hΩ : IsOpen Ω) (hY : ContDiffOn ℝ 1 Y Ω) {x : E}
    {s : ℝ} {γ : ℝ → E} (hγ : IsIntegralCurveIn Y Ω x s γ) : flowMap Y Ω s x = γ s := by
  have hex : ∃ γ, IsIntegralCurveIn Y Ω x s γ := ⟨γ, hγ⟩
  rw [flowMap, dite_eq_left hex]
  have hγ₁ := hex.choose_spec
  have hK : IsCompact (hex.choose '' [[0, s]] ∪ γ '' [[0, s]]) :=
    (isCompact_uIcc.image_of_continuousOn hγ₁.1).union (isCompact_uIcc.image_of_continuousOn hγ.1)
  have hKΩ : hex.choose '' [[0, s]] ∪ γ '' [[0, s]] ⊆ Ω :=
    union_subset (image_subset_iff.2 hγ₁.2.2.2) (image_subset_iff.2 hγ.2.2.2)
  obtain ⟨δ, -, -, g, M, L, hg, hgY⟩ :=
    (isC1On_of_contDiffOn hΩ hY ({0} : Set ℝ)).exists_cutoff hΩ isCompact_singleton hK hKΩ
  have hsol : ∀ c : ℝ → E, IsIntegralCurveIn Y Ω x s c →
      (∀ r ∈ [[0, s]], c r ∈ hex.choose '' [[0, s]] ∪ γ '' [[0, s]]) →
      IsSolution g (fun _ ↦ 0) 0 x (0 ⊓ s) (0 ⊔ s) c := fun c hc hcK ↦
    isSolution_restrict (isSolution_congr_field
      ((isIntegralCurveIn_iff_isSolution (fun _ ↦ (0 : ℝ))).1 hc).1
      (fun r hr ↦ (hgY _ (self_subset_cthickening _ (hcK r hr)) 0 rfl).symm) left_mem_uIcc)
      (uIcc_of_le inf_le_sup).le
  have hu : IsControlOn (fun _ ↦ (0 : ℝ)) {0} (0 ⊓ s) (0 ⊔ s) :=
    ⟨aestronglyMeasurable_const, fun _ _ ↦ rfl⟩
  exact IsSolution.eqOn hg.isLipschitzSystem hu left_mem_uIcc
    (hsol _ hγ₁ fun r hr ↦ Or.inl ⟨r, hr, rfl⟩) (hsol γ hγ fun r hr ↦ Or.inr ⟨r, hr, rfl⟩)
    right_mem_uIcc

/-- The local structure of the flow: near `x ∈ Ω`, a cut-off `g` of `Y` (a bounded `C¹` system,
`ControlSystem.IsC1On.exists_cutoff`) equals `Y` on `ball x r`, and for `|s| < ε` its flow
`P_{0 → ·}` from every `y ∈ ball x r` is an integral curve of `Y` in `Ω` on `[[0, s]]` (it stays in
`closedBall x (2 r) ⊆ Ω`, `ControlSystem.norm_flow_sub_flow_time_le`). -/
private theorem exists_cutoff_flow (hΩ : IsOpen Ω) (hY : ContDiffOn ℝ 1 Y Ω) {x : E}
    (hx : x ∈ Ω) :
    ∃ (g : E → ℝ → E) (M L : ℝ≥0) (r ε : ℝ), IsBoundedC1System g {0} M L ∧ 0 < r ∧ 0 < ε ∧
      ε ≤ 1 ∧ (∀ y ∈ ball x r, g y 0 = Y y) ∧ ∀ s ∈ Ioo (-ε) ε, ∀ y ∈ ball x r,
        IsIntegralCurveIn Y Ω y s (fun t ↦ flow g (fun _ ↦ 0) 0 t y) := by
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  have hr : 0 < ρ / 3 := by positivity
  have hKΩ : closedBall x (2 * (ρ / 3)) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hρΩ
  obtain ⟨δ, -, -, g, M, L, hg, hgY⟩ := (isC1On_of_contDiffOn hΩ hY ({0} : Set ℝ)).exists_cutoff
    hΩ isCompact_singleton (isCompact_closedBall x _) hKΩ
  have hgK : ∀ y ∈ closedBall x (2 * (ρ / 3)), g y 0 = Y y := fun y hy ↦
    hgY y (self_subset_cthickening _ hy) 0 rfl
  have hM : (0 : ℝ) < M + 1 := by positivity
  refine ⟨g, M, L, ρ / 3, min 1 (ρ / 3 / (M + 1)), hg, hr, lt_min one_pos (by positivity),
    min_le_left _ _, fun y hy ↦ hgK y (closedBall_subset_closedBall (by linarith)
    (ball_subset_closedBall hy)), fun s hs y hy ↦ ?_⟩
  have hu : IsControlOn (fun _ ↦ (0 : ℝ)) {0} (-1) 1 :=
    ⟨aestronglyMeasurable_const, fun _ _ ↦ rfl⟩
  have h01 : (0 : ℝ) ∈ Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
  have hsol := isSolution_flow hg.isLipschitzSystem hu h01 y
  have hts : ∀ t ∈ [[0, s]], |t| ≤ min 1 (ρ / 3 / (M + 1)) := fun t ht ↦ by
    rw [abs_le]
    rcases mem_uIcc.1 ht with h | h <;> constructor <;> linarith [hs.1, hs.2]
  have hsub : [[0, s]] ⊆ Icc (-1) 1 := fun t ht ↦ abs_le.1 ((hts t ht).trans (min_le_left _ _))
  have hsub' : [[0, s]] ⊆ [[-1, 1]] := by rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hmem : ∀ t ∈ [[0, s]], flow g (fun _ ↦ 0) 0 t y ∈ closedBall x (2 * (ρ / 3)) := by
    intro t ht
    have h1 := norm_flow_sub_flow_time_le hg.isLipschitzSystem hu (M := M)
      (fun z v hv ↦ hg.norm_le z v hv) h01 (hsub ht) h01 y
    rw [flow_self, sub_zero] at h1
    have h2 : (M : ℝ) * |t| ≤ ρ / 3 := by
      calc (M : ℝ) * |t| ≤ (M + 1) * (ρ / 3 / (M + 1)) :=
            mul_le_mul (by linarith) ((hts t ht).trans (min_le_right _ _)) (abs_nonneg _) hM.le
        _ = ρ / 3 := by field_simp
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_closedBall, dist_eq_norm]
    calc ‖flow g (fun _ ↦ 0) 0 t y - x‖ ≤ ‖flow g (fun _ ↦ 0) 0 t y - y‖ + ‖y - x‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (ρ / 3) := by linarith
  exact (isIntegralCurveIn_iff_isSolution (fun _ ↦ (0 : ℝ))).2 ⟨isSolution_congr_field
    (isSolution_restrict hsol hsub') (fun t ht ↦ hgK _ (hmem t ht)) left_mem_uIcc,
    fun t ht ↦ hKΩ (hmem t ht)⟩

/-- `s ↦ c + ∫₀ˢ G` has derivative `G(0)` at `0` for `G` continuous on `[-1, 1]`. -/
private theorem hasDerivAt_add_integral_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {G : ℝ → F} (hG : ContinuousOn G (Icc (-1) 1)) (c : F) :
    HasDerivAt (fun s ↦ c + ∫ r in (0 : ℝ)..s, G r) (G 0) 0 :=
  (intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
    ((hG.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo 0
      ⟨by norm_num, by norm_num⟩)
    (hG.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num)))).const_add c

/-- **Local existence**: every point of `Ω` lies in `D_s` for `s` near `0`.

Proof: the flow of a cut-off of `Y` near `x` is an integral curve of `Y` in `Ω` on `[[0, s]]` for
`|s|` small (it stays in a ball in `Ω` where the cut-off equals `Y`). -/
theorem eventually_mem_flowDomain (hΩ : IsOpen Ω) (hY : ContDiffOn ℝ 1 Y Ω) {x : E}
    (hx : x ∈ Ω) : ∀ᶠ s in 𝓝 (0 : ℝ), x ∈ flowDomain Y Ω s := by
  obtain ⟨g, M, L, r, ε, -, hr, hε, -, -, hint⟩ := exists_cutoff_flow hΩ hY hx
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hε) hε] with s hs
  exact ⟨_, hint s hs x (mem_ball_self hr)⟩

/-- The orbit `s ↦ e^{sY}(x)` has velocity `Y(x)` at `s = 0`.

Proof: near `s = 0`, `e^{sY}(x) = P_{0 → s}(x) = x + ∫₀ˢ g(P_{0 → r}(x)) dr` for a cut-off `g`
of `Y` (`flowMap_eq_of_isIntegralCurveIn`), with a continuous integrand equal to `Y(x)` at `0`
(`intervalIntegral.integral_hasDerivAt_right`). -/
theorem hasDerivAt_flowMap_zero (hΩ : IsOpen Ω) (hY : ContDiffOn ℝ 1 Y Ω) {x : E}
    (hx : x ∈ Ω) : HasDerivAt (fun s ↦ flowMap Y Ω s x) (Y x) 0 := by
  obtain ⟨g, M, L, r, ε, hg, hr, hε, hε1, hgY, hint⟩ := exists_cutoff_flow hΩ hY hx
  have hu : IsControlOn (fun _ ↦ (0 : ℝ)) {0} (-1) 1 :=
    ⟨aestronglyMeasurable_const, fun _ _ ↦ rfl⟩
  have h01 : (0 : ℝ) ∈ Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
  have hI : [[(-1 : ℝ), 1]] = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hsol := isSolution_flow hg.isLipschitzSystem hu h01 x
  have hc : ContinuousOn (fun t ↦ flow g (fun _ ↦ 0) 0 t x) (Icc (-1) 1) := hI ▸ hsol.1
  have hd := hasDerivAt_add_integral_zero (G := fun r ↦ g (flow g (fun _ ↦ 0) 0 r x) 0)
    (hg.isC1On.continuousOn.comp (hc.prodMk continuousOn_const) fun _ _ ↦ ⟨mem_univ _, rfl⟩) x
  have hG0 : g (flow g (fun _ ↦ 0) 0 0 x) 0 = Y x := by
    rw [flow_self]; exact hgY x (mem_ball_self hr)
  rw [hG0] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hε) hε] with s hs
  rw [flowMap_eq_of_isIntegralCurveIn hΩ hY (hint s hs x (mem_ball_self hr))]
  exact hsol.2.2 s (hI ▸ ⟨by linarith [hs.1], by linarith [hs.2]⟩)

/-- **The variational equation at `s = 0`**: `s ↦ D(e^{sY})(x)` has derivative `DY(x)` at
`s = 0` (and value `id` there, `flowMap_zero`). This is the derivative of the flow that
Sussmann's cotangent lift needs (Step 2 of the module docstring).

Proof, by the package's flow theory: near `x` and for small `s`, `e^{sY} = P_{0 → s}`, the flow of
a cut-off `g` of `Y` (`flowMap_eq_of_isIntegralCurveIn`), so `D(e^{sY})(x) = R(0, s)`, the
resolvent of `ξ' = DY(P_{0 → r}(x)) ξ` (`ControlSystem.hasFDerivAt_flow`);
`R(0, s) = id + ∫₀ˢ A(r) ∘ R(0, r) dr` (`ControlSystem.stateTransition_eq_integral`) with a
continuous integrand equal to `DY(x)` at `0`. -/
theorem hasDerivAt_fderiv_flowMap_zero (hΩ : IsOpen Ω) (hY : ContDiffOn ℝ 1 Y Ω) {x : E}
    (hx : x ∈ Ω) :
    HasDerivAt (fun s ↦ fderiv ℝ (flowMap Y Ω s) x) (fderiv ℝ Y x) 0 := by
  obtain ⟨g, M, L, r, ε, hg, hr, hε, hε1, hgY, hint⟩ := exists_cutoff_flow hΩ hY hx
  have hu : IsControlOn (fun _ ↦ (0 : ℝ)) {0} (-1) 1 :=
    ⟨aestronglyMeasurable_const, fun _ _ ↦ rfl⟩
  have h01 : (0 : ℝ) ∈ Icc (-1) 1 := ⟨by norm_num, by norm_num⟩
  have hI : [[(-1 : ℝ), 1]] = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hc : ContinuousOn (fun t ↦ flow g (fun _ ↦ 0) 0 t x) (Icc (-1) 1) :=
    hI ▸ (isSolution_flow hg.isLipschitzSystem hu h01 x).1
  set A : ℝ → E →L[ℝ] E := fun t ↦ fderiv ℝ (g · 0) (flow g (fun _ ↦ 0) 0 t x) with hA
  have hAc : ContinuousOn A (Icc (-1) 1) :=
    hg.isC1On.continuousOn_fderiv.comp (hc.prodMk continuousOn_const) fun _ _ ↦
      ⟨mem_univ _, rfl⟩
  have hAm : AEStronglyMeasurable A (volume.restrict (Icc (-1) 1)) :=
    hAc.aestronglyMeasurable measurableSet_Icc
  have hAK : ∀ t ∈ Icc (-1 : ℝ) 1, ‖A t‖ ≤ L := fun t _ ↦ hg.norm_fderiv_le _ 0 rfl
  have hR := (stateTransition_eq_integral hAm hAK h01).2
  have hRc : ContinuousOn (stateTransition A 0) (Icc (-1) 1) :=
    (lipschitzOnWith_stateTransition_right hAm hAK h01).continuousOn
  have hd := hasDerivAt_add_integral_zero (G := fun r ↦ (A r).comp (stateTransition A 0 r))
    (hAc.clm_comp hRc) (ContinuousLinearMap.id ℝ E)
  have hA0 : (A 0).comp (stateTransition A 0 0) = fderiv ℝ Y x := by
    rw [stateTransition_self, ContinuousLinearMap.comp_id, hA]
    dsimp only
    rw [flow_self]
    exact Filter.EventuallyEq.fderiv_eq
      (eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr)) hgY)
  rw [hA0] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hε) hε] with s hs
  have hs1 : s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have heq : flowMap Y Ω s =ᶠ[𝓝 x] flow g (fun _ ↦ 0) 0 s := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with y hy
    exact flowMap_eq_of_isIntegralCurveIn hΩ hY (hint s hs y hy)
  rw [heq.fderiv_eq, (hasFDerivAt_flow hg hu h01 hs1 x).fderiv]
  exact hR s hs1

end Flow

/-! ### Symmetries of an optimal control system -/

section Symmetry

/-- Conditions (i)–(ii) of Sussmann's definition of a symmetry (p. 389), for a map `σ` on `V₁`:
for every `u ∈ U` there is `u₁ ∈ U` with `dσ(x) f_u(x) = f_{u₁}(σ(x))` and
`f⁰_{u₁}(σ(x)) = f⁰_u(x)` on `V₁` (`σ` maps `(f_u, f⁰_u)` to `(f_{u₁}, f⁰_{u₁})`), and there is
`u₂ ∈ U` with `dσ(x) f_{u₂}(x) = f_u(σ(x))` and `f⁰_u(σ(x)) = f⁰_{u₂}(x)` on `V₁` (`σ⁻¹` maps
`(f_u, f⁰_u)` to `(f_{u₂}, f⁰_{u₂})`). The controls may be permuted; the cost is invariant. -/
def PermutesFamily (f : E → V → E) (φ : E → V → ℝ) (U : Set V) (σ : E → E) (V₁ : Set E) :
    Prop :=
  (∀ u ∈ U, ∃ u₁ ∈ U, ∀ x ∈ V₁, fderiv ℝ σ x (f x u) = f (σ x) u₁ ∧ φ (σ x) u₁ = φ x u) ∧
    ∀ u ∈ U, ∃ u₂ ∈ U, ∀ x ∈ V₁, fderiv ℝ σ x (f x u₂) = f (σ x) u ∧ φ (σ x) u = φ x u₂

/-- **A symmetry of the optimal control system `(Ω, U, f, φ)`** (Sussmann, p. 389): a
diffeomorphism `σ : V₁ → V₂` between open subsets of `Ω`, here of class `C¹` (S2: `σ` maps `V₁`
bijectively onto `V₂`, is `C¹` on `V₁`, and its inverse is `C¹` on `V₂`), satisfying (i)–(ii)
(`PermutesFamily`). -/
structure IsSymmetry (f : E → V → E) (φ : E → V → ℝ) (Ω : Set E) (U : Set V) (σ : E → E)
    (V₁ V₂ : Set E) : Prop where
  isOpen_left : IsOpen V₁
  isOpen_right : IsOpen V₂
  left_subset : V₁ ⊆ Ω
  right_subset : V₂ ⊆ Ω
  bijOn : BijOn σ V₁ V₂
  contDiffOn : ContDiffOn ℝ 1 σ V₁
  contDiffOn_invFunOn : ContDiffOn ℝ 1 (Function.invFunOn σ V₁) V₂
  permutesFamily : PermutesFamily f φ U σ V₁

/-- **An infinitesimal symmetry** of `(Ω, U, f, φ)`: a vector field `Y` on `Ω`, here of class `C¹`
(Sussmann: smooth; S2), every time-`s` map `e^{sY} : D_s → D_{-s}` of which, `s ∈ ℝ`, is a
symmetry (Sussmann, p. 389: "every diffeomorphism `e^{tτ(X)}` is a symmetry of `P`"). -/
structure IsInfinitesimalSymmetry (f : E → V → E) (φ : E → V → ℝ) (Ω : Set E) (U : Set V)
    (Y : E → E) : Prop where
  contDiffOn : ContDiffOn ℝ 1 Y Ω
  isSymmetry : ∀ s : ℝ,
    IsSymmetry f φ Ω U (flowMap Y Ω s) (flowDomain Y Ω s) (flowDomain Y Ω (-s))

variable {f : E → V → E} {φ : E → V → ℝ} {Ω : Set E} {U : Set V} {σ : E → E} {V₁ V₂ : Set E}

/-- An explicit flow `Φ` of `Y` that preserves `Ω` gives integral curves: `r ↦ Φ r x`, `x ∈ Ω`,
is an integral curve of `Y` in `Ω` on every `[[0, s]]` (fundamental theorem of calculus). -/
theorem isIntegralCurveIn_of_flow {Y : E → E} (hY : ContDiffOn ℝ 1 Y Ω) (Φ : ℝ → E → E)
    (hΦΩ : ∀ s, ∀ x ∈ Ω, Φ s x ∈ Ω) (hΦ0 : ∀ x ∈ Ω, Φ 0 x = x)
    (hΦd : ∀ x ∈ Ω, ∀ s, HasDerivAt (fun r ↦ Φ r x) (Y (Φ s x)) s) {x : E} (hx : x ∈ Ω)
    (s : ℝ) : IsIntegralCurveIn Y Ω x s (fun r ↦ Φ r x) := by
  have hc : Continuous fun r ↦ Φ r x :=
    continuous_iff_continuousAt.2 fun r ↦ (hΦd x hx r).continuousAt
  have hYc : Continuous fun r ↦ Y (Φ r x) :=
    hY.continuousOn.comp_continuous hc fun r ↦ hΦΩ r x hx
  refine ⟨hc.continuousOn, hYc.intervalIntegrable _ _, fun r _ ↦ ?_, fun r _ ↦ hΦΩ r x hx⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ρ _ ↦ hΦd x hx ρ)
    (hYc.intervalIntegrable _ _), hΦ0 x hx]
  abel

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- **Explicit-flow bridge**: a global flow `Φ` of `Y` on `Ω` (`Φ s` maps `Ω` into itself,
`Φ 0 = id`, `∂ₛΦ(s, x) = Y(Φ(s, x))`, `Φ (-s) ∘ Φ s = id` on `Ω`, every `Φ s` of class `C¹` on
`Ω`) whose maps all satisfy (i)–(ii) on `Ω` makes `Y` an infinitesimal symmetry. This is the form
applications need: the flow of a symmetry group is usually known in closed form (rotations,
translations, scalings), and then `D_s = Ω`, `e^{sY} = Φ s`
(`flowMap_eq_of_isIntegralCurveIn`), and the diffeomorphism clauses of `IsSymmetry` follow from
`Φ (-s) = (Φ s)⁻¹`. (A bridge from (i)–(ii) alone, for the flow of an arbitrary `C¹` field on
`D_s`, would need the openness of `D_s` and the smoothness of `e^{sY}` on all of it; it is a
possible extension.) -/
theorem isInfinitesimalSymmetry_of_flow (hΩ : IsOpen Ω) {Y : E → E} (hY : ContDiffOn ℝ 1 Y Ω)
    (Φ : ℝ → E → E) (hΦΩ : ∀ s, ∀ x ∈ Ω, Φ s x ∈ Ω) (hΦ0 : ∀ x ∈ Ω, Φ 0 x = x)
    (hΦd : ∀ x ∈ Ω, ∀ s, HasDerivAt (fun r ↦ Φ r x) (Y (Φ s x)) s)
    (hΦinv : ∀ s, ∀ x ∈ Ω, Φ (-s) (Φ s x) = x) (hΦc : ∀ s, ContDiffOn ℝ 1 (Φ s) Ω)
    (hperm : ∀ s, PermutesFamily f φ U (Φ s) Ω) : IsInfinitesimalSymmetry f φ Ω U Y := by
  have hcurve : ∀ {x}, x ∈ Ω → ∀ s, IsIntegralCurveIn Y Ω x s (fun r ↦ Φ r x) :=
    fun hx s ↦ isIntegralCurveIn_of_flow hY Φ hΦΩ hΦ0 hΦd hx s
  have hdom : ∀ s, flowDomain Y Ω s = Ω := fun s ↦
    (flowDomain_subset Y Ω s).antisymm fun x hx ↦ ⟨_, hcurve hx s⟩
  have hmap : ∀ s, ∀ x ∈ Ω, flowMap Y Ω s x = Φ s x := fun s x hx ↦
    flowMap_eq_of_isIntegralCurveIn hΩ hY (hcurve hx s)
  have hΦinv' : ∀ s, ∀ y ∈ Ω, Φ s (Φ (-s) y) = y := fun s y hy ↦ by
    simpa using hΦinv (-s) y hy
  have hbij : ∀ s, BijOn (flowMap Y Ω s) Ω Ω := fun s ↦ by
    refine ⟨fun x hx ↦ (hmap s x hx).symm ▸ hΦΩ s x hx, fun x hx y hy hxy ↦ ?_, fun y hy ↦ ?_⟩
    · rw [hmap s x hx, hmap s y hy] at hxy
      rw [← hΦinv s x hx, hxy, hΦinv s y hy]
    · exact ⟨Φ (-s) y, hΦΩ _ y hy, by rw [hmap s _ (hΦΩ _ y hy), hΦinv' s y hy]⟩
  have hfd : ∀ s, ∀ x ∈ Ω, fderiv ℝ (flowMap Y Ω s) x = fderiv ℝ (Φ s) x := fun s x hx ↦
    Filter.EventuallyEq.fderiv_eq (eventually_of_mem (hΩ.mem_nhds hx) (hmap s))
  refine ⟨hY, fun s ↦ ?_⟩
  rw [hdom s, hdom (-s)]
  refine ⟨hΩ, hΩ, subset_rfl, subset_rfl, hbij s, (hΦc s).congr (hmap s), ?_, ?_⟩
  · refine (hΦc (-s)).congr fun y hy ↦ ?_
    have hmem : Function.invFunOn (flowMap Y Ω s) Ω y ∈ Ω :=
      Function.invFunOn_mem ((hbij s).surjOn hy)
    calc Function.invFunOn (flowMap Y Ω s) Ω y
        = Φ (-s) (Φ s (Function.invFunOn (flowMap Y Ω s) Ω y)) := (hΦinv s _ hmem).symm
      _ = Φ (-s) y := by rw [← hmap s _ hmem, (hbij s).invOn_invFunOn.2 hy]
  · obtain ⟨h1, h2⟩ := hperm s
    refine ⟨fun u hu ↦ ?_, fun u hu ↦ ?_⟩
    · obtain ⟨u₁, hu₁, h⟩ := h1 u hu
      exact ⟨u₁, hu₁, fun x hx ↦ by rw [hfd s x hx, hmap s x hx]; exact h x hx⟩
    · obtain ⟨u₂, hu₂, h⟩ := h2 u hu
      exact ⟨u₂, hu₂, fun x hx ↦ by rw [hfd s x hx, hmap s x hx]; exact h x hx⟩

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- The derivative of a symmetry is invertible on `V₁`.

Proof: `σ⁻¹ := Function.invFunOn σ V₁` satisfies `σ⁻¹ ∘ σ = id` near `x` and `σ ∘ σ⁻¹ = id`
near `σ(x)` (`Set.BijOn.invOn_invFunOn`, `V₁` and `V₂` open); the chain rule gives
`D(σ⁻¹)(σ(x)) ∘ Dσ(x) = id` and `Dσ(x) ∘ D(σ⁻¹)(σ(x)) = id`. -/
theorem IsSymmetry.isUnit_fderiv (hσ : IsSymmetry f φ Ω U σ V₁ V₂) {x : E} (hx : x ∈ V₁) :
    IsUnit (fderiv ℝ σ x) := by
  set τ := Function.invFunOn σ V₁
  have hinv := hσ.bijOn.invOn_invFunOn
  have hσx : σ x ∈ V₂ := hσ.bijOn.mapsTo hx
  have hτσ : τ (σ x) = x := hinv.1 hx
  have hdσ : HasFDerivAt σ (fderiv ℝ σ x) x :=
    ((hσ.contDiffOn.contDiffAt (hσ.isOpen_left.mem_nhds hx)).differentiableAt
      one_ne_zero).hasFDerivAt
  have hdτ : HasFDerivAt τ (fderiv ℝ τ (σ x)) (σ x) :=
    ((hσ.contDiffOn_invFunOn.contDiffAt (hσ.isOpen_right.mem_nhds hσx)).differentiableAt
      one_ne_zero).hasFDerivAt
  have h1 : (fderiv ℝ τ (σ x)).comp (fderiv ℝ σ x) = ContinuousLinearMap.id ℝ E :=
    (hdτ.comp x hdσ).unique ((hasFDerivAt_id x).congr_of_eventuallyEq
      (eventually_of_mem (hσ.isOpen_left.mem_nhds hx) fun y hy ↦ hinv.1 hy))
  have h2 : (fderiv ℝ σ x).comp (fderiv ℝ τ (σ x)) = ContinuousLinearMap.id ℝ E :=
    ((hτσ.symm ▸ hdσ : HasFDerivAt σ (fderiv ℝ σ x) (τ (σ x))).comp (σ x) hdτ).unique
      ((hasFDerivAt_id (σ x)).congr_of_eventuallyEq
        (eventually_of_mem (hσ.isOpen_right.mem_nhds hσx) fun y hy ↦ hinv.2 hy))
  exact ⟨⟨fderiv ℝ σ x, fderiv ℝ τ (σ x), h2, h1⟩, rfl⟩

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- **The cotangent lift of a symmetry is a symmetry of the Hamiltonian family**, the half of the
claim that the theorem uses (Sussmann, proof of Theorem 4.1, p. 390: "it is easy to see that
`T*(τ)` is an infinitesimal group of symmetries of `H^c(P)`", stated without proof; Step 1 of the
module docstring). For `ρ(x, p) = (σ(x), p ∘ dσ(x)⁻¹)` and `u ∈ U`, the `u₂` of (i)–(ii) gives
`H_u ∘ ρ = H_{u₂}` on `T*V₁`: `H(σ(x), p ∘ dσ(x)⁻¹, u) = H(x, p, u₂)` for `x ∈ V₁` and every
covector `p`, for every multiplier `ν`. (The other half, `H_{u₁} ∘ ρ = H_u` from the `u₁` halves of
(i)–(ii), is not needed.)

Proof: `dσ(x) f(x, u₂) = f(σ(x), u)` and the invertibility of `dσ(x)`
(`IsSymmetry.isUnit_fderiv`) give `dσ(x)⁻¹ f(σ(x), u) = f(x, u₂)`; with `φ(σ(x), u) = φ(x, u₂)`
this is the identity. -/
theorem IsSymmetry.controlHamiltonian_cotangentLift (hσ : IsSymmetry f φ Ω U σ V₁ V₂) (ν : ℝ)
    {u : V} (hu : u ∈ U) :
    ∃ u₂ ∈ U, ∀ x ∈ V₁, ∀ p : StrongDual ℝ E,
      controlHamiltonian f φ ν (σ x) (p.comp (Ring.inverse (fderiv ℝ σ x))) u =
        controlHamiltonian f φ ν x p u₂ := by
  obtain ⟨u₂, hu₂, h⟩ := hσ.permutesFamily.2 u hu
  refine ⟨u₂, hu₂, fun x hx p ↦ ?_⟩
  obtain ⟨hf, hφ⟩ := h x hx
  have hinv : Ring.inverse (fderiv ℝ σ x) (f (σ x) u) = f x u₂ := by
    rw [← hf]
    change (Ring.inverse (fderiv ℝ σ x) * fderiv ℝ σ x) (f x u₂) = f x u₂
    rw [Ring.inverse_mul_cancel _ (hσ.isUnit_fderiv hx), one_apply_eq_self]
  simp only [controlHamiltonian, ContinuousLinearMap.comp_apply, hinv, hφ]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- **Sussmann's (3.3)–(3.4)** in coordinates (Step 3 of the module docstring): if `Y` is an
infinitesimal symmetry and `u ∈ U` maximizes `H(x, p, ·)` on `U`, then the Poisson bracket
`{h_Y, H_u}(x, p) = ⟨p, [Y, f_u](x)⟩ + ν Dφ_u(x) Y(x)` vanishes, `[Y, f_u] = Df_u · Y - DY · f_u`
(`VectorField.lieBracket`). Only `f(·, u)` and `φ(·, u)` differentiable at `x` are needed.

Proof, following the proof of Theorem 3.1 (pp. 385–386): for `s` near `0`, `x ∈ D_s`
(`eventually_mem_flowDomain`), and the cotangent lift of `σ_s = e^{sY}`
(`IsSymmetry.controlHamiltonian_cotangentLift`) gives `u₂(s) ∈ U` with
`h(s) := H(σ_s(x), p ∘ Dσ_s(x)⁻¹, u) = H(x, p, u₂(s)) ≤ H(x, p, u) = h(0)`: `h` has a local
maximum at `0`. Its derivative there is `p(Df_u(x) Y(x) - DY(x) f_u(x)) + ν Dφ_u(x) Y(x)`
(`hasDerivAt_flowMap_zero`, `hasDerivAt_fderiv_flowMap_zero` and the derivative `-DY(x)` of
`Ring.inverse` at `id`, `hasFDerivAt_ringInverse`), so it vanishes
(`IsLocalMax.hasDerivAt_eq_zero`).

Departure from the paper (S4): Sussmann differentiates `H_u` along the flow of the Hamiltonian
field of `h_Y`; the proof differentiates it along the cotangent lift of `e^{sY}`, which is that
flow but is not identified with it here, because of the cost of that identification. -/
theorem IsInfinitesimalSymmetry.bracket_eq_zero (hΩ : IsOpen Ω) {Y : E → E}
    (hY : IsInfinitesimalSymmetry f φ Ω U Y) {x : E} (hx : x ∈ Ω) {u : V} (hu : u ∈ U)
    (hfu : DifferentiableAt ℝ (f · u) x) (hφu : DifferentiableAt ℝ (φ · u) x) {ν : ℝ}
    {p : StrongDual ℝ E}
    (hmax : ∀ v ∈ U, controlHamiltonian f φ ν x p v ≤ controlHamiltonian f φ ν x p u) :
    p (VectorField.lieBracket ℝ Y (f · u) x) + ν * fderiv ℝ (φ · u) x (Y x) = 0 := by
  have hσ0 : flowMap Y Ω 0 x = x := by rw [flowMap_zero]; rfl
  have hD0 : fderiv ℝ (flowMap Y Ω 0) x = 1 := by rw [flowMap_zero, fderiv_id]; rfl
  -- the local maximum at `s = 0`
  have hloc : IsLocalMax (fun s ↦ p (Ring.inverse (fderiv ℝ (flowMap Y Ω s) x)
      (f (flowMap Y Ω s x) u)) + ν * φ (flowMap Y Ω s x) u) 0 := by
    filter_upwards [eventually_mem_flowDomain hΩ hY.contDiffOn hx] with s hs
    obtain ⟨u₂, hu₂, hH⟩ := (hY.isSymmetry s).controlHamiltonian_cotangentLift ν hu
    have h0 := hH x hs p
    simp only [controlHamiltonian, ContinuousLinearMap.comp_apply] at h0
    rw [hσ0, hD0, Ring.inverse_one, one_apply_eq_self, h0]
    exact hmax u₂ hu₂
  -- its derivative at `s = 0`
  have hσd := hasDerivAt_flowMap_zero hΩ hY.contDiffOn hx
  have hinv : HasDerivAt (fun s ↦ Ring.inverse (fderiv ℝ (flowMap Y Ω s) x))
      (-fderiv ℝ Y x) 0 := by
    have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (E →L[ℝ] E)ˣ)).comp_hasDerivAt_of_eq 0
      (hasDerivAt_fderiv_flowMap_zero hΩ hY.contDiffOn hx) (by rw [hD0, Units.val_one])
    refine h.congr_deriv ?_
    simp
  have hfd : HasDerivAt (fun s ↦ f (flowMap Y Ω s x) u) (fderiv ℝ (f · u) x (Y x)) 0 :=
    hfu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hσd hσ0.symm
  have hφd : HasDerivAt (fun s ↦ φ (flowMap Y Ω s x) u) (fderiv ℝ (φ · u) x (Y x)) 0 :=
    hφu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hσd hσ0.symm
  have hid := hinv.clm_apply hfd
  rw [hσ0, hD0, Ring.inverse_one, one_apply_eq_self] at hid
  have h := IsLocalMax.hasDerivAt_eq_zero hloc
    ((p.hasFDerivAt.comp_hasDerivAt 0 hid).add (hφd.const_mul ν))
  rw [neg_apply, neg_add_eq_sub] at h
  exact h

end Symmetry

/-! ### Momentum and the Noether theorem -/

section Noether

/-- The momentum of a vector field `Y`, `h_Y(x, p) = ⟨p, Y(x)⟩` on `T*Ω = Ω × E*` (Sussmann,
p. 384: "every vector field `X` gives rise to a smooth function `h_X` on `T*M`"). -/
def momentum (Y : E → E) (x : E) (p : StrongDual ℝ E) : ℝ :=
  p (Y x)

variable {f : E → V → E} {φ : E → V → ℝ} {Ω : Set E} {U : Set V}

/-- A function whose increments are dominated by those of an absolutely continuous real function,
`dist (g x) (g y) ≤ G y - G x` for `x ≤ y` in `[[a, b]]`, is absolutely continuous on `[[a, b]]`.
(Mathlib proves the absolute continuity of an interval integral only for real integrands.) -/
private theorem absolutelyContinuousOnInterval_of_dist_le {X : Type*} [PseudoMetricSpace X]
    {g : ℝ → X} {G : ℝ → ℝ} {a b : ℝ} (hG : AbsolutelyContinuousOnInterval G a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, x ≤ y → dist (g x) (g y) ≤ G y - G x) :
    AbsolutelyContinuousOnInterval g a b := by
  have h' : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (g x) (g y) ≤ dist (G x) (G y) := by
    intro x hx y hy
    rcases le_total x y with hxy | hxy
    · exact (h x hx y hy hxy).trans ((le_abs_self _).trans (by rw [Real.dist_eq, abs_sub_comm]))
    · rw [dist_comm, dist_comm (G x)]
      exact (h y hy x hx hxy).trans ((le_abs_self _).trans (by rw [Real.dist_eq, abs_sub_comm]))
  unfold AbsolutelyContinuousOnInterval at hG ⊢
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg)
    ?_ hG
  rw [eventually_inf_principal]
  filter_upwards with E hE
  exact Finset.sum_le_sum fun i hi ↦ h' _ (hE.1 i hi).1 _ (hE.1 i hi).2

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **Noether's theorem for optimal control** (Sussmann, Theorem 4.1, p. 389, for one vector
field; generalized as in S5). Let `Y` be an infinitesimal symmetry of the optimal control system
`(Ω, U, f, φ)` of class `C¹`, and let `(ũ, q)` be an admissible pair on `[0, T]` with a covector
curve `p` satisfying the adjoint equation and the maximum condition of the maximum principle for
some multiplier `ν ∈ ℝ` (normal or abnormal; the Hamiltonian need not be constant). Then the
momentum `⟨p(t), Y(q(t))⟩` is constant on `[0, T]`.

Proof, Step 4 of the module docstring (Sussmann, proof of Theorem 3.1, p. 385):
`g(t) = ⟨p(t), Y(q(t))⟩` is absolutely continuous on `[0, T]`: on `[a, b] ⊆ [0, T]`,
`|g(b) - g(a)| ≤ M ∫ₐᵇ ‖ṗ‖ + B L ∫ₐᵇ ‖q̇‖`, with `M`, `L` a bound and a Lipschitz constant of `Y`
on `q([0, T])` (from a cut-off, `ControlSystem.IsC1On.exists_cutoff`) and `B` a bound of `p`. At
almost every `t ∈ (0, T)`, `q̇ = f(q, ũ)` and `ṗ = -p ∘ ∂ₓf(q, ũ) - ν ∂ₓφ(q, ũ)` (Lebesgue's
differentiation theorem, `IntervalIntegrable.ae_hasDerivAt_integral`) and the maximum condition
holds, so `ġ(t) = -(⟨p, [Y, f_{ũ(t)}](q)⟩ + ν Dφ_{ũ(t)}(q) Y(q)) = 0`
(`IsInfinitesimalSymmetry.bracket_eq_zero`). An absolutely continuous function with derivative
`0` almost everywhere is constant (`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`). -/
theorem noether (hΩ : IsOpen Ω) (hf : ∀ u ∈ U, ContDiffOn ℝ 1 (f · u) Ω)
    (hφ : ∀ u ∈ U, ContDiffOn ℝ 1 (φ · u) Ω) {Y : E → E}
    (hY : IsInfinitesimalSymmetry f φ Ω U Y) {T ν : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    {p : ℝ → StrongDual ℝ E} (href : IsAdmissibleIn f Ω U (q 0) T ũ q)
    (hadj : IsAdjoint f φ ν ũ q T p) (hmax : IsMaximal f φ ν U ũ q T p) :
    ∀ t ∈ Icc 0 T, momentum Y (q t) (p t) = momentum Y (q 0) (p 0) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hI : [[0, T]] = Icc 0 T := uIcc_of_le hT
  obtain ⟨⟨-, hũU, hqc, hiq, hq⟩, hqΩ⟩ := href
  obtain ⟨hip, hp⟩ := hadj
  set Fq : ℝ → E := fun r ↦ f (q r) (ũ r) with hFq
  set Fp : ℝ → StrongDual ℝ E := fun r ↦
    (p r).comp (linearization f ũ q r) + ν • fderiv ℝ (φ · (ũ r)) (q r) with hFp
  have hsub : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, [[a, b]] ⊆ [[0, T]] := fun a ha b hb ↦
    uIcc_subset_uIcc (hI ▸ ha) (hI ▸ hb)
  -- the increments of `q` and `p`
  have hqinc : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, q b - q a = ∫ r in a..b, Fq r := by
    intro a ha b hb
    rw [hq b hb, hq a ha, add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left
      (hiq.mono_set (hsub 0 h0T b hb)) (hiq.mono_set (hsub 0 h0T a ha))]
  have hpinc : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, p a - p b = ∫ r in a..b, Fp r := by
    intro a ha b hb
    rw [hp a ha, hp b hb, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_add_adjacent_intervals (hip.mono_set (hsub a ha b hb))
        (hip.mono_set (hsub b hb T ⟨hT, le_rfl⟩)), add_sub_cancel_right]
  -- a bound and a Lipschitz constant of `Y` on `q([0, T])`, from a cut-off
  obtain ⟨δ, -, -, gY, MY, LY, hgY, hgYY⟩ :=
    (isC1On_of_contDiffOn hΩ hY.contDiffOn ({0} : Set ℝ)).exists_cutoff hΩ isCompact_singleton
      (isCompact_Icc.image_of_continuousOn hqc) (image_subset_iff.2 hqΩ)
  have hYq : ∀ r ∈ Icc 0 T, gY (q r) 0 = Y (q r) := fun r hr ↦
    hgYY _ (self_subset_cthickening _ ⟨r, hr, rfl⟩) 0 rfl
  have hYbd : ∀ r ∈ Icc 0 T, ‖Y (q r)‖ ≤ MY := fun r hr ↦ hYq r hr ▸ hgY.norm_le _ 0 rfl
  have hYlip : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, ‖Y (q b) - Y (q a)‖ ≤ LY * ‖q b - q a‖ := by
    intro a ha b hb
    rw [← hYq a ha, ← hYq b hb]
    exact (hgY.isLipschitzSystem.lipschitzWith 0 rfl).norm_sub_le _ _
  -- a bound of `p` on `[0, T]`
  have hpc : ContinuousOn p (Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left (μ := volume) (a := 0)
      (b := T) (f := Fp)
      (by rw [hI]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).1 hip)
    rw [hI] at h
    exact (continuousOn_const.add h).congr fun r hr ↦ hp r hr
  obtain ⟨Bp, hBp⟩ := isCompact_Icc.exists_bound_of_continuousOn hpc
  -- the dominating function `G`
  set G : ℝ → ℝ := fun b ↦ ∫ r in (0 : ℝ)..b, ((MY : ℝ) * ‖Fp r‖ + Bp * LY * ‖Fq r‖) with hG
  have hGi : IntervalIntegrable (fun r ↦ (MY : ℝ) * ‖Fp r‖ + Bp * LY * ‖Fq r‖) volume 0 T :=
    (hip.norm.const_mul _).add (hiq.norm.const_mul _)
  have hGac : AbsolutelyContinuousOnInterval G 0 T :=
    hGi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hGinc : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T,
      G b - G a = MY * (∫ r in a..b, ‖Fp r‖) + Bp * LY * ∫ r in a..b, ‖Fq r‖ := by
    intro a ha b hb
    simp only [hG]
    rw [intervalIntegral.integral_interval_sub_left (hGi.mono_set (hsub 0 h0T b hb))
      (hGi.mono_set (hsub 0 h0T a ha)), intervalIntegral.integral_add
      ((hip.norm.mono_set (hsub a ha b hb)).const_mul _)
      ((hiq.norm.mono_set (hsub a ha b hb)).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hdom : ∀ a ∈ uIcc 0 T, ∀ b ∈ uIcc 0 T, a ≤ b →
      dist (momentum Y (q a) (p a)) (momentum Y (q b) (p b)) ≤ G b - G a := by
    intro a ha b hb hab
    rw [hI] at ha hb
    have hpd : ‖p a - p b‖ ≤ ∫ r in a..b, ‖Fp r‖ := by
      rw [hpinc a ha b hb]; exact intervalIntegral.norm_integral_le_integral_norm hab
    have hqd : ‖q b - q a‖ ≤ ∫ r in a..b, ‖Fq r‖ := by
      rw [hqinc a ha b hb]; exact intervalIntegral.norm_integral_le_integral_norm hab
    have hp0 : 0 ≤ ∫ r in a..b, ‖Fp r‖ :=
      intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _
    have hB0 : 0 ≤ Bp := (norm_nonneg _).trans (hBp a ha)
    have e : momentum Y (q a) (p a) - momentum Y (q b) (p b) =
        (p a - p b) (Y (q a)) - p b (Y (q b) - Y (q a)) := by
      simp only [momentum, sub_apply, map_sub]; ring
    rw [hGinc a ha b hb, dist_eq_norm, e]
    calc ‖(p a - p b) (Y (q a)) - p b (Y (q b) - Y (q a))‖
        ≤ ‖(p a - p b) (Y (q a))‖ + ‖p b (Y (q b) - Y (q a))‖ := norm_sub_le _ _
      _ ≤ ‖p a - p b‖ * ‖Y (q a)‖ + ‖p b‖ * ‖Y (q b) - Y (q a)‖ :=
          add_le_add ((p a - p b).le_opNorm _) ((p b).le_opNorm _)
      _ ≤ (∫ r in a..b, ‖Fp r‖) * MY + Bp * (LY * ∫ r in a..b, ‖Fq r‖) :=
          add_le_add (mul_le_mul hpd (hYbd a ha) (norm_nonneg _) hp0)
            (mul_le_mul (hBp b hb) ((hYlip a ha b hb).trans
              (mul_le_mul_of_nonneg_left hqd LY.2)) (norm_nonneg _) hB0)
      _ = MY * (∫ r in a..b, ‖Fp r‖) + Bp * LY * ∫ r in a..b, ‖Fq r‖ := by ring
  have hgac : AbsolutelyContinuousOnInterval (fun s ↦ momentum Y (q s) (p s)) 0 T :=
    absolutelyContinuousOnInterval_of_dist_le hGac hdom
  -- the derivative vanishes almost everywhere
  have hne0 : ∀ᵐ s : ℝ, s ≠ 0 := by simp [ae_iff, measure_singleton]
  have hneT : ∀ᵐ s : ℝ, s ≠ T := by simp [ae_iff, measure_singleton]
  have hae : ∀ᵐ s, s ∈ uIcc 0 T → HasDerivAt (fun s ↦ momentum Y (q s) (p s)) 0 s := by
    filter_upwards [hiq.ae_hasDerivAt_integral, hip.ae_hasDerivAt_integral,
      (ae_restrict_iff' measurableSet_Icc).1 hmax, hne0, hneT] with s hsq hsp hsm hs0 hsT hs
    have hs' : s ∈ Icc 0 T := hI ▸ hs
    have hnhds : Icc 0 T ∈ 𝓝 s :=
      Icc_mem_nhds (lt_of_le_of_ne hs'.1 (Ne.symm hs0)) (lt_of_le_of_ne hs'.2 hsT)
    have hqd : HasDerivAt q (Fq s) s :=
      ((hsq hs 0 left_mem_uIcc).const_add (q 0)).congr_of_eventuallyEq
        (eventually_of_mem hnhds hq)
    have hpd : HasDerivAt p (-Fp s) s := by
      refine ((hsp hs T right_mem_uIcc).const_sub (p T)).congr_of_eventuallyEq
        (eventually_of_mem hnhds fun r hr ↦ ?_)
      rw [hp r hr, intervalIntegral.integral_symm, ← sub_eq_add_neg]
    have hqs : q s ∈ Ω := hqΩ s hs'
    have hYd : HasFDerivAt Y (fderiv ℝ Y (q s)) (q s) :=
      ((hY.contDiffOn.contDiffAt (hΩ.mem_nhds hqs)).differentiableAt one_ne_zero).hasFDerivAt
    have hgd := hpd.clm_apply (hYd.comp_hasDerivAt s hqd)
    have hb := hY.bracket_eq_zero hΩ hqs (hũU s hs')
      (((hf _ (hũU s hs')).contDiffAt (hΩ.mem_nhds hqs)).differentiableAt one_ne_zero)
      (((hφ _ (hũU s hs')).contDiffAt (hΩ.mem_nhds hqs)).differentiableAt one_ne_zero) (hsm hs')
    refine hgd.congr_deriv ?_
    simp only [hFp, hFq, linearization, VectorField.lieBracket, neg_apply, add_apply,
      ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul, map_sub, Function.comp_apply]
      at hb ⊢
    linarith
  obtain ⟨C, hC⟩ := hgac.const_of_ae_hasDerivAt_zero hae
  rw [hI] at hC
  exact (hC t ht).trans (hC 0 h0T).symm

section LieAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- **An infinitesimal group of symmetries** of `(Ω, U, f, φ)` (Sussmann, p. 389): a smooth action
`τ` of the real Lie algebra `L` on `Ω`, that is a Lie algebra homomorphism from `L` to the vector
fields (p. 380), here linear with `τ⁅X, X'⁆ = [τ X, τ X']` on `Ω` (S8), such that every `τ(X)` is
an infinitesimal symmetry (`C¹` for smooth, S2). -/
structure IsInfinitesimalGroupOfSymmetries (f : E → V → E) (φ : E → V → ℝ) (Ω : Set E)
    (U : Set V) (τ : L →ₗ[ℝ] E → E) : Prop where
  map_lie : ∀ X X' : L, ∀ x ∈ Ω, τ ⁅X, X'⁆ x = VectorField.lieBracket ℝ (τ X) (τ X') x
  isInfinitesimalSymmetry : ∀ X : L, IsInfinitesimalSymmetry f φ Ω U (τ X)

/-- **The momentum map** `μ^τ : T*Ω → L*`, `μ^τ(x, p)(X) = ⟨p, τ(X)(x)⟩` (Sussmann, p. 389; `L*`
the algebraic dual, S8). -/
def momentumMap (τ : L →ₗ[ℝ] E → E) (x : E) (p : StrongDual ℝ E) : Module.Dual ℝ L :=
  (p : E →ₗ[ℝ] ℝ) ∘ₗ LinearMap.proj x ∘ₗ τ

omit [FiniteDimensional ℝ E] in
/-- `μ^τ(x, p)(X) = h_{τ(X)}(x, p)`. -/
theorem momentumMap_apply (τ : L →ₗ[ℝ] E → E) (x : E) (p : StrongDual ℝ E) (X : L) :
    momentumMap τ x p X = momentum (τ X) x p :=
  rfl

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **Noether's theorem for optimal control, Lie-algebra form** (Sussmann, Theorem 4.1, p. 389,
generalized as in S5): along every pair `(q, p)` with the adjoint equation and the maximum
condition, the momentum map `μ^τ(q(t), p(t)) ∈ L*` of an infinitesimal group of symmetries is
constant on `[0, T]`.

Proof: `noether` for each `τ(X)`. The bracket condition `hτ.map_lie` is not used. -/
theorem noether_momentumMap (hΩ : IsOpen Ω) (hf : ∀ u ∈ U, ContDiffOn ℝ 1 (f · u) Ω)
    (hφ : ∀ u ∈ U, ContDiffOn ℝ 1 (φ · u) Ω) {τ : L →ₗ[ℝ] E → E}
    (hτ : IsInfinitesimalGroupOfSymmetries f φ Ω U τ) {T ν : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    {p : ℝ → StrongDual ℝ E} (href : IsAdmissibleIn f Ω U (q 0) T ũ q)
    (hadj : IsAdjoint f φ ν ũ q T p) (hmax : IsMaximal f φ ν U ũ q T p) :
    ∀ t ∈ Icc 0 T, momentumMap τ (q t) (p t) = momentumMap τ (q 0) (p 0) := fun t ht ↦
  LinearMap.ext fun X ↦ noether hΩ hf hφ (hτ.isInfinitesimalSymmetry X) href hadj hmax t ht

omit [FiniteDimensional ℝ E] in
/-- The momentum map is linear in the covector: `μ^τ(x, -p) = -μ^τ(x, p)` (S6). -/
theorem momentumMap_neg (τ : L →ₗ[ℝ] E → E) (x : E) (p : StrongDual ℝ E) :
    momentumMap τ x (-p) = -momentumMap τ x p :=
  LinearMap.ext fun X ↦ by simp [momentumMap]

end LieAlgebra

/-! ### Sussmann's statement: biextremals, minimization convention -/

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- The Hamiltonian changes sign with the multiplier and the covector:
`H^{-ν}(x, -p, u) = -H^ν(x, p, u)` (S6). -/
theorem controlHamiltonian_neg (f : E → V → E) (φ : E → V → ℝ) (ν : ℝ) (x : E)
    (p : StrongDual ℝ E) (u : V) :
    controlHamiltonian f φ (-ν) x (-p) u = -controlHamiltonian f φ ν x p u := by
  simp only [controlHamiltonian, neg_apply]; ring

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- The adjoint equation is linear in `(p, ν)` (S6): the integrand for `(-p, -ν)` is minus that
for `(p, ν)`. -/
theorem IsAdjoint.neg {ν T : ℝ} {ũ : ℝ → V} {q : ℝ → E} {p : ℝ → StrongDual ℝ E}
    (h : IsAdjoint f φ ν ũ q T p) : IsAdjoint f φ (-ν) ũ q T (-p) := by
  obtain ⟨hi, he⟩ := h
  have e : ∀ r, ((-p) r).comp (linearization f ũ q r) + (-ν) • fderiv ℝ (φ · (ũ r)) (q r) =
      -((p r).comp (linearization f ũ q r) + ν • fderiv ℝ (φ · (ũ r)) (q r)) := fun r ↦ by
    rw [Pi.neg_apply, ContinuousLinearMap.neg_comp, neg_smul, neg_add]
  refine ⟨hi.neg.congr fun r _ ↦ (e r).symm, fun t ht ↦ ?_⟩
  rw [intervalIntegral.integral_congr fun r _ ↦ e r, intervalIntegral.integral_neg, Pi.neg_apply,
    Pi.neg_apply, he t ht, neg_add]

/-- **A controlled `c`-biextremal** of `(Ω, U, f, φ)` on `[0, T]` (Sussmann, (EAV1)–(EAV3),
pp. 388–389, read in coordinates, S1 and S7): `(ũ, q)` is an admissible pair, `c ≥ 0`, the
covector curve `ζ` solves the adjoint equation (4.3) (in integral form, which makes `ζ`
absolutely continuous, (EAV1)), the Hamiltonian `H^c = ⟨ζ, f_u⟩ + c f⁰_u` is minimized by `ũ(t)`
over `U` for almost every `t`, with a constant minimum (4.4), and `(ζ(t), c) ≠ (0, 0)` for every
`t` (EAV3). -/
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

omit [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [BorelSpace V] in
/-- A biextremal in Sussmann's minimization convention gives the package's maximum condition for
`(-ζ, -c)` (S6): `controlHamiltonian_neg` turns the minimum into a maximum. -/
theorem IsBiextremal.isMaximal_neg {T c : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    {ζ : ℝ → StrongDual ℝ E} (h : IsBiextremal f φ Ω U T ũ q c ζ) :
    IsMaximal f φ (-c) U ũ q T (-ζ) := by
  unfold IsMaximal
  filter_upwards [h.isMinimal] with t ht u hu
  rw [Pi.neg_apply, controlHamiltonian_neg, controlHamiltonian_neg]
  exact neg_le_neg (ht u hu)

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **Sussmann, Theorem 4.1** (p. 389), as stated there: let `(Ω, U, f, φ)` be an optimal control
system of class `C¹`, `L` a Lie algebra and `τ` an infinitesimal group of symmetries, and let
`Ξ = (q, ζ)` be a biextremal. Then the momentum map `μ^τ` is constant along `Ξ`: all the functions
`(x, z) ↦ ⟨z, τ(X)(x)⟩`, `X ∈ L`, are constant along `Ξ`. (In coordinates, with the readings
S1–S8.)

Proof: `noether_momentumMap` for `(-ζ, -c)` (`IsAdjoint.neg`, `IsBiextremal.isMaximal_neg`) and
`momentumMap_neg`. The hypotheses `c ≥ 0`, `const` and `ne_zero` are not used (S5). -/
theorem sussmann_theorem4_1 {L : Type*} [LieRing L] [LieAlgebra ℝ L] (hΩ : IsOpen Ω)
    (hf : ∀ u ∈ U, ContDiffOn ℝ 1 (f · u) Ω) (hφ : ∀ u ∈ U, ContDiffOn ℝ 1 (φ · u) Ω)
    {τ : L →ₗ[ℝ] E → E} (hτ : IsInfinitesimalGroupOfSymmetries f φ Ω U τ) {T c : ℝ}
    {ũ : ℝ → V} {q : ℝ → E} {ζ : ℝ → StrongDual ℝ E} (hΞ : IsBiextremal f φ Ω U T ũ q c ζ) :
    ∀ t ∈ Icc 0 T, momentumMap τ (q t) (ζ t) = momentumMap τ (q 0) (ζ 0) := by
  intro t ht
  have h := noether_momentumMap hΩ hf hφ hτ hΞ.isAdmissibleIn hΞ.isAdjoint.neg hΞ.isMaximal_neg
    t ht
  rwa [Pi.neg_apply, Pi.neg_apply, momentumMap_neg, momentumMap_neg, neg_inj] at h

end Noether

/-! ### With the maximum principle -/

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- **The maximum principle with Noether's integrals of motion**: the conclusions of
`Pontryagin.maximum_principle` (free terminal time, integral cost, mixed boundary conditions,
strong local minimizers), and moreover the momentum `⟨p(t), Y(q(t))⟩` of every infinitesimal
symmetry `Y` of `(Ω, U, f, φ)` is constant on `[0, T]`. (One multiplier serves for all the
symmetries at once, since `noether` holds for every extremal.)

Proof: the multiplier of `Pontryagin.maximum_principle`, and `noether` for each `Y`, with
`ControlSystem.IsC1On.contDiffOn` for the regularity. -/
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
        ∀ t ∈ Icc 0 T, momentum Y (q t) (p t) = momentum Y (q 0) (p 0) := by
  obtain ⟨ν, p, hν, hlip, hne, hadj, hmax, hH, htrans⟩ :=
    maximum_principle hΩ hU hf hφ hmin hG hGsurj hG0 hGN
  exact ⟨ν, p, hν, hlip, hne, hadj, hmax, hH, htrans, fun Y hY ↦
    noether hΩ (fun u hu ↦ hf.contDiffOn hΩ hu) (fun u hu ↦ hφ.contDiffOn hΩ hu) hY hmin.2.1
      hadj hmax⟩

/-! ### Example: rotations of the plane -/

/-- **Rotations of the plane are symmetries** of the system `ż = a z + u` on `ℂ ≅ ℝ²` (`a ∈ ℂ`,
so that the system commutes with rotations), with controls in the closed unit disk and the
rotation-invariant cost `‖z‖² + ‖u‖²`: the field `Y(z) = i z`, whose flow is the group of
rotations `z ↦ e^{is} z`, is an infinitesimal symmetry. The rotations permute the controls
(`u₁ = e^{is} u`, `u₂ = e^{-is} u`), as Sussmann's definition allows.

Proof: `isInfinitesimalSymmetry_of_flow` with `Φ(s, z) = e^{is} z`. -/
theorem isInfinitesimalSymmetry_rotation (a : ℂ) :
    IsInfinitesimalSymmetry (E := ℂ) (V := ℂ) (fun z u ↦ a * z + u)
      (fun z u ↦ ‖z‖ ^ 2 + ‖u‖ ^ 2) univ (closedBall 0 1) (fun z ↦ Complex.I * z) := by
  have hexp : ∀ s : ℝ, ‖Complex.exp (s * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I
  have hlin : ∀ s : ℝ, fderiv ℝ (fun z : ℂ ↦ Complex.exp (s * Complex.I) * z) =
      fun _ ↦ Complex.exp (s * Complex.I) • ContinuousLinearMap.id ℝ ℂ := fun s ↦ by
    ext1 z
    exact ((hasFDerivAt_id z).const_smul (Complex.exp (s * Complex.I))).fderiv
  refine isInfinitesimalSymmetry_of_flow isOpen_univ
    ((contDiff_const.mul contDiff_id).contDiffOn) (fun s z ↦ Complex.exp (s * Complex.I) * z)
    (fun _ _ _ ↦ mem_univ _) (fun x _ ↦ by simp) (fun z _ s ↦ ?_) (fun s z _ ↦ ?_)
    (fun s ↦ (contDiff_const.mul contDiff_id).contDiffOn) (fun s ↦ ⟨?_, ?_⟩)
  · have h := (((hasDerivAt_id (s : ℂ)).mul_const Complex.I).cexp.comp_ofReal).mul_const z
    convert h using 1
    · simp
    · simp; ring
  · rw [← mul_assoc, ← Complex.exp_add]; push_cast; simp
  · intro u hu
    refine ⟨Complex.exp (s * Complex.I) * u, ?_, fun x _ ↦ ?_⟩
    · simpa [hexp] using hu
    · rw [hlin]; simp [hexp]; ring
  · intro u hu
    refine ⟨Complex.exp (-(s * Complex.I)) * u, ?_, fun x _ ↦ ?_⟩
    · simpa [Complex.norm_exp_ofReal_mul_I, ← neg_mul, ← Complex.ofReal_neg] using hu
    · rw [hlin]
      simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        norm_mul, hexp]
      constructor
      · rw [mul_add, mul_left_comm _ a, ← mul_assoc (Complex.exp _) (Complex.exp _),
          ← Complex.exp_add]; simp
      · simp [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

/-- **Conservation of angular momentum** for the rotation-invariant system of
`isInfinitesimalSymmetry_rotation`: along every pair `(q, p)` with the adjoint equation and the
maximum condition, for any multiplier `ν`, the momentum `⟨p(t), i q(t)⟩` of the rotations is
constant on `[0, T]` (`noether`). -/
theorem noether_rotation (a : ℂ) {T ν : ℝ} {ũ q : ℝ → ℂ} {p : ℝ → StrongDual ℝ ℂ}
    (href : IsAdmissibleIn (fun z u ↦ a * z + u) univ (closedBall 0 1) (q 0) T ũ q)
    (hadj : IsAdjoint (fun z u ↦ a * z + u) (fun z u ↦ ‖z‖ ^ 2 + ‖u‖ ^ 2) ν ũ q T p)
    (hmax : IsMaximal (fun z u ↦ a * z + u) (fun z u ↦ ‖z‖ ^ 2 + ‖u‖ ^ 2) ν (closedBall 0 1)
      ũ q T p) :
    ∀ t ∈ Icc 0 T, p t (Complex.I * q t) = p 0 (Complex.I * q 0) :=
  noether isOpen_univ
    (fun _ _ ↦ (contDiff_const.mul contDiff_id |>.add contDiff_const).contDiffOn)
    (fun _ _ ↦ (contDiff_norm_sq ℝ |>.add contDiff_const).contDiffOn)
    (isInfinitesimalSymmetry_rotation a) href hadj hmax

end Pontryagin
