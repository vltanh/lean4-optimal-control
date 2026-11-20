module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Challenge: the maximum principle, Filippov's theorem and Noether's theorem

Statements of record of the package `OptimalControl`: the **Pontryagin maximum principle** with
free terminal time, an integral cost and mixed boundary conditions, for strong local minimizers
(`maximum_principle`), proved by the argument of A. A. Agrachev and Yu. L. Sachkov, *Control
Theory from the Geometric Viewpoint* (Encyclopaedia of Mathematical Sciences 87, Springer, 2004),
Chapter 12; **Filippov's theorem** on the compactness of attainable sets (their Theorem 10.1;
`isCompact_reachableSet`, `isCompact_reachableSetLE`); the **existence of optimal controls** for
integral costs that follows from it (`exists_optimal_fixedTime`, `exists_optimal_freeTime`); and
**Noether's theorem for optimal control** (`noether`), Theorem 4.1 of H. J. Sussmann, *Symmetries
and integrals of motion in optimal control* (Banach Center Publications 32, 1995, pp. 379–393).
This file imports only Mathlib. The definitions between the two markers are copied word for word
from the library module `OptimalControl/Defs.lean` (`scripts/sync_challenge_defs.py`), so that
the Challenge and the Solution use the same constants. Page numbers refer to the authors' draft of
Agrachev and Sachkov's book (preface September 2003) and to Sussmann's published paper;
`docs/AGRACHEV_SACHKOV.md` lists the departures D1–D11, `docs/SUSSMANN.md` the readings S1–S8.

## Conventions

* `E` (states) is a finite-dimensional real normed space. In the maximum principle the control
  values lie in a finite-dimensional real normed space `V` and the boundary constraint takes
  values in a finite-dimensional real normed space `Q`; in Filippov's theorem `V` is a metric
  space; in both, `V` carries its Borel σ-algebra. In Noether's theorem `V` is any type with a
  σ-algebra. In the maximum principle and in Noether's theorem, the manifold `M` of the sources is
  an open set `Ω ⊆ E` (D1 and S1); in Filippov's theorem the states range over `E`.
* Time runs over `[0, T]` (`Icc 0 T`). A *control* is a measurable `u : ℝ → V` with `u(t) ∈ U` for
  `t ∈ [0, T]`, for a control set `U ⊆ V`, compact in the maximum principle and in Filippov's
  theorem and arbitrary in Noether's theorem. An *admissible pair* `(u, x)` from `x₀` on `[0, T]`
  for `x' = F(x, u)` (`ControlSystem.IsAdmissible`) is a control `u` and a Carathéodory trajectory
  `x`: `x` is continuous on `[0, T]`, `t ↦ F(x(t), u(t))` is integrable on `[0, T]`, and
  `x(t) = x₀ + ∫₀ᵗ F(x(s), u(s)) ds` for `t ∈ [0, T]`. Values outside `[0, T]` play no role.
  `Pontryagin.IsAdmissibleIn` adds `x(t) ∈ Ω` on `[0, T]`.
* `∫ s in a..b, g s` is the interval (Bochner) integral for Lebesgue measure `volume`, and
  `∀ᵐ t ∂(volume.restrict (Icc 0 T))` means "for almost every `t ∈ [0, T]`".
* Covectors are elements of `StrongDual ℝ E = E →L[ℝ] ℝ`; `fderiv ℝ g x` is the Fréchet
  derivative; `ContDiffAt ℝ 1 G z` says that `G` is `C¹` near `z`; `𝓝 z` is the neighbourhood
  filter, and `∀ᶠ z' in 𝓝 z, P z'` says that `P` holds near `z`.
* `ControlSystem.IsC1On f Ω U` (A–S's (10.2)–(10.4) with `C¹` for `C^∞`): `(x, u) ↦ f(x, u)` is
  continuous on `Ω × U`, `f(·, u)` is differentiable at every `x ∈ Ω` for `u ∈ U`, and
  `(x, u) ↦ ∂ₓf(x, u)` is continuous on `Ω × U`.

## The maximum principle (`maximum_principle`)

The problem: minimize the cost `∫₀ᵀ φ(q(t), u(t)) dt` (`Pontryagin.cost`) over admissible pairs
`(u, q)` of `q' = f(q, u)` in the open set `Ω`, with free terminal time `T > 0` and the boundary
condition `(q(0), q(T)) ∈ N ⊆ E × E`. `f` and `φ` satisfy `IsC1On` and `U` is compact.

Hypotheses: `(ũ, q)` on `[0, T]` is a *strong local minimizer* (`IsStrongLocalMinimizer`): `T > 0`,
`(ũ, q)` is admissible in `Ω`, `(q(0), q(T)) ∈ N`, and for some `ε > 0` every admissible pair
`(u', q')` in `Ω` on `[0, T']` with `T' > 0`, `(q'(0), q'(T')) ∈ N`, `|T' - T| < ε` and
`‖q'(σ T') - q(σ T)‖ < ε` for all `σ ∈ [0, 1]` has cost at least that of `(ũ, q)`. (A minimizer
among all admissible pairs is one.) Near `(q(0), q(T))`, `N` contains the zeros of a `C¹` map
`G : E × E → Q` with surjective derivative and `G(q(0), q(T)) = 0`; that is, `N` contains a
submanifold through the end points with tangent space `ker G'(q(0), q(T))`.

Conclusion: there are `ν ≤ 0` and a covector curve `p : ℝ → E*`, Lipschitz on `[0, T]`, with

1. `(ν, p(t)) ≠ (0, 0)` for every `t ∈ [0, T]`;
2. the adjoint equation `ṗ = -p ∘ ∂ₓf(q, ũ) - ν ∂ₓφ(q, ũ)` in integral form (`IsAdjoint`):
   `p(t) = p(T) + ∫ₜᵀ (p(r) ∘ ∂ₓf(q(r), ũ(r)) + ν ∂ₓφ(q(r), ũ(r))) dr` on `[0, T]`, with an
   integrable integrand;
3. the maximum condition (`IsMaximal`): for almost every `t ∈ [0, T]`,
   `H(q(t), p(t), u) ≤ H(q(t), p(t), ũ(t))` for all `u ∈ U`, where
   `H(q, p, u) = p(f(q, u)) + ν φ(q, u)` (`controlHamiltonian`);
4. `H(q(t), p(t), ũ(t)) = 0` for almost every `t ∈ [0, T]` (free terminal time);
5. the transversality condition: `-p(0)(v) + p(T)(w) = 0` for all `(v, w) ∈ ker G'(q(0), q(T))`.

This is Agrachev and Sachkov's Theorem 12.5 (p. 183) with the remark after it (free time), with
their `λ_t` as `p(t)`, their sign `ν ≤ 0`, and strong local minimizers for their optimal controls.

## Filippov's theorem (`isCompact_reachableSet`, `isCompact_reachableSetLE`)

For `F : E → V → E` jointly continuous, `U` compact, convex velocity sets `F(x, U)` for every
`x`, and a bound `‖F(x(s), u(s))‖ ≤ M` for `s ∈ [0, T]` along every admissible pair `(u, x)` from
`x₀` on `[0, T]`, the attainable set `ControlSystem.reachableSet F U x₀ T` (the end points `x(T)`
of these pairs) is compact for `T ≥ 0`. If the bound holds on `[0, τ]` for the admissible pairs on
`[0, τ]`, for every `τ ∈ [0, T]`, then `ControlSystem.reachableSetLE F U x₀ T`, the union of the
attainable sets at the times `τ ∈ [0, T]`, is compact. (Agrachev and Sachkov work with smooth
systems on a manifold; here `F` is only continuous, and the bound on the velocities, which keeps
the trajectories bounded, is a hypothesis.)

## Existence of optimal controls (`exists_optimal_fixedTime`, `exists_optimal_freeTime`)

For `V` a separable metric space, `F` and a running cost `φ : E → V → ℝ` jointly continuous, `U`
compact, `‖F‖ ≤ M` on `E × U`, and convex extended velocity sets `{(F(x, u), φ(x, u)) | u ∈ U}`:
among the admissible pairs from `x₀` that reach an attainable `x₁` at time `T ≥ 0` (or at some
time `τ ∈ [0, T]`), one has the least cost `∫₀ᵀ φ(x, u)` (or `∫₀^τ φ(x, u)`). The proof applies
Filippov's theorem to the system extended by the cost.

## Noether's theorem (`noether`)

Sussmann's optimal control system `(M, U, f, f⁰)` is `(Ω, U, f, φ)`, with `f(·, u)` and `φ(·, u)`
of class `C¹` on the open set `Ω` for every `u ∈ U`. The integral curves of a vector field
`Y : E → E` are taken in `Ω`, in Carathéodory form (`IsIntegralCurveIn`), and the time-`s` map
`e^{sY}` (`flowMap`) is defined on the set `D_s` of their initial points (`flowDomain`). A
*symmetry* (`IsSymmetry`, Sussmann p. 389) is a `C¹` diffeomorphism `σ : V₁ → V₂` between open
subsets of `Ω` that maps the family `{(f_u, φ_u) | u ∈ U}` into itself in both directions,
possibly permuting the controls (`PermutesFamily`): for every `u ∈ U` there are `u₁, u₂ ∈ U` with
`dσ(x) f_u(x) = f_{u₁}(σ(x))`, `φ_{u₁}(σ(x)) = φ_u(x)`, `dσ(x) f_{u₂}(x) = f_u(σ(x))` and
`φ_u(σ(x)) = φ_{u₂}(x)` for `x ∈ V₁`; so the cost is invariant. An *infinitesimal symmetry*
(`IsInfinitesimalSymmetry`) is a `C¹` field `Y` on `Ω` every `e^{sY} : D_s → D_{-s}` of which is a
symmetry; its momentum is `h_Y(x, p) = p(Y(x))` (`momentum`).

Statement: if `Y` is an infinitesimal symmetry and `(ũ, q)` is an admissible pair in `Ω` on
`[0, T]` with a covector curve `p` that satisfies the adjoint equation (`IsAdjoint`) and the
maximum condition (`IsMaximal`) of the maximum principle for some multiplier `ν ∈ ℝ`, then
`p(t)(Y(q(t))) = p(0)(Y(q(0)))` for every `t ∈ [0, T]`. This is Sussmann's Theorem 4.1 (p. 389)
for one vector field, under weaker hypotheses: `ν` is any real number (Sussmann minimizes, with
`(ζ, c)`, `c ≥ 0`, which is `(p, ν) = (-ζ, -c)` here), the Hamiltonian need not be constant nor
`(p, ν)` nonzero, and `Y` is `C¹` rather than `C^∞`. His form, for a Lie algebra acting by
infinitesimal symmetries, follows by applying it to each field of the action.
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS

-- Palomar compiles the Challenge with plain `lean`, without the `[leanOptions]` of
-- `lakefile.toml`, so an option that changes elaboration is set here, in the copied block: the
-- block then elaborates to the same terms in the Challenge and in the library. (Without it,
-- `Pontryagin.IsAdjoint` finds `NormedSpace ℝ ℝ` by another path, and Comparator rejects it.)
set_option maxSynthPendingDepth 3

open MeasureTheory Set Filter Topology

namespace ControlSystem

section Admissible

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace V]

/-- An admissible pair on `[0, T]` from `x₀` for the control system `x' = F(x, u)`, `u ∈ U`: a
measurable control `u` with values in `U` on `[0, T]` and a trajectory `x`, continuous on
`[0, T]`, with `t ↦ F(x(t), u(t))` integrable and `x(t) = x₀ + ∫₀ᵗ F(x(s), u(s)) ds` on
`[0, T]`. -/
def IsAdmissible (F : E → V → E) (U : Set V) (x₀ : E) (T : ℝ) (u : ℝ → V) (x : ℝ → E) : Prop :=
  Measurable u ∧ (∀ t ∈ Icc 0 T, u t ∈ U) ∧ ContinuousOn x (Icc 0 T) ∧
    IntervalIntegrable (fun s ↦ F (x s) (u s)) volume 0 T ∧
    ∀ t ∈ Icc 0 T, x t = x₀ + ∫ s in (0 : ℝ)..t, F (x s) (u s)

/-- The attainable set at time `T`: the endpoints `x(T)` of the admissible trajectories on
`[0, T]` from `x₀`. -/
def reachableSet (F : E → V → E) (U : Set V) (x₀ : E) (T : ℝ) : Set E :=
  {p | ∃ u x, IsAdmissible F U x₀ T u x ∧ x T = p}

/-- The attainable set for times at most `T`: the union of the `reachableSet F U x₀ τ`,
`τ ∈ [0, T]`. -/
def reachableSetLE (F : E → V → E) (U : Set V) (x₀ : E) (T : ℝ) : Set E :=
  ⋃ τ ∈ Icc 0 T, reachableSet F U x₀ τ

end Admissible

section Regularity

variable {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The regularity of Agrachev–Sachkov's control systems on an open set `Ω`, conditions
(10.2)–(10.4) of their §10.1 (authors' draft, p. 133) with `C¹` in place of `C^∞` (departure D3):
`(x, u) ↦ f x u` is continuous on `Ω × U`, `x ↦ f x u` is differentiable on `Ω` for `u ∈ U`, and
`(x, u) ↦ ∂ₓf(x, u)` is continuous on `Ω × U`. The same conditions are imposed on the integrand
`φ` of a cost (`F = ℝ`). -/
structure IsC1On (f : E → V → F) (Ω : Set E) (U : Set V) : Prop where
  continuousOn : ContinuousOn (fun p : E × V ↦ f p.1 p.2) (Ω ×ˢ U)
  differentiableAt : ∀ x ∈ Ω, ∀ u ∈ U, DifferentiableAt ℝ (f · u) x
  continuousOn_fderiv : ContinuousOn (fun p : E × V ↦ fderiv ℝ (f · p.2) p.1) (Ω ×ˢ U)

end Regularity

end ControlSystem

namespace Pontryagin

open ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- An admissible pair in `Ω` on `[0, T]` from `x₀` (A–S, §10.1, p. 133): a measurable control
`u` with values in `U` on `[0, T]` and its Carathéodory trajectory `x` from `x₀`
(`ControlSystem.IsAdmissible`), with `x(t) ∈ Ω` for `t ∈ [0, T]`. -/
def IsAdmissibleIn (f : E → V → E) (Ω : Set E) (U : Set V) (x₀ : E) (T : ℝ) (u : ℝ → V)
    (x : ℝ → E) : Prop :=
  IsAdmissible f U x₀ T u x ∧ ∀ t ∈ Icc 0 T, x t ∈ Ω

/-- The cost `J(u) = ∫₀ᵀ φ(x(t), u(t)) dt` of a pair `(u, x)` on `[0, T]` ((12.20), p. 175). -/
noncomputable def cost (φ : E → V → ℝ) (T : ℝ) (u : ℝ → V) (x : ℝ → E) : ℝ :=
  ∫ t in (0 : ℝ)..T, φ (x t) (u t)

/-- The Hamiltonian `h^ν_u(λ) = ⟨λ, f_u(q)⟩ + ν φ(q, u)` (A–S, Theorem 12.3, p. 176; with
`φ = 0` it is `h_u(λ) = ⟨λ, f_u(q)⟩` of §12.1, p. 163). -/
def controlHamiltonian (f : E → V → E) (φ : E → V → ℝ) (ν : ℝ) (q : E) (p : StrongDual ℝ E)
    (u : V) : ℝ :=
  p (f q u) + ν * φ q u

/-- The linearization `A(t) = ∂ₓf(q̃(t), ũ(t))` of the system along a reference pair. -/
noncomputable def linearization (f : E → V → E) (ũ : ℝ → V) (q : ℝ → E) (t : ℝ) : E →L[ℝ] E :=
  fderiv ℝ (f · (ũ t)) (q t)

/-- The Hamiltonian system of the maximum principle along the reference pair `(ũ, q̃)` on
`[0, T]`, in coordinates (A–S (12.4) for `φ = 0`, `ν = 0`; (12.24), (12.30) in general): the
covector curve `p` solves the adjoint equation `ṗ = -p ∘ ∂ₓf(q̃, ũ) - ν ∂ₓφ(q̃, ũ)` in integral
form, `p(t) = p(T) + ∫ₜᵀ (p(r) ∘ ∂ₓf(q̃(r), ũ(r)) + ν ∂ₓφ(q̃(r), ũ(r))) dr` on `[0, T]`, the
integrand being integrable. (The state part of the Hamiltonian system is the control system.) -/
def IsAdjoint (f : E → V → E) (φ : E → V → ℝ) (ν : ℝ) (ũ : ℝ → V) (q : ℝ → E) (T : ℝ)
    (p : ℝ → StrongDual ℝ E) : Prop :=
  IntervalIntegrable (fun r ↦ (p r).comp (linearization f ũ q r) +
      ν • fderiv ℝ (φ · (ũ r)) (q r)) volume 0 T ∧
    ∀ t ∈ Icc 0 T, p t = p T + ∫ r in t..T,
      ((p r).comp (linearization f ũ q r) + ν • fderiv ℝ (φ · (ũ r)) (q r))

/-- The maximality condition (A–S (12.5), (12.31)): for almost every `t ∈ [0, T]`,
`h^ν_{ũ(t)}(p(t)) = max_{u ∈ U} h^ν_u(p(t))` (written as an inequality for every `u ∈ U`; the
maximum is attained at `ũ(t) ∈ U`). -/
def IsMaximal (f : E → V → E) (φ : E → V → ℝ) (ν : ℝ) (U : Set V) (ũ : ℝ → V) (q : ℝ → E)
    (T : ℝ) (p : ℝ → StrongDual ℝ E) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Icc 0 T)), ∀ u ∈ U,
    controlHamiltonian f φ ν (q t) (p t) u ≤ controlHamiltonian f φ ν (q t) (p t) (ũ t)

/-- A strong local minimizer of the problem with free terminal time, integral cost `∫ φ` and the
boundary condition `(q(0), q(T)) ∈ N` (A–S (12.49)–(12.52), p. 183, with free `t₁`): `(u, q)` is
an admissible pair in `Ω` on `[0, T]`, `T > 0`, satisfying the boundary condition, and for some
`ε > 0` no admissible pair in `Ω` on `[0, T']`, `T' > 0`, satisfying the boundary condition, with
`|T' - T| < ε` and `‖q'(σ T') - q(σ T)‖ < ε` for all `σ ∈ [0, 1]`, has a smaller cost.
A–S's optimal controls (global minimizers) are strong local minimizers (departure D5). -/
def IsStrongLocalMinimizer (f : E → V → E) (φ : E → V → ℝ) (Ω : Set E) (U : Set V)
    (N : Set (E × E)) (T : ℝ) (u : ℝ → V) (q : ℝ → E) : Prop :=
  0 < T ∧ IsAdmissibleIn f Ω U (q 0) T u q ∧ (q 0, q T) ∈ N ∧
    ∃ ε > 0, ∀ (T' : ℝ) (u' : ℝ → V) (q' : ℝ → E), 0 < T' →
      IsAdmissibleIn f Ω U (q' 0) T' u' q' → (q' 0, q' T') ∈ N → |T' - T| < ε →
      (∀ σ ∈ Icc (0 : ℝ) 1, ‖q' (σ * T') - q (σ * T)‖ < ε) → cost φ T u q ≤ cost φ T' u' q'

section Symmetry

/-! The objects of Noether's theorem (Sussmann, §4, pp. 387–389), in coordinates (S1). -/

open scoped Interval

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
`Pontryagin.flowMap_eq_of_isIntegralCurveIn`); `x` itself outside `flowDomain Y Ω s`. -/
noncomputable def flowMap (Y : E → E) (Ω : Set E) (s : ℝ) (x : E) : E :=
  if h : ∃ γ, IsIntegralCurveIn Y Ω x s γ then h.choose s else x

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

/-- The momentum of a vector field `Y`, `h_Y(x, p) = ⟨p, Y(x)⟩` on `T*Ω = Ω × E*` (Sussmann,
p. 384: "every vector field `X` gives rise to a smooth function `h_X` on `T*M`"). -/
def momentum (Y : E → E) (x : E) (p : StrongDual ℝ E) : ℝ :=
  p (Y x)

end Symmetry

end Pontryagin

-- END SHARED DEFINITIONS

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
      ∀ v w : E, fderiv ℝ G (q 0, q T) (v, w) = 0 → -p 0 v + p T w = 0 := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **Noether's theorem for optimal control** (Sussmann, Theorem 4.1, for one vector field): if
`Y` is an infinitesimal symmetry of the optimal control system `(Ω, U, f, φ)` of class `C¹`, then
along every admissible pair `(ũ, q)` with a covector curve `p` that satisfies the adjoint equation
and the maximum condition for some multiplier `ν`, the momentum `p(t)(Y(q(t)))` is constant on
`[0, T]`. -/
theorem noether {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace V] {Ω : Set E} (hΩ : IsOpen Ω) {U : Set V} {f : E → V → E}
    {φ : E → V → ℝ} (hf : ∀ u ∈ U, ContDiffOn ℝ 1 (f · u) Ω)
    (hφ : ∀ u ∈ U, ContDiffOn ℝ 1 (φ · u) Ω) {Y : E → E}
    (hY : IsInfinitesimalSymmetry f φ Ω U Y) {T ν : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    {p : ℝ → StrongDual ℝ E} (href : IsAdmissibleIn f Ω U (q 0) T ũ q)
    (hadj : IsAdjoint f φ ν ũ q T p) (hmax : IsMaximal f φ ν U ũ q T p) :
    ∀ t ∈ Icc 0 T, momentum Y (q t) (p t) = momentum Y (q 0) (p 0) := by
  sorry

end OptimalControlChallenge

end
