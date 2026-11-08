module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Challenge: the Pontryagin maximum principle and Filippov's theorem

Statements of record of the package `OptimalControl`: the **Pontryagin maximum principle** with
free terminal time, an integral cost and mixed boundary conditions, for strong local minimizers
(`maximum_principle`), proved by the argument of A. A. Agrachev and Yu. L. Sachkov, *Control
Theory from the Geometric Viewpoint* (Encyclopaedia of Mathematical Sciences 87, Springer, 2004),
Chapter 12; **Filippov's theorem** on the compactness of attainable sets (their Theorem 10.1;
`isCompact_reachableSet`, `isCompact_reachableSetLE`); and the **existence of optimal controls**
for integral costs that follows from it (`exists_optimal_fixedTime`, `exists_optimal_freeTime`).
This file imports only Mathlib. The definitions between the two markers are copied word for word
from the library module `OptimalControl/Defs.lean` (`scripts/sync_challenge_defs.py`), so that
the Challenge and the Solution use the same constants. Page numbers refer to the authors' draft of
the book (preface September 2003); `docs/AGRACHEV_SACHKOV.md` lists the departures D1–D11.

## Conventions

* `E` (states) is a finite-dimensional real normed space. In the maximum principle the control
  values lie in a finite-dimensional real normed space `V` and the boundary constraint takes
  values in a finite-dimensional real normed space `Q`; in Filippov's theorem `V` is a metric
  space. `V` carries its Borel σ-algebra. In the maximum principle, Agrachev and Sachkov's
  manifold `M` is an open set `Ω ⊆ E` (departure D1); in Filippov's theorem the states range over
  `E`.
* Time runs over `[0, T]` (`Icc 0 T`). A *control* is a measurable `u : ℝ → V` with `u(t) ∈ U` for
  `t ∈ [0, T]`, for a compact control set `U`. An *admissible pair* `(u, x)` from `x₀` on `[0, T]`
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
-/

@[expose] public section

-- BEGIN SHARED DEFINITIONS

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

end OptimalControlChallenge

end
