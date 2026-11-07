module

public import OptimalControl.ODE.LinearCaratheodory

/-!
# The Pontryagin maximum principle: definitions

The objects of Chapter 12 of A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the
Geometric Viewpoint* (Encyclopaedia of Mathematical Sciences 87, Springer, 2004; cited from the
authors' draft, preface September 2003, whose page numbers are used), read on an open subset `Ω`
of a finite-dimensional real normed space `E` (departure D1; the departures
from A–S are listed in the README):

* the control system `q' = f_u(q)`, `q ∈ Ω`, `u ∈ U ⊆ V` ((12.1), p. 163), with
  `ControlSystem.IsC1On f Ω U` for A–S's (10.2)–(10.4) (`C¹` for `C^∞`, D3) and `U` compact
  (D4);
* admissible pairs in `Ω` (`IsAdmissibleIn`): Carathéodory solutions
  (`ControlSystem.IsAdmissible`) with a measurable control with values in `U`, staying in `Ω`;
* the attainable set `A_{q₀}(t)` (§10.2, p. 134; `attainableSet`) and its local version
  (`localAttainableSet`: initial points `ψ(a)` with `a` near `a₀` and trajectories uniformly
  near the reference one), which is what the proofs use;
* the cost `J(u) = ∫₀ᵗ φ(q, u)` ((12.20), p. 175; `cost`);
* the Hamiltonian `h^ν_u(λ) = ⟨λ, f_u(q)⟩ + ν φ(q, u)` (Theorem 12.3, p. 176;
  `controlHamiltonian`); covectors are `StrongDual ℝ E` (`T*_q M = E*`);
* the field `g_{τ,u}(q₁) = (P^{t₁}_τ)_*(f_u - f_{ũ(τ)})(q₁)` of (12.12), p. 170 (`needleVector`),
  read pointwise (D2): the derivative of the flow along the reference trajectory is the resolvent
  of the variational equation (A–S's (2.19); `ControlSystem.fderiv_flow_eq_stateTransition`), so
  `g_{τ,u}(q₁) = R(τ, t₁)(f(q̃(τ), u) - f(q̃(τ), ũ(τ)))` with `R` the resolvent of
  `ξ' = ∂ₓf(q̃(t), ũ(t)) ξ`;
* the conditions of the maximum principle on a covector curve `p` (A–S's `λ_t`): the Hamiltonian
  system (12.4)/(12.30), which in coordinates is the adjoint equation
  `ṗ = -p ∘ ∂ₓf(q̃, ũ) - ν ∂ₓφ(q̃, ũ)` (`IsAdjoint`, integral form), and the maximality condition
  (12.5)/(12.31) for almost every `t` (`IsMaximal`);
* strong local minimizers of the problem with free terminal time, integral cost and the boundary
  condition `(q(0), q(t₁)) ∈ N ⊆ M × M` ((12.49)–(12.52), p. 183; `IsStrongLocalMinimizer`):
  A–S's optimality (a global minimum) generalized to a minimum among competitors with terminal
  time and trajectory uniformly close (departure D5).

This module defines `attainableSet`, `localAttainableSet` and `needleVector`. The other objects,
which the statements of record use, are defined in `OptimalControl/Defs.lean` (`IsAdmissibleIn`,
`cost`, `controlHamiltonian`, `linearization`, `IsAdjoint`, `IsMaximal`,
`IsStrongLocalMinimizer`, with `ControlSystem.IsAdmissible` and `ControlSystem.IsC1On`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal Interval

namespace Pontryagin

open ControlSystem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- The attainable set `A_{q₀}(T)` (A–S, §10.2, p. 134): the endpoints `x(T)` of the admissible
pairs in `Ω` on `[0, T]` from `q₀`. -/
def attainableSet (f : E → V → E) (Ω : Set E) (U : Set V) (q₀ : E) (T : ℝ) : Set E :=
  {y | ∃ u x, IsAdmissibleIn f Ω U q₀ T u x ∧ x T = y}

/-- The local attainable set at time `t₁` near a reference trajectory `q̃`, with initial points
`ψ(a)`: the endpoints `x(t₁)` of the admissible pairs in `Ω` from `ψ(a)` with `‖a - a₀‖ < ε` and
`‖x(t) - q̃(t)‖ < ε` on `[0, t₁]`. (A–S use the attainable set `A_{q₀}(t₁)`, `ψ` constant, and,
in the proof of Theorem 12.4 (2), initial points in `N₀`; the proofs only use competitors near the
reference, which is what this set records.) -/
def localAttainableSet {P : Type*} [NormedAddCommGroup P] (f : E → V → E) (Ω : Set E)
    (U : Set V) (ψ : P → E) (a₀ : P) (q : ℝ → E) (t₁ ε : ℝ) : Set E :=
  {y | ∃ (a : P) (u : ℝ → V) (x : ℝ → E), ‖a - a₀‖ < ε ∧ IsAdmissibleIn f Ω U (ψ a) t₁ u x ∧
    (∀ t ∈ Icc 0 t₁, ‖x t - q t‖ < ε) ∧ x t₁ = y}

/-- A–S's vector `g_{τ,u}(q₁) = (P^{t₁}_τ)_*(f_u - f_{ũ(τ)})(q₁)` of (12.12), p. 170, at
`q₁ = q̃(t₁)`, read pointwise: `R(τ, t₁)(f(q̃(τ), u) - f(q̃(τ), ũ(τ)))`, with `R` the resolvent of
the variational equation along `q̃` (departure D2). -/
noncomputable def needleVector (f : E → V → E) (ũ : ℝ → V) (q : ℝ → E) (t₁ τ : ℝ) (u : V) : E :=
  stateTransition (linearization f ũ q) τ t₁ (f (q τ) u - f (q τ) (ũ τ))

end Pontryagin
