module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# The definitions of the main statements

The definitions that the statements of record in `OptimalControlChallenge.lean` use:

* control systems `x' = F(x, u)`, `u ∈ U`, with Carathéodory trajectories
  (`ControlSystem.IsAdmissible`) and their attainable sets at time `T`
  (`ControlSystem.reachableSet`) and up to time `T` (`ControlSystem.reachableSetLE`);
* the regularity of Agrachev and Sachkov's control systems (`ControlSystem.IsC1On`);
* the objects of the maximum principle (`Pontryagin`): admissible pairs in an open set, the cost,
  the Hamiltonian, the linearization along a reference pair, the adjoint equation, the maximum
  condition and strong local minimizers.

The block between the two marker comments is copied word for word into
`OptimalControlChallenge.lean` by `scripts/sync_challenge_defs.py` (CI checks the copy with
`--check`), so that the Challenge and the library elaborate the same constants, which Palomar's
Comparator requires. This module imports exactly what the Challenge imports, and nothing precedes
the block. The rest of the library builds on these definitions: Filippov's theorem in
`OptimalControl/ODE/ControlSystem.lean`, Carathéodory theory in `OptimalControl/ODE/`, the
maximum principle in `OptimalControl/Pontryagin/`.

Agrachev and Sachkov, *Control Theory from the Geometric Viewpoint* (Encyclopaedia of
Mathematical Sciences 87, Springer, 2004), are cited from the authors' draft (preface September
2003), whose page numbers are used; the departures D1–D11 from their text are listed in the
README.
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

end
