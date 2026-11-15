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
  condition and strong local minimizers;
* the objects of Noether's theorem (`Pontryagin`, after Sussmann): integral curves and flows of a
  vector field in an open set, symmetries and infinitesimal symmetries of an optimal control
  system, and the momentum of a vector field.

The block between the two marker comments is copied word for word into
`OptimalControlChallenge.lean` by `scripts/sync_challenge_defs.py` (CI checks the copy with
`--check`), so that the Challenge and the library elaborate the same constants, which Palomar's
Comparator requires. This module imports exactly what the Challenge imports, and nothing precedes
the block. The rest of the library builds on these definitions: Filippov's theorem in
`OptimalControl/ODE/ControlSystem.lean`, Carathéodory theory in `OptimalControl/ODE/`, the
maximum principle in `OptimalControl/Pontryagin/`, Noether's theorem in
`OptimalControl/Pontryagin/Noether.lean`.

Agrachev and Sachkov, *Control Theory from the Geometric Viewpoint* (Encyclopaedia of
Mathematical Sciences 87, Springer, 2004), are cited from the authors' draft (preface September
2003), whose page numbers are used; the departures D1–D11 from their text are listed in
`docs/AGRACHEV_SACHKOV.md`. H. J. Sussmann, *Symmetries and integrals of motion in optimal
control* (Banach Center Publications 32, 1995, pp. 379–393), is cited with the page numbers of the
published paper; its readings S1–S8 are listed in `docs/SUSSMANN.md`.
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

end
