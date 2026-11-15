# Optimal control in Lean: details

The full statements, the definitions they use, the supporting theory, the method of proof and the
files. The [README](../README.md) has the overview. The comparison with Agrachev and Sachkov's
Chapter 12, result by result, with the departures D1–D11 and the gaps found in the source, is in
[AGRACHEV_SACHKOV.md](AGRACHEV_SACHKOV.md). The comparison with Sussmann's paper on Noether's
theorem, with the readings S1–S8, is in [SUSSMANN.md](SUSSMANN.md).

- [Conventions](#conventions)
- [The statements of record](#the-statements-of-record)
- [The maximum principle](#the-maximum-principle)
- [Noether's theorem](#noethers-theorem)
- [Filippov's theorem and the existence of optimal controls](#filippovs-theorem-and-the-existence-of-optimal-controls)
- [Measurable selection](#measurable-selection)
- [Carathéodory theory](#carathéodory-theory)
- [Method](#method)
- [Files](#files)

## Conventions

`E`, `V`, `P` and `Q` are finite-dimensional real normed spaces: `E` is the state space, `V` the
space of control values (with its Borel σ-algebra), `P` and `Q` parametrize boundary conditions.
The state constraint `Ω ⊆ E` is open. In the maximum principle and in Filippov's theorem the
control set `U ⊆ V` is compact. Noether's theorem needs neither: there `V` is any type with a
σ-algebra and `U` any subset of it.

The declarations of the maximum principle are in the namespace `Pontryagin`, those on control
systems in `ControlSystem`.

## The statements of record

[`OptimalControlChallenge.lean`](../OptimalControlChallenge.lean) is the Lean statement of record.
It imports only Mathlib and states, with `sorry`:

- the maximum principle (`OptimalControlChallenge.maximum_principle`);
- Filippov's theorem (`OptimalControlChallenge.isCompact_reachableSet`,
  `OptimalControlChallenge.isCompact_reachableSetLE`);
- the existence of optimal controls (`OptimalControlChallenge.exists_optimal_fixedTime`,
  `OptimalControlChallenge.exists_optimal_freeTime`);
- Noether's theorem for optimal control (`OptimalControlChallenge.noether`).

Its module docstring explains every convention the statements use.
[`OptimalControlSolution.lean`](../OptimalControlSolution.lean) restates them word for word and
proves them from the library.

[`comparator.json`](../comparator.json) configures Palomar's Comparator, which checks that the
Solution proves exactly the Challenge's statements and uses only the standard axioms.

The definitions that the statements use are kept in
[`OptimalControl/Defs.lean`](../OptimalControl/Defs.lean) between two marker comments.
`python3 scripts/sync_challenge_defs.py` copies them word for word into the Challenge (CI checks
the copy with `--check`), so that the Challenge and the library elaborate the same constants.

The Challenge's statements are those of the library, with these differences, which
`OptimalControlSolution.lean` supplies:

- Filippov's theorem and the existence of optimal controls are stated without the Borel
  σ-algebra on `E` that the library's statements carry;
- the existence of optimal controls is also stated without the completeness of `E`;
- Filippov's theorem is stated without the hypothesis `0 ≤ M` (for `M < 0` the attainable sets
  are empty).

Noether's theorem is stated exactly as in the library.

[`formalization.yaml`](../formalization.yaml) holds the metadata (`formalization.yaml` v0.4): the
sources, the readings and departures, the related formal work and the production process.

## The maximum principle

[`Pontryagin.maximum_principle`](../OptimalControl/Pontryagin/MaximumPrinciple.lean#L320): the
maximum principle with free terminal time, an integral cost and mixed boundary conditions
`(q(0), q(T)) ∈ N`, for strong local minimizers. This is Agrachev and Sachkov's Theorem 12.5 with
the remark that follows it (free time), a case they leave to the reader.

```lean
theorem maximum_principle {Ω : Set E} (hΩ : IsOpen Ω) {U : Set V}
    (hU : IsCompact U) {f : E → V → E} (hf : IsC1On f Ω U) {φ : E → V → ℝ}
    (hφ : IsC1On φ Ω U) {N : Set (E × E)} {T : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    (hmin : IsStrongLocalMinimizer f φ Ω U N T ũ q) {G : E × E → Q}
    (hG : ContDiffAt ℝ 1 G (q 0, q T)) (hGsurj : Function.Surjective (fderiv ℝ G (q 0, q T)))
    (hG0 : G (q 0, q T) = 0) (hGN : ∀ᶠ z in 𝓝 (q 0, q T), G z = 0 → z ∈ N) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), ν ≤ 0 ∧ (∃ K, LipschitzOnWith K p (Icc 0 T)) ∧
      (∀ t ∈ Icc 0 T, (ν, p t) ≠ 0) ∧ IsAdjoint f φ ν ũ q T p ∧ IsMaximal f φ ν U ũ q T p ∧
      (∀ᵐ t ∂(volume.restrict (Icc 0 T)), controlHamiltonian f φ ν (q t) (p t) (ũ t) = 0) ∧
      ∀ v w : E, fderiv ℝ G (q 0, q T) (v, w) = 0 → -p 0 v + p T w = 0
```

In words: near `(q(0), q(T))` the set `N` contains the zeros of a `C¹` map `G` with surjective
derivative. Then there are `ν ≤ 0` and a Lipschitz covector curve `p` such that

- `(ν, p(t)) ≠ 0` for every `t`;
- the adjoint equation holds;
- the maximum condition and `H = 0` hold for almost every `t`;
- the transversality condition `(-p(0), p(T)) ⊥ ker G'(q(0), q(T))` holds.

The definitions ([`OptimalControl/Defs.lean`](../OptimalControl/Defs.lean)):

- [`ControlSystem.IsC1On f Ω U`](../OptimalControl/Defs.lean#L85): Agrachev and Sachkov's
  regularity (10.2)–(10.4) with `C¹` for `C^∞`: `(x, u) ↦ f x u` and `(x, u) ↦ ∂ₓf(x, u)` are
  continuous on `Ω × U`, and `f(·, u)` is differentiable on `Ω` for `u ∈ U`;
- [`IsAdmissibleIn f Ω U x₀ T u x`](../OptimalControl/Defs.lean#L105): `u` is measurable with
  values in `U` on `[0, T]`, `x` is continuous on `[0, T]` with values in `Ω` and
  `x(t) = x₀ + ∫₀ᵗ f(x(s), u(s)) ds` (a Carathéodory solution,
  [`ControlSystem.IsAdmissible`](../OptimalControl/Defs.lean#L57));
- [`IsStrongLocalMinimizer f φ Ω U N T ũ q`](../OptimalControl/Defs.lean#L149): `T > 0`,
  `(ũ, q)` is admissible in `Ω` on `[0, T]` with `(q(0), q(T)) ∈ N`, and for some `ε > 0` no
  admissible pair `(u', q')` in `Ω` on `[0, T']`, `T' > 0`, with `(q'(0), q'(T')) ∈ N`,
  `|T' - T| < ε` and `‖q'(σ T') - q(σ T)‖ < ε` for all `σ ∈ [0, 1]`, has a smaller cost
  `∫₀^{T'} φ(q', u')`;
- [`controlHamiltonian`](../OptimalControl/Defs.lean#L115):
  `controlHamiltonian f φ ν q p u = p (f q u) + ν * φ q u`;
- [`IsAdjoint f φ ν ũ q T p`](../OptimalControl/Defs.lean#L128): the adjoint equation
  `ṗ = -p ∘ ∂ₓf(q, ũ) - ν ∂ₓφ(q, ũ)` in integral form,
  `p(t) = p(T) + ∫ₜᵀ (p(r) ∘ ∂ₓf(q(r), ũ(r)) + ν ∂ₓφ(q(r), ũ(r))) dr` on `[0, T]`, the integrand
  being integrable;
- [`IsMaximal f φ ν U ũ q T p`](../OptimalControl/Defs.lean#L138): for almost every
  `t ∈ [0, T]`, `H(q(t), p(t), u) ≤ H(q(t), p(t), ũ(t))` for all `u ∈ U`.

<details>
<summary>The definitions in Lean</summary>

```lean
structure IsC1On (f : E → V → F) (Ω : Set E) (U : Set V) : Prop where
  continuousOn : ContinuousOn (fun p : E × V ↦ f p.1 p.2) (Ω ×ˢ U)
  differentiableAt : ∀ x ∈ Ω, ∀ u ∈ U, DifferentiableAt ℝ (f · u) x
  continuousOn_fderiv : ContinuousOn (fun p : E × V ↦ fderiv ℝ (f · p.2) p.1) (Ω ×ˢ U)

def IsAdmissible (F : E → V → E) (U : Set V) (x₀ : E) (T : ℝ) (u : ℝ → V) (x : ℝ → E) : Prop :=
  Measurable u ∧ (∀ t ∈ Icc 0 T, u t ∈ U) ∧ ContinuousOn x (Icc 0 T) ∧
    IntervalIntegrable (fun s ↦ F (x s) (u s)) volume 0 T ∧
    ∀ t ∈ Icc 0 T, x t = x₀ + ∫ s in (0 : ℝ)..t, F (x s) (u s)

def IsAdmissibleIn (f : E → V → E) (Ω : Set E) (U : Set V) (x₀ : E) (T : ℝ) (u : ℝ → V)
    (x : ℝ → E) : Prop :=
  IsAdmissible f U x₀ T u x ∧ ∀ t ∈ Icc 0 T, x t ∈ Ω

def attainableSet (f : E → V → E) (Ω : Set E) (U : Set V) (q₀ : E) (T : ℝ) : Set E :=
  {y | ∃ u x, IsAdmissibleIn f Ω U q₀ T u x ∧ x T = y}

noncomputable def cost (φ : E → V → ℝ) (T : ℝ) (u : ℝ → V) (x : ℝ → E) : ℝ :=
  ∫ t in (0 : ℝ)..T, φ (x t) (u t)

def controlHamiltonian (f : E → V → E) (φ : E → V → ℝ) (ν : ℝ) (q : E) (p : StrongDual ℝ E)
    (u : V) : ℝ :=
  p (f q u) + ν * φ q u

noncomputable def linearization (f : E → V → E) (ũ : ℝ → V) (q : ℝ → E) (t : ℝ) : E →L[ℝ] E :=
  fderiv ℝ (f · (ũ t)) (q t)

noncomputable def needleVector (f : E → V → E) (ũ : ℝ → V) (q : ℝ → E) (t₁ τ : ℝ) (u : V) : E :=
  stateTransition (linearization f ũ q) τ t₁ (f (q τ) u - f (q τ) (ũ τ))

def IsAdjoint (f : E → V → E) (φ : E → V → ℝ) (ν : ℝ) (ũ : ℝ → V) (q : ℝ → E) (T : ℝ)
    (p : ℝ → StrongDual ℝ E) : Prop :=
  IntervalIntegrable (fun r ↦ (p r).comp (linearization f ũ q r) +
      ν • fderiv ℝ (φ · (ũ r)) (q r)) volume 0 T ∧
    ∀ t ∈ Icc 0 T, p t = p T + ∫ r in t..T,
      ((p r).comp (linearization f ũ q r) + ν • fderiv ℝ (φ · (ũ r)) (q r))

def IsMaximal (f : E → V → E) (φ : E → V → ℝ) (ν : ℝ) (U : Set V) (ũ : ℝ → V) (q : ℝ → E)
    (T : ℝ) (p : ℝ → StrongDual ℝ E) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Icc 0 T)), ∀ u ∈ U,
    controlHamiltonian f φ ν (q t) (p t) u ≤ controlHamiltonian f φ ν (q t) (p t) (ũ t)

def IsStrongLocalMinimizer (f : E → V → E) (φ : E → V → ℝ) (Ω : Set E) (U : Set V)
    (N : Set (E × E)) (T : ℝ) (u : ℝ → V) (q : ℝ → E) : Prop :=
  0 < T ∧ IsAdmissibleIn f Ω U (q 0) T u q ∧ (q 0, q T) ∈ N ∧
    ∃ ε > 0, ∀ (T' : ℝ) (u' : ℝ → V) (q' : ℝ → E), 0 < T' →
      IsAdmissibleIn f Ω U (q' 0) T' u' q' → (q' 0, q' T') ∈ N → |T' - T| < ε →
      (∀ σ ∈ Icc (0 : ℝ) 1, ‖q' (σ * T') - q (σ * T)‖ < ε) → cost φ T u q ≤ cost φ T' u' q'
```

[`attainableSet`](../OptimalControl/Pontryagin/Defs.lean#L60) and
[`needleVector`](../OptimalControl/Pontryagin/Defs.lean#L76) are defined in
[`OptimalControl/Pontryagin/Defs.lean`](../OptimalControl/Pontryagin/Defs.lean), the others in
[`OptimalControl/Defs.lean`](../OptimalControl/Defs.lean).

[`stateTransition A s t`](../OptimalControl/ODE/LinearCaratheodory.lean#L66) is the resolvent of
`ξ' = A(t) ξ` from time `s` to time `t`.
</details>

## Noether's theorem

[`Pontryagin.noether`](../OptimalControl/Pontryagin/Noether.lean#L690): Noether's theorem for
optimal control, H. J. Sussmann's Theorem 4.1 (1995) for one vector field. Along every extremal
of the maximum principle, the momentum of an infinitesimal symmetry is constant.

```lean
theorem noether (hΩ : IsOpen Ω) (hf : ∀ u ∈ U, ContDiffOn ℝ 1 (f · u) Ω)
    (hφ : ∀ u ∈ U, ContDiffOn ℝ 1 (φ · u) Ω) {Y : E → E}
    (hY : IsInfinitesimalSymmetry f φ Ω U Y) {T ν : ℝ} {ũ : ℝ → V} {q : ℝ → E}
    {p : ℝ → StrongDual ℝ E} (href : IsAdmissibleIn f Ω U (q 0) T ũ q)
    (hadj : IsAdjoint f φ ν ũ q T p) (hmax : IsMaximal f φ ν U ũ q T p) :
    ∀ t ∈ Icc 0 T, momentum Y (q t) (p t) = momentum Y (q 0) (p 0)
```

In words: `f(·, u)` and `φ(·, u)` are `C¹` on the open set `Ω` for every `u ∈ U`, and `Y` is an
infinitesimal symmetry of `(Ω, U, f, φ)`. If `(ũ, q)` is an admissible pair in `Ω` on `[0, T]`
and `p` satisfies the adjoint equation and the maximum condition for some multiplier `ν ∈ ℝ`,
then `p(t)(Y(q(t)))` is constant on `[0, T]`. Here `V` is any type with a σ-algebra, and `U`
any subset of it. Neither `ν ≤ 0`, nor the vanishing or constancy of the Hamiltonian, nor
`(ν, p) ≠ 0`, nor optimality is assumed.

The definitions ([`OptimalControl/Defs.lean`](../OptimalControl/Defs.lean), shared with the
Challenge):

- [`IsIntegralCurveIn Y Ω x s γ`](../OptimalControl/Defs.lean#L167): `γ` is a Carathéodory
  integral curve of `Y` from `x` in `Ω`, on the interval between `0` and `s`;
- [`flowDomain Y Ω s`](../OptimalControl/Defs.lean#L174) and
  [`flowMap Y Ω s`](../OptimalControl/Defs.lean#L181): the domain `D_s` of the time-`s` map
  `e^{sY}` (the initial points of such curves), and its value, chosen among the curves (for `Y`
  of class `C¹` they agree,
  [`flowMap_eq_of_isIntegralCurveIn`](../OptimalControl/Pontryagin/Noether.lean#L304));
- [`PermutesFamily f φ U σ V₁`](../OptimalControl/Defs.lean#L189): Sussmann's conditions
  (i)–(ii). For every `u ∈ U` there are `u₁, u₂ ∈ U` with `dσ(x) f_u(x) = f_{u₁}(σ(x))`,
  `φ_{u₁}(σ(x)) = φ_u(x)`, `dσ(x) f_{u₂}(x) = f_u(σ(x))` and `φ_u(σ(x)) = φ_{u₂}(x)` on `V₁`: the
  controls may be permuted, and the cost is invariant;
- [`IsSymmetry f φ Ω U σ V₁ V₂`](../OptimalControl/Defs.lean#L198): `σ` is a `C¹`
  diffeomorphism from `V₁` onto `V₂`, open subsets of `Ω`, satisfying (i)–(ii);
- [`IsInfinitesimalSymmetry f φ Ω U Y`](../OptimalControl/Defs.lean#L212): `Y` is `C¹` on `Ω`
  and every `e^{sY} : D_s → D_{-s}` is a symmetry;
- [`momentum Y x p`](../OptimalControl/Defs.lean#L220): `p(Y(x))`, Sussmann's `h_Y`.

The module also proves:

- the form for a Lie algebra `L` acting by infinitesimal symmetries, with the momentum map
  `μ^τ(q(t), p(t)) ∈ L*`
  ([`Pontryagin.noether_momentumMap`](../OptimalControl/Pontryagin/Noether.lean#L840));
- Theorem 4.1 as Sussmann states it, for his biextremals
  ([`Pontryagin.sussmann_theorem4_1`](../OptimalControl/Pontryagin/Noether.lean#L919));
- the maximum principle whose multiplier makes every such momentum constant
  ([`Pontryagin.maximum_principle_noether`](../OptimalControl/Pontryagin/Noether.lean#L943));
- the infinitesimal symmetries given by an explicit global flow that satisfies (i)–(ii)
  ([`Pontryagin.isInfinitesimalSymmetry_of_flow`](../OptimalControl/Pontryagin/Noether.lean#L499));
- an example: for `ż = a z + u` on `ℂ` with `|u| ≤ 1` and cost `‖z‖² + ‖u‖²`, the rotations are
  symmetries that permute the controls, and the angular momentum `p(i q)` is constant
  ([`Pontryagin.noether_rotation`](../OptimalControl/Pontryagin/Noether.lean#L1006)).

<details>
<summary>The definitions in Lean</summary>

```lean
def IsIntegralCurveIn (Y : E → E) (Ω : Set E) (x : E) (s : ℝ) (γ : ℝ → E) : Prop :=
  ContinuousOn γ [[0, s]] ∧ IntervalIntegrable (fun r ↦ Y (γ r)) volume 0 s ∧
    (∀ r ∈ [[0, s]], γ r = x + ∫ ρ in (0 : ℝ)..r, Y (γ ρ)) ∧ ∀ r ∈ [[0, s]], γ r ∈ Ω

def flowDomain (Y : E → E) (Ω : Set E) (s : ℝ) : Set E :=
  {x | ∃ γ, IsIntegralCurveIn Y Ω x s γ}

noncomputable def flowMap (Y : E → E) (Ω : Set E) (s : ℝ) (x : E) : E :=
  if h : ∃ γ, IsIntegralCurveIn Y Ω x s γ then h.choose s else x

def PermutesFamily (f : E → V → E) (φ : E → V → ℝ) (U : Set V) (σ : E → E) (V₁ : Set E) :
    Prop :=
  (∀ u ∈ U, ∃ u₁ ∈ U, ∀ x ∈ V₁, fderiv ℝ σ x (f x u) = f (σ x) u₁ ∧ φ (σ x) u₁ = φ x u) ∧
    ∀ u ∈ U, ∃ u₂ ∈ U, ∀ x ∈ V₁, fderiv ℝ σ x (f x u₂) = f (σ x) u ∧ φ (σ x) u = φ x u₂

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

structure IsInfinitesimalSymmetry (f : E → V → E) (φ : E → V → ℝ) (Ω : Set E) (U : Set V)
    (Y : E → E) : Prop where
  contDiffOn : ContDiffOn ℝ 1 Y Ω
  isSymmetry : ∀ s : ℝ,
    IsSymmetry f φ Ω U (flowMap Y Ω s) (flowDomain Y Ω s) (flowDomain Y Ω (-s))

def momentum (Y : E → E) (x : E) (p : StrongDual ℝ E) : ℝ :=
  p (Y x)
```

`[[0, s]]` is the interval between `0` and `s` (`Set.uIcc`).
</details>

## Filippov's theorem and the existence of optimal controls

Filippov's theorem (Agrachev and Sachkov, Theorem 10.1): for `F` jointly continuous, `U`
compact, convex velocity sets `F(x, U)` and velocities bounded along admissible trajectories, the
attainable sets are compact. Here `V` need only be a metric space with its Borel σ-algebra.

- At time `T`:
  [`ControlSystem.isCompact_reachableSet`](../OptimalControl/ODE/ControlSystem.lean#L405).
- Up to time `T`:
  [`ControlSystem.isCompact_reachableSetLE`](../OptimalControl/ODE/ControlSystem.lean#L383).

```lean
theorem isCompact_reachableSet (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hU : IsCompact U) (hconv : ∀ z, Convex ℝ (F z '' U)) {x₀ : E} {T M : ℝ} (hT : 0 ≤ T)
    (hM : 0 ≤ M)
    (hbd : ∀ u x, IsAdmissible F U x₀ T u x → ∀ s ∈ Icc 0 T, ‖F (x s) (u s)‖ ≤ M) :
    IsCompact (reachableSet F U x₀ T)
```

Hence optimal controls exist for integral costs when the velocity sets extended by the cost,
`{(F(x, u), φ(x, u)) | u ∈ U}`, are convex:

- with fixed terminal time,
  [`ControlSystem.exists_optimal_fixedTime`](../OptimalControl/ODE/ControlSystem.lean#L514);
- with free terminal time,
  [`ControlSystem.exists_optimal_freeTime`](../OptimalControl/ODE/ControlSystem.lean#L548).

```lean
theorem exists_optimal_fixedTime (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hU : IsCompact U) (hφ : Continuous fun p : E × V ↦ φ p.1 p.2)
    (hconv : ∀ z, Convex ℝ ((fun w ↦ (F z w, φ z w)) '' U)) {M : ℝ}
    (hFM : ∀ z, ∀ w ∈ U, ‖F z w‖ ≤ M) (hT : 0 ≤ T) {x₁ : E}
    (h₁ : x₁ ∈ reachableSet F U x₀ T) :
    ∃ u x, IsAdmissible F U x₀ T u x ∧ x T = x₁ ∧
      ∀ u' x', IsAdmissible F U x₀ T u' x' → x' T = x₁ →
        ∫ t in (0 : ℝ)..T, φ (x t) (u t) ≤ ∫ t in (0 : ℝ)..T, φ (x' t) (u' t)
```

[`OptimalControl/ODE/StateConstraint.lean`](../OptimalControl/ODE/StateConstraint.lean) proves
the same two results for problems posed on part of the space
([`ControlSystem.isCompact_constrainedEndpoints`](../OptimalControl/ODE/StateConstraint.lean#L309),
[`ControlSystem.exists_optimal_constrained`](../OptimalControl/ODE/StateConstraint.lean#L378)):

- a closed state constraint `S`, with `F` and `φ` continuous, the velocities bounded and the
  velocity sets convex only on `S × U`;
- a compact set `K₀` of initial points;
- a closed relation `N` between initial and terminal points;
- terminal times in a window `[T₀, T₁]`.

The argument is the same: uniform limits of trajectories in the closed set `S` stay in `S`, so
continuity and convexity are needed only there.

## Measurable selection

Zeros of a Carathéodory function on a compact set can be chosen measurably (the
Kuratowski–Ryll-Nardzewski construction; Filippov's lemma). `V` is a metric space with its Borel
σ-algebra.

- [`MeasureTheory.exists_measurable_forall_mem_ae_eq_zero`](../OptimalControl/MeasureTheory/MeasurableSelection.lean#L261):
  zeros for almost every `t`;
- [`MeasureTheory.exists_measurable_forall_mem_and_eq_zero`](../OptimalControl/MeasureTheory/MeasurableSelection.lean#L215):
  zeros for every `t`.

```lean
theorem exists_measurable_forall_mem_ae_eq_zero {μ : Measure α} {U : Set V} (hU : IsCompact U)
    (hUne : U.Nonempty) {g : α → V → E} (hmeas : ∀ w ∈ U, Measurable fun t ↦ g t w)
    (hcont : ∀ t, ContinuousOn (g t) U) (hex : ∀ᵐ t ∂μ, ∃ w ∈ U, g t w = 0) :
    ∃ σ : α → V, Measurable σ ∧ (∀ t, σ t ∈ U) ∧ ∀ᵐ t ∂μ, g t (σ t) = 0
```

## Carathéodory theory

For a control system `y' = f(y, u(t))` with `f` continuous on `E × U` and Lipschitz in the state,
and `u` measurable with values in the compact set `U`:

- [`Caratheodory.lean`](../OptimalControl/ODE/Caratheodory.lean): existence and uniqueness of
  Carathéodory solutions, forward and backward in time
  ([`ControlSystem.exists_isSolution`](../OptimalControl/ODE/Caratheodory.lean#L412),
  [`ControlSystem.IsSolution.eqOn`](../OptimalControl/ODE/Caratheodory.lean#L553)), the integral
  Gronwall inequality
  ([`ControlSystem.le_mul_exp_of_le_add_integral`](../OptimalControl/ODE/Caratheodory.lean#L240)),
  the flow and its cocycle property
  ([`ControlSystem.flow_flow`](../OptimalControl/ODE/Caratheodory.lean#L582)), and the cut-off of
  a `C¹` system near a compact subset of `Ω`
  ([`ControlSystem.IsC1On.exists_cutoff`](../OptimalControl/ODE/Caratheodory.lean#L143));
- [`LinearCaratheodory.lean`](../OptimalControl/ODE/LinearCaratheodory.lean): the resolvent of a
  linear equation with bounded measurable coefficients and the adjoint equation, with uniqueness
  ([`ControlSystem.adjoint_stateTransition`](../OptimalControl/ODE/LinearCaratheodory.lean#L380),
  [`ControlSystem.eq_comp_stateTransition_of_adjoint`](../OptimalControl/ODE/LinearCaratheodory.lean#L406));
- [`FlowDerivative.lean`](../OptimalControl/ODE/FlowDerivative.lean): the derivative of the flow
  in the initial point is the resolvent of the variational equation
  ([`ControlSystem.hasFDerivAt_flow`](../OptimalControl/ODE/FlowDerivative.lean#L168),
  [`ControlSystem.fderiv_flow_eq_stateTransition`](../OptimalControl/ODE/FlowDerivative.lean#L392));
- [`VariationsFormula.lean`](../OptimalControl/ODE/VariationsFormula.lean): the variations
  formula along a trajectory and Agrachev and Sachkov's Proposition 11.3 read pointwise
  ([`ControlSystem.flow_flow_eq_add_integral_variationField`](../OptimalControl/ODE/VariationsFormula.lean#L101),
  [`ControlSystem.adjoint_fderiv_flow`](../OptimalControl/ODE/VariationsFormula.lean#L336));
- [`NeedleVariation.lean`](../OptimalControl/ODE/NeedleVariation.lean): needle variations; the
  end-point map of finitely many needles is Lipschitz and differentiable at `σ = 0` within the
  orthant
  ([`ControlSystem.lipschitzOnWith_needle`](../OptimalControl/ODE/NeedleVariation.lean#L242),
  [`ControlSystem.hasFDerivWithinAt_needle`](../OptimalControl/ODE/NeedleVariation.lean#L522));
- [`TimeChange.lean`](../OptimalControl/ODE/TimeChange.lean): measurable changes of time
  ([`ControlSystem.IsAdmissible.timeChange`](../OptimalControl/ODE/TimeChange.lean#L357),
  [`ControlSystem.IsAdmissible.timeChangeOn`](../OptimalControl/ODE/TimeChange.lean#L304));
- Lebesgue points
  ([`ae_isLebesguePointWithin`](../OptimalControl/MeasureTheory/LebesguePoints.lean#L62),
  [`IsLebesguePointWithin.exists_near`](../OptimalControl/MeasureTheory/LebesguePoints.lean#L113))
  and convex cones
  ([`exists_dual_ne_zero_nonpos_of_ne_top`](../OptimalControl/Convex/Cone/Support.lean#L46),
  [`exists_finset_hull_eq_top`](../OptimalControl/Convex/Cone/Support.lean#L83),
  [`exists_forall_hull_eq_top_of_dist_lt`](../OptimalControl/Convex/Cone/Support.lean#L123)).

## Method

The maximum principle follows Agrachev and Sachkov's proof (Chapter 12), in coordinates on an
open subset of `E`.

1. **Needle vectors.** At a Lebesgue point `τ` of the reference control and `u ∈ U`, the vector
   `g_{τ,u}(q₁)` of (12.12) is `R(τ, t₁)(f(q(τ), u) - f(q(τ), ũ(τ)))`, with `R` the resolvent
   of the variational equation along the reference trajectory (`needleVector`).
2. **Lemma 12.2** (`lemma12_2_local`). If these vectors generate the whole space as a convex
   cone, finitely many of them do. A needle time that repeats an earlier one, or that equals
   `t₁`, is moved to a nearby Lebesgue point of `(0, t₁)`, which keeps the generation since it
   survives small perturbations. After a cut-off of the system near the reference trajectory,
   the end point of the needle variations is a map of `(a, σ) ∈ P × ℝᵏ₊` (`a` moves the initial
   point) that is Lipschitz and differentiable at `(a₀, 0)` within the cone, with derivative
   given by the variations formula. Its derivative maps the cone onto the space, and Lemma 12.1
   on the cone makes the end point an interior point of the attainable set.
3. **Lemma 12.1** (`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`) is proved as
   Agrachev and Sachkov prove it. The rescaled maps `α⁻¹F(α ·)` are Lipschitz with a common
   constant, hence equicontinuous, and converge pointwise, hence uniformly (Mathlib's Ascoli
   lemma `Equicontinuous.tendsto_uniformFun_iff_pi`), to the derivative. **Brouwer's fixed-point
   theorem**, taken from the [FixedPoint](https://github.com/vltanh/lean4-fixed-point) package
   (`Brouwer.exists_fixedPoint`), then gives the openness.
4. **Theorem 12.1** (`theorem12_1`, and `exists_costate_of_boundary` with initial points `ψ(a)`
   and an end-point map `Φ`). At a point that is not interior, the cone of the variations is not
   the whole space, so a covector `ξ ≠ 0` supports it. Then `p(t) = ξ ∘ Φ' ∘ R(t, t₁)` solves
   the adjoint equation (Proposition 11.3, read pointwise), and the supporting inequality at the
   Lebesgue points, which have full measure, is the maximum condition.
5. **Theorems 12.2–12.5** are reduced to this by Agrachev and Sachkov's auxiliary systems: the
   time-scaled system `q' = v f(q, u)` (free time), the cost-extended system `y' = φ(q, u) + v`,
   `q' = f(q, u)` (cost), and the doubled system `x' = 0`, `q' = f(q, u)` on `E × E` (mixed
   boundary conditions). On a product state space whose dynamics do not depend on one factor,
   that factor's part of the costate is constant
   ([`Pontryagin.Reduction.adjoint_prod`](../OptimalControl/Pontryagin/IntegralCost.lean#L116)).
6. **`maximum_principle`** applies the three reductions at once, through one auxiliary system
   `y' = v (φ(q, u) + β)`, `x' = 0`, `q' = v f(q, u)` with controls
   `(v, β, u) ∈ [1 - δ, 1 + δ] × [0, 1] × U`, to `exists_costate_of_boundary`. Strong local
   optimality is what makes the end point non-interior. The pointwise nontriviality
   `(ν, p(t)) ≠ 0` uses the uniqueness for the adjoint equation.

The Carathéodory theory beneath (existence, uniqueness and differentiable dependence of
solutions, the cut-off) is proved by Picard iteration and Gronwall's inequality.

Filippov's theorem is proved by the standard argument: the trajectories are equi-Lipschitz, a
cluster point exists by Tychonoff's theorem, its derivative lies in the convex velocity set almost
everywhere, and a measurable control realizing it is found by measurable selection.

Noether's theorem follows Sussmann's proof of his Theorem 3.1, applied to the cotangent lift
`ρ_s(x, p) = (e^{sY}(x), p ∘ (De^{sY}(x))⁻¹)` of the flow of `Y` (departure S4).

1. **Cotangent lift.** For a symmetry `σ` and `u ∈ U`, the `u₂` of (i)–(ii) gives
   `H(σ(x), p ∘ dσ(x)⁻¹, u) = H(x, p, u₂)`
   ([`IsSymmetry.controlHamiltonian_cotangentLift`](../OptimalControl/Pontryagin/Noether.lean#L576)).
2. **The flow at `s = 0`.** Near `x`, `Y` equals a bounded `C¹` field, whose flow is `e^{sY}`
   for small `s`. So `e^{sY}(x)` has derivative `Y(x)` at `s = 0`, and `De^{sY}(x)`, the
   resolvent of the variational equation, has derivative `DY(x)`
   ([`hasDerivAt_fderiv_flowMap_zero`](../OptimalControl/Pontryagin/Noether.lean#L427)).
3. **The bracket vanishes.** If `u` maximizes `H(x, p, ·)`, then `s ↦ H(ρ_s(x, p), u)` has a
   maximum at `s = 0`, so its derivative `p([Y, f_u](x)) + ν Dφ_u(x) Y(x)` vanishes
   ([`IsInfinitesimalSymmetry.bracket_eq_zero`](../OptimalControl/Pontryagin/Noether.lean#L609)).
4. **The momentum is constant.** `t ↦ p(t)(Y(q(t)))` is absolutely continuous, and at almost
   every `t` its derivative is minus the bracket of step 3, hence `0`.

## Files

| Path | Content |
| --- | --- |
| [`OptimalControl.lean`](../OptimalControl.lean) | imports the whole library |
| [`OptimalControl/Pontryagin.lean`](../OptimalControl/Pontryagin.lean) | imports the maximum principle and Noether's theorem, and through them the modules they use |
| [`OptimalControl/Defs.lean`](../OptimalControl/Defs.lean) | the definitions that the statements of record use (shared with the Challenge): admissible pairs, attainable sets, `IsC1On`, cost, Hamiltonian, the adjoint equation, the maximum condition, strong local minimizers; integral curves and flows, symmetries, infinitesimal symmetries, momentum |
| [`OptimalControl/MeasureTheory/MeasurableSelection.lean`](../OptimalControl/MeasureTheory/MeasurableSelection.lean) | measurable selection of zeros of Carathéodory functions on a compact set; measurability of `{t \| ∃ w ∈ C, g t w = 0}` |
| [`OptimalControl/MeasureTheory/LebesguePoints.lean`](../OptimalControl/MeasureTheory/LebesguePoints.lean) | Lebesgue points of a function within an interval: almost every point is one, and they are dense |
| [`OptimalControl/ODE/ControlSystem.lean`](../OptimalControl/ODE/ControlSystem.lean) | Filippov's theorem, existence of optimal controls; the fundamental theorem of calculus for Lipschitz curves |
| [`OptimalControl/ODE/StateConstraint.lean`](../OptimalControl/ODE/StateConstraint.lean) | Filippov's theorem and the existence of optimal controls with a closed state constraint, a compact set of initial points, a closed endpoint relation and a window of terminal times |
| [`OptimalControl/ODE/Caratheodory.lean`](../OptimalControl/ODE/Caratheodory.lean) | bounded `C¹` and Lipschitz control systems, existence and uniqueness of Carathéodory solutions, the flow, Gronwall's inequality, the cut-off |
| [`OptimalControl/ODE/LinearCaratheodory.lean`](../OptimalControl/ODE/LinearCaratheodory.lean) | the resolvent of a linear equation with measurable coefficients, the adjoint equation |
| [`OptimalControl/ODE/FlowDerivative.lean`](../OptimalControl/ODE/FlowDerivative.lean) | the derivative of the flow in the initial point is the resolvent of the variational equation |
| [`OptimalControl/ODE/VariationsFormula.lean`](../OptimalControl/ODE/VariationsFormula.lean) | the variations formula along a trajectory; Proposition 11.3 read pointwise |
| [`OptimalControl/ODE/NeedleVariation.lean`](../OptimalControl/ODE/NeedleVariation.lean) | needle variations of a control and the derivative of their end-point map |
| [`OptimalControl/ODE/TimeChange.lean`](../OptimalControl/ODE/TimeChange.lean) | measurable changes of time |
| [`OptimalControl/Convex/Cone/Support.lean`](../OptimalControl/Convex/Cone/Support.lean) | supporting hyperplanes and finite generation of convex cones |
| [`OptimalControl/Convex/Cone/Openness.lean`](../OptimalControl/Convex/Cone/Openness.lean) | openness at the vertex of a cone (Lemma 12.1 with its Remark (1)), by Brouwer's theorem |
| [`OptimalControl/Pontryagin/Defs.lean`](../OptimalControl/Pontryagin/Defs.lean) | attainable sets in `Ω`, local attainable sets, needle vectors |
| [`OptimalControl/Pontryagin/Geometric.lean`](../OptimalControl/Pontryagin/Geometric.lean) | Lemmas 12.1, 12.2 and Theorem 12.1, and the general form `exists_costate_of_boundary` |
| [`OptimalControl/Pontryagin/FreeTime.lean`](../OptimalControl/Pontryagin/FreeTime.lean) | Theorem 12.2 (free time) |
| [`OptimalControl/Pontryagin/IntegralCost.lean`](../OptimalControl/Pontryagin/IntegralCost.lean) | Theorems 12.3–12.5 (integral cost, fixed time, boundary conditions) |
| [`OptimalControl/Pontryagin/MaximumPrinciple.lean`](../OptimalControl/Pontryagin/MaximumPrinciple.lean) | the maximum principle with free time, cost and mixed boundary conditions |
| [`OptimalControl/Pontryagin/Noether.lean`](../OptimalControl/Pontryagin/Noether.lean) | Noether's theorem for optimal control (Sussmann, Theorem 4.1): flows of `C¹` fields, the cotangent lift of a symmetry, the vanishing bracket, the conserved momentum; the Lie-algebra form, Sussmann's form for biextremals, the corollary of the maximum principle; symmetries from explicit flows, rotations of the plane |
| [`OptimalControlChallenge.lean`](../OptimalControlChallenge.lean), [`OptimalControlSolution.lean`](../OptimalControlSolution.lean), [`comparator.json`](../comparator.json), [`formalization.yaml`](../formalization.yaml) | the statements of record, their proofs, Comparator's configuration, the metadata (Palomar) |
| [`scripts/Audit.lean`](../scripts/Audit.lean) | the axiom audit |
| [`scripts/sync_challenge_defs.py`](../scripts/sync_challenge_defs.py) | copies the shared definitions into the Challenge (`--check`: checks the copy) |
| [`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml) | CI: build without warnings, the Challenge, audit, import list of the audit, the Challenge's copy of the definitions, line lengths |
| [`.github/workflows/palomar_preflight.yml`](../.github/workflows/palomar_preflight.yml) | Palomar's mechanical verification of a commit, run only on demand |
