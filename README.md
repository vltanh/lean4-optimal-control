# Optimal control in Lean

[![Lean Action CI](https://github.com/vltanh/lean4-optimal-control/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-optimal-control/actions/workflows/lean_action_ci.yml)

Optimal control theory in Lean 4 with Mathlib: control systems with Carathéodory trajectories,
**Filippov's theorem** on the compactness of attainable sets and the existence of optimal controls,
and **the Pontryagin maximum principle** with free terminal time, an integral cost and mixed
boundary conditions, for strong local minimizers, proved by the argument of Agrachev and Sachkov
(Chapter 12 of *Control Theory from the Geometric Viewpoint*).

Everything is proved. There is no `sorry`, no `axiom` and no `native_decide`, and
`lake env lean scripts/Audit.lean` checks that the main theorems and every declaration of the
library, private and auxiliary ones included, depend only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound` (it fails on any other axiom, `sorryAx` included).

## Main results

`E`, `V`, `P` and `Q` are finite-dimensional real normed spaces: `E` is the state space, `V` the
space of control values (with its Borel σ-algebra), `P` and `Q` parametrize boundary conditions.
The control set `U ⊆ V` is compact and the state constraint `Ω ⊆ E` is open. The declarations of
the maximum principle are in the namespace `Pontryagin`, those on control systems in
`ControlSystem`.

### The maximum principle

[`Pontryagin.maximum_principle`](OptimalControl/Pontryagin/MaximumPrinciple.lean): the maximum
principle with free terminal time, an integral cost and mixed boundary conditions
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
derivative; then there are `ν ≤ 0` and a Lipschitz covector curve `p` with `(ν, p(t)) ≠ 0` for
every `t`, the adjoint equation, the maximum condition and `H = 0` for almost every `t`, and the
transversality condition `(-p(0), p(T)) ⊥ ker G'(q(0), q(T))`. The definitions
([`OptimalControl/Pontryagin/Defs.lean`](OptimalControl/Pontryagin/Defs.lean),
[`OptimalControl/ODE/Caratheodory.lean`](OptimalControl/ODE/Caratheodory.lean),
[`OptimalControl/ODE/ControlSystem.lean`](OptimalControl/ODE/ControlSystem.lean)):

- `ControlSystem.IsC1On f Ω U`: Agrachev and Sachkov's regularity (10.2)–(10.4) with `C¹` for
  `C^∞`: `(x, u) ↦ f x u` and `(x, u) ↦ ∂ₓf(x, u)` are continuous on `Ω × U`, and `f(·, u)` is
  differentiable on `Ω` for `u ∈ U`;
- `IsAdmissibleIn f Ω U x₀ T u x`: `u` is measurable with values in `U` on `[0, T]`, `x` is
  continuous on `[0, T]` with values in `Ω` and `x(t) = x₀ + ∫₀ᵗ f(x(s), u(s)) ds` (a
  Carathéodory solution, `ControlSystem.IsAdmissible`);
- `IsStrongLocalMinimizer f φ Ω U N T ũ q`: `T > 0`, `(ũ, q)` is admissible in `Ω` on `[0, T]`
  with `(q(0), q(T)) ∈ N`, and for some `ε > 0` no admissible pair `(u', q')` in `Ω` on
  `[0, T']`, `T' > 0`, with `(q'(0), q'(T')) ∈ N`, `|T' - T| < ε` and
  `‖q'(σ T') - q(σ T)‖ < ε` for all `σ ∈ [0, 1]`, has a smaller cost `∫₀^{T'} φ(q', u')`;
- `controlHamiltonian f φ ν q p u = p (f q u) + ν * φ q u`;
- `IsAdjoint f φ ν ũ q T p`: the adjoint equation `ṗ = -p ∘ ∂ₓf(q, ũ) - ν ∂ₓφ(q, ũ)` in
  integral form, `p(t) = p(T) + ∫ₜᵀ (p(r) ∘ ∂ₓf(q(r), ũ(r)) + ν ∂ₓφ(q(r), ũ(r))) dr` on
  `[0, T]`, the integrand being integrable;
- `IsMaximal f φ ν U ũ q T p`: for almost every `t ∈ [0, T]`,
  `H(q(t), p(t), u) ≤ H(q(t), p(t), ũ(t))` for all `u ∈ U`.

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

`stateTransition A s t` is the resolvent of `ξ' = A(t) ξ` from time `s` to time `t`
([`OptimalControl/ODE/LinearCaratheodory.lean`](OptimalControl/ODE/LinearCaratheodory.lean)).
</details>

### Agrachev and Sachkov's Chapter 12

| Agrachev–Sachkov (draft pages) | Lean | File |
| --- | --- | --- |
| Lemma 12.1, p. 168 | `Pontryagin.lemma12_1`; on any convex cone (its Remark (1)): `HasFDerivWithinAt.zero_mem_interior_image_inter_cone` | [`Geometric.lean`](OptimalControl/Pontryagin/Geometric.lean), [`Openness.lean`](OptimalControl/Convex/Cone/Openness.lean) |
| Lemma 12.2, p. 170 | `Pontryagin.lemma12_2`; in the form used by the proof of Theorem 12.4: `Pontryagin.lemma12_2_local` | [`Geometric.lean`](OptimalControl/Pontryagin/Geometric.lean) |
| Theorem 12.1, p. 164 (geometric PMP) | `Pontryagin.theorem12_1`; in the form used by the proof of Theorem 12.4: `Pontryagin.exists_costate_of_boundary` | [`Geometric.lean`](OptimalControl/Pontryagin/Geometric.lean) |
| Theorem 12.2, p. 173 (free time) | `Pontryagin.theorem12_2` | [`FreeTime.lean`](OptimalControl/Pontryagin/FreeTime.lean) |
| Theorem 12.3, p. 176 (cost, fixed end points) | `Pontryagin.theorem12_3` | [`IntegralCost.lean`](OptimalControl/Pontryagin/IntegralCost.lean) |
| Theorem 12.4, p. 178 (cost, `q(0) ∈ N₀`, `q(t₁) ∈ N₁`) | `Pontryagin.theorem12_4` | [`IntegralCost.lean`](OptimalControl/Pontryagin/IntegralCost.lean) |
| Theorem 12.5, p. 183 (cost, `(q(0), q(t₁)) ∈ N`) | `Pontryagin.theorem12_5` | [`IntegralCost.lean`](OptimalControl/Pontryagin/IntegralCost.lean) |
| Theorem 12.5 with free time (remark after it) | `Pontryagin.maximum_principle` | [`MaximumPrinciple.lean`](OptimalControl/Pontryagin/MaximumPrinciple.lean) |

In these statements `q` is the reference trajectory (Agrachev and Sachkov's `q̃`) of the
reference control `ũ`, and `p` the covector curve (their `λ_t`). The submanifolds `N₀`, `N₁`
and `N` enter, as in Agrachev and Sachkov's proof, only near the end points: `N₀` through a `C¹`
parametrization `ψ`, `N₁` and `N` through `C¹` maps `Φ`, `G` with surjective derivative whose
zeros lie in them.

<details>
<summary>The statements in Lean</summary>

With the section variables `{Ω : Set E} {U : Set V} {f : E → V → E} {φ : E → V → ℝ} {t₁ : ℝ}
{ũ : ℝ → V} {q : ℝ → E}`:

```lean
theorem lemma12_1 {m n : ℕ} {F : (Fin m → ℝ) → Fin n → ℝ} {F' : (Fin m → ℝ) →L[ℝ] Fin n → ℝ}
    (hlip : ∃ K, LipschitzWith K F) (h0 : F 0 = 0) (hF : HasFDerivAt F F' 0)
    (hsurj : F' '' {x | ∀ i, 0 ≤ x i} = univ) :
    ∀ O ∈ 𝓝 (0 : Fin m → ℝ), (0 : Fin n → ℝ) ∈ interior (F '' (O ∩ {x | ∀ i, 0 ≤ x i}))

theorem HasFDerivWithinAt.zero_mem_interior_image_inter_cone {C : Set E} {Fm : E → F}
    {Fm' : E →L[ℝ] F} (hFm : HasFDerivWithinAt Fm Fm' C 0) (hC : Convex ℝ C)
    (hCcone : ∀ x ∈ C, ∀ c : ℝ, 0 ≤ c → c • x ∈ C)
    (h0 : Fm 0 = 0) (hlip : ∃ ρ > 0, ∃ K, LipschitzOnWith K Fm (C ∩ ball 0 ρ))
    (hsurj : Fm' '' C = univ) :
    ∀ O ∈ 𝓝 (0 : E), (0 : F) ∈ interior (Fm '' (O ∩ C))

theorem lemma12_2 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hcone : PointedCone.hull ℝ ((fun p : ℝ × V ↦ needleVector f ũ q t₁ p.1 p.2) ''
      ({τ | τ ∈ Icc 0 t₁ ∧ IsLebesguePointWithin ũ (Icc 0 t₁) τ} ×ˢ U)) = ⊤) :
    q t₁ ∈ interior (attainableSet f Ω U (q 0) t₁)

theorem theorem12_1 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hbd : q t₁ ∈ frontier (attainableSet f Ω U (q 0) t₁)) :
    ∃ p : ℝ → StrongDual ℝ E, (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, p t ≠ 0) ∧ IsAdjoint f 0 0 ũ q t₁ p ∧ IsMaximal f 0 0 U ũ q t₁ p

theorem theorem12_2 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (ht₁ : 0 < t₁)
    (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q) {ε : ℝ} (hε : ε ∈ Ioo 0 t₁)
    (hbd : q t₁ ∈ frontier (⋃ t ∈ Ioo (t₁ - ε) (t₁ + ε), attainableSet f Ω U (q 0) t)) :
    ∃ p : ℝ → StrongDual ℝ E, (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, p t ≠ 0) ∧ IsAdjoint f 0 0 ũ q t₁ p ∧ IsMaximal f 0 0 U ũ q t₁ p ∧
      ∀ᵐ t ∂(volume.restrict (Icc 0 t₁)), controlHamiltonian f 0 0 (q t) (p t) (ũ t) = 0

theorem theorem12_3 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U)
    (ht₁ : 0 < t₁) (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (hopt : ∀ (u : ℝ → V) (x : ℝ → E), IsAdmissibleIn f Ω U (q 0) t₁ u x → x t₁ = q t₁ →
      cost φ t₁ ũ q ≤ cost φ t₁ u x) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      (∀ t ∈ Icc 0 t₁, (ν, p t) ≠ 0) ∧ IsAdjoint f φ ν ũ q t₁ p ∧ IsMaximal f φ ν U ũ q t₁ p ∧
      ν ≤ 0

theorem theorem12_4 (hΩ : IsOpen Ω) (hU : IsCompact U) (hf : IsC1On f Ω U) (hφ : IsC1On φ Ω U)
    (ht₁ : 0 < t₁) {N₀ N₁ : Set E} (href : IsAdmissibleIn f Ω U (q 0) t₁ ũ q)
    (_hq₀ : q 0 ∈ N₀) (_hq₁ : q t₁ ∈ N₁)
    (hopt : ∀ (u : ℝ → V) (x : ℝ → E), IsAdmissibleIn f Ω U (x 0) t₁ u x → x 0 ∈ N₀ →
      x t₁ ∈ N₁ → cost φ t₁ ũ q ≤ cost φ t₁ u x)
    {ψ : P → E} {a₀ : P} (hψ : ContDiffAt ℝ 1 ψ a₀) (hψ0 : ψ a₀ = q 0)
    (hψN : ∀ᶠ a in 𝓝 a₀, ψ a ∈ N₀) {Φ : E → Q} (hΦ : ContDiffAt ℝ 1 Φ (q t₁))
    (hΦsurj : Function.Surjective (fderiv ℝ Φ (q t₁))) (hΦ0 : Φ (q t₁) = 0)
    (hΦN : ∀ᶠ x in 𝓝 (q t₁), Φ x = 0 → x ∈ N₁) :
    ∃ (ν : ℝ) (p : ℝ → StrongDual ℝ E), (∃ K, LipschitzOnWith K p (Icc 0 t₁)) ∧
      IsAdjoint f φ ν ũ q t₁ p ∧ IsMaximal f φ ν U ũ q t₁ p ∧
      (∀ t ∈ Icc 0 t₁, (p t, ν) ≠ 0) ∧ ν ≤ 0 ∧
      (p 0).comp (fderiv ℝ ψ a₀) = 0 ∧ ∀ w, fderiv ℝ Φ (q t₁) w = 0 → p t₁ w = 0

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
      ∀ v w : E, fderiv ℝ G (q 0, q t₁) (v, w) = 0 → -p 0 v + p t₁ w = 0
```

In `theorem12_4` the hypotheses `q(0) ∈ N₀` and `q(t₁) ∈ N₁` are Agrachev and Sachkov's (the
reference trajectory satisfies the boundary conditions); the proof does not use them, since they
follow from the hypotheses on `ψ` and `Φ`.
</details>

### Filippov's theorem and the existence of optimal controls

[`ControlSystem.isCompact_reachableSet`](OptimalControl/ODE/ControlSystem.lean) and
`ControlSystem.isCompact_reachableSetLE`: for `F` jointly continuous, `U` compact, convex velocity
sets `F(x, U)` and velocities bounded along admissible trajectories, the attainable sets at time
`T` and up to time `T` are compact (Agrachev and Sachkov, Theorem 10.1). Here `V` need only be a
metric space with its Borel σ-algebra.

```lean
theorem isCompact_reachableSet (hF : Continuous fun p : E × V ↦ F p.1 p.2)
    (hU : IsCompact U) (hconv : ∀ z, Convex ℝ (F z '' U)) {x₀ : E} {T M : ℝ} (hT : 0 ≤ T)
    (hM : 0 ≤ M)
    (hbd : ∀ u x, IsAdmissible F U x₀ T u x → ∀ s ∈ Icc 0 T, ‖F (x s) (u s)‖ ≤ M) :
    IsCompact (reachableSet F U x₀ T)
```

Hence the existence of optimal controls for integral costs when the velocity sets extended by the
cost, `{(F(x, u), φ(x, u)) | u ∈ U}`, are convex, with fixed (`ControlSystem.exists_optimal_fixedTime`)
or free (`ControlSystem.exists_optimal_freeTime`) terminal time:

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

### Measurable selection

[`MeasureTheory.exists_measurable_forall_mem_ae_eq_zero`](OptimalControl/MeasureTheory/MeasurableSelection.lean)
(and `MeasureTheory.exists_measurable_forall_mem_and_eq_zero`, with zeros for every `t`): zeros of
a Carathéodory function on a compact set can be chosen measurably (the Kuratowski–Ryll-Nardzewski
construction; Filippov's lemma). `V` is a metric space with its Borel σ-algebra.

```lean
theorem exists_measurable_forall_mem_ae_eq_zero {μ : Measure α} {U : Set V} (hU : IsCompact U)
    (hUne : U.Nonempty) {g : α → V → E} (hmeas : ∀ w ∈ U, Measurable fun t ↦ g t w)
    (hcont : ∀ t, ContinuousOn (g t) U) (hex : ∀ᵐ t ∂μ, ∃ w ∈ U, g t w = 0) :
    ∃ σ : α → V, Measurable σ ∧ (∀ t, σ t ∈ U) ∧ ∀ᵐ t ∂μ, g t (σ t) = 0
```

### Carathéodory theory

For a control system `y' = f(y, u(t))` with `f` continuous on `E × U` and Lipschitz in the state,
and `u` measurable with values in the compact set `U`:

- existence and uniqueness of Carathéodory solutions, forward and backward in time
  (`ControlSystem.exists_isSolution`, `ControlSystem.IsSolution.eqOn`), the integral Gronwall
  inequality (`ControlSystem.le_mul_exp_of_le_add_integral`), the flow and its cocycle property
  (`ControlSystem.flow_flow`), and the cut-off of a `C¹` system near a compact subset of `Ω`
  (`ControlSystem.IsC1On.exists_cutoff`) —
  [`Caratheodory.lean`](OptimalControl/ODE/Caratheodory.lean);
- the resolvent of a linear equation with bounded measurable coefficients and the adjoint
  equation, with uniqueness (`ControlSystem.adjoint_stateTransition`,
  `ControlSystem.eq_comp_stateTransition_of_adjoint`) —
  [`LinearCaratheodory.lean`](OptimalControl/ODE/LinearCaratheodory.lean);
- the derivative of the flow in the initial point is the resolvent of the variational equation
  (`ControlSystem.hasFDerivAt_flow`, `ControlSystem.fderiv_flow_eq_stateTransition`) —
  [`FlowDerivative.lean`](OptimalControl/ODE/FlowDerivative.lean);
- the variations formula along a trajectory and Agrachev and Sachkov's Proposition 11.3 read
  pointwise (`ControlSystem.flow_flow_eq_add_integral_variationField`,
  `ControlSystem.adjoint_fderiv_flow`) —
  [`VariationsFormula.lean`](OptimalControl/ODE/VariationsFormula.lean);
- needle variations: the end-point map of finitely many needles is Lipschitz and differentiable
  at `σ = 0` within the orthant (`ControlSystem.lipschitzOnWith_needle`,
  `ControlSystem.hasFDerivWithinAt_needle`) —
  [`NeedleVariation.lean`](OptimalControl/ODE/NeedleVariation.lean);
- measurable changes of time (`ControlSystem.IsAdmissible.timeChange`,
  `ControlSystem.IsAdmissible.timeChangeOn`) —
  [`TimeChange.lean`](OptimalControl/ODE/TimeChange.lean);
- Lebesgue points (`ae_isLebesguePointWithin`, `IsLebesguePointWithin.exists_near`) and convex
  cones (`exists_dual_ne_zero_nonpos_of_ne_top`, `exists_finset_hull_eq_top`,
  `exists_forall_hull_eq_top_of_dist_lt`).

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
   given by the variations formula; its derivative maps the cone onto the space, and Lemma 12.1
   on the cone makes the end point an interior point of the attainable set.
3. **Lemma 12.1** (`HasFDerivWithinAt.zero_mem_interior_image_inter_cone`) is proved as
   Agrachev and Sachkov prove it: the rescaled maps `α⁻¹F(α ·)` are Lipschitz with a common
   constant, hence equicontinuous, and converge pointwise, hence uniformly (Mathlib's Ascoli
   lemma `Equicontinuous.tendsto_uniformFun_iff_pi`), to the derivative; **Brouwer's fixed-point
   theorem**, taken from the [FixedPoint](https://github.com/vltanh/lean4-fixed-point) package
   (`Brouwer.exists_fixedPoint`), then gives the openness.
4. **Theorem 12.1** (`theorem12_1`, and `exists_costate_of_boundary` with initial points `ψ(a)`
   and an end-point map `Φ`). At a point that is not interior, the cone of the variations is not
   the whole space, so a covector `ξ ≠ 0` supports it; `p(t) = ξ ∘ Φ' ∘ R(t, t₁)` solves the
   adjoint equation (Proposition 11.3, read pointwise), and the supporting inequality at the
   Lebesgue points, which have full measure, is the maximum condition.
5. **Theorems 12.2–12.5** are reduced to this by Agrachev and Sachkov's auxiliary systems: the
   time-scaled system `q' = v f(q, u)` (free time), the cost-extended system `y' = φ(q, u) + v`,
   `q' = f(q, u)` (cost), and the doubled system `x' = 0`, `q' = f(q, u)` on `E × E` (mixed
   boundary conditions). On a product state space whose dynamics do not depend on one factor,
   that factor's part of the costate is constant (`Pontryagin.Reduction.adjoint_prod`).
6. **`maximum_principle`** applies the three reductions at once, through one auxiliary system
   `y' = v (φ(q, u) + β)`, `x' = 0`, `q' = v f(q, u)` with controls
   `(v, β, u) ∈ [1 - δ, 1 + δ] × [0, 1] × U`, to `exists_costate_of_boundary`; strong local
   optimality is what makes the end point non-interior. The pointwise nontriviality
   `(ν, p(t)) ≠ 0` uses the uniqueness for the adjoint equation.

The Carathéodory theory beneath (existence, uniqueness and differentiable dependence of solutions,
the cut-off) is proved by Picard iteration and Gronwall's inequality. Filippov's theorem is proved
by the standard argument: the trajectories are equi-Lipschitz, a cluster point exists by
Tychonoff's theorem, its derivative lies in the convex velocity set almost everywhere, and a
measurable control realizing it is found by measurable selection.

### Readings and departures from Agrachev–Sachkov

The source is the authors' draft of the book (preface September 2003), posted on A. A.
Agrachev's home page (<https://people.sissa.it/~agrachev/agrachev_files/books.html>); page numbers
in the docstrings are the draft's. The docstrings refer to these departures:

- D1. The manifold `M` is an open subset `Ω` of a finite-dimensional real normed space `E`.
- D2. The chronological calculus (operators on `C^∞(M)`; (2.19), (2.28), (2.31), Proposition
  11.3) is read pointwise along trajectories, in coordinates: the vectors `g_{τ,u}` through the
  resolvent of the variational equation, Proposition 11.3 as the adjoint equation, the variations
  formula (12.13) as an integral equation for the transported trajectory.
- D3. The system and the cost are `C¹` in the state instead of `C^∞` (a generalization).
- D4. `U` is compact (the local boundedness of `f(q, u(t))` is tacit in the source); the
  auxiliary parameter sets of §§12.3–12.4 (`|v - 1| < δ`, `v ≥ 0`) are compact intervals.
- D5. Strong local minimizers instead of optimal (globally minimizing) controls (a
  generalization).
- D6. Free time together with a cost and mixed boundary conditions, which Agrachev and Sachkov
  leave to the reader (an exercise after Theorem 12.3, p. 177; remarks after Theorems 12.4 and
  12.5, pp. 179 and 184), is proved by applying the reductions of Theorems 12.2, 12.3 and 12.5
  through one auxiliary system.
- D7. Time changes are measurable (a forced departure): Agrachev and Sachkov derive the
  reparametrization for a smooth new time (p. 173) and apply it to measurable `v`. Here, for `v`
  measurable with values in `[c₁, c₂]`, `c₁ > 0`, and `θ(t) = ∫₀ᵗ v`, the push-forward of
  `v · Leb|[0, T]` under `θ` is `Leb|[0, θ(T)]`, which gives the change of variables in the
  integral equation and in the cost; Mathlib's substitution lemmas need a derivative at every
  point, while `θ' = v` holds only almost everywhere.
- D8. Lemma 12.1 in the form of its Remark (1), on any convex cone, with `F` Lipschitz only near
  `0` on the cone and differentiable at `0` within it.
- D9. One supporting covector for all needle variations at once, in Theorems 12.4 and 12.5 (and
  `exists_costate_of_boundary`): the proof of Theorem 12.4 takes, in (12.41), a covector for each
  finite needle variation, while the maximum condition at almost every `t` needs a single one.
- D10. Brouwer's theorem, for which the source gives no reference, comes from the FixedPoint
  package.
- D11. Carathéodory well-posedness and differentiable dependence, which the source cites to
  Gamkrelidze (1978), are proved here by Picard iteration and Gronwall's inequality; a cut-off to a
  compact tube around the reference trajectory replaces the source's assumption that the vector
  fields are complete.

Further readings: `0 < t₁` is Agrachev and Sachkov's standing assumption ("Fix an arbitrary
instant `t₁ > 0`", p. 163), a hypothesis of Lemma 12.2 and of the theorems here (it is needed: for
`M = ℝ`, `U = [-1, 1]`, `f(q, u) = u` and `ũ ≡ 0`, the vectors `g_{0,u}(q₀) = u` generate `ℝ`, but
the attainable set at time `0` is `{q₀}`); the hypothesis that the end point lies on the boundary
of the attainable set is weakened, in `lemma12_2_local` and `exists_costate_of_boundary`, to "not
an interior point of the image of the attainable set of nearby trajectories"
(`localAttainableSet`), which is what the proofs use; the nontriviality `(λ_t, ν) ≢ (0, 0)` of
(12.32) is stated for every `t` (in Theorem 12.5 through the uniqueness for the adjoint
equation); the needle intervals are half-open, so that the zero variation is the reference control
exactly.

### Gaps in Agrachev–Sachkov

- **Lemma 12.1, Remark (1).** The proof takes points in the interior of the cone, which is empty
  for a convex cone with empty interior, a case the remark allows. The proof here takes the
  points `v + L z` as combinations of points of the cone with positive coefficients, so it uses
  no interior; for the cones to which the lemma is applied (`ℝᵏ₊` and `P × ℝᵏ₊`) the source's
  step is valid as written.
- **A needle at `t₁`.** In the proof of Lemma 12.2 the set of Lebesgue points may contain `t₁`,
  and a needle at `t₁` gives no variation on `[0, t₁]`. Such a needle time is moved to a nearby
  Lebesgue point of `(0, t₁)`, as Agrachev and Sachkov move repeated times.
- **The needle map.** That the end-point map of the needle variations is Lipschitz and
  differentiable at `0`, with partial derivatives `g_{τᵢ,uᵢ}(q₁)` (p. 172), is stated without
  proof; it is proved in [`NeedleVariation.lean`](OptimalControl/ODE/NeedleVariation.lean).

### References

- A. A. Agrachev and Yu. L. Sachkov, *Control Theory from the Geometric Viewpoint*,
  Encyclopaedia of Mathematical Sciences 87, Springer, 2004 (Chapter 10, Theorem 10.1; Chapter
  12).
- R. V. Gamkrelidze, *Principles of Optimal Control Theory*, Plenum, 1978.

## Using it from another Lake project

Add to the `lakefile.toml` of your project, with a full commit hash of this repository in place of
the placeholder:

```toml
[[require]]
name = "OptimalControl"
git = "https://github.com/vltanh/lean4-optimal-control"
rev = "<full commit hash>"
```

and import the modules you need, for instance `public import OptimalControl.Pontryagin` in a
module, or `import OptimalControl` for everything. The package requires Lean and Mathlib
`v4.36.0-rc2` (your project should use the same versions) and depends on
[FixedPoint](https://github.com/vltanh/lean4-fixed-point) for Brouwer's fixed-point theorem.

## Building

```sh
lake exe cache get                 # Mathlib's compiled files
lake build
lake env lean scripts/Audit.lean   # the axioms of the main theorems; fails on any other axiom
```

The build has no warnings; CI builds with `--wfail`, runs the audit, checks that the audit imports
every module, and checks that no line exceeds 100 characters.

## Layout

| Path | Content |
| --- | --- |
| [`OptimalControl.lean`](OptimalControl.lean) | imports the whole library |
| [`OptimalControl/Pontryagin.lean`](OptimalControl/Pontryagin.lean) | imports the maximum principle, and through it every other module |
| [`OptimalControl/MeasureTheory/MeasurableSelection.lean`](OptimalControl/MeasureTheory/MeasurableSelection.lean) | measurable selection of zeros of Carathéodory functions on a compact set; measurability of `{t \| ∃ w ∈ C, g t w = 0}` |
| [`OptimalControl/MeasureTheory/LebesguePoints.lean`](OptimalControl/MeasureTheory/LebesguePoints.lean) | Lebesgue points of a function within an interval: almost every point is one, and they are dense |
| [`OptimalControl/ODE/ControlSystem.lean`](OptimalControl/ODE/ControlSystem.lean) | control systems with Carathéodory trajectories, Filippov's theorem, existence of optimal controls; the fundamental theorem of calculus for Lipschitz curves |
| [`OptimalControl/ODE/Caratheodory.lean`](OptimalControl/ODE/Caratheodory.lean) | `C¹` control systems (`IsC1On`), existence and uniqueness of Carathéodory solutions, the flow, Gronwall's inequality, the cut-off |
| [`OptimalControl/ODE/LinearCaratheodory.lean`](OptimalControl/ODE/LinearCaratheodory.lean) | the resolvent of a linear equation with measurable coefficients, the adjoint equation |
| [`OptimalControl/ODE/FlowDerivative.lean`](OptimalControl/ODE/FlowDerivative.lean) | the derivative of the flow in the initial point is the resolvent of the variational equation |
| [`OptimalControl/ODE/VariationsFormula.lean`](OptimalControl/ODE/VariationsFormula.lean) | the variations formula along a trajectory; Proposition 11.3 read pointwise |
| [`OptimalControl/ODE/NeedleVariation.lean`](OptimalControl/ODE/NeedleVariation.lean) | needle variations of a control and the derivative of their end-point map |
| [`OptimalControl/ODE/TimeChange.lean`](OptimalControl/ODE/TimeChange.lean) | measurable changes of time |
| [`OptimalControl/Convex/Cone/Support.lean`](OptimalControl/Convex/Cone/Support.lean) | supporting hyperplanes and finite generation of convex cones |
| [`OptimalControl/Convex/Cone/Openness.lean`](OptimalControl/Convex/Cone/Openness.lean) | openness at the vertex of a cone (Lemma 12.1 with its Remark (1)), by Brouwer's theorem |
| [`OptimalControl/Pontryagin/Defs.lean`](OptimalControl/Pontryagin/Defs.lean) | admissible pairs, attainable sets, cost, Hamiltonian, needle vectors, the adjoint equation, the maximum condition, strong local minimizers |
| [`OptimalControl/Pontryagin/Geometric.lean`](OptimalControl/Pontryagin/Geometric.lean) | Lemmas 12.1, 12.2 and Theorem 12.1, and the general form `exists_costate_of_boundary` |
| [`OptimalControl/Pontryagin/FreeTime.lean`](OptimalControl/Pontryagin/FreeTime.lean) | Theorem 12.2 (free time) |
| [`OptimalControl/Pontryagin/IntegralCost.lean`](OptimalControl/Pontryagin/IntegralCost.lean) | Theorems 12.3–12.5 (integral cost, fixed time, boundary conditions) |
| [`OptimalControl/Pontryagin/MaximumPrinciple.lean`](OptimalControl/Pontryagin/MaximumPrinciple.lean) | the maximum principle with free time, cost and mixed boundary conditions |
| [`scripts/Audit.lean`](scripts/Audit.lean) | the axiom audit |
| [`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml) | CI: build without warnings, audit, import list of the audit, line lengths |

## Credits

- Maintained by The-Anh Vu-Le.
- Written by Claude (Opus 5.5, model `claude-opus-5-5`) in Claude Code.
- No person has reviewed the proofs; Lean has checked them.

## License

Apache-2.0; see [LICENSE](LICENSE).
