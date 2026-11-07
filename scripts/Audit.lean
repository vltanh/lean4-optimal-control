module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library, so that proofs are visible to the axiom
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find OptimalControl -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all OptimalControl.Convex.Cone.Openness
import all OptimalControl.Convex.Cone.Support
import all OptimalControl.Defs
import all OptimalControl.MeasureTheory.LebesguePoints
import all OptimalControl.MeasureTheory.MeasurableSelection
import all OptimalControl.ODE.Caratheodory
import all OptimalControl.ODE.ControlSystem
import all OptimalControl.ODE.FlowDerivative
import all OptimalControl.ODE.LinearCaratheodory
import all OptimalControl.ODE.NeedleVariation
import all OptimalControl.ODE.StateConstraint
import all OptimalControl.ODE.TimeChange
import all OptimalControl.ODE.VariationsFormula
import all OptimalControl.Pontryagin
import all OptimalControl.Pontryagin.Defs
import all OptimalControl.Pontryagin.FreeTime
import all OptimalControl.Pontryagin.Geometric
import all OptimalControl.Pontryagin.IntegralCost
import all OptimalControl.Pontryagin.MaximumPrinciple

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

Prints the axioms on which the main theorems depend, then checks that they and every declaration
of the library, including private and auxiliary ones, depend only on Lean's standard axioms
`propext`, `Classical.choice` and `Quot.sound`. Any other axiom fails the audit: a `sorry` (which
shows up as the axiom `sorryAx`), an `axiom` declared anywhere, or `Lean.ofReduceBool` from
`native_decide`.
-/

open Lean Elab Command

namespace Audit

/-- The main theorems of the library. -/
meta def mainResults : List Name :=
  [-- the maximum principle (Agrachev–Sachkov, Chapter 12)
   ``Pontryagin.maximum_principle,
   ``Pontryagin.theorem12_1,
   ``Pontryagin.theorem12_2,
   ``Pontryagin.theorem12_3,
   ``Pontryagin.theorem12_4,
   ``Pontryagin.theorem12_5,
   ``Pontryagin.lemma12_1,
   ``Pontryagin.lemma12_2,
   ``Pontryagin.lemma12_2_local,
   ``Pontryagin.exists_costate_of_boundary,
   ``HasFDerivWithinAt.zero_mem_interior_image_inter_cone,
   -- Filippov's theorem and the existence of optimal controls
   ``ControlSystem.isCompact_reachableSet,
   ``ControlSystem.isCompact_reachableSetLE,
   ``ControlSystem.exists_optimal_fixedTime,
   ``ControlSystem.exists_optimal_freeTime,
   ``ControlSystem.isCompact_constrainedEndpoints,
   ``ControlSystem.exists_optimal_constrained,
   -- measurable selection
   ``MeasureTheory.exists_measurable_forall_mem_and_eq_zero,
   ``MeasureTheory.exists_measurable_forall_mem_ae_eq_zero,
   -- Carathéodory solutions, flows and their derivatives
   ``ControlSystem.exists_isSolution,
   ``ControlSystem.IsSolution.eqOn,
   ``ControlSystem.flow_flow,
   ``ControlSystem.le_mul_exp_of_le_add_integral,
   ``ControlSystem.IsC1On.exists_cutoff,
   ``ControlSystem.adjoint_stateTransition,
   ``ControlSystem.eq_comp_stateTransition_of_adjoint,
   ``ControlSystem.hasFDerivAt_flow,
   ``ControlSystem.fderiv_flow_eq_stateTransition,
   ``ControlSystem.flow_flow_eq_add_integral_variationField,
   ``ControlSystem.adjoint_fderiv_flow,
   ``ControlSystem.hasFDerivWithinAt_needle,
   ``ControlSystem.lipschitzOnWith_needle,
   ``ControlSystem.IsAdmissible.timeChange,
   ``ControlSystem.IsAdmissible.timeChangeOn,
   -- Lebesgue points, convex cones, Lipschitz curves
   ``ae_isLebesguePointWithin,
   ``IsLebesguePointWithin.exists_near,
   ``exists_dual_ne_zero_nonpos_of_ne_top,
   ``exists_finset_hull_eq_top,
   ``exists_forall_hull_eq_top_of_dist_lt,
   ``LipschitzWith.intervalIntegral_deriv_eq_sub]

/-- Lean's standard axioms, the only ones the audit accepts. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`OptimalControl).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      out := out ++ d.constNames
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array MessageData := #[]
  let mut rows : Array String := #[]
  for n in mainResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then
      bad := bad.push m!"{n}: {axs.toList}"
    rows := rows.push s!"{n}: {axs.toList}"
  let library := libraryConstants env
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then
      bad := bad.push m!"{c}: {axs.toList}"
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by:\n{MessageData.joinSep bad.toList "\n"}"

end Audit

#print axioms Pontryagin.maximum_principle

#audit
