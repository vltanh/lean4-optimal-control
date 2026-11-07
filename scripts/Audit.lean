module

public meta import Lean.Elab.Command
-- One `import all` line per module of the library, so that proofs are visible to the axiom
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find OptimalControl -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all OptimalControl.Convex.Cone.Openness
import all OptimalControl.Convex.Cone.Support
import all OptimalControl.MeasureTheory.LebesguePoints
import all OptimalControl.MeasureTheory.MeasurableSelection
import all OptimalControl.ODE.Caratheodory
import all OptimalControl.ODE.ControlSystem
import all OptimalControl.ODE.FlowDerivative
import all OptimalControl.ODE.LinearCaratheodory
import all OptimalControl.ODE.NeedleVariation
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
`propext`, `Classical.choice` and `Quot.sound`. A `sorry` shows up as the axiom `sorryAx`.

**While the library is not sorry-free** (`allowSorry = true` below), `sorryAx` is tolerated: the
audit lists, in a warning, the declarations that contain a `sorry` themselves, and counts those
that depend on one; it fails only on an axiom other than the standard three and `sorryAx` (an
`axiom` declared anywhere, or `Lean.ofReduceBool` from `native_decide`). Once the last `sorry` is
gone, set `allowSorry` to `false`: then `sorryAx` fails the audit like any other axiom.
-/

open Lean Elab Command

namespace Audit

/-- **Temporary:** whether `sorryAx` is tolerated. Set to `false` once the library is
sorry-free. -/
meta def allowSorry : Bool := true

/-- The main theorems of the library. -/
meta def mainResults : List Name :=
  [``Pontryagin.maximum_principle,
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
   ``ControlSystem.isCompact_reachableSet,
   ``ControlSystem.isCompact_reachableSetLE,
   ``ControlSystem.exists_optimal_fixedTime,
   ``ControlSystem.exists_optimal_freeTime,
   ``MeasureTheory.exists_measurable_forall_mem_ae_eq_zero]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms that the audit accepts: the standard ones, and `sorryAx` while `allowSorry`. -/
meta def allowedAxioms : List Name :=
  if allowSorry then standardAxioms ++ [``sorryAx] else standardAxioms

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`OptimalControl).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      out := out ++ d.constNames
  return out

/-- Whether the type or the value of `c` mentions `sorryAx` itself: `c` contains a `sorry`, as
opposed to depending on another declaration that does. -/
meta def containsSorry (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some ci =>
    ci.type.getUsedConstants.contains ``sorryAx ||
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants.contains ``sorryAx)).getD false
  | none => false

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut rows : Array String := #[]
  for n in mainResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!allowedAxioms.contains ·) then bad := bad.push n
    rows := rows.push s!"{n}: {axs.toList}"
  let library := libraryConstants env
  let mut dependsOnSorry := 0
  let mut withSorry : Array Name := #[]
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!allowedAxioms.contains ·) then bad := bad.push c
    if axs.contains ``sorryAx then
      dependsOnSorry := dependsOnSorry + 1
      if containsSorry env c then withSorry := withSorry.push c
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if !bad.isEmpty then "see the error."
     else if dependsOnSorry == 0 then "all use only the standard axioms."
     else s!"all use only the standard axioms and `sorryAx` ({dependsOnSorry} depend on " ++
       "`sorryAx`; see the warning)."))
  unless withSorry.isEmpty do
    let names := (withSorry.qsort (·.toString < ·.toString)).toList.map (s!"  {·}")
    logWarning (s!"SORRY: {withSorry.size} declarations of the library contain a `sorry` " ++
      s!"(tolerated while `Audit.allowSorry` is true):\n" ++ "\n".intercalate names)
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#print axioms Pontryagin.maximum_principle

#audit
