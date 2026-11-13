module

public import GraphMinor
import Lean

/-! Fails unless every declaration of the `GraphMinor` modules uses only `propext`,
`Classical.choice` and `Quot.sound`. In the module system the axioms of each imported
declaration, private helpers included, are recorded when its module is built, so checking the
public declarations covers everything they use. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array String := #[]
  for h : i in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]
    unless (`GraphMinor).isPrefixOf mod do continue
    for c in env.header.moduleData[i]!.constNames do
      count := count + 1
      for a in ← liftCoreM (collectAxioms c) do
        unless allowed.contains a do
          bad := bad.push s!"{c} ({mod}) uses {a}"
  logInfo m!"{env.header.moduleNames.size} modules loaded"
  if bad.isEmpty then
    logInfo m!"{count} declarations checked; only propext, Classical.choice and Quot.sound are used"
  else
    throwError m!"disallowed axioms:\n{"\n".intercalate bad.toList}"
