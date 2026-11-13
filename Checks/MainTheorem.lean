module

import Solution
import SolutionThomason
import Lean

/-! Fails unless each of the three main theorems of `Solution.lean`, and Thomason's bound in
`SolutionThomason.lean`, uses only `propext`, `Classical.choice` and `Quot.sound`, and prints the
axioms each one uses. -/

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for thm in [ ``GraphMinor.graph_minor_theorem, ``GraphMinor.structure_theorem,
      ``GraphMinor.disjoint_paths_algorithm, ``GraphMinor.thomason_bound ] do
    let ax ← liftCoreM (collectAxioms thm)
    logInfo m!"{thm} uses: {ax}"
    for a in ax do
      unless allowed.contains a do
        throwError m!"disallowed axiom: {a}"
