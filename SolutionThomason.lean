module

public import GraphMinor.GM09.Defs
public import GraphMinor.GM13.Defs
public import GraphMinor.GM16.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import GraphMinor.Thomason.UniformTheorem

/-!
# Thomason's bound, proved

This file proves the statement of `ChallengeThomason.lean`, with the same name. The proof is
`GraphMinor.Thomason.thomason84` (`GraphMinor/Thomason/UniformTheorem.lean`), which proves
`GraphMinor.GM13.Thomason84Statement`, the same statement written as a `Prop` in
`GraphMinor/GM13/Cited.lean`.
-/

public section

namespace GraphMinor

open Graph

universe u v

/-- **Thomason's bound**, as stated in Graph Minors XIII, (5.5), page 83, for every `p ≥ 1`: a
finite non-null simple graph `G` with `|E(G)| ≥ 2.68 p (log₂ p) ^ (1/2) |V(G)|` has a `K_p`
minor. -/
theorem thomason_bound {α : Type u} {β : Type v} (G : Graph α β) (p : ℕ) (hp : 1 ≤ p)
    (hV : V(G).Finite) (hE : E(G).Finite) (hne : V(G).Nonempty) (hs : GM09.IsSimpleGraph G)
    (hd : (2.68 : ℝ) * (p : ℝ) * Real.sqrt (Real.logb 2 p) * (V(G).ncard : ℝ) ≤
      (E(G).ncard : ℝ)) :
    GM13.HasGraphModel (GM16.completeGraph p) G :=
  Thomason.thomason84 G p hp hV hE hne hs hd

end GraphMinor

#print axioms GraphMinor.thomason_bound
