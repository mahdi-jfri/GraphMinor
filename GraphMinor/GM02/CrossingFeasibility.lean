module

public import GraphMinor.GM02.ExtractedSchemeFeasible
import GraphMinor.GM02.CorrectedSchemeGluing

/-!
# Feasibility across a separation

Cut a feasible linkage into maximal side pieces to obtain a crossing
scheme with feasible induced graphs. Conversely, join the side paths
along the contracted paths of a crossing scheme. Original terminals
assigned only to the other side must be deleted as well as reserved
vertices. This corrects the printed induced-graph definition, whose
failure is proved by the star counterexample.
-/

public section
namespace GraphMinor.GM02
open Graph Set
universe u v

/-- Graph Minors II, (2.9), page 315, with corrected induced graphs.
The statement printed in II is false: its deletions allow a side path
to pass internally through an original terminal assigned elsewhere.
`CrossingScheme.inducedLeft` and `CrossingScheme.inducedRight` also delete
such original separator terminals. The crossing-scheme conditions are
unchanged. With this correction, feasibility is equivalent to existence
of a crossing scheme with both induced terminated graphs feasible. -/
theorem theorem_2_9_proof {α : Type u} {β : Type v} {G H H' : Graph α β}
    (A : Termination V(G)) (hsep : IsSeparation G H H') :
    A.Feasible G ↔ ∃ C : CrossingScheme G H H' A,
      C.left.Feasible C.inducedLeft ∧ C.right.Feasible C.inducedRight := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨extractedCrossingScheme G H H' A P hP hsep,
      extractedCrossingScheme_left_feasible G H H' A P hP hsep,
      extractedCrossingScheme_right_feasible G H H' A P hP hsep⟩
  · rintro ⟨C, hL, hR⟩
    exact feasible_of_corrected_induced_feasible hsep C hL hR

end GraphMinor.GM02
