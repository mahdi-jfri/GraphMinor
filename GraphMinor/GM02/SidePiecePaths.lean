module

public import GraphMinor.GM02.SidePieceIndex
public import GraphMinor.GM02.SideRunTransfer

/-!
# Side pieces as paths in their assigned subgraphs

A maximal run assigned to a side can be viewed as a pair path in that
side's graph, with exactly the same vertex support as its original path
piece. These witnesses realize the two side terminations before the
reservation deletions in the forward proof of corrected II (2.9).
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)

/-- A true-colored piece is a path in the first side. -/
noncomputable def RunPieceIndex.leftPath (i : RunPieceIndex A G H P)
    (hc : i.color A G H P = true) : PairPath (pathGraph H) (i.pair A G H P) where
  start := (i.path A G H P).start
  finish := (i.path A G H P).finish
  ends_eq := rfl
  walk := sideRunLeftWalk (P i.1).walk i.2.val i.2.property hc
  isPath := sideRunLeftWalk_isPath (P i.1).walk (P i.1).isPath i.2.val i.2.property hc

/-- The path in the first side has the original piece's vertices. -/
theorem RunPieceIndex.leftPath_vertices (i : RunPieceIndex A G H P)
    (hc : i.color A G H P = true) :
    (i.leftPath A G H P hc).vertices = (i.path A G H P).vertices := by
  exact congrArg (fun l : List α => {a | a ∈ l})
    (sideRunLeftWalk_support (P i.1).walk i.2.val i.2.property hc)

/-- A false-colored piece is a path in the second side. -/
noncomputable def RunPieceIndex.rightPath {H' : Graph α β} (hsep : IsSeparation G H H')
    (i : RunPieceIndex A G H P) (hc : i.color A G H P = false) :
    PairPath (pathGraph H') (i.pair A G H P) where
  start := (i.path A G H P).start
  finish := (i.path A G H P).finish
  ends_eq := rfl
  walk := sideRunRightWalk hsep (P i.1).walk i.2.val i.2.property hc
  isPath := sideRunRightWalk_isPath hsep (P i.1).walk (P i.1).isPath i.2.val i.2.property hc

/-- The path in the second side has the original piece's vertices. -/
theorem RunPieceIndex.rightPath_vertices {H' : Graph α β} (hsep : IsSeparation G H H')
    (i : RunPieceIndex A G H P) (hc : i.color A G H P = false) :
    (i.rightPath A G H P hsep hc).vertices = (i.path A G H P).vertices := by
  exact congrArg (fun l : List α => {a | a ∈ l})
    (sideRunRightWalk_support hsep (P i.1).walk i.2.val i.2.property hc)

end GraphMinor.GM02
