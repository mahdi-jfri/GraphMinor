module

public import GraphMinor.Compute.GM06Alg34Input

/-!
# Finite cell labels and closure incidence

Index the supplied drawing's vertices, open edges, and regions by a
finite sum type. Their closure lists are read directly from endpoints
and the supplied region boundaries. These lists are finite data used
to recompute regions after vertex deletion in (3.3)(i). They contain no
geometric choices or reduction certificates.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Finite labels for vertex points, open edges, and regions. -/
abbrev GM06CellIndex (x : GM06DrawingData) :=
  Fin x.n ⊕ (Fin x.ends.length ⊕ Fin x.regions.length)

namespace GM06DrawingData

/-- Labels of all cells in the closure of a supplied cell. -/
def cellClosure (x : GM06DrawingData) : GM06CellIndex x → List (GM06CellIndex x)
  | .inl v => [.inl v]
  | .inr (.inl e) => [.inr (.inl e), .inl x.ends[e].1, .inl x.ends[e].2]
  | .inr (.inr r) => .inr (.inr r) ::
      (x.regions[r].vertices.map Sum.inl ++ x.regions[r].edges.map (Sum.inr ∘ Sum.inl))

/-- Two finite cell labels touch when one is in the supplied closure
list of the other. -/
def cellTouch (x : GM06DrawingData) (a b : GM06CellIndex x) : Bool :=
  decide (a ∈ x.cellClosure b ∨ b ∈ x.cellClosure a)

/-- Cells remaining in the drawing induced by the active vertex labels.
Regions are never part of the drawing's point set. -/
def activeCell (x : GM06DrawingData) (vs : List (Fin x.n)) : GM06CellIndex x → Bool
  | .inl v => decide (v ∈ vs)
  | .inr (.inl e) => decide (x.ends[e].1 ∈ vs ∧ x.ends[e].2 ∈ vs)
  | .inr (.inr _) => false

end GM06DrawingData
end GraphMinor.Compute
