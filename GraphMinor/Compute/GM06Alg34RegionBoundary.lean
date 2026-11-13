module

public import GraphMinor.Compute.GM06Alg34RegionRoots

/-!
# Finite boundary lists for recomputed regions

The closure of a new region is the union of the original cell closures
in its complement component. Test this using the supplied closure lists
and finite reachability. Among these closure cells, the active vertex
and edge labels form the new region boundary. These are finite reference
functions on the supplied data, without selecting geometric objects.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- Whether a supplied cell occurs in the closure of a recomputed region. -/
def regionClosureHit (x : GM06DrawingData) (vs : List (Fin x.n)) (r : Fin x.cellCount)
    (b : GM06CellIndex x) : Bool :=
  decide (∃ c : GM06CellIndex x, x.activeCell vs c = false ∧
    (x.complementGraph vs).Reachable r (x.cellNumbering c) ∧ b ∈ x.cellClosure c)

/-- Active original vertex labels on the boundary of one new region. -/
def regionBoundaryVertices (x : GM06DrawingData) (vs : List (Fin x.n)) (r : Fin x.cellCount) :
    List (Fin x.n) :=
  (List.finRange x.n).filter (fun v => decide (v ∈ vs) && x.regionClosureHit vs r (.inl v))

/-- Active original edge labels on the boundary of one new region. -/
def regionBoundaryEdges (x : GM06DrawingData) (vs : List (Fin x.n)) (r : Fin x.cellCount) :
    List (Fin x.ends.length) :=
  (List.finRange x.ends.length).filter (fun e =>
    x.activeCell vs (.inr (.inl e)) && x.regionClosureHit vs r (.inr (.inl e)))

/-- The new vertex boundary list records exactly active closure hits. -/
theorem mem_regionBoundaryVertices_iff (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.cellCount) (v : Fin x.n) :
    v ∈ x.regionBoundaryVertices vs r ↔ v ∈ vs ∧ x.regionClosureHit vs r (.inl v) = true := by
  simp only [regionBoundaryVertices, List.mem_filter, List.mem_finRange, true_and,
    Bool.and_eq_true, decide_eq_true_eq]

/-- The new edge boundary list records exactly active closure hits. -/
theorem mem_regionBoundaryEdges_iff (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.cellCount) (e : Fin x.ends.length) :
    e ∈ x.regionBoundaryEdges vs r ↔ x.activeCell vs (.inr (.inl e)) = true ∧
      x.regionClosureHit vs r (.inr (.inl e)) = true := by
  simp only [regionBoundaryEdges, List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true]

end GraphMinor.Compute.GM06DrawingData
