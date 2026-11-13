module

public import GraphMinor.Compute.GM06Alg34VertexComponents
public import GraphMinor.Compute.GM06Alg34InducedData

/-!
# Finite data for deleting a component away from the cuffs

Test whether a component contains any supplied cuff vertex. If it does
not, delete exactly its reachable labels and compute the induced
payload. This is the finite-data update of VI (3.3)(ii), page 120.
All tests and surviving labels are computed from the supplied lists.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- Test that no supplied cuff vertex lies in the component of a label. -/
def isInteriorComponent (x : GM06DrawingData) (a : Fin x.n) : Bool :=
  !(x.cuffs.any (fun L => L.any (fun b => decide (x.vertexGraph.Reachable a b))))

/-- The component test excludes exactly all supplied cuff vertices. -/
theorem isInteriorComponent_eq_true_iff (x : GM06DrawingData) (a : Fin x.n) :
    x.isInteriorComponent a = true ↔
      ∀ L ∈ x.cuffs, ∀ b ∈ L, ¬ x.vertexGraph.Reachable a b := by
  simp [isInteriorComponent]

/-- Find a component with no supplied cuff vertex by scanning its source labels. -/
def findInteriorComponent (x : GM06DrawingData) : Option (Fin x.n) :=
  (List.finRange x.n).find? x.isInteriorComponent

/-- The labels outside the selected component, in their original order. -/
def interiorComponentSurvivors (x : GM06DrawingData) (a : Fin x.n) : List (Fin x.n) :=
  (List.finRange x.n).filter (fun b => decide (¬ x.vertexGraph.Reachable a b))

/-- Exactly the labels not reachable from the selected source survive. -/
theorem mem_interiorComponentSurvivors_iff (x : GM06DrawingData) (a b : Fin x.n) :
    b ∈ x.interiorComponentSurvivors a ↔ ¬ x.vertexGraph.Reachable a b := by
  simp [interiorComponentSurvivors]

/-- The retained-label set is exactly the complement of the selected component. -/
theorem interiorComponentSurvivors_block (x : GM06DrawingData) (a : Fin x.n) :
    block (x.interiorComponentSurvivors a) = Set.univ \ block (x.componentVertices a) := by
  ext b
  change b ∈ x.interiorComponentSurvivors a ↔ _
  simp only [x.mem_interiorComponentSurvivors_iff, Set.mem_diff, Set.mem_univ,
    block, Set.mem_setOf_eq, x.mem_componentVertices_iff, true_and]

/-- The complete payload obtained by deleting the selected interior component. -/
def interiorComponentData (x : GM06DrawingData) (a : Fin x.n) : GM06DrawingData :=
  x.inducedData (x.interiorComponentSurvivors a)

/-- An interior component's deletion retains every supplied cuff vertex. -/
theorem cuff_mem_interiorComponentSurvivors (x : GM06DrawingData) (a : Fin x.n)
    (ha : x.isInteriorComponent a = true) {L : List (Fin x.n)} (hL : L ∈ x.cuffs)
    {b : Fin x.n} (hb : b ∈ L) : b ∈ x.interiorComponentSurvivors a :=
  (x.mem_interiorComponentSurvivors_iff a b).mpr
    ((x.isInteriorComponent_eq_true_iff a).mp ha L hL b hb)

end GraphMinor.Compute.GM06DrawingData
