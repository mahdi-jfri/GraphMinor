module

public import GraphMinor.Compute.GM06Alg34VertexGraph
public import GraphMinor.Compute.GM06Alg34Singleton
public import GraphMinor.GM06.Section3Basic

/-!
# Finite vertex lists for drawing components

List the labels reachable from a supplied vertex. The list represents
exactly the multigraph component through that vertex. Least-label roots
identify distinct components using only the finite endpoint graph.
These are the component inputs used by the reductions in VI (3.3).
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

open Set Surface GM06

/-- The supplied labels in the component containing a given label. -/
def componentVertices (x : GM06DrawingData) (a : Fin x.n) : List (Fin x.n) :=
  (List.finRange x.n).filter (fun b => decide (x.vertexGraph.Reachable a b))

/-- The component list consists exactly of the labels reachable from its source. -/
theorem mem_componentVertices_iff (x : GM06DrawingData) (a b : Fin x.n) :
    b ∈ x.componentVertices a ↔ x.vertexGraph.Reachable a b := by
  simp only [componentVertices, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

/-- A component's finite label list contains its source. -/
theorem mem_componentVertices_self (x : GM06DrawingData) (a : Fin x.n) :
    a ∈ x.componentVertices a := (x.mem_componentVertices_iff a a).mpr (.refl a)

/-- The component list has no repeated vertex labels. -/
theorem componentVertices_nodup (x : GM06DrawingData) (a : Fin x.n) :
    (x.componentVertices a).Nodup := (List.nodup_finRange _).filter _

/-- The finite label list denotes exactly the multigraph's walk component. -/
theorem componentVertices_block (x : GM06DrawingData) (a : Fin x.n) :
    block (x.componentVertices a) = GM06.reachSet x.graph a := by
  ext b
  change b ∈ x.componentVertices a ↔ _
  rw [x.mem_componentVertices_iff, x.vertexGraph_reachable_iff]
  exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

/-- Inducing on the computed labels gives an actual graph component. -/
theorem componentVertices_isGraphComponent (x : GM06DrawingData) (a : Fin x.n) :
    IsGraphComponent (x.graph.induce (block (x.componentVertices a))) x.graph := by
  rw [x.componentVertices_block]
  exact GM06.isGraphComponent_compOf (show a ∈ x.graph.vertexSet from trivial)

/-- The least label in one endpoint-graph component. -/
def isComponentRoot (x : GM06DrawingData) (a : Fin x.n) : Bool :=
  decide (∀ b : Fin x.n, b < a → ¬ x.vertexGraph.Reachable a b)

/-- Enumerate components by their least supplied vertex label. -/
def componentRoots (x : GM06DrawingData) : List (Fin x.n) :=
  (List.finRange x.n).filter x.isComponentRoot

/-- Root membership says exactly that no smaller label is reachable. -/
theorem mem_componentRoots_iff (x : GM06DrawingData) (a : Fin x.n) :
    a ∈ x.componentRoots ↔ ∀ b : Fin x.n, b < a → ¬ x.vertexGraph.Reachable a b := by
  simp only [componentRoots, isComponentRoot, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]

/-- Reachable canonical component roots coincide. -/
theorem componentRoots_eq_of_reachable (x : GM06DrawingData) {a b : Fin x.n}
    (ha : a ∈ x.componentRoots) (hb : b ∈ x.componentRoots)
    (hab : x.vertexGraph.Reachable a b) : a = b := by
  have hamin := (x.mem_componentRoots_iff a).mp ha
  have hbmin := (x.mem_componentRoots_iff b).mp hb
  rcases lt_trichotomy a b with hlt | rfl | hgt
  · exact False.elim (hbmin a hlt hab.symm)
  · rfl
  · exact False.elim (hamin b hgt hab)

/-- Every supplied vertex reaches the canonical root of its component. -/
theorem exists_componentRoot (x : GM06DrawingData) (a : Fin x.n) :
    ∃ r ∈ x.componentRoots, x.vertexGraph.Reachable a r := by
  let C := Finset.univ.filter (fun b : Fin x.n => x.vertexGraph.Reachable a b)
  have haC : a ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl a⟩
  have hC : C.Nonempty := ⟨a, haC⟩
  let r := C.min' hC
  have hr := (Finset.mem_filter.mp (Finset.min'_mem C hC)).2
  refine ⟨r, (x.mem_componentRoots_iff r).mpr ?_, hr⟩
  intro b hbr hrb
  have hbC : b ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.trans hrb⟩
  exact (not_lt_of_ge (Finset.min'_le C b hbC)) hbr

end GraphMinor.Compute.GM06DrawingData
