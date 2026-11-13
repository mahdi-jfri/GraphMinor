module

public import GraphMinor.Compute.GM06Alg34DualData
public import GraphMinor.GM06.Alg34DualEndpointCorrect
public import GraphMinor.GM06.Alg34DualRegionBoundary

/-!
# Labelling an assembled dual payload

The finite payload keeps original edge slots and transposes the vertex
and region slots. Compose these index casts with the proved geometric
bijections. The resulting maps are correctness witnesses only and are
never read by the RAM program.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}

/-- The dual payload's vertex labels are its supplied primal region labels. -/
@[expose] noncomputable def dualDataVertexEquiv (h : GM06DrawingRep x G Δ)
    (hd : IsDiscDualDrawing G D) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    Fin (x.dualData L hR g).n ≃ D.V := h.dualVertexEquiv hd

/-- The dual payload's edge labels retain the original edge order. -/
@[expose] noncomputable def dualDataEdgeEquiv (h : GM06DrawingRep x G Δ)
    (hd : IsDiscDualDrawing G D) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    Fin (x.dualData L hR g).ends.length ≃ D.E :=
  (finCongr (x.dualData_edges_length L hR g)).trans (h.dualEdgeEquiv hd)

/-- The dual payload's regions retain the primal vertex order. -/
@[expose] noncomputable def dualDataRegionEquiv (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hconn : IsGraphConnected G.toGraph)
    (hd : IsDiscDualDrawing G D) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    Fin (x.dualData L hR g).regions.length ≃ D.R :=
  (finCongr (x.dualData_regions_length L hR g)).trans (h.dualRegionEquiv hS hconn hd)

/-- Reading a dual payload endpoint slot reads the selected primal incident regions. -/
theorem dualData_ends_get (L : List (Fin x.n)) (hR : 0 < x.regions.length)
    (g : Fin L.length → Fin x.regions.length) (e : Fin (x.dualData L hR g).ends.length) :
    (x.dualData L hR g).ends[e] =
      (x.dualEdgeEnds (finCongr (x.dualData_edges_length L hR g) e)).getD
        (⟨0, hR⟩, ⟨0, hR⟩) := by
  change (x.dualEndsOfNonempty hR)[e.val] = _
  simp only [GM06DrawingData.dualEndsOfNonempty, List.getElem_map, List.getElem_finRange]
  rfl

/-- The assembled dual endpoint record has exactly the actual dual edge ends. -/
theorem dualData_ends [T1Space S] (h : GM06DrawingRep x G Δ)
    (hd : IsDiscDualDrawing G D) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length)
    (e : Fin (x.dualData L hR g).ends.length) :
    closure (h.dualDataEdgeEquiv hd L hR g e).val ∩ D.V =
      {((h.dualDataVertexEquiv hd L hR g) ((x.dualData L hR g).ends[e].1)).val,
        ((h.dualDataVertexEquiv hd L hR g) ((x.dualData L hR g).ends[e].2)).val} := by
  rw [dualData_ends_get]
  exact h.dualEndsOfNonempty_ends hd hR (finCongr (x.dualData_edges_length L hR g) e)

/-- Every assembled dual region record has exactly its actual topological boundary. -/
theorem dualData_boundary [T1Space S] (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) (hconn : IsGraphConnected G.toGraph)
    (hd : IsDiscDualDrawing G D) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length)
    (r : Fin (x.dualData L hR g).regions.length) :
    closure (h.dualDataRegionEquiv hS hconn hd L hR g r).val \
        (h.dualDataRegionEquiv hS hconn hd L hR g r).val =
      {p | ∃ v ∈ (x.dualData L hR g).regions[r].vertices,
        (h.dualDataVertexEquiv hd L hR g v).val = p} ∪
      ⋃ e ∈ (x.dualData L hR g).regions[r].edges,
        (h.dualDataEdgeEquiv hd L hR g e).val := by
  let v : Fin x.n := finCongr (x.dualData_regions_length L hR g) r
  have hr : (x.dualData L hR g).regions[r] = x.dualRegionBoundary hR v := by
    change (List.ofFn (x.dualRegionBoundary hR))[r.val] = _
    rw [List.getElem_ofFn]
    rfl
  change closure (h.dualRegionLabel hd v).val \ (h.dualRegionLabel hd v).val = _
  rw [hr, h.dualRegionBoundary_eq hS hconn hd v]
  apply congrArg₂ (· ∪ ·)
  · rfl
  · ext p
    constructor
    · intro hp
      obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp hp
      refine mem_iUnion₂.mpr ⟨Fin.cast (x.dualEndsOfNonempty_length hR).symm e,
        List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
      exact hpe
    · intro hp
      obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp hp
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      exact mem_iUnion₂.mpr ⟨a, ha, hpe⟩

end GraphMinor.Compute.GM06DrawingRep
