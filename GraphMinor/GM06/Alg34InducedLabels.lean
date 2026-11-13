module

public import GraphMinor.GM06.Alg34InducedCells
public import GraphMinor.GM06.Alg34RegionLabels
public import GraphMinor.Compute.GM06Alg34InducedData

/-!
# Vertex, edge, and region labels after deletion

The new labels are positions in the canonical lists of surviving
vertices, surviving edges, and complement-component roots. Map each
position to the old geometric object it denotes. These maps are
bijective onto the induced drawing's vertices, edges, and regions.
This verifies the object labels of the computed updated input.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06 GM11

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- The actual surviving vertex denoted by a canonical new vertex position. -/
def inducedVertex (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (i : Fin (x.activeVertices vs).length) : (induceDrawing G (h.vertexImage vs)).V :=
  ⟨(h.vertex ((x.activeVertices vs).get i)).val, by
    rw [induceDrawing_V G (h.vertexImage_subset vs)]
    exact (h.vertex_mem_image_iff vs _).mpr
      ((x.mem_activeVertices_iff vs _).mp (List.get_mem _ i))⟩

/-- The actual surviving edge denoted by a canonical new edge position. -/
def inducedEdge (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (i : Fin (x.activeEdges vs).length) : (induceDrawing G (h.vertexImage vs)).E :=
  ⟨(h.edge ((x.activeEdges vs).get i)).val, (h.edge_mem_induced_iff vs _).mpr
    ((x.mem_activeEdges_iff vs _).mp (List.get_mem _ i))⟩

/-- The actual new region denoted by a position in the canonical root list. -/
def inducedRegion (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (i : Fin (x.regionRoots vs).length) : (induceDrawing G (h.vertexImage vs)).R :=
  h.regionLabel vs ⟨(x.regionRoots vs).get i, List.get_mem _ i⟩

/-- The canonical new vertex labels describe all surviving vertices bijectively. -/
theorem inducedVertex_bijective (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) :
    Function.Bijective (h.inducedVertex vs) := by
  constructor
  · intro i j hij
    have hval := congrArg (fun p : (induceDrawing G (h.vertexImage vs)).V => p.val) hij
    have hv : (x.activeVertices vs).get i = (x.activeVertices vs).get j :=
      h.vertex.injective (Subtype.ext hval)
    exact (x.activeVertices_nodup vs).get_inj_iff.mp hv
  · intro p
    have hp : p.val ∈ h.vertexImage vs :=
      (induceDrawing_V G (h.vertexImage_subset vs)).subset p.property
    obtain ⟨v, hv, heq⟩ := hp
    let i := gm06ListIndex (x.activeVertices vs) v ((x.mem_activeVertices_iff vs v).mpr hv)
    refine ⟨i, Subtype.ext ?_⟩
    change (h.vertex ((x.activeVertices vs).get i)).val = p.val
    rw [gm06ListIndex_get]
    exact heq

/-- The canonical new edge labels describe all surviving edges bijectively. -/
theorem inducedEdge_bijective (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) :
    Function.Bijective (h.inducedEdge vs) := by
  constructor
  · intro i j hij
    have hval := congrArg (fun e : (induceDrawing G (h.vertexImage vs)).E => e.val) hij
    have he : (x.activeEdges vs).get i = (x.activeEdges vs).get j :=
      h.edge.injective (Subtype.ext hval)
    exact (x.activeEdges_nodup vs).get_inj_iff.mp he
  · intro e
    have heG : e.val ∈ G.E := (induceDrawing_E G (h.vertexImage vs)).subset e.property |>.1
    obtain ⟨a, ha⟩ := h.edge.surjective ⟨e.val, heG⟩
    have heq : (h.edge a).val = e.val := congrArg Subtype.val ha
    have ha' : a ∈ x.activeEdges vs := (x.mem_activeEdges_iff vs a).mpr
      ((h.edge_mem_induced_iff vs a).mp (heq.symm ▸ e.property))
    let i := gm06ListIndex (x.activeEdges vs) a ha'
    refine ⟨i, Subtype.ext ?_⟩
    change (h.edge ((x.activeEdges vs).get i)).val = e.val
    rw [gm06ListIndex_get]
    exact heq

/-- Canonical root positions describe all new regions bijectively. -/
theorem inducedRegion_bijective (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) :
    Function.Bijective (h.inducedRegion vs) := by
  constructor
  · intro i j hij
    have heq := (h.regionLabel_bijective vs).1 hij
    have hget := congrArg Subtype.val heq
    exact (x.regionRoots_nodup vs).get_inj_iff.mp hget
  · intro r
    obtain ⟨a, ha⟩ := (h.regionLabel_bijective vs).2 r
    let i := gm06ListIndex (x.regionRoots vs) a.val a.property
    refine ⟨i, ?_⟩
    have hlabel : (⟨(x.regionRoots vs).get i, List.get_mem _ i⟩ :
        {r : Fin x.cellCount // r ∈ x.regionRoots vs}) = a :=
      Subtype.ext (gm06ListIndex_get _ _ _)
    change h.regionLabel vs _ = r
    rw [hlabel]
    exact ha

end GraphMinor.Compute.GM06DrawingRep
