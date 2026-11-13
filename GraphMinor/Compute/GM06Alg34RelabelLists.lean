module

public import GraphMinor.Compute.GM06Alg34LabelList

/-!
# Relabelling finite lists after deletion

Filter each supplied list to surviving labels, then replace each label
by its index in the canonical active list. Index bounds follow from
finite list membership alone. This works for cuff orders, division
blocks, and region boundaries without choosing any geometric data.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- Filter and renumber a supplied vertex list in its existing order. -/
def relabelVertexList (x : GM06DrawingData) (vs L : List (Fin x.n)) :
    List (Fin (x.activeVertices vs).length) :=
  ((L.filter (fun v => decide (v ∈ vs))).attach).map (fun v =>
    gm06ListIndex (x.activeVertices vs) v.val (by
      have hv := (List.mem_filter.mp v.property).2
      exact (x.mem_activeVertices_iff vs v.val).mpr (of_decide_eq_true hv)))

/-- Filter and renumber a supplied edge list in its existing order. -/
def relabelEdgeList (x : GM06DrawingData) (vs : List (Fin x.n)) (L : List (Fin x.ends.length)) :
    List (Fin (x.activeEdges vs).length) :=
  ((L.filter (fun e => decide (e ∈ x.activeEdges vs))).attach).map (fun e =>
    gm06ListIndex (x.activeEdges vs) e.val (by
      have he := (List.mem_filter.mp e.property).2
      exact of_decide_eq_true he))

/-- The endpoint list of all surviving edges, with canonical new vertex labels. -/
def activeEnds (x : GM06DrawingData) (vs : List (Fin x.n)) :
    List (Fin (x.activeVertices vs).length × Fin (x.activeVertices vs).length) :=
  List.ofFn (fun i : Fin (x.activeEdges vs).length =>
    let e := (x.activeEdges vs).get i
    let he := (x.mem_activeEdges_iff vs e).mp (List.get_mem _ i)
    (gm06ListIndex (x.activeVertices vs) x.ends[e].1 ((x.mem_activeVertices_iff vs _).mpr he.1),
      gm06ListIndex (x.activeVertices vs) x.ends[e].2 ((x.mem_activeVertices_iff vs _).mpr he.2)))

/-- One new endpoint pair is supplied for each surviving old edge. -/
theorem activeEnds_length (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.activeEnds vs).length = (x.activeEdges vs).length := by simp [activeEnds]

/-- Reading a relabelled vertex list through its active-label list
recovers exactly the supplied list filtered to surviving vertices. -/
theorem map_relabelVertexList (x : GM06DrawingData) (vs L : List (Fin x.n)) :
    (x.relabelVertexList vs L).map (fun i => (x.activeVertices vs).get i) =
      L.filter (fun v => decide (v ∈ vs)) := by
  simp only [relabelVertexList, List.map_map, Function.comp_def, gm06ListIndex_get,
    List.attach_map_val, List.map_id]
  simpa only [id_eq, List.map_id] using (List.attach_map_val (f := id))

/-- Reading a relabelled edge list through the active edge labels
recovers exactly the supplied list filtered to surviving edges. -/
theorem map_relabelEdgeList (x : GM06DrawingData) (vs : List (Fin x.n))
    (L : List (Fin x.ends.length)) :
    (x.relabelEdgeList vs L).map (fun i => (x.activeEdges vs).get i) =
      L.filter (fun e => decide (e ∈ x.activeEdges vs)) := by
  simp only [relabelEdgeList, List.map_map, Function.comp_def, gm06ListIndex_get,
    List.attach_map_val, List.map_id]
  simpa only [id_eq, List.map_id] using (List.attach_map_val (f := id))

end GraphMinor.Compute.GM06DrawingData
