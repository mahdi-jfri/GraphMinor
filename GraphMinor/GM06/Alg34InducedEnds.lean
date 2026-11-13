module

public import GraphMinor.GM06.Alg34InducedLabels
public import GraphMinor.Compute.GM06Alg34ActiveEnds

/-!
# Endpoint representation after deletion

Each surviving edge has both original ends among the active vertices.
Intersecting its closure with the induced vertex set therefore retains
exactly those ends. The computed new endpoint numbers denote the same
points by the finite endpoint identities. This verifies the endpoint
condition of the updated drawing representation, including loops.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- The new endpoint list describes the actual ends of every surviving
edge in the induced drawing. -/
theorem inducedEdge_ends (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n))
    (e : Fin (x.activeEnds vs).length) :
    closure (h.inducedEdge vs (Fin.cast (x.activeEnds_length vs) e)).val ∩
        (induceDrawing G (h.vertexImage vs)).V =
      {(h.inducedVertex vs (x.activeEnds vs)[e].1).val,
        (h.inducedVertex vs (x.activeEnds vs)[e].2).val} := by
  let i := Fin.cast (x.activeEnds_length vs) e
  let old := (x.activeEdges vs).get i
  have hold : x.ends[old].1 ∈ vs ∧ x.ends[old].2 ∈ vs :=
    (x.mem_activeEdges_iff vs old).mp (List.get_mem _ i)
  have hpair : ({(h.vertex x.ends[old].1).val, (h.vertex x.ends[old].2).val} : Set S) ⊆
      h.vertexImage vs := pair_subset_iff.mpr
    ⟨(h.vertex_mem_image_iff vs _).mpr hold.1, (h.vertex_mem_image_iff vs _).mpr hold.2⟩
  have hfst : (x.activeVertices vs).get (x.activeEnds vs)[e].1 = x.ends[old].1 := by
    have hh := x.activeEnds_fst vs i
    simp only [i, Fin.val_cast] at hh
    convert hh using 1
  have hsnd : (x.activeVertices vs).get (x.activeEnds vs)[e].2 = x.ends[old].2 := by
    have hh := x.activeEnds_snd vs i
    simp only [i, Fin.val_cast] at hh
    convert hh using 1
  change closure (h.edge old).val ∩ (induceDrawing G (h.vertexImage vs)).V =
    {(h.vertex ((x.activeVertices vs).get (x.activeEnds vs)[e].1)).val,
      (h.vertex ((x.activeVertices vs).get (x.activeEnds vs)[e].2)).val}
  rw [induceDrawing_V G (h.vertexImage_subset vs), hfst, hsnd]
  calc
    closure (h.edge old).val ∩ h.vertexImage vs =
        (closure (h.edge old).val ∩ G.V) ∩ h.vertexImage vs := by
      ext p
      constructor
      · exact fun hp => ⟨⟨hp.1, h.vertexImage_subset vs hp.2⟩, hp.2⟩
      · exact fun hp => ⟨hp.1.1, hp.2⟩
    _ = _ := by rw [h.ends old, inter_eq_left.mpr hpair]

end GraphMinor.Compute.GM06DrawingRep
