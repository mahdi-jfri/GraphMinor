module

public import GraphMinor.GM01.PathEndRegions
public import GraphMinor.Minor.Model
import GraphMinor.GM01.GraphSeparators

/-!
# Extending a path to the first boundary

For Graph Minors I, (4.8), page 58, the late blocks are avoided by
working in a connected initial piece. A path there from the attachment
vertex to the early cut cannot enter the early part before its final
vertex. The initial-subpath lemma for avoidance regions supplies this
last assertion.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- The region form of the boundary extension in GM01 (4.8), page 58.
A connected initial piece contains the attachment and the cut. Its path
to the cut stays beyond the early boundary until its final vertex. -/
theorem exists_path_to_region_boundary_avoiding {α β : Type*} {H : Graph α β}
    {D : Set α} {last cut x : α}
    (hconn : GraphConnected (H.induce (V(H) \ D)))
    (hx : x ∈ V(H) \ D) (hcut : cut ∈ V(H) \ D)
    (hxRegion : x ∈ vertexAvoidanceRegion H last cut) :
    ∃ P : Graph α β, IsGraphPathWithEnds H P x cut ∧
      Disjoint V(P) ((D ∪ (V(H) \ vertexAvoidanceRegion H last cut)) \ {cut}) := by
  obtain ⟨P, hP⟩ := exists_path_of_adj_reachable hx (hconn.2 x hx cut hcut)
  have hle : H.induce (V(H) \ D) ≤ H := by
    refine ⟨fun _ h ↦ h.1, ?_⟩
    intro e a b he
    exact he.1
  have hPH := hP.mono hle
  have hRegion := path_subset_vertexAvoidanceRegion_insert_cut hPH hxRegion
  refine ⟨P, hPH, ?_⟩
  apply Set.disjoint_left.mpr
  intro y hy hyCut
  rcases hyCut.1 with hyD | hyEarly
  · exact (hP.le.vertexSet_mono hy).2 hyD
  · rcases hRegion hy with hyEq | hyRegion
    · exact hyCut.2 hyEq
    · exact hyEarly.2 hyRegion

end GraphMinor.GM01
