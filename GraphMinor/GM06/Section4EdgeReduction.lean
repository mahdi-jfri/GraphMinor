module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4NoObstructions
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section4Minimal
import GraphMinor.GM06.Section4Uncross
import GraphMinor.GM06.Section4Routed
import GraphMinor.GM06.Section5Red
import GraphMinor.GM11.Walks

/-!
# A homotopic segment edge permits Reduction 2

The final sentence of VI (4.2), page 127, applies Reduction 2 to the
edge supplied by (4.3). The minimal boundary path has every boundary
vertex on this single-edge path. If Reduction 2(ii) does not already
apply, its only vertices are therefore its ends. It has one edge, so
Reduction 2(iii) applies.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

/-- An edge in the homotopy class of a routed boundary segment permits
Reduction 2, as used at the end of VI (4.2), page 127. -/
theorem reduction2_of_edge_homotopic_to_segment
    {S : Type u} [TopologicalSpace S] {G H Hst : Drawing S}
    {A e : Set S} {s t : S} (hS : IsSurface S) (hG : G.IsProper)
    (hbd : H.V ∩ bd S = G.V ∩ bd S)
    (hA : A ∈ segmentsOf (bd S) (H.V ∩ bd S))
    (hs : s ∈ H.V ∩ bd S) (ht : t ∈ H.V ∩ bd S) (hst : s ≠ t)
    (hsA : s ∈ closure A) (htA : t ∈ closure A)
    (hHst : IsSubpathOf H Hst s t) (hHA : PathHomotopicToArc Hst s t A)
    (hl : G.toGraph.IsLink e s t)
    (f g : Curve S) (hf : ParametrizesSet f (closure e) s t)
    (hg : ParametrizesSet g Hst.U s t) (hfg : CurvesHomotopic f g) :
    Section4Reduction2Applies G H := by
  let : T2Space S := hS.2.1
  let W : GraphWalk G.toGraph s t := .cons hl (.nil hl.right_mem)
  let Q := walkDrawing G W
  have hW : W.IsSimple := by
    simp [W, GraphWalk.IsSimple, GraphWalk.support, hst]
  have hQsub : Q.IsSubdrawing G := walkDrawing_isSubdrawing G W
  have hQpath : IsPathDrawing Q s t := isPathDrawing_walkDrawing_of_isSimple G hW hst
  have hQV : Q.V = {s, t} := by
    rw [walkDrawing_V]
    ext x
    simp [W, GraphWalk.support]
  have hend : ({s, t} : Set S) ⊆ closure e := by
    rw [← hl.2.2.2]
    exact inter_subset_left
  have hQU : Q.U = closure e := by
    ext x
    rw [mem_walkDrawing_U]
    constructor
    · rintro (hx | ⟨e', he', hx⟩)
      · apply hend
        simpa [W, GraphWalk.support] using hx
      · have heq : e' = e := by simpa [W, GraphWalk.edges] using he'
        exact heq ▸ hx
    · intro hx
      exact Or.inr ⟨e, by simp [W, GraphWalk.edges], hx⟩
  have hfQ : ParametrizesSet f Q.U s t := hQU.symm ▸ hf
  have hQA : PathHomotopicToArc Q s t A :=
    pathHomotopicToArc_of_pathsHomotopic ⟨f, g, hfQ, hg, hfg⟩ hHA
  have hsegG : IsSegmentOf (bd S) (G.V ∩ bd S) A := by rw [← hbd]; exact hA
  obtain ⟨P, hP⟩ := exists_isMinimalBoundaryPath_of_segment_path
    hS hG hst hsegG ⟨hQsub, hQsub.U_subset, hQpath⟩ hQA
  by_contra hno
  have hPVbd := minimalBoundaryPath_vertices_boundary_of_not_reduction2
    hno hA hs ht hst hsA htA hHst hHA hP
  have hPV : P.V ⊆ {s, t} := by
    intro x hx
    rw [← hQV]
    exact boundary_vertex_mem_of_isMinimalBoundaryPath hS hG hsegG hP
      ⟨hQsub, hQsub.U_subset, hQpath⟩ hQA ⟨hx, hPVbd hx⟩
  have hPE : P.E.ncard = 1 :=
    ncard_edges_eq_one_of_path_vertices_subset_ends hP.2.2.1 hst hPV
  exact hno ⟨A, hA, s, hs, t, ht, hst, hsA, htA, ⟨Hst, hHst, hHA⟩,
    P, hP, Or.inr (Or.inr hPE)⟩

end GraphMinor.GM06
