module

public import GraphMinor.GM06.Section4Comparison
import GraphMinor.GM06.Section4SubgraphDrawing
import GraphMinor.GM06.Section4EdgeHomotopy
import GraphMinor.GM06.Section4ComponentSeparation
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM07.PushForest

/-!
# A connected comparison drawing permits Reduction 1

Graph Minors VI (4.2), page 126, observes that G′ is disconnected when
Reduction 1 cannot apply. We prove the contrapositive. A spanning tree
of G′ has exactly the boundary vertices of the chosen component. Its
edges have homotopic paths in that component by the definition of G′.
Combining those edge homotopies makes this tree homotopic to the
component, giving the subdrawing required by Reduction 1.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

/-- Graph Minors VI (4.2), page 126: if G′ is connected, Reduction 1
applies to the chosen component of H. -/
theorem reduction1_of_connected_componentComparisonDrawing
    {S : Type} [TopologicalSpace S] [T2Space S] {G H : Drawing S}
    (hG : G.IsProper) (hH : H.IsProper) (hforest : IsGraphForest H.toGraph)
    (hbd : H.V ∩ bd S = G.V ∩ bd S)
    {K : Graph S (Set S)} (hK : IsGraphComponent K H.toGraph)
    (hconn : IsGraphConnected (componentComparisonDrawing G H K).toGraph) :
    Section4Reduction1Applies G H := by
  have hW : Graph.vertexSet K ∩ bd S ⊆ G.V := by
    intro x hx
    have hxH : x ∈ H.V ∩ bd S := ⟨hK.1.vertexSet_mono hx.1, hx.2⟩
    exact (hbd ▸ hxH).1
  let D := componentComparisonDrawing G H K
  have hDV : D.V = Graph.vertexSet K ∩ bd S := componentComparisonDrawing_V G H K hW
  obtain ⟨T, hTD, hTV, hTc, hTf⟩ := exists_spanning_tree D.finite_edges hconn
  let F := drawingOfSubgraph D T
  have hFD : F.IsSubdrawing D := drawingOfSubgraph_isSubdrawing D T
  have hFG : F.IsSubdrawing G := hFD.trans (componentComparisonDrawing_isSubdrawing G H K)
  have hFV : F.V = Graph.vertexSet K ∩ bd S :=
    (drawingOfSubgraph_V D hTD).trans (hTV.trans hDV)
  have hFT : F.toGraph = T := drawingOfSubgraph_toGraph D hTD
  have hFf : IsGraphForest F.toGraph := hFT.symm ▸ hTf
  have hFc : IsGraphConnected F.toGraph := hFT.symm ▸ hTc
  have hFp : F.IsProper := isProper_of_isSubdrawing hG hFG
  let Hc := induceDrawing H (Graph.vertexSet K)
  have hHcsub : Hc.IsSubdrawing H := induceDrawing_isSubdrawing H hK.1.vertexSet_mono
  have hHcV : Hc.V = Graph.vertexSet K := induceDrawing_V H hK.1.vertexSet_mono
  have hHcU : Hc.U = compPointSet K := induceDrawing_U_of_component H hK
  have hHcK : Hc.toGraph = K := induceDrawing_toGraph_of_component H hK
  have hHcp : Hc.IsProper := isProper_of_isSubdrawing hH hHcsub
  have hHcf : IsGraphForest Hc.toGraph := by
    rw [hHcK]
    exact isGraphForest_of_le hK.1 hforest
  have hHcc : IsGraphConnected Hc.toGraph := hHcK.symm ▸ hK.2.1
  have hFVHc : F.V ⊆ Hc.V := by rw [hFV, hHcV]; exact inter_subset_left
  have hFbd : F.V ∩ bd S = Hc.V ∩ bd S := by
    rw [hFV, hHcV, inter_assoc, inter_self]
  have hedges : ∀ (e : Set S) (a b : S), F.toGraph.IsLink e a b →
      ∃ p q : Path a b, (∀ t, p t ∈ closure e) ∧ (∀ t, q t ∈ Hc.U) ∧ p.Homotopic q := by
    intro e a b hl
    have hlD : D.toGraph.IsLink e a b := (hFD.isLink_iff hl.1).mp hl
    obtain ⟨ha, _, _, P, hP, f, g, hf, hg, hfg⟩ :=
      componentComparisonDrawing_edge_data G H K hlD
    let p : Path a b := ⟨f, hf.2.2.1, hf.2.2.2⟩
    let q : Path a b := ⟨g, hg.2.2.1, hg.2.2.2⟩
    have hPU : P.U ⊆ compPointSet K := path_U_subset_compPointSet_of_start hK hP ha.1
    refine ⟨p, q, fun t => hf.2.1 ▸ mem_range_self t, ?_, GM07.homotopic_of_curves hfg⟩
    intro t
    rw [hHcU]
    exact hPU (hg.2.1 ▸ mem_range_self t)
  have hhom : ForestsHomotopic F Hc := forestsHomotopic_of_edge_representatives
    hFp hHcp hFf hHcf hFc hHcc hFVHc hFbd hedges
  refine ⟨Hc, hHcsub, hHcsub.U_subset, ?_, F, hFG, hFG.U_subset, ?_, hhom⟩
  · rw [hHcK]
    exact hK
  · rw [hFV, hHcV]

/-- The disconnection observation in Graph Minors VI (4.2), page 126,
now with the spanning-tree and homotopy steps supplied. -/
theorem not_connected_componentComparisonDrawing_of_not_reduction1
    {S : Type} [TopologicalSpace S] [T2Space S] {G H : Drawing S}
    (hG : G.IsProper) (hH : H.IsProper) (hforest : IsGraphForest H.toGraph)
    (hbd : H.V ∩ bd S = G.V ∩ bd S)
    {K : Graph S (Set S)} (hK : IsGraphComponent K H.toGraph)
    (hno : ¬ Section4Reduction1Applies G H) :
    ¬ IsGraphConnected (componentComparisonDrawing G H K).toGraph :=
  fun hconn => hno (reduction1_of_connected_componentComparisonDrawing hG hH hforest hbd hK hconn)

end GraphMinor.GM06
