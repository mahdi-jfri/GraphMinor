module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM11.PaintingCells
import GraphMinor.GM11.Walks

/-!
# Boundary vertices of the components in VI (4.2)

The proof of Graph Minors VI (4.2), page 125, first excludes components with
fewer than two boundary vertices. A component with at most one such vertex is
homotopic to that vertex, or to the empty drawing. Its boundary point set is a
subdrawing of the instance, so Reduction 1 applies.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- A component with at most one boundary vertex permits Reduction 1 of
Graph Minors VI, Section 4, page 124. The homotopy conditions between distinct
boundary vertices are vacuous for that component. -/
theorem reduction1_of_subsingleton_component_boundary
    {S : Type u} [TopologicalSpace S] [T2Space S] {G H : Drawing S}
    (hH : H.IsProper) (hforest : IsGraphForest H.toGraph)
    (hbd : H.V ∩ bd S = G.V ∩ bd S)
    {C : Graph S (Set S)} (hC : IsGraphComponent C H.toGraph)
    (hsmall : (Graph.vertexSet C ∩ bd S).Subsingleton) :
    Section4Reduction1Applies G H := by
  let Hc := induceDrawing H (Graph.vertexSet C)
  have hHcV : Hc.V = Graph.vertexSet C := induceDrawing_V H hC.1.vertexSet_mono
  have hHcG : Hc.toGraph = C := induceDrawing_toGraph_of_component H hC
  have hHcsub : Hc.IsSubdrawing H := induceDrawing_isSubdrawing H hC.1.vertexSet_mono
  have hHcprop : Hc.IsProper := induceDrawing_isProper H hH hC.1.vertexSet_mono
  have hHcforest : IsGraphForest Hc.toGraph := by
    rw [hHcG]
    exact isGraphForest_of_le hC.1 hforest
  let A := Graph.vertexSet C ∩ bd S
  have hA : A.Finite := (H.finite_V.subset hC.1.vertexSet_mono).inter_of_left _
  let K := pointsDrawing hA
  have hAG : A ⊆ G.V := by
    intro x hx
    have hxH : x ∈ H.V ∩ bd S := ⟨hC.1.vertexSet_mono hx.1, hx.2⟩
    exact (hbd ▸ hxH).1
  have hKE : K.E = ∅ := by
    ext e
    constructor
    · intro he
      obtain ⟨x, hx⟩ := he.1
      have hxx : x ∈ A \ A := he.2.1 hx
      exact False.elim (hxx.2 hxx.1)
    · intro he
      exact False.elim he
  have hKG : K.IsSubdrawing G := by
    refine ⟨hAG, ?_⟩
    rw [hKE]
    exact empty_subset _
  have hKU : K.U ⊆ G.U := fun x hx => G.V_subset_U (hAG hx)
  have hKprop : K.IsProper := by
    change bd S ∩ A ⊆ A
    exact inter_subset_right
  have hKforest : IsGraphForest K.toGraph := by
    intro x W _
    cases W with
    | nil _ => rfl
    | cons hl r =>
      have he := hl.1
      rw [hKE] at he
      exact False.elim he
  have hKV : K.V = Hc.V ∩ bd S := by
    rw [hHcV]
    rfl
  have hKbd : K.V ∩ bd S = Hc.V ∩ bd S := by
    rw [hKV, inter_assoc, inter_self]
  have hhom : ForestsHomotopic K Hc := by
    refine ⟨hKprop, hHcprop, hKforest, hHcforest, hKbd, ?_⟩
    intro s hs t ht hst
    exact False.elim (hst (hsmall hs.1 ht.1))
  refine ⟨Hc, hHcsub, hHcsub.U_subset, ?_, K, hKG, hKU, hKV, hhom⟩
  rw [hHcG]
  exact hC

/-- The first sentence of the proof of Graph Minors VI (4.2), page 125:
"No component of $H$ has fewer than two vertices in $bd(\\Sigma)$, because reduction 1 cannot be applied."
This holds for any surface before using the cylinder assumption. -/
theorem component_boundary_two_le_of_not_reduction1
    {S : Type u} [TopologicalSpace S] [T2Space S] {G H : Drawing S}
    (hH : H.IsProper) (hforest : IsGraphForest H.toGraph)
    (hbd : H.V ∩ bd S = G.V ∩ bd S) (hno : ¬ Section4Reduction1Applies G H)
    {C : Graph S (Set S)} (hC : IsGraphComponent C H.toGraph) :
    2 ≤ (Graph.vertexSet C ∩ bd S).ncard := by
  have hfin : (Graph.vertexSet C ∩ bd S).Finite :=
    (H.finite_V.subset hC.1.vertexSet_mono).inter_of_left _
  by_contra hnot
  have hcard : (Graph.vertexSet C ∩ bd S).ncard ≤ 1 := by omega
  have hsmall : (Graph.vertexSet C ∩ bd S).Subsingleton := (ncard_le_one hfin).mp hcard
  exact hno (reduction1_of_subsingleton_component_boundary hH hforest hbd hC hsmall)

end GraphMinor.GM06
