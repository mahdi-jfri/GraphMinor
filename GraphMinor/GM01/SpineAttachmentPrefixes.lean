module

public import GraphMinor.GM01.RootedGraphs
public import GraphMinor.GM09.Basic
import GraphMinor.GM01.PathLastEdgeCover
import GraphMinor.GM01.ConnectedInducedSets
import GraphMinor.GM01.SubdivisionConnected

/-!
# Contracting attachment prefixes into the spine

Graph Minors I, page 60, contracts all but one edge of each selected
attachment path. Remove its final edge. Add the remaining prefix to
the corresponding connected spine piece. The clean intersections
keep all enlarged pieces disjoint and keep them away from every arm.
The removed edge gives the required link to the arm root.
-/

public section

namespace GraphMinor.GM01

open Set Graph Function GraphMinor.GM09

/-- The actual prefix contraction in the page-60 comb construction.
The resulting spine pieces retain the old pieces and have one joining
edge to each binary-arm support. -/
theorem exists_spine_pieces_with_attachment_prefixes {α β I : Type*}
    (G : Graph α β) (C : I → Set α) (hC : ∀ i, C i ⊆ V(G))
    (hCC : ∀ i, GraphConnected (G.induce (C i)))
    (hCD : Pairwise fun i j ↦ Disjoint (C i) (C j))
    (B : I → RootedGraph α β) (hDis : ∀ i j, Disjoint (C i) V((B j).graph))
    (a : I → α) (hA : ∀ i, a i ∈ C i) (P : I → Graph α β)
    (hP : ∀ i, IsGraphPathWithEnds G (P i) (a i) (B i).root.val)
    (hPC : ∀ i j, V(P i) ∩ C j ⊆ {a i})
    (hSelf : ∀ i, V(P i) ∩ V((B i).graph) = {(B i).root.val})
    (hOther : ∀ i j, i ≠ j → Disjoint V(P i) V((B j).graph))
    (hPP : Pairwise fun i j ↦ Disjoint V(P i) V(P j)) :
    ∃ D : I → Set α, (∀ i, C i ⊆ D i) ∧ (∀ i, D i ⊆ V(G)) ∧
      (∀ i, GraphConnected (G.induce (D i))) ∧
      (Pairwise fun i j ↦ Disjoint (D i) (D j)) ∧
      (∀ i j, Disjoint (D i) V((B j).graph)) ∧
      (∀ i, ∃ e x, x ∈ D i ∧ G.IsLink e x (B i).root.val) ∧
      (∀ i, D i ⊆ C i ∪ V(P i)) := by
  classical
  have hNontrivial : ∀ i, a i ≠ (B i).root.val := by
    intro i heq
    exact disjoint_left.mp (hDis i i) (hA i) (heq.symm ▸ (B i).root.property)
  have hChoice := fun i ↦ exists_last_edge_with_vertex_cover (hP i) (hNontrivial i)
  choose e q R hLink hRP hR hNot hCover using hChoice
  have hRC : ∀ i j, i ≠ j → Disjoint V(R i) (C j) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxR hxC
    have hxa : x = a i := hPC i j ⟨(hRP i).vertexSet_mono hxR,hxC⟩
    exact disjoint_left.mp (hCD hij) (hxa.symm ▸ hA i) hxC
  have hRB : ∀ i j, Disjoint V(R i) V((B j).graph) := by
    intro i j
    by_cases hij : i = j
    · subst j
      apply disjoint_left.mpr
      intro x hxR hxB
      have hxEnd : x ∈ ({(B i).root.val} : Set α) :=
        hSelf i ▸ ⟨(hRP i).vertexSet_mono hxR,hxB⟩
      have hxb : x = (B i).root.val := hxEnd
      exact hNot i (hxb ▸ hxR)
    · exact (hOther i j hij).mono_left (hRP i).vertexSet_mono
  have hRR : Pairwise fun i j ↦ Disjoint V(R i) V(R j) := by
    intro i j hij
    exact (hPP hij).mono (hRP i).vertexSet_mono (hRP j).vertexSet_mono
  let D := fun i ↦ C i ∪ V(R i)
  refine ⟨D,fun _ ↦ subset_union_left,?_,?_,?_,?_,?_,?_⟩
  · intro i x hx
    exact hx.elim (fun h ↦ hC i h) (fun h ↦ (hR i).le.vertexSet_mono h)
  · intro i
    exact graphConnected_induce_union (hCC i)
      (graphConnected_induce_of_subgraph (hR i).le (graphConnected_of_isGraphPath (hR i)))
      ⟨a i,hA i,(hR i).left_mem⟩
  · intro i j hij
    exact ((hCD hij).union_right (hRC j i hij.symm).symm).union_left
      ((hRC i j hij).union_right (hRR hij))
  · intro i j
    exact (hDis i j).union_left (hRB i j)
  · intro i
    exact ⟨e i,q i,Or.inr (hR i).right_mem,(hLink i).mono (hP i).le⟩
  · intro i
    exact union_subset_union_right (C i) (hRP i).vertexSet_mono

end GraphMinor.GM01
