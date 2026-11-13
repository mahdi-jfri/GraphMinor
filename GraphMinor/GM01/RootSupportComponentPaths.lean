module

public import GraphMinor.GM01.GraphSeparators
public import GraphMinor.GM09.Defs
import GraphMinor.GM09.Section2c

/-!
# The joining path and old-support avoidance in the inside component

Graph Minors I, (5.2), page 61, uses two consequences of the local
situation. A connected component meeting the root support avoids
every support separated from it by the cut. Within the connected
root-support graph, take a path from the ambient root and stop at
its first component vertex. This gives the joining path with only
its final vertex in the component and every vertex in the root support.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- A connected subgraph remaining after the cut, if it meets one side
of a separator, avoids the other side. This proves the first sentence
of GM01 (5.2), page 61. -/
theorem connected_subgraph_disjoint_of_graphSeparates {α β : Type*}
    {G C : Graph α β} {X S B : Set α} (hCG : C ≤ G.deleteVerts X)
    (hCC : GraphConnected C) (hMeet : (V(C) ∩ S).Nonempty)
    (hSep : GraphSeparates G X S B) : Disjoint V(C) B := by
  obtain ⟨w,hwC,hwS⟩ := hMeet
  apply disjoint_left.mpr
  intro x hxC hxB
  have hr : Relation.ReflTransGen (G.deleteVerts X).Adj w x :=
    Relation.ReflTransGen.mono
      (fun _ _ h ↦ by obtain ⟨e,he⟩ := h; exact ⟨e,he.mono hCG⟩)
      w x (hCC.2 w hwC x hxC)
  exact hSep w hwS x hxB (hCG.vertexSet_mono hwC) (hCG.vertexSet_mono hxC) hr

/-- Stop an actual root-support path at its first component vertex,
as in the minimal-path choice in GM01 (5.2), page 61. -/
theorem exists_clean_root_support_path {α β : Type*} {G K : Graph α β}
    (hKG : K ≤ G) (hKC : GraphConnected K) {root : α} (hRoot : root ∈ V(K))
    (T : Set α) (hMeet : (V(K) ∩ T).Nonempty) :
    ∃ v ∈ T, ∃ P : Graph α β, IsGraphPathWithEnds G P root v ∧
      V(P) ⊆ V(K) ∧ V(P) ∩ T = {v} := by
  obtain ⟨w,hwK,hwT⟩ := hMeet
  obtain ⟨Q,hQ⟩ := exists_path_of_adj_reachable hRoot (hKC.2 root hRoot w hwK)
  obtain ⟨v,hv,P,_,hP₀,hPT,_⟩ := hQ.exists_first_hit ⟨w,hQ.right_mem,hwT⟩
  have hPK := hP₀.mono hQ.le
  exact ⟨v,hv.2,P,hPK.mono hKG,hPK.le.vertexSet_mono,hPT⟩

end GraphMinor.GM01
