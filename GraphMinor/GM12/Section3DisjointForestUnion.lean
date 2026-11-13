module

public import GraphMinor.Surface.Defs
import GraphMinor.GM11.Walks

/-!
# Disjoint unions preserve the forest property

In XII (3.1), page 245, the local forests in the feasibility discs
have disjoint supports. A walk starting in one component cannot use
an edge of the other, because the components have disjoint vertices.
Thus every simple closed walk transfers to one local forest and has
length zero.
-/

public section

namespace GraphMinor.GM12

open Set Surface

private theorem walk_stays_in_disjoint_subdrawing
    {S : Type*} [TopologicalSpace S] {A B K : Drawing S}
    (hA : A.IsSubdrawing K) (hB : B.IsSubdrawing K)
    (hdis : Disjoint A.V B.V) (hE : K.E ⊆ A.E ∪ B.E)
    {u v : S} (W : GraphWalk K.toGraph u v) (hu : u ∈ A.V) :
    (∀ x ∈ W.support, x ∈ A.V) ∧ (∀ e ∈ W.edges, e ∈ A.E) := by
  revert hu
  induction W with
  | nil huK =>
    intro hu
    constructor
    · intro x hx
      have hxu : x = _ := List.mem_singleton.mp hx
      exact hxu ▸ hu
    · intro e he
      exact False.elim (List.not_mem_nil he)
  | @cons u v w e he rest ih =>
    intro hu
    have heA : e ∈ A.E := by
      rcases hE he.1 with heA | heB
      · exact heA
      · have hb := (hB.isLink_iff heB).mpr he
        exact False.elim (Set.disjoint_left.mp hdis hu hb.2.1)
    have ha := (hA.isLink_iff heA).mpr he
    obtain ⟨hrestV, hrestE⟩ := ih ha.2.2.1
    constructor
    · intro x hx
      rcases List.mem_cons.mp hx with hxu | hxrest
      · exact hxu ▸ hu
      · exact hrestV x hxrest
    · intro f hf
      rcases List.mem_cons.mp hf with hfe | hfrest
      · exact hfe ▸ heA
      · exact hrestE f hfrest

/-- A graph covered by two forests on disjoint vertex sets is a
forest. Walks stay in the component containing their first vertex. -/
theorem isGraphForest_of_disjoint_subdrawing_cover
    {S : Type*} [TopologicalSpace S] (A B K : Drawing S)
    (hA : A.IsSubdrawing K) (hB : B.IsSubdrawing K)
    (hdis : Disjoint A.V B.V) (hV : K.V ⊆ A.V ∪ B.V) (hE : K.E ⊆ A.E ∪ B.E)
    (hforestA : IsGraphForest A.toGraph) (hforestB : IsGraphForest B.toGraph) :
    IsGraphForest K.toGraph := by
  have hcomponent : ∀ {A B : Drawing S}, A.IsSubdrawing K → B.IsSubdrawing K →
      Disjoint A.V B.V → K.E ⊆ A.E ∪ B.E → IsGraphForest A.toGraph →
      ∀ {u : S} (W : GraphWalk K.toGraph u u), u ∈ A.V → W.IsSimpleClosed → W.length = 0 := by
    intro A B hA hB hdis hE hforest u W hu hW
    obtain ⟨hWV, hWE⟩ := walk_stays_in_disjoint_subdrawing hA hB hdis hE W hu
    obtain ⟨W', hs, he⟩ := hA.exists_walk_down W hWV hWE
    have hW' : W'.IsSimpleClosed := by
      change W'.support.tail.Nodup ∧ W'.edges.Nodup
      rw [hs, he]
      exact hW
    have hzero := hforest u W' hW'
    change W.edges.length = 0
    rw [← he]
    exact hzero
  intro u W hW
  have hu : u ∈ K.V := W.mem_vertexSet_of_mem_support W.start_mem_support
  rcases hV hu with huA | huB
  · exact hcomponent hA hB hdis hE hforestA W huA hW
  · exact hcomponent hB hA hdis.symm (by simpa only [union_comm] using hE)
      hforestB W huB hW

end GraphMinor.GM12
