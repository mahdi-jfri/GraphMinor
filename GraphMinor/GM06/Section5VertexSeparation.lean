module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section3Induce
import GraphMinor.GM11.Walks

/-!
# Separating a branch attached at one vertex

The exclusion of Reduction 2 in VI (5.1), page 129, removes a part
of the graph attached only at an initial vertex and missed by the
linkage. Keep the drawing induced on the other vertices. Put all
remaining edges, and the removed vertices, on the other side.
The attachment condition puts every end of those edges on the
removed side or at the single attachment vertex.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- A set of vertices attached to the rest only at v can be put on
one side of a separation with separator contained in {v}. The other
side is the full drawing induced on the remaining vertices, as
required to apply Reduction 2 in VI (5.1), page 129. -/
theorem exists_separation_of_set_attached_at_vertex
    {S : Type u} [TopologicalSpace S] [T1Space S] (G : Drawing S)
    {X : Set S} {v : S} (hX : X ⊆ G.V)
    (hport : ∀ e a b, G.toGraph.IsLink e a b → a ∈ X → b ∈ X ∨ b = v) :
    ∃ H : Drawing S,
      IsGraphSeparation G.toGraph (induceDrawing G (G.V \ X)).toGraph H.toGraph ∧
      (induceDrawing G (G.V \ X)).V ∩ H.V ⊆ {v} := by
  classical
  let F := induceDrawing G (G.V \ X)
  have hFG : F.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hFV : F.V = G.V \ X := induceDrawing_V G sdiff_subset
  have hends : ∀ e ∈ G.E \ F.E, closure e ∩ G.V ⊆ X ∪ {v} := by
    intro e he
    obtain ⟨a, b, hl⟩ := G.toGraph.exists_isLink_of_mem_edgeSet he.1
    have hhit : a ∈ X ∨ b ∈ X := by
      by_contra hn
      have ha : a ∉ X := fun h => hn (Or.inl h)
      have hb : b ∉ X := fun h => hn (Or.inr h)
      apply he.2
      rw [induceDrawing_E]
      refine ⟨he.1, ?_⟩
      rw [hl.2.2.2]
      rintro y (rfl | hy)
      · exact ⟨hl.left_mem, ha⟩
      · rw [mem_singleton_iff.mp hy]
        exact ⟨hl.right_mem, hb⟩
    have hab : a ∈ X ∪ {v} ∧ b ∈ X ∪ {v} := by
      rcases hhit with ha | hb
      · exact ⟨Or.inl ha, (hport e a b hl ha).elim Or.inl Or.inr⟩
      · exact ⟨(hport e b a hl.symm hb).elim Or.inl Or.inr, Or.inl hb⟩
    rw [hl.2.2.2]
    rintro y (rfl | hy)
    · exact hab.1
    · rw [mem_singleton_iff.mp hy]
      exact hab.2
  let H := G.span (X ∪ {v}) (G.E \ F.E)
  have hHG : H.IsSubdrawing G := Drawing.span_isSubdrawing G _ _
  have hHE : H.E = G.E \ F.E := by
    rw [Drawing.span_E]
    exact inter_eq_left.mpr sdiff_subset
  have hHV : H.V ⊆ X ∪ {v} := by
    rw [Drawing.span_V, Drawing.spanV]
    rintro y (hy | hy)
    · exact hy.1
    · obtain ⟨e, ⟨he, _⟩, hye⟩ := mem_iUnion₂.mp hy
      exact hends e he hye
  have hXH : X ⊆ H.V := by
    intro y hy
    rw [Drawing.span_V, Drawing.spanV]
    exact Or.inl ⟨Or.inl hy, hX hy⟩
  have hFle : F.toGraph ≤ G.toGraph := {
    vertexSet_mono := hFG.1
    isLink_mono := fun e a b hl => (hFG.isLink_iff hl.1).mp hl }
  have hHle : H.toGraph ≤ G.toGraph := {
    vertexSet_mono := hHG.1
    isLink_mono := fun e a b hl => (hHG.isLink_iff hl.1).mp hl }
  refine ⟨H, ⟨hFle, hHle, ?_, ?_, ?_⟩, ?_⟩
  · change F.V ∪ H.V = G.V
    apply subset_antisymm (union_subset hFG.1 hHG.1)
    intro y hy
    by_cases hyX : y ∈ X
    · exact Or.inr (hXH hyX)
    · apply Or.inl
      rw [hFV]
      exact ⟨hy, hyX⟩
  · change F.E ∪ H.E = G.E
    rw [hHE, union_comm]
    exact sdiff_union_of_subset hFG.2
  · change Disjoint F.E H.E
    rw [hHE]
    exact disjoint_left.mpr fun e heF heH => heH.2 heF
  · intro y hy
    have hyNotX : y ∉ X := by
      have hh := hy.1
      rw [hFV] at hh
      exact hh.2
    rcases hHV hy.2 with hyX | hyv
    · exact False.elim (hyNotX hyX)
    · exact hyv

end GraphMinor.GM06
