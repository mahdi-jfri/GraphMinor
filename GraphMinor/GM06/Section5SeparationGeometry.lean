module

public import GraphMinor.GM06.Defs
import GraphMinor.GM11.Walks

/-!
# Point sets in the separation of Reduction 2

For VI (5.5), page 130, translate the graph separation into the
geometry of the drawings. Its two point sets cover the drawing and
meet precisely in their common vertices. In Reduction 2 the removed
side consequently meets the retained side and the cuffs only at the
specified initial vertex.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- An old vertex lying on a subdrawing is a vertex of that subdrawing. -/
theorem vertex_mem_of_mem_subdrawing_point_set
    {S : Type*} [TopologicalSpace S] {G H : Drawing S} (hHG : H.IsSubdrawing G)
    {x : S} (hxH : x ∈ H.U) (hxG : x ∈ G.V) : x ∈ H.V := by
  by_contra hx
  obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hxH hx
  exact ((hHG.2 he).2.1 hxe).2 hxG

/-- The two point sets of a graph separation cover the old drawing
and meet exactly in the common vertex set. -/
theorem point_sets_of_graph_separation
    {S : Type*} [TopologicalSpace S] {G G₁ G₂ : Drawing S}
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph) :
    G₁.U ∪ G₂.U = G.U ∧ G₁.U ∩ G₂.U = G₁.V ∩ G₂.V := by
  have h₁ : G₁.IsSubdrawing G := ⟨hsep.1.vertexSet_mono, hsep.1.edgeSet_mono⟩
  have h₂ : G₂.IsSubdrawing G := ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono⟩
  have hV : G₁.V ∪ G₂.V = G.V := hsep.2.2.1
  have hE : G₁.E ∪ G₂.E = G.E := hsep.2.2.2.1
  have hdE : Disjoint G₁.E G₂.E := hsep.2.2.2.2
  constructor
  · apply subset_antisymm (union_subset h₁.U_subset h₂.U_subset)
    intro x hx
    rw [G.U_eq] at hx
    rcases hx with hx | hx
    · rcases hV ▸ hx with hx | hx
      · exact Or.inl (G₁.V_subset_U hx)
      · exact Or.inr (G₂.V_subset_U hx)
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      rcases hE ▸ he with he | he
      · exact Or.inl (G₁.closure_subset_U he hxe)
      · exact Or.inr (G₂.closure_subset_U he hxe)
  · apply subset_antisymm
    · rintro x ⟨hx₁, hx₂⟩
      by_cases hxV : x ∈ G.V
      · exact ⟨vertex_mem_of_mem_subdrawing_point_set h₁ hx₁ hxV,
          vertex_mem_of_mem_subdrawing_point_set h₂ hx₂ hxV⟩
      · have hxV₁ : x ∉ G₁.V := fun h => hxV (h₁.1 h)
        have hxV₂ : x ∉ G₂.V := fun h => hxV (h₂.1 h)
        obtain ⟨a, ha, hxa⟩ := G₁.exists_edge_of_mem hx₁ hxV₁
        obtain ⟨b, hb, hxb⟩ := G₂.exists_edge_of_mem hx₂ hxV₂
        have hab : a = b := G.edge_eq_of_mem (h₁.2 ha) (h₂.2 hb) hxa hxb
        exact False.elim (disjoint_left.mp hdE ha (hab.symm ▸ hb))
    · rintro x ⟨hx₁, hx₂⟩
      exact ⟨G₁.V_subset_U hx₁, G₂.V_subset_U hx₂⟩

/-- The discarded side of Reduction 2 meets the retained drawing
and the surface boundary only at its specified initial vertex. -/
theorem discarded_side_meets_retained_and_boundary_only_at_initial
    {k : ℕ} {G G' G₂ : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hG' : IsCylinderSection5Drawing k G') (i : Fin k)
    (hsep : IsGraphSeparation G.toGraph G'.toGraph G₂.toGraph)
    (hoverlap : G'.V ∩ G₂.V ⊆ {cylinderM1Point k i}) :
    G'.U ∩ G₂.U ⊆ {cylinderM1Point k i} ∧
      G₂.U ∩ bd ClosedCylinder ⊆ {cylinderM1Point k i} := by
  have hsets := point_sets_of_graph_separation hsep
  refine ⟨hsets.2 ▸ hoverlap, ?_⟩
  rintro x ⟨hx₂, hxbd⟩
  have h₂ : G₂.IsSubdrawing G := ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono⟩
  have hxGV : x ∈ G.V := hG.2.1 ⟨hxbd, h₂.U_subset hx₂⟩
  have hxM : x ∈ cylinderM1 k ∪ cylinderM2 k := hG.2.2 ▸ ⟨hxGV, hxbd⟩
  have hxG'V : x ∈ G'.V := (hG'.2.2.symm ▸ hxM).1
  exact hoverlap ⟨hxG'V, vertex_mem_of_mem_subdrawing_point_set h₂ hx₂ hxGV⟩

end GraphMinor.GM06
