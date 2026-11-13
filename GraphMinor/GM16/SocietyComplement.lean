module

public import GraphMinor.GM16.Defs
import GraphMinor.GM09.Basic

/-!
# Complements of societies in a segregation

The proof of XVI (1.3), page 51, uses the complementary subgraph
of each society. Its separator is exactly the society boundary.
Every other society lies in this complement. These facts allow
locations inside societies to be assembled into a location of the graph.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- The complementary graph `C(A, Ω)` in the proof of XVI (1.3),
page 51. Its vertices are those outside `A`, together with its boundary,
and its edges are the edges outside `A`. -/
def societyComplement {α : Type u} {β : Type v} (G : Graph α β)
    (A : Society α β) : Graph α β :=
  (G.induce ((V(G) \ V(A.G)) ∪ A.Ω.bar)).restrict (E(G) \ E(A.G))

/-- The complement used on page 51 of XVI separates a society from
the rest of the graph, with precisely its boundary as separator. -/
theorem societyComplement_isSeparation {α : Type u} {β : Type v}
    {G₀ : Graph α β} {S_seg : Set (Society α β)} (hSeg : IsGraphSegregation G₀ S_seg)
    {A : Society α β} (hA : A ∈ S_seg) :
    IsGraphSeparation G₀ A.G (societyComplement G₀ A) ∧
      V(A.G) ∩ V(societyComplement G₀ A) = A.Ω.bar := by
  have hA_le : A.G ≤ G₀ := hSeg.le A hA
  let V_B := (V(G₀) \ V(A.G)) ∪ A.Ω.bar
  let E_B := E(G₀) \ E(A.G)
  let B := (G₀.induce V_B).restrict E_B
  have hVB_sub : V_B ⊆ V(G₀) := by
    rintro v (⟨hvG₀, _⟩ | hv_bar)
    · exact hvG₀
    · exact hA_le.vertexSet_mono (A.bar_subset hv_bar)
  have hB_le : B ≤ G₀ := restrict_le.trans (G₀.induce_le hVB_sub)
  have hVB_eq : V(B) = V_B := by simp [B]
  have hEB_eq : E(B) = E_B := by
    ext e
    simp only [B, edgeSet_restrict, mem_inter_iff, edgeSet_induce]
    refine ⟨fun h => h.2, fun ⟨heG₀, he_not_A⟩ => ⟨?_, ⟨heG₀, he_not_A⟩⟩⟩
    have he_union : e ∈ E(subgraphSUnion G₀ ((fun S' : Society α β => S'.G) '' S_seg)) := by
      rw [hSeg.union_eq]
      exact heG₀
    rw [edgeSet_subgraphSUnion (by rintro _ ⟨S', hS', rfl⟩; exact hSeg.le S' hS')] at he_union
    obtain ⟨_, ⟨A', hA', rfl⟩, heA'⟩ := mem_iUnion₂.mp he_union
    have hAA'_ne : A ≠ A' := fun hEq => he_not_A (hEq ▸ heA')
    obtain ⟨x, y, hxy_A'⟩ := A'.G.exists_isLink_of_mem_edgeSet heA'
    have hxy_G₀ : G₀.IsLink e x y := hxy_A'.mono (hSeg.le A' hA')
    have hmem_VB : ∀ z ∈ V(A'.G), z ∈ V_B := by
      intro z hzA'
      by_cases hzA : z ∈ V(A.G)
      · exact Or.inr (hSeg.vertex_inter_subset A hA A' hA' hAA'_ne ⟨hzA, hzA'⟩).1
      · exact Or.inl ⟨(hSeg.le A' hA').vertexSet_mono hzA', hzA⟩
    exact ⟨x, y, hxy_G₀, hmem_VB x hxy_A'.left_mem, hmem_VB y hxy_A'.right_mem⟩
  change IsGraphSeparation G₀ A.G B ∧ V(A.G) ∩ V(B) = A.Ω.bar
  refine ⟨⟨hA_le, hB_le, ?_, ?_, ?_⟩, ?_⟩
  · ext v
    rw [mem_union, hVB_eq]
    refine ⟨by rintro (hvA | hvB); exact hA_le.vertexSet_mono hvA; exact hVB_sub hvB, fun hvG₀ => ?_⟩
    by_cases hvA : v ∈ V(A.G)
    · exact Or.inl hvA
    · exact Or.inr (Or.inl ⟨hvG₀, hvA⟩)
  · ext e
    rw [mem_union, hEB_eq]
    refine ⟨by rintro (heA | ⟨heG₀, _⟩); exact hA_le.edgeSet_mono heA; exact heG₀, fun heG₀ => ?_⟩
    by_cases heA : e ∈ E(A.G)
    · exact Or.inl heA
    · exact Or.inr ⟨heG₀, heA⟩
  · rw [hEB_eq]
    exact disjoint_sdiff_self_right
  · ext v
    rw [mem_inter_iff, hVB_eq]
    constructor
    · rintro ⟨hvA, ⟨_, hv_not_A⟩ | hv_bar⟩
      · exact (hv_not_A hvA).elim
      · exact hv_bar
    · intro hv_bar
      exact ⟨A.bar_subset hv_bar, Or.inr hv_bar⟩



/-- Every other society is contained in the complementary side of a
society separation. This is the disjointness step in the location assembly
on page 51 of XVI. -/
theorem le_societyComplement_of_ne {α : Type u} {β : Type v}
    {G : Graph α β} {𝒮 : Set (Society α β)} (hSeg : IsGraphSegregation G 𝒮)
    {A B : Society α β} (hA : A ∈ 𝒮) (hB : B ∈ 𝒮) (hne : A ≠ B) :
    B.G ≤ societyComplement G A := by
  have hBG := hSeg.le B hB
  refine ⟨?_, ?_⟩
  · intro x hxB
    change x ∈ (V(G) \ V(A.G)) ∪ A.Ω.bar
    by_cases hxA : x ∈ V(A.G)
    · exact Or.inr ((hSeg.vertex_inter_subset A hA B hB hne ⟨hxA, hxB⟩).1)
    · exact Or.inl ⟨hBG.vertexSet_mono hxB, hxA⟩
  · intro e x y hxy
    have hxyG := hxy.mono hBG
    have he_not : e ∉ E(A.G) := fun he =>
      disjoint_left.mp (hSeg.edge_disjoint A hA B hB hne) he hxy.edge_mem
    have hxy_vertices : ∀ z ∈ V(B.G), z ∈ (V(G) \ V(A.G)) ∪ A.Ω.bar := by
      intro z hz
      by_cases hzA : z ∈ V(A.G)
      · exact Or.inr ((hSeg.vertex_inter_subset A hA B hB hne ⟨hzA, hz⟩).1)
      · exact Or.inl ⟨hBG.vertexSet_mono hz, hzA⟩
    exact ⟨⟨hxyG.edge_mem, he_not⟩, hxyG,
      hxy_vertices x hxy.left_mem, hxy_vertices y hxy.right_mem⟩

end GraphMinor.GM16
