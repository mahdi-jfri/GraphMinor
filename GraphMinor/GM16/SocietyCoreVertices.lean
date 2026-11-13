module

public import GraphMinor.GM16.SocietyLocationCores
import GraphMinor.GM09.Basic

/-!
# The vertices where ring pieces attach

In the torso assembly of XVI (1.3), page 51, the global core is the
union of the local cores. Every society boundary remains. A local core
meets the set of all society boundary vertices precisely in its own
boundary. These are the attachment vertices of its ring to the drawn
graph.
-/

public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- A local location retains the society boundary because each right
side contains it, as required in the construction on page 51 of XVI. -/
theorem society_boundary_subset_local_core {α : Type u} {β : Type v}
    {A : Society α β} {ℒ : Set (Graph α β × Graph α β)}
    (hBoundary : ∀ p ∈ ℒ, A.Ω.bar ⊆ V(p.2)) :
    A.Ω.bar ⊆ V(graphLocationCore A.G ℒ) := by
  intro x hx
  exact ⟨A.bar_subset hx, fun p hp => hBoundary p hp hx⟩

/-- The global location core is the union of the society cores. -/
theorem assembled_core_vertex_cover {α : Type u} {β : Type v}
    {G : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2)) :
    V(graphLocationCore G (assembledSocietyLocation G 𝒮 ℒ)) =
      ⋃ A ∈ 𝒮, V(graphLocationCore A.G (ℒ A)) := by
  ext x
  constructor
  · intro hx
    have hxG := (graphLocationCore_le G _).vertexSet_mono hx
    have hxUnion : x ∈ V(subgraphSUnion G ((fun A : Society α β => A.G) '' 𝒮)) :=
      hSeg.union_eq.symm ▸ hxG
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA⟩ := mem_iUnion₂.mp hxUnion
    exact mem_iUnion₂.mpr ⟨A, hA, (mem_assembled_core_iff hSeg hBoundary hA hxA).mp hx⟩
  · intro hx
    obtain ⟨A, hA, hxA⟩ := mem_iUnion₂.mp hx
    exact (mem_assembled_core_iff hSeg hBoundary hA
      ((graphLocationCore_le A.G _).vertexSet_mono hxA)).mpr hxA

/-- A society core meets the union of the society boundary sets
precisely in its own boundary. -/
theorem local_core_inter_segregationVertices {α : Type u} {β : Type v}
    {G : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2))
    {A : Society α β} (hA : A ∈ 𝒮) :
    V(graphLocationCore A.G (ℒ A)) ∩ segregationVertices 𝒮 = A.Ω.bar := by
  ext x
  constructor
  · rintro ⟨hxCore, hxSeg⟩
    obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp hxSeg
    by_cases hAB : A = B
    · exact hAB.symm ▸ hxB
    · exact (hSeg.vertex_inter_subset A hA B hB hAB
        ⟨(graphLocationCore_le A.G _).vertexSet_mono hxCore, B.bar_subset hxB⟩).1
  · intro hx
    exact ⟨society_boundary_subset_local_core (hBoundary A hA) hx,
      mem_iUnion₂.mpr ⟨A, hA, hx⟩⟩

/-- Every society boundary vertex remains in the assembled core. -/
theorem segregationVertices_subset_assembled_core {α : Type u} {β : Type v}
    {G : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2)) :
    segregationVertices 𝒮 ⊆ V(graphLocationCore G (assembledSocietyLocation G 𝒮 ℒ)) := by
  rw [assembled_core_vertex_cover hSeg hBoundary]
  intro x hx
  obtain ⟨A, hA, hxA⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion₂.mpr ⟨A, hA, society_boundary_subset_local_core (hBoundary A hA) hxA⟩

end GraphMinor.GM16
