module

public import GraphMinor.GM16.SocietyLocations
public import GraphMinor.GM16.LocationCore
import GraphMinor.GM09.Basic

/-!
# The cores of the assembled society locations

In XVI (1.3), page 51, the assembled location retains exactly the
local core within each society. The boundary condition on the local
right sides ensures this at the attachment vertices. Since the local
left sides cover all edges, the assembled core has no edges.
-/

public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- Within a society, the assembled location retains exactly its local
core. The other society locations impose no further restriction there. -/
theorem mem_assembled_core_iff {α : Type u} {β : Type v}
    {G : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2))
    {A : Society α β} (hA : A ∈ 𝒮) {x : α} (hxA : x ∈ V(A.G)) :
    x ∈ V(graphLocationCore G (assembledSocietyLocation G 𝒮 ℒ)) ↔
      x ∈ V(graphLocationCore A.G (ℒ A)) := by
  change (x ∈ V(G) ∧ ∀ p ∈ assembledSocietyLocation G 𝒮 ℒ, x ∈ V(p.2)) ↔
    (x ∈ V(A.G) ∧ ∀ p ∈ ℒ A, x ∈ V(p.2))
  constructor
  · rintro ⟨_, hx⟩
    refine ⟨hxA, fun p hp => ?_⟩
    have hm : extendLocationPair G (societyComplement G A) p ∈
        assembledSocietyLocation G 𝒮 ℒ :=
      mem_iUnion₂.mpr ⟨A, hA, mem_image_of_mem _ hp⟩
    have hxUnion : x ∈ V(p.2) ∪ V(societyComplement G A) := hx _ hm
    rcases hxUnion with hxRight | hxComp
    · exact hxRight
    · have hxBar : x ∈ A.Ω.bar := by
        rw [← (societyComplement_isSeparation hSeg hA).2]
        exact ⟨hxA, hxComp⟩
      exact hBoundary A hA p hp hxBar
  · rintro ⟨_, hx⟩
    refine ⟨(hSeg.le A hA).vertexSet_mono hxA, ?_⟩
    intro p hp
    obtain ⟨B, hB, q, hq, rfl⟩ := mem_iUnion₂.mp hp
    change x ∈ V(q.2) ∪ V(societyComplement G B)
    by_cases hAB : A = B
    · subst B
      exact Or.inl (hx q hq)
    · exact Or.inr ((le_societyComplement_of_ne hSeg hB hA
        (fun heq => hAB heq.symm)).vertexSet_mono hxA)

/-- All edges disappear from the assembled core when the local left
sides cover the edges of each society, as in XVI (1.3), page 51. -/
theorem assembled_core_edgeSet_eq_empty {α : Type u} {β : Type v}
    {G : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hLocal : ∀ A ∈ 𝒮, IsGraphLocation A.G (ℒ A))
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2))
    (hCover : ∀ A ∈ 𝒮, ∀ e ∈ E(A.G), ∃ p ∈ ℒ A, e ∈ E(p.1)) :
    E(graphLocationCore G (assembledSocietyLocation G 𝒮 ℒ)) = ∅ := by
  apply (assembledSocietyLocation_isLocation hSeg hLocal hBoundary).edgeSet_core_eq_empty
  intro e he
  have heUnion : e ∈ E(subgraphSUnion G ((fun A : Society α β => A.G) '' 𝒮)) :=
    hSeg.union_eq.symm ▸ he
  rw [edgeSet_subgraphSUnion (by rintro _ ⟨A, hA, rfl⟩; exact hSeg.le A hA)] at heUnion
  obtain ⟨_, ⟨A, hA, rfl⟩, heA⟩ := mem_iUnion₂.mp heUnion
  obtain ⟨p, hp, hep⟩ := hCover A hA e heA
  exact ⟨extendLocationPair G (societyComplement G A) p,
    mem_iUnion₂.mpr ⟨A, hA, mem_image_of_mem _ hp⟩, hep⟩

end GraphMinor.GM16
