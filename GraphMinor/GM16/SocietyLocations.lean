module

public import GraphMinor.GM16.SocietyComplement
public import GraphMinor.GM16.LocationExtension
import GraphMinor.GM09.Basic

/-!
# Assembling the location in the proof of XVI (1.3)

On page 51 each society supplies a local location, whose right sides
contain its boundary. We extend those right sides by the society
complement and take their union. Within one society the location
condition follows from the local location. Between two societies it
follows because either society lies in the other's complement.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- The union of the extended society locations in XVI, page 51.
For a small society the local location consists of its entire graph
and its boundary graph. For a large one it is the location of (3.2). -/
def assembledSocietyLocation {α : Type u} {β : Type v}
    (G : Graph α β) (𝒮 : Set (Society α β))
    (ℒ : Society α β → Set (Graph α β × Graph α β)) :
    Set (Graph α β × Graph α β) :=
  ⋃ A ∈ 𝒮, extendLocationPair G (societyComplement G A) '' ℒ A

/-- The omitted location verification in XVI, page 51: the local
locations of the societies assemble to a location of the whole graph. -/
theorem assembledSocietyLocation_isLocation {α : Type u} {β : Type v}
    {G : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hLocal : ∀ A ∈ 𝒮, IsGraphLocation A.G (ℒ A))
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2)) :
    IsGraphLocation G (assembledSocietyLocation G 𝒮 ℒ) := by
  have hExt : ∀ A ∈ 𝒮,
      IsGraphLocation G (extendLocationPair G (societyComplement G A) '' ℒ A) := by
    intro A hA
    obtain ⟨hSep, hcut⟩ := societyComplement_isSeparation hSeg hA
    exact (hLocal A hA).extend hSep (fun p hp => hcut ▸ hBoundary A hA p hp)
  refine ⟨hSeg.finite.biUnion (fun A hA => (hExt A hA).finite), ?_, ?_⟩
  · intro p hp
    obtain ⟨A, hA, hpA⟩ := mem_iUnion₂.mp hp
    exact (hExt A hA).isSeparation hpA
  · intro p hp q hq hpq
    obtain ⟨A, hA, hpA⟩ := mem_iUnion₂.mp hp
    obtain ⟨B, hB, hqB⟩ := mem_iUnion₂.mp hq
    by_cases hAB : A = B
    · subst B
      exact (hExt A hA).left_le_right hpA hqB hpq
    · obtain ⟨p₀, hp₀, rfl⟩ := hpA
      obtain ⟨q₀, hq₀, rfl⟩ := hqB
      have hAG := hSeg.le A hA
      have hcomp := (societyComplement_isSeparation hSeg hB).1.2.1
      exact ((hLocal A hA).isSeparation hp₀).1.trans
        ((le_societyComplement_of_ne hSeg hB hA (fun heq => hAB heq.symm)).trans
          (le_subgraphUnion_right
            (((hLocal B hB).isSeparation hq₀).2.1.trans (hSeg.le B hB)) hcomp))

/-- Every separator in the assembled location is the corresponding
local separator. This gives its bound `max(3, 2ρ + 1)` in XVI, page 51. -/
theorem assembledSocietyLocation_separator {α : Type u} {β : Type v}
    {G : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hLocal : ∀ A ∈ 𝒮, IsGraphLocation A.G (ℒ A))
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2))
    {p : Graph α β × Graph α β}
    (hp : p ∈ assembledSocietyLocation G 𝒮 ℒ) :
    ∃ A ∈ 𝒮, ∃ q ∈ ℒ A,
      p.1 = q.1 ∧ V(p.1) ∩ V(p.2) = V(q.1) ∩ V(q.2) := by
  obtain ⟨A, hA, q, hq, rfl⟩ := mem_iUnion₂.mp hp
  refine ⟨A, hA, q, hq, rfl, ?_⟩
  obtain ⟨hSep, hcut⟩ := societyComplement_isSeparation hSeg hA
  exact (extendLocationPair_isSeparation hSep ((hLocal A hA).isSeparation hq)
    (hcut ▸ hBoundary A hA q hq)).2

/-- The assembled left sides cover every vertex when the local left
sides cover every vertex of each society. -/
theorem assembledSocietyLocation_left_vertex_cover {α : Type u} {β : Type v}
    {G : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hCover : ∀ A ∈ 𝒮, ∀ x ∈ V(A.G), ∃ p ∈ ℒ A, x ∈ V(p.1)) :
    ∀ x ∈ V(G), ∃ p ∈ assembledSocietyLocation G 𝒮 ℒ, x ∈ V(p.1) := by
  intro x hx
  have hxUnion : x ∈ V(subgraphSUnion G ((fun A : Society α β => A.G) '' 𝒮)) :=
    hSeg.union_eq.symm ▸ hx
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA⟩ := mem_iUnion₂.mp hxUnion
  obtain ⟨p, hp, hxp⟩ := hCover A hA x hxA
  exact ⟨extendLocationPair G (societyComplement G A) p,
    mem_iUnion₂.mpr ⟨A, hA, mem_image_of_mem _ hp⟩, hxp⟩

end GraphMinor.GM16
