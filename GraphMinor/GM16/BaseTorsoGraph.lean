module

public import GraphMinor.GM16.TorsoEdgePiece
public import GraphMinor.GM16.SmallSocietyLocation
import GraphMinor.GM09.Basic

/-!
# The drawn graph in the torso outgrowth

In XVI (1.3), page 51, retain all society boundary vertices and the
torso edges assigned to small societies. The remaining torso edges
belong to the ring pieces. Each small edge has all its ends in its
society boundary, so inducing on the union of the boundaries keeps it.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- The torso edges assigned to small societies in XVI, page 51. -/
def smallSocietyEdges {α : Type u} {β : Type v}
    (𝒮 : Set (Society α β)) (F : Society α β → Set β) : Set β :=
  {e | ∃ A ∈ 𝒮, A.Ω.bar.ncard ≤ 3 ∧ e ∈ F A}

/-- The graph drawn on the surface in the torso construction of
XVI (1.3), page 51: boundary vertices and small-society edges. -/
def baseTorsoGraph {α : Type u} {β : Type v} (H : Graph α β)
    (𝒮 : Set (Society α β)) (F : Society α β → Set β) : Graph α β :=
  (H.induce (segregationVertices 𝒮)).restrict (smallSocietyEdges 𝒮 F)

/-- The base graph has exactly the attachment vertices. -/
theorem vertexSet_baseTorsoGraph {α : Type u} {β : Type v}
    (H : Graph α β) (𝒮 : Set (Society α β)) (F : Society α β → Set β) :
    V(baseTorsoGraph H 𝒮 F) = segregationVertices 𝒮 := rfl

/-- The small local location has only its society boundary as separator. -/
theorem smallSocietyLocation_separator_subset {α : Type u} {β : Type v}
    {A : Society α β} {p : Graph α β × Graph α β}
    (hp : p ∈ smallSocietyLocation A) : V(p.1) ∩ V(p.2) ⊆ A.Ω.bar := by
  obtain rfl := hp
  exact inter_subset_right

/-- All assigned small-society edges survive in the base graph. -/
theorem edgeSet_baseTorsoGraph {α : Type u} {β : Type v}
    {H : Graph α β} {𝒮 : Set (Society α β)} {F : Society α β → Set β}
    (hF : ∀ A, F A ⊆ E(H))
    (hEnds : ∀ A ∈ 𝒮, A.Ω.bar.ncard ≤ 3 →
      ∀ e ∈ F A, ∀ x, H.Inc e x → x ∈ A.Ω.bar) :
    E(baseTorsoGraph H 𝒮 F) = smallSocietyEdges 𝒮 F := by
  apply edgeSet_induce_restrict_eq_of_ends_subset
  · rintro e ⟨A, _, _, he⟩
    exact hF A he
  · rintro e ⟨A, hA, hsmall, he⟩ x hx
    exact mem_iUnion₂.mpr ⟨A, hA, hEnds A hA hsmall e he x hx⟩

/-- The base graph is a subgraph of the global torso. -/
theorem baseTorsoGraph_le {α : Type u} {β : Type v}
    {H : Graph α β} {𝒮 : Set (Society α β)} {F : Society α β → Set β}
    (hV : segregationVertices 𝒮 ⊆ V(H)) : baseTorsoGraph H 𝒮 F ≤ H :=
  restrict_le.trans (H.induce_le hV)

end GraphMinor.GM16
