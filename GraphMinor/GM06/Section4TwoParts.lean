module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section3Basic

/-!
# Separating two internally joined vertex sets

The proof of VI (4.2), pages 126–127, partitions G′ into its two cuff
parts. If each part is joined in the graph, any walk between the parts
would join the whole graph. Thus a nonempty part is exactly the vertex
set of a component whenever the graph is disconnected.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u v

/-- If two sets cover the vertices of a disconnected graph and each
set is internally joined, every nonempty set is a whole component. -/
theorem exists_component_of_two_joined_parts
    {α : Type u} {β : Type v} {G : Graph α β} {X Y : Set α}
    (hcover : Graph.vertexSet G = X ∪ Y) (hX : X.Nonempty)
    (hjoinX : ∀ a ∈ X, ∀ b ∈ X, Nonempty (GraphWalk G a b))
    (hjoinY : ∀ a ∈ Y, ∀ b ∈ Y, Nonempty (GraphWalk G a b))
    (hdisconn : ¬ IsGraphConnected G) :
    ∃ C : Graph α β, IsGraphComponent C G ∧ Graph.vertexSet C = X := by
  obtain ⟨a, ha⟩ := hX
  have haG : a ∈ Graph.vertexSet G := hcover.symm ▸ Or.inl ha
  let C := compOf G a
  have hC : IsGraphComponent C G := isGraphComponent_compOf haG
  have hXC : X ⊆ Graph.vertexSet C := by
    intro b hb
    exact ⟨hcover.symm ▸ Or.inl hb, hjoinX a ha b hb⟩
  refine ⟨C, hC, Subset.antisymm ?_ hXC⟩
  intro z hz
  by_contra hzX
  have hzY : z ∈ Y := (hcover ▸ hC.1.vertexSet_mono hz).resolve_left hzX
  have haz : Nonempty (GraphWalk G a z) := hz.2
  have hall : ∀ b ∈ Graph.vertexSet G, Nonempty (GraphWalk G a b) := by
    intro b hb
    rcases hcover ▸ hb with hbX | hbY
    · exact hjoinX a ha b hbX
    · obtain ⟨P⟩ := haz
      obtain ⟨Q⟩ := hjoinY z hzY b hbY
      exact ⟨P.append Q⟩
  apply hdisconn
  refine ⟨⟨a, haG⟩, ?_⟩
  intro b hb c hc
  obtain ⟨P⟩ := hall b hb
  obtain ⟨Q⟩ := hall c hc
  exact ⟨P.reverse.append Q⟩

end GraphMinor.GM06
