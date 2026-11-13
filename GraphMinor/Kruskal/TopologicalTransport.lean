module

public import GraphMinor.Kruskal.FiniteNames
import GraphMinor.Minor.Basic

/-!
# Transporting topological containment

Graph Minors IV defines containment up to graph isomorphism. We construct the
image of a subgraph under an isomorphism, then use it to transfer subdivision
witnesses between different choices of vertex and edge names.
-/

public section

namespace GraphMinor.Kruskal

open Graph Set

/-- An isomorphism carries every subgraph to an isomorphic subgraph of its
codomain. Its vertex and edge maps are restricted to the actual sets of the
subgraph before applying `renameGraph`. -/
theorem exists_iso_subgraph_image {α β α' β' : Type*}
    {G K : Graph α β} {G' : Graph α' β'} (φ : Iso G G') (hKG : K ≤ G) :
    ∃ K' ≤ G', Nonempty (Iso K K') := by
  let vertices : V(K) ↪ α' :=
    ⟨fun x ↦ (φ.vertexEquiv ⟨x, hKG.vertexSet_mono x.property⟩ : α'), by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : V(G) ↦ z.val)
        (φ.vertexEquiv.injective (Subtype.ext hxy)))⟩
  let edges : E(K) ↪ β' :=
    ⟨fun e ↦ (φ.edgeEquiv ⟨e, hKG.edgeSet_mono e.property⟩ : β'), by
      intro e f hef
      exact Subtype.ext (congrArg (fun z : E(G) ↦ z.val)
        (φ.edgeEquiv.injective (Subtype.ext hef)))⟩
  refine ⟨renameGraph K vertices edges, ?_, ⟨renameGraphIso K vertices edges⟩⟩
  constructor
  · rintro x ⟨a, rfl⟩
    exact (φ.vertexEquiv ⟨a, hKG.vertexSet_mono a.property⟩).property
  · rintro e x y ⟨d, a, b, hab, rfl, rfl, rfl⟩
    exact (φ.isLink_iff ⟨d, hKG.edgeSet_mono d.property⟩
      ⟨a, hKG.vertexSet_mono a.property⟩ ⟨b, hKG.vertexSet_mono b.property⟩).1
      (hKG.isLink_mono hab)

/-- Topological containment is preserved when the source is replaced by an
isomorphic graph. The subdivision sequence itself does not change. -/
theorem isTopologicalMinor_iso_source {α β α' β' γ δ : Type*}
    {H : Graph α β} {H' : Graph α' β'} {G : Graph γ δ}
    (φ : Iso H H') (h : GM04.IsTopologicalMinor H' G) :
    GM04.IsTopologicalMinor H G := by
  obtain ⟨H₀, S, ⟨ψ⟩, hsub, K, hKG, hSK⟩ := h
  exact ⟨H₀, S, ⟨φ.trans ψ⟩, hsub, K, hKG, hSK⟩

/-- Topological containment is preserved by an isomorphism of the target.
The terminal subgraph is carried through that isomorphism. -/
theorem isTopologicalMinor_iso_target {α β α' β' γ δ : Type*}
    {H : Graph α β} {G : Graph α' β'} {G' : Graph γ δ}
    (φ : Iso G G') (h : GM04.IsTopologicalMinor H G) :
    GM04.IsTopologicalMinor H G' := by
  obtain ⟨H₀, S, hH₀, hsub, K, hKG, ⟨ψ⟩⟩ := h
  obtain ⟨K', hK'G', ⟨χ⟩⟩ := exists_iso_subgraph_image φ hKG
  exact ⟨H₀, S, hH₀, hsub, K', hK'G', ⟨ψ.trans χ⟩⟩

/-- Enlarging the target preserves a topological minor witness. -/
theorem isTopologicalMinor_mono_target {α β α' β' : Type*}
    {H : Graph α β} {G G' : Graph α' β'}
    (hGG' : G ≤ G') (h : GM04.IsTopologicalMinor H G) :
    GM04.IsTopologicalMinor H G' := by
  obtain ⟨H₀, S, hH₀, hsub, K, hKG, hSK⟩ := h
  exact ⟨H₀, S, hH₀, hsub, K, hKG.trans hGG', hSK⟩

/-- Every finite subgraph is a topological minor, with no edge subdivision. -/
theorem isTopologicalMinor_of_le {α β : Type*} {H G : Graph α β}
    (hHG : H ≤ G) (hV : V(H).Finite) (hE : E(H).Finite) :
    GM04.IsTopologicalMinor H G :=
  isTopologicalMinor_mono_target hHG (isTopologicalMinor_refl H hV hE)

end GraphMinor.Kruskal
