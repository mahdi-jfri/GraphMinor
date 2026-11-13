module

public import GraphMinor.Surface.SurfaceGraph

/-!
# Joining graph representations of schism pieces

Two finite graphs whose common points are vertices of both combine into
a finite graph. No edge gains a new interior vertex, and edges from
different graphs meet only in the common vertex set. This assembles the
loop pieces of the branched schisms before cutting in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Join graph representations along common vertices. This is the local
graph construction used for the branched types in VIII (18.2), page 286. -/
theorem isGraph_union_of_inter_subset_vertices {S : Type w} [TopologicalSpace S]
    {V W : Set S} {E D : Set (Set S)} (hg : IsGraph V E) (hh : IsGraph W D)
    (hinter : gr V E ∩ gr W D ⊆ V ∩ W) : IsGraph (V ∪ W) (E ∪ D) := by
  have hedge : ∀ {V W : Set S} {E D : Set (Set S)}, IsGraph V E →
      gr V E ∩ gr W D ⊆ V ∩ W → ∀ e ∈ E,
      ∃ u v, u ≠ v ∧ IsLineWithEnds e u v ∧ e ∩ (V ∪ W) = {u, v} := by
    intro V W E D h hmeet e he
    obtain ⟨u, v, huv, hl, hi⟩ := h.edge e he
    refine ⟨u, v, huv, hl, ?_⟩
    apply Subset.antisymm
    · rintro x ⟨hxe, hxV | hxW⟩
      · exact hi.subset ⟨hxe, hxV⟩
      · have hxV := (hmeet ⟨Or.inr ⟨e, he, hxe⟩, Or.inl hxW⟩).1
        exact hi.subset ⟨hxe, hxV⟩
    · intro x hx
      obtain ⟨hxe, hxV⟩ := hi.symm.subset hx
      exact ⟨hxe, Or.inl hxV⟩
  have hinter' : gr W D ∩ gr V E ⊆ W ∩ V := fun x hx =>
    ⟨(hinter ⟨hx.2, hx.1⟩).2, (hinter ⟨hx.2, hx.1⟩).1⟩
  refine ⟨hg.fin.union hh.fin, hg.fine.union hh.fine, ?_, ?_⟩
  · intro e he
    rcases he with he | he
    · exact hedge hg hinter e he
    · simpa only [union_comm V W] using hedge hh hinter' e he
  · intro e he f hf hne x hx
    rcases he with he | he <;> rcases hf with hf | hf
    · exact Or.inl (hg.disj e he f hf hne hx)
    · exact Or.inl (hinter ⟨Or.inr ⟨e, he, hx.1⟩, Or.inr ⟨f, hf, hx.2⟩⟩).1
    · exact Or.inr (hinter' ⟨Or.inr ⟨e, he, hx.1⟩, Or.inr ⟨f, hf, hx.2⟩⟩).1
    · exact Or.inr (hh.disj e he f hf hne hx)

end GraphMinor.GM08
