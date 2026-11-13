module

public import GraphMinor.Surface.Dissection
import GraphMinor.Surface.SurfacePull

/-!
# Dissections on components

A face cannot meet both sides of a partition into open and closed sets.
Pull back the faces on one side along its inclusion. This gives the
component dissections used in the Euler calculation of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

/-- A dissection restricts to an embedded compact space whose image is
open and closed. This is the restriction to cut components in the proof
of Graph Minors VIII (18.2), page 286. -/
theorem isDissection_pull_clopen {S T : Type} [TopologicalSpace S]
    [TopologicalSpace T] [T2Space T] [CompactSpace S] [Nonempty S]
    {j : S → T} (hj : IsClosedEmbedding j) (hr : IsClopen (range j))
    {V : Set T} {E 𝓕 : Set (Set T)} (hd : IsDissection V E 𝓕) :
    IsDissection (j ⁻¹' V)
      ((fun e => j ⁻¹' e) '' {e ∈ E | e ⊆ range j})
      ((fun Φ => j ⁻¹' Φ) '' {Φ ∈ 𝓕 | Φ ⊆ range j}) := by
  have : T2Space S := hj.isEmbedding.t2Space
  have hside : ∀ Φ ∈ 𝓕, Φ ⊆ range j ∨ Φ ⊆ (range j)ᶜ := by
    intro Φ hΦ
    have hD := hd.disc Φ hΦ
    have hsplit := IsPreconnected.subset_or_subset hr.2 hr.1.isOpen_compl
      disjoint_compl_right (by simp : discInt Φ ⊆ range j ∪ (range j)ᶜ)
      hD.isPreconnected_discInt
    rcases hsplit with h | h
    · exact Or.inl (hD.subset_closure_discInt.trans (closure_minimal h hr.1))
    · exact Or.inr (hD.subset_closure_discInt.trans (closure_minimal h hr.2.isClosed_compl))
  have hpb : ∀ Φ ∈ {Φ ∈ 𝓕 | Φ ⊆ range j}, IsClosedDisc (j ⁻¹' Φ) ∧ discBd (j ⁻¹' Φ) = j ⁻¹' discBd Φ :=
    fun Φ hΦ => isClosedDisc_preimage hj (hd.disc Φ hΦ.1) hΦ.2
  have hint : ∀ Φ ∈ {Φ ∈ 𝓕 | Φ ⊆ range j}, ∀ y ∈ discInt (j ⁻¹' Φ), j y ∈ discInt Φ := by
    intro Φ hΦ y hy
    refine ⟨hy.1, fun h => hy.2 ?_⟩
    rw [(hpb Φ hΦ).2]
    exact h
  refine ⟨hd.graph.pull hj.isEmbedding, (hd.fin.subset (sep_subset _ _)).image _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨Φ, hΦ, rfl⟩
    exact (hpb Φ hΦ).1
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨Φ, hΦ, hxΦ⟩ := hd.cover.symm.subset (mem_univ (j x))
    have hsub : Φ ⊆ range j := by
      rcases hside Φ hΦ with h | h
      · exact h
      · exact False.elim (h hxΦ ⟨x, rfl⟩)
    exact ⟨_, ⟨Φ, ⟨hΦ, hsub⟩, rfl⟩, hxΦ⟩
  · rintro _ ⟨Φ, hΦ, rfl⟩
    rw [(hpb Φ hΦ).2]
    intro y hy
    have hne : Nonempty T := ⟨j y⟩
    have hdO := (hd.disc Φ hΦ.1).isOArc_discBd
    obtain ⟨e, he, hye⟩ := hd.graph.subset_edges hdO (hd.bd Φ hΦ.1) hy
    exact ⟨_, ⟨e, ⟨he.1, he.2.trans ((discBd_subset Φ).trans hΦ.2)⟩, rfl⟩, hye⟩
  · rintro _ ⟨Φ, hΦ, rfl⟩
    rw [Set.disjoint_left]
    rintro y hy ⟨_, ⟨e, he, rfl⟩, hye⟩
    exact Set.disjoint_left.mp (hd.int Φ hΦ.1) (hint Φ hΦ y hy) ⟨e, he.1, hye⟩
  · rintro _ ⟨Φ, hΦ, rfl⟩ _ ⟨Φ', hΦ', rfl⟩ hne
    have hne' : Φ ≠ Φ' := fun h => hne (by rw [h])
    rw [Set.disjoint_left]
    intro y hy hy'
    exact Set.disjoint_left.mp (hd.disj Φ hΦ.1 Φ' hΦ'.1 hne') (hint Φ hΦ y hy) hy'
  · intro x hx
    have hx' : j x ∉ V := hx
    refine (encard_le_encard ?_).trans ((encard_image_le (fun Φ => j ⁻¹' Φ) _).trans (hd.count (j x) hx'))
    rintro _ ⟨⟨Φ, hΦ, rfl⟩, hxΦ⟩
    exact ⟨Φ, ⟨hΦ.1, hxΦ⟩, rfl⟩

end GraphMinor.GM08
