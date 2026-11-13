module

public import GraphMinor.GM10.Section4Minors

/-!
# Expanding the edge labels of a branch-decomposition

The induction in Graph Minors X, (4.2)(iii), page 165, restores edges
removed by a local reduction. We give a bound for this restoration when
the old edges partition the new edges into groups. Cuts between groups
have no larger boundary, and cuts within one group have bounded boundary.
The proof uses the tree-labelling duality from Section 3 to refine the
labels to individual edges.
-/

public section

namespace GraphMinor.GM10

open Hypergraph

universe u v u' v'

/-- Restoring groups of edges preserves a branch-width bound if cuts
between groups do not increase their boundary and every cut within one
group has boundary at most the bound. -/
theorem branchWidth_le_of_edge_partition
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Hypergraph α β} {H : Hypergraph α' β'} {k : ℕ}
    (hγG : 1 ≤ maxEdgeSize G) (hγH : 1 ≤ maxEdgeSize H)
    (hkG : maxEdgeSize G ≤ k) (hkH : maxEdgeSize H ≤ k)
    (f : β → β') (hf : Set.MapsTo f G.edgeSet H.edgeSet)
    (hcut : ∀ X ⊆ H.edgeSet,
      (branchEdgeBoundary G (G.edgeSet ∩ f ⁻¹' X)).ncard ≤
        (branchEdgeBoundary H X).ncard)
    (hfiber : ∀ e ∈ H.edgeSet, ∀ X ⊆ G.edgeSet ∩ f ⁻¹' {e},
      (branchEdgeBoundary G X).ncard ≤ k)
    (hw : branchWidth H ≤ k) : branchWidth G ≤ k := by
  classical
  by_contra hnot
  have htG := (theorem_4_3_claim_3 hγG hkG).2 (Nat.lt_of_not_ge hnot)
  obtain ⟨ℬ, hbias, hsing⟩ := (theorem_4_3_claim_1 hγG hkG).2 htG
  let Φ : Set β' → Set β := fun X ↦ G.edgeSet ∩ f ⁻¹' X
  have hΦ_compl : ∀ X ⊆ H.edgeSet, Φ (H.edgeSet \ X) = G.edgeSet \ Φ X := by
    intro X _
    ext e
    simp only [Φ, Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff]
    exact ⟨fun ⟨he, _, hn⟩ ↦ ⟨he, fun h ↦ hn h.2⟩,
      fun ⟨he, hn⟩ ↦ ⟨he, hf he, fun hx ↦ hn ⟨he, hx⟩⟩⟩
  have heffG : ∀ X, IsEfficient H.edgeSet (edgeConnFunc H k) X →
      IsEfficient G.edgeSet (edgeConnFunc G k) (Φ X) := by
    intro X hX
    refine ⟨Set.inter_subset_left, ?_⟩
    have hle := hcut X hX.1
    have hkX := hX.2
    dsimp [edgeConnFunc, kappa0] at hkX ⊢
    change ((branchEdgeBoundary G (Φ X)).ncard : ℤ) - k ≤ 0
    dsimp [Φ]
    omega
  have hfiber_mem : ∀ e ∈ H.edgeSet, Φ {e} ∈ ℬ := by
    intro e he
    have hfinite : (Φ {e}).Finite := G.edgeSet_finite.subset Set.inter_subset_left
    have hsubset_mem : ∀ X : Set β, X.Finite → X ⊆ Φ {e} → X ∈ ℬ := by
      intro X hX
      refine Set.Finite.induction_on X hX (fun _ ↦ empty_mem_of_isBias_edgeConnFunc hbias) ?_
      intro a s _ _ ih has
      have haG : a ∈ G.edgeSet := (has (Set.mem_insert a s)).1
      have hs : s ⊆ Φ {e} := (Set.subset_insert a s).trans has
      have hu : IsEfficient G.edgeSet (edgeConnFunc G k) ({a} ∪ s) := by
        refine ⟨?_, ?_⟩
        · rw [Set.singleton_union]
          exact has.trans Set.inter_subset_left
        · have hb := hfiber e he (insert a s) has
          rw [Set.singleton_union]
          dsimp [edgeConnFunc, kappa0]
          omega
      simpa only [Set.singleton_union] using
        union_mem_of_isBias_edgeConnFunc hbias (hsing ⟨a, haG, rfl⟩) (ih hs) hu
    exact hsubset_mem _ hfinite Set.Subset.rfl
  let ℬH : Set (Set β') := {X | IsEfficient H.edgeSet (edgeConnFunc H k) X ∧ Φ X ∈ ℬ}
  have hbH : BiasExtends H.edgeSet (edgeConnFunc H k) (singletonEdges H) ℬH := by
    refine ⟨⟨fun _ h ↦ h.1, ?_, ?_⟩, ?_⟩
    · intro X hX
      rcases hbias.mem_or_compl_mem (heffG X hX) with h | h
      · exact Or.inl ⟨hX, h⟩
      · right
        refine ⟨⟨Set.sdiff_subset, ?_⟩, ?_⟩
        · rw [← (isConnectivityFunction_edgeConnFunc H k).compl_eq hX.1]
          exact hX.2
        · rw [hΦ_compl X hX.1]
          exact h
    · intro X Y Z hX hY hZ hU
      apply hbias.union_ne hX.2 hY.2 hZ.2
      ext e
      simp only [Set.mem_union, Φ, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ((h | h) | h) <;> exact h.1
      · intro he
        have hm : f e ∈ X ∪ Y ∪ Z := hU.symm ▸ hf he
        rcases hm with (hx | hy) | hz
        · exact Or.inl (Or.inl ⟨he, hx⟩)
        · exact Or.inl (Or.inr ⟨he, hy⟩)
        · exact Or.inr ⟨he, hz⟩
    · rintro _ ⟨e, he, rfl⟩
      exact ⟨singletonEdges_isEfficient hkH _ ⟨e, he, rfl⟩, hfiber_mem e he⟩
  have htH := (theorem_4_3_claim_1 hγH hkH).1 ⟨ℬH, hbH⟩
  exact (Nat.not_lt_of_ge hw) ((theorem_4_3_claim_3 hγH hkH).1 htH)

private theorem not_mem_boundary_of_unique_edge
    {α : Type u} {β : Type v} {G : Hypergraph α β} {d : β} {x : α} {X : Set β}
    (honly : ∀ a, G.Inc a x → a = d) : x ∉ branchEdgeBoundary G X := by
  rintro ⟨_, ⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
  obtain rfl := honly a hax
  obtain rfl := honly b hbx
  exact hb.2 ha

/-- Restoring an edge preserves a width bound if each of its ends is
also an end of a surviving edge or is incident with no other edge.
This includes pendant edges, isolated edges, parallel edges, and loops. -/
theorem branchWidth_le_of_delete_edge_with_private_ends
    {α : Type u} {β : Type v} {G : Hypergraph α β} {d e : β} {k : ℕ}
    (he : e ∈ G.edgeSet) (hed : e ≠ d)
    (hends : ∀ x, G.Inc d x → G.Inc e x ∨ ∀ a, G.Inc a x → a = d)
    (hγG : 1 ≤ maxEdgeSize G) (hγH : 1 ≤ maxEdgeSize (G.deleteEdges {d}))
    (hk : maxEdgeSize G ≤ k) (hw : branchWidth (G.deleteEdges {d}) ≤ k) :
    branchWidth G ≤ k := by
  classical
  let H := G.deleteEdges {d}
  let f : β → β := fun a ↦ if a = d then e else a
  have hf_ne : ∀ a, f a ≠ d := by
    intro a
    dsimp [f]
    split_ifs with ha
    · exact hed
    · exact ha
  have hf : Set.MapsTo f G.edgeSet H.edgeSet := by
    intro a ha
    refine ⟨?_, hf_ne a⟩
    dsimp [f]
    split_ifs <;> assumption
  have hinc : ∀ X x, x ∈ branchEdgeBoundary G X →
      ∀ a, G.Inc a x → H.Inc (f a) x := by
    intro X x hxBound a hx
    refine ⟨?_, hf_ne a⟩
    dsimp [f]
    split_ifs with ha
    · rcases hends x (ha ▸ hx) with hxe | hprivate
      · exact hxe
      · exact (not_mem_boundary_of_unique_edge hprivate hxBound).elim
    · exact hx
  have hkH : maxEdgeSize H ≤ k := by
    apply maxEdgeSize_le_iff.2
    intro a ha
    have heq : H.ends a = G.ends a := by
      ext x
      exact ⟨And.left, fun hx ↦ ⟨hx, ha.2⟩⟩
    change (H.ends a).ncard ≤ k
    rw [heq]
    exact (edgeSize_le_maxEdgeSize ha.1).trans hk
  apply branchWidth_le_of_edge_partition hγG hγH hk hkH f hf ?_ ?_ hw
  · intro X hX
    apply Set.ncard_le_ncard _ (branchEdgeBoundary_finite H X)
    intro x hxBound
    have hincBound := hinc _ x hxBound
    obtain ⟨hx, ⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩ := hxBound
    refine ⟨hx, ⟨f a, ha.2, hincBound a hax⟩, f b, ?_, hincBound b hbx⟩
    refine ⟨hf hb.1, ?_⟩
    intro hfb
    exact hb.2 ⟨hb.1, hfb⟩
  · intro z hz X hX
    have hsub : branchEdgeBoundary G X ⊆ G.ends z := by
      intro x hxBound
      have hincBound := hinc X x hxBound
      obtain ⟨_, ⟨a, ha, hax⟩, _⟩ := hxBound
      have hfa : f a = z := (hX ha).2
      have hx : G.Inc (f a) x := (hincBound a hax).1
      exact hfa ▸ hx
    exact (Set.ncard_le_ncard hsub (ends_finite G z)).trans
      ((edgeSize_le_maxEdgeSize hz.1).trans hk)

/-- Restoring an edge whose ends are contained in the ends of a surviving
edge preserves any branch-width bound at least the maximum edge size. -/
theorem branchWidth_le_of_delete_edge_with_ends_subset
    {α : Type u} {β : Type v} {G : Hypergraph α β} {d e : β} {k : ℕ}
    (he : e ∈ G.edgeSet) (hed : e ≠ d) (hends : G.ends d ⊆ G.ends e)
    (hγG : 1 ≤ maxEdgeSize G) (hγH : 1 ≤ maxEdgeSize (G.deleteEdges {d}))
    (hk : maxEdgeSize G ≤ k) (hw : branchWidth (G.deleteEdges {d}) ≤ k) :
    branchWidth G ≤ k :=
  branchWidth_le_of_delete_edge_with_private_ends he hed
    (fun _ hx ↦ Or.inl (hends hx)) hγG hγH hk hw

end GraphMinor.GM10
