module

public import GraphMinor.Compute.Case3StepsRoutedMember
public import GraphMinor.Compute.Algorithm99Relabel

/-!
# Ordered compact numbering of one division member

Step 6 of XIII (9.9), p. 105, applies (7.2) to a member as a graph on its
own vertex set. Its vertices are numbered in increasing order. Every positive
routed pair already has both ends in that set, so deleting the complement
loses no edge before the order-preserving renumbering.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The selected member on consecutive labels, ordered by its original vertices. -/
noncomputable def case3CompactMember (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z) :
    MultiDigraph (case3SelectedMember x Z i).verts.card :=
  (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).induce
    ((case3SelectedMember x Z i).verts.orderEmbOfFin rfl)

/-- Each positive routed pair has both ends in the selected member's vertex set. -/
theorem case3RoutedMember_edge_ends (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (i : Case3SelectedGroup x Z) (u v : Fin x.n)
    (hp : 0 < (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).edgeMult u v) :
    u ∈ (case3SelectedMember x Z i).verts ∧ v ∈ (case3SelectedMember x Z i).verts := by
  classical
  have hown : case3PairOwner x Z u v = case3RawIndexLabel x i.1 ∧ 0 < D.edgeMult u v := by
    change 0 < (if case3PairOwner x Z u v = case3RawIndexLabel x i.1 then D.edgeMult u v else 0) at hp
    split_ifs at hp with h
    · exact ⟨h, hp⟩
    · exact False.elim (Nat.not_lt_zero _ hp)
  have hvalid : u = v ∨ x.G.Adj u v := by
    by_cases he : u = v
    · exact Or.inl he
    · right
      rw [← hG, MultiDigraph.toSimpleGraph_adj]
      exact ⟨he, Or.inl hown.2⟩
  rcases (case3PairOwner_selection_iff x Z hdiv u v hvalid i).mpr hown.1 with hadj | ⟨he, _, hu⟩
  · exact (case3SelectedMember x Z i).adj_verts _ _ hadj
  · exact ⟨hu, he ▸ hu⟩

/-- Deleting vertices outside a routed member removes no positive pair. -/
theorem case3RoutedMember_delete_compl (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (i : Case3SelectedGroup x Z) :
    (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).deleteVertices
      (case3SelectedMember x Z i).vertsᶜ = case3RoutedMember x D Z (case3RawIndexLabel x i.1) := by
  classical
  ext u v
  rw [MultiDigraph.deleteVertices_edgeMult]
  split_ifs with hin
  · rfl
  · have hz : (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).edgeMult u v = 0 := by
      by_contra h
      have he := case3RoutedMember_edge_ends x D hG Z hdiv i u v (Nat.pos_of_ne_zero h)
      apply hin
      simpa only [Finset.mem_compl, not_not] using he
    exact hz.symm

/-- The existing compact-deletion program writes exactly the ordered member encoding. -/
theorem case3CompactMember_enc_eq (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z) :
    ((case3RoutedMember x D Z (case3RawIndexLabel x i.1)).deleteVerticesCompact
      (case3SelectedMember x Z i).vertsᶜ).enc = (case3CompactMember x D Z i).enc := by
  unfold MultiDigraph.deleteVerticesCompact compactEmb case3CompactMember
  exact congrArg (fun S : Finset (Fin x.n) =>
    ((case3RoutedMember x D Z (case3RawIndexLabel x i.1)).induce (S.orderEmbOfFin rfl)).enc)
    (compl_compl (case3SelectedMember x Z i).verts)

end GraphMinor.Compute
