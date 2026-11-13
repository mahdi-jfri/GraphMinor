module

public import GraphMinor.Compute.Case3StepsSelectedVertices
public import GraphMinor.Compute.Case3StepsGroupMask
public import GraphMinor.Compute.Case3StepsLoopOwner

/-!
# Loop owners chosen in member scan order

A vertex is assigned to the first selected member containing it. Division
coverage ensures that the scan finds such a member. Assigning all loops at
a vertex to this same member restores multiplicities without duplicating
edges. This fixes the choice needed in Graph Minors XIII, (9.9), step 5,
p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The test for a containing selected candidate in the contiguous label range. -/
noncomputable def case3GroupContains (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (q : Fin (x.n + (case3InputEdges x).length)) : Prop :=
  let i := (case3GroupLabelEquiv x).symm q
  case3GroupActive x Z i ∧
    u ∈ outsideOfBoundary x Z (case3GroupBoundary x Z i) ∪ case3GroupBoundary x Z i

/-- At a selected group the scan test is exactly member vertex membership. -/
theorem case3GroupContains_selected (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (i : Case3SelectedGroup x Z) :
    case3GroupContains x Z u (case3GroupLabelEquiv x i.1) ↔
      u ∈ (case3SelectedMember x Z i).verts := by
  simp only [case3GroupContains, Equiv.symm_apply_apply, i.2, true_and,
    case3SelectedMember_verts]

/-- Division coverage gives a successful candidate for each vertex. -/
theorem case3GroupContains_exists (x : Alg81Input) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (u : Fin x.n) :
    ∃ q, case3GroupContains x Z u q := by
  obtain ⟨A, ⟨i, rfl⟩, hu⟩ := case3Division_vertex_covered hdiv u
  exact ⟨case3GroupLabelEquiv x i.1, (case3GroupContains_selected x Z u i).mpr hu⟩

/-- The numeric loop-owner label is the first containing selected member. -/
noncomputable def case3OrderedLoopLabel (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) : ℕ := case3FirstIndex (case3GroupContains x Z u)

/-- The loop-owner search succeeds because the division covers every vertex. -/
theorem case3OrderedLoopLabel_lt (x : Alg81Input) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (u : Fin x.n) :
    case3OrderedLoopLabel x Z u < x.n + (case3InputEdges x).length := by
  have hle := case3FirstIndex_le (case3GroupContains x Z u)
  change case3OrderedLoopLabel x Z u ≤ _ at hle
  by_contra h
  have heq : case3OrderedLoopLabel x Z u = x.n + (case3InputEdges x).length := by omega
  obtain ⟨q, hq⟩ := case3GroupContains_exists x Z hdiv u
  exact ((case3FirstIndex_eq_sentinel_iff _).mp heq) q hq

/-- The selected group at the first successful owner label. -/
noncomputable def case3OrderedLoopOwner (x : Alg81Input) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (u : Fin x.n) :
    Case3SelectedGroup x Z :=
  ⟨(case3GroupLabelEquiv x).symm
      ⟨case3OrderedLoopLabel x Z u, case3OrderedLoopLabel_lt x Z hdiv u⟩,
    (case3FirstIndex_spec (case3GroupContains x Z u)
      (case3OrderedLoopLabel_lt x Z hdiv u)).1.1⟩

/-- The first containing member contains the vertex to which its loops belong. -/
theorem case3OrderedLoopOwner_contains (x : Alg81Input) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (u : Fin x.n) :
    u ∈ (case3SelectedMember x Z (case3OrderedLoopOwner x Z hdiv u)).verts :=
  (case3FirstIndex_spec (case3GroupContains x Z u)
    (case3OrderedLoopLabel_lt x Z hdiv u)).1.2

/-- The chosen member has precisely the scan's numeric owner label. -/
theorem case3OrderedLoopOwner_label (x : Alg81Input) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (u : Fin x.n) :
    case3RawIndexLabel x (case3OrderedLoopOwner x Z hdiv u).1 =
      case3OrderedLoopLabel x Z u := by
  rw [← case3GroupLabelEquiv_val]
  exact congrArg Fin.val ((case3GroupLabelEquiv x).apply_symm_apply _)

/-- The member scan order supplies explicit loop-assignment data for the lift. -/
noncomputable def case3OrderedLoopAssignment (x : Alg81Input) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) :
    Case3LoopAssignment x (case3SelectedMembers x Z) where
  member u := ⟨case3SelectedMember x Z (case3OrderedLoopOwner x Z hdiv u),
    ⟨case3OrderedLoopOwner x Z hdiv u, rfl⟩⟩
  contains_vertex := case3OrderedLoopOwner_contains x Z hdiv

end GraphMinor.Compute
