module

public import GraphMinor.Compute.Case3StepsPairOwner

/-!
# Pair routing agrees with the multigraph edge lift

For a positive pair record, its owner label selects exactly the edge
predicate of the restored member: its simple edge belongs to the member,
or it is a loop assigned to that member at a retained vertex. Thus routing
keeps the entire stored parallel class in exactly the member prescribed by
the lift in XIII (9.9), step 5, p. 105.
-/

public section

namespace GraphMinor.Compute

/-- A loop's numeric label identifies exactly its chosen selected group. -/
theorem case3PairOwner_loop_eq_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (u : Fin x.n) (i : Case3SelectedGroup x Z) :
    case3PairOwner x Z u u = case3RawIndexLabel x i.1 ↔
      case3OrderedLoopOwner x Z hdiv u = i := by
  rw [case3PairOwner_loop, ← case3OrderedLoopOwner_label x Z hdiv u]
  constructor
  · intro h
    exact Subtype.ext ((case3RawIndexLabel_injective x) h)
  · rintro rfl
    rfl

/-- The loop-owner label test agrees with the explicit loop-assignment data. -/
theorem case3PairOwner_loop_assigned_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (u : Fin x.n) (i : Case3SelectedGroup x Z) :
    case3PairOwner x Z u u = case3RawIndexLabel x i.1 ↔
      u ∈ case3AssignedLoops (case3OrderedLoopAssignment x Z hdiv) (case3SelectedMember x Z i) := by
  rw [case3PairOwner_loop_eq_iff x Z hdiv u i, mem_case3AssignedLoops]
  change case3OrderedLoopOwner x Z hdiv u = i ↔
    case3SelectedMember x Z (case3OrderedLoopOwner x Z hdiv u) = case3SelectedMember x Z i
  exact (case3SelectedMember_injective x Z).eq_iff.symm

/-- For every valid pair, routing tests precisely the restored-member edge predicate. -/
theorem case3PairOwner_selection_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (u v : Fin x.n) (hvalid : u = v ∨ x.G.Adj u v) (i : Case3SelectedGroup x Z) :
    ((case3SelectedMember x Z i).graph.Adj u v ∨
      (u = v ∧
        u ∈ case3AssignedLoops (case3OrderedLoopAssignment x Z hdiv) (case3SelectedMember x Z i) ∧
        u ∈ (case3SelectedMember x Z i).verts)) ↔
      case3PairOwner x Z u v = case3RawIndexLabel x i.1 := by
  by_cases he : u = v
  · subst v
    constructor
    · rintro (hadj | ⟨_, hloop, _⟩)
      · exact False.elim ((case3SelectedMember x Z i).graph.loopless.irrefl u hadj)
      · exact (case3PairOwner_loop_assigned_iff x Z hdiv u i).mpr hloop
    · intro h
      have hi := (case3PairOwner_loop_eq_iff x Z hdiv u i).mp h
      refine Or.inr ⟨rfl, (case3PairOwner_loop_assigned_iff x Z hdiv u i).mp h, ?_⟩
      exact hi ▸ case3OrderedLoopOwner_contains x Z hdiv u
  · have hadj := hvalid.resolve_left he
    simp only [he, false_and, or_false]
    exact case3PairOwner_adj_iff x Z u v hadj i

end GraphMinor.Compute
