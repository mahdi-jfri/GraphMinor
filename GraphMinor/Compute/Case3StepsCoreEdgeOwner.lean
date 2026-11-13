module

public import GraphMinor.Compute.Case3StepsComponentOwner
import GraphMinor.Compute.Case3StepsReadCoreEdgeProg

/-!
# Routing core edges to selected groups

The least matching component boundary owns a core edge when such a boundary
exists. Otherwise the edge's own candidate is selected. The owner therefore
has exactly the label stored by the core-edge program, as required for the
merged raw members of Graph Minors XIII, (8.6), p. 96.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Select the matching component group, or the edge's own group if none matches. -/
noncomputable def case3CoreEdgeOwner (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length)
    (hc : ((case3InputEdges x)[j.1]).1 ∈ Z ∧ ((case3InputEdges x)[j.1]).2 ∈ Z) :
    Case3SelectedGroup x Z := by
  classical
  let e := (case3InputEdges x)[j.1]
  let P := fun z => z ∉ Z ∧ case3AttachmentRowSet x Z z = {e.1, e.2}
  by_cases h : case3FirstIndex P < x.n
  · exact case3ComponentOwner x Z ⟨case3FirstIndex P, h⟩ (case3FirstIndex_spec P h).1.1
  · exact ⟨.inr j, (case3GroupActive_inr_iff x Z j).mpr
      ⟨hc, (case3FirstIndex_eq_sentinel_iff P).mp
        (Nat.le_antisymm (case3FirstIndex_le P) (Nat.le_of_not_gt h))⟩⟩

/-- The core-edge owner has the same numeric label as the computed table entry. -/
theorem case3CoreEdgeOwner_label (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length)
    (hc : ((case3InputEdges x)[j.1]).1 ∈ Z ∧ ((case3InputEdges x)[j.1]).2 ∈ Z) :
    case3RawIndexLabel x (case3CoreEdgeOwner x Z j hc).1 = case3CoreEdgeRepEntry x Z j := by
  classical
  unfold case3CoreEdgeOwner
  dsimp only
  split_ifs with h
  · rw [case3ComponentOwner_label]
    have hs := (case3FirstIndex_spec _ h).1.2
    unfold case3ComponentRepresentative
    rw [hs]
    simp only [case3CoreEdgeRepEntry, hc, ↓reduceIte, case3CoreEdgeRepresentative, h, and_self]
  · simp only [case3RawIndexLabel, case3CoreEdgeRepEntry, hc, ↓reduceIte,
      case3CoreEdgeRepresentative, h, and_self]

/-- The owner boundary is the core edge's endpoint pair. -/
theorem case3CoreEdgeOwner_boundary (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length)
    (hc : ((case3InputEdges x)[j.1]).1 ∈ Z ∧ ((case3InputEdges x)[j.1]).2 ∈ Z) :
    case3GroupBoundary x Z (case3CoreEdgeOwner x Z j hc).1 =
      {((case3InputEdges x)[j.1]).1, ((case3InputEdges x)[j.1]).2} := by
  classical
  unfold case3CoreEdgeOwner
  dsimp only
  split_ifs with h
  · rw [case3ComponentOwner_boundary,
      ← case3AttachmentRowSet_eq_attachOf x Z _ (case3FirstIndex_spec _ h).1.1]
    exact (case3FirstIndex_spec _ h).1.2
  · rfl

/-- A core edge belongs exactly to the group identified by its stored label. -/
theorem case3CoreEdgeOwner_edge_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length)
    (hc : ((case3InputEdges x)[j.1]).1 ∈ Z ∧ ((case3InputEdges x)[j.1]).2 ∈ Z)
    (i : Case3SelectedGroup x Z) :
    (case3SelectedMember x Z i).graph.Adj
      ((case3InputEdges x)[j.1]).1 ((case3InputEdges x)[j.1]).2 ↔
      case3CoreEdgeRepEntry x Z j = case3RawIndexLabel x i.1 := by
  rw [case3SelectedMember_adj_core_iff x Z i _ _ hc.1 hc.2
    (case3InputEdges_get_spec x j).2, ← case3CoreEdgeOwner_boundary x Z j hc,
    ← case3CoreEdgeOwner_label x Z j hc]
  constructor
  · intro h
    have heq := case3GroupBoundary_injective_on_active x Z i.1
      (case3CoreEdgeOwner x Z j hc).1 i.2 (case3CoreEdgeOwner x Z j hc).2 h
    exact congrArg (case3RawIndexLabel x) heq.symm
  · intro h
    exact congrArg (case3GroupBoundary x Z) ((case3RawIndexLabel_injective x) h.symm)

end GraphMinor.Compute
