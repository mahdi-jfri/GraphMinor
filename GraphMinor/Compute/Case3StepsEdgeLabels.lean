module

public import GraphMinor.Compute.Case3StepsCoreEdgeOwner
import GraphMinor.Compute.Case3StepsReadCoreEdgeProg

/-!
# Owner labels for canonical simple edges

An edge with an outside endpoint uses that endpoint's component label. A
core edge uses its stored core-edge label. The resulting number identifies
exactly the selected member containing the edge. These labels will populate
a dense endpoint table for routing the multigraph pair records in XIII
(9.9), step 5, p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- The computed owner label for a canonical simple edge. -/
noncomputable def case3EdgeLabel (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) : ℕ :=
  let e := (case3InputEdges x)[j.1]
  if e.1 ∈ Z then
    if e.2 ∈ Z then case3CoreEdgeRepEntry x Z j else case3ComponentRepresentative x Z e.2
  else case3ComponentRepresentative x Z e.1

/-- For every simple edge, the stored label tests exact selected-member membership. -/
theorem case3EdgeLabel_adj_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) (i : Case3SelectedGroup x Z) :
    (case3SelectedMember x Z i).graph.Adj
      ((case3InputEdges x)[j.1]).1 ((case3InputEdges x)[j.1]).2 ↔
      case3EdgeLabel x Z j = case3RawIndexLabel x i.1 := by
  have he := (case3InputEdges_get_spec x j).2
  unfold case3EdgeLabel
  dsimp only
  by_cases hu : ((case3InputEdges x)[j.1]).1 ∈ Z
  · by_cases hv : ((case3InputEdges x)[j.1]).2 ∈ Z
    · simp only [hu, hv, ↓reduceIte]
      exact case3CoreEdgeOwner_edge_iff x Z j ⟨hu, hv⟩ i
    · simp only [hu, hv, ↓reduceIte]
      rw [(case3SelectedMember x Z i).graph.adj_comm]
      exact case3SelectedMember_adj_outside_iff x Z i _ _ hv he.symm
  · simp only [hu, ↓reduceIte]
    exact case3SelectedMember_adj_outside_iff x Z i _ _ hu he

/-- Every simple edge routes to a genuine candidate label. -/
theorem case3EdgeLabel_lt (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) :
    case3EdgeLabel x Z j < x.n + (case3InputEdges x).length := by
  unfold case3EdgeLabel
  dsimp only
  split_ifs with hu hv
  · unfold case3CoreEdgeRepEntry
    simp only [hu, hv, and_self, ↓reduceIte]
    exact case3CoreEdgeRepresentative_lt x Z _ _ j.1 j.2
  · have h := case3ComponentRepresentative_lt x Z _ hv
    omega
  · have h := case3ComponentRepresentative_lt x Z _ hu
    omega

end GraphMinor.Compute
