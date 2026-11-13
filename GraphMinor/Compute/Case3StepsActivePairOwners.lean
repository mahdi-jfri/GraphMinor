module

public import GraphMinor.Compute.Case3StepsPairSelection
public import GraphMinor.Compute.MultiDigraph

/-!
# Owners of the stored positive multigraph pairs

Each stored pair is a loop or an edge of the underlying simple graph. Its
computed owner therefore lies in the selected-candidate range and agrees
with the restored-member predicate. The bucket pass uses these labels once
per stored pair, independently of its multiplicity.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The owner label of a positive pair at its canonical encoding index. -/
noncomputable def case3ActivePairOwner (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (j : Fin D.numActivePairs) : ℕ :=
  case3PairOwner x Z (D.activePairsList[j.1]).1 (D.activePairsList[j.1]).2

/-- Each stored pair is a loop or an edge of the simple society graph. -/
theorem case3ActivePair_valid (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (j : Fin D.numActivePairs) :
    (D.activePairsList[j.1]).1 = (D.activePairsList[j.1]).2 ∨
      x.G.Adj (D.activePairsList[j.1]).1 (D.activePairsList[j.1]).2 := by
  have hpos := (MultiDigraph.mem_activePairsList D _).mp (List.getElem_mem j.2)
  by_cases he : (D.activePairsList[j.1]).1 = (D.activePairsList[j.1]).2
  · exact Or.inl he
  · right
    rw [← hG, MultiDigraph.toSimpleGraph_adj]
    exact ⟨he, Or.inl hpos⟩

/-- Every positive pair routes to a genuine candidate label. -/
theorem case3ActivePairOwner_lt (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z)) (j : Fin D.numActivePairs) :
    case3ActivePairOwner x D Z j < x.n + (case3InputEdges x).length := by
  rcases case3ActivePair_valid x D hG j with he | hadj
  · unfold case3ActivePairOwner
    rw [he, case3PairOwner_loop]
    exact case3OrderedLoopLabel_lt x Z hdiv _
  · exact case3PairOwner_lt_of_adj x Z _ _ hadj

/-- Positive pair routing agrees exactly with the restored-member edge test. -/
theorem case3ActivePairOwner_selection_iff (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (j : Fin D.numActivePairs) (i : Case3SelectedGroup x Z) :
    ((case3SelectedMember x Z i).graph.Adj (D.activePairsList[j.1]).1 (D.activePairsList[j.1]).2 ∨
      ((D.activePairsList[j.1]).1 = (D.activePairsList[j.1]).2 ∧
        (D.activePairsList[j.1]).1 ∈ case3AssignedLoops (case3OrderedLoopAssignment x Z hdiv)
          (case3SelectedMember x Z i) ∧
        (D.activePairsList[j.1]).1 ∈ (case3SelectedMember x Z i).verts)) ↔
      case3ActivePairOwner x D Z j = case3RawIndexLabel x i.1 :=
  case3PairOwner_selection_iff x Z hdiv _ _ (case3ActivePair_valid x D hG j) i

end GraphMinor.Compute
