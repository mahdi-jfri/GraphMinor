module

public import GraphMinor.Compute.Case3StepsEdgeMatrixAccess
public import GraphMinor.Compute.Case3StepsOrderedLoopOwner
import GraphMinor.Compute.Case3StepsReadCoreEdgeProg

/-!
# A common owner lookup for directed multigraph pairs

Loops use the computed first-containing-member table. Nonloops use the
endpoint matrix. The lookup therefore assigns each positive pair record to
one selected member, while keeping its stored multiplicity unchanged, as
required in XIII (9.9), step 5, p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- A loop uses its vertex owner; a nonloop uses the endpoint-owner matrix. -/
noncomputable def case3PairOwner (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) : ℕ :=
  if u = v then case3OrderedLoopLabel x Z u else
    (case3EdgeMatrixPrefix x Z (case3InputEdges x).length).getD (case3PairPosition u v) 0

/-- Every adjacent pair has a canonical simple edge with its unordered endpoints. -/
theorem case3CanonicalEdgePair (x : Alg81Input) (u v : Fin x.n) (hadj : x.G.Adj u v) :
    ∃ j : Fin (case3InputEdges x).length,
      ({u, v} : Finset (Fin x.n)) =
        {((case3InputEdges x)[j.1]).1, ((case3InputEdges x)[j.1]).2} := by
  have hne : u ≠ v := fun h => x.G.loopless.irrefl u (h ▸ hadj)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm : (u, v) ∈ case3InputEdges x := (mem_edgeListOf x.G _).mpr ⟨hlt, hadj⟩
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
    exact ⟨⟨k, hk⟩, by rw [he]⟩
  · have hm : (v, u) ∈ case3InputEdges x := (mem_edgeListOf x.G _).mpr ⟨hgt, hadj.symm⟩
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
    exact ⟨⟨k, hk⟩, by rw [he]; exact Finset.pair_comm _ _⟩

/-- For an adjacent pair, owner-label equality is exact selected-member adjacency. -/
theorem case3PairOwner_adj_iff (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) (hadj : x.G.Adj u v) (i : Case3SelectedGroup x Z) :
    (case3SelectedMember x Z i).graph.Adj u v ↔
      case3PairOwner x Z u v = case3RawIndexLabel x i.1 := by
  have hne : u ≠ v := fun h => x.G.loopless.irrefl u (h ▸ hadj)
  obtain ⟨j, hj⟩ := case3CanonicalEdgePair x u v hadj
  simp only [case3PairOwner, hne, ↓reduceIte]
  exact case3EdgeMatrix_adj_iff x Z j u v hj i

/-- Nonloop owner labels lie in the candidate range. -/
theorem case3PairOwner_lt_of_adj (x : Alg81Input) (Z : Finset (Fin x.n))
    (u v : Fin x.n) (hadj : x.G.Adj u v) :
    case3PairOwner x Z u v < x.n + (case3InputEdges x).length := by
  have hne : u ≠ v := fun h => x.G.loopless.irrefl u (h ▸ hadj)
  obtain ⟨j, hj⟩ := case3CanonicalEdgePair x u v hadj
  rw [case3PairOwner, ite_eq_right hne, case3EdgeMatrix_getD x Z j u v hj]
  exact case3EdgeLabel_lt x Z j

/-- A loop's owner label is the label of its first containing selected member. -/
theorem case3PairOwner_loop (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) : case3PairOwner x Z u u = case3OrderedLoopLabel x Z u := by
  simp only [case3PairOwner, ↓reduceIte]

end GraphMinor.Compute
