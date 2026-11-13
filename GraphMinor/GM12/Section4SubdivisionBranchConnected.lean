module

public import GraphMinor.GM12.Section4SubdivisionBranches
public import GraphMinor.Minor.Model
public import Mathlib.Combinatorics.Graph.Delete

/-!
# Connectivity of the subdivision contraction branches

To recover the original graph in XII (4.5), page 252, contract
all but the first edge of each subdivided chain. From each positive
cut, follow the later cuts to the original right endpoint. These
walks stay inside its branch and use no representing first edge.
They prove that every branch is connected after those edges are
deleted.
-/

public section

namespace GraphMinor.GM12

open Set Graph Relation

/-- Each subdivision contraction branch is connected after the
representing first edges are deleted. This proves the connectivity
part of the original-graph minor in XII (4.5), page 252. -/
theorem subdivisionBranch_connected_subgraph {m n : ℕ}
    (κ : Fin n × Bool → Fin m) (k : Fin n → ℕ) (hk : ∀ e, 0 < k e) (v : Fin m) :
    ∃ K ≤ (subdivisionGraph κ k).deleteEdges (range (subdivisionFirstEdge k hk)),
      K.vertexSet = subdivisionBranch κ k v ∧ GraphConnected K := by
  let K := ((subdivisionGraph κ k).deleteEdges (range (subdivisionFirstEdge k hk))).induce
    (subdivisionBranch κ k v)
  have hpositive : ∀ e, κ (e, true) = v → ∀ r : Fin (k e + 1), 0 < r.val →
      ReflTransGen K.Adj (subdivisionVertexAt κ k e r) (Sum.inl v) := by
    intro e howner
    refine Fin.reverseInduction ?_ ?_
    · intro _
      rw [subdivisionVertexAt_last κ k e (hk e), howner]
    · intro i ih hi
      have hleft : subdivisionVertexAt κ k e i.castSucc ∈ subdivisionBranch κ k v :=
        (mem_subdivisionBranch_vertexAt_pos κ k v e i.castSucc hi).mpr howner
      have hright : subdivisionVertexAt κ k e i.succ ∈ subdivisionBranch κ k v :=
        (mem_subdivisionBranch_vertexAt_pos κ k v e i.succ (by change 0 < i.val + 1; omega)).mpr howner
      have hlK : K.IsLink ⟨e, i⟩ (subdivisionVertexAt κ k e i.castSucc)
          (subdivisionVertexAt κ k e i.succ) :=
        ⟨⟨subdivisionGraph_isLink κ k e i, subdivisionEdge_not_mem_firstEdges k hk e i hi⟩,
          hleft, hright⟩
      exact (ReflTransGen.single ⟨⟨e, i⟩, hlK⟩).trans (ih (by change 0 < i.val + 1; omega))
  have hreach : ∀ z ∈ subdivisionBranch κ k v, ReflTransGen K.Adj z (Sum.inl v) := by
    intro z hz
    cases z with
    | inl w =>
      change w = v at hz
      subst w
      exact ReflTransGen.refl
    | inr q =>
      obtain ⟨e, j⟩ := q
      change κ (e, true) = v at hz
      have h := hpositive e hz ⟨j.val + 1, by have := j.isLt; omega⟩ (by change 0 < j.val + 1; omega)
      rw [subdivisionVertexAt_internal] at h
      exact h
  refine ⟨K, ?_, rfl, ⟨⟨Sum.inl v, rfl⟩, ?_⟩⟩
  · apply Graph.induce_le
    intro z _
    exact mem_univ z
  · intro x hx y hy
    exact (hreach x hx).trans (symm (hreach y hy))

end GraphMinor.GM12
