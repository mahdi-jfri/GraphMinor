module

public import GraphMinor.GM01.ForestTrees
public import GraphMinor.GM01.PathCombs
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM01.Basic

/-!
# The forest tree in a three-vertex comb

In the proof of Graph Minors I, (3.1), page 54, `P(ℓ,3)` contains `Y_ℓ`
as a minor. Contract the three spine vertices to the centre, and retain
the three binary copies as its branches. The branch sets below carry out
this contraction explicitly. This is the forest configuration needed for
(1.1).
-/

public section

namespace GraphMinor.GM01

open Set SimpleGraph

private def forestCombBranch : ForestTreeVertex →
    (⊤ : SimpleGraph (PathCombVertex 3)).Subgraph
  | none => pathComb 0 3
  | some p => (⊤ : SimpleGraph (PathCombVertex 3)).singletonSubgraph (Sum.inr p)

private theorem forestCombBranch_verts (v : ForestTreeVertex) :
    (forestCombBranch v).verts = match v with
      | none => range Sum.inl
      | some p => {Sum.inr p} := by
  cases v with
  | none =>
    ext x
    cases x with
    | inl i => exact ⟨fun _ ↦ ⟨i, rfl⟩, fun _ ↦ trivial⟩
    | inr p => simp [forestCombBranch, pathComb, pathCombVertices]
  | some p => rfl

/-- The minor assertion used in the proof of Graph Minors I, (3.1),
page 54. The centre branch is the spine and the remaining branches are
singletons in their corresponding binary copies. -/
theorem forestTree_isIsoMinor_pathComb (ℓ : ℕ) :
    IsIsoMinor (forestTreeGraph ℓ) (toGraph (pathComb ℓ 3)) := by
  apply isIsoMinor_toGraph_of_connected_subgraphs (forestTree_vertices_finite ℓ)
    (pathComb_vertices_finite ℓ 3) forestCombBranch
  · intro v hv
    cases v with
    | none => exact pathComb_mono (Nat.zero_le ℓ)
    | some p =>
      apply (singletonSubgraph_le_iff _ _).mpr
      change p.2.length < ℓ
      change p.2.length + 1 ≤ ℓ at hv
      omega
  · intro v _
    cases v with
    | none => exact pathComb_connected (by decide)
    | some p => exact Subgraph.singletonSubgraph_connected
  · intro v _ w _ hne
    rw [forestCombBranch_verts, forestCombBranch_verts]
    cases v with
    | none =>
      cases w with
      | none => exact False.elim (hne rfl)
      | some p =>
        apply disjoint_singleton_right.mpr
        rintro ⟨i, hi⟩
        cases hi
    | some p =>
      cases w with
      | none =>
        apply disjoint_singleton_left.mpr
        rintro ⟨i, hi⟩
        cases hi
      | some q =>
        apply disjoint_singleton.mpr
        intro h
        exact hne (congrArg some (Sum.inr.inj h))
  · intro v w h
    have hv := h.1
    have hw := h.2.1
    rcases h.2.2 with ⟨hwne, hparent⟩ | ⟨hvne, hparent⟩
    · cases w with
      | none => exact False.elim (hwne rfl)
      | some p =>
        rcases p with ⟨i, word⟩
        cases word with
        | nil =>
          have hvnone : v = none := hparent.symm
          subst v
          refine ⟨Sum.inl i, ?_, Sum.inr (i, []), ?_, ?_⟩
          · exact pathComb_spine_mem 0 3 i
          · exact mem_singleton _
          · exact ⟨rfl, rfl, by change 0 + 1 ≤ ℓ at hw; omega⟩
        | cons bit word =>
          have hvsome : v = some (i, word) := hparent.symm
          subst v
          refine ⟨Sum.inr (i, word), mem_singleton _,
            Sum.inr (i, bit :: word), mem_singleton _, ?_⟩
          exact ⟨rfl, by change word.length + 1 ≤ ℓ at hv; omega,
            by change (bit :: word).length + 1 ≤ ℓ at hw; simpa using hw,
            Or.inl ⟨bit, rfl⟩⟩
    · cases v with
      | none => exact False.elim (hvne rfl)
      | some p =>
        rcases p with ⟨i, word⟩
        cases word with
        | nil =>
          have hwnone : w = none := hparent.symm
          subst w
          refine ⟨Sum.inr (i, []), mem_singleton _, Sum.inl i,
            pathComb_spine_mem 0 3 i, ?_⟩
          exact ⟨rfl, rfl, by change 0 + 1 ≤ ℓ at hv; omega⟩
        | cons bit word =>
          have hwsome : w = some (i, word) := hparent.symm
          subst w
          refine ⟨Sum.inr (i, bit :: word), mem_singleton _,
            Sum.inr (i, word), mem_singleton _, ?_⟩
          exact ⟨rfl,
            by change (bit :: word).length + 1 ≤ ℓ at hv; simpa using hv,
            by change word.length + 1 ≤ ℓ at hw; omega,
            Or.inr ⟨bit, rfl⟩⟩

end GraphMinor.GM01
