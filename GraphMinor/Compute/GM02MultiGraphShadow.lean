module

public import GraphMinor.Compute.Bridge13
public import GraphMinor.Compute.GM02NumberedInstance

/-!
# The numbered path graph of an input multigraph

The multigraph encoding retains loops and parallel-edge multiplicities.
Its mathematical undirected graph has vertices below the supplied count.
Number these actual vertices by the same natural values. Distinct-vertex
adjacency then gives exactly the encoded underlying simple graph, as
required by the final reduction of II (3.2), page 318.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02

/-- The input's actual natural-number vertices have their given finite names. -/
def gm02MultiVertexEquiv {n : ℕ} (G : MultiDigraph n) :
    V(G.toGMDigraph.toGraph) ≃ Fin n where
  toFun u := ⟨u.val, u.property⟩
  invFun u := ⟨u.val, u.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Forgetting edge directions gives adjacency in either multiplicity direction, including loops. -/
theorem gm02MultiGraph_adj {n : ℕ} (G : MultiDigraph n) (u v : Fin n) :
    G.toGMDigraph.toGraph.Adj u.val v.val ↔ 0 < G.edgeMult u v ∨ 0 < G.edgeMult v u := by
  constructor
  · rintro ⟨e, he⟩
    change (∃ (hu : e.1 < n) (hv : e.2.1 < n), e.2.2 < G.edgeMult ⟨e.1, hu⟩ ⟨e.2.1, hv⟩) ∧
      ((e.2.1 = u.val ∧ e.1 = v.val) ∨ (e.2.1 = v.val ∧ e.1 = u.val)) at he
    obtain ⟨hu, hv, hidx⟩ := he.1
    rcases he.2 with ⟨hhead, htail⟩ | ⟨hhead, htail⟩
    · have he1 : (⟨e.1, hu⟩ : Fin n) = v := Fin.ext htail
      have he2 : (⟨e.2.1, hv⟩ : Fin n) = u := Fin.ext hhead
      rw [he1, he2] at hidx
      exact Or.inr ((Nat.zero_le _).trans_lt hidx)
    · have he1 : (⟨e.1, hu⟩ : Fin n) = u := Fin.ext htail
      have he2 : (⟨e.2.1, hv⟩ : Fin n) = v := Fin.ext hhead
      rw [he1, he2] at hidx
      exact Or.inl ((Nat.zero_le _).trans_lt hidx)
  · rintro (h | h)
    · refine ⟨(u.val, v.val, 0), ?_⟩
      exact ⟨⟨u.isLt, v.isLt, h⟩, Or.inr ⟨rfl, rfl⟩⟩
    · refine ⟨(v.val, u.val, 0), ?_⟩
      exact ⟨⟨v.isLt, u.isLt, h⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- The numbered distinct-endpoint path graph is the input's underlying simple graph. -/
theorem gm02Multi_pathGraph_comap {n : ℕ} (G : MultiDigraph n) :
    (pathGraph G.toGMDigraph.toGraph).comap (fun u : Fin n => u.val) = G.toSimpleGraph := by
  ext u v
  change (G.toGMDigraph.toGraph.Adj u.val v.val ∧ u.val ≠ v.val) ↔ G.toSimpleGraph.Adj u v
  rw [gm02MultiGraph_adj, MultiDigraph.toSimpleGraph_adj]
  constructor
  · rintro ⟨hm, hne⟩
    exact ⟨fun he => hne (congrArg Fin.val he), hm⟩
  · rintro ⟨hne, hm⟩
    exact ⟨hm, fun he => hne (Fin.ext he)⟩

/-- Numbering a terminated input multigraph produces exactly its underlying simple graph. -/
theorem gm02Multi_numbered_graph {n : ℕ} (G : MultiDigraph n)
    (A : Termination V(G.toGMDigraph.toGraph)) :
    (gm02NumberedInstance G.toGMDigraph.toGraph A (gm02MultiVertexEquiv G)).G = G.toSimpleGraph := by
  rw [gm02NumberedInstance_graph]
  exact gm02Multi_pathGraph_comap G

end GraphMinor.Compute
