module

public import GraphMinor.Kruskal.EmbeddedChainVertices

/-!
# Links of the embedded replacing paths

The chain stem at position `k` maps to a prefix of depth `parentDepth + k`.
The next head maps to the prefix one step farther along the same image
address. Deleting its last index therefore gives the mapped stem, so each
chain segment maps to an actual edge of the target address tree.
-/

public section

namespace GraphMinor.Kruskal

open Graph

private theorem dropLast_take_succ {q : List ℕ} {m : ℕ} (hm : m < q.length) :
    (q.take (m + 1)).dropLast = q.take m := by
  have hshort : (q.take m).length = m := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  have hlong : (q.take (m + 1)).length = m + 1 := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  have hne : q.take m ≠ q.take (m + 1) := by
    intro h
    have hl := congrArg List.length h
    omega
  have hp := proper_prefix_dropLast (List.take_prefix_take_left (Nat.le_succ m)) hne
  have heq : (q.take m).length = (q.take (m + 1)).dropLast.length := by
    rw [List.length_dropLast, hshort, hlong]
    omega
  exact (hp.eq_of_length heq).symm

namespace OrderedTree.AddressEmbedding

/-- The image of a stem is the prefix at its depth on the replacing path. -/
theorem rawVertex_stem {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) (k : ℕ) :
    φ.rawVertex (chainStem s.addressParent e k) =
      (φ.vertices (s.addressChild e)).val.take
        ((φ.vertices (s.addressParent e)).val.length + k) := by
  cases k with
  | zero =>
    change (φ.vertices (s.addressParent e)).val =
      (φ.vertices (s.addressChild e)).val.take ((φ.vertices (s.addressParent e)).val.length + 0)
    simpa only [Nat.add_zero] using (List.prefix_iff_eq_take.1 (φ.parent_prefix_child e))
  | succ k => rfl

/-- The image of a segment head is the next prefix on the replacing path,
including the final segment, whose head is the original image child. -/
theorem rawVertex_finish {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) (j : ℕ) :
    φ.rawVertex (chainFinish s.addressChild φ.internalCount (e, j)) =
      (φ.vertices (s.addressChild e)).val.take
        ((φ.vertices (s.addressParent e)).val.length + j / 2 + 1) := by
  classical
  unfold chainFinish
  dsimp only [Prod.fst, Prod.snd]
  split_ifs with hj
  · subst j
    change (φ.vertices (s.addressChild e)).val = _
    have hdiv : 2 * φ.internalCount e / 2 = φ.internalCount e := by omega
    rw [hdiv, ← φ.child_length_eq e, List.take_length]
  · rfl

/-- The prescribed edge name has positive depth and so is not the target root. -/
theorem chainEdges_length {s t : OrderedTree} (φ : AddressEmbedding s t) (d : E(φ.chains)) :
    (φ.chainEdges d).length =
      (φ.vertices (s.addressParent d.val.1)).val.length + d.val.2 / 2 + 1 := by
  obtain ⟨⟨e, j⟩, hd⟩ := d
  change (φ.rawVertex (chainFinish s.addressChild φ.internalCount (e, j))).length = _
  rw [φ.rawVertex_finish, List.length_take]
  have hb : j / 2 ≤ φ.internalCount e := by
    change j = 2 * φ.internalCount e ∨ j % 2 = 1 ∧ j < 2 * φ.internalCount e at hd
    omega
  have hc := φ.child_length_eq e
  exact Nat.min_eq_left (by omega)

/-- Deleting the last index from the image edge head gives the image stem. -/
theorem chainEdges_parent {s t : OrderedTree} (φ : AddressEmbedding s t) (d : E(φ.chains)) :
    (φ.chainEdges d).dropLast =
      φ.rawVertex (chainStem s.addressParent d.val.1 (d.val.2 / 2)) := by
  obtain ⟨⟨e, j⟩, hd⟩ := d
  change (φ.rawVertex (chainFinish s.addressChild φ.internalCount (e, j))).dropLast = _
  rw [φ.rawVertex_finish, φ.rawVertex_stem]
  have hb : j / 2 ≤ φ.internalCount e := by
    change j = 2 * φ.internalCount e ∨ j % 2 = 1 ∧ j < 2 * φ.internalCount e at hd
    omega
  have hc := φ.child_length_eq e
  exact dropLast_take_succ (by omega)

/-- Every image edge name is an actual edge of the target address tree. -/
theorem chainEdges_mem {s t : OrderedTree} (φ : AddressEmbedding s t) (d : E(φ.chains)) :
    φ.chainEdges d ∈ E(rootedGraph t.toRootedTree) := by
  have hlen := φ.chainEdges_length d
  have hne : φ.chainEdges d ≠ [] := by
    intro h
    have hz : (φ.chainEdges d).length = 0 := by rw [h]; rfl
    omega
  exact t.toRootedTree.mem_edges.2 ⟨hne, φ.rawVertex_mem (φ.chainHead d)⟩

/-- Both ends of every chain segment map to the ends of its image edge. -/
theorem chainLinks {s t : OrderedTree} (φ : AddressEmbedding s t)
    (d : E(φ.chains)) (x y : V(φ.chains)) (hxy : φ.chains.IsLink d.val x.val y.val) :
    (rootedGraph t.toRootedTree).IsLink (φ.chainEdges d) (φ.chainVertices x) (φ.chainVertices y) := by
  refine ⟨φ.chainEdges_mem d, ?_⟩
  obtain ⟨_, hxy⟩ := hxy
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · apply Or.inl
    have hx' : φ.chainVertices x =
        φ.rawVertex (chainStem s.addressParent d.val.1 (d.val.2 / 2)) :=
      congrArg φ.rawVertex hx
    have hy' : φ.chainVertices y = φ.chainEdges d := congrArg φ.rawVertex hy
    exact ⟨hx'.trans (φ.chainEdges_parent d).symm, hy'⟩
  · apply Or.inr
    have hx' : φ.chainVertices x = φ.chainEdges d := congrArg φ.rawVertex hx
    have hy' : φ.chainVertices y =
        φ.rawVertex (chainStem s.addressParent d.val.1 (d.val.2 / 2)) :=
      congrArg φ.rawVertex hy
    exact ⟨hx', hy'.trans (φ.chainEdges_parent d).symm⟩

end OrderedTree.AddressEmbedding
end GraphMinor.Kruskal
