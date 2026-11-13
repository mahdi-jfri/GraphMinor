module

public import GraphMinor.GM01.CombSkippedBinary
public import GraphMinor.GM01.CombBoundaryAttachment
public import GraphMinor.GM01.CombLastRegion

/-!
# The skipped arm and its boundary attachment

Graph Minors I, (4.1), page 55, attaches the skipped binary-tree arm to
the initial piece. Use the model on the exact two-cell support and the
boundary replacing path proved to meet that support only at its root.
Both source ends of the boundary edge precede the final tail cut, so
its entire replacing path avoids the last block. This supplies the arm
and attachment data for the final fork contraction.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The actual skipped binary-tree arm comes with a boundary path from
the preceding cut centre, meeting that arm only at its root and avoiding
the final block. -/
theorem exists_skipped_binary_attachment {α β : Type*} {γ L n : ℕ}
    (hL : 0 < L) (htail : 2 * n ≤ L) {G N R : Graph α β} (hN : N ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    (P : (pathComb γ L).coe.edgeSet → Graph α β) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (root : α) (hR : IsGraphPathWithEnds G R root (c (rootedPathComb γ L hL).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (j : Fin n) (hj0 : 0 < j.val) (hjn : j.val + 1 < n) :
    ∃ K : Graph α β, K ≤ N ∧ V(K) ⊆ combBlock hL (subgraphUnion G N R) c j ∧
      ∃ b : V(K), HasRootedMinor (binaryRootedTree γ) (⟨K,b⟩ : RootedGraph α β) ∧
        ∃ B : Graph α β, IsGraphPathWithEnds G B
          (c ⟨Sum.inl ⟨2 * j.val - 1, by omega⟩, pathComb_spine_mem γ L _⟩) b.val ∧
          V(B) ∩ V(K) = {b.val} ∧
          Disjoint V(B) (combBlock hL (subgraphUnion G N R) c (⟨n - 1, by omega⟩ : Fin n)) := by
  obtain ⟨K, hKN, hKblock, hSupport, hroot, hBinary⟩ := exists_skipped_block_binary_model
    hL htail hN hc hcentres P hE hPaths hInter root hR hmeet j hj0 hjn
  have hbound : 2 * j.val + 2 ≤ L := by omega
  obtain ⟨boundary, hEnds, hBoundary, hMeet⟩ := exists_comb_boundary_attachment hc P hPaths
    (fun e f hne ↦ (hInter e f hne).1) (2 * j.val) (by omega) hbound
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hLastEq := comb_lastBlock_eq_region hL (by omega : 2 ≤ n) htail hN hc hcentres hPN
    hE hRanges (fun e f hne ↦ (hInter e f hne).1) root hR hmeet
  have hAvoid : Disjoint V(P boundary)
      (combBlock hL (subgraphUnion G N R) c (⟨n - 1, by omega⟩ : Fin n)) := by
    rw [hLastEq]
    apply comb_subdivision_path_disjoint_later_region hc hPN hE hRanges
      (fun e f hne ↦ (hInter e f hne).1) ⟨2 * n - 3, by omega⟩
      (by change 2 * n - 3 < L - 1; omega) boundary
    intro v hv
    rw [hEnds, Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · change 2 * j.val - 1 ≤ 2 * n - 3
      omega
    · change 2 * j.val + 0 ≤ 2 * n - 3
      omega
  refine ⟨K, hKN, hKblock.vertexSet_mono,
    ⟨_, hroot⟩, hBinary, P boundary, hBoundary.mono hN, ?_, hAvoid⟩
  change V(P boundary) ∩ V(K) =
    {c (combShiftEmbedding (2 * j.val) hbound (rootedPathComb γ 2 (by decide)).root)}
  rw [hSupport]
  exact hMeet

end GraphMinor.GM01
