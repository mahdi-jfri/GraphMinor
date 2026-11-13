module

public import GraphMinor.GM01.CombSegmentModels
import GraphMinor.GM01.CombSubdivisionSplit
import GraphMinor.GM01.SelectedBoundaryPath
import GraphMinor.GM01.TerminalPieceComplement

/-!
# Connectivity after removing a terminal comb segment

In Graph Minors I, (4.12), page 59, the vertices outside the second
end are contracted into the root piece. They form a connected graph:
the earlier cells are connected and the boundary replacing path,
stopped before its final vertex, attaches to them. The subdivision
split proves that these are all the vertices outside the terminal
segment. This also handles attachment vertices inside replacing paths.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- Removing a nonempty terminal interval leaves a connected induced
graph on the other vertices. Applied to the last two cells, this is
the root-piece connectivity used in GM01 (4.12), page 59. -/
theorem comb_terminal_segment_complement_connected {α β : Type*} {γ L k m : ℕ}
    (hk : 0 < k) (hm : 0 < m) (hsum : k + m = L) {D : Graph α β}
    (c : (pathComb γ L).verts → α) (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f)) :
    GraphConnected (D.induce (V(D) \ combSegmentSupport c P k (by omega : k + m ≤ L))) := by
  have hkL : k < L := by omega
  have hcentres : ∀ v, c v ∈ V(D) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  let f := combShiftEmbedding (γ := γ) k (by omega : k + m ≤ L)
  let hf := fun {a b} (h : (pathComb γ m).coe.Adj a b) ↦ combShiftEmbedding_adj k (show k + m ≤ L by omega) h
  let r := (rootedPathComb γ m hm).root
  let a : (pathComb γ L).verts := ⟨Sum.inl ⟨k - 1, by omega⟩, pathComb_spine_mem γ L _⟩
  have hadj : (pathComb γ L).coe.Adj a (f r) := by
    apply pathComb_spine_adj (γ := γ)
    apply pathGraph_adj.mpr
    exact Or.inl (by change k - 1 + 1 = k + 0; omega)
  let e : (pathComb γ L).coe.edgeSet := ⟨s(a,f r), hadj⟩
  obtain ⟨u, v, he, hP, _⟩ := hPaths e
  have hPair : s(a,f r) = s(u,v) := he
  have hBoundary : IsGraphPathWithEnds D (P e) (c a) (c (f r)) := by
    rcases Sym2.eq_iff.mp hPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hP
    · exact hP.symm
  have haOutside : a ∉ range f := by
    intro ha
    have h := (mem_range_combShiftEmbedding_iff k (by omega) a).mp ha
    change k ≤ k - 1 ∧ k - 1 < k + m at h
    omega
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hMeet : V(P e) ∩ combSegmentSupport c P k (by omega : k + m ≤ L) = {c (f r)} :=
    selected_subdivision_boundary_intersection f hf hc P hRanges
      (fun e f hne ↦ (hInter e f hne).1) r a haOutside e rfl
  have hFirst := combSegment_model hk c hc hcentres P hPaths hInter 0 (by omega : 0 + k ≤ L)
  have hdis := disjoint_combSegmentSupports hc P hRanges (fun e f hne ↦ (hInter e f hne).1)
    0 k (by omega : 0 + k ≤ L) (by omega : k + m ≤ L) (by omega)
  have haFirst : c a ∈ combSegmentSupport c P 0 (by omega : 0 + k ≤ L) := by
    apply (mem_combSegmentSupport_iff c P 0 (by omega) _).mpr
    exact Or.inl ⟨a, Nat.zero_le _, by change k - 1 < 0 + k; omega, rfl⟩
  have hbLast : c (f r) ∈ combSegmentSupport c P k (by omega : k + m ≤ L) :=
    Or.inl (mem_range_self r)
  have hcover := comb_subdivision_split_cover hk hm hsum c P hV e (by rfl)
  exact connected_complement_of_terminal_piece hFirst.1 hFirst.2.1 hdis haFirst hbLast
    hBoundary hMeet hcover

end GraphMinor.GM01
