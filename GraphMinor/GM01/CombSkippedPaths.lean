module

public import GraphMinor.GM01.CombBlocks
public import GraphMinor.GM01.CombShifts
public import GraphMinor.GM01.CombTailCentres
public import GraphMinor.GM01.CombPathsOutside
import GraphMinor.GM01.PathsInRegions
import Lean.Elab.Tactic.Omega

/-!
# The two-cell subdivision inside a skipped block

In Graph Minors I, (4.1), page 55, the skipped block supplies two
consecutive spine cells. Shift a two-cell source to that interval.
The earlier cut puts all its centres and paths in the earlier region.
The next cut excludes them from the later region. Root-path invariance
identifies the difference of these two regions with the actual block
of `H`. Thus the selected subdivision lies entirely in that block.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The centres and replacing paths of the two cells in a noninitial,
nonfinal block lie in that block. This is the skipped-block placement
needed for GM01 (4.1), page 55. -/
theorem comb_two_cells_in_block {α β : Type*} {γ L n : ℕ} (hL : 0 < L) (htail : 2 * n ≤ L)
    {G N R : Graph α β} (hN : N ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c) (hcentres : ∀ v, c v ∈ V(N))
    (P : (pathComb γ L).coe.edgeSet → Graph α β) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : α) (hR : IsGraphPathWithEnds G R root (c (rootedPathComb γ L hL).root))
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (j : Fin n) (hj0 : 0 < j.val) (hjn : j.val + 1 < n) :
    (∀ v : (pathComb γ 2).verts,
      c (combShiftEmbedding (2 * j.val) (by omega : 2 * j.val + 2 ≤ L) v) ∈
        combBlock (by omega : 0 < L) (subgraphUnion G N R) c j) ∧
    (∀ e : (pathComb γ 2).coe.edgeSet,
      V(P (combShiftEdges (2 * j.val) (by omega : 2 * j.val + 2 ≤ L) e)) ⊆
        combBlock (by omega : 0 < L) (subgraphUnion G N R) c j) := by
  let offset := 2 * j.val
  have hbound : offset + 2 ≤ L := by dsimp [offset]; omega
  let f := combShiftEmbedding (γ := γ) offset hbound
  let low : Fin L := ⟨offset - 1, by dsimp [offset]; omega⟩
  let high : Fin L := ⟨offset + 1, by dsimp [offset]; omega⟩
  let last : Fin L := ⟨L - 1, by omega⟩
  let A := vertexAvoidanceRegion N
    (c ⟨Sum.inl last, pathComb_spine_mem γ L last⟩)
    (c ⟨Sum.inl low, pathComb_spine_mem γ L low⟩)
  let B := vertexAvoidanceRegion N
    (c ⟨Sum.inl last, pathComb_spine_mem γ L last⟩)
    (c ⟨Sum.inl high, pathComb_spine_mem γ L high⟩)
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hlow : low.val < L - 1 := by dsimp [low, offset]; omega
  have hhigh : high.val < L - 1 := by dsimp [high, offset]; omega
  have hBlock : combBlock (by omega : 0 < L) (subgraphUnion G N R) c j = A \ B := by
    have hjlt : j.val < n := j.isLt
    have hnonzero : 2 * j.val ≠ 0 := by omega
    have hnextzero : 2 * (j.val + 1) ≠ 0 := by omega
    have hjL : 2 * j.val < L := by omega
    have hnextL : 2 * (j.val + 1) < L := by omega
    simp only [combBlock, orderedRegionBlock, hjlt, hjn, ↓reduceIte,
      combSpineRegion, hnonzero, hnextzero, hjL, hnextL, ↓reduceDIte]
    have hindex : 2 * (j.val + 1) - 1 = offset + 1 := by dsimp [offset]; omega
    have hLo := comb_root_path_region_eq hN hR.le hc hPN hE hRanges hInter low last
      hlow (hcentres _) hmeet
    have hHi := comb_root_path_region_eq hN hR.le hc hPN hE hRanges hInter high last
      hhigh (hcentres _) hmeet
    simpa only [A, B, low, high, last, offset, hindex] using congrArg₂ (· \ ·) hLo hHi
  have hIndex : ∀ v : (pathComb γ 2).verts,
      (pathCombSpineIndex (f v).val).val = offset + (pathCombSpineIndex v.val).val := by
    rintro ⟨v, hv⟩
    cases v <;> rfl
  have hAfter : ∀ v : (pathComb γ 2).verts, low.val < (pathCombSpineIndex (f v).val).val := by
    intro v
    rw [hIndex]
    dsimp [low, offset]
    omega
  have hBefore : ∀ v : (pathComb γ 2).verts, (pathCombSpineIndex (f v).val).val ≤ high.val := by
    intro v
    rw [hIndex]
    have hv := (pathCombSpineIndex v.val).isLt
    dsimp [high]
    omega
  have hCentreA : ∀ v : (pathComb γ 2).verts, c (f v) ∈ A := fun v ↦
    comb_subdivision_later_vertex_mem_region hc hcentres hPaths low (f v) (hAfter v)
  have hCentreNotB : ∀ v : (pathComb γ 2).verts, c (f v) ∉ B := fun v ↦
    comb_subdivision_centre_not_mem_later_region hc hPN hE hRanges hInter high hhigh (f v) (hBefore v)
  refine ⟨?_, ?_⟩
  · intro v
    rw [hBlock]
    exact ⟨hCentreA v, hCentreNotB v⟩
  · intro e
    obtain ⟨edge, he⟩ := e
    induction edge using Sym2.inductionOn with
    | hf a b =>
      let e : (pathComb γ 2).coe.edgeSet := ⟨s(a,b), he⟩
      let e' := combShiftEdges offset hbound e
      have hmap : e'.val = s(f a,f b) := combShiftEdges_ends offset hbound rfl
      obtain ⟨a', b', he', hP, _⟩ := hPaths e'
      have hpair : s(f a,f b) = s(a',b') := hmap.symm.trans he'
      have hPab : IsGraphPathWithEnds N (P e') (c (f a)) (c (f b)) := by
        rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hP
        · exact hP.symm
      have hNoCut : c ⟨Sum.inl low, pathComb_spine_mem γ L low⟩ ∉ V(P e') := by
        intro hm
        have hmem := (subdivision_centre_mem_path_iff hc hRanges e'
          ⟨Sum.inl low, pathComb_spine_mem γ L low⟩).mp hm
        rw [hmap, Sym2.mem_iff] at hmem
        rcases hmem with h | h
        · have hv := congrArg (fun z : (pathComb γ L).verts ↦ (pathCombSpineIndex z.val).val) h
          have hlt := hAfter a
          change low.val = (pathCombSpineIndex (f a).val).val at hv
          omega
        · have hv := congrArg (fun z : (pathComb γ L).verts ↦ (pathCombSpineIndex z.val).val) h
          have hlt := hAfter b
          change low.val = (pathCombSpineIndex (f b).val).val at hv
          omega
      have hPA : V(P e') ⊆ A := path_subset_vertexAvoidanceRegion hPab (hCentreA a) hNoCut
      have hPB : Disjoint V(P e') B :=
        comb_subdivision_path_disjoint_later_region hc hPN hE hRanges hInter high hhigh e' (by
          intro v hv
          rw [hmap, Sym2.mem_iff] at hv
          rcases hv with rfl | rfl
          · exact hBefore a
          · exact hBefore b)
      intro x hx
      rw [hBlock]
      exact ⟨hPA hx, fun h ↦ Set.disjoint_left.mp hPB hx h⟩

end GraphMinor.GM01
