module

public import GraphMinor.Compute.Case3Block
public import GraphMinor.Compute.Specs9
public import GraphMinor.Compute.Algorithm86
import GraphMinor.Compute.Algorithm33MultiComb

/-!
# Compass Society Extraction and Explicit (8.6) Division Characterization for Step 5 of (9.9)

This file implements compass society extraction and merged division characterization for
**Graph Minors XIII, Algorithm (9.9), Step 5** (page 105):
1. **Iterated Vertex Deletion and Automatic Disjointness from `X'`:**
   Proves `(G.deleteVertices Z).deleteVertices X = G.deleteVertices (X ∪ Z)` and shows that for any
   valid wall `W : WallOfHeight h (G.deleteVertices X')` (`2 ≤ h`), every vertex of `W.vertexFinset`
   and every vertex of `W.compassFinset` is incident to an edge of `(G.deleteVertices X').toSimpleGraph`
   and therefore automatically lies outside `X'`. Consequently,
   `GM13.wallCompass (delGraph G X') (W.toGMWall h2 he hW)` has vertex set `W.compassFinset.toNatSet`
   and equals `GM13.wallCompass (G.deleteVertices X').toGMDigraph.toGraph (W.toGMWall h2 he hW)`, and
   `W.IsFlatWall h2` implies `GM13.IsFlatWallIn (delGraph G X') (W.toGMWall h2 he hW)`.
2. **Canonical Compass Lists (`case3KVList`, `case3KEList`, `case3Corners`):**
   Constructs the canonical sorted compass vertex list `case3KVList W`, compass edge-triple list
   `case3KEList D_del W`, and corner list `case3Corners W h2`, and proves that
   `subgraphOfLists (delGraph G X') (case3KVList W) (case3KEList D_del W)` equals
   `GM13.wallCompass (delGraph G X') (W.toGMWall h2 he hW)`.
3. **Compact Simple Compass Society (`case3Alg81Input`):**
   Constructs the compact `Alg81Input` on `Fin (W.compassFinset.card)` via
   `W.compassFinset.orderEmbOfFin rfl`, proves that `W.IsFlatWall h2` implies
   `¬ HasCrossInSociety` and `¬ GM13.HasCross`, proves that no raw member is of Type (iii)
   (`¬ IsAlg86TypeIII`), and bounds `alg81Size` by `(n + 1) * (D_del.numEdges + n + 1)`.
4. **Explicit Characterization of Merged (8.6) Division Members (`mergedMemberOfBoundary`):**
   For any 4-linked core `(Z, C)` of a cross-free society without isolated corners, proves that
   every raw member `A ∈ alg86RawDivision x Z` satisfies `alg86Boundary x A = A.verts ∩ Z`, and
   every merged member `B ∈ alg86Division x Z` is uniquely determined by its boundary
   `bd = B.verts ∩ Z` via `mergedMemberOfBoundary x Z bd`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Graph GraphMinor.Surface GraphMinor.GM09 Classical
open scoped BigOperators Graph

/-! ### Section 1: Iterated Vertex Deletion and Automatic Disjointness of Valid Walls from `X'` -/

/-- Deleting `Z` and then `X` from `G : MultiDigraph n` is identical to deleting `X ∪ Z`. -/
@[simp]
theorem MultiDigraph.deleteVertices_deleteVertices {n : ℕ}
    (G : MultiDigraph n) (Z X : Finset (Fin n)) :
    (G.deleteVertices Z).deleteVertices X = G.deleteVertices (X ∪ Z) := by
  ext u v
  simp only [MultiDigraph.deleteVertices_edgeMult, Finset.mem_union, not_or]
  by_cases huX : u ∈ X <;> by_cases hvX : v ∈ X <;>
    by_cases huZ : u ∈ Z <;> by_cases hvZ : v ∈ Z <;>
    simp [huX, hvX, huZ, hvZ]

/-- Any two adjacent vertices in `(G.deleteVertices X').toSimpleGraph` lie outside `X'`. -/
theorem MultiDigraph.not_mem_of_toSimpleGraph_adj_deleteVertices {n : ℕ}
    {G : MultiDigraph n} {X' : Finset (Fin n)} {u v : Fin n}
    (hadj : (G.deleteVertices X').toSimpleGraph.Adj u v) :
    u ∉ X' ∧ v ∉ X' := by
  rw [MultiDigraph.toSimpleGraph_adj, MultiDigraph.deleteVertices_edgeMult,
    MultiDigraph.deleteVertices_edgeMult] at hadj
  rcases hadj with ⟨_, h1 | h2⟩
  · split_ifs at h1 with h
    · exact h
    · omega
  · split_ifs at h2 with h
    · exact ⟨h.2, h.1⟩
    · omega

namespace WallOfHeight

variable {h n : ℕ} {D_del : MultiDigraph n}

/-- Every coordinate in `GM13.elementaryWallVerts h` (`2 ≤ h`) is incident to some elementary wall
edge in `elemWallEdges h`. -/
theorem exists_mem_elemWallEdges_of_branchIdx (h2 : 2 ≤ h) (u : Fin (elemWallNumVerts h)) :
    ∃ v : Fin (elemWallNumVerts h),
      (u, v) ∈ elemWallEdges h ∨ (v, u) ∈ elemWallEdges h := by
  let p := elemWallVertCoord h u
  have hp : p ∈ GM13.elementaryWallVerts h := elemWallVertCoord_mem_elementaryWallVerts h u
  rcases hp with ⟨hx_le, hy_le, hne_00, hne_top⟩
  have hex_q : ∃ q : ℕ × ℕ, ∃ hq : q ∈ GM13.elementaryWallVerts h,
      isElemWallEdgeCoord p q = true ∨ isElemWallEdgeCoord q p = true := by
    by_cases hx0 : p.1 = 0
    · have hy_pos : 1 ≤ p.2 := by
        by_contra hlt
        exact hne_00 (Prod.ext hx0 (by omega))
      refine ⟨(1, p.2), mem_elementaryWallVerts_of_bounds (by omega) (by omega) hy_le, Or.inl ?_⟩
      unfold isElemWallEdgeCoord
      simp [hx0]
    · by_cases hp10 : p = (1, 0)
      · refine ⟨(2, 0), mem_elementaryWallVerts_of_bounds (by omega) (by omega) (by omega), Or.inl ?_⟩
        unfold isElemWallEdgeCoord
        simp [hp10]
      · refine ⟨(p.1 - 1, p.2), ?_, Or.inr ?_⟩
        · refine ⟨by omega, hy_le, ?_, ?_⟩
          · intro h0
            have hx1 : p.1 - 1 = 0 := congrArg Prod.fst h0
            have hy0 : p.2 = 0 := congrArg Prod.snd h0
            exact hp10 (Prod.ext (by omega) hy0)
          · intro htop
            have : p.1 - 1 = 2 * h + 1 := congrArg Prod.fst htop
            omega
        · unfold isElemWallEdgeCoord
          dsimp only
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
          exact Or.inl ⟨trivial, by omega⟩
  rcases hex_q with ⟨q, hq, hedge⟩
  let v := elemWallCoordIdx h q hq
  have hv : elemWallVertCoord h v = q := elemWallVertCoord_elemWallCoordIdx h hq
  refine ⟨v, ?_⟩
  rw [mem_elemWallEdges_iff, mem_elemWallEdges_iff, hv]
  exact hedge

/-- Every vertex in `W.subdivPathVerts k` is incident to a wall edge of `W`. -/
theorem exists_isWallEdge_of_mem_subdivPathVerts (W : WallOfHeight h D_del)
    {k : Fin (elemWallEdges h).length} {v : Fin n} (hv : v ∈ W.subdivPathVerts k) :
    ∃ w : Fin n, W.IsWallEdge v w := by
  let e := (elemWallEdges h)[k.1]'k.2
  have hdef : W.subdivPathVerts k = W.branchVert e.1 :: (W.internalVerts k ++ [W.branchVert e.2]) :=
    rfl
  have hlen : 2 ≤ (W.subdivPathVerts k).length := by
    rw [hdef]
    simp
  rcases List.mem_iff_getElem.mp hv with ⟨i, hi, rfl⟩
  by_cases hi1 : i + 1 < (W.subdivPathVerts k).length
  · exact ⟨(W.subdivPathVerts k)[i + 1]'hi1, W.isWallEdge_subdivPathVerts_getElem k i hi1⟩
  · have hi_pos : 0 < i := by omega
    have hi_prev : (i - 1) + 1 < (W.subdivPathVerts k).length := by omega
    have hwe := (W.isWallEdge_subdivPathVerts_getElem k (i - 1) hi_prev).symm
    have heq : (i - 1) + 1 = i := by omega
    simp only [heq] at hwe
    exact ⟨(W.subdivPathVerts k)[i - 1]'(by omega), hwe⟩

/-- Every vertex in `W.vertexFinset` (`2 ≤ h`) is incident to a wall edge of `W`. -/
theorem exists_isWallEdge_of_mem_vertexFinset (W : WallOfHeight h D_del) (h2 : 2 ≤ h)
    {v : Fin n} (hv : v ∈ W.vertexFinset) :
    ∃ w : Fin n, W.IsWallEdge v w := by
  rw [W.mem_vertexFinset_iff] at hv
  rcases hv with ⟨u, rfl⟩ | ⟨k, hvk⟩
  · rcases exists_mem_elemWallEdges_of_branchIdx h2 u with ⟨u', hmem | hmem⟩
    · rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, hget⟩
      let k : Fin (elemWallEdges h).length := ⟨idx, hidx⟩
      have hmem_p : W.branchVert u ∈ W.subdivPathVerts k := by
        rw [W.mem_subdivPathVerts_iff k]
        left
        have hk : ((elemWallEdges h)[k.1]'k.2).1 = u := congrArg Prod.fst hget
        rw [hk]
      exact W.exists_isWallEdge_of_mem_subdivPathVerts hmem_p
    · rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, hget⟩
      let k : Fin (elemWallEdges h).length := ⟨idx, hidx⟩
      have hmem_p : W.branchVert u ∈ W.subdivPathVerts k := by
        rw [W.mem_subdivPathVerts_iff k]
        right; right
        have hk : ((elemWallEdges h)[k.1]'k.2).2 = u := congrArg Prod.snd hget
        rw [hk]
      exact W.exists_isWallEdge_of_mem_subdivPathVerts hmem_p
  · exact W.exists_isWallEdge_of_mem_subdivPathVerts
      ((W.mem_subdivPathVerts_iff k v).mpr (Or.inr (Or.inl hvk)))

/-- Every vertex in `W.compassFinset` (`2 ≤ h`, `W.IsValid`) is adjacent to some vertex in
`D_del.toSimpleGraph`. -/
theorem exists_adj_of_mem_compassFinset {W : WallOfHeight h D_del} (h2 : 2 ≤ h) (hW : W.IsValid)
    {v : Fin n} (hv : v ∈ W.compassFinset) :
    ∃ w : Fin n, D_del.toSimpleGraph.Adj v w := by
  rw [W.compassFinset_eq_reachSet_seedVert h2 hW, Finset.mem_union, mem_reachSet] at hv
  rcases hv with hvP | hreach
  · rcases W.exists_isWallEdge_of_mem_vertexFinset h2 (W.perimeterFinset_subset_vertexFinset hvP) with
      ⟨w, hwe⟩
    exact ⟨w, hwe.adj_toSimpleGraph hW⟩
  · rcases hreach.symm with ⟨walk⟩
    cases walk with
    | nil =>
      have hsW : W.seedVert h2 ∈ W.vertexFinset :=
        Finset.sdiff_subset (W.seedVert_mem_insideFinset h2 hW)
      rcases W.exists_isWallEdge_of_mem_vertexFinset h2 hsW with ⟨w, hwe⟩
      exact ⟨w, hwe.adj_toSimpleGraph hW⟩
    | @cons _ b _ hadj _ =>
      rw [restrictGraph_adj] at hadj
      exact ⟨b, hadj.2.2⟩

/-- For any valid wall `W : WallOfHeight h D_del` (`2 ≤ h`) with `G.deleteVertices X' = D_del`,
every vertex of `W.vertexFinset` lies outside `X'`. -/
theorem not_mem_of_mem_vertexFinset_of_deleteVertices {G : MultiDigraph n} {X' : Finset (Fin n)}
    {W : WallOfHeight h D_del} (h2 : 2 ≤ h) (hW : W.IsValid)
    (hD : G.deleteVertices X' = D_del) {v : Fin n} (hv : v ∈ W.vertexFinset) :
    v ∉ X' := by
  rcases W.exists_isWallEdge_of_mem_vertexFinset h2 hv with ⟨w, hwe⟩
  have hadj : (G.deleteVertices X').toSimpleGraph.Adj v w := by
    rw [hD]
    exact hwe.adj_toSimpleGraph hW
  exact (G.not_mem_of_toSimpleGraph_adj_deleteVertices hadj).1

/-- For any valid wall `W : WallOfHeight h D_del` (`2 ≤ h`) with `G.deleteVertices X' = D_del`,
every vertex of `W.compassFinset` lies outside `X'`. -/
theorem not_mem_of_mem_compassFinset_of_deleteVertices {G : MultiDigraph n} {X' : Finset (Fin n)}
    {W : WallOfHeight h D_del} (h2 : 2 ≤ h) (hW : W.IsValid)
    (hD : G.deleteVertices X' = D_del) {v : Fin n} (hv : v ∈ W.compassFinset) :
    v ∉ X' := by
  rcases W.exists_adj_of_mem_compassFinset h2 hW hv with ⟨w, hadj⟩
  rw [← hD] at hadj
  exact (G.not_mem_of_toSimpleGraph_adj_deleteVertices hadj).1

theorem disjoint_vertexFinset_of_deleteVertices {G : MultiDigraph n} {X' : Finset (Fin n)}
    {W : WallOfHeight h D_del} (h2 : 2 ≤ h) (hW : W.IsValid)
    (hD : G.deleteVertices X' = D_del) :
    Disjoint W.vertexFinset X' :=
  Finset.disjoint_left.mpr fun _ hv => W.not_mem_of_mem_vertexFinset_of_deleteVertices h2 hW hD hv

theorem disjoint_compassFinset_of_deleteVertices {G : MultiDigraph n} {X' : Finset (Fin n)}
    {W : WallOfHeight h D_del} (h2 : 2 ≤ h) (hW : W.IsValid)
    (hD : G.deleteVertices X' = D_del) :
    Disjoint W.compassFinset X' :=
  Finset.disjoint_left.mpr fun _ hv => W.not_mem_of_mem_compassFinset_of_deleteVertices h2 hW hD hv

/-- In `D_del = G.deleteVertices X'`, avoiding `X'` in the compass reachability changes nothing,
so `W.compassFinsetAvoid X' = W.compassFinset`. -/
theorem compassFinsetAvoid_eq_compassFinset_of_deleteVertices
    {G : MultiDigraph n} {X' : Finset (Fin n)}
    {W : WallOfHeight h D_del} (h2 : 2 ≤ h) (hW : W.IsValid)
    (hD : G.deleteVertices X' = D_del) :
    W.compassFinsetAvoid X' = W.compassFinset := by
  have hdisj : Disjoint X' W.vertexFinset :=
    (W.disjoint_vertexFinset_of_deleteVertices h2 hW hD).symm
  rw [W.compassFinsetAvoid_eq_reachSet_seedVert h2 hW hdisj,
    W.compassFinset_eq_reachSet_seedVert h2 hW]
  have hres :
      restrictGraph D_del.toSimpleGraph (Finset.univ \ (X' ∪ W.perimeterFinset)) =
        restrictGraph D_del.toSimpleGraph (Finset.univ \ W.perimeterFinset) := by
    ext u v
    simp only [restrictGraph_adj, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      not_or]
    constructor
    · rintro ⟨⟨_, huP⟩, ⟨_, hvP⟩, hadj⟩
      exact ⟨huP, hvP, hadj⟩
    · rintro ⟨huP, hvP, hadj⟩
      have hadj' : (G.deleteVertices X').toSimpleGraph.Adj u v := by rwa [hD]
      obtain ⟨huX, hvX⟩ := G.not_mem_of_toSimpleGraph_adj_deleteVertices hadj'
      exact ⟨⟨huX, huP⟩, ⟨hvX, hvP⟩, hadj⟩
  rw [hres]

/-- For `G.deleteVertices X' = D_del`, the vertex set of `GM13.wallCompass (delGraph G X')` is
`W.compassFinset.toNatSet`. -/
theorem wallCompassVerts_delGraph_eq {G : MultiDigraph n} {X' : Finset (Fin n)}
    {W : WallOfHeight h D_del} (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hD : G.deleteVertices X' = D_del) :
    GM13.wallCompassVerts (delGraph G X') (W.toGMWall h2 he hW) =
      W.compassFinset.toNatSet := by
  have hdisj : Disjoint X' W.vertexFinset :=
    (W.disjoint_vertexFinset_of_deleteVertices h2 hW hD).symm
  have hval := W.val_compassFinsetAvoid_eq_wallCompassVerts h2 he hW X' hdisj
  rw [W.compassFinsetAvoid_eq_compassFinset_of_deleteVertices h2 hW hD] at hval
  have hdel :
      GM09.deleteVertices D_del.toGMDigraph.toGraph (Fin.val '' (X' : Set (Fin n))) =
        delGraph G X' := by
    change GM09.deleteVertices D_del.toGMDigraph.toGraph X'.toNatSet =
      ((G.deleteVertices X').toGMDigraph.deleteVertices X'.toNatSet).toGraph
    rw [hD, GM13.deleteVertices_toGraph_eq]
  rw [← hdel]
  exact hval.symm

/-- For `G.deleteVertices X' = D_del`, `GM13.wallCompass (delGraph G X') (W.toGMWall h2 he hW)`
is identical to `GM13.wallCompass D_del.toGMDigraph.toGraph (W.toGMWall h2 he hW)`. -/
theorem wallCompass_delGraph_eq_wallCompass_toGMDigraph
    {G : MultiDigraph n} {X' : Finset (Fin n)}
    {W : WallOfHeight h D_del} (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hD : G.deleteVertices X' = D_del) :
    GM13.wallCompass (delGraph G X') (W.toGMWall h2 he hW) =
      GM13.wallCompass D_del.toGMDigraph.toGraph (W.toGMWall h2 he hW) := by
  have hV₁ := W.wallCompassVerts_delGraph_eq h2 he hW hD
  have hV₂ := (W.val_compassFinset_eq_wallCompassVerts h2 he hW).symm
  change (delGraph G X').induce (GM13.wallCompassVerts (delGraph G X') (W.toGMWall h2 he hW)) =
    D_del.toGMDigraph.toGraph.induce
      (GM13.wallCompassVerts D_del.toGMDigraph.toGraph (W.toGMWall h2 he hW))
  rw [hV₁, hV₂]
  refine Graph.ext rfl fun e x y => ?_
  rw [Graph.induce_isLink, Graph.induce_isLink]
  refine and_congr_left fun ⟨hx, hy⟩ => ?_
  have hsub : delGraph G X' ≤ D_del.toGMDigraph.toGraph := by
    unfold delGraph
    rw [hD]
    exact GM13.Digraph.IsSubdigraph.toGraph_le (D_del.toGMDigraph.deleteVertices_isSubdigraph _)
  constructor
  · exact fun hl => hl.mono hsub
  · intro hl
    have he_mem : e ∈ E(delGraph G X') := by
      rw [edgeSet_delGraph, hD]
      exact hl.edge_mem
    exact (hsub.isLink_iff he_mem).mpr hl

/-- Package a valid `W : WallOfHeight h D_del` (`2 ≤ h`, `Even h`, `G.deleteVertices X' = D_del`)
into a `ParsedWallSection D_del X'`. -/
def toParsedWallSection {G : MultiDigraph n} {X' : Finset (Fin n)}
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hD : G.deleteVertices X' = D_del) :
    ParsedWallSection D_del X' where
  h := h
  h2 := h2
  he := he
  W := W
  hW := hW
  branch_not_mem u :=
    W.not_mem_of_mem_vertexFinset_of_deleteVertices h2 hW hD
      ((W.mem_vertexFinset_iff _).mpr (Or.inl ⟨u, rfl⟩))
  internal_not_mem k _ hv :=
    W.not_mem_of_mem_vertexFinset_of_deleteVertices h2 hW hD
      ((W.mem_vertexFinset_iff _).mpr (Or.inr ⟨k, hv⟩))

/-- If `W : WallOfHeight h D_del` satisfies `W.IsFlatWall h2` and `G.deleteVertices X' = D_del`,
then `W.toGMWall h2 he hW` is a flat wall in `delGraph G X'`. -/
theorem isFlatWallIn_delGraph_of_isFlatWall {G : MultiDigraph n} {X' : Finset (Fin n)}
    {W : WallOfHeight h D_del} (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hflat : W.IsFlatWall h2) (hD : G.deleteVertices X' = D_del) :
    GM13.IsFlatWallIn (delGraph G X') (W.toGMWall h2 he hW) := by
  have hflat_gm := (W.isFlatWall_iff_toGMWall h2 he hW).mp hflat
  refine ⟨?_, ?_⟩
  · subst hD
    exact (W.toParsedWallSection h2 he hW rfl).toGMWall_le_delGraph
  · rw [W.wallCompass_delGraph_eq_wallCompass_toGMDigraph h2 he hW hD]
    exact hflat_gm.2

end WallOfHeight

/-! ### Section 2: Canonical `case3KVList`, `case3KEList`, `case3Corners`, and `wallCompass` -/

/-- Canonical sorted list of vertex indices `< n` in `W.compassFinset`. -/
noncomputable def case3KVList {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) :
    List ℕ :=
  ((List.finRange n).filter (· ∈ W.compassFinset)).map Fin.val

/-- Canonical list of directed edge triples `(u, v, k)` in `D_del` with both endpoints in
`W.compassFinset`. -/
noncomputable def case3KEList {h n : ℕ} (D_del : MultiDigraph n) (W : WallOfHeight h D_del) :
    List (ℕ × ℕ × ℕ) :=
  ((List.finRange n).filter (· ∈ W.compassFinset)).flatMap (fun u =>
    ((List.finRange n).filter (· ∈ W.compassFinset)).flatMap (fun v =>
      (List.range (D_del.edgeMult u v)).map (fun k => (u.1, v.1, k))))

/-- Canonical 4-element corner list `[c_0, c_1, c_2, c_3]` of `W`. -/
def case3Corners {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) (h2 : 2 ≤ h) :
    List ℕ :=
  List.ofFn (fun i : Fin 4 => (W.branchVert (elemWallCornerIdx h2 i)).1)

@[simp]
theorem mem_case3KVList_iff {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (v : ℕ) :
    v ∈ case3KVList W ↔ ∃ u ∈ W.compassFinset, u.1 = v := by
  simp [case3KVList]

theorem mem_case3KVList_iff_fin {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (u : Fin n) :
    u.1 ∈ case3KVList W ↔ u ∈ W.compassFinset := by
  rw [mem_case3KVList_iff]
  exact ⟨fun ⟨w, hw, heq⟩ => Fin.ext heq ▸ hw, fun hu => ⟨u, hu, rfl⟩⟩

theorem nodup_case3KVList {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) :
    (case3KVList W).Nodup :=
  ((List.nodup_finRange n).filter _).map Fin.val_injective

@[simp]
theorem length_case3KVList {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) :
    (case3KVList W).length = W.compassFinset.card := by
  unfold case3KVList
  rw [List.length_map, length_filter_finRange_eq_card]

theorem length_case3KVList_le {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) :
    (case3KVList W).length ≤ n := by
  rw [length_case3KVList]
  exact (Finset.card_le_univ _).trans (by simp)

theorem case3KVList_valid {h n : ℕ} {G D_del : MultiDigraph n} {X' : Finset (Fin n)}
    {W : WallOfHeight h D_del} (h2 : 2 ≤ h) (hW : W.IsValid)
    (hD : G.deleteVertices X' = D_del) :
    ∀ v ∈ case3KVList W, isDelGraphVert n X' v = true := by
  intro v hv
  rcases (mem_case3KVList_iff W v).mp hv with ⟨u, hu, rfl⟩
  unfold isDelGraphVert
  rw [dite_eq_left u.2, decide_eq_true_eq]
  exact W.not_mem_of_mem_compassFinset_of_deleteVertices h2 hW hD hu

@[simp]
theorem mem_case3KEList_iff {h n : ℕ} (D_del : MultiDigraph n) (W : WallOfHeight h D_del)
    (e : ℕ × ℕ × ℕ) :
    e ∈ case3KEList D_del W ↔
      e ∈ D_del.toGMDigraph.edgeSet ∧ e.1 ∈ case3KVList W ∧ e.2.1 ∈ case3KVList W := by
  rcases e with ⟨a, b, k⟩
  unfold case3KEList
  simp only [List.mem_flatMap, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
    List.mem_map, List.mem_range, Prod.mk.injEq, MultiDigraph.toGMDigraph,
    Set.mem_ofPred_eq, mem_case3KVList_iff]
  constructor
  · rintro ⟨u, huK, v, hvK, k', hk', rfl, rfl, rfl⟩
    exact ⟨⟨u.2, v.2, hk'⟩, ⟨u, huK, rfl⟩, ⟨v, hvK, rfl⟩⟩
  · rintro ⟨⟨_, _, hk⟩, ⟨u, huK, rfl⟩, ⟨v, hvK, rfl⟩⟩
    exact ⟨u, huK, v, hvK, k, hk, rfl, rfl, rfl⟩

theorem nodup_case3KEList {h n : ℕ} (D_del : MultiDigraph n) (W : WallOfHeight h D_del) :
    (case3KEList D_del W).Nodup := by
  unfold case3KEList
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun v _ => ?_, ?_⟩
    · exact List.nodup_range.map (fun k₁ k₂ h => by injection h with _ h2; injection h2)
    · refine ((List.nodup_finRange n).filter _).pairwise_of_forall_ne
        fun v₁ _ v₂ _ hne e he₁ he₂ => ?_
      simp only [List.mem_map, List.mem_range] at he₁ he₂
      rcases he₁ with ⟨_, _, rfl⟩
      rcases he₂ with ⟨_, _, heq⟩
      injection heq with _ h2
      injection h2 with h21 _
      exact hne (Fin.ext h21.symm)
  · refine ((List.nodup_finRange n).filter _).pairwise_of_forall_ne
      fun u₁ _ u₂ _ hne e he₁ he₂ => ?_
    simp only [List.mem_flatMap, List.mem_filter, List.mem_finRange, true_and,
      List.mem_map, List.mem_range] at he₁ he₂
    rcases he₁ with ⟨v₁, _, _, _, rfl⟩
    rcases he₂ with ⟨v₂, _, _, _, heq⟩
    injection heq with h1 _
    exact hne (Fin.ext h1.symm)

theorem length_case3KEList_le {h n : ℕ} (D_del : MultiDigraph n) (W : WallOfHeight h D_del) :
    (case3KEList D_del W).length ≤ D_del.numEdges := by
  unfold case3KEList MultiDigraph.numEdges
  have hsum_finRange : ∀ f : Fin n → ℕ,
      ((List.finRange n).map f).sum = ∑ u : Fin n, f u := by
    intro f
    rw [← Fin.sum_univ_def]
  rw [List.length_flatMap]
  refine (((List.filter_sublist (l := List.finRange n)).map _).sum_le_sum
    (fun _ _ => Nat.zero_le _)).trans ?_
  rw [hsum_finRange]
  refine Finset.sum_le_sum fun u _ => ?_
  rw [List.length_flatMap]
  refine (((List.filter_sublist (l := List.finRange n)).map _).sum_le_sum
    (fun _ _ => Nat.zero_le _)).trans ?_
  rw [hsum_finRange]
  refine Finset.sum_le_sum fun v _ => ?_
  simp

theorem case3KEList_valid {h n : ℕ} (D_del : MultiDigraph n) (W : WallOfHeight h D_del) :
    ∀ e ∈ case3KEList D_del W,
      isDelGraphEdge D_del e = true ∧ e.1 ∈ case3KVList W ∧ e.2.1 ∈ case3KVList W := by
  intro e he
  rw [mem_case3KEList_iff] at he
  exact ⟨isDelGraphEdge_eq_true_iff_mem_toGMDigraph.mpr he.1, he.2.1, he.2.2⟩

theorem WallOfHeight.perimeterFinset_subset_compassFinset {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) {v : Fin n} (hv : v ∈ W.perimeterFinset) :
    v ∈ W.compassFinset := by
  rw [W.compassFinset_eq_compassFinsetAvoid_empty]
  unfold WallOfHeight.compassFinsetAvoid
  rw [Finset.mem_union]
  exact Or.inl hv

theorem case3Corners_mem_case3KVList {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) :
    ∀ c ∈ case3Corners W h2, c ∈ case3KVList W := by
  intro c hc
  unfold case3Corners at hc
  rw [List.mem_ofFn] at hc
  rcases hc with ⟨i, rfl⟩
  rw [mem_case3KVList_iff_fin]
  exact W.perimeterFinset_subset_compassFinset (W.cornerVert_mem_perimeterFinset h2 he i)

/-- For `G.deleteVertices X' = D_del`, `subgraphOfLists` of `case3KVList W` and
`case3KEList D_del W` in `delGraph G X'` equals `GM13.wallCompass (delGraph G X') (W.toGMWall h2 he hW)`. -/
theorem subgraphOfLists_case3KVList_case3KEList_eq_wallCompass
    {h n : ℕ} {G D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hD : G.deleteVertices X' = D_del) :
    subgraphOfLists (delGraph G X') (case3KVList W) (case3KEList D_del W) =
      GM13.wallCompass (delGraph G X') (W.toGMWall h2 he hW) := by
  have hK_le : GM13.wallCompass (delGraph G X') (W.toGMWall h2 he hW) ≤ delGraph G X' := by
    have hW_in : GM13.IsWallIn (delGraph G X') (W.toGMWall h2 he hW) := by
      subst hD
      exact (W.toParsedWallSection h2 he hW rfl).toGMWall_le_delGraph
    exact GM13.wallCompass_le hW_in
  have hV_verts : {v : ℕ | v ∈ case3KVList W} =
      GM13.wallCompassVerts (delGraph G X') (W.toGMWall h2 he hW) := by
    rw [W.wallCompassVerts_delGraph_eq h2 he hW hD]
    ext v
    simp [mem_case3KVList_iff, Finset.toNatSet]
  have hV : {v : ℕ | v ∈ case3KVList W} =
      V(GM13.wallCompass (delGraph G X') (W.toGMWall h2 he hW)) :=
    hV_verts
  refine subgraphOfLists_eq_of_vertexSet_edgeSet hK_le hV ?_
  ext e
  simp only [Set.mem_ofPred_eq, mem_case3KEList_iff]
  change (e ∈ D_del.toGMDigraph.edgeSet ∧ e.1 ∈ case3KVList W ∧ e.2.1 ∈ case3KVList W) ↔
    e ∈ E((delGraph G X').induce (GM13.wallCompassVerts (delGraph G X') (W.toGMWall h2 he hW)))
  rw [← hV_verts, edgeSet_induce]
  constructor
  · rintro ⟨heD, he1, he2⟩
    refine ⟨e.1, e.2.1, ?_, he1, he2⟩
    rw [delGraph_eq]
    have he_del : e ∈ (G.toGMDigraph.deleteVertices X'.toNatSet).edgeSet := by
      rw [← G.toGMDigraph_deleteVertices_edgeSet_eq X', hD]
      exact heD
    exact ⟨he_del, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨x, y, hl, hx, hy⟩
    have hl_D : D_del.toGMDigraph.toGraph.IsLink e x y := by
      have hsub : delGraph G X' ≤ D_del.toGMDigraph.toGraph := by
        unfold delGraph
        rw [hD]
        exact GM13.Digraph.IsSubdigraph.toGraph_le (D_del.toGMDigraph.deleteVertices_isSubdigraph _)
      exact hl.mono hsub
    rcases hl_D with ⟨heD, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨heD, hy, hx⟩
    · exact ⟨heD, hx, hy⟩

/-! ### Section 3: Compact Compass Society `case3Alg81Input` on `Fin (W.compassFinset.card)` -/

/-- Number of vertices `m = |V(K)|` in the compass of `W`. -/
noncomputable def compassCard {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) : ℕ :=
  W.compassFinset.card

/-- Order embedding `Fin (compassCard W) ↪o Fin n` enumerating `W.compassFinset` in increasing order. -/
noncomputable def compassEmb {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del) :
    Fin (compassCard W) ↪o Fin n :=
  W.compassFinset.orderEmbOfFin rfl

@[simp]
theorem compassEmb_mem_compassFinset {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (u : Fin (compassCard W)) :
    compassEmb W u ∈ W.compassFinset :=
  Finset.orderEmbOfFin_mem W.compassFinset rfl u

@[simp]
theorem compassEmb_val_mem_case3KVList {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (u : Fin (compassCard W)) :
    (compassEmb W u).1 ∈ case3KVList W :=
  (mem_case3KVList_iff_fin W (compassEmb W u)).mpr (compassEmb_mem_compassFinset W u)

/-- For any `S : Finset (Fin n)`, `(List.finRange n).filter (· ∈ S)` equals
`(List.finRange S.card).map (S.orderEmbOfFin rfl)`. -/
theorem filter_finRange_eq_map_orderEmbOfFin {n : ℕ} (S : Finset (Fin n)) :
    (List.finRange n).filter (· ∈ S) =
      (List.finRange S.card).map (S.orderEmbOfFin rfl) := by
  refine (List.Pairwise.eq_of_mem_iff (r := (· < ·)) ?_ ?_ ?_).symm
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp fun h => (S.orderEmbOfFin rfl).lt_iff_lt.mpr h
  · exact (List.pairwise_lt_finRange n).filter _
  · intro u
    simp only [List.mem_map, List.mem_finRange, true_and, List.mem_filter, decide_eq_true_eq]
    simp only [← Set.mem_range, Finset.range_orderEmbOfFin, Finset.mem_coe]

theorem mem_range_compassEmb_iff {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)
    (u : Fin n) :
    (∃ i, compassEmb W i = u) ↔ u ∈ W.compassFinset := by
  have h := Finset.range_orderEmbOfFin W.compassFinset (rfl : W.compassFinset.card = compassCard W)
  have hu : u ∈ Set.range (compassEmb W) ↔ u ∈ (W.compassFinset : Set (Fin n)) := by
    exact (congrArg (fun S : Set (Fin n) => u ∈ S) h).to_iff
  simpa using hu

theorem map_compassEmb_val_eq_case3KVList {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) :
    (List.finRange (compassCard W)).map (fun u => (compassEmb W u).1) = case3KVList W := by
  unfold case3KVList compassEmb compassCard
  rw [filter_finRange_eq_map_orderEmbOfFin, List.map_map]
  rfl

/-- Underlying simple graph on `Fin (compassCard W)` induced by `D_del.toSimpleGraph` via
`compassEmb W`. -/
noncomputable def compactCompassGraph {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) : SimpleGraph (Fin (compassCard W)) :=
  D_del.toSimpleGraph.comap (compassEmb W)

noncomputable instance instDecidableRelCompactCompassGraphAdj {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) :
    DecidableRel (compactCompassGraph D_del W).Adj := by
  intro u v
  change Decidable (D_del.toSimpleGraph.Adj (compassEmb W u) (compassEmb W v))
  infer_instance

@[simp]
theorem compactCompassGraph_adj {h n : ℕ} (D_del : MultiDigraph n) (W : WallOfHeight h D_del)
    (u v : Fin (compassCard W)) :
    (compactCompassGraph D_del W).Adj u v ↔
      D_del.toSimpleGraph.Adj (compassEmb W u) (compassEmb W v) :=
  Iff.rfl

/-- Pullback of the `i`-th corner `W.cornerVert h2 i` into `Fin (compassCard W)`. -/
noncomputable def compactCorner {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (i : Fin 4) :
    Fin (compassCard W) :=
  have hmem : ∃ u, compassEmb W u = W.cornerVert h2 i :=
    (mem_range_compassEmb_iff W _).mpr
      (W.perimeterFinset_subset_compassFinset (W.cornerVert_mem_perimeterFinset h2 he i))
  hmem.choose

@[simp]
theorem compassEmb_compactCorner {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (i : Fin 4) :
    compassEmb W (compactCorner W h2 he i) = W.cornerVert h2 i := by
  have hmem : ∃ u, compassEmb W u = W.cornerVert h2 i :=
    (mem_range_compassEmb_iff W _).mpr
      (W.perimeterFinset_subset_compassFinset (W.cornerVert_mem_perimeterFinset h2 he i))
  exact hmem.choose_spec

theorem compactCorner_injective {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    Function.Injective (compactCorner W h2 he) := by
  intro i j hij
  have hc := congrArg (compassEmb W) hij
  rw [compassEmb_compactCorner, compassEmb_compactCorner] at hc
  exact W.cornerVert_injective h2 hW hc

/-- The compact `Alg81Input` on `Fin (compassCard W)` representing the simple compass society of `W`
in `D_del`. -/
noncomputable def case3Alg81Input {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    Alg81Input where
  n := compassCard W
  G := compactCompassGraph D_del W
  decAdj := instDecidableRelCompactCompassGraphAdj D_del W
  omega := List.ofFn (compactCorner W h2 he)
  nodup_omega := List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW)

@[simp]
theorem case3Alg81Input_n {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (case3Alg81Input D_del W h2 he hW).n = compassCard W :=
  rfl

@[simp]
theorem case3Alg81Input_G {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (case3Alg81Input D_del W h2 he hW).G = compactCompassGraph D_del W :=
  rfl

@[simp]
theorem case3Alg81Input_omega {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (case3Alg81Input D_del W h2 he hW).omega = List.ofFn (compactCorner W h2 he) :=
  rfl

theorem isSimpleWalkList_map_compassEmb {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) {a b : Fin (compassCard W)}
    (p : (compactCompassGraph D_del W).Walk a b) :
    WallOfHeight.IsSimpleWalkList D_del (p.support.map (compassEmb W)) := by
  induction p with
  | nil => trivial
  | @cons u v w hadj rest ih =>
    change WallOfHeight.IsSimpleWalkList D_del
      (compassEmb W u :: (rest.support.map (compassEmb W)))
    cases hrest : rest.support with
    | nil => exact False.elim (SimpleGraph.Walk.support_ne_nil rest hrest)
    | cons y ys =>
      have hy : y = v := by
        have hhead := SimpleGraph.Walk.head_support rest
        simpa [hrest] using hhead
      subst hy
      rw [hrest] at ih
      exact ⟨hadj, ih⟩

/-- If `W.IsFlatWall h2`, then the compact compass society `case3Alg81Input D_del W h2 he hW` has no
cross (`¬ HasCrossInSociety`). -/
theorem not_hasCrossInSociety_case3Alg81Input {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hflat : W.IsFlatWall h2) :
    ¬ HasCrossInSociety (case3Alg81Input D_del W h2 he hW).G
        (case3Alg81Input D_del W h2 he hW).omega := by
  change ¬ HasCrossInSociety (compactCompassGraph D_del W) (List.ofFn (compactCorner W h2 he))
  rintro ⟨p₁, p₂, q₁, q₂, P, Q, hP, hQ, hdisj, i₁, i₂, i₃, i₄, h1, h2_lt, h3, h4, hcases⟩
  have hlen : (List.ofFn (compactCorner W h2 he)).length = 4 :=
    List.length_ofFn
  have hi : i₁ = 0 ∧ i₂ = 1 ∧ i₃ = 2 ∧ i₄ = 3 := by omega
  rcases hi with ⟨rfl, rfl, rfl, rfl⟩
  have hc0 : (List.ofFn (compactCorner W h2 he))[0] = compactCorner W h2 he 0 :=
    List.getElem_ofFn (f := compactCorner W h2 he) (i := 0) (h := by omega)
  have hc1 : (List.ofFn (compactCorner W h2 he))[1] = compactCorner W h2 he 1 :=
    List.getElem_ofFn (f := compactCorner W h2 he) (i := 1) (h := by omega)
  have hc2 : (List.ofFn (compactCorner W h2 he))[2] = compactCorner W h2 he 2 :=
    List.getElem_ofFn (f := compactCorner W h2 he) (i := 2) (h := by omega)
  have hc3 : (List.ofFn (compactCorner W h2 he))[3] = compactCorner W h2 he 3 :=
    List.getElem_ofFn (f := compactCorner W h2 he) (i := 3) (h := by omega)
  rw [hc0, hc1, hc2, hc3] at hcases
  -- Standardize P, Q to connect (0, 2) and (1, 3)
  have hex_std :
      ∃ (Q₁ : (compactCompassGraph D_del W).Walk (compactCorner W h2 he 0) (compactCorner W h2 he 2))
        (Q₂ : (compactCompassGraph D_del W).Walk (compactCorner W h2 he 1) (compactCorner W h2 he 3)),
        Q₁.IsPath ∧ Q₂.IsPath ∧ List.Disjoint Q₁.support Q₂.support := by
    rcases hcases with ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
        ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨P, Q, hP, hQ, hdisj⟩
    · refine ⟨P, Q.reverse, hP, hQ.reverse, ?_⟩
      rw [SimpleGraph.Walk.support_reverse]
      exact by simpa only [List.disjoint_reverse_left, List.disjoint_reverse_right] using hdisj
    · refine ⟨P.reverse, Q, hP.reverse, hQ, ?_⟩
      rw [SimpleGraph.Walk.support_reverse]
      exact by simpa only [List.disjoint_reverse_left, List.disjoint_reverse_right] using hdisj
    · refine ⟨P.reverse, Q.reverse, hP.reverse, hQ.reverse, ?_⟩
      rw [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_reverse]
      exact by simpa only [List.disjoint_reverse_left, List.disjoint_reverse_right] using hdisj
    · exact ⟨Q, P, hQ, hP, hdisj.symm⟩
    · refine ⟨Q, P.reverse, hQ, hP.reverse, ?_⟩
      rw [SimpleGraph.Walk.support_reverse]
      exact by simpa only [List.disjoint_reverse_left, List.disjoint_reverse_right] using hdisj.symm
    · refine ⟨Q.reverse, P, hQ.reverse, hP, ?_⟩
      rw [SimpleGraph.Walk.support_reverse]
      exact by simpa only [List.disjoint_reverse_left, List.disjoint_reverse_right] using hdisj.symm
    · refine ⟨Q.reverse, P.reverse, hQ.reverse, hP.reverse, ?_⟩
      rw [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_reverse]
      exact by simpa only [List.disjoint_reverse_left, List.disjoint_reverse_right] using hdisj.symm
  rcases hex_std with ⟨Q₁, Q₂, hQ₁, hQ₂, hQ_disj⟩
  have hne₁ : Q₁.support.map (compassEmb W) ≠ [] :=
    by
      intro hnil
      exact SimpleGraph.Walk.support_ne_nil Q₁ (List.map_eq_nil_iff.mp hnil)
  have hne₂ : Q₂.support.map (compassEmb W) ≠ [] :=
    by
      intro hnil
      exact SimpleGraph.Walk.support_ne_nil Q₂ (List.map_eq_nil_iff.mp hnil)
  apply hflat.2
  refine ⟨Q₁.support.map (compassEmb W), Q₂.support.map (compassEmb W),
    { ne_nil₁ := hne₁
      ne_nil₂ := hne₂
      nodup₁ := hQ₁.support_nodup.map (compassEmb W).injective
      nodup₂ := hQ₂.support_nodup.map (compassEmb W).injective
      isWalk₁ := isSimpleWalkList_map_compassEmb D_del W Q₁
      isWalk₂ := isSimpleWalkList_map_compassEmb D_del W Q₂
      head₁ := by
        rw [List.head_map, SimpleGraph.Walk.head_support, compassEmb_compactCorner]
      getLast₁ := by
        rw [List.getLast_map, SimpleGraph.Walk.getLast_support, compassEmb_compactCorner]
      head₂ := by
        rw [List.head_map, SimpleGraph.Walk.head_support, compassEmb_compactCorner]
      getLast₂ := by
        rw [List.getLast_map, SimpleGraph.Walk.getLast_support, compassEmb_compactCorner]
      disjoint := by
        intro v hv₁ hv₂
        rcases List.mem_map.mp hv₁ with ⟨u₁, hu₁, rfl⟩
        rcases List.mem_map.mp hv₂ with ⟨u₂, hu₂, heq⟩
        exact hQ_disj hu₁ ((compassEmb W).injective heq ▸ hu₂) },
    ?_, ?_⟩
  · intro v hv
    rcases List.mem_map.mp hv with ⟨u, _, rfl⟩
    exact compassEmb_mem_compassFinset W u
  · intro v hv
    rcases List.mem_map.mp hv with ⟨u, _, rfl⟩
    exact compassEmb_mem_compassFinset W u

/-- Every corner vertex in `List.ofFn (compactCorner W h2 he)` has a neighbor in
`compactCompassGraph D_del W`. -/
theorem exists_adj_of_mem_omega_case3Alg81Input {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {u : Fin (compassCard W)}
    (hu : u ∈ List.ofFn (compactCorner W h2 he)) :
    ∃ v : Fin (compassCard W), (compactCompassGraph D_del W).Adj u v := by
  rw [List.mem_ofFn] at hu
  rcases hu with ⟨i, rfl⟩
  obtain ⟨k, hperim_k, hmem_subdiv⟩ :=
    (W.mem_perimeterFinset_iff (W.cornerVert h2 i)).mp (W.cornerVert_mem_perimeterFinset h2 he i)
  have hlen : 2 ≤ (W.subdivPathVerts k).length := by
    change 2 ≤ (W.branchVert _ :: (W.internalVerts k ++ [W.branchVert _])).length
    simp
  rcases List.mem_iff_getElem.mp hmem_subdiv with ⟨idx, hidx, hget⟩
  have hex_nb : ∃ w ∈ W.subdivPathVerts k, W.IsWallEdge (W.cornerVert h2 i) w := by
    by_cases hidx1 : idx + 1 < (W.subdivPathVerts k).length
    · refine ⟨(W.subdivPathVerts k)[idx + 1]'hidx1, List.getElem_mem hidx1, ?_⟩
      rw [← hget]
      exact W.isWallEdge_subdivPathVerts_getElem k idx hidx1
    · have hidx_pos : 0 < idx := by omega
      have hidx_prev : (idx - 1) + 1 < (W.subdivPathVerts k).length := by omega
      have hwe := (W.isWallEdge_subdivPathVerts_getElem k (idx - 1) hidx_prev).symm
      have heq : (idx - 1) + 1 = idx := by omega
      simp only [heq, hget] at hwe
      exact ⟨(W.subdivPathVerts k)[idx - 1]'(by omega), List.getElem_mem (by omega), hwe⟩
  rcases hex_nb with ⟨w, hw_L, hwe⟩
  have hw_perim : w ∈ W.perimeterFinset :=
    (W.mem_perimeterFinset_iff w).mpr ⟨k, hperim_k, hw_L⟩
  have hw_comp : ∃ v, compassEmb W v = w :=
    (mem_range_compassEmb_iff W w).mpr (W.perimeterFinset_subset_compassFinset hw_perim)
  rcases hw_comp with ⟨v, hv_eq⟩
  refine ⟨v, ?_⟩
  change D_del.toSimpleGraph.Adj (compassEmb W (compactCorner W h2 he i)) (compassEmb W v)
  rw [compassEmb_compactCorner, hv_eq]
  exact hwe.adj_toSimpleGraph hW

/-- No subgraph `A` of `case3Alg81Input D_del W h2 he hW` is of Type (iii) (`¬ IsAlg86TypeIII`). -/
theorem not_isAlg86TypeIII_case3Alg81Input {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (A : Alg86Subgraph (case3Alg81Input D_del W h2 he hW).G) :
    ¬ IsAlg86TypeIII (case3Alg81Input D_del W h2 he hW) A := by
  change ¬ ∃ v ∈ (List.ofFn (compactCorner W h2 he)).toFinset,
    (∀ w, ¬ (compactCompassGraph D_del W).Adj v w) ∧ A.verts = {v} ∧ A.graph = ⊥
  rintro ⟨v, hv_om, hiso, _, _⟩
  have hv_mem : v ∈ List.ofFn (compactCorner W h2 he) := List.mem_toFinset.mp hv_om
  rcases exists_adj_of_mem_omega_case3Alg81Input D_del W h2 he hW hv_mem with ⟨w, hadj⟩
  exact hiso w hadj

/-- Size bound: `alg81Size (case3Alg81Input D_del W h2 he hW) ≤ (n + 1) * (D_del.numEdges + n + 1)`. -/
theorem alg81Size_case3Alg81Input_le {h n : ℕ} (D_del : MultiDigraph n)
    (W : WallOfHeight h D_del) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    alg81Size (case3Alg81Input D_del W h2 he hW) ≤ (n + 1) * (D_del.numEdges + n + 1) := by
  have hn_le : (case3Alg81Input D_del W h2 he hW).n ≤ n := by
    change W.compassFinset.card ≤ n
    exact (Finset.card_le_univ _).trans (by simp)
  have he_le : (case3Alg81Input D_del W h2 he hW).G.edgeFinset.card ≤ D_del.numEdges := by
    have hmap : (case3Alg81Input D_del W h2 he hW).G.edgeFinset.card ≤
        D_del.toSimpleGraph.edgeFinset.card := by
      let f : Sym2 (Fin (case3Alg81Input D_del W h2 he hW).n) ↪ Sym2 (Fin n) :=
        ⟨Sym2.map (compassEmb W), Sym2.map.injective (compassEmb W).injective⟩
      have hsub : (case3Alg81Input D_del W h2 he hW).G.edgeFinset.map f ⊆
          D_del.toSimpleGraph.edgeFinset := by
        intro e he_mem
        rcases Finset.mem_map.mp he_mem with ⟨e₀, he₀, rfl⟩
        induction e₀ using Sym2.ind with | _ a b =>
        rw [SimpleGraph.mem_edgeFinset] at he₀ ⊢
        exact he₀
      rw [← Finset.card_map f]
      exact Finset.card_le_card hsub
    have hcard_le : D_del.toSimpleGraph.edgeFinset.card ≤ D_del.numEdges := by
      rw [← length_edgeListOf_eq_card_edgeFinset D_del.toSimpleGraph]
      exact card_edgeFinset_toSimpleGraph_le_numEdges D_del
    exact hmap.trans hcard_le
  unfold alg81Size societySize
  exact Nat.mul_le_mul (by omega) (by omega)

/-! ### Section 4: Explicit Characterization of Merged (8.6) Division Members -/

/-- The outside component of `x.G \ Z` containing `u`. -/
noncomputable def compOutside (x : Alg81Input) (Z : Finset (Fin x.n)) (u : Fin x.n) :
    Finset (Fin x.n) :=
  (Finset.univ \ Z).filter (fun w =>
    (restrictGraph x.G (Finset.univ \ Z)).Reachable u w)

/-- The attachment set `N(K) ∩ Z` in `Z` of the outside component of `u`. -/
noncomputable def attachOf (x : Alg81Input) (Z : Finset (Fin x.n)) (u : Fin x.n) :
    Finset (Fin x.n) :=
  Z.filter (fun z => ∃ w ∈ compOutside x Z u, x.G.Adj w z)

/-- The union of all outside components of `x.G \ Z` whose attachment set in `Z` equals `bd`. -/
noncomputable def outsideOfBoundary (x : Alg81Input) (Z bd : Finset (Fin x.n)) :
    Finset (Fin x.n) :=
  (Finset.univ \ Z).filter (fun u => attachOf x Z u = bd)

theorem isComponentOutsideCore_compOutside (x : Alg81Input) (Z : Finset (Fin x.n))
    {u : Fin x.n} (hu : u ∉ Z) :
    IsComponentOutsideCore x.G Z (compOutside x Z u) := by
  refine ⟨u, hu, fun w => ?_⟩
  simp [compOutside]

theorem mem_compOutside_self (x : Alg81Input) (Z : Finset (Fin x.n))
    {u : Fin x.n} (hu : u ∉ Z) :
    u ∈ compOutside x Z u := by
  simp [compOutside, hu]

theorem compOutside_eq_of_mem {x : Alg81Input} {Z : Finset (Fin x.n)}
    {u v : Fin x.n} (hv : v ∈ compOutside x Z u) :
    compOutside x Z v = compOutside x Z u := by
  have hv' : v ∉ Z ∧ (restrictGraph x.G (Finset.univ \ Z)).Reachable u v := by
    simpa [compOutside] using hv
  have hreach := hv'.2
  ext w
  simp only [compOutside, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact and_congr_right fun _ => ⟨fun h => hreach.trans h, fun h => hreach.symm.trans h⟩

theorem attachOf_eq_of_mem_compOutside {x : Alg81Input} {Z : Finset (Fin x.n)}
    {u v : Fin x.n} (hv : v ∈ compOutside x Z u) :
    attachOf x Z v = attachOf x Z u := by
  unfold attachOf
  rw [compOutside_eq_of_mem hv]

theorem eq_compOutside_of_isComponentOutsideCore {x : Alg81Input} {Z K : Finset (Fin x.n)}
    (hK : IsComponentOutsideCore x.G Z K) {u : Fin x.n} (hu : u ∈ K) :
    K = compOutside x Z u := by
  rcases hK with ⟨v₀, _, hmem⟩
  have hu_reach := ((hmem u).mp hu).2
  ext w
  rw [hmem w]
  simp only [compOutside, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact and_congr_right fun _ =>
    ⟨fun h => hu_reach.symm.trans h, fun h => hu_reach.trans h⟩

theorem outsideOfBoundary_disjoint_Z (x : Alg81Input) (Z bd : Finset (Fin x.n)) :
    Disjoint (outsideOfBoundary x Z bd) Z := by
  rw [Finset.disjoint_left]
  intro u hu
  simp only [outsideOfBoundary, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hu
  exact hu.1

theorem attachOf_subset_Z (x : Alg81Input) (Z : Finset (Fin x.n)) (u : Fin x.n) :
    attachOf x Z u ⊆ Z :=
  Finset.filter_subset _ _

theorem outsideOfBoundary_closed {x : Alg81Input} {Z bd : Finset (Fin x.n)}
    {u v : Fin x.n} (hu : u ∈ outsideOfBoundary x Z bd) (hv : v ∉ Z) (hadj : x.G.Adj u v) :
    v ∈ outsideOfBoundary x Z bd := by
  simp only [outsideOfBoundary, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
    true_and] at hu ⊢
  have hv_comp : v ∈ compOutside x Z u :=
    (isComponentOutsideCore_compOutside x Z hu.1).closed_outside_Z
      (mem_compOutside_self x Z hu.1) hv hadj
  rw [attachOf_eq_of_mem_compOutside hv_comp]
  exact ⟨hv, hu.2⟩

theorem mem_bd_of_adj_outsideOfBoundary {x : Alg81Input} {Z bd : Finset (Fin x.n)}
    {u z : Fin x.n} (hu : u ∈ outsideOfBoundary x Z bd) (hz : z ∈ Z) (hadj : x.G.Adj u z) :
    z ∈ bd := by
  simp only [outsideOfBoundary, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
    true_and] at hu
  rw [← hu.2]
  unfold attachOf
  rw [Finset.mem_filter]
  exact ⟨hz, u, mem_compOutside_self x Z hu.1, hadj⟩

/-- Explicit constructor for the merged (8.6) division member with boundary `bd ⊆ Z`. -/
noncomputable def mergedMemberOfBoundary (x : Alg81Input) (Z bd : Finset (Fin x.n))
    (hbd_sub : bd ⊆ Z) : Alg86Subgraph x.G where
  verts := outsideOfBoundary x Z bd ∪ bd
  graph := {
    Adj := fun a b =>
      x.G.Adj a b ∧
        ((a ∈ outsideOfBoundary x Z bd ∨ b ∈ outsideOfBoundary x Z bd) ∨
          (a ∈ Z ∧ b ∈ Z ∧ bd = {a, b}))
    symm := ⟨by
      intro a b ⟨hadj, hcond⟩
      refine ⟨hadj.symm, ?_⟩
      rcases hcond with (ha | hb) | ⟨haZ, hbZ, hbd⟩
      · exact Or.inl (Or.inr ha)
      · exact Or.inl (Or.inl hb)
      · exact Or.inr ⟨hbZ, haZ, by rw [hbd, Finset.pair_comm]⟩⟩
    loopless := ⟨fun a ⟨hadj, _⟩ => x.G.loopless.irrefl a hadj⟩
  }
  sub := fun _ _ h => h.1
  adj_verts := by
    intro a b ⟨hadj, hcond⟩
    rcases hcond with (ha | hb) | ⟨_, _, hbd⟩
    · refine ⟨Finset.mem_union_left _ ha, ?_⟩
      by_cases hbZ : b ∈ Z
      · exact Finset.mem_union_right _ (mem_bd_of_adj_outsideOfBoundary ha hbZ hadj)
      · exact Finset.mem_union_left _ (outsideOfBoundary_closed ha hbZ hadj)
    · refine ⟨?_, Finset.mem_union_left _ hb⟩
      by_cases haZ : a ∈ Z
      · exact Finset.mem_union_right _ (mem_bd_of_adj_outsideOfBoundary hb haZ hadj.symm)
      · exact Finset.mem_union_left _ (outsideOfBoundary_closed hb haZ hadj.symm)
    · subst hbd
      exact ⟨Finset.mem_union_right _ (by simp), Finset.mem_union_right _ (by simp)⟩

@[simp]
theorem verts_inter_Z_mergedMemberOfBoundary (x : Alg81Input) (Z bd : Finset (Fin x.n))
    (hbd_sub : bd ⊆ Z) :
    (mergedMemberOfBoundary x Z bd hbd_sub).verts ∩ Z = bd := by
  change (outsideOfBoundary x Z bd ∪ bd) ∩ Z = bd
  rw [Finset.union_inter_distrib_right,
    Finset.disjoint_iff_inter_eq_empty.mp (outsideOfBoundary_disjoint_Z x Z bd),
    Finset.empty_union, Finset.inter_eq_left.mpr hbd_sub]

@[simp]
theorem verts_sdiff_Z_mergedMemberOfBoundary (x : Alg81Input) (Z bd : Finset (Fin x.n))
    (hbd_sub : bd ⊆ Z) :
    (mergedMemberOfBoundary x Z bd hbd_sub).verts \ Z = outsideOfBoundary x Z bd := by
  change (outsideOfBoundary x Z bd ∪ bd) \ Z = outsideOfBoundary x Z bd
  rw [Finset.union_sdiff_distrib,
    Finset.sdiff_eq_self_of_disjoint (outsideOfBoundary_disjoint_Z x Z bd),
    Finset.sdiff_eq_empty_iff_subset.mpr hbd_sub, Finset.union_empty]

/-- Under a 4-linked core `(Z, C)` in a cross-free society `x`, every raw member
`A ∈ alg86RawDivision x Z` satisfies `alg86Boundary x A = A.verts ∩ Z`. -/
theorem alg86Boundary_eq_inter_Z_of_mem_raw
    {x : Alg81Input} {Z : Finset (Fin x.n)} {C : SimpleGraph (Fin x.n)}
    (htrace : Alg83Trace x Z C) (h4 : IsFourLinkedCore x.omega Z C)
    (_hnocross : ¬ HasCrossInSociety x.G x.omega)
    {A : Alg86Subgraph x.G} (hA : A ∈ alg86RawDivision x Z) :
    alg86Boundary x A = A.verts ∩ Z := by
  have hcore_gm : GM13.IsFourLinkedCore x.toSociety (toCoreGraph Z C) :=
    isFourLinkedCore_toCoreGraph htrace h4
  have hA_gm : A.toGMGraph ∈ GM13.coreRawDivision x.toSociety (toCoreGraph Z C) :=
    (mem_alg86RawDivision_iff_toGMGraph_mem_coreRawDivision x Z C A).mp hA
  have hbd_gm := (GM13.lemma_8_6_claim_2 hcore_gm hA_gm).symm
  rw [divBoundary_toGMGraph, Alg86Subgraph.vertexSet_toGMGraph, vertexSet_toCoreGraph] at hbd_gm
  exact Finset.coe_inj.mp (by simpa [Finset.coe_inter] using hbd_gm)

/-- Under a 4-linked core `(Z, C)` in a cross-free society `x`, every merged member
`B ∈ alg86Division x Z` satisfies `alg86Boundary x B = B.verts ∩ Z`. -/
theorem alg86Boundary_eq_inter_Z_of_mem_division
    {x : Alg81Input} {Z : Finset (Fin x.n)} {C : SimpleGraph (Fin x.n)}
    (htrace : Alg83Trace x Z C) (h4 : IsFourLinkedCore x.omega Z C)
    (_hnocross : ¬ HasCrossInSociety x.G x.omega)
    {B : Alg86Subgraph x.G} (hB : B ∈ alg86Division x Z) :
    alg86Boundary x B = B.verts ∩ Z := by
  have hcore_gm : GM13.IsFourLinkedCore x.toSociety (toCoreGraph Z C) :=
    isFourLinkedCore_toCoreGraph htrace h4
  have hB_gm : B.toGMGraph ∈ GM13.coreDivision x.toSociety (toCoreGraph Z C) := by
    rw [← image_toGMGraph_alg86Division x Z C]
    exact ⟨B, hB, rfl⟩
  have hbd_gm :=
    (GM13.inter_core_eq_divBoundary_of_mem_coreDivision hcore_gm hB_gm).symm
  rw [divBoundary_toGMGraph, Alg86Subgraph.vertexSet_toGMGraph, vertexSet_toCoreGraph] at hbd_gm
  exact Finset.coe_inj.mp (by simpa [Finset.coe_inter] using hbd_gm)

/-- For any raw member `A₀ ∈ alg86RawDivision x Z` (when there are no Type (iii) members),
the merged member `alg86SubgraphUnion (alg86EquivClass x Z A₀)` equals
`mergedMemberOfBoundary x Z (A₀.verts ∩ Z) Finset.inter_subset_right`. -/
theorem alg86SubgraphUnion_equivClass_eq_mergedMemberOfBoundary
    {x : Alg81Input} {Z : Finset (Fin x.n)} {C : SimpleGraph (Fin x.n)}
    (htrace : Alg83Trace x Z C) (h4 : IsFourLinkedCore x.omega Z C)
    (hnocross : ¬ HasCrossInSociety x.G x.omega)
    (hnoIII : ∀ A : Alg86Subgraph x.G, ¬ IsAlg86TypeIII x A)
    {A₀ : Alg86Subgraph x.G} (hA₀ : A₀ ∈ alg86RawDivision x Z) :
    alg86SubgraphUnion (alg86EquivClass x Z A₀) =
      mergedMemberOfBoundary x Z (A₀.verts ∩ Z) Finset.inter_subset_right := by
  let bd := A₀.verts ∩ Z
  have hbd_A₀ : alg86Boundary x A₀ = bd :=
    alg86Boundary_eq_inter_Z_of_mem_raw htrace h4 hnocross hA₀
  have hclass_iff : ∀ A : Alg86Subgraph x.G,
      A ∈ alg86EquivClass x Z A₀ ↔ A ∈ alg86RawDivision x Z ∧ A.verts ∩ Z = bd := by
    intro A
    unfold alg86EquivClass Alg86BoundaryEquiv
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hA => ?_
    rw [alg86Boundary_eq_inter_Z_of_mem_raw htrace h4 hnocross hA, hbd_A₀]
  have hA₀_class : A₀ ∈ alg86EquivClass x Z A₀ := (hclass_iff A₀).mpr ⟨hA₀, rfl⟩
  ext v w
  · rw [mem_verts_alg86SubgraphUnion]
    change (∃ A ∈ alg86EquivClass x Z A₀, v ∈ A.verts) ↔
      v ∈ outsideOfBoundary x Z bd ∪ bd
    rw [Finset.mem_union]
    constructor
    · rintro ⟨A, hA_cl, hvA⟩
      obtain ⟨hA_raw, hA_bd⟩ := (hclass_iff A).mp hA_cl
      by_cases hvZ : v ∈ Z
      · right
        rw [← hA_bd]
        exact Finset.mem_inter.mpr ⟨hvA, hvZ⟩
      · left
        rcases hA_raw with ⟨u₁, u₂, hu₁Z, hu₂Z, _, hverts, _⟩ |
            ⟨K, hK, hverts, _⟩ | hIII
        · rw [hverts, Finset.mem_insert, Finset.mem_singleton] at hvA
          rcases hvA with rfl | rfl
          · exact False.elim (hvZ hu₁Z)
          · exact False.elim (hvZ hu₂Z)
        · have hvK : v ∈ K := by
            rw [hverts, Finset.mem_union, Finset.mem_filter] at hvA
            rcases hvA with hvK | ⟨hvZ', _⟩
            · exact hvK
            · exact False.elim (hvZ hvZ')
          have hK_eq : K = compOutside x Z v := eq_compOutside_of_isComponentOutsideCore hK hvK
          have hattach_eq : attachOf x Z v = A.verts ∩ Z := by
            rw [hverts, Finset.union_inter_distrib_right,
              Finset.disjoint_iff_inter_eq_empty.mp hK.disjoint_Z, Finset.empty_union,
              Finset.inter_eq_left.mpr (Finset.filter_subset _ _), hK_eq]
            rfl
          simp only [outsideOfBoundary, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
            true_and]
          exact ⟨hvZ, hattach_eq.trans hA_bd⟩
        · exact False.elim (hnoIII A hIII)
    · rintro (hv_out | hv_bd)
      · simp only [outsideOfBoundary, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and] at hv_out
        rcases hv_out with ⟨hvZ, hattach⟩
        have hK : IsComponentOutsideCore x.G Z (compOutside x Z v) :=
          isComponentOutsideCore_compOutside x Z hvZ
        let A := mkAlg86TypeII x Z (compOutside x Z v) hK
        have hA_raw : A ∈ alg86RawDivision x Z :=
          Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z (compOutside x Z v) hK))
        have hA_bd : A.verts ∩ Z = bd := by
          change (compOutside x Z v ∪ attachOf x Z v) ∩ Z = bd
          rw [Finset.union_inter_distrib_right,
            Finset.disjoint_iff_inter_eq_empty.mp hK.disjoint_Z, Finset.empty_union,
            Finset.inter_eq_left.mpr (attachOf_subset_Z x Z v), hattach]
        refine ⟨A, (hclass_iff A).mpr ⟨hA_raw, hA_bd⟩, ?_⟩
        exact Finset.mem_union_left _ (mem_compOutside_self x Z hvZ)
      · exact ⟨A₀, hA₀_class, (Finset.mem_inter.mp hv_bd).1⟩
  · rw [adj_alg86SubgraphUnion]
    change (∃ A ∈ alg86EquivClass x Z A₀, A.graph.Adj v w) ↔
      x.G.Adj v w ∧
        ((v ∈ outsideOfBoundary x Z bd ∨ w ∈ outsideOfBoundary x Z bd) ∨
          (v ∈ Z ∧ w ∈ Z ∧ bd = {v, w}))
    constructor
    · rintro ⟨A, hA_cl, hadjA⟩
      obtain ⟨hA_raw, hA_bd⟩ := (hclass_iff A).mp hA_cl
      have hadjG : x.G.Adj v w := A.sub hadjA
      refine ⟨hadjG, ?_⟩
      rcases hA_raw with ⟨u₁, u₂, hu₁Z, hu₂Z, _, hverts, hadj_iff⟩ |
          ⟨K, hK, hverts, hadj_iff⟩ | hIII
      · right
        rw [hadj_iff] at hadjA
        have hbd_eq : bd = {u₁, u₂} := by
          rw [← hA_bd, hverts, Finset.inter_eq_left.mpr]
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        rcases hadjA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hu₁Z, hu₂Z, hbd_eq⟩
        · exact ⟨hu₂Z, hu₁Z, hbd_eq.trans (Finset.pair_comm w v)⟩
      · left
        rw [hadj_iff, hK.adj_iff_mem_or_mem] at hadjA
        have hK_sub : K ⊆ outsideOfBoundary x Z bd := by
          intro u huK
          have huZ : u ∉ Z := hK.not_mem_Z huK
          have hK_eq : K = compOutside x Z u := eq_compOutside_of_isComponentOutsideCore hK huK
          have hattach_eq : attachOf x Z u = A.verts ∩ Z := by
            rw [hverts, Finset.union_inter_distrib_right,
              Finset.disjoint_iff_inter_eq_empty.mp hK.disjoint_Z, Finset.empty_union,
              Finset.inter_eq_left.mpr (Finset.filter_subset _ _), hK_eq]
            rfl
          simp only [outsideOfBoundary, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
            true_and]
          exact ⟨huZ, hattach_eq.trans hA_bd⟩
        rcases hadjA.2 with hvK | hwK
        · exact Or.inl (hK_sub hvK)
        · exact Or.inr (hK_sub hwK)
      · exact False.elim (hnoIII A hIII)
    · rintro ⟨hadjG, (hv_out | hw_out) | ⟨hvZ, hwZ, hbd_eq⟩⟩
      · simp only [outsideOfBoundary, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and] at hv_out
        have hK : IsComponentOutsideCore x.G Z (compOutside x Z v) :=
          isComponentOutsideCore_compOutside x Z hv_out.1
        let A := mkAlg86TypeII x Z (compOutside x Z v) hK
        have hA_raw : A ∈ alg86RawDivision x Z :=
          Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z (compOutside x Z v) hK))
        have hA_bd : A.verts ∩ Z = bd := by
          change (compOutside x Z v ∪ attachOf x Z v) ∩ Z = bd
          rw [Finset.union_inter_distrib_right,
            Finset.disjoint_iff_inter_eq_empty.mp hK.disjoint_Z, Finset.empty_union,
            Finset.inter_eq_left.mpr (attachOf_subset_Z x Z v), hv_out.2]
        refine ⟨A, (hclass_iff A).mpr ⟨hA_raw, hA_bd⟩, ?_⟩
        exact (hK.adj_iff_mem_or_mem v w).mpr ⟨hadjG, Or.inl (mem_compOutside_self x Z hv_out.1)⟩
      · simp only [outsideOfBoundary, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
          true_and] at hw_out
        have hK : IsComponentOutsideCore x.G Z (compOutside x Z w) :=
          isComponentOutsideCore_compOutside x Z hw_out.1
        let A := mkAlg86TypeII x Z (compOutside x Z w) hK
        have hA_raw : A ∈ alg86RawDivision x Z :=
          Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z (compOutside x Z w) hK))
        have hA_bd : A.verts ∩ Z = bd := by
          change (compOutside x Z w ∪ attachOf x Z w) ∩ Z = bd
          rw [Finset.union_inter_distrib_right,
            Finset.disjoint_iff_inter_eq_empty.mp hK.disjoint_Z, Finset.empty_union,
            Finset.inter_eq_left.mpr (attachOf_subset_Z x Z w), hw_out.2]
        refine ⟨A, (hclass_iff A).mpr ⟨hA_raw, hA_bd⟩, ?_⟩
        exact (hK.adj_iff_mem_or_mem v w).mpr ⟨hadjG, Or.inr (mem_compOutside_self x Z hw_out.1)⟩
      · let A := mkAlg86TypeI x hadjG
        have hA_raw : A ∈ alg86RawDivision x Z :=
          Or.inl (isAlg86TypeI_mkAlg86TypeI x Z hvZ hwZ hadjG)
        have hA_bd : A.verts ∩ Z = bd := by
          change ({v, w} : Finset (Fin x.n)) ∩ Z = bd
          rw [hbd_eq, Finset.inter_eq_left.mpr]
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        refine ⟨A, (hclass_iff A).mpr ⟨hA_raw, hA_bd⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- Predicate stating that `bd : Finset (Fin x.n)` is the boundary `A.verts ∩ Z` of some raw member
`A ∈ alg86RawDivision x Z`, equivalently either `bd = attachOf x Z u` for some `u ∉ Z`, or
`bd = {u, v}` for some core edge `u, v ∈ Z` with `x.G.Adj u v`. -/
def IsRawBoundary (x : Alg81Input) (Z bd : Finset (Fin x.n)) : Prop :=
  (∃ u : Fin x.n, u ∉ Z ∧ attachOf x Z u = bd) ∨
    (∃ u v : Fin x.n, u ∈ Z ∧ v ∈ Z ∧ x.G.Adj u v ∧ bd = {u, v})

theorem isRawBoundary_iff_exists_raw {x : Alg81Input} {Z bd : Finset (Fin x.n)}
    (hnoIII : ∀ A : Alg86Subgraph x.G, ¬ IsAlg86TypeIII x A) :
    IsRawBoundary x Z bd ↔ ∃ A ∈ alg86RawDivision x Z, A.verts ∩ Z = bd := by
  constructor
  · rintro (⟨u, huZ, rfl⟩ | ⟨u, v, huZ, hvZ, hadj, rfl⟩)
    · have hK : IsComponentOutsideCore x.G Z (compOutside x Z u) :=
        isComponentOutsideCore_compOutside x Z huZ
      let A := mkAlg86TypeII x Z (compOutside x Z u) hK
      refine ⟨A, Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z (compOutside x Z u) hK)), ?_⟩
      change (compOutside x Z u ∪ attachOf x Z u) ∩ Z = attachOf x Z u
      rw [Finset.union_inter_distrib_right,
        Finset.disjoint_iff_inter_eq_empty.mp hK.disjoint_Z, Finset.empty_union,
        Finset.inter_eq_left.mpr (attachOf_subset_Z x Z u)]
    · let A := mkAlg86TypeI x hadj
      refine ⟨A, Or.inl (isAlg86TypeI_mkAlg86TypeI x Z huZ hvZ hadj), ?_⟩
      change ({u, v} : Finset (Fin x.n)) ∩ Z = {u, v}
      rw [Finset.inter_eq_left.mpr]
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
  · rintro ⟨A, hA_raw, rfl⟩
    rcases hA_raw with ⟨u, v, huZ, hvZ, hadj, hverts, _⟩ |
        ⟨K, hK, hverts, _⟩ | hIII
    · right
      refine ⟨u, v, huZ, hvZ, hadj, ?_⟩
      rw [hverts, Finset.inter_eq_left.mpr]
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · left
      obtain ⟨u, huK⟩ := hK.nonempty
      have huZ : u ∉ Z := hK.not_mem_Z huK
      have hK_eq : K = compOutside x Z u := eq_compOutside_of_isComponentOutsideCore hK huK
      refine ⟨u, huZ, ?_⟩
      rw [hverts, Finset.union_inter_distrib_right,
        Finset.disjoint_iff_inter_eq_empty.mp hK.disjoint_Z, Finset.empty_union,
        Finset.inter_eq_left.mpr (Finset.filter_subset _ _), hK_eq]
      rfl
    · exact False.elim (hnoIII A hIII)

theorem IsRawBoundary.subset_Z {x : Alg81Input} {Z bd : Finset (Fin x.n)}
    (hbd : IsRawBoundary x Z bd) :
    bd ⊆ Z := by
  rcases hbd with ⟨u, _, rfl⟩ | ⟨u, v, huZ, hvZ, _, rfl⟩
  · exact attachOf_subset_Z x Z u
  · intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption

/-- Characterization of `alg86Division x Z`: its members are exactly
`mergedMemberOfBoundary x Z bd hbd.subset_Z` as `bd` ranges over `IsRawBoundary x Z bd`. -/
theorem mem_alg86Division_iff_exists_isRawBoundary
    {x : Alg81Input} {Z : Finset (Fin x.n)} {C : SimpleGraph (Fin x.n)}
    (htrace : Alg83Trace x Z C) (h4 : IsFourLinkedCore x.omega Z C)
    (hnocross : ¬ HasCrossInSociety x.G x.omega)
    (hnoIII : ∀ A : Alg86Subgraph x.G, ¬ IsAlg86TypeIII x A)
    (B : Alg86Subgraph x.G) :
    B ∈ alg86Division x Z ↔
      ∃ (bd : Finset (Fin x.n)) (hbd : IsRawBoundary x Z bd),
        B = mergedMemberOfBoundary x Z bd hbd.subset_Z := by
  constructor
  · rintro ⟨A₀, hA₀_raw, rfl⟩
    have hbd : IsRawBoundary x Z (A₀.verts ∩ Z) :=
      (isRawBoundary_iff_exists_raw hnoIII).mpr ⟨A₀, hA₀_raw, rfl⟩
    exact ⟨A₀.verts ∩ Z, hbd,
      alg86SubgraphUnion_equivClass_eq_mergedMemberOfBoundary htrace h4 hnocross hnoIII hA₀_raw⟩
  · rintro ⟨bd, hbd, rfl⟩
    obtain ⟨A₀, hA₀_raw, hA₀_bd⟩ := (isRawBoundary_iff_exists_raw hnoIII).mp hbd
    subst hA₀_bd
    exact ⟨A₀, hA₀_raw,
      (alg86SubgraphUnion_equivClass_eq_mergedMemberOfBoundary
        htrace h4 hnocross hnoIII hA₀_raw).symm⟩

end GraphMinor.Compute
