module

public import GraphMinor.Compute.Algorithm101
public import GraphMinor.GM13.Section9Subwalls

/-!
# Subwall Inside-Vertex Characterization and Homogeneity Test for Algorithm (10.4)

This file implements the subwall enumeration and homogeneity-testing primitives required by
Graph Minors XIII, Algorithm (10.4) (pages 107–108, proof of (10.3)):

1. **Section 1. Shifted Elementary Wall Predicates and `subwallInsideFinset`:**
   Computable branch-vertex and subdivision-edge predicates (`isSubwallInsideBr`,
   `isSubwallInsideEdge`) characterizing `((W.toGMWall h2 he hW).subwallAt i j h' ...).insideVerts`
   via `wallSubsetInd`, together with the middle-vertex index `subwallMiddle₁Idx`.
2. **Section 2. Subwall Shift Enumeration (`validSubwallShifts`) and Composition:**
   Complete enumeration of even shifts `(di, dj)` for subwalls of height `h₂` inside a subwall of
   height `h₁`, and equality of `insideVerts` between iterated subwalls and `(i₁ + di, j₁ + dj)`
   shifted subwalls of `H`.
3. **Section 3. Computable Folio Coverage (`recordsCoverSubwall`) and Bridge to
   `IsHomogeneousSubwall`:**
   Equivalence between `IsHomogeneousSubwall vOut.toGMVision δ h₂ (blk.toGMWall.subwallAt ...)`
   and `recordsCoverSubwall` across all `(di, dj) ∈ validSubwallShifts h₁ h₂`.
4. **Section 4. Word RAM Gadgets (`hasMatchingMemberInProg`, `checkSubwallCoversProg`,
   `buildSubwallInsideBitSetProg`, `testOneSubwallShiftProg`):**
   Word RAM programs and `Exec` proofs for building subwall inside-vertex bitsets and testing
   whether a shifted subwall `H''` covers all interior member folio codes of `H_s`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-! ### Section 1: Shifted Elementary Wall Predicates and `subwallInsideFinset` -/

/-- Decidable check that `p : ℕ × ℕ` is of the form `GM13.wallShift i j q` for some
`q ∈ GM13.elementaryWallVerts h'`. -/
def isInShiftedElemWall (i j h' : ℕ) (p : ℕ × ℕ) : Bool :=
  decide (i ≤ p.1 ∧ j ≤ p.2 ∧ (p.1 - i, p.2 - j) ∈ elemWallCoords h')

theorem isInShiftedElemWall_eq_true_iff (i j h' : ℕ) (p : ℕ × ℕ) :
    isInShiftedElemWall i j h' p = true ↔
      ∃ q ∈ GM13.elementaryWallVerts h', p = GM13.wallShift i j q := by
  unfold isInShiftedElemWall
  rw [decide_eq_true_eq, mem_elemWallCoords_iff_mem_elementaryWallVerts]
  constructor
  · rintro ⟨hi, hj, hmem⟩
    refine ⟨(p.1 - i, p.2 - j), hmem, ?_⟩
    exact Prod.ext (Nat.sub_add_cancel hi).symm (Nat.sub_add_cancel hj).symm
  · rintro ⟨q, hmem, rfl⟩
    unfold GM13.wallShift
    refine ⟨Nat.le_add_left i q.1, Nat.le_add_left j q.2, ?_⟩
    have hsub : (q.1 + i - i, q.2 + j - j) = q :=
      Prod.ext (Nat.add_sub_cancel q.1 i) (Nat.add_sub_cancel q.2 j)
    rwa [hsub]

/-- Decidable check that `p : ℕ × ℕ` is of the form `GM13.wallShift i j q` for some
`q ∈ GM13.elementaryWallPerimeterVerts h'`. -/
def isInShiftedElemWallPerim (i j h' : ℕ) (p : ℕ × ℕ) : Bool :=
  isInShiftedElemWall i j h' p && isElemWallPerimCoord h' (p.1 - i, p.2 - j)

theorem isInShiftedElemWallPerim_eq_true_iff (i j h' : ℕ) (p : ℕ × ℕ) :
    isInShiftedElemWallPerim i j h' p = true ↔
      ∃ q ∈ GM13.elementaryWallPerimeterVerts h', p = GM13.wallShift i j q := by
  unfold isInShiftedElemWallPerim
  rw [Bool.and_eq_true, isInShiftedElemWall_eq_true_iff]
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hper⟩
    have hsub : ((GM13.wallShift i j q).1 - i, (GM13.wallShift i j q).2 - j) = q :=
      Prod.ext (Nat.add_sub_cancel q.1 i) (Nat.add_sub_cancel q.2 j)
    rw [hsub, isElemWallPerimCoord_eq_true_iff h' hq] at hper
    exact ⟨q, hper, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨q, hq.1, rfl⟩, ?_⟩
    have hsub : ((GM13.wallShift i j q).1 - i, (GM13.wallShift i j q).2 - j) = q :=
      Prod.ext (Nat.add_sub_cancel q.1 i) (Nat.add_sub_cancel q.2 j)
    rwa [hsub, isElemWallPerimCoord_eq_true_iff h' hq.1]

/-- Decidable check that the `k`-th edge of `elemWallEdges h` belongs to the `(i, j)`-shifted
elementary wall of height `h'`. -/
def isSubwallEdge (h i j h' : ℕ) (k : Fin (elemWallEdges h).length) : Bool :=
  let e := (elemWallEdges h)[k.1]'k.2
  isInShiftedElemWall i j h' (elemWallVertCoord h e.1) &&
    isInShiftedElemWall i j h' (elemWallVertCoord h e.2)

/-- Decidable check that the `k`-th edge of `elemWallEdges h` belongs to the perimeter of the
`(i, j)`-shifted elementary wall of height `h'`. -/
def isSubwallPerimEdge (h i j h' : ℕ) (k : Fin (elemWallEdges h).length) : Bool :=
  let e := (elemWallEdges h)[k.1]'k.2
  isInShiftedElemWallPerim i j h' (elemWallVertCoord h e.1) &&
    isInShiftedElemWallPerim i j h' (elemWallVertCoord h e.2)

theorem isSubwallEdge_eq_true_iff {h i j h' : ℕ}
    (h2' : 2 ≤ h') (hle : h' ≤ h) (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    (k : Fin (elemWallEdges h).length) :
    isSubwallEdge h i j h' k = true ↔
      ∃ e₀ ∈ E(GM13.elementaryWall h'),
        elemWallEdgeSym2 h k = Sym2.map (GM13.wallShift i j) e₀ := by
  let e := (elemWallEdges h)[k.1]'k.2
  let p₁ := elemWallVertCoord h e.1
  let p₂ := elemWallVertCoord h e.2
  have hadj : GM13.elementaryWallAdj h p₁ p₂ := elemWallEdge_elementaryWallAdj h k
  unfold isSubwallEdge
  change (isInShiftedElemWall i j h' p₁ && isInShiftedElemWall i j h' p₂) = true ↔
    ∃ e₀ ∈ E(GM13.elementaryWall h'), s(p₁, p₂) = Sym2.map (GM13.wallShift i j) e₀
  rw [Bool.and_eq_true, isInShiftedElemWall_eq_true_iff, isInShiftedElemWall_eq_true_iff]
  constructor
  · rintro ⟨⟨q₁, hq₁, hp₁_eq⟩, ⟨q₂, hq₂, hp₂_eq⟩⟩
    rw [hp₁_eq, hp₂_eq] at hadj
    have hadj' : GM13.elementaryWallAdj h' q₁ q₂ :=
      (GM13.elementaryWallAdj_wallShift_iff h2' hle hi_even hj_even hi_le hj_le hq₁ hq₂).mpr hadj
    exact ⟨s(q₁, q₂), ⟨q₁, q₂, hadj', rfl⟩, by rw [hp₁_eq, hp₂_eq]; rfl⟩
  · rintro ⟨e₀, ⟨q₁, q₂, hadj', rfl⟩, heq⟩
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨q₁, hadj'.1, h1⟩, ⟨q₂, hadj'.2.1, h2⟩⟩
    · exact ⟨⟨q₂, hadj'.2.1, h1⟩, ⟨q₁, hadj'.1, h2⟩⟩

theorem isSubwallPerimEdge_eq_true_iff {h i j h' : ℕ}
    (h2' : 2 ≤ h') (hle : h' ≤ h) (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    (k : Fin (elemWallEdges h).length) :
    isSubwallPerimEdge h i j h' k = true ↔
      ∃ e₀ ∈ E(GM13.elementaryWallPerimeter h'),
        elemWallEdgeSym2 h k = Sym2.map (GM13.wallShift i j) e₀ := by
  let e := (elemWallEdges h)[k.1]'k.2
  let p₁ := elemWallVertCoord h e.1
  let p₂ := elemWallVertCoord h e.2
  have hadj : GM13.elementaryWallAdj h p₁ p₂ := elemWallEdge_elementaryWallAdj h k
  unfold isSubwallPerimEdge
  change (isInShiftedElemWallPerim i j h' p₁ && isInShiftedElemWallPerim i j h' p₂) = true ↔
    ∃ e₀ ∈ E(GM13.elementaryWallPerimeter h'), s(p₁, p₂) = Sym2.map (GM13.wallShift i j) e₀
  rw [Bool.and_eq_true, isInShiftedElemWallPerim_eq_true_iff, isInShiftedElemWallPerim_eq_true_iff]
  constructor
  · rintro ⟨⟨q₁, hq₁, hp₁_eq⟩, ⟨q₂, hq₂, hp₂_eq⟩⟩
    rw [hp₁_eq, hp₂_eq] at hadj
    have hadj' : GM13.elementaryWallAdj h' q₁ q₂ :=
      (GM13.elementaryWallAdj_wallShift_iff h2' hle hi_even hj_even hi_le hj_le hq₁.1 hq₂.1).mpr hadj
    have he₀ : s(q₁, q₂) ∈ E(GM13.elementaryWallPerimeter h') := by
      unfold GM13.elementaryWallPerimeter; rw [edgeSet_induce, Set.mem_ofPred_eq]
      exact ⟨q₁, q₂, ⟨hadj', rfl⟩, hq₁, hq₂⟩
    exact ⟨s(q₁, q₂), he₀, by rw [hp₁_eq, hp₂_eq]; rfl⟩
  · rintro ⟨e₀, he₀, heq⟩
    unfold GM13.elementaryWallPerimeter at he₀
    rw [edgeSet_induce, Set.mem_ofPred_eq] at he₀
    rcases he₀ with ⟨q₁, q₂, ⟨_, rfl⟩, hq₁, hq₂⟩
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨⟨q₁, hq₁, h1⟩, ⟨q₂, hq₂, h2⟩⟩
    · exact ⟨⟨q₂, hq₂, h1⟩, ⟨q₁, hq₁, h2⟩⟩

/-- Decidable check that branch vertex `u : Fin (elemWallNumVerts h)` is an endpoint of at least
one edge satisfying `edgePred`. -/
def isEdgeEndpointBr (h : ℕ) (edgePred : Fin (elemWallEdges h).length → Bool)
    (u : Fin (elemWallNumVerts h)) : Bool :=
  (List.finRange (elemWallEdges h).length).any fun k =>
    edgePred k &&
      decide (((elemWallEdges h)[k.1]'k.2).1 = u ∨ ((elemWallEdges h)[k.1]'k.2).2 = u)

theorem wallSubsetInd_isEdgeEndpointBr_eq_true_iff {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid)
    (edgePred : Fin (elemWallEdges h).length → Bool) (v : Fin n) :
    wallSubsetInd W (isEdgeEndpointBr h edgePred) edgePred v = true ↔
      ∃ k : Fin (elemWallEdges h).length, edgePred k = true ∧ v ∈ W.subdivPathVerts k := by
  rw [wallSubsetInd_eq_true_iff hW]
  constructor
  · rintro (⟨u, rfl, hbr⟩ | ⟨k, hv, hke⟩)
    · unfold isEdgeEndpointBr at hbr
      simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
        decide_eq_true_eq] at hbr
      rcases hbr with ⟨k, hke, h1 | h2⟩
      · exact ⟨k, hke, (W.mem_subdivPathVerts_iff k (W.branchVert u)).mpr (Or.inl (h1.symm ▸ rfl))⟩
      · exact ⟨k, hke, (W.mem_subdivPathVerts_iff k (W.branchVert u)).mpr (Or.inr (Or.inr (h2.symm ▸ rfl)))⟩
    · exact ⟨k, hke, (W.mem_subdivPathVerts_iff k v).mpr (Or.inr (Or.inl hv))⟩
  · rintro ⟨k, hke, hv_sub⟩
    rw [W.mem_subdivPathVerts_iff k] at hv_sub
    rcases hv_sub with rfl | hv_int | rfl
    · exact Or.inl ⟨((elemWallEdges h)[k.1]'k.2).1, rfl,
        List.any_eq_true.mpr ⟨k, List.mem_finRange k, by simp [hke]⟩⟩
    · exact Or.inr ⟨k, hv_int, hke⟩
    · exact Or.inl ⟨((elemWallEdges h)[k.1]'k.2).2, rfl,
        List.any_eq_true.mpr ⟨k, List.mem_finRange k, by simp [hke]⟩⟩

/-- Branch-vertex predicate for `((W.toGMWall ...).subwallAt i j h' ...).insideVerts`. -/
def isSubwallInsideBr (h i j h' : ℕ) (u : Fin (elemWallNumVerts h)) : Bool :=
  isEdgeEndpointBr h (isSubwallEdge h i j h') u &&
    !isEdgeEndpointBr h (isSubwallPerimEdge h i j h') u

/-- Subdivision-edge predicate for `((W.toGMWall ...).subwallAt i j h' ...).insideVerts`. -/
def isSubwallInsideEdge (h i j h' : ℕ) (k : Fin (elemWallEdges h).length) : Bool :=
  isSubwallEdge h i j h' k && !isSubwallPerimEdge h i j h' k

/-- Finset of vertices strictly inside the perimeter of `(W.toGMWall ...).subwallAt i j h' ...`. -/
def subwallInsideFinset {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (i j h' : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n =>
    wallSubsetInd W (isSubwallInsideBr h i j h') (isSubwallInsideEdge h i j h') v = true

theorem mem_subwallInsideFinset_iff {h n : ℕ} {D_del : MultiDigraph n}
    {W : WallOfHeight h D_del} (hW : W.IsValid) (i j h' : ℕ) (v : Fin n) :
    v ∈ subwallInsideFinset W i j h' ↔
      (∃ k : Fin (elemWallEdges h).length,
        isSubwallEdge h i j h' k = true ∧ v ∈ W.subdivPathVerts k) ∧
      ¬ (∃ k : Fin (elemWallEdges h).length,
        isSubwallPerimEdge h i j h' k = true ∧ v ∈ W.subdivPathVerts k) := by
  rw [ ← wallSubsetInd_isEdgeEndpointBr_eq_true_iff hW (isSubwallEdge h i j h') v,
       ← wallSubsetInd_isEdgeEndpointBr_eq_true_iff hW (isSubwallPerimEdge h i j h') v ]
  unfold subwallInsideFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [wallSubsetInd_eq_true_iff hW, wallSubsetInd_eq_true_iff hW, wallSubsetInd_eq_true_iff hW]
  unfold isSubwallInsideBr isSubwallInsideEdge
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro (⟨u, rfl, h1, h2⟩ | ⟨k, hv, h1, h2⟩)
    · refine ⟨Or.inl ⟨u, rfl, h1⟩, ?_⟩
      rintro (⟨u', hu', hp'⟩ | ⟨k', hv', _⟩)
      · have : u' = u := hW.1 hu'
        subst this; rw [h2] at hp'; cases hp'
      · exact hW.2.2.1 k' u hv'
    · refine ⟨Or.inr ⟨k, hv, h1⟩, ?_⟩
      rintro (⟨u', rfl, _⟩ | ⟨k', hv', hp'⟩)
      · exact hW.2.2.1 k u' hv
      · by_cases hkk : k' = k
        · subst hkk; rw [h2] at hp'; cases hp'
        · exact hW.2.2.2 k' k hkk hv' hv
  · rintro ⟨⟨u, rfl, h1⟩ | ⟨k, hv, h1⟩, hnot⟩
    · left
      refine ⟨u, rfl, h1, ?_⟩
      cases hp : isEdgeEndpointBr h (isSubwallPerimEdge h i j h') u
      · rfl
      · exfalso; exact hnot (Or.inl ⟨u, rfl, hp⟩)
    · right
      refine ⟨k, hv, h1, ?_⟩
      cases hp : isSubwallPerimEdge h i j h' k
      · rfl
      · exfalso; exact hnot (Or.inr ⟨k, hv, hp⟩)

private theorem subwallAt_baseIso_edgeEquiv_val {α β : Type*} (W₀ : GM13.Wall α β) (i j h' : ℕ)
    (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ W₀.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W₀.height - 2 * h') (hj_le : j ≤ W₀.height - h')
    (e₀ : E(GM13.elementaryWall h'))
    (heW : Sym2.map (GM13.wallShift i j) e₀.1 ∈ E(GM13.elementaryWall W₀.height)) :
    ((W₀.subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le).baseIso.edgeEquiv e₀).1 =
      (W₀.baseIso.edgeEquiv ⟨Sym2.map (GM13.wallShift i j) e₀.1, heW⟩).1 := rfl

private theorem subwallAt_subdivisionPaths {α β : Type*} (W₀ : GM13.Wall α β) (i j h' : ℕ)
    (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ W₀.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W₀.height - 2 * h') (hj_le : j ≤ W₀.height - h') :
    (W₀.subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le).subdivisionPaths =
      W₀.subdivisionPaths := rfl

private theorem mem_vertexSet_subwallAt_iff {α β : Type*} (W₀ : GM13.Wall α β) (i j h' : ℕ)
    (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ W₀.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W₀.height - 2 * h') (hj_le : j ≤ W₀.height - h') (x : α) :
    x ∈ V((W₀.subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le).graph) ↔
      ∃ (e_sym : Sym2 (ℕ × ℕ)) (_ : e_sym ∈ E(GM13.elementaryWall h'))
        (heW : Sym2.map (GM13.wallShift i j) e_sym ∈ E(GM13.elementaryWall W₀.height)),
        x ∈ V(W₀.subdivisionPaths
          (W₀.baseIso.edgeEquiv ⟨Sym2.map (GM13.wallShift i j) e_sym, heW⟩).1) := by
  let H' := W₀.subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le
  have hh' : 1 ≤ h' := by omega
  have hbase_sub : V(H'.baseGraph) ⊆ ⋃ e ∈ E(H'.baseGraph), V(H'.subdivisionPaths e) := by
    intro y hy
    let q := H'.baseIso.vertexEquiv.symm ⟨y, hy⟩
    have hyq : H'.branchVertex q.1 q.2 = y :=
      congrArg Subtype.val (H'.baseIso.vertexEquiv.apply_symm_apply ⟨y, hy⟩)
    rcases exists_elementaryWallAdj_of_mem hh' q.2 with ⟨q', hadj'⟩
    let e₀ : E(GM13.elementaryWall h') := ⟨s(q.1, q'), q.1, q', hadj', rfl⟩
    let e_b := H'.baseIso.edgeEquiv e₀
    have hlink₀ : (GM13.elementaryWall h').IsLink e₀.1 q.1 q' := ⟨hadj', rfl⟩
    have hlink_b : H'.baseGraph.IsLink e_b.1
        (H'.branchVertex q.1 q.2) (H'.branchVertex q' hadj'.2.1) :=
      (H'.baseIso.isLink_iff (e := e₀) (x := q) (y := ⟨q', hadj'.2.1⟩)).mp hlink₀
    rcases H'.path_of_edge e_b.1 e_b.2 with ⟨u, v, hlink_uv, hpath, _, _⟩
    have hy_mem : y ∈ V(H'.subdivisionPaths e_b.1) := by
      rw [← hyq]
      rcases H'.baseGraph.eq_or_eq_of_isLink_of_isLink hlink_b hlink_uv with rfl | rfl
      · exact hpath.left_mem
      · exact hpath.right_mem
    exact Set.mem_biUnion e_b.2 hy_mem
  change x ∈ V(H'.graph) ↔ _
  rw [H'.vertexSet_eq, Set.union_eq_right.mpr hbase_sub]
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨e_b, he_b, hx⟩
    let e₀ := H'.baseIso.edgeEquiv.symm ⟨e_b, he_b⟩
    have he_b_eq : (H'.baseIso.edgeEquiv e₀).1 = e_b :=
      congrArg Subtype.val (H'.baseIso.edgeEquiv.apply_symm_apply ⟨e_b, he_b⟩)
    rcases e₀ with ⟨e_sym, ⟨q₁, q₂, hadj', rfl⟩⟩
    have hadjW : GM13.elementaryWallAdj W₀.height (GM13.wallShift i j q₁) (GM13.wallShift i j q₂) :=
      (GM13.elementaryWallAdj_wallShift_iff h2' hle hi_even hj_even hi_le hj_le
        hadj'.1 hadj'.2.1).mp hadj'
    have heW : Sym2.map (GM13.wallShift i j) s(q₁, q₂) ∈ E(GM13.elementaryWall W₀.height) :=
      ⟨_, _, hadjW, rfl⟩
    have he_W₀_eq : e_b = (W₀.baseIso.edgeEquiv ⟨Sym2.map (GM13.wallShift i j) s(q₁, q₂), heW⟩).1 := by
      rw [← he_b_eq]
      exact subwallAt_baseIso_edgeEquiv_val W₀ i j h' h2' he' hle hi_even hj_even hi_le hj_le
        ⟨s(q₁, q₂), ⟨q₁, q₂, hadj', rfl⟩⟩ heW
    rw [subwallAt_subdivisionPaths W₀ i j h' h2' he' hle hi_even hj_even hi_le hj_le, he_W₀_eq] at hx
    exact ⟨s(q₁, q₂), ⟨q₁, q₂, hadj', rfl⟩, heW, hx⟩
  · rintro ⟨e_sym, he_sym, heW, hx⟩
    let e₀ : E(GM13.elementaryWall h') := ⟨e_sym, he_sym⟩
    let e_b := H'.baseIso.edgeEquiv e₀
    have he_b_eq : e_b.1 = (W₀.baseIso.edgeEquiv ⟨Sym2.map (GM13.wallShift i j) e_sym, heW⟩).1 :=
      subwallAt_baseIso_edgeEquiv_val W₀ i j h' h2' he' hle hi_even hj_even hi_le hj_le e₀ heW
    refine ⟨e_b.1, e_b.2, ?_⟩
    rwa [subwallAt_subdivisionPaths W₀ i j h' h2' he' hle hi_even hj_even hi_le hj_le, he_b_eq]

private theorem mem_vertexSet_perimeter_subwallAt_iff {α β : Type*} (W₀ : GM13.Wall α β) (i j h' : ℕ)
    (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ W₀.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W₀.height - 2 * h') (hj_le : j ≤ W₀.height - h') (x : α) :
    x ∈ V((W₀.subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le).perimeter) ↔
      ∃ (e_sym : Sym2 (ℕ × ℕ)) (_ : e_sym ∈ E(GM13.elementaryWallPerimeter h'))
        (heW : Sym2.map (GM13.wallShift i j) e_sym ∈ E(GM13.elementaryWall W₀.height)),
        x ∈ V(W₀.subdivisionPaths
          (W₀.baseIso.edgeEquiv ⟨Sym2.map (GM13.wallShift i j) e_sym, heW⟩).1) := by
  let H' := W₀.subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le
  change x ∈ V(H'.perimeter) ↔ _
  unfold GM13.Wall.perimeter
  rw [GM09.vertexSet_subgraphSUnion]
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨P, ⟨e_sym, he_perim, rfl⟩, hx⟩
    have he_elem : e_sym ∈ E(GM13.elementaryWall h') :=
      let ⟨p, q, hpq⟩ := he_perim; ⟨p, q, hpq.1.1, hpq.1.2⟩
    rcases he_elem with ⟨q₁, q₂, hadj', rfl⟩
    have hadjW : GM13.elementaryWallAdj W₀.height (GM13.wallShift i j q₁) (GM13.wallShift i j q₂) :=
      (GM13.elementaryWallAdj_wallShift_iff h2' hle hi_even hj_even hi_le hj_le
        hadj'.1 hadj'.2.1).mp hadj'
    have heW : Sym2.map (GM13.wallShift i j) s(q₁, q₂) ∈ E(GM13.elementaryWall W₀.height) :=
      ⟨_, _, hadjW, rfl⟩
    have he_b_eq :
        (H'.baseIso.edgeEquiv ⟨s(q₁, q₂), ⟨q₁, q₂, hadj', rfl⟩⟩).1 =
          (W₀.baseIso.edgeEquiv ⟨Sym2.map (GM13.wallShift i j) s(q₁, q₂), heW⟩).1 :=
      subwallAt_baseIso_edgeEquiv_val W₀ i j h' h2' he' hle hi_even hj_even hi_le hj_le
        ⟨s(q₁, q₂), ⟨q₁, q₂, hadj', rfl⟩⟩ heW
    rw [subwallAt_subdivisionPaths W₀ i j h' h2' he' hle hi_even hj_even hi_le hj_le, he_b_eq] at hx
    exact ⟨s(q₁, q₂), he_perim, heW, hx⟩
  · rintro ⟨e_sym, he_perim, heW, hx⟩
    have he_elem : e_sym ∈ E(GM13.elementaryWall h') :=
      let ⟨p, q, hpq⟩ := he_perim; ⟨p, q, hpq.1.1, hpq.1.2⟩
    have he_b_eq :
        (H'.baseIso.edgeEquiv ⟨e_sym, he_elem⟩).1 =
          (W₀.baseIso.edgeEquiv ⟨Sym2.map (GM13.wallShift i j) e_sym, heW⟩).1 :=
      subwallAt_baseIso_edgeEquiv_val W₀ i j h' h2' he' hle hi_even hj_even hi_le hj_le
        ⟨e_sym, he_elem⟩ heW
    refine ⟨H'.subdivisionPaths (H'.baseIso.edgeEquiv ⟨e_sym, he_elem⟩).1,
      ⟨e_sym, he_perim, rfl⟩, ?_⟩
    rwa [subwallAt_subdivisionPaths W₀ i j h' h2' he' hle hi_even hj_even hi_le hj_le, he_b_eq]

private theorem ofData_subdivisionPaths_baseIso_edgeEquiv {α β : Type*} {h : ℕ}
    (h2 : 2 ≤ h) (he : Even h) (D : GM13.WallData α β h)
    {e₀ : Sym2 (ℕ × ℕ)} (he₀ : e₀ ∈ E(GM13.elementaryWall h)) :
    (GM13.Wall.ofData h2 he D).subdivisionPaths
      ((GM13.Wall.ofData h2 he D).baseIso.edgeEquiv ⟨e₀, he₀⟩).1 = D.P e₀ :=
  D.pathOf_lab he₀

namespace WallOfHeight

variable {h n : ℕ} {D_del : MultiDigraph n} (W : WallOfHeight h D_del)

theorem toGMWall_subdivisionPaths_edgeEquiv (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {e₀ : Sym2 (ℕ × ℕ)} (he₀ : e₀ ∈ E(GM13.elementaryWall h)) :
    (W.toGMWall h2 he hW).subdivisionPaths
      ((W.toGMWall h2 he hW).baseIso.edgeEquiv ⟨e₀, he₀⟩).1 = W.subdivPathOfSym2 hW e₀ := by
  have hh : 1 ≤ h := by omega
  unfold toGMWall
  rw [ofData_subdivisionPaths_baseIso_edgeEquiv h2 he (W.toWallData hh hW) he₀]
  rfl

/-- `V(((W.toGMWall h2 he hW).subwallAt i j h' ...).graph)` equals the union of
`V(W.subdivPathGraph hW k)` over all `k` with `isSubwallEdge h i j h' k = true`. -/
theorem vertexSet_subwallAt_toGMWall_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    let H' := (W.toGMWall h2 he hW).subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le
    V(H'.graph) =
      {x : ℕ | ∃ v : Fin n,
        (∃ k : Fin (elemWallEdges h).length,
          isSubwallEdge h i j h' k = true ∧ v ∈ W.subdivPathVerts k) ∧ v.1 = x} := by
  intro H'
  ext x
  rw [show H' = (W.toGMWall h2 he hW).subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le from rfl,
      mem_vertexSet_subwallAt_iff (W.toGMWall h2 he hW) i j h' h2' he' hle hi_even hj_even hi_le hj_le x]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e_sym, he_sym, heW, hx⟩
    rw [W.toGMWall_subdivisionPaths_edgeEquiv h2 he hW heW] at hx
    rcases heW with ⟨p₁, p₂, hadjW, hmap_eq⟩
    rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hadjW with ⟨k, hk⟩
    have hk_sym : elemWallEdgeSym2 h k = Sym2.map (GM13.wallShift i j) e_sym := hk.trans hmap_eq.symm
    rw [← hk_sym, W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k] at hx
    simp only [Set.mem_ofPred_eq, List.mem_map] at hx
    rcases hx with ⟨v, hv, rfl⟩
    have hsub_edge : isSubwallEdge h i j h' k = true :=
      (isSubwallEdge_eq_true_iff h2' hle hi_even hj_even hi_le hj_le k).mpr ⟨e_sym, he_sym, hk_sym⟩
    exact ⟨v, ⟨k, hsub_edge, hv⟩, rfl⟩
  · rintro ⟨v, ⟨k, hsub_edge, hv⟩, rfl⟩
    rcases (isSubwallEdge_eq_true_iff h2' hle hi_even hj_even hi_le hj_le k).mp hsub_edge with
      ⟨e_sym, he_sym, hk_eq⟩
    have heW : Sym2.map (GM13.wallShift i j) e_sym ∈ E(GM13.elementaryWall h) := by
      rw [← hk_eq]; exact elemWallEdgeSym2_mem_edgeSet h k
    refine ⟨e_sym, he_sym, heW, ?_⟩
    rw [W.toGMWall_subdivisionPaths_edgeEquiv h2 he hW heW, ← hk_eq,
        W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k]
    exact List.mem_map_of_mem hv

/-- `V(((W.toGMWall h2 he hW).subwallAt i j h' ...).perimeter)` equals the union of
`V(W.subdivPathGraph hW k)` over all `k` with `isSubwallPerimEdge h i j h' k = true`. -/
theorem vertexSet_perimeter_subwallAt_toGMWall_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    let H' := (W.toGMWall h2 he hW).subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le
    V(H'.perimeter) =
      {x : ℕ | ∃ v : Fin n,
        (∃ k : Fin (elemWallEdges h).length,
          isSubwallPerimEdge h i j h' k = true ∧ v ∈ W.subdivPathVerts k) ∧ v.1 = x} := by
  intro H'
  ext x
  rw [show H' = (W.toGMWall h2 he hW).subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le from rfl,
      mem_vertexSet_perimeter_subwallAt_iff (W.toGMWall h2 he hW) i j h' h2' he' hle hi_even hj_even hi_le hj_le x]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e_sym, he_perim, heW, hx⟩
    rw [W.toGMWall_subdivisionPaths_edgeEquiv h2 he hW heW] at hx
    rcases heW with ⟨p₁, p₂, hadjW, hmap_eq⟩
    rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hadjW with ⟨k, hk⟩
    have hk_sym : elemWallEdgeSym2 h k = Sym2.map (GM13.wallShift i j) e_sym := hk.trans hmap_eq.symm
    rw [← hk_sym, W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k] at hx
    simp only [Set.mem_ofPred_eq, List.mem_map] at hx
    rcases hx with ⟨v, hv, rfl⟩
    have hperim_edge : isSubwallPerimEdge h i j h' k = true :=
      (isSubwallPerimEdge_eq_true_iff h2' hle hi_even hj_even hi_le hj_le k).mpr ⟨e_sym, he_perim, hk_sym⟩
    exact ⟨v, ⟨k, hperim_edge, hv⟩, rfl⟩
  · rintro ⟨v, ⟨k, hperim_edge, hv⟩, rfl⟩
    rcases (isSubwallPerimEdge_eq_true_iff h2' hle hi_even hj_even hi_le hj_le k).mp hperim_edge with
      ⟨e_sym, he_perim, hk_eq⟩
    have heW : Sym2.map (GM13.wallShift i j) e_sym ∈ E(GM13.elementaryWall h) := by
      rw [← hk_eq]; exact elemWallEdgeSym2_mem_edgeSet h k
    refine ⟨e_sym, he_perim, heW, ?_⟩
    rw [W.toGMWall_subdivisionPaths_edgeEquiv h2 he hW heW, ← hk_eq,
        W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k]
    exact List.mem_map_of_mem hv

/-- `((W.toGMWall h2 he hW).subwallAt i j h' ...).insideVerts` equals
`(subwallInsideFinset W i j h').toNatSet`. -/
theorem subwallAt_insideVerts_eq_toNatSet (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    ((W.toGMWall h2 he hW).subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le).insideVerts =
      (subwallInsideFinset W i j h').toNatSet := by
  unfold GM13.Wall.insideVerts
  rw [W.vertexSet_subwallAt_toGMWall_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le,
      W.vertexSet_perimeter_subwallAt_toGMWall_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le]
  ext x
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Finset.toNatSet, Set.mem_image, Finset.mem_coe,
    mem_subwallInsideFinset_iff hW]
  constructor
  · rintro ⟨⟨v, h1, rfl⟩, hnot⟩
    exact ⟨v, ⟨h1, fun h2 => hnot ⟨v, h2, rfl⟩⟩, rfl⟩
  · rintro ⟨v, ⟨h1, hnot⟩, rfl⟩
    refine ⟨⟨v, h1, rfl⟩, ?_⟩
    rintro ⟨v', h2, heq⟩
    have : v' = v := Fin.ext heq
    subst this
    exact hnot h2

/-- Branch vertex index in `Fin (elemWallNumVerts h)` of the first middle vertex `middleVertex₁`
of the `(i, j)`-shifted subwall of height `h'`. -/
def subwallMiddle₁Idx {h : ℕ} (i j h' : ℕ)
    (h2' : 2 ≤ h') (hle : h' ≤ h)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') : Fin (elemWallNumVerts h) :=
  elemWallCoordIdx h (GM13.wallShift i j (GM13.elementaryWallMiddle₁ h'))
    (GM13.wallShift_mem_elementaryWallVerts h2' hle hi_le hj_le
      (elementaryWallMiddle₁_mem_elementaryWallVerts h2'))

/-- `((W.toGMWall h2 he hW).subwallAt i j h' ...).middleVertex₁` is the image under `W.branchVert`
of `subwallMiddle₁Idx i j h' h2' hle hi_le hj_le`. -/
@[simp]
theorem subwallAt_middleVertex₁_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    ((W.toGMWall h2 he hW).subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le).middleVertex₁ =
      (W.branchVert (subwallMiddle₁Idx i j h' h2' hle hi_le hj_le)).1 := by
  unfold GM13.Wall.middleVertex₁ subwallMiddle₁Idx
  exact W.toGMWall_branchVertex h2 he hW (GM13.wallShift i j (GM13.elementaryWallMiddle₁ h'))
    (GM13.wallShift_mem_elementaryWallVerts h2' hle hi_le hj_le
      (elementaryWallMiddle₁_mem_elementaryWallVerts h2'))

end WallOfHeight

/-! ### Section 2: Subwall Shift Enumeration (`validSubwallShifts`) and Composition -/

/-- List of all even shifts `(di, dj)` with `di ≤ 2 * h₁ - 2 * h₂` and `dj ≤ h₁ - h₂`. -/
def validSubwallShifts (h₁ h₂ : ℕ) : List (ℕ × ℕ) :=
  (List.range (h₁ - h₂ + 1)).flatMap fun ki =>
    (List.range ((h₁ - h₂) / 2 + 1)).map fun kj =>
      (2 * ki, 2 * kj)

theorem mem_validSubwallShifts_iff {h₁ h₂ : ℕ}
    (he₁ : Even h₁) (he₂ : Even h₂) (hle : h₂ ≤ h₁) (p : ℕ × ℕ) :
    p ∈ validSubwallShifts h₁ h₂ ↔
      Even p.1 ∧ Even p.2 ∧ p.1 ≤ 2 * h₁ - 2 * h₂ ∧ p.2 ≤ h₁ - h₂ := by
  unfold validSubwallShifts
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  rcases he₁ with ⟨m₁, rfl⟩
  rcases he₂ with ⟨m₂, rfl⟩
  constructor
  · rintro ⟨ki, hki, kj, hkj, rfl⟩
    exact ⟨⟨ki, by ring⟩, ⟨kj, by ring⟩, by omega, by omega⟩
  · rintro ⟨⟨ki, h1⟩, ⟨kj, h2⟩, hi_le, hj_le⟩
    refine ⟨ki, by omega, kj, by omega, ?_⟩
    exact Prod.ext (by omega) (by omega)

private theorem subwallAt_induce_baseGraph_eq {α β : Type*}
    (W : GM13.Wall α β) {i₁ j₁ h₁ di dj h₂ : ℕ}
    (h2₁ : 2 ≤ h₁) (he₁ : Even h₁) (hle₁ : h₁ ≤ W.height)
    (hi₁_even : Even i₁) (hj₁_even : Even j₁)
    (hi₁_le : i₁ ≤ 2 * W.height - 2 * h₁) (hj₁_le : j₁ ≤ W.height - h₁)
    (h2₂ : 2 ≤ h₂) (hle₁₂ : h₂ ≤ h₁)
    (hdi_le : di ≤ 2 * h₁ - 2 * h₂) (hdj_le : dj ≤ h₁ - h₂) :
    let W₁ := W.subwallAt i₁ j₁ h₁ h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
    W₁.baseGraph.induce
      ((fun p : GM13.elementaryWallVerts h₁ => (W₁.baseIso.vertexEquiv p).1) ''
        {p : GM13.elementaryWallVerts h₁ |
          ∃ q ∈ GM13.elementaryWallVerts h₂, p.1 = GM13.wallShift di dj q}) =
    W.baseGraph.induce
      ((fun p : GM13.elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : GM13.elementaryWallVerts W.height |
          ∃ q ∈ GM13.elementaryWallVerts h₂, p.1 = GM13.wallShift (i₁ + di) (j₁ + dj) q}) := by
  intro W₁
  have hshift_comm : ∀ q : ℕ × ℕ,
      GM13.wallShift (i₁ + di) (j₁ + dj) q = GM13.wallShift i₁ j₁ (GM13.wallShift di dj q) :=
    fun q => Prod.ext (by dsimp [GM13.wallShift]; omega) (by dsimp [GM13.wallShift]; omega)
  let S₁ : Set α :=
    (fun p : GM13.elementaryWallVerts h₁ => (W₁.baseIso.vertexEquiv p).1) ''
      {p : GM13.elementaryWallVerts h₁ |
        ∃ q ∈ GM13.elementaryWallVerts h₂, p.1 = GM13.wallShift di dj q}
  let S₂ : Set α :=
    (fun p : GM13.elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
      {p : GM13.elementaryWallVerts W.height |
        ∃ q ∈ GM13.elementaryWallVerts h₁, p.1 = GM13.wallShift i₁ j₁ q}
  let S₃ : Set α :=
    (fun p : GM13.elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
      {p : GM13.elementaryWallVerts W.height |
        ∃ q ∈ GM13.elementaryWallVerts h₂, p.1 = GM13.wallShift (i₁ + di) (j₁ + dj) q}
  have hS₁_eq : S₁ = S₃ := by
    ext v
    simp only [S₁, S₃, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨p', hp'⟩, ⟨q, hq, rfl⟩, rfl⟩
      have hpW : GM13.wallShift (i₁ + di) (j₁ + dj) q ∈ GM13.elementaryWallVerts W.height := by
        rw [hshift_comm q]
        exact GM13.wallShift_mem_elementaryWallVerts h2₁ hle₁ hi₁_le hj₁_le hp'
      have hpW' : GM13.wallShift i₁ j₁ (GM13.wallShift di dj q) ∈ GM13.elementaryWallVerts W.height := by
        rwa [← hshift_comm q]
      exact ⟨⟨GM13.wallShift (i₁ + di) (j₁ + dj) q, hpW⟩, ⟨q, hq, rfl⟩,
        congrArg (fun z => (W.baseIso.vertexEquiv z).1)
          (Subtype.ext (hshift_comm q) : (⟨_, hpW⟩ : V(GM13.elementaryWall W.height)) = ⟨_, hpW'⟩)⟩
    · rintro ⟨⟨p, hp⟩, ⟨q, hq, rfl⟩, rfl⟩
      have hp' : GM13.wallShift di dj q ∈ GM13.elementaryWallVerts h₁ :=
        GM13.wallShift_mem_elementaryWallVerts h2₂ hle₁₂ hdi_le hdj_le hq
      have hpW' : GM13.wallShift i₁ j₁ (GM13.wallShift di dj q) ∈ GM13.elementaryWallVerts W.height := by
        rwa [← hshift_comm q]
      exact ⟨⟨GM13.wallShift di dj q, hp'⟩, ⟨q, hq, rfl⟩,
        congrArg (fun z => (W.baseIso.vertexEquiv z).1)
          (Subtype.ext (hshift_comm q).symm : (⟨_, hpW'⟩ : V(GM13.elementaryWall W.height)) = ⟨_, hp⟩)⟩
  have hS₃_sub_S₂ : S₃ ⊆ S₂ := by
    rintro _ ⟨⟨p, hp⟩, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨⟨GM13.wallShift (i₁ + di) (j₁ + dj) q, hp⟩,
      ⟨GM13.wallShift di dj q,
        GM13.wallShift_mem_elementaryWallVerts h2₂ hle₁₂ hdi_le hdj_le hq,
        hshift_comm q⟩, rfl⟩
  change (W.baseGraph.induce S₂).induce S₁ = W.baseGraph.induce S₃
  rw [hS₁_eq]
  refine Graph.ext rfl fun e x y => ?_
  simp only [induce_isLink]
  exact ⟨fun ⟨⟨hl, _, _⟩, hx, hy⟩ => ⟨hl, hx, hy⟩,
    fun ⟨hl, hx, hy⟩ => ⟨⟨hl, hS₃_sub_S₂ hx, hS₃_sub_S₂ hy⟩, hx, hy⟩⟩

/-- Any subwall `W₂` of `W₁ = W.subwallAt i₁ j₁ h₁ ...` has shift `(i₁ + di, j₁ + dj)` in `W` for
some `(di, dj) ∈ validSubwallShifts h₁ W₂.height`, and its `insideVerts` equals
`(W.subwallAt (i₁ + di) (j₁ + dj) W₂.height ...).insideVerts`. -/
theorem exists_validSubwallShift_of_isSubwallOf_subwallAt {α β : Type*}
    {W W₂ : GM13.Wall α β} {i₁ j₁ h₁ : ℕ}
    (h2₁ : 2 ≤ h₁) (he₁ : Even h₁) (hle₁ : h₁ ≤ W.height)
    (hi₁_even : Even i₁) (hj₁_even : Even j₁)
    (hi₁_le : i₁ ≤ 2 * W.height - 2 * h₁) (hj₁_le : j₁ ≤ W.height - h₁)
    (hsub₂ : W₂.IsSubwallOf (W.subwallAt i₁ j₁ h₁ h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le)) :
    let h₂ := W₂.height
    ∃ p ∈ validSubwallShifts h₁ h₂,
      ∃ (hle₂ : h₂ ≤ W.height)
        (hi₂_even : Even (i₁ + p.1)) (hj₂_even : Even (j₁ + p.2))
        (hi₂_le : i₁ + p.1 ≤ 2 * W.height - 2 * h₂)
        (hj₂_le : j₁ + p.2 ≤ W.height - h₂),
        W₂.insideVerts =
          (W.subwallAt (i₁ + p.1) (j₁ + p.2) h₂ W₂.two_le_height W₂.even_height
            hle₂ hi₂_even hj₂_even hi₂_le hj₂_le).insideVerts := by
  intro h₂
  let W₁ := W.subwallAt i₁ j₁ h₁ h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
  have hsub₁ : W₁.IsSubwallOf W :=
    W.subwallAt_isSubwallOf i₁ j₁ h₁ h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
  have hle₁₂ : h₂ ≤ h₁ := hsub₂.height_le
  have hle₂ : h₂ ≤ W.height := le_trans hle₁₂ hle₁
  rcases hsub₂.exists_shift with ⟨di, dj, hdi_ev, hdj_ev, hdi_le, hdj_le, hbv₂, hpaths₂, hbase₂⟩
  change di ≤ 2 * h₁ - 2 * h₂ at hdi_le
  change dj ≤ h₁ - h₂ at hdj_le
  have hp_mem : (di, dj) ∈ validSubwallShifts h₁ h₂ :=
    (mem_validSubwallShifts_iff he₁ W₂.even_height hle₁₂ (di, dj)).mpr
      ⟨hdi_ev, hdj_ev, hdi_le, hdj_le⟩
  have hi₂_even : Even (i₁ + di) := hi₁_even.add hdi_ev
  have hj₂_even : Even (j₁ + dj) := hj₁_even.add hdj_ev
  have hi₂_le : i₁ + di ≤ 2 * W.height - 2 * h₂ := by omega
  have hj₂_le : j₁ + dj ≤ W.height - h₂ := by omega
  have hsub₂W : W₂.IsSubwallOf W := hsub₂.trans hsub₁
  refine ⟨(di, dj), hp_mem, hle₂, hi₂_even, hj₂_even, hi₂_le, hj₂_le, ?_⟩
  have hshift_comm : ∀ q : ℕ × ℕ,
      GM13.wallShift (i₁ + di) (j₁ + dj) q = GM13.wallShift i₁ j₁ (GM13.wallShift di dj q) :=
    fun q => Prod.ext (by dsimp [GM13.wallShift]; omega) (by dsimp [GM13.wallShift]; omega)
  refine (hsub₂W.eq_subwallAt_of_shift hi₂_even hj₂_even hi₂_le hj₂_le ?_ hpaths₂
    (hbase₂.trans (subwallAt_induce_baseGraph_eq W h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
      W₂.two_le_height hle₁₂ hdi_le hdj_le))).2.2.2.2.2
  intro q hq₂ hqW
  have hq₁ : GM13.wallShift di dj q ∈ GM13.elementaryWallVerts h₁ :=
    GM13.wallShift_mem_elementaryWallVerts W₂.two_le_height hle₁₂ hdi_le hdj_le hq₂
  rw [hbv₂ q hq₂ hq₁]
  have hqW' : GM13.wallShift i₁ j₁ (GM13.wallShift di dj q) ∈ GM13.elementaryWallVerts W.height := by
    rwa [← hshift_comm q]
  exact congrArg (fun z => (W.baseIso.vertexEquiv z).1)
    (Subtype.ext (hshift_comm q).symm : (⟨_, hqW'⟩ : V(GM13.elementaryWall W.height)) = ⟨_, hqW⟩)

/-- Conversely, for every `(di, dj) ∈ validSubwallShifts h₁ h₂`, the subwall
`W₁.subwallAt di dj h₂ ...` is a subwall of `W₁` of height `h₂` whose `insideVerts` equals
`(W.subwallAt (i₁ + di) (j₁ + dj) h₂ ...).insideVerts`. -/
theorem exists_isSubwallOf_subwallAt_of_mem_validSubwallShifts {α β : Type*}
    (W : GM13.Wall α β) {i₁ j₁ h₁ h₂ : ℕ}
    (h2₁ : 2 ≤ h₁) (he₁ : Even h₁) (hle₁ : h₁ ≤ W.height)
    (hi₁_even : Even i₁) (hj₁_even : Even j₁)
    (hi₁_le : i₁ ≤ 2 * W.height - 2 * h₁) (hj₁_le : j₁ ≤ W.height - h₁)
    (h2₂ : 2 ≤ h₂) (he₂ : Even h₂) (hle₁₂ : h₂ ≤ h₁)
    {p : ℕ × ℕ} (hp : p ∈ validSubwallShifts h₁ h₂) :
    let W₁ := W.subwallAt i₁ j₁ h₁ h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
    ∃ (W₂ : GM13.Wall α β) (hle₂ : h₂ ≤ W.height)
      (hi₂_even : Even (i₁ + p.1)) (hj₂_even : Even (j₁ + p.2))
      (hi₂_le : i₁ + p.1 ≤ 2 * W.height - 2 * h₂)
      (hj₂_le : j₁ + p.2 ≤ W.height - h₂),
      W₂.IsSubwallOf W₁ ∧ W₂.height = h₂ ∧
      W₂.insideVerts =
        (W.subwallAt (i₁ + p.1) (j₁ + p.2) h₂ h2₂ he₂
          hle₂ hi₂_even hj₂_even hi₂_le hj₂_le).insideVerts := by
  intro W₁
  rcases (mem_validSubwallShifts_iff he₁ he₂ hle₁₂ p).mp hp with
    ⟨hdi_ev, hdj_ev, hdi_le, hdj_le⟩
  let W₂ := W₁.subwallAt p.1 p.2 h₂ h2₂ he₂ hle₁₂ hdi_ev hdj_ev hdi_le hdj_le
  have hsub₂ : W₂.IsSubwallOf W₁ :=
    W₁.subwallAt_isSubwallOf p.1 p.2 h₂ h2₂ he₂ hle₁₂ hdi_ev hdj_ev hdi_le hdj_le
  have hle₂ : h₂ ≤ W.height := le_trans hle₁₂ hle₁
  have hi₂_even : Even (i₁ + p.1) := hi₁_even.add hdi_ev
  have hj₂_even : Even (j₁ + p.2) := hj₁_even.add hdj_ev
  have hi₂_le : i₁ + p.1 ≤ 2 * W.height - 2 * h₂ := by omega
  have hj₂_le : j₁ + p.2 ≤ W.height - h₂ := by omega
  have hsub₁ : W₁.IsSubwallOf W :=
    W.subwallAt_isSubwallOf i₁ j₁ h₁ h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
  have hsub₂W : W₂.IsSubwallOf W := hsub₂.trans hsub₁
  have hshift_comm : ∀ q : ℕ × ℕ,
      GM13.wallShift (i₁ + p.1) (j₁ + p.2) q = GM13.wallShift i₁ j₁ (GM13.wallShift p.1 p.2 q) :=
    fun q => Prod.ext (by dsimp [GM13.wallShift]; omega) (by dsimp [GM13.wallShift]; omega)
  refine ⟨W₂, hle₂, hi₂_even, hj₂_even, hi₂_le, hj₂_le, hsub₂, rfl, ?_⟩
  refine (hsub₂W.eq_subwallAt_of_shift hi₂_even hj₂_even hi₂_le hj₂_le ?_ rfl
    (subwallAt_induce_baseGraph_eq W h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
      h2₂ hle₁₂ hdi_le hdj_le)).2.2.2.2.2
  intro q hq₂ hqW
  have hqW' : GM13.wallShift i₁ j₁ (GM13.wallShift p.1 p.2 q) ∈ GM13.elementaryWallVerts W.height := by
    rwa [← hshift_comm q]
  exact congrArg (fun z => (W.baseIso.vertexEquiv z).1)
    (Subtype.ext (hshift_comm q).symm : (⟨_, hqW'⟩ : V(GM13.elementaryWall W.height)) = ⟨_, hqW⟩)

/-! ### Section 3: Computable Folio Coverage (`recordsCoverSubwall`) and Bridge to `IsHomogeneousSubwall` -/

/-- Decidable check that `m : VisionMemberRecord` is an interior member with `m.vOf ∈ S.toNatSet`. -/
def memberInFinset {n : ℕ} (S : Finset (Fin n)) (m : VisionMemberRecord) : Bool :=
  decide (m.isInterior = 1) && decide (m.vOf ∈ S.image Fin.val)

theorem memberInFinset_eq_true_iff {n : ℕ} (S : Finset (Fin n)) (m : VisionMemberRecord) :
    memberInFinset S m = true ↔ m.isInterior = 1 ∧ m.vOf ∈ S.toNatSet := by
  unfold memberInFinset
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, mem_image_val_iff_mem_toNatSet]

/-- Decidable check that `records` contains some interior member in `S₂` with `folioCode = code`. -/
def hasMatchingMemberIn {n : ℕ} (records : List VisionMemberRecord) (S₂ : Finset (Fin n))
    (code : ℕ) : Bool :=
  records.any (fun m' => memberInFinset S₂ m' && decide (m'.folioCode = code))

/-- Decidable check that every interior member in `S₁` has a matching-folio interior member in `S₂`. -/
def recordsCoverSubwall {n : ℕ} (records : List VisionMemberRecord)
    (S₁ S₂ : Finset (Fin n)) : Bool :=
  records.all (fun m => !memberInFinset S₁ m || hasMatchingMemberIn records S₂ m.folioCode)

theorem memberInFinset_recordAt_eq_true_iff {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    {blk : ParsedCase3Block (G.deleteVertices X') X'} {q δ : ℕ}
    (vOut : ParsedVisionOutput G X' blk q δ) (S : Finset (Fin n))
    (j : Fin blk.members.length) :
    memberInFinset S (vOut.recordAt j) = true ↔
      GM13.IsInteriorMember blk.toGMWall blk.toDivision
        ((blk.members[j.1]'j.2).toSubgraph (delGraph G X')) ∧
      vOut.toGMVision.vOf ((blk.members[j.1]'j.2).toSubgraph (delGraph G X')) ∈ S.toNatSet := by
  let r := blk.members[j.1]'j.2
  have hr : r ∈ blk.members := List.getElem_mem j.2
  have hval := vOut.hrecords_valid j
  change isValidVisionMemberRecord G X' blk q δ vOut.xSeq r (vOut.recordAt j) = true at hval
  unfold isValidVisionMemberRecord at hval
  rw [Bool.and_eq_true] at hval
  rcases hval with ⟨hbase, _⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbase
  have hisInt : (vOut.recordAt j).isInterior = (if isMemberInterior blk.wallSec.W r then 1 else 0) :=
    hbase.1.1.1.1.1
  rw [memberInFinset_eq_true_iff, isInteriorMember_toSubgraph_iff blk hr,
      vOut.toGMVision_vOf_at j, hisInt]
  by_cases hInt : isMemberInterior blk.wallSec.W r = true <;> simp [hInt]

theorem recordsCoverSubwall_eq_true_iff {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    {blk : ParsedCase3Block (G.deleteVertices X') X'} {q δ : ℕ}
    (vOut : ParsedVisionOutput G X' blk q δ)
    (hx_len : vOut.xSeq.length ≤ q)
    (hrep : ∀ (j : Fin blk.members.length)
      (_ : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
      (folioOut : ParsedFolioAndModels
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length) δ),
      parseFolioAndModelsFull
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        δ (vOut.recordAt j).folioWords = some folioOut →
      IsDeltaFolioRep δ
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        folioOut.folio)
    (S₁ S₂ : Finset (Fin n)) :
    recordsCoverSubwall vOut.records S₁ S₂ = true ↔
      ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
        GM13.IsInteriorMember blk.toGMWall blk.toDivision A →
        vOut.toGMVision.vOf A ∈ S₁.toNatSet →
        ∃ A' : Graph ℕ (ℕ × ℕ × ℕ),
          GM13.IsInteriorMember blk.toGMWall blk.toDivision A' ∧
          vOut.toGMVision.vOf A' ∈ S₂.toNatSet ∧
          vOut.toGMVision.HasSameMemberDeltaFolio δ A A' := by
  unfold recordsCoverSubwall hasMatchingMemberIn
  rw [List.all_eq_true]
  constructor
  · intro hall A hIntA hvA
    rcases hIntA.1 with ⟨r, hr, rfl⟩
    rcases List.mem_iff_getElem.mp hr with ⟨idx, hidx, rfl⟩
    let j₁ : Fin blk.members.length := ⟨idx, hidx⟩
    have hm₁_mem : vOut.recordAt j₁ ∈ vOut.records :=
      List.getElem_mem (by rw [vOut.hrecords_len]; exact j₁.2)
    have hm₁_in : memberInFinset S₁ (vOut.recordAt j₁) = true :=
      (memberInFinset_recordAt_eq_true_iff vOut S₁ j₁).mpr ⟨hIntA, hvA⟩
    have hcov := hall (vOut.recordAt j₁) hm₁_mem
    rw [hm₁_in, Bool.not_true, Bool.false_or, List.any_eq_true] at hcov
    rcases hcov with ⟨m₂, hm₂_mem, hm₂_cond⟩
    rcases List.mem_iff_getElem.mp hm₂_mem with ⟨idx₂, hidx₂, rfl⟩
    let j₂ : Fin blk.members.length := ⟨idx₂, by rw [← vOut.hrecords_len]; exact hidx₂⟩
    change (memberInFinset S₂ (vOut.recordAt j₂) &&
      decide ((vOut.recordAt j₂).folioCode = (vOut.recordAt j₁).folioCode)) = true at hm₂_cond
    rw [Bool.and_eq_true, memberInFinset_recordAt_eq_true_iff vOut S₂ j₂, decide_eq_true_eq] at hm₂_cond
    rcases hm₂_cond with ⟨⟨hInt₂, hv₂⟩, hcode_eq⟩
    have hInt₁_bool : isMemberInterior blk.wallSec.W (blk.members[j₁.1]'j₁.2) = true :=
      (isInteriorMember_toSubgraph_iff blk (List.getElem_mem j₁.2)).mp hIntA
    have hInt₂_bool : isMemberInterior blk.wallSec.W (blk.members[j₂.1]'j₂.2) = true :=
      (isInteriorMember_toSubgraph_iff blk (List.getElem_mem j₂.2)).mp hInt₂
    have hsame : vOut.toGMVision.HasSameMemberDeltaFolio δ
        ((blk.members[j₁.1]'j₁.2).toSubgraph (delGraph G X'))
        ((blk.members[j₂.1]'j₂.2).toSubgraph (delGraph G X')) :=
      (vOut.folioCode_eq_iff_hasSameMemberDeltaFolio hx_len hInt₁_bool hInt₂_bool hrep).mp hcode_eq.symm
    exact ⟨(blk.members[j₂.1]'j₂.2).toSubgraph (delGraph G X'), hInt₂, hv₂, hsame⟩
  · intro hcov m₁ hm₁_mem
    rcases List.mem_iff_getElem.mp hm₁_mem with ⟨idx₁, hidx₁, rfl⟩
    let j₁ : Fin blk.members.length := ⟨idx₁, by rw [← vOut.hrecords_len]; exact hidx₁⟩
    change (!memberInFinset S₁ (vOut.recordAt j₁) ||
      vOut.records.any (fun m' =>
        memberInFinset S₂ m' && decide (m'.folioCode = (vOut.recordAt j₁).folioCode))) = true
    by_cases hm₁ : memberInFinset S₁ (vOut.recordAt j₁) = true
    · rw [hm₁, Bool.not_true, Bool.false_or, List.any_eq_true]
      rcases (memberInFinset_recordAt_eq_true_iff vOut S₁ j₁).mp hm₁ with ⟨hInt₁, hv₁⟩
      rcases hcov hInt₁ hv₁ with ⟨A', hInt₂, hv₂, hsame⟩
      rcases hInt₂.1 with ⟨r₂, hr₂, rfl⟩
      rcases List.mem_iff_getElem.mp hr₂ with ⟨idx₂, hidx₂, rfl⟩
      let j₂ : Fin blk.members.length := ⟨idx₂, hidx₂⟩
      have hInt₁_bool : isMemberInterior blk.wallSec.W (blk.members[j₁.1]'j₁.2) = true :=
        (isInteriorMember_toSubgraph_iff blk (List.getElem_mem j₁.2)).mp hInt₁
      have hInt₂_bool : isMemberInterior blk.wallSec.W (blk.members[j₂.1]'j₂.2) = true :=
        (isInteriorMember_toSubgraph_iff blk (List.getElem_mem j₂.2)).mp hInt₂
      have hcode_eq : (vOut.recordAt j₁).folioCode = (vOut.recordAt j₂).folioCode :=
        (vOut.folioCode_eq_iff_hasSameMemberDeltaFolio hx_len hInt₁_bool hInt₂_bool hrep).mpr hsame
      have hm₂_in : memberInFinset S₂ (vOut.recordAt j₂) = true :=
        (memberInFinset_recordAt_eq_true_iff vOut S₂ j₂).mpr ⟨hInt₂, hv₂⟩
      refine ⟨vOut.recordAt j₂, List.getElem_mem (by rw [vOut.hrecords_len]; exact j₂.2), ?_⟩
      simp [hm₂_in, hcode_eq]
    · rw [Bool.not_eq_true] at hm₁
      simp [hm₁]

/-- Characterization of `IsHomogeneousSubwall` for `blk.toGMWall.subwallAt i₁ j₁ h₁ ...` in terms
of `recordsCoverSubwall` over `validSubwallShifts h₁ h₂`. -/
theorem isHomogeneousSubwall_subwallAt_iff_all_validSubwallShifts
    {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    {blk : ParsedCase3Block (G.deleteVertices X') X'} {q δ : ℕ}
    (vOut : ParsedVisionOutput G X' blk q δ)
    (hx_len : vOut.xSeq.length ≤ q)
    (hrep : ∀ (j : Fin blk.members.length)
      (_ : isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true)
      (folioOut : ParsedFolioAndModels
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length) δ),
      parseFolioAndModelsFull
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        δ (vOut.recordAt j).folioWords = some folioOut →
      IsDeltaFolioRep δ
        (tildeAMultiDigraph (vOut.recordAt j).tildeA_vList (vOut.recordAt j).tildeA_eList)
        (prefixRootFinset (vOut.recordAt j).tildeA_vList.length
          ((vOut.recordAt j).sSeq ++ vOut.xSeq).length)
        folioOut.folio)
    (i₁ j₁ h₁ h₂ : ℕ)
    (h2₁ : 2 ≤ h₁) (he₁ : Even h₁) (hle₁ : h₁ ≤ blk.wallSec.h)
    (hi₁_even : Even i₁) (hj₁_even : Even j₁)
    (hi₁_le : i₁ ≤ 2 * blk.wallSec.h - 2 * h₁) (hj₁_le : j₁ ≤ blk.wallSec.h - h₁)
    (h2₂ : 2 ≤ h₂) (he₂ : Even h₂) (hle₁₂ : h₂ ≤ h₁) :
    let H₁ := blk.toGMWall.subwallAt i₁ j₁ h₁ h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
    GM13.IsHomogeneousSubwall vOut.toGMVision δ h₂ H₁ ↔
      ∀ p ∈ validSubwallShifts h₁ h₂,
        recordsCoverSubwall vOut.records
          (subwallInsideFinset blk.wallSec.W i₁ j₁ h₁)
          (subwallInsideFinset blk.wallSec.W (i₁ + p.1) (j₁ + p.2) h₂) = true := by
  intro H₁
  have hH₁_sub : H₁.IsSubwallOf blk.toGMWall :=
    blk.toGMWall.subwallAt_isSubwallOf i₁ j₁ h₁ h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
  have hH₁_in : H₁.insideVerts = (subwallInsideFinset blk.wallSec.W i₁ j₁ h₁).toNatSet :=
    blk.wallSec.W.subwallAt_insideVerts_eq_toNatSet blk.wallSec.h2 blk.wallSec.he blk.wallSec.hW
      i₁ j₁ h₁ h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le
  constructor
  · intro hhom p hp
    rw [recordsCoverSubwall_eq_true_iff vOut hx_len hrep]
    intro A hIntA hvA
    rw [← hH₁_in] at hvA
    rcases exists_isSubwallOf_subwallAt_of_mem_validSubwallShifts blk.toGMWall
        h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le h2₂ he₂ hle₁₂ hp with
      ⟨H₂, hle₂, hi₂_ev, hj₂_ev, hi₂_le, hj₂_le, hsub₂, hheight₂, hin₂⟩
    have hH₂_in :
        (blk.toGMWall.subwallAt (i₁ + p.1) (j₁ + p.2) h₂ h2₂ he₂
          hle₂ hi₂_ev hj₂_ev hi₂_le hj₂_le).insideVerts =
          (subwallInsideFinset blk.wallSec.W (i₁ + p.1) (j₁ + p.2) h₂).toNatSet :=
      blk.wallSec.W.subwallAt_insideVerts_eq_toNatSet blk.wallSec.h2 blk.wallSec.he blk.wallSec.hW
        (i₁ + p.1) (j₁ + p.2) h₂ h2₂ he₂ hle₂ hi₂_ev hj₂_ev hi₂_le hj₂_le
    rcases hhom.2 hIntA hvA hsub₂ hheight₂ with ⟨A', hIntA', hvA', hsame⟩
    rw [hin₂, hH₂_in] at hvA'
    exact ⟨A', hIntA', hvA', hsame⟩
  · intro hall
    refine ⟨hH₁_sub, fun A hIntA hvA H₂ hsub₂ hheight₂ => ?_⟩
    rw [hH₁_in] at hvA
    rcases exists_validSubwallShift_of_isSubwallOf_subwallAt
        h2₁ he₁ hle₁ hi₁_even hj₁_even hi₁_le hj₁_le hsub₂ with
      ⟨p, hp, hle₂, hi₂_ev, hj₂_ev, hi₂_le, hj₂_le, hin₂⟩
    subst hheight₂
    have hcov := (recordsCoverSubwall_eq_true_iff vOut hx_len hrep
      (subwallInsideFinset blk.wallSec.W i₁ j₁ h₁)
      (subwallInsideFinset blk.wallSec.W (i₁ + p.1) (j₁ + p.2) H₂.height)).mp (hall p hp)
    rcases hcov hIntA hvA with ⟨A', hIntA', hvA', hsame⟩
    have hH₂_in :
        (blk.toGMWall.subwallAt (i₁ + p.1) (j₁ + p.2) H₂.height H₂.two_le_height H₂.even_height
          hle₂ hi₂_ev hj₂_ev hi₂_le hj₂_le).insideVerts =
          (subwallInsideFinset blk.wallSec.W (i₁ + p.1) (j₁ + p.2) H₂.height).toNatSet :=
      blk.wallSec.W.subwallAt_insideVerts_eq_toNatSet blk.wallSec.h2 blk.wallSec.he blk.wallSec.hW
        (i₁ + p.1) (j₁ + p.2) H₂.height H₂.two_le_height H₂.even_height hle₂
        hi₂_ev hj₂_ev hi₂_le hj₂_le
    rw [hin₂, hH₂_in]
    exact ⟨A', hIntA', hvA', hsame⟩

/-! ### Section 4: Word RAM Gadgets for Subwall Inside-Vertex Bitset and Folio Coverage Test -/

/-- Partial `hasMatchingMemberIn` over `records.take k`. -/
def hasMatchingMemberInPrefix {n : ℕ} (records : List VisionMemberRecord) (S₂ : Finset (Fin n))
    (code k : ℕ) : Bool :=
  (records.take k).any (fun m' => memberInFinset S₂ m' && decide (m'.folioCode = code))

theorem hasMatchingMemberInPrefix_zero {n : ℕ} (records : List VisionMemberRecord)
    (S₂ : Finset (Fin n)) (code : ℕ) :
    hasMatchingMemberInPrefix records S₂ code 0 = false := rfl

theorem hasMatchingMemberInPrefix_full {n : ℕ} (records : List VisionMemberRecord)
    (S₂ : Finset (Fin n)) (code : ℕ) :
    hasMatchingMemberInPrefix records S₂ code records.length =
      hasMatchingMemberIn records S₂ code := by
  unfold hasMatchingMemberInPrefix hasMatchingMemberIn
  rw [List.take_of_length_le (le_rfl)]

theorem hasMatchingMemberInPrefix_succ {n : ℕ} (records : List VisionMemberRecord)
    (S₂ : Finset (Fin n)) (code : ℕ) {k : ℕ} (hk : k < records.length) :
    hasMatchingMemberInPrefix records S₂ code (k + 1) =
      (hasMatchingMemberInPrefix records S₂ code k ||
        (memberInFinset S₂ (records[k]'hk) && decide ((records[k]'hk).folioCode = code))) := by
  unfold hasMatchingMemberInPrefix
  rw [take_add_one_eq_append_getElem records k hk, List.any_append, List.any_cons, List.any_nil,
    Bool.or_false]

/-- Partial `recordsCoverSubwall` over `records.take k`. -/
def recordsCoverSubwallPrefix {n : ℕ} (records : List VisionMemberRecord)
    (S₁ S₂ : Finset (Fin n)) (k : ℕ) : Bool :=
  (records.take k).all (fun m => !memberInFinset S₁ m || hasMatchingMemberIn records S₂ m.folioCode)

theorem recordsCoverSubwallPrefix_zero {n : ℕ} (records : List VisionMemberRecord)
    (S₁ S₂ : Finset (Fin n)) :
    recordsCoverSubwallPrefix records S₁ S₂ 0 = true := rfl

theorem recordsCoverSubwallPrefix_full {n : ℕ} (records : List VisionMemberRecord)
    (S₁ S₂ : Finset (Fin n)) :
    recordsCoverSubwallPrefix records S₁ S₂ records.length =
      recordsCoverSubwall records S₁ S₂ := by
  unfold recordsCoverSubwallPrefix recordsCoverSubwall
  rw [List.take_of_length_le (le_rfl)]

theorem recordsCoverSubwallPrefix_succ {n : ℕ} (records : List VisionMemberRecord)
    (S₁ S₂ : Finset (Fin n)) {k : ℕ} (hk : k < records.length) :
    recordsCoverSubwallPrefix records S₁ S₂ (k + 1) =
      (recordsCoverSubwallPrefix records S₁ S₂ k &&
        (!memberInFinset S₁ (records[k]'hk) ||
          hasMatchingMemberIn records S₂ (records[k]'hk).folioCode)) := by
  unfold recordsCoverSubwallPrefix
  rw [take_add_one_eq_append_getElem records k hk, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true]

/-- Inner loop body of `hasMatchingMemberInProg`: checks if member `r_j` is interior, has
`vOf[r_j] ∈ S₂`, and has `folioCode[r_j] = r_code`; if so, sets `r_found := 1`. -/
def hasMatchingMemberBody (a_memIsInt a_memVOf a_memFolioCode a_in2 : Arr)
    (r_code r_found r_j r_tmp1 r_tmp2 : Reg) : Cmd :=
  .seq (.assign r_tmp1 (.read a_memIsInt (.reg r_j)))
    (.ite (.op .eq (.reg r_tmp1) (.const 1))
      (.seq (.assign r_tmp1 (.read a_memVOf (.reg r_j)))
        (.seq (.assign r_tmp1 (.read a_in2 (.reg r_tmp1)))
          (.seq (.assign r_tmp2 (.read a_memFolioCode (.reg r_j)))
            (.ite (.op .mul (.op .eq (.reg r_tmp1) (.const 1))
                            (.op .eq (.reg r_tmp2) (.reg r_code)))
              (.assign r_found (.const 1))
              .skip))))
      .skip)

/-- Word RAM program computing `if hasMatchingMemberIn records S₂ code then 1 else 0` in `r_found`,
using scratch registers `r_base .. r_base + 2`. -/
def hasMatchingMemberInProg (a_memIsInt a_memVOf a_memFolioCode a_in2 : Arr)
    (r_M r_code r_found r_base : Reg) : Cmd :=
  .seq (.assign r_found (.const 0))
    (.seq (.assign r_base (.const 0))
      (forUp r_base (.reg r_M)
        (hasMatchingMemberBody a_memIsInt a_memVOf a_memFolioCode a_in2
          r_code r_found r_base (r_base + 1) (r_base + 2))))

open Classical in
theorem eval_bitSetList_mem_toNatSet {w n : ℕ} (S : Finset (Fin n)) (s : State) (a r : ℕ)
    {v : ℕ} (hv_n : v < n) (hn_w : n < 2 ^ w) (hw : 1 < 2 ^ w)
    (ha : s.arrs a = bitSetList S) (hr : s.regs r = v) :
    (Expr.read a (.reg r)).eval w s = some (if v ∈ S.toNatSet then 1 else 0) := by
  have hv_w : v < 2 ^ w := Nat.lt_trans hv_n hn_w
  have hlen : v < (s.arrs a).length := by rw [ha, length_bitSetList]; exact hv_n
  have hget : (s.arrs a)[v]'hlen = if v ∈ S.toNatSet then 1 else 0 := by
    have hlt' : v < (bitSetList S).length := by rw [length_bitSetList]; exact hv_n
    have hcongr : (s.arrs a)[v]'hlen = (bitSetList S)[v]'hlt' := by congr 1
    rw [hcongr]
    simp only [bitSetList, List.getElem_ofFn, Finset.toNatSet, Set.mem_image, Finset.mem_coe]
    have hiff : (⟨v, hv_n⟩ : Fin n) ∈ S ↔ ∃ u ∈ S, u.1 = v :=
      ⟨fun h => ⟨⟨v, hv_n⟩, h, rfl⟩,
       fun ⟨u, hu, heq⟩ => Fin.ext (show (⟨v, hv_n⟩ : Fin n).1 = u.1 from heq.symm) ▸ hu⟩
    by_cases hmem : (⟨v, hv_n⟩ : Fin n) ∈ S
    · rw [ite_eq_left hmem, ite_eq_left (hiff.mp hmem)]
    · rw [ite_eq_right hmem, ite_eq_right (mt hiff.mpr hmem)]
  have hval_w : (if v ∈ S.toNatSet then 1 else 0) < 2 ^ w := by split_ifs <;> omega
  simp [Expr.eval, checkWord, hr, hv_w, hlen, hget, hval_w]

open Classical in
theorem hasMatchingMemberLoop_exec {w n : ℕ}
    (records : List VisionMemberRecord) (S₂ : Finset (Fin n)) (code : ℕ)
    (a_memIsInt a_memVOf a_memFolioCode a_in2 : ℕ)
    (r_M r_code r_found r_base : ℕ)
    (hr_M : r_M < r_base) (hr_code : r_code < r_base) (hr_found : r_found < r_base)
    (hne_mf : r_M ≠ r_found) (hne_cf : r_code ≠ r_found)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hM_w : records.length < 2 ^ w) (hcode_w : code < 2 ^ w)
    (hrec_props : ∀ m ∈ records,
      m.isInterior = 0 ∨ (m.isInterior = 1 ∧ m.vOf < n ∧ m.folioCode < 2 ^ w))
    (rem k : ℕ) (hrem : k + rem = records.length)
    {s : State}
    (hIntArr : s.arrs a_memIsInt = records.map VisionMemberRecord.isInterior)
    (hvOfArr : s.arrs a_memVOf = records.map VisionMemberRecord.vOf)
    (hfCodeArr : s.arrs a_memFolioCode = records.map VisionMemberRecord.folioCode)
    (hin2 : s.arrs a_in2 = bitSetList S₂)
    (hrM : s.regs r_M = records.length)
    (hrcode : s.regs r_code = code)
    (hrfound : s.regs r_found = if hasMatchingMemberInPrefix records S₂ code k then 1 else 0)
    (hrj : s.regs r_base = k) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_M)
        (hasMatchingMemberBody a_memIsInt a_memVOf a_memFolioCode a_in2
          r_code r_found r_base (r_base + 1) (r_base + 2))) s s' t ∧
      t ≤ 3 + 31 * rem ∧
      s'.regs r_found = (if hasMatchingMemberIn records S₂ code then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < r_base → r ≠ r_found → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = records.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_M)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrM, hM_w, h0_w]
    rw [hasMatchingMemberInPrefix_full] at hrfound
    exact ⟨s, 3, .while_false hcond, by omega, hrfound, fun _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < records.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    let m := records[k]'hk_lt
    have hisInt_cases := hrec_props m (List.getElem_mem hk_lt)
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_M)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hrM, hk_w, hM_w, hk_lt, hw]
    have hisInt_w : m.isInterior < 2 ^ w := by rcases hisInt_cases with h0 | ⟨h1, _⟩ <;> omega
    let s₁ := s.setReg (r_base + 1) m.isInterior
    have hex₁ : Exec w (.assign (r_base + 1) (.read a_memIsInt (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hrj, hk_w, hIntArr, hk_lt, m, hisInt_w])
    rcases hisInt_cases with hisInt0 | ⟨hisInt1, hvOf_n, hfc_w⟩
    · have hite_cond : (Expr.op .eq (.reg (r_base + 1)) (.const 1)).eval w s₁ = some 0 := by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hisInt0, hw, h0_w]
      have hex_body :
          Exec w (hasMatchingMemberBody a_memIsInt a_memVOf a_memFolioCode a_in2
            r_code r_found r_base (r_base + 1) (r_base + 2)) s s₁ (3 + (3 + 1)) :=
        .seq hex₁ (.ite_false hite_cond (.skip _))
      let s₂ := s₁.setReg r_base (k + 1)
      have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₁ s₂ 4 :=
        .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hk_w, hw, hk1_w])
      have hm_in2 : memberInFinset S₂ m = false := by unfold memberInFinset; simp [hisInt0]
      have hrfound₂ :
          s₂.regs r_found = (if hasMatchingMemberInPrefix records S₂ code (k + 1) then 1 else 0) := by
        rw [hasMatchingMemberInPrefix_succ records S₂ code hk_lt]
        change s₂.regs r_found = if (hasMatchingMemberInPrefix records S₂ code k ||
          (memberInFinset S₂ m && decide (m.folioCode = code))) then 1 else 0
        rw [hm_in2, Bool.false_and, Bool.or_false]
        simp [s₂, s₁, State.setReg, show r_found ≠ r_base by omega, show r_found ≠ r_base + 1 by omega, hrfound]
      rcases ih (k + 1) (by omega) (s := s₂) (by simp [s₂, s₁, hIntArr]) (by simp [s₂, s₁, hvOfArr])
          (by simp [s₂, s₁, hfCodeArr]) (by simp [s₂, s₁, hin2])
          (by simp [s₂, s₁, State.setReg, show r_M ≠ r_base by omega, show r_M ≠ r_base + 1 by omega, hrM])
          (by simp [s₂, s₁, State.setReg, show r_code ≠ r_base by omega, show r_code ≠ r_base + 1 by omega, hrcode])
          hrfound₂ (by simp [s₂]) with ⟨s₃, t₃, hex₃, ht₃, hrfound₃, harr₃, hreg₃⟩
      refine ⟨s₃, 3 + ((3 + (3 + 1)) + 4) + t₃, .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
        by omega, hrfound₃, fun a => by rw [harr₃ a]; simp [s₂, s₁],
        fun r hr hne => by rw [hreg₃ r hr hne]; simp [s₂, s₁, State.setReg, show r ≠ r_base by omega, show r ≠ r_base + 1 by omega]⟩
    · have hite_cond : (Expr.op .eq (.reg (r_base + 1)) (.const 1)).eval w s₁ = some 1 := by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hisInt1, hw]
      have hvOf_w : m.vOf < 2 ^ w := Nat.lt_trans hvOf_n hn_w
      let s₂ := s₁.setReg (r_base + 1) m.vOf
      have hex₂ : Exec w (.assign (r_base + 1) (.read a_memVOf (.reg r_base))) s₁ s₂ 3 :=
        .assign (by simp [s₁, Expr.eval, checkWord, hrj, hk_w, hvOfArr, hk_lt, m, hvOf_w])
      let b_in2 : ℕ := if m.vOf ∈ S₂.toNatSet then 1 else 0
      let s₃ := s₂.setReg (r_base + 1) b_in2
      have hex₃ : Exec w (.assign (r_base + 1) (.read a_in2 (.reg (r_base + 1)))) s₂ s₃ 3 :=
        .assign (eval_bitSetList_mem_toNatSet S₂ s₂ a_in2 (r_base + 1) hvOf_n hn_w hw (by simp [s₂, s₁, hin2]) (by simp [s₂]))
      let s₄ := s₃.setReg (r_base + 2) m.folioCode
      have hex₄ : Exec w (.assign (r_base + 2) (.read a_memFolioCode (.reg r_base))) s₃ s₄ 3 :=
        .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hrj, hk_w, hfCodeArr, hk_lt, m, hfc_w])
      have hb_w : b_in2 < 2 ^ w := by dsimp [b_in2]; split_ifs <;> omega
      have hrb1₄ : s₄.regs (r_base + 1) = b_in2 := by simp [s₄, s₃, State.setReg]
      have hrb2₄ : s₄.regs (r_base + 2) = m.folioCode := by simp [s₄]
      have hrcode₄ : s₄.regs r_code = code := by
        simp [s₄, s₃, s₂, s₁, State.setReg, show r_code ≠ r_base + 2 by omega, show r_code ≠ r_base + 1 by omega, hrcode]
      by_cases hmatch : memberInFinset S₂ m = true ∧ m.folioCode = code
      · have hmem_S₂ : m.vOf ∈ S₂.toNatSet := ((memberInFinset_eq_true_iff S₂ m).mp hmatch.1).2
        have hb_eq1 : b_in2 = 1 := ite_eq_left hmem_S₂
        have hfc_eq : m.folioCode = code := hmatch.2
        have hmul_cond :
            (Expr.op .mul (.op .eq (.reg (r_base + 1)) (.const 1))
                          (.op .eq (.reg (r_base + 2)) (.reg r_code))).eval w s₄ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrb1₄, hrb2₄, hb_eq1, hfc_eq, hrcode₄, hcode_w, hw]
        let s₅ := s₄.setReg r_found 1
        have hex₅ :
            Exec w (.ite (.op .mul (.op .eq (.reg (r_base + 1)) (.const 1))
                                   (.op .eq (.reg (r_base + 2)) (.reg r_code)))
              (.assign r_found (.const 1)) .skip) s₄ s₅ (7 + 2) :=
          .ite_true hmul_cond (by omega) (.assign (by simp [Expr.eval, checkWord, hw]))
        let s₆ := s₅.setReg r_base (k + 1)
        have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₅ s₆ 4 :=
          .assign (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, show r_base ≠ r_found by omega,
            Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hk_w, hw, hk1_w])
        have hrfound₆ :
            s₆.regs r_found = (if hasMatchingMemberInPrefix records S₂ code (k + 1) then 1 else 0) := by
          rw [hasMatchingMemberInPrefix_succ records S₂ code hk_lt]
          change s₆.regs r_found = if (hasMatchingMemberInPrefix records S₂ code k ||
            (memberInFinset S₂ m && decide (m.folioCode = code))) then 1 else 0
          rw [hmatch.1, decide_eq_true hmatch.2, Bool.and_true, Bool.or_true, ite_eq_left rfl]
          simp [s₆, s₅, State.setReg, show r_found ≠ r_base by omega]
        rcases ih (k + 1) (by omega) (s := s₆)
            (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hIntArr]) (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hvOfArr])
            (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hfCodeArr]) (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hin2])
            (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, show r_M ≠ r_base by omega, hne_mf,
              show r_M ≠ r_base + 2 by omega, show r_M ≠ r_base + 1 by omega, hrM])
            (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, show r_code ≠ r_base by omega, hne_cf,
              show r_code ≠ r_base + 2 by omega, show r_code ≠ r_base + 1 by omega, hrcode])
            hrfound₆ (by simp [s₆]) with ⟨s₇, t₇, hex₇, ht₇, hrfound₇, harr₇, hreg₇⟩
        refine ⟨s₇, 3 + ((3 + (3 + (3 + (3 + (3 + (7 + 2)))))) + 4) + t₇,
          .while_true hcond (by omega) (.seq (.seq hex₁ (.ite_true hite_cond (by omega)
            (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))))) hex_inc) hex₇,
          by omega, hrfound₇, fun a => by rw [harr₇ a]; simp [s₆, s₅, s₄, s₃, s₂, s₁],
          fun r hr hne => by rw [hreg₇ r hr hne]; simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hne,
            show r ≠ r_base by omega, show r ≠ r_base + 1 by omega, show r ≠ r_base + 2 by omega]⟩
      · have hnot_both : ¬ (b_in2 = 1 ∧ m.folioCode = code) := by
          rintro ⟨hb1, hfc⟩
          have hmem_S₂ : m.vOf ∈ S₂.toNatSet := by by_contra hnot; dsimp [b_in2] at hb1; rw [ite_eq_right hnot] at hb1; omega
          exact hmatch ⟨(memberInFinset_eq_true_iff S₂ m).mpr ⟨hisInt1, hmem_S₂⟩, hfc⟩
        have hmul_cond :
            (Expr.op .mul (.op .eq (.reg (r_base + 1)) (.const 1))
                          (.op .eq (.reg (r_base + 2)) (.reg r_code))).eval w s₄ = some 0 := by
          by_cases hb1 : b_in2 = 1
          · have hfc_ne : m.folioCode ≠ code := fun h => hnot_both ⟨hb1, h⟩
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrb1₄, hrb2₄, hb1, hfc_ne, hrcode₄, hfc_w, hcode_w, hw, h0_w]
          · have hb0 : b_in2 = 0 := by dsimp [b_in2] at hb1 ⊢; split_ifs at hb1 ⊢ <;> omega
            by_cases hfc : m.folioCode = code
            · simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrb1₄, hrb2₄, hb0, hfc, hrcode₄, hcode_w, hw, h0_w]
            · simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrb1₄, hrb2₄, hb0, hfc, hrcode₄, hfc_w, hcode_w, hw, h0_w]
        have hex₅ :
            Exec w (.ite (.op .mul (.op .eq (.reg (r_base + 1)) (.const 1))
                                   (.op .eq (.reg (r_base + 2)) (.reg r_code)))
              (.assign r_found (.const 1)) .skip) s₄ s₄ (7 + 1) :=
          .ite_false (c₁ := .assign r_found (.const 1)) hmul_cond (.skip s₄)
        let s₆ := s₄.setReg r_base (k + 1)
        have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₄ s₆ 4 :=
          .assign (by simp [s₄, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, hk_w, hw, hk1_w])
        have hbool_false : (memberInFinset S₂ m && decide (m.folioCode = code)) = false := by
          rw [Bool.and_eq_false_iff]
          by_cases hm_in : memberInFinset S₂ m = true
          · right; rw [decide_eq_false_iff_not]; exact fun h => hmatch ⟨hm_in, h⟩
          · left; exact Bool.not_eq_true _ ▸ hm_in
        have hrfound₆ :
            s₆.regs r_found = (if hasMatchingMemberInPrefix records S₂ code (k + 1) then 1 else 0) := by
          rw [hasMatchingMemberInPrefix_succ records S₂ code hk_lt]
          change s₆.regs r_found = if (hasMatchingMemberInPrefix records S₂ code k ||
            (memberInFinset S₂ m && decide (m.folioCode = code))) then 1 else 0
          rw [hbool_false, Bool.or_false]
          simp [s₆, s₄, s₃, s₂, s₁, State.setReg,
            show r_found ≠ r_base by omega, show r_found ≠ r_base + 1 by omega, show r_found ≠ r_base + 2 by omega, hrfound]
        rcases ih (k + 1) (by omega) (s := s₆)
            (by simp [s₆, s₄, s₃, s₂, s₁, hIntArr]) (by simp [s₆, s₄, s₃, s₂, s₁, hvOfArr])
            (by simp [s₆, s₄, s₃, s₂, s₁, hfCodeArr]) (by simp [s₆, s₄, s₃, s₂, s₁, hin2])
            (by simp [s₆, s₄, s₃, s₂, s₁, State.setReg, show r_M ≠ r_base by omega,
              show r_M ≠ r_base + 2 by omega, show r_M ≠ r_base + 1 by omega, hrM])
            (by simp [s₆, s₄, s₃, s₂, s₁, State.setReg, show r_code ≠ r_base by omega,
              show r_code ≠ r_base + 2 by omega, show r_code ≠ r_base + 1 by omega, hrcode])
            hrfound₆ (by simp [s₆]) with ⟨s₇, t₇, hex₇, ht₇, hrfound₇, harr₇, hreg₇⟩
        refine ⟨s₇, 3 + ((3 + (3 + (3 + (3 + (3 + (7 + 1)))))) + 4) + t₇,
          .while_true hcond (by omega) (.seq (.seq hex₁ (.ite_true hite_cond (by omega)
            (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))))) hex_inc) hex₇,
          by omega, hrfound₇, fun a => by rw [harr₇ a]; simp [s₆, s₄, s₃, s₂, s₁],
          fun r hr hne => by rw [hreg₇ r hr hne]; simp [s₆, s₄, s₃, s₂, s₁, State.setReg,
            show r ≠ r_base by omega, show r ≠ r_base + 1 by omega, show r ≠ r_base + 2 by omega]⟩

open Classical in
theorem hasMatchingMemberInProg_exec {w n : ℕ}
    (records : List VisionMemberRecord) (S₂ : Finset (Fin n)) (code : ℕ)
    (a_memIsInt a_memVOf a_memFolioCode a_in2 : ℕ)
    (r_M r_code r_found r_base : ℕ)
    (hr_M : r_M < r_base) (hr_code : r_code < r_base) (hr_found : r_found < r_base)
    (hne_mf : r_M ≠ r_found) (hne_cf : r_code ≠ r_found)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hM_w : records.length < 2 ^ w) (hcode_w : code < 2 ^ w)
    (hrec_props : ∀ m ∈ records,
      m.isInterior = 0 ∨ (m.isInterior = 1 ∧ m.vOf < n ∧ m.folioCode < 2 ^ w))
    {s : State}
    (hIntArr : s.arrs a_memIsInt = records.map VisionMemberRecord.isInterior)
    (hvOfArr : s.arrs a_memVOf = records.map VisionMemberRecord.vOf)
    (hfCodeArr : s.arrs a_memFolioCode = records.map VisionMemberRecord.folioCode)
    (hin2 : s.arrs a_in2 = bitSetList S₂)
    (hrM : s.regs r_M = records.length)
    (hrcode : s.regs r_code = code) :
    ∃ s' t,
      Exec w (hasMatchingMemberInProg a_memIsInt a_memVOf a_memFolioCode a_in2
        r_M r_code r_found r_base) s s' t ∧
      t ≤ 7 + 31 * records.length ∧
      s'.regs r_found = (if hasMatchingMemberIn records S₂ code then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < r_base → r ≠ r_found → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_found 0
  have hex₁ : Exec w (.assign r_found (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases hasMatchingMemberLoop_exec records S₂ code
      a_memIsInt a_memVOf a_memFolioCode a_in2 r_M r_code r_found r_base
      hr_M hr_code hr_found hne_mf hne_cf hw hn_w hM_w hcode_w hrec_props
      records.length 0 (by omega) (s := s₂)
      (by simp [s₂, s₁, hIntArr]) (by simp [s₂, s₁, hvOfArr])
      (by simp [s₂, s₁, hfCodeArr]) (by simp [s₂, s₁, hin2])
      (by simp [s₂, s₁, State.setReg, show r_M ≠ r_base by omega, hne_mf, hrM])
      (by simp [s₂, s₁, State.setReg, show r_code ≠ r_base by omega, hne_cf, hrcode])
      (by simp [s₂, s₁, State.setReg, show r_found ≠ r_base by omega, hasMatchingMemberInPrefix_zero])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hrfound₃, harr₃, hreg₃⟩
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hrfound₃,
    fun a => by rw [harr₃ a]; simp [s₂, s₁],
    fun r hr hne => by rw [hreg₃ r hr hne]; simp [s₂, s₁, State.setReg, show r ≠ r_base by omega, hne]⟩

/-- Outer loop body of `checkSubwallCoversProg`: if member `r_i` is interior and has
`vOf[r_i] ∈ S₁`, runs `hasMatchingMemberInProg` for `folioCode[r_i]` and clears `r_cov` if not
found. -/
def checkSubwallCoversBody (a_memIsInt a_memVOf a_memFolioCode a_in1 a_in2 : Arr)
    (r_M r_cov r_i r_code r_found r_inner : Reg) : Cmd :=
  .seq (.assign r_found (.read a_memIsInt (.reg r_i)))
    (.ite (.op .eq (.reg r_found) (.const 1))
      (.seq (.assign r_found (.read a_memVOf (.reg r_i)))
        (.seq (.assign r_found (.read a_in1 (.reg r_found)))
          (.ite (.op .eq (.reg r_found) (.const 1))
            (.seq (.assign r_code (.read a_memFolioCode (.reg r_i)))
              (.seq (hasMatchingMemberInProg a_memIsInt a_memVOf a_memFolioCode a_in2
                  r_M r_code r_found r_inner)
                (.ite (.op .eq (.reg r_found) (.const 0))
                  (.assign r_cov (.const 0))
                  .skip)))
            .skip)))
      .skip)

/-- Word RAM program computing `if recordsCoverSubwall records S₁ S₂ then 1 else 0` in `r_cov`,
using scratch registers `r_base .. r_base + 5`. -/
def checkSubwallCoversProg (a_memIsInt a_memVOf a_memFolioCode a_in1 a_in2 : Arr)
    (r_M r_cov r_base : Reg) : Cmd :=
  .seq (.assign r_cov (.const 1))
    (.seq (.assign r_base (.const 0))
      (forUp r_base (.reg r_M)
        (checkSubwallCoversBody a_memIsInt a_memVOf a_memFolioCode a_in1 a_in2
          r_M r_cov r_base (r_base + 1) (r_base + 2) (r_base + 3))))

open Classical in
theorem checkSubwallCoversLoop_exec {w n : ℕ}
    (records : List VisionMemberRecord) (S₁ S₂ : Finset (Fin n))
    (a_memIsInt a_memVOf a_memFolioCode a_in1 a_in2 : ℕ)
    (r_M r_cov r_base : ℕ)
    (hr_M : r_M < r_base) (hr_cov : r_cov < r_base) (hne_mc : r_M ≠ r_cov)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hM_w : records.length < 2 ^ w)
    (hrec_props : ∀ m ∈ records,
      m.isInterior = 0 ∨ (m.isInterior = 1 ∧ m.vOf < n ∧ m.folioCode < 2 ^ w))
    (rem k : ℕ) (hrem : k + rem = records.length)
    {s : State}
    (hIntArr : s.arrs a_memIsInt = records.map VisionMemberRecord.isInterior)
    (hvOfArr : s.arrs a_memVOf = records.map VisionMemberRecord.vOf)
    (hfCodeArr : s.arrs a_memFolioCode = records.map VisionMemberRecord.folioCode)
    (hin1 : s.arrs a_in1 = bitSetList S₁)
    (hin2 : s.arrs a_in2 = bitSetList S₂)
    (hrM : s.regs r_M = records.length)
    (hrcov : s.regs r_cov = if recordsCoverSubwallPrefix records S₁ S₂ k then 1 else 0)
    (hri : s.regs r_base = k) :
    ∃ s' t,
      Exec w (forUp r_base (.reg r_M)
        (checkSubwallCoversBody a_memIsInt a_memVOf a_memFolioCode a_in1 a_in2
          r_M r_cov r_base (r_base + 1) (r_base + 2) (r_base + 3))) s s' t ∧
      t ≤ 3 + rem * (37 + 31 * records.length) ∧
      s'.regs r_cov = (if recordsCoverSubwall records S₁ S₂ then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < r_base → r ≠ r_cov → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = records.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_M)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrM, hM_w, h0_w]
    rw [recordsCoverSubwallPrefix_full] at hrcov
    exact ⟨s, 3, .while_false hcond, by omega, hrcov, fun _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < records.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    let m := records[k]'hk_lt
    have hisInt_cases := hrec_props m (List.getElem_mem hk_lt)
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_M)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrM, hk_w, hM_w, hk_lt, hw]
    have hisInt_w : m.isInterior < 2 ^ w := by rcases hisInt_cases with h0 | ⟨h1, _⟩ <;> omega
    let s₁ := s.setReg (r_base + 2) m.isInterior
    have hex₁ : Exec w (.assign (r_base + 2) (.read a_memIsInt (.reg r_base))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hri, hk_w, hIntArr, hk_lt, m, hisInt_w])
    rcases hisInt_cases with hisInt0 | ⟨hisInt1, hvOf_n, hfc_w⟩
    · have hite1 : (Expr.op .eq (.reg (r_base + 2)) (.const 1)).eval w s₁ = some 0 := by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hisInt0, hw, h0_w]
      let s₂ := s₁.setReg r_base (k + 1)
      have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₁ s₂ 4 :=
        .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hk_w, hw, hk1_w])
      have hm_in1 : memberInFinset S₁ m = false := by unfold memberInFinset; simp [hisInt0]
      have hrcov₂ :
          s₂.regs r_cov = (if recordsCoverSubwallPrefix records S₁ S₂ (k + 1) then 1 else 0) := by
        rw [recordsCoverSubwallPrefix_succ records S₁ S₂ hk_lt]
        change s₂.regs r_cov = if (recordsCoverSubwallPrefix records S₁ S₂ k &&
          (!memberInFinset S₁ m || hasMatchingMemberIn records S₂ m.folioCode)) then 1 else 0
        rw [hm_in1, Bool.not_false, Bool.true_or, Bool.and_true]
        simp [s₂, s₁, State.setReg, show r_cov ≠ r_base by omega, show r_cov ≠ r_base + 2 by omega, hrcov]
      rcases ih (k + 1) (by omega) (s := s₂)
          (by simp [s₂, s₁, hIntArr]) (by simp [s₂, s₁, hvOfArr])
          (by simp [s₂, s₁, hfCodeArr]) (by simp [s₂, s₁, hin1]) (by simp [s₂, s₁, hin2])
          (by simp [s₂, s₁, State.setReg, show r_M ≠ r_base by omega, show r_M ≠ r_base + 2 by omega, hrM])
          hrcov₂ (by simp [s₂]) with ⟨s₃, t₃, hex₃, ht₃, hrcov₃, harr₃, hreg₃⟩
      have hstep_le : 3 + ((3 + (3 + 1)) + 4) + t₃ ≤
          3 + (rem + 1) * (37 + 31 * records.length) := by rw [Nat.succ_mul]; omega
      refine ⟨s₃, 3 + ((3 + (3 + 1)) + 4) + t₃,
        .while_true hcond (by omega) (.seq (.seq hex₁ (.ite_false hite1 (.skip _))) hex_inc) hex₃,
        hstep_le, hrcov₃, fun a => by rw [harr₃ a]; simp [s₂, s₁],
        fun r hr hne => by rw [hreg₃ r hr hne]; simp [s₂, s₁, State.setReg, show r ≠ r_base by omega, show r ≠ r_base + 2 by omega]⟩
    · have hite1 : (Expr.op .eq (.reg (r_base + 2)) (.const 1)).eval w s₁ = some 1 := by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hisInt1, hw]
      have hvOf_w : m.vOf < 2 ^ w := Nat.lt_trans hvOf_n hn_w
      let s₂ := s₁.setReg (r_base + 2) m.vOf
      have hex₂ : Exec w (.assign (r_base + 2) (.read a_memVOf (.reg r_base))) s₁ s₂ 3 :=
        .assign (by simp [s₁, Expr.eval, checkWord, hri, hk_w, hvOfArr, hk_lt, m, hvOf_w])
      let b_in1 : ℕ := if m.vOf ∈ S₁.toNatSet then 1 else 0
      let s₃ := s₂.setReg (r_base + 2) b_in1
      have hex₃ : Exec w (.assign (r_base + 2) (.read a_in1 (.reg (r_base + 2)))) s₂ s₃ 3 :=
        .assign (eval_bitSetList_mem_toNatSet S₁ s₂ a_in1 (r_base + 2) hvOf_n hn_w hw (by simp [s₂, s₁, hin1]) (by simp [s₂]))
      by_cases hm_S₁ : m.vOf ∈ S₁.toNatSet
      · have hb1_eq1 : b_in1 = 1 := ite_eq_left hm_S₁
        have hite2 : (Expr.op .eq (.reg (r_base + 2)) (.const 1)).eval w s₃ = some 1 := by
          simp [s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hb1_eq1, hw]
        let s₄ := s₃.setReg (r_base + 1) m.folioCode
        have hex₄ : Exec w (.assign (r_base + 1) (.read a_memFolioCode (.reg r_base))) s₃ s₄ 3 :=
          .assign (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hri, hk_w, hfCodeArr, hk_lt, m, hfc_w])
        rcases hasMatchingMemberInProg_exec records S₂ m.folioCode
            a_memIsInt a_memVOf a_memFolioCode a_in2 r_M (r_base + 1) (r_base + 2) (r_base + 3)
            (by omega) (by omega) (by omega) (by omega) (by omega) hw hn_w hM_w hfc_w hrec_props (s := s₄)
            (by simp [s₄, s₃, s₂, s₁, hIntArr]) (by simp [s₄, s₃, s₂, s₁, hvOfArr])
            (by simp [s₄, s₃, s₂, s₁, hfCodeArr]) (by simp [s₄, s₃, s₂, s₁, hin2])
            (by simp [s₄, s₃, s₂, s₁, State.setReg, show r_M ≠ r_base + 1 by omega, show r_M ≠ r_base + 2 by omega, hrM])
            (by simp [s₄]) with ⟨s₅, t₅, hex₅, ht₅, hrfound₅, harr₅, hreg₅⟩
        have hm_in1 : memberInFinset S₁ m = true := (memberInFinset_eq_true_iff S₁ m).mpr ⟨hisInt1, hm_S₁⟩
        by_cases hhas : hasMatchingMemberIn records S₂ m.folioCode = true
        · have hrf5_1 : s₅.regs (r_base + 2) = 1 := by rw [hrfound₅, ite_eq_left hhas]
          have hite3 : (Expr.op .eq (.reg (r_base + 2)) (.const 0)).eval w s₅ = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrf5_1, hw, h0_w]
          let s₆ := s₅.setReg r_base (k + 1)
          have hri₅ : s₅.regs r_base = k := by
            rw [hreg₅ r_base (by omega) (by omega)]; simp [s₄, s₃, s₂, s₁, State.setReg, hri]
          have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₅ s₆ 4 :=
            .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₅, hk_w, hw, hk1_w])
          have hrcov₆ :
              s₆.regs r_cov = (if recordsCoverSubwallPrefix records S₁ S₂ (k + 1) then 1 else 0) := by
            rw [recordsCoverSubwallPrefix_succ records S₁ S₂ hk_lt]
            change s₆.regs r_cov = if (recordsCoverSubwallPrefix records S₁ S₂ k &&
              (!memberInFinset S₁ m || hasMatchingMemberIn records S₂ m.folioCode)) then 1 else 0
            rw [hhas, Bool.or_true, Bool.and_true]
            simp only [s₆, State.setReg, show r_cov ≠ r_base by omega, Function.update_apply, ↓reduceIte]
            rw [hreg₅ r_cov (by omega) (by omega)]
            simp [s₄, s₃, s₂, s₁, State.setReg, show r_cov ≠ r_base + 1 by omega, show r_cov ≠ r_base + 2 by omega, hrcov]
          rcases ih (k + 1) (by omega) (s := s₆)
              (by simp [s₆, harr₅, s₄, s₃, s₂, s₁, hIntArr]) (by simp [s₆, harr₅, s₄, s₃, s₂, s₁, hvOfArr])
              (by simp [s₆, harr₅, s₄, s₃, s₂, s₁, hfCodeArr]) (by simp [s₆, harr₅, s₄, s₃, s₂, s₁, hin1])
              (by simp [s₆, harr₅, s₄, s₃, s₂, s₁, hin2])
              (by simp only [s₆, State.setReg, show r_M ≠ r_base by omega, Function.update_apply, ↓reduceIte];
                  rw [hreg₅ r_M (by omega) (by omega)];
                  simp [s₄, s₃, s₂, s₁, State.setReg, show r_M ≠ r_base + 1 by omega, show r_M ≠ r_base + 2 by omega, hrM])
              hrcov₆ (by simp [s₆]) with ⟨s₇, t₇, hex₇, ht₇, hrcov₇, harr₇, hreg₇⟩
          have hstep_le : 3 + ((3 + (3 + (3 + (3 + (3 + (3 + (t₅ + (3 + 1)))))))) + 4) + t₇ ≤
              3 + (rem + 1) * (37 + 31 * records.length) := by rw [Nat.succ_mul]; omega
          refine ⟨s₇, _, .while_true hcond (by omega) (.seq (.seq hex₁ (.ite_true hite1 (by omega)
            (.seq hex₂ (.seq hex₃ (.ite_true hite2 (by omega)
              (.seq hex₄ (.seq hex₅ (.ite_false hite3 (.skip _))))))))) hex_inc) hex₇,
            hstep_le, hrcov₇, fun a => by rw [harr₇ a]; simp [s₆, harr₅, s₄, s₃, s₂, s₁],
            fun r hr hne => by
              rw [hreg₇ r hr hne]; simp only [s₆, State.setReg, show r ≠ r_base by omega, Function.update_apply, ↓reduceIte]
              rw [hreg₅ r (by omega) (by omega)]; simp [s₄, s₃, s₂, s₁, State.setReg, show r ≠ r_base + 1 by omega, show r ≠ r_base + 2 by omega]⟩
        · have hrf5_0 : s₅.regs (r_base + 2) = 0 := by rw [hrfound₅, ite_eq_right hhas]
          have hite3 : (Expr.op .eq (.reg (r_base + 2)) (.const 0)).eval w s₅ = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrf5_0, hw, h0_w]
          let s₅' := s₅.setReg r_cov 0
          have hex₅' : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
              (.assign r_cov (.const 0)) .skip) s₅ s₅' (3 + 2) :=
            .ite_true hite3 (by omega) (.assign (by simp [Expr.eval, checkWord, h0_w]))
          let s₆ := s₅'.setReg r_base (k + 1)
          have hri₅' : s₅'.regs r_base = k := by
            simp only [s₅', State.setReg, show r_base ≠ r_cov by omega, Function.update_apply, ↓reduceIte]
            rw [hreg₅ r_base (by omega) (by omega)]; simp [s₄, s₃, s₂, s₁, State.setReg, hri]
          have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₅' s₆ 4 :=
            .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri₅', hk_w, hw, hk1_w])
          have hhas_f : hasMatchingMemberIn records S₂ m.folioCode = false := Bool.not_eq_true _ ▸ hhas
          have hrcov₆ :
              s₆.regs r_cov = (if recordsCoverSubwallPrefix records S₁ S₂ (k + 1) then 1 else 0) := by
            rw [recordsCoverSubwallPrefix_succ records S₁ S₂ hk_lt]
            change s₆.regs r_cov = if (recordsCoverSubwallPrefix records S₁ S₂ k &&
              (!memberInFinset S₁ m || hasMatchingMemberIn records S₂ m.folioCode)) then 1 else 0
            rw [hm_in1, hhas_f, Bool.not_true, Bool.false_or, Bool.and_false, ite_eq_right Bool.false_ne_true]
            simp [s₆, s₅', State.setReg, show r_cov ≠ r_base by omega]
          rcases ih (k + 1) (by omega) (s := s₆)
              (by simp [s₆, s₅', harr₅, s₄, s₃, s₂, s₁, hIntArr]) (by simp [s₆, s₅', harr₅, s₄, s₃, s₂, s₁, hvOfArr])
              (by simp [s₆, s₅', harr₅, s₄, s₃, s₂, s₁, hfCodeArr]) (by simp [s₆, s₅', harr₅, s₄, s₃, s₂, s₁, hin1])
              (by simp [s₆, s₅', harr₅, s₄, s₃, s₂, s₁, hin2])
              (by simp only [s₆, s₅', State.setReg, show r_M ≠ r_base by omega, hne_mc, Function.update_apply, ↓reduceIte];
                  rw [hreg₅ r_M (by omega) (by omega)];
                  simp [s₄, s₃, s₂, s₁, State.setReg, show r_M ≠ r_base + 1 by omega, show r_M ≠ r_base + 2 by omega, hrM])
              hrcov₆ (by simp [s₆]) with ⟨s₇, t₇, hex₇, ht₇, hrcov₇, harr₇, hreg₇⟩
          have hstep_le : 3 + ((3 + (3 + (3 + (3 + (3 + (3 + (t₅ + (3 + 2)))))))) + 4) + t₇ ≤
              3 + (rem + 1) * (37 + 31 * records.length) := by rw [Nat.succ_mul]; omega
          refine ⟨s₇, _, .while_true hcond (by omega) (.seq (.seq hex₁ (.ite_true hite1 (by omega)
            (.seq hex₂ (.seq hex₃ (.ite_true hite2 (by omega) (.seq hex₄ (.seq hex₅ hex₅'))))))) hex_inc) hex₇,
            hstep_le, hrcov₇, fun a => by rw [harr₇ a]; simp [s₆, s₅', harr₅, s₄, s₃, s₂, s₁],
            fun r hr hne => by
              rw [hreg₇ r hr hne]; simp only [s₆, s₅', State.setReg, show r ≠ r_base by omega, hne, Function.update_apply, ↓reduceIte]
              rw [hreg₅ r (by omega) (by omega)]; simp [s₄, s₃, s₂, s₁, State.setReg, show r ≠ r_base + 1 by omega, show r ≠ r_base + 2 by omega]⟩
      · have hb1_eq0 : b_in1 = 0 := ite_eq_right hm_S₁
        have hite2 : (Expr.op .eq (.reg (r_base + 2)) (.const 1)).eval w s₃ = some 0 := by
          simp [s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hb1_eq0, hw, h0_w]
        let s₄ := s₃.setReg r_base (k + 1)
        have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₃ s₄ 4 :=
          .assign (by simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hk_w, hw, hk1_w])
        have hm_in1 : memberInFinset S₁ m = false := by
          rw [Bool.eq_false_iff, Ne, memberInFinset_eq_true_iff]; exact fun ⟨_, h⟩ => hm_S₁ h
        have hrcov₄ :
            s₄.regs r_cov = (if recordsCoverSubwallPrefix records S₁ S₂ (k + 1) then 1 else 0) := by
          rw [recordsCoverSubwallPrefix_succ records S₁ S₂ hk_lt]
          change s₄.regs r_cov = if (recordsCoverSubwallPrefix records S₁ S₂ k &&
            (!memberInFinset S₁ m || hasMatchingMemberIn records S₂ m.folioCode)) then 1 else 0
          rw [hm_in1, Bool.not_false, Bool.true_or, Bool.and_true]
          simp [s₄, s₃, s₂, s₁, State.setReg, show r_cov ≠ r_base by omega, show r_cov ≠ r_base + 2 by omega, hrcov]
        rcases ih (k + 1) (by omega) (s := s₄)
            (by simp [s₄, s₃, s₂, s₁, hIntArr]) (by simp [s₄, s₃, s₂, s₁, hvOfArr])
            (by simp [s₄, s₃, s₂, s₁, hfCodeArr]) (by simp [s₄, s₃, s₂, s₁, hin1]) (by simp [s₄, s₃, s₂, s₁, hin2])
            (by simp [s₄, s₃, s₂, s₁, State.setReg, show r_M ≠ r_base by omega, show r_M ≠ r_base + 2 by omega, hrM])
            hrcov₄ (by simp [s₄]) with ⟨s₅, t₅, hex₅, ht₅, hrcov₅, harr₅, hreg₅⟩
        have hstep_le : 3 + ((3 + (3 + (3 + (3 + (3 + 1))))) + 4) + t₅ ≤
            3 + (rem + 1) * (37 + 31 * records.length) := by rw [Nat.succ_mul]; omega
        refine ⟨s₅, _, .while_true hcond (by omega) (.seq (.seq hex₁ (.ite_true hite1 (by omega)
          (.seq hex₂ (.seq hex₃ (.ite_false hite2 (.skip _)))))) hex_inc) hex₅,
          hstep_le, hrcov₅, fun a => by rw [harr₅ a]; simp [s₄, s₃, s₂, s₁],
          fun r hr hne => by rw [hreg₅ r hr hne]; simp [s₄, s₃, s₂, s₁, State.setReg, show r ≠ r_base by omega, show r ≠ r_base + 2 by omega]⟩

open Classical in
theorem checkSubwallCoversProg_exec {w n : ℕ}
    (records : List VisionMemberRecord) (S₁ S₂ : Finset (Fin n))
    (a_memIsInt a_memVOf a_memFolioCode a_in1 a_in2 : ℕ)
    (r_M r_cov r_base : ℕ)
    (hr_M : r_M < r_base) (hr_cov : r_cov < r_base) (hne_mc : r_M ≠ r_cov)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hM_w : records.length < 2 ^ w)
    (hrec_props : ∀ m ∈ records,
      m.isInterior = 0 ∨ (m.isInterior = 1 ∧ m.vOf < n ∧ m.folioCode < 2 ^ w))
    {s : State}
    (hIntArr : s.arrs a_memIsInt = records.map VisionMemberRecord.isInterior)
    (hvOfArr : s.arrs a_memVOf = records.map VisionMemberRecord.vOf)
    (hfCodeArr : s.arrs a_memFolioCode = records.map VisionMemberRecord.folioCode)
    (hin1 : s.arrs a_in1 = bitSetList S₁)
    (hin2 : s.arrs a_in2 = bitSetList S₂)
    (hrM : s.regs r_M = records.length) :
    ∃ s' t,
      Exec w (checkSubwallCoversProg a_memIsInt a_memVOf a_memFolioCode a_in1 a_in2
        r_M r_cov r_base) s s' t ∧
      t ≤ 7 + records.length * (37 + 31 * records.length) ∧
      s'.regs r_cov = (if recordsCoverSubwall records S₁ S₂ then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < r_base → r ≠ r_cov → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_cov 1
  have hex₁ : Exec w (.assign r_cov (.const 1)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases checkSubwallCoversLoop_exec records S₁ S₂
      a_memIsInt a_memVOf a_memFolioCode a_in1 a_in2 r_M r_cov r_base
      hr_M hr_cov hne_mc hw hn_w hM_w hrec_props records.length 0 (by omega) (s := s₂)
      (by simp [s₂, s₁, hIntArr]) (by simp [s₂, s₁, hvOfArr])
      (by simp [s₂, s₁, hfCodeArr]) (by simp [s₂, s₁, hin1]) (by simp [s₂, s₁, hin2])
      (by simp [s₂, s₁, State.setReg, show r_M ≠ r_base by omega, hne_mc, hrM])
      (by simp [s₂, s₁, State.setReg, show r_cov ≠ r_base by omega, recordsCoverSubwallPrefix_zero])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hrcov₃, harr₃, hreg₃⟩
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hrcov₃,
    fun a => by rw [harr₃ a]; simp [s₂, s₁],
    fun r hr hne => by rw [hreg₃ r hr hne]; simp [s₂, s₁, State.setReg, show r ≠ r_base by omega, hne]⟩

end GraphMinor.Compute
