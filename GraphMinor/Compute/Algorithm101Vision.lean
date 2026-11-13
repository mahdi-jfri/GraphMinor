module

public import GraphMinor.Compute.Case3Block
public import GraphMinor.Compute.Algorithm101Defs
public import GraphMinor.GM13.Section10

/-!
# Vision Output Representation and Pure Reading Decoder for Algorithm (10.1)

This file defines the word-by-word encoding format and pure reading decoder (`parseVisionOutput`)
for the Vision produced by Algorithm (10.1) (Graph Minors XIII, Section 10, pages 106–107),
proving:

1. **Section 1. Wall Vertex Sets (`V(H)`, `V(H.perimeter)`, `H.insideVerts`) and Division
   Boundary / Interior Unpacking:**
   Computable characterizations of `V(H.graph)`, `V(H.perimeter)`, `H.insideVerts`,
   `GM13.IsInteriorMember`, and `GM13.divBoundary` for a `ParsedCase3Block`.
2. **Section 2. Paths in `K = S_H.G` and Clockwise Ordering of `Ω̄`:**
   Lifting vertex-list paths in `K` to `GM09.IsGraphPathWithEnds S_H.G`, and decidable checking
   of `S_H.Ω.IsClockwise3` on the four corners of `H`.
3. **Section 3. Subdigraphs `Ã` (`subdigraphOfLists`, `memberTildeAVList`):**
   Constructing `Ã ⊆ G.toGMDigraph` with `X ⊆ V(Ã)` and `(Ã \ X).toGraph = A`.
4. **Section 4. Vision Output Format, Pure Reading Parser, and `toGMVision`:**
   `VisionMemberRecord`, `ParsedVisionOutput`, `parseVisionOutput`, `encVisionOutput`,
   round-trip `parseVisionOutput_encVisionOutput`, conversion `ParsedVisionOutput.toGMVision` to
   `GM13.Vision`, and the `folioCode` equivalence theorem for `HasSameMemberDeltaFolio`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-! ### Section 1: Wall Vertex Sets (`V(H)`, `V(H.perimeter)`, `H.insideVerts`) and Division Unpacking -/

/-- Decidable check that a coordinate `p : ℕ × ℕ` lies on the perimeter of the elementary wall of
height `h` (`GM13.elementaryWallPerimeterVerts h`, `GraphMinor/GM13/Defs.lean`). -/
def isElemWallPerimCoord (h : ℕ) (p : ℕ × ℕ) : Bool :=
  decide (p.2 = 0 ∨ p.2 = h ∨ p.1 ≤ 1 ∨ 2 * h ≤ p.1)

@[simp]
theorem isElemWallPerimCoord_eq_true_iff (h : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ GM13.elementaryWallVerts h) :
    isElemWallPerimCoord h p = true ↔ p ∈ GM13.elementaryWallPerimeterVerts h := by
  unfold isElemWallPerimCoord GM13.elementaryWallPerimeterVerts
  simp [hp]

/-- Decidable check that the `k`-th edge of `elemWallEdges h` lies on `GM13.elementaryWallPerimeter h`. -/
def isElemWallPerimEdge (h : ℕ) (k : Fin (elemWallEdges h).length) : Bool :=
  let e := (elemWallEdges h)[k.1]'k.2
  isElemWallPerimCoord h (elemWallVertCoord h e.1) &&
    isElemWallPerimCoord h (elemWallVertCoord h e.2)

theorem isElemWallPerimEdge_eq_true_iff (h : ℕ) (k : Fin (elemWallEdges h).length) :
    isElemWallPerimEdge h k = true ↔
      elemWallEdgeSym2 h k ∈ E(GM13.elementaryWallPerimeter h) := by
  let e := (elemWallEdges h)[k.1]'k.2
  let p₁ := elemWallVertCoord h e.1
  let p₂ := elemWallVertCoord h e.2
  have hp₁ : p₁ ∈ GM13.elementaryWallVerts h := elemWallVertCoord_mem_elementaryWallVerts h e.1
  have hp₂ : p₂ ∈ GM13.elementaryWallVerts h := elemWallVertCoord_mem_elementaryWallVerts h e.2
  have hadj : GM13.elementaryWallAdj h p₁ p₂ := elemWallEdge_elementaryWallAdj h k
  unfold isElemWallPerimEdge
  change (isElemWallPerimCoord h p₁ && isElemWallPerimCoord h p₂) = true ↔
    s(p₁, p₂) ∈ E((GM13.elementaryWall h).induce (GM13.elementaryWallPerimeterVerts h))
  rw [Bool.and_eq_true, isElemWallPerimCoord_eq_true_iff h hp₁,
    isElemWallPerimCoord_eq_true_iff h hp₂, edgeSet_induce, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨p₁, p₂, ⟨hadj, rfl⟩, h1, h2⟩
  · rintro ⟨q₁, q₂, ⟨_, heq⟩, hq₁, hq₂⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hq₁, hq₂⟩
    · exact ⟨hq₂, hq₁⟩

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)

private theorem toWallData_c (hh : 1 ≤ h) (hW : W.IsValid) :
    (W.toWallData hh hW).c = W.branchVertAtCoord := by
  delta toWallData
  rfl

private theorem toWallData_P (hh : 1 ≤ h) (hW : W.IsValid) :
    (W.toWallData hh hW).P = W.subdivPathOfSym2 hW := by
  delta toWallData
  rfl

/-- Finset of vertices on the perimeter of `W : WallOfHeight h G`. -/
def perimFinset : Finset (Fin n) :=
  (((List.finRange (elemWallEdges h).length).filter (isElemWallPerimEdge h)).flatMap
    W.subdivPathVerts).toFinset

/-- Finset of vertices strictly inside the perimeter of `W : WallOfHeight h G`. -/
def perimInsideFinset : Finset (Fin n) :=
  W.vertexFinset \ W.perimFinset

theorem mem_vertexFinset_iff_or (v : Fin n) :
    v ∈ W.vertexFinset ↔
      (∃ u : Fin (elemWallNumVerts h), W.branchVert u = v) ∨
      (∃ k : Fin (elemWallEdges h).length, v ∈ W.internalVerts k) := by
  unfold vertexFinset
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset,
    List.mem_flatMap, List.mem_finRange]

theorem mem_perimFinset_iff (v : Fin n) :
    v ∈ W.perimFinset ↔
      ∃ k : Fin (elemWallEdges h).length,
        isElemWallPerimEdge h k = true ∧ v ∈ W.subdivPathVerts k := by
  unfold perimFinset
  simp [List.mem_toFinset, List.mem_flatMap, List.mem_filter]

/-- `V((W.toGMWall h2 he hW).graph)` equals `W.vertexFinset.toNatSet`. -/
theorem vertexSet_toGMWall_eq_vertexFinset (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    V((W.toGMWall h2 he hW).graph) = W.vertexFinset.toNatSet := by
  have hh : 1 ≤ h := by omega
  change V((W.toWallData hh hW).graph) = W.vertexFinset.toNatSet
  rw [(W.toWallData hh hW).vertexSet_eq, W.toWallData_c hh hW, W.toWallData_P hh hW,
    W.image_branchVertAtCoord_eq]
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop, Finset.toNatSet,
    Set.mem_image, Finset.mem_coe, W.mem_vertexFinset_iff_or]
  constructor
  · rintro (⟨u, rfl⟩ | ⟨e₀, ⟨p, q, hpq, rfl⟩, hx⟩)
    · exact ⟨W.branchVert u, Or.inl ⟨u, rfl⟩, rfl⟩
    · rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
      rw [← hk, W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k] at hx
      simp only [Set.mem_ofPred_eq, List.mem_map, W.mem_subdivPathVerts_iff k] at hx
      rcases hx with ⟨v, rfl | hv | rfl, rfl⟩
      · exact ⟨_, Or.inl ⟨_, rfl⟩, rfl⟩
      · exact ⟨v, Or.inr ⟨k, hv⟩, rfl⟩
      · exact ⟨_, Or.inl ⟨_, rfl⟩, rfl⟩
  · rintro ⟨v, ⟨u, rfl⟩ | ⟨k, hv⟩, rfl⟩
    · exact Or.inl ⟨u, rfl⟩
    · right
      refine ⟨elemWallEdgeSym2 h k, elemWallEdgeSym2_mem_edgeSet h k, ?_⟩
      rw [W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k]
      simp only [Set.mem_ofPred_eq, List.mem_map, W.mem_subdivPathVerts_iff k]
      exact ⟨v, Or.inr (Or.inl hv), rfl⟩

private theorem vertexSet_perimeter_ofData {α β : Type*} {h : ℕ}
    (h2 : 2 ≤ h) (he : Even h) (D : GM13.WallData α β h) :
    V((GM13.Wall.ofData h2 he D).perimeter) =
      ⋃ e₀ ∈ E(GM13.elementaryWallPerimeter h), V(D.P e₀) := by
  unfold GM13.Wall.perimeter
  rw [GM09.vertexSet_subgraphSUnion]
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨P, ⟨e₀, he₀, rfl⟩, hx⟩
    have he₀' : e₀ ∈ E(GM13.elementaryWall h) :=
      let ⟨p, q, hpq⟩ := he₀; ⟨p, q, hpq.1.1, hpq.1.2⟩
    have hpath :
        (GM13.Wall.ofData h2 he D).subdivisionPaths
          ((GM13.Wall.ofData h2 he D).baseIso.edgeEquiv ⟨e₀, he₀'⟩).1 = D.P e₀ :=
      D.pathOf_lab he₀'
    rw [hpath] at hx
    exact ⟨e₀, he₀, hx⟩
  · rintro ⟨e₀, he₀, hx⟩
    have he₀' : e₀ ∈ E(GM13.elementaryWall h) :=
      let ⟨p, q, hpq⟩ := he₀; ⟨p, q, hpq.1.1, hpq.1.2⟩
    have hpath :
        (GM13.Wall.ofData h2 he D).subdivisionPaths
          ((GM13.Wall.ofData h2 he D).baseIso.edgeEquiv ⟨e₀, he₀'⟩).1 = D.P e₀ :=
      D.pathOf_lab he₀'
    exact ⟨D.P e₀, ⟨e₀, he₀, hpath.symm⟩, hx⟩

/-- `V((W.toGMWall h2 he hW).perimeter)` equals `W.perimFinset.toNatSet`. -/
theorem vertexSet_perimeter_toGMWall_eq_perimFinset (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    V((W.toGMWall h2 he hW).perimeter) = W.perimFinset.toNatSet := by
  have hh : 1 ≤ h := by omega
  change V((GM13.Wall.ofData h2 he (W.toWallData hh hW)).perimeter) = W.perimFinset.toNatSet
  rw [vertexSet_perimeter_ofData h2 he (W.toWallData hh hW), W.toWallData_P hh hW]
  ext x
  simp only [Set.mem_iUnion, exists_prop, Finset.toNatSet, Set.mem_image,
    Finset.mem_coe, W.mem_perimFinset_iff]
  constructor
  · rintro ⟨e₀, he₀, hx⟩
    have he₀' : e₀ ∈ E(GM13.elementaryWall h) :=
      let ⟨p, q, hpq⟩ := he₀; ⟨p, q, hpq.1.1, hpq.1.2⟩
    rcases he₀' with ⟨p, q, hpq, rfl⟩
    rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
    rw [← hk] at he₀ hx
    have hperim : isElemWallPerimEdge h k = true :=
      (isElemWallPerimEdge_eq_true_iff h k).mpr he₀
    rw [W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k] at hx
    simp only [Set.mem_ofPred_eq, List.mem_map] at hx
    rcases hx with ⟨v, hv, rfl⟩
    exact ⟨v, ⟨k, hperim, hv⟩, rfl⟩
  · rintro ⟨v, ⟨k, hperim, hv⟩, rfl⟩
    have he₀ : elemWallEdgeSym2 h k ∈ E(GM13.elementaryWallPerimeter h) :=
      (isElemWallPerimEdge_eq_true_iff h k).mp hperim
    refine ⟨elemWallEdgeSym2 h k, he₀, ?_⟩
    rw [W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k]
    exact List.mem_map_of_mem hv

/-- `(W.toGMWall h2 he hW).insideVerts` equals `W.perimInsideFinset.toNatSet`. -/
theorem insideVerts_toGMWall_eq_perimInsideFinset (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (W.toGMWall h2 he hW).insideVerts = W.perimInsideFinset.toNatSet := by
  unfold GM13.Wall.insideVerts perimInsideFinset
  rw [W.vertexSet_toGMWall_eq_vertexFinset h2 he hW,
    W.vertexSet_perimeter_toGMWall_eq_perimFinset h2 he hW]
  ext x
  simp only [Set.mem_sdiff, Finset.toNatSet, Set.mem_image, Finset.mem_coe, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hnot⟩
    exact ⟨v, ⟨hv, fun hp => hnot ⟨v, hp, rfl⟩⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hnot⟩, rfl⟩
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rintro ⟨v', hv', heq⟩
    have : v' = v := Fin.ext heq
    subst this
    exact hnot hv'

end WallOfHeight

@[simp]
theorem coe_image_val_eq_toNatSet {n : ℕ} (Z : Finset (Fin n)) :
    ((Z.image Fin.val : Finset ℕ) : Set ℕ) = Z.toNatSet := by
  rw [Finset.coe_image, Finset.toNatSet]

@[simp]
theorem mem_image_val_iff_mem_toNatSet {n : ℕ} (Z : Finset (Fin n)) (v : ℕ) :
    v ∈ Z.image Fin.val ↔ v ∈ Z.toNatSet := by
  rw [← Finset.mem_coe, coe_image_val_eq_toNatSet]

/-- Decidable check that a member record `r` of a `ParsedCase3Block` represents an interior member
of `𝒜` (disjoint from `V(H.perimeter)`). -/
def isMemberInterior {h n : ℕ} {D_del : MultiDigraph n}
    (W : WallOfHeight h D_del) (r : Case3MemberRecord) : Bool :=
  r.vList.all (fun v => decide (v ∉ W.perimFinset.image Fin.val))

theorem isInteriorMember_toSubgraph_iff {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {r : Case3MemberRecord} (hr : r ∈ p.members) :
    GM13.IsInteriorMember p.toGMWall p.toDivision (r.toSubgraph (delGraph G X')) ↔
      isMemberInterior p.wallSec.W r = true := by
  unfold GM13.IsInteriorMember isMemberInterior ParsedCase3Block.toGMWall
  have hmem_div : r.toSubgraph (delGraph G X') ∈ p.toDivision := ⟨r, hr, rfl⟩
  rw [p.vertexSet_member_toSubgraph hr,
    p.wallSec.W.vertexSet_perimeter_toGMWall_eq_perimFinset p.wallSec.h2 p.wallSec.he p.wallSec.hW,
    Set.disjoint_left, List.all_eq_true]
  simp only [hmem_div, true_and, Set.mem_ofPred_eq, mem_image_val_iff_mem_toNatSet,
    decide_eq_true_eq]

/-- Decidable check that `v : ℕ` lies in the division boundary `∂A` of `r` in `(K, Ω)`. -/
def isMemberBoundaryVert (corners : List ℕ) (K_eList : List (ℕ × ℕ × ℕ))
    (r : Case3MemberRecord) (v : ℕ) : Bool :=
  decide (v ∈ r.vList) &&
    (decide (v ∈ corners) ||
      K_eList.any (fun e => decide (e ∉ r.eList ∧ (e.1 = v ∨ e.2.1 = v))))

/-- Computable list of boundary vertices `∂A` of a member record `r`. -/
def memberBoundaryList (corners : List ℕ) (K_eList : List (ℕ × ℕ × ℕ))
    (r : Case3MemberRecord) : List ℕ :=
  r.vList.filter (isMemberBoundaryVert corners K_eList r)

theorem nodup_memberBoundaryList {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {r : Case3MemberRecord} (hr : r ∈ p.members) :
    (memberBoundaryList p.corners p.K_eList r).Nodup :=
  (p.member_valid_iff hr).2.1.filter _

theorem mem_corners_iff_mem_bar {n : ℕ} {D_del : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block D_del X') (v : ℕ) :
    v ∈ p.corners ↔ v ∈ p.toSociety.Ω.bar := by
  rw [p.hcorners_eq]
  change v ∈ List.ofFn (fun i : Fin 4 => (p.wallSec.W.branchVert (elemWallCornerIdx p.wallSec.h2 i)).1) ↔
    v ∈ Set.range p.toGMWall.corner
  rw [List.mem_ofFn, Set.mem_range]
  refine exists_congr fun i => ?_
  unfold ParsedCase3Block.toGMWall
  rw [p.wallSec.W.toGMWall_corner p.wallSec.h2 p.wallSec.he p.wallSec.hW i]

theorem toCompassGraph_isLink_iff {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {e : ℕ × ℕ × ℕ} {u v : ℕ} :
    p.toCompassGraph.IsLink e u v ↔
      e ∈ p.K_eList ∧ ((e.2.1 = u ∧ e.1 = v) ∨ (e.2.1 = v ∧ e.1 = u)) := by
  have hle : p.toCompassGraph ≤ delGraph G X' := subgraphOfLists_le _ _ _
  constructor
  · intro hlink
    have he : e ∈ p.K_eList := by
      have hm := hlink.edge_mem
      rwa [p.edgeSet_toCompassGraph, Set.mem_ofPred_eq] at hm
    have hlink_del : (delGraph G X').IsLink e u v := hlink.mono hle
    rw [delGraph_eq] at hlink_del
    exact ⟨he, hlink_del.2⟩
  · rintro ⟨he, hends⟩
    have he_mem : e ∈ E(p.toCompassGraph) := by
      rw [p.edgeSet_toCompassGraph]
      exact he
    have he_del := p.K_eList_mem_delGraph he
    have hlink_del : (delGraph G X').IsLink e u v := by
      rw [delGraph_eq] at he_del ⊢
      exact ⟨he_del.1, hends⟩
    exact (hle.isLink_iff he_mem).mpr hlink_del

theorem toCompassGraph_inc_iff {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {e : ℕ × ℕ × ℕ} {v : ℕ} :
    p.toCompassGraph.Inc e v ↔ e ∈ p.K_eList ∧ (e.1 = v ∨ e.2.1 = v) := by
  unfold Graph.Inc
  simp only [toCompassGraph_isLink_iff p]
  constructor
  · rintro ⟨w, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨he, Or.inr rfl⟩
    · exact ⟨he, Or.inl rfl⟩
  · rintro ⟨he, rfl | rfl⟩
    · exact ⟨e.2.1, he, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨e.1, he, Or.inl ⟨rfl, rfl⟩⟩

theorem mem_memberBoundaryList_iff {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {r : Case3MemberRecord} (hr : r ∈ p.members) (v : ℕ) :
    v ∈ memberBoundaryList p.corners p.K_eList r ↔
      v ∈ GM13.divBoundary p.toSociety (r.toSubgraph (delGraph G X')) := by
  unfold memberBoundaryList isMemberBoundaryVert GM13.divBoundary
  rw [List.mem_filter]
  change (v ∈ r.vList ∧
    (decide (v ∈ r.vList) &&
      (decide (v ∈ p.corners) ||
        p.K_eList.any (fun e => decide (e ∉ r.eList ∧ (e.1 = v ∨ e.2.1 = v))))) = true) ↔
    v ∈ V(r.toSubgraph (delGraph G X')) ∧ (v ∈ p.toSociety.Ω.bar ∨
      ∃ e ∈ E(p.toCompassGraph) \ E(r.toSubgraph (delGraph G X')), p.toCompassGraph.Inc e v)
  rw [p.vertexSet_member_toSubgraph hr, p.edgeSet_member_toSubgraph hr,
    p.edgeSet_toCompassGraph, ← mem_corners_iff_mem_bar p v]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
    Set.mem_sdiff, Set.mem_ofPred_eq, toCompassGraph_inc_iff p]
  constructor
  · rintro ⟨hv, _, hbar | ⟨e, heK, he_not, hends⟩⟩
    · exact ⟨hv, Or.inl hbar⟩
    · exact ⟨hv, Or.inr ⟨e, ⟨heK, he_not⟩, heK, hends⟩⟩
  · rintro ⟨hv, hbar | ⟨e, ⟨heK, he_not⟩, _, hends⟩⟩
    · exact ⟨hv, hv, Or.inl hbar⟩
    · exact ⟨hv, hv, Or.inr ⟨e, heK, he_not, hends⟩⟩

/-! ### Section 2: Paths in `K = p.toSociety.G` and Clockwise Ordering of `Ω̄` -/

/-- Decidable check that `u` and `v` are distinct and joined by an edge in `K_eList`. -/
def isKEdgeBetween (K_eList : List (ℕ × ℕ × ℕ)) (u v : ℕ) : Bool :=
  decide (u ≠ v) &&
    K_eList.any (fun e => decide ((e.2.1 = u ∧ e.1 = v) ∨ (e.2.1 = v ∧ e.1 = u)))

/-- First edge in `K_eList` linking `u` and `v`. -/
def findKEdgeBetween (K_eList : List (ℕ × ℕ × ℕ)) (u v : ℕ) : ℕ × ℕ × ℕ :=
  (K_eList.find? (fun e => decide ((e.2.1 = u ∧ e.1 = v) ∨ (e.2.1 = v ∧ e.1 = u)))).getD (0, 0, 0)

theorem findKEdgeBetween_isLink {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') {u v : ℕ}
    (hadj : isKEdgeBetween p.K_eList u v = true) :
    p.toCompassGraph.IsLink (findKEdgeBetween p.K_eList u v) u v := by
  unfold isKEdgeBetween at hadj
  rw [Bool.and_eq_true, List.any_eq_true] at hadj
  rcases hadj with ⟨_, e₀, he₀, hends₀⟩
  unfold findKEdgeBetween
  cases hfind : p.K_eList.find?
      (fun e => decide ((e.2.1 = u ∧ e.1 = v) ∨ (e.2.1 = v ∧ e.1 = u))) with
  | none =>
    have hfalse := List.find?_eq_none.mp hfind e₀ he₀
    exact False.elim (hfalse hends₀)
  | some e =>
    dsimp only [Option.getD_some]
    rw [toCompassGraph_isLink_iff p]
    have hpred := List.find?_some hfind
    simp only [decide_eq_true_eq] at hpred
    exact ⟨List.mem_of_find?_eq_some hfind, hpred⟩

/-- Successive pairs of vertices in `L : List ℕ` are joined by edges in `K_eList`. -/
def IsKWalkList (K_eList : List (ℕ × ℕ × ℕ)) : List ℕ → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => isKEdgeBetween K_eList u v = true ∧ IsKWalkList K_eList (v :: rest)

instance instDecidableIsKWalkList (K_eList : List (ℕ × ℕ × ℕ)) :
    ∀ L : List ℕ, Decidable (IsKWalkList K_eList L)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | u :: v :: rest =>
    letI : Decidable (IsKWalkList K_eList (v :: rest)) :=
      instDecidableIsKWalkList K_eList (v :: rest)
    inferInstanceAs (Decidable (isKEdgeBetween K_eList u v = true ∧ IsKWalkList K_eList (v :: rest)))

/-- Lift a non-empty `IsKWalkList p.K_eList L` with vertices in `p.K_vList` to a `GraphWalk` in
`p.toCompassGraph`. -/
def toKGraphWalk {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') :
    ∀ {L : List ℕ} (hne : L ≠ []),
      (∀ v ∈ L, v ∈ p.K_vList) →
      IsKWalkList p.K_eList L →
      GraphWalk p.toCompassGraph (L.head hne) (L.getLast hne)
  | [], hne, _, _ => False.elim (hne rfl)
  | [u], _, hmem, _ =>
    .nil (by
      rw [p.vertexSet_toCompassGraph]
      exact hmem u List.mem_cons_self)
  | u :: v :: rest, _, hmem, hw =>
    .cons (findKEdgeBetween_isLink p hw.1)
      (toKGraphWalk p (List.cons_ne_nil v rest)
        (fun w hw_mem => hmem w (List.mem_cons_of_mem u hw_mem)) hw.2)

@[simp]
theorem support_toKGraphWalk {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') :
    ∀ {L : List ℕ} (hne : L ≠ []) (hmem : ∀ v ∈ L, v ∈ p.K_vList)
      (hw : IsKWalkList p.K_eList L),
      (toKGraphWalk p hne hmem hw).support = L
  | [], hne, _, _ => False.elim (hne rfl)
  | [_], _, _, _ => rfl
  | _ :: v :: rest, _, hmem, hw => by
    change _ :: (toKGraphWalk p (List.cons_ne_nil v rest) _ hw.2).support = _
    rw [support_toKGraphWalk p (List.cons_ne_nil v rest) _ hw.2]
    rfl

theorem isSimple_toKGraphWalk {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {L : List ℕ} (hne : L ≠ []) (hmem : ∀ v ∈ L, v ∈ p.K_vList)
    (hw : IsKWalkList p.K_eList L) (hnd : L.Nodup) :
    (toKGraphWalk p hne hmem hw).IsSimple := by
  unfold GraphWalk.IsSimple
  rw [support_toKGraphWalk]
  exact hnd

/-- Path subgraph in `p.toCompassGraph` constructed from a simple `K`-walk list `L`. -/
def kPathGraph {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {L : List ℕ} (hne : L ≠ []) (hmem : ∀ v ∈ L, v ∈ p.K_vList)
    (hw : IsKWalkList p.K_eList L) : Graph ℕ (ℕ × ℕ × ℕ) :=
  GM09.walkSubgraph (toKGraphWalk p hne hmem hw)

theorem isGraphPathWithEnds_kPathGraph {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {L : List ℕ} (hne : L ≠ []) (hmem : ∀ v ∈ L, v ∈ p.K_vList)
    (hw : IsKWalkList p.K_eList L) (hnd : L.Nodup) :
    GM09.IsGraphPathWithEnds p.toSociety.G (kPathGraph p hne hmem hw)
      (L.head hne) (L.getLast hne) :=
  GM09.isGraphPathWithEnds_walkSubgraph (isSimple_toKGraphWalk p hne hmem hw hnd)

@[simp]
theorem vertexSet_kPathGraph {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X')
    {L : List ℕ} (hne : L ≠ []) (hmem : ∀ v ∈ L, v ∈ p.K_vList)
    (hw : IsKWalkList p.K_eList L) :
    V(kPathGraph p hne hmem hw) = {v : ℕ | v ∈ L} := by
  unfold kPathGraph
  rw [GM09.vertexSet_walkSubgraph, support_toKGraphWalk]

/-- Decidable check that three indices `i₁, i₂, i₃ : Fin 4` are in cyclic clockwise order
`0 → 1 → 2 → 3 → 0`. -/
def isFin4Clockwise3 (i₁ i₂ i₃ : Fin 4) : Bool :=
  decide ((i₁ < i₂ ∧ i₂ < i₃) ∨ (i₂ < i₃ ∧ i₃ < i₁) ∨ (i₃ < i₁ ∧ i₁ < i₂))

private theorem wallCornerCyclicPerm_apply_0 {α β : Type*} (W : GM13.Wall α β) :
    (GM13.wallCornerCyclicPerm W) (W.corner 0) = W.corner 1 := by
  simp [GM13.wallCornerCyclicPerm]

private theorem wallCornerCyclicPerm_apply_1 {α β : Type*} (W : GM13.Wall α β) :
    (GM13.wallCornerCyclicPerm W) (W.corner 1) = W.corner 2 := by
  have h01 : W.corner 1 ≠ W.corner 0 := W.corner_injective.ne (by decide)
  simp [GM13.wallCornerCyclicPerm, h01]

private theorem wallCornerCyclicPerm_apply_2 {α β : Type*} (W : GM13.Wall α β) :
    (GM13.wallCornerCyclicPerm W) (W.corner 2) = W.corner 3 := by
  have h02 : W.corner 2 ≠ W.corner 0 := W.corner_injective.ne (by decide)
  have h12 : W.corner 2 ≠ W.corner 1 := W.corner_injective.ne (by decide)
  simp [GM13.wallCornerCyclicPerm, h02, h12]

private theorem wallCornerCyclicPerm_apply_3 {α β : Type*} (W : GM13.Wall α β) :
    (GM13.wallCornerCyclicPerm W) (W.corner 3) = W.corner 0 := by
  have h03 : W.corner 3 ≠ W.corner 0 := W.corner_injective.ne (by decide)
  have h13 : W.corner 3 ≠ W.corner 1 := W.corner_injective.ne (by decide)
  have h23 : W.corner 3 ≠ W.corner 2 := W.corner_injective.ne (by decide)
  simp [GM13.wallCornerCyclicPerm, h03, h13, h23]

private theorem wallCornerCyclicPerm_firstHitIn_step1 {α β : Type*} (W : GM13.Wall α β)
    {X : Set α} {i j : Fin 4}
    (hstep : (GM13.wallCornerCyclicPerm W) (W.corner i) = W.corner j)
    (hjX : W.corner j ∈ X) :
    (GM13.wallCornerCyclicPerm W).FirstHitIn X (W.corner i) (W.corner j) :=
  ⟨1, le_rfl, hstep, hjX, fun _ hk1 hkl => by omega⟩

private theorem wallCornerCyclicPerm_firstHitIn_step2 {α β : Type*} (W : GM13.Wall α β)
    {X : Set α} {i m j : Fin 4}
    (hstep1 : (GM13.wallCornerCyclicPerm W) (W.corner i) = W.corner m)
    (hstep2 : (GM13.wallCornerCyclicPerm W) (W.corner m) = W.corner j)
    (hm_not : W.corner m ∉ X)
    (hjX : W.corner j ∈ X) :
    (GM13.wallCornerCyclicPerm W).FirstHitIn X (W.corner i) (W.corner j) := by
  refine ⟨2, by omega, ?_, hjX, fun k hk1 hk2 => ?_⟩
  · change (GM13.wallCornerCyclicPerm W) ((GM13.wallCornerCyclicPerm W) (W.corner i)) = W.corner j
    rw [hstep1, hstep2]
  · have hk_eq : k = 1 := by omega
    subst hk_eq
    change (GM13.wallCornerCyclicPerm W) (W.corner i) ∉ X
    rw [hstep1]
    exact hm_not

private theorem wallCornerCyclicPerm_isClockwise3_of_lt {α β : Type*} (W : GM13.Wall α β)
    {i₁ i₂ i₃ : Fin 4} (h12 : i₁ < i₂) (h23 : i₂ < i₃) :
    (GM13.wallCornerCyclicPerm W).IsClockwise3 (W.corner i₁) (W.corner i₂) (W.corner i₃) := by
  have h01 : W.corner 0 ≠ W.corner 1 := W.corner_injective.ne (by decide)
  have h02 : W.corner 0 ≠ W.corner 2 := W.corner_injective.ne (by decide)
  have h03 : W.corner 0 ≠ W.corner 3 := W.corner_injective.ne (by decide)
  have h12' : W.corner 1 ≠ W.corner 2 := W.corner_injective.ne (by decide)
  have h13 : W.corner 1 ≠ W.corner 3 := W.corner_injective.ne (by decide)
  have h23' : W.corner 2 ≠ W.corner 3 := W.corner_injective.ne (by decide)
  have hbar : ∀ i : Fin 4, W.corner i ∈ (GM13.wallCornerCyclicPerm W).bar := fun i => ⟨i, rfl⟩
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases i₃ <;> try (exfalso; revert h12 h23; decide)
  · -- (0, 1, 2)
    rw [CyclicPerm.isClockwise3_iff]
    refine ⟨h01, h02, h12', hbar 0, hbar 1, hbar 2,
      wallCornerCyclicPerm_firstHitIn_step1 W (wallCornerCyclicPerm_apply_0 W) (by simp),
      wallCornerCyclicPerm_firstHitIn_step1 W (wallCornerCyclicPerm_apply_1 W) (by simp),
      wallCornerCyclicPerm_firstHitIn_step2 W (wallCornerCyclicPerm_apply_2 W)
        (wallCornerCyclicPerm_apply_3 W) (by simp [Ne.symm h03, Ne.symm h13, Ne.symm h23'])
        (by simp)⟩
  · -- (0, 1, 3)
    rw [CyclicPerm.isClockwise3_iff]
    refine ⟨h01, h03, h13, hbar 0, hbar 1, hbar 3,
      wallCornerCyclicPerm_firstHitIn_step1 W (wallCornerCyclicPerm_apply_0 W) (by simp),
      wallCornerCyclicPerm_firstHitIn_step2 W (wallCornerCyclicPerm_apply_1 W)
        (wallCornerCyclicPerm_apply_2 W) (by simp [Ne.symm h02, Ne.symm h12', h23'])
        (by simp),
      wallCornerCyclicPerm_firstHitIn_step1 W (wallCornerCyclicPerm_apply_3 W) (by simp)⟩
  · -- (0, 2, 3)
    rw [CyclicPerm.isClockwise3_iff]
    refine ⟨h02, h03, h23', hbar 0, hbar 2, hbar 3,
      wallCornerCyclicPerm_firstHitIn_step2 W (wallCornerCyclicPerm_apply_0 W)
        (wallCornerCyclicPerm_apply_1 W) (by simp [Ne.symm h01, h12', h13])
        (by simp),
      wallCornerCyclicPerm_firstHitIn_step1 W (wallCornerCyclicPerm_apply_2 W) (by simp),
      wallCornerCyclicPerm_firstHitIn_step1 W (wallCornerCyclicPerm_apply_3 W) (by simp)⟩
  · -- (1, 2, 3)
    rw [CyclicPerm.isClockwise3_iff]
    refine ⟨h12', h13, h23', hbar 1, hbar 2, hbar 3,
      wallCornerCyclicPerm_firstHitIn_step1 W (wallCornerCyclicPerm_apply_1 W) (by simp),
      wallCornerCyclicPerm_firstHitIn_step1 W (wallCornerCyclicPerm_apply_2 W) (by simp),
      wallCornerCyclicPerm_firstHitIn_step2 W (wallCornerCyclicPerm_apply_3 W)
        (wallCornerCyclicPerm_apply_0 W) (by simp [h01, h02, h03])
        (by simp)⟩

theorem wallCornerCyclicPerm_isClockwise3_of_isFin4Clockwise3 {α β : Type*}
    (W : GM13.Wall α β) {i₁ i₂ i₃ : Fin 4}
    (h : isFin4Clockwise3 i₁ i₂ i₃ = true) :
    (GM13.wallCornerCyclicPerm W).IsClockwise3 (W.corner i₁) (W.corner i₂) (W.corner i₃) := by
  unfold isFin4Clockwise3 at h
  rw [decide_eq_true_eq] at h
  rcases h with ⟨h12, h23⟩ | ⟨h23, h31⟩ | ⟨h31, h12⟩
  · exact wallCornerCyclicPerm_isClockwise3_of_lt W h12 h23
  · have hcw := wallCornerCyclicPerm_isClockwise3_of_lt W h23 h31
    exact (GM13.wallCornerCyclicPerm W).isClockwise3_rotate
      ((GM13.wallCornerCyclicPerm W).isClockwise3_rotate hcw)
  · have hcw := wallCornerCyclicPerm_isClockwise3_of_lt W h31 h12
    exact (GM13.wallCornerCyclicPerm W).isClockwise3_rotate hcw

theorem isFin4Clockwise3_trichotomy {i₁ i₂ i₃ : Fin 4}
    (h12 : i₁ ≠ i₂) (h13 : i₁ ≠ i₃) (h23 : i₂ ≠ i₃) :
    isFin4Clockwise3 i₁ i₂ i₃ = true ∨ isFin4Clockwise3 i₁ i₃ i₂ = true := by
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases i₃ <;> revert h12 h13 h23 <;> decide

/-- Decidable check that `t₁, t₂, t₃ : ℕ` appear in clockwise order in `corners : List ℕ` (of length 4). -/
def isClockwiseCorners (corners : List ℕ) (t₁ t₂ t₃ : ℕ) : Bool :=
  (List.finRange 4).any fun i₁ =>
    (List.finRange 4).any fun i₂ =>
      (List.finRange 4).any fun i₃ =>
        decide (corners.getD i₁.1 0 = t₁ ∧ corners.getD i₂.1 0 = t₂ ∧ corners.getD i₃.1 0 = t₃) &&
          isFin4Clockwise3 i₁ i₂ i₃

theorem isClockwiseCorners_implies_isClockwise3 {n : ℕ} {D_del : MultiDigraph n}
    {X' : Finset (Fin n)} (p : ParsedCase3Block D_del X') {t₁ t₂ t₃ : ℕ}
    (hcw : isClockwiseCorners p.corners t₁ t₂ t₃ = true) :
    p.toSociety.Ω.IsClockwise3 t₁ t₂ t₃ := by
  unfold isClockwiseCorners at hcw
  simp only [List.any_eq_true, List.mem_finRange, true_and, Bool.and_eq_true,
    decide_eq_true_eq] at hcw
  rcases hcw with ⟨i₁, i₂, i₃, ⟨ht₁, ht₂, ht₃⟩, hfin⟩
  have hget : ∀ i : Fin 4, p.corners.getD i.1 0 = p.toGMWall.corner i := by
    intro i
    rw [p.hcorners_eq, List.getD_eq_getElem _ _ (by simp [i.2]), List.getElem_ofFn]
    exact (p.wallSec.W.toGMWall_corner p.wallSec.h2 p.wallSec.he p.wallSec.hW i).symm
  rw [← ht₁, ← ht₂, ← ht₃, hget i₁, hget i₂, hget i₃]
  exact wallCornerCyclicPerm_isClockwise3_of_isFin4Clockwise3 p.toGMWall hfin

/-! ### Section 3: Subdigraphs `Ã` (`subdigraphOfLists`, `memberTildeAVList`) -/

/-- Subdigraph of `G.toGMDigraph` specified by vertex list `vList` and edge list `eList`. -/
def subdigraphOfLists {n : ℕ} (G : MultiDigraph n)
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) : GM13.Digraph ℕ (ℕ × ℕ × ℕ) :=
  G.toGMDigraph.subdigraphOf {v : ℕ | v ∈ vList} {e : ℕ × ℕ × ℕ | e ∈ eList}

theorem isSubdigraph_subdigraphOfLists {n : ℕ} (G : MultiDigraph n)
    (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) :
    (subdigraphOfLists G vList eList).IsSubdigraph G.toGMDigraph where
  vertexSet_subset := Set.inter_subset_left
  edgeSet_subset _ he := he.1.1
  head_eq _ _ := rfl
  tail_eq _ _ := rfl

@[simp]
theorem vertexSet_subdigraphOfLists_of_valid {n : ℕ} (G : MultiDigraph n)
    {vList : List ℕ} (eList : List (ℕ × ℕ × ℕ))
    (hv : ∀ v ∈ vList, v < n) :
    (subdigraphOfLists G vList eList).vertexSet = {v : ℕ | v ∈ vList} := by
  change G.toGMDigraph.vertexSet ∩ {v : ℕ | v ∈ vList} = {v : ℕ | v ∈ vList}
  rw [Set.inter_eq_right]
  intro v hv_mem
  exact hv v hv_mem

@[simp]
theorem edgeSet_subdigraphOfLists_of_valid {n : ℕ} (G : MultiDigraph n)
    {vList : List ℕ} {eList : List (ℕ × ℕ × ℕ)}
    (he : ∀ e ∈ eList, isDelGraphEdge G e = true ∧ e.1 ∈ vList ∧ e.2.1 ∈ vList) :
    (subdigraphOfLists G vList eList).edgeSet = {e : ℕ × ℕ × ℕ | e ∈ eList} := by
  change {e ∈ G.toGMDigraph.edgeSet ∩ {e | e ∈ eList} | e.2.1 ∈ vList ∧ e.1 ∈ vList} =
    {e : ℕ × ℕ × ℕ | e ∈ eList}
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨_, he_mem⟩, _⟩
    exact he_mem
  · intro he_mem
    rcases he e he_mem with ⟨heG, he1, he2⟩
    exact ⟨⟨isDelGraphEdge_eq_true_iff_mem_toGMDigraph.mp heG, he_mem⟩, he2, he1⟩

/-- Canonical vertex list `(sSeq ++ xSeq) ++ r.vList.filter (· ∉ sSeq)` of `Ã` for a member record `r`
with boundary sequence `sSeq` and deleted set sequence `xSeq`. -/
def memberTildeAVList (xSeq : List ℕ) (r : Case3MemberRecord) (sSeq : List ℕ) : List ℕ :=
  (sSeq ++ xSeq) ++ r.vList.filter (fun v => decide (v ∉ sSeq))

theorem take_memberTildeAVList (xSeq : List ℕ) (r : Case3MemberRecord) (sSeq : List ℕ) :
    (memberTildeAVList xSeq r sSeq).take (sSeq ++ xSeq).length = sSeq ++ xSeq := by
  unfold memberTildeAVList
  exact List.take_left

theorem le_length_memberTildeAVList (xSeq : List ℕ) (r : Case3MemberRecord) (sSeq : List ℕ) :
    (sSeq ++ xSeq).length ≤ (memberTildeAVList xSeq r sSeq).length := by
  unfold memberTildeAVList
  simp

theorem mem_memberTildeAVList_iff (xSeq : List ℕ) (r : Case3MemberRecord) (sSeq : List ℕ)
    (hs_sub : ∀ s ∈ sSeq, s ∈ r.vList) (v : ℕ) :
    v ∈ memberTildeAVList xSeq r sSeq ↔ v ∈ r.vList ∨ v ∈ xSeq := by
  unfold memberTildeAVList
  simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ((hvs | hvx) | ⟨hvr, _⟩)
    · exact Or.inl (hs_sub v hvs)
    · exact Or.inr hvx
    · exact Or.inl hvr
  · rintro (hvr | hvx)
    · by_cases hvs : v ∈ sSeq
      · exact Or.inl (Or.inl hvs)
      · exact Or.inr ⟨hvr, hvs⟩
    · exact Or.inl (Or.inr hvx)

theorem nodup_memberTildeAVList (xSeq : List ℕ) (r : Case3MemberRecord) (sSeq : List ℕ)
    (hx_nd : xSeq.Nodup) (hr_nd : r.vList.Nodup) (hs_nd : sSeq.Nodup)
    (hs_sub : ∀ s ∈ sSeq, s ∈ r.vList)
    (hdisj_rx : ∀ v ∈ r.vList, v ∉ xSeq) :
    (memberTildeAVList xSeq r sSeq).Nodup := by
  unfold memberTildeAVList
  have hdisj_sx : List.Disjoint sSeq xSeq :=
    fun v hvs hvx => hdisj_rx v (hs_sub v hvs) hvx
  have hnd_sx : (sSeq ++ xSeq).Nodup := hs_nd.append hx_nd hdisj_sx
  have hnd_rem : (r.vList.filter (fun v => decide (v ∉ sSeq))).Nodup := hr_nd.filter _
  refine hnd_sx.append hnd_rem ?_
  intro v hvsx hvrem
  rw [List.mem_append] at hvsx
  rw [List.mem_filter, decide_eq_true_eq] at hvrem
  rcases hvsx with hvs | hvx
  · exact hvrem.2 hvs
  · exact hdisj_rx v hvrem.1 hvx

theorem deleteVertices_subdigraphOfLists_toGraph {n : ℕ} {G : MultiDigraph n}
    {X' : Finset (Fin n)} (p : ParsedCase3Block (G.deleteVertices X') X')
    {xSeq : List ℕ} (hx_set : {x : ℕ | x ∈ xSeq} = X'.toNatSet)
    {r : Case3MemberRecord} (hr : r ∈ p.members)
    {sSeq : List ℕ} (hs_sub : ∀ s ∈ sSeq, s ∈ r.vList)
    {eList : List (ℕ × ℕ × ℕ)}
    (he_valid : ∀ e ∈ eList,
      isDelGraphEdge G e = true ∧
      e.1 ∈ memberTildeAVList xSeq r sSeq ∧
      e.2.1 ∈ memberTildeAVList xSeq r sSeq)
    (he_filter : eList.filter (fun e => decide (e.1 ∉ xSeq ∧ e.2.1 ∉ xSeq)) = r.eList) :
    ((subdigraphOfLists G (memberTildeAVList xSeq r sSeq) eList).deleteVertices
      X'.toNatSet).toGraph =
      r.toSubgraph (delGraph G X') := by
  let vList := memberTildeAVList xSeq r sSeq
  have hr_val := p.member_valid_iff hr
  have hv_lt : ∀ v ∈ vList, v < n := by
    intro v hv
    rw [mem_memberTildeAVList_iff xSeq r sSeq hs_sub] at hv
    rcases hv with hvr | hvx
    · have hv_del := p.K_vList_mem_delGraph (hr_val.2.2.1 v hvr)
      exact ((mem_vertexSet_delGraph_iff G X' v).mp hv_del).1
    · have hvX : v ∈ X'.toNatSet := hx_set ▸ hvx
      rcases hvX with ⟨w, _, rfl⟩
      exact w.2
  have hD_V : (subdigraphOfLists G vList eList).vertexSet = {v : ℕ | v ∈ vList} :=
    vertexSet_subdigraphOfLists_of_valid G eList hv_lt
  have hD_E : (subdigraphOfLists G vList eList).edgeSet = {e : ℕ × ℕ × ℕ | e ∈ eList} :=
    edgeSet_subdigraphOfLists_of_valid G he_valid
  have hdisj_rx : ∀ v ∈ r.vList, v ∉ X'.toNatSet := by
    intro v hvr hvX
    have hv_del := p.K_vList_mem_delGraph (hr_val.2.2.1 v hvr)
    rw [vertexSet_delGraph] at hv_del
    exact hv_del.2 hvX
  have hV_del :
      V(((subdigraphOfLists G vList eList).deleteVertices X'.toNatSet).toGraph) =
        {v : ℕ | v ∈ r.vList} := by
    change (subdigraphOfLists G vList eList).vertexSet ∩
        ((subdigraphOfLists G vList eList).vertexSet \ X'.toNatSet) =
      {v : ℕ | v ∈ r.vList}
    rw [Set.inter_eq_right.mpr Set.sdiff_subset, hD_V]
    dsimp only [vList]
    ext v
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq,
      mem_memberTildeAVList_iff xSeq r sSeq hs_sub, ← hx_set]
    constructor
    · rintro ⟨hvr | hvx, hnot⟩
      · exact hvr
      · exact False.elim (hnot hvx)
    · intro hvr
      have hnot : v ∉ xSeq := fun hvx => hdisj_rx v hvr (hx_set ▸ hvx)
      exact ⟨Or.inl hvr, hnot⟩
  have hE_del :
      ∀ e : ℕ × ℕ × ℕ,
        e ∈ E(((subdigraphOfLists G vList eList).deleteVertices X'.toNatSet).toGraph) ↔
          e ∈ r.eList := by
    intro e
    change (e ∈ (subdigraphOfLists G vList eList).edgeSet ∧
        e.2.1 ∈ (subdigraphOfLists G vList eList).vertexSet \ X'.toNatSet ∧
        e.1 ∈ (subdigraphOfLists G vList eList).vertexSet \ X'.toNatSet) ↔
      e ∈ r.eList
    rw [hD_E, hD_V, ← he_filter]
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, ← hx_set, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨he, ⟨_, he2⟩, ⟨_, he1⟩⟩
      exact ⟨he, he1, he2⟩
    · rintro ⟨he, he1, he2⟩
      rcases he_valid e he with ⟨_, hv1, hv2⟩
      exact ⟨he, ⟨hv2, he2⟩, ⟨hv1, he1⟩⟩
  refine Graph.ext ?_ fun e x y => ?_
  · rw [hV_del, p.vertexSet_member_toSubgraph hr]
  · have hle_r : r.toSubgraph (delGraph G X') ≤ delGraph G X' := subgraphOfLists_le _ _ _
    constructor
    · intro hlink
      have he_mem : e ∈ r.eList := (hE_del e).mp hlink.edge_mem
      have he_r : e ∈ E(r.toSubgraph (delGraph G X')) := by
        rw [p.edgeSet_member_toSubgraph hr]
        exact he_mem
      have he_K := (hr_val.2.2.2.2.2.1 e he_mem).1
      have he_del : e ∈ E(delGraph G X') := (p.K_eList_mem_delGraph he_K).1
      have hlink_del : (delGraph G X').IsLink e x y := by
        rw [delGraph_eq] at he_del ⊢
        exact ⟨he_del, hlink.2⟩
      exact (hle_r.isLink_iff he_r).mpr hlink_del
    · intro hlink
      have he_r : e ∈ r.eList := by
        have hm := hlink.edge_mem
        rwa [p.edgeSet_member_toSubgraph hr] at hm
      have he_del_sub :
          e ∈ E(((subdigraphOfLists G vList eList).deleteVertices X'.toNatSet).toGraph) :=
        (hE_del e).mpr he_r
      have hlink_del : (delGraph G X').IsLink e x y := hlink.mono hle_r
      rw [delGraph_eq] at hlink_del
      exact ⟨he_del_sub, hlink_del.2⟩

/-! ### Section 4: Vision Output Format, Pure Reading Parser, and `toGMVision` -/

/-- Decidable check for a valid path `L : List ℕ` in `K = p.toSociety.G` between `s` and `t`. -/
def isValidKPathBetween (K_vList : List ℕ) (K_eList : List (ℕ × ℕ × ℕ))
    (L : List ℕ) (s t : ℕ) : Bool :=
  if hne : L ≠ [] then
    decide L.Nodup &&
    decide (∀ v ∈ L, v ∈ K_vList) &&
    decide (IsKWalkList K_eList L) &&
    decide (L.head hne = s ∧ L.getLast hne = t)
  else false

/-- Serialized vision record for one member `j < p.members.length` of `𝒜`. -/
structure VisionMemberRecord where
  isInterior : ℕ
  sSeq : List ℕ
  P₁ : List ℕ
  P₂ : List ℕ
  P₃ : List ℕ
  tildeA_vList : List ℕ
  tildeA_eList : List (ℕ × ℕ × ℕ)
  folioWords : List ℕ
  folioCode : ℕ
  vOf : ℕ
  vOfPath : List ℕ
  deriving DecidableEq

/-- Flat `List ℕ` encoding of a `VisionMemberRecord`. -/
def VisionMemberRecord.enc (m : VisionMemberRecord) : List ℕ :=
  [m.isInterior] ++
  (m.sSeq.length :: m.sSeq) ++
  (m.P₁.length :: m.P₁) ++
  (m.P₂.length :: m.P₂) ++
  (m.P₃.length :: m.P₃) ++
  (m.tildeA_vList.length :: m.tildeA_vList) ++
  (m.tildeA_eList.length :: encEdgeTriples m.tildeA_eList) ++
  (m.folioWords.length :: m.folioWords) ++
  [m.folioCode, m.vOf] ++
  (m.vOfPath.length :: m.vOfPath)

/-- Parse a length-prefixed `List ℕ` from the front of `l`. -/
def takeLengthPrefixedNat (l : List ℕ) : Option (List ℕ × List ℕ) :=
  match l with
  | [] => none
  | len :: rest => takeExactNat len rest

@[simp]
theorem takeLengthPrefixedNat_append (xs rest : List ℕ) :
    takeLengthPrefixedNat (xs.length :: xs ++ rest) = some (xs, rest) := by
  unfold takeLengthPrefixedNat
  exact takeExactNat_append xs rest

/-- Parse one `VisionMemberRecord` from the front of `l : List ℕ`. -/
def parseOneVisionMemberRecord (l : List ℕ) : Option (VisionMemberRecord × List ℕ) :=
  match l with
  | [] => none
  | isInt :: rest₁ =>
    match takeLengthPrefixedNat rest₁ with
    | none => none
    | some (sSeq, rest₂) =>
      match takeLengthPrefixedNat rest₂ with
      | none => none
      | some (P₁, rest₃) =>
        match takeLengthPrefixedNat rest₃ with
        | none => none
        | some (P₂, rest₄) =>
          match takeLengthPrefixedNat rest₄ with
          | none => none
          | some (P₃, rest₅) =>
            match takeLengthPrefixedNat rest₅ with
            | none => none
            | some (tildeA_vList, rest₆) =>
              match rest₆ with
              | [] => none
              | e_len :: rest₇ =>
                match takeEdgeTriples e_len rest₇ with
                | none => none
                | some (tildeA_eList, rest₈) =>
                  match takeLengthPrefixedNat rest₈ with
                  | none => none
                  | some (folioWords, rest₉) =>
                    match rest₉ with
                    | code :: vOf :: rest₁₀ =>
                      match takeLengthPrefixedNat rest₁₀ with
                      | none => none
                      | some (vOfPath, rest₁₁) =>
                        some (⟨isInt, sSeq, P₁, P₂, P₃, tildeA_vList, tildeA_eList,
                          folioWords, code, vOf, vOfPath⟩, rest₁₁)
                    | _ => none

@[simp]
theorem parseOneVisionMemberRecord_enc_append (m : VisionMemberRecord) (rest : List ℕ) :
    parseOneVisionMemberRecord (m.enc ++ rest) = some (m, rest) := by
  unfold VisionMemberRecord.enc parseOneVisionMemberRecord takeLengthPrefixedNat
  simp only [List.cons_append, List.nil_append, List.append_assoc,
    takeExactNat_append, takeEdgeTriples_encEdgeTriples_append]

/-- Parse `k` consecutive `VisionMemberRecord`s from the front of `l`. -/
def parseVisionMemberRecords : ℕ → List ℕ → Option (List VisionMemberRecord × List ℕ)
  | 0, l => some ([], l)
  | k + 1, l =>
    match parseOneVisionMemberRecord l with
    | none => none
    | some (m, rest) =>
      match parseVisionMemberRecords k rest with
      | none => none
      | some (ms, rest') => some (m :: ms, rest')

@[simp]
theorem parseVisionMemberRecords_flatMap_enc_append (ms : List VisionMemberRecord) (rest : List ℕ) :
    parseVisionMemberRecords ms.length (ms.flatMap VisionMemberRecord.enc ++ rest) =
      some (ms, rest) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
      parseVisionMemberRecords, parseOneVisionMemberRecord_enc_append, ih]

theorem length_fst_of_parseVisionMemberRecords {k : ℕ} {l : List ℕ}
    {ms : List VisionMemberRecord} {rest : List ℕ}
    (h : parseVisionMemberRecords k l = some (ms, rest)) :
    ms.length = k := by
  induction k generalizing l ms rest with
  | zero =>
    simp only [parseVisionMemberRecords, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩
    rfl
  | succ k ih =>
    unfold parseVisionMemberRecords at h
    cases h1 : parseOneVisionMemberRecord l with
    | none => simp [h1] at h
    | some p₁ =>
      rcases p₁ with ⟨m, rest₁⟩
      rw [h1] at h
      dsimp only at h
      cases h2 : parseVisionMemberRecords k rest₁ with
      | none => simp [h2] at h
      | some p₂ =>
        rcases p₂ with ⟨ms', rest₂⟩
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp [ih h2]

/-- Decidable check that `m.folioWords` parses via `parseFolioAndModelsFull` and has
`m.folioCode = folioRepCode q folioOut.folio`. -/
def isValidMemberFolioWords (q δ : ℕ) (xSeq : List ℕ) (m : VisionMemberRecord) : Bool :=
  match parseFolioAndModelsFull
      (tildeAMultiDigraph m.tildeA_vList m.tildeA_eList)
      (prefixRootFinset m.tildeA_vList.length (m.sSeq ++ xSeq).length)
      δ m.folioWords with
  | some folioOut => decide (m.folioCode = folioRepCode q folioOut.folio)
  | none => false

/-- Decidable validity check for one `VisionMemberRecord` `m` corresponding to `r ∈ p.members`. -/
def isValidVisionMemberRecord {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n))
    (p : ParsedCase3Block (G.deleteVertices X') X')
    (q δ : ℕ) (xSeq : List ℕ) (r : Case3MemberRecord) (m : VisionMemberRecord) : Bool :=
  let bList := memberBoundaryList p.corners p.K_eList r
  let isInt := if isMemberInterior p.wallSec.W r then 1 else 0
  decide (m.isInterior = isInt) &&
  decide (m.tildeA_vList = memberTildeAVList xSeq r m.sSeq) &&
  decide m.tildeA_eList.Nodup &&
  decide (m.tildeA_eList.length ≤ G.numEdges) &&
  decide (∀ e ∈ m.tildeA_eList,
    isDelGraphEdge G e = true ∧ e.1 ∈ m.tildeA_vList ∧ e.2.1 ∈ m.tildeA_vList) &&
  decide (m.tildeA_eList.filter (fun e => decide (e.1 ∉ xSeq ∧ e.2.1 ∉ xSeq)) = r.eList) &&
  (if isMemberInterior p.wallSec.W r then
    decide m.sSeq.Nodup &&
    decide (m.sSeq.toFinset = bList.toFinset) &&
    decide (m.sSeq.length ≤ 3) &&
    (if m.sSeq.length = 3 then
      let s₁ := m.sSeq.getD 0 0
      let s₂ := m.sSeq.getD 1 0
      let s₃ := m.sSeq.getD 2 0
      let t₁ := m.P₁.getLastD 0
      let t₂ := m.P₂.getLastD 0
      let t₃ := m.P₃.getLastD 0
      isValidKPathBetween p.K_vList p.K_eList m.P₁ s₁ t₁ &&
      isValidKPathBetween p.K_vList p.K_eList m.P₂ s₂ t₂ &&
      isValidKPathBetween p.K_vList p.K_eList m.P₃ s₃ t₃ &&
      decide ((∀ v ∈ m.P₁, v ∉ m.P₂) ∧ (∀ v ∈ m.P₁, v ∉ m.P₃) ∧ (∀ v ∈ m.P₂, v ∉ m.P₃)) &&
      decide (∀ v ∈ m.P₁, (v ∈ bList ↔ v = s₁) ∧ (v ∈ p.corners ↔ v = t₁)) &&
      decide (∀ v ∈ m.P₂, (v ∈ bList ↔ v = s₂) ∧ (v ∈ p.corners ↔ v = t₂)) &&
      decide (∀ v ∈ m.P₃, (v ∈ bList ↔ v = s₃) ∧ (v ∈ p.corners ↔ v = t₃)) &&
      isClockwiseCorners p.corners t₁ t₂ t₃
    else true) &&
    decide (m.vOf ∈ p.wallSec.W.vertexFinset.image Fin.val) &&
    (let s₀ := m.vOfPath.headD 0
     isValidKPathBetween p.K_vList p.K_eList m.vOfPath s₀ m.vOf &&
     decide ((s₀ ∈ bList) ∨ (bList = [] ∧ s₀ ∈ r.vList)) &&
     decide (∀ v ∈ m.vOfPath, v ∈ p.wallSec.W.vertexFinset.image Fin.val ↔ v = m.vOf)) &&
    isValidMemberFolioWords q δ xSeq m
  else
    decide (m.sSeq = []))

/-- List of all edges `(u, v, k)` of `G` with both endpoints in `xSeq ++ p.K_vList`. -/
def allXKMultiDigraphEdges {n : ℕ} (G : MultiDigraph n)
    (xSeq K_vList : List ℕ) : List (ℕ × ℕ × ℕ) :=
  let xkSet := (xSeq ++ K_vList).toFinset
  (List.finRange n).flatMap fun u =>
    (List.finRange n).flatMap fun v =>
      if u.1 ∈ xkSet ∧ v.1 ∈ xkSet then
        (List.range (G.edgeMult u v)).map fun k => (u.1, v.1, k)
      else []

theorem mem_allXKMultiDigraphEdges_iff {n : ℕ} (G : MultiDigraph n)
    (xSeq K_vList : List ℕ) (e : ℕ × ℕ × ℕ) :
    e ∈ allXKMultiDigraphEdges G xSeq K_vList ↔
      e ∈ G.toGMDigraph.edgeSet ∧
      (e.1 ∈ xSeq ∨ e.1 ∈ K_vList) ∧
      (e.2.1 ∈ xSeq ∨ e.2.1 ∈ K_vList) := by
  rcases e with ⟨u, v, k⟩
  unfold allXKMultiDigraphEdges
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_toFinset, List.mem_append,
    MultiDigraph.toGMDigraph, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u', v', hmem⟩
    split_ifs at hmem with hxk
    · simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hmem
      rcases hmem with ⟨k', hk', rfl, rfl, rfl⟩
      exact ⟨⟨u'.2, v'.2, hk'⟩, hxk.1, hxk.2⟩
    · nomatch hmem
  · rintro ⟨⟨hu, hv, hk⟩, hu_xk, hv_xk⟩
    refine ⟨⟨u, hu⟩, ⟨v, hv⟩, ?_⟩
    rw [ite_eq_left ⟨hu_xk, hv_xk⟩]
    simp [hk]

/-- Complete parsed and validated Vision output of Algorithm (10.1). -/
structure ParsedVisionOutput {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n))
    (p : ParsedCase3Block (G.deleteVertices X') X') (q δ : ℕ) where
  xSeq : List ℕ
  records : List VisionMemberRecord
  hx_nodup : xSeq.Nodup
  hx_set : xSeq.toFinset = X'.image Fin.val
  hmembers_ne : p.members ≠ []
  hrecords_len : records.length = p.members.length
  hrecords_valid : ∀ j : Fin p.members.length,
    isValidVisionMemberRecord G X' p q δ xSeq
      (p.members[j.1]'j.2) (records[j.1]'(by rw [hrecords_len]; exact j.2)) = true
  hedges_nodup : ((records.map VisionMemberRecord.tildeA_eList).flatten).Nodup
  hedges_cover : ∀ e ∈ allXKMultiDigraphEdges G xSeq p.K_vList,
    e ∈ (records.map VisionMemberRecord.tildeA_eList).flatten

/-- Pure reading parser for the Vision output of Algorithm (10.1). -/
def parseVisionOutput {n : ℕ} (G : MultiDigraph n) (X' : Finset (Fin n))
    (p : ParsedCase3Block (G.deleteVertices X') X') (q δ : ℕ)
    (words : List ℕ) : Option (ParsedVisionOutput G X' p q δ) :=
  match takeLengthPrefixedNat words with
  | none => none
  | some (xSeq, rest₁) =>
    match rest₁ with
    | [] => none
    | num_rec :: rest₂ =>
      match parseVisionMemberRecords num_rec rest₂ with
      | none => none
      | some (records, _) =>
        if hrec_len : records.length = p.members.length then
          if hcond :
              xSeq.Nodup ∧
              xSeq.toFinset = X'.image Fin.val ∧
              p.members ≠ [] ∧
              (∀ j : Fin p.members.length,
                isValidVisionMemberRecord G X' p q δ xSeq
                  (p.members[j.1]'j.2) (records[j.1]'(by rw [hrec_len]; exact j.2)) = true) ∧
              ((records.map VisionMemberRecord.tildeA_eList).flatten).Nodup ∧
              (∀ e ∈ allXKMultiDigraphEdges G xSeq p.K_vList,
                e ∈ (records.map VisionMemberRecord.tildeA_eList).flatten) then
            some ⟨xSeq, records, hcond.1, hcond.2.1, hcond.2.2.1, hrec_len,
              hcond.2.2.2.1, hcond.2.2.2.2.1, hcond.2.2.2.2.2⟩
          else none
        else none

/-- Flat `List ℕ` encoder for the Vision output of Algorithm (10.1). -/
def encVisionOutput (xSeq : List ℕ) (records : List VisionMemberRecord) : List ℕ :=
  (xSeq.length :: xSeq) ++ (records.length :: records.flatMap VisionMemberRecord.enc)

@[simp]
theorem parseVisionOutput_encVisionOutput {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
    {p : ParsedCase3Block (G.deleteVertices X') X'} {q δ : ℕ}
    (vOut : ParsedVisionOutput G X' p q δ) (rest : List ℕ) :
    parseVisionOutput G X' p q δ (encVisionOutput vOut.xSeq vOut.records ++ rest) =
      some vOut := by
  have henc :
      encVisionOutput vOut.xSeq vOut.records ++ rest =
        (vOut.xSeq.length :: vOut.xSeq) ++
          (vOut.records.length :: (vOut.records.flatMap VisionMemberRecord.enc ++ rest)) := by
    simp [encVisionOutput, List.append_assoc]
  rw [henc]
  unfold parseVisionOutput
  rw [takeLengthPrefixedNat_append]
  dsimp only
  rw [parseVisionMemberRecords_flatMap_enc_append]
  dsimp only
  rw [dite_eq_left vOut.hrecords_len]
  have hcond :
      vOut.xSeq.Nodup ∧
      vOut.xSeq.toFinset = X'.image Fin.val ∧
      p.members ≠ [] ∧
      (∀ j : Fin p.members.length,
        isValidVisionMemberRecord G X' p q δ vOut.xSeq
          (p.members[j.1]'j.2) (vOut.records[j.1]'(by rw [vOut.hrecords_len]; exact j.2)) = true) ∧
      ((vOut.records.map VisionMemberRecord.tildeA_eList).flatten).Nodup ∧
      (∀ e ∈ allXKMultiDigraphEdges G vOut.xSeq p.K_vList,
        e ∈ (vOut.records.map VisionMemberRecord.tildeA_eList).flatten) :=
    ⟨vOut.hx_nodup, vOut.hx_set, vOut.hmembers_ne, vOut.hrecords_valid,
      vOut.hedges_nodup, vOut.hedges_cover⟩
  rw [dite_eq_left hcond]

namespace ParsedVisionOutput

variable {n : ℕ} {G : MultiDigraph n} {X' : Finset (Fin n)}
  {p : ParsedCase3Block (G.deleteVertices X') X'} {q δ : ℕ}
  (vOut : ParsedVisionOutput G X' p q δ)

theorem xSeq_set_eq : {x : ℕ | x ∈ vOut.xSeq} = X'.toNatSet := by
  ext x
  have h := Finset.ext_iff.mp vOut.hx_set x
  simpa [Finset.toNatSet] using h

/-- Look up the member index `j < p.members.length` whose subgraph is `A` (defaulting to `0`). -/
noncomputable def findMemberIdx (A : Graph ℕ (ℕ × ℕ × ℕ)) : Fin p.members.length :=
  have hpos : 0 < p.members.length := List.length_pos_of_ne_nil vOut.hmembers_ne
  letI : DecidablePred (fun j : Fin p.members.length =>
      (p.members[j.1]'j.2).toSubgraph (delGraph G X') = A) :=
    fun _ => Classical.propDecidable _
  match (List.finRange p.members.length).find?
      (fun j => decide ((p.members[j.1]'j.2).toSubgraph (delGraph G X') = A)) with
  | some j => j
  | none => ⟨0, hpos⟩

theorem member_injective {j₁ j₂ : Fin p.members.length}
    (heq : (p.members[j₁.1]'j₁.2).toSubgraph (delGraph G X') =
      (p.members[j₂.1]'j₂.2).toSubgraph (delGraph G X')) :
    j₁ = j₂ := by
  let r₁ := p.members[j₁.1]'j₁.2
  let r₂ := p.members[j₂.1]'j₂.2
  have hr₁ : r₁ ∈ p.members := List.getElem_mem j₁.2
  have hr₂ : r₂ ∈ p.members := List.getElem_mem j₂.2
  have hV_eq : {v : ℕ | v ∈ r₁.vList} = {v : ℕ | v ∈ r₂.vList} := by
    rw [← p.vertexSet_member_toSubgraph hr₁, ← p.vertexSet_member_toSubgraph hr₂, heq]
  have hE_eq : {e : ℕ × ℕ × ℕ | e ∈ r₁.eList} = {e : ℕ × ℕ × ℕ | e ∈ r₂.eList} := by
    rw [← p.edgeSet_member_toSubgraph hr₁, ← p.edgeSet_member_toSubgraph hr₂, heq]
  have hfinV : r₁.vList.toFinset = r₂.vList.toFinset := by
    ext v; simp only [List.mem_toFinset]; exact Set.ext_iff.mp hV_eq v
  have hfinE : r₁.eList.toFinset = r₂.eList.toFinset := by
    ext e; simp only [List.mem_toFinset]; exact Set.ext_iff.mp hE_eq e
  have hpair : (r₁.vList.toFinset, r₁.eList.toFinset) =
      (r₂.vList.toFinset, r₂.eList.toFinset) := Prod.ext hfinV hfinE
  have hnd := p.hmembers_distinct
  have hget :
      (p.members.map (fun r => (r.vList.toFinset, r.eList.toFinset)))[j₁.1]'(by simp [j₁.2]) =
      (p.members.map (fun r => (r.vList.toFinset, r.eList.toFinset)))[j₂.1]'(by simp [j₂.2]) := by
    simpa [r₁, r₂] using hpair
  exact Fin.ext ((hnd.getElem_inj_iff).mp hget)

@[simp]
theorem findMemberIdx_toSubgraph (j : Fin p.members.length) :
    vOut.findMemberIdx ((p.members[j.1]'j.2).toSubgraph (delGraph G X')) = j := by
  unfold findMemberIdx
  dsimp only
  let : DecidablePred (fun j' : Fin p.members.length =>
      (p.members[j'.1]'j'.2).toSubgraph (delGraph G X') =
        (p.members[j.1]'j.2).toSubgraph (delGraph G X')) :=
    fun _ => Classical.propDecidable _
  cases hfind : (List.finRange p.members.length).find?
      (fun j' => decide ((p.members[j'.1]'j'.2).toSubgraph (delGraph G X') =
        (p.members[j.1]'j.2).toSubgraph (delGraph G X'))) with
  | none =>
    have hfalse := List.find?_eq_none.mp hfind j (List.mem_finRange j)
    simp at hfalse
  | some j' =>
    have hpred := List.find?_some hfind
    simp only [decide_eq_true_eq] at hpred
    exact member_injective hpred

theorem exists_fin_of_mem_toDivision {A : Graph ℕ (ℕ × ℕ × ℕ)} (hA : A ∈ p.toDivision) :
    ∃ j : Fin p.members.length, (p.members[j.1]'j.2).toSubgraph (delGraph G X') = A := by
  rcases hA with ⟨r, hr, rfl⟩
  rcases List.mem_iff_getElem.mp hr with ⟨j, hj, rfl⟩
  exact ⟨⟨j, hj⟩, rfl⟩

/-- Record at index `j : Fin p.members.length`. -/
def recordAt (j : Fin p.members.length) : VisionMemberRecord :=
  vOut.records[j.1]'(by rw [vOut.hrecords_len]; exact j.2)

/-- Subdigraph `Ã_j` for member index `j : Fin p.members.length`. -/
def tildeAAt (j : Fin p.members.length) : GM13.Digraph ℕ (ℕ × ℕ × ℕ) :=
  let m := vOut.recordAt j
  subdigraphOfLists G m.tildeA_vList m.tildeA_eList

theorem recordAt_sSeq_subset_vList (j : Fin p.members.length) :
    ∀ s ∈ (vOut.recordAt j).sSeq, s ∈ (p.members[j.1]'j.2).vList := by
  let r := p.members[j.1]'j.2
  let m := vOut.recordAt j
  have hval := vOut.hrecords_valid j
  change isValidVisionMemberRecord G X' p q δ vOut.xSeq r m = true at hval
  unfold isValidVisionMemberRecord at hval
  rw [Bool.and_eq_true] at hval
  rcases hval with ⟨_, hbr⟩
  by_cases hint : isMemberInterior p.wallSec.W r = true
  · rw [ite_eq_left hint] at hbr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbr
    have hs_eq : m.sSeq.toFinset = (memberBoundaryList p.corners p.K_eList r).toFinset :=
      hbr.1.1.1.1.1.2
    intro s hs
    have hmem : s ∈ (memberBoundaryList p.corners p.K_eList r).toFinset := by
      rw [← hs_eq]
      exact List.mem_toFinset.mpr hs
    rw [List.mem_toFinset] at hmem
    unfold memberBoundaryList at hmem
    exact (List.mem_filter.mp hmem).1
  · rw [ite_eq_right hint, decide_eq_true_eq] at hbr
    intro s hs
    change s ∈ m.sSeq at hs
    rw [hbr] at hs
    nomatch hs

theorem tildeAAt_valid (j : Fin p.members.length) :
    (vOut.tildeAAt j).IsSubdigraph G.toGMDigraph ∧
    X'.toNatSet ⊆ (vOut.tildeAAt j).vertexSet ∧
    ((vOut.tildeAAt j).deleteVertices X'.toNatSet).toGraph =
      (p.members[j.1]'j.2).toSubgraph (delGraph G X') ∧
    (vOut.tildeAAt j).edgeSet = {e : ℕ × ℕ × ℕ | e ∈ (vOut.recordAt j).tildeA_eList} ∧
    (vOut.tildeAAt j).vertexSet = {v : ℕ | v ∈ (vOut.recordAt j).tildeA_vList} := by
  let r := p.members[j.1]'j.2
  let m := vOut.recordAt j
  have hr : r ∈ p.members := List.getElem_mem j.2
  have hr_val := p.member_valid_iff hr
  have hs_sub := vOut.recordAt_sSeq_subset_vList j
  have hval := vOut.hrecords_valid j
  change isValidVisionMemberRecord G X' p q δ vOut.xSeq r m = true at hval
  unfold isValidVisionMemberRecord at hval
  rw [Bool.and_eq_true] at hval
  rcases hval with ⟨hbase, _⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbase
  rcases hbase with ⟨⟨⟨⟨⟨_, hv_eq⟩, _⟩, _⟩, he_valid⟩, he_filter⟩
  have hv_lt : ∀ v ∈ m.tildeA_vList, v < n := by
    intro v hv
    rw [hv_eq, mem_memberTildeAVList_iff vOut.xSeq r m.sSeq hs_sub] at hv
    rcases hv with hvr | hvx
    · have hv_del := p.K_vList_mem_delGraph (hr_val.2.2.1 v hvr)
      exact ((mem_vertexSet_delGraph_iff G X' v).mp hv_del).1
    · have hvX : v ∈ X'.toNatSet := vOut.xSeq_set_eq ▸ hvx
      rcases hvX with ⟨w, _, rfl⟩
      exact w.2
  have hV : (vOut.tildeAAt j).vertexSet = {v : ℕ | v ∈ m.tildeA_vList} :=
    vertexSet_subdigraphOfLists_of_valid G m.tildeA_eList hv_lt
  have hE : (vOut.tildeAAt j).edgeSet = {e : ℕ × ℕ × ℕ | e ∈ m.tildeA_eList} :=
    edgeSet_subdigraphOfLists_of_valid G he_valid
  refine ⟨isSubdigraph_subdigraphOfLists G m.tildeA_vList m.tildeA_eList, ?_, ?_, hE, hV⟩
  · rw [hV, hv_eq, ← vOut.xSeq_set_eq]
    intro x hx
    exact (mem_memberTildeAVList_iff vOut.xSeq r m.sSeq hs_sub x).mpr (Or.inr hx)
  · unfold tildeAAt
    dsimp only
    rw [hv_eq]
    refine deleteVertices_subdigraphOfLists_toGraph p vOut.xSeq_set_eq hr hs_sub ?_ he_filter
    rwa [← hv_eq]

private theorem exists_unique_fin_of_flatten_nodup {α : Type*} {ls : List (List α)}
    (hnd : ls.flatten.Nodup) {x : α} (hx : x ∈ ls.flatten) :
    ∃ j : Fin ls.length, x ∈ ls[j.1]'j.2 ∧
      ∀ j' : Fin ls.length, x ∈ ls[j'.1]'j'.2 → j' = j := by
  induction ls with
  | nil => nomatch hx
  | cons l ls ih =>
    rw [List.flatten_cons, List.nodup_append] at hnd
    rw [List.flatten_cons, List.mem_append] at hx
    rcases hx with hxl | hxls
    · refine ⟨⟨0, by simp⟩, hxl, fun j' hj' => ?_⟩
      rcases j' with ⟨_ | k, hk⟩
      · rfl
      · have hmem_flat : x ∈ ls.flatten :=
          List.mem_flatten.mpr ⟨ls[k]'(by simpa using hk), List.getElem_mem _, hj'⟩
        exact False.elim (hnd.2.2 x hxl x hmem_flat rfl)
    · rcases ih hnd.2.1 hxls with ⟨j, hj_mem, hj_uniq⟩
      refine ⟨⟨j.1 + 1, by simp [j.2]⟩, hj_mem, fun j' hj' => ?_⟩
      rcases j' with ⟨_ | k, hk⟩
      · exact False.elim (hnd.2.2 x hj' x hxls rfl)
      · have hk' : k < ls.length := by simpa using hk
        have heq := hj_uniq ⟨k, hk'⟩ hj'
        exact Fin.ext (by simpa using congrArg Fin.val heq)

private theorem isGraphPathWithEnds_and_inter_of_isValidKPathBetween
    {L : List ℕ} {s t : ℕ}
    (hpath : isValidKPathBetween p.K_vList p.K_eList L s t = true) :
    ∃ P : Graph ℕ (ℕ × ℕ × ℕ),
      GM09.IsGraphPathWithEnds p.toSociety.G P s t ∧
      V(P) = {v : ℕ | v ∈ L} := by
  unfold isValidKPathBetween at hpath
  split_ifs at hpath with hne
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpath
  rcases hpath with ⟨⟨⟨hnd, hmem⟩, hw⟩, rfl, rfl⟩
  exact ⟨kPathGraph p hne hmem hw,
    isGraphPathWithEnds_kPathGraph p hne hmem hw hnd,
    vertexSet_kPathGraph p hne hmem hw⟩

theorem sSeq_valid_at (j : Fin p.members.length)
    (hInt : GM13.IsInteriorMember p.toGMWall p.toDivision
      ((p.members[j.1]'j.2).toSubgraph (delGraph G X'))) :
    GM13.IsClockwiseBoundaryNumbering p.toSociety
      ((p.members[j.1]'j.2).toSubgraph (delGraph G X'))
      (vOut.recordAt j).sSeq := by
  let r := p.members[j.1]'j.2
  let m := vOut.recordAt j
  have hr : r ∈ p.members := List.getElem_mem j.2
  have hint_bool : isMemberInterior p.wallSec.W r = true :=
    (isInteriorMember_toSubgraph_iff p hr).mp hInt
  have hval := vOut.hrecords_valid j
  change isValidVisionMemberRecord G X' p q δ vOut.xSeq r m = true at hval
  unfold isValidVisionMemberRecord at hval
  rw [Bool.and_eq_true] at hval
  rcases hval with ⟨_, hbr⟩
  rw [ite_eq_left hint_bool] at hbr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbr
  rcases hbr with ⟨⟨⟨⟨⟨⟨hs_nd, hs_fin⟩, _⟩, hcw_branch⟩, _⟩, _⟩, _⟩
  have hs_set : {x : ℕ | x ∈ m.sSeq} =
      GM13.divBoundary p.toSociety (r.toSubgraph (delGraph G X')) := by
    ext v
    have hfin := Finset.ext_iff.mp hs_fin v
    simp only [List.mem_toFinset] at hfin
    exact hfin.trans (mem_memberBoundaryList_iff p hr v)
  refine ⟨hs_nd, hs_set, fun s₁ s₂ s₃ heq => ?_⟩
  change m.sSeq = [s₁, s₂, s₃] at heq
  have hlen3 : m.sSeq.length = 3 := by rw [heq]; rfl
  rw [ite_eq_left hlen3] at hcw_branch
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcw_branch
  rcases hcw_branch with ⟨⟨⟨⟨⟨⟨⟨hP₁, hP₂⟩, hP₃⟩, hdisj⟩, hinter₁⟩, hinter₂⟩, hinter₃⟩, hcw⟩
  have hs₁ : m.sSeq.getD 0 0 = s₁ := by simp [heq]
  have hs₂ : m.sSeq.getD 1 0 = s₂ := by simp [heq]
  have hs₃ : m.sSeq.getD 2 0 = s₃ := by simp [heq]
  rw [hs₁] at hP₁ hinter₁
  rw [hs₂] at hP₂ hinter₂
  rw [hs₃] at hP₃ hinter₃
  let t₁ := m.P₁.getLastD 0
  let t₂ := m.P₂.getLastD 0
  let t₃ := m.P₃.getLastD 0
  obtain ⟨P₁, hpath₁, hV₁⟩ := isGraphPathWithEnds_and_inter_of_isValidKPathBetween hP₁
  obtain ⟨P₂, hpath₂, hV₂⟩ := isGraphPathWithEnds_and_inter_of_isValidKPathBetween hP₂
  obtain ⟨P₃, hpath₃, hV₃⟩ := isGraphPathWithEnds_and_inter_of_isValidKPathBetween hP₃
  have hmem_s₁ : s₁ ∈ m.P₁ := by
    have h := hpath₁.left_mem; rwa [hV₁, Set.mem_ofPred_eq] at h
  have hmem_t₁ : t₁ ∈ m.P₁ := by
    have h := hpath₁.right_mem; rwa [hV₁, Set.mem_ofPred_eq] at h
  have hmem_s₂ : s₂ ∈ m.P₂ := by
    have h := hpath₂.left_mem; rwa [hV₂, Set.mem_ofPred_eq] at h
  have hmem_t₂ : t₂ ∈ m.P₂ := by
    have h := hpath₂.right_mem; rwa [hV₂, Set.mem_ofPred_eq] at h
  have hmem_s₃ : s₃ ∈ m.P₃ := by
    have h := hpath₃.left_mem; rwa [hV₃, Set.mem_ofPred_eq] at h
  have hmem_t₃ : t₃ ∈ m.P₃ := by
    have h := hpath₃.right_mem; rwa [hV₃, Set.mem_ofPred_eq] at h
  refine ⟨P₁, P₂, P₃, t₁, t₂, t₃, ?_, ?_, ?_, hpath₁, ?_, ?_, hpath₂, ?_, ?_, hpath₃, ?_, ?_,
    isClockwiseCorners_implies_isClockwise3 p hcw⟩
  · rw [hV₁, hV₂, Set.disjoint_left]; exact hdisj.1
  · rw [hV₁, hV₃, Set.disjoint_left]; exact hdisj.2.1
  · rw [hV₂, hV₃, Set.disjoint_left]; exact hdisj.2.2
  · rw [hV₁]
    ext v
    change (v ∈ m.P₁ ∧ v ∈ GM13.divBoundary p.toSociety (r.toSubgraph (delGraph G X'))) ↔ v = s₁
    rw [← mem_memberBoundaryList_iff p hr v]
    exact ⟨fun ⟨hv, hb⟩ => (hinter₁ v hv).1.mp hb,
      by rintro rfl; exact ⟨hmem_s₁, (hinter₁ _ hmem_s₁).1.mpr rfl⟩⟩
  · rw [hV₁]
    ext v
    change (v ∈ m.P₁ ∧ v ∈ p.toSociety.Ω.bar) ↔ v = t₁
    rw [← mem_corners_iff_mem_bar p v]
    exact ⟨fun ⟨hv, hc⟩ => (hinter₁ v hv).2.mp hc,
      by rintro rfl; exact ⟨hmem_t₁, (hinter₁ _ hmem_t₁).2.mpr rfl⟩⟩
  · rw [hV₂]
    ext v
    change (v ∈ m.P₂ ∧ v ∈ GM13.divBoundary p.toSociety (r.toSubgraph (delGraph G X'))) ↔ v = s₂
    rw [← mem_memberBoundaryList_iff p hr v]
    exact ⟨fun ⟨hv, hb⟩ => (hinter₂ v hv).1.mp hb,
      by rintro rfl; exact ⟨hmem_s₂, (hinter₂ _ hmem_s₂).1.mpr rfl⟩⟩
  · rw [hV₂]
    ext v
    change (v ∈ m.P₂ ∧ v ∈ p.toSociety.Ω.bar) ↔ v = t₂
    rw [← mem_corners_iff_mem_bar p v]
    exact ⟨fun ⟨hv, hc⟩ => (hinter₂ v hv).2.mp hc,
      by rintro rfl; exact ⟨hmem_t₂, (hinter₂ _ hmem_t₂).2.mpr rfl⟩⟩
  · rw [hV₃]
    ext v
    change (v ∈ m.P₃ ∧ v ∈ GM13.divBoundary p.toSociety (r.toSubgraph (delGraph G X'))) ↔ v = s₃
    rw [← mem_memberBoundaryList_iff p hr v]
    exact ⟨fun ⟨hv, hb⟩ => (hinter₃ v hv).1.mp hb,
      by rintro rfl; exact ⟨hmem_s₃, (hinter₃ _ hmem_s₃).1.mpr rfl⟩⟩
  · rw [hV₃]
    ext v
    change (v ∈ m.P₃ ∧ v ∈ p.toSociety.Ω.bar) ↔ v = t₃
    rw [← mem_corners_iff_mem_bar p v]
    exact ⟨fun ⟨hv, hc⟩ => (hinter₃ v hv).2.mp hc,
      by rintro rfl; exact ⟨hmem_t₃, (hinter₃ _ hmem_t₃).2.mpr rfl⟩⟩

theorem vOf_valid_at (j : Fin p.members.length)
    (hInt : GM13.IsInteriorMember p.toGMWall p.toDivision
      ((p.members[j.1]'j.2).toSubgraph (delGraph G X'))) :
    let A := (p.members[j.1]'j.2).toSubgraph (delGraph G X')
    let m := vOut.recordAt j
    m.vOf ∈ V(p.toGMWall.graph) ∧
    ∃ P : Graph ℕ (ℕ × ℕ × ℕ), ∃ s : ℕ,
      (s ∈ GM13.divBoundary p.toSociety A ∨ (GM13.divBoundary p.toSociety A = ∅ ∧ s ∈ V(A))) ∧
      GM09.IsGraphPathWithEnds p.toSociety.G P s m.vOf ∧
      V(P) ∩ V(p.toGMWall.graph) = {m.vOf} := by
  intro A m
  let r := p.members[j.1]'j.2
  have hr : r ∈ p.members := List.getElem_mem j.2
  have hint_bool : isMemberInterior p.wallSec.W r = true :=
    (isInteriorMember_toSubgraph_iff p hr).mp hInt
  have hval := vOut.hrecords_valid j
  change isValidVisionMemberRecord G X' p q δ vOut.xSeq r m = true at hval
  unfold isValidVisionMemberRecord at hval
  rw [Bool.and_eq_true] at hval
  rcases hval with ⟨_, hbr⟩
  rw [ite_eq_left hint_bool] at hbr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbr
  rcases hbr with ⟨⟨⟨_, hvOf_mem⟩, ⟨hP_vOf, hs₀_cond⟩, hinter_H⟩, _⟩
  unfold ParsedCase3Block.toGMWall
  rw [p.wallSec.W.vertexSet_toGMWall_eq_vertexFinset p.wallSec.h2 p.wallSec.he p.wallSec.hW]
  have hvOf_nat : m.vOf ∈ p.wallSec.W.vertexFinset.toNatSet :=
    (mem_image_val_iff_mem_toNatSet p.wallSec.W.vertexFinset m.vOf).mp hvOf_mem
  refine ⟨hvOf_nat, ?_⟩
  let s₀ := m.vOfPath.headD 0
  obtain ⟨P, hpath, hVP⟩ := isGraphPathWithEnds_and_inter_of_isValidKPathBetween hP_vOf
  have hmem_vOf : m.vOf ∈ m.vOfPath := by
    have h := hpath.right_mem; rwa [hVP, Set.mem_ofPred_eq] at h
  refine ⟨P, s₀, ?_, hpath, ?_⟩
  · rcases hs₀_cond with hs₀_b | ⟨hb_emp, hs₀_r⟩
    · exact Or.inl ((mem_memberBoundaryList_iff p hr s₀).mp hs₀_b)
    · right
      refine ⟨?_, ?_⟩
      · ext v
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hv_bd
        have hv_b : v ∈ memberBoundaryList p.corners p.K_eList r :=
          (mem_memberBoundaryList_iff p hr v).mpr hv_bd
        rw [hb_emp] at hv_b
        nomatch hv_b
      · rw [p.vertexSet_member_toSubgraph hr]
        exact hs₀_r
  · rw [hVP]
    ext v
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
      ← mem_image_val_iff_mem_toNatSet]
    exact ⟨fun ⟨hv, hvH⟩ => (hinter_H v hv).mp hvH,
      by rintro rfl; exact ⟨hmem_vOf, hvOf_mem⟩⟩

/-- Convert a `ParsedVisionOutput` to a `GM13.Vision`. -/
noncomputable def toGMVision :
    GM13.Vision G.toGMDigraph X'.toNatSet p.toGMWall p.toSociety p.toDivision where
  xSeq := vOut.xSeq
  xSeq_nodup := vOut.hx_nodup
  xSeq_set := vOut.xSeq_set_eq
  tildeA A := vOut.tildeAAt (vOut.findMemberIdx A)
  tildeA_valid := by
    intro A hA
    rcases exists_fin_of_mem_toDivision hA with ⟨j, rfl⟩
    rw [vOut.findMemberIdx_toSubgraph j]
    have h := vOut.tildeAAt_valid j
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  edge_partition := by
    intro e heG hhead htail
    change G.toGMDigraph.head e ∈ X'.toNatSet ∪ V(p.toCompassGraph) at hhead
    change G.toGMDigraph.tail e ∈ X'.toNatSet ∪ V(p.toCompassGraph) at htail
    rw [← vOut.xSeq_set_eq, p.vertexSet_toCompassGraph] at hhead htail
    have he_xk : e ∈ allXKMultiDigraphEdges G vOut.xSeq p.K_vList :=
      (mem_allXKMultiDigraphEdges_iff G vOut.xSeq p.K_vList e).mpr ⟨heG, htail, hhead⟩
    have he_flat := vOut.hedges_cover e he_xk
    rcases exists_unique_fin_of_flatten_nodup vOut.hedges_nodup he_flat with
      ⟨j_rec, hj_mem, hj_uniq⟩
    let j : Fin p.members.length := ⟨j_rec.1, by
      have hlen := j_rec.2
      simp only [List.length_map, vOut.hrecords_len] at hlen
      exact hlen⟩
    have hj_mem' : e ∈ (vOut.recordAt j).tildeA_eList := by
      simpa [recordAt, j] using hj_mem
    let A_j := (p.members[j.1]'j.2).toSubgraph (delGraph G X')
    have hAj_div : A_j ∈ p.toDivision :=
      ⟨p.members[j.1]'j.2, List.getElem_mem j.2, rfl⟩
    refine ⟨A_j, ⟨hAj_div, ?_⟩, ?_⟩
    · rw [vOut.findMemberIdx_toSubgraph j, (vOut.tildeAAt_valid j).2.2.2.1]
      exact hj_mem'
    · rintro A' ⟨hA'_div, he_A'⟩
      rcases exists_fin_of_mem_toDivision hA'_div with ⟨j', rfl⟩
      rw [vOut.findMemberIdx_toSubgraph j', (vOut.tildeAAt_valid j').2.2.2.1] at he_A'
      let j'_rec : Fin (vOut.records.map VisionMemberRecord.tildeA_eList).length :=
        ⟨j'.1, by rw [List.length_map, vOut.hrecords_len]; exact j'.2⟩
      have hj'_mem : e ∈ (vOut.records.map VisionMemberRecord.tildeA_eList)[j'_rec.1]'j'_rec.2 := by
        simpa [recordAt, j'_rec] using he_A'
      have hj_val : j'.1 = j.1 :=
        congrArg (fun x : Fin (vOut.records.map VisionMemberRecord.tildeA_eList).length => x.1)
          (hj_uniq j'_rec hj'_mem)
      have hj_eq : j' = j := Fin.ext hj_val
      rw [hj_eq]
  sSeq A := (vOut.recordAt (vOut.findMemberIdx A)).sSeq
  sSeq_valid := by
    intro A hInt
    rcases exists_fin_of_mem_toDivision hInt.1 with ⟨j, rfl⟩
    rw [vOut.findMemberIdx_toSubgraph j]
    exact vOut.sSeq_valid_at j hInt
  vOf A := (vOut.recordAt (vOut.findMemberIdx A)).vOf
  vOf_valid := by
    intro A hInt
    rcases exists_fin_of_mem_toDivision hInt.1 with ⟨j, rfl⟩
    rw [vOut.findMemberIdx_toSubgraph j]
    exact vOut.vOf_valid_at j hInt

@[simp]
theorem toGMVision_vOf_at (j : Fin p.members.length) :
    vOut.toGMVision.vOf ((p.members[j.1]'j.2).toSubgraph (delGraph G X')) =
      (vOut.recordAt j).vOf := by
  change (vOut.recordAt (vOut.findMemberIdx _)).vOf = (vOut.recordAt j).vOf
  rw [vOut.findMemberIdx_toSubgraph j]

@[simp]
theorem toGMVision_pi_at (j : Fin p.members.length) :
    vOut.toGMVision.pi ((p.members[j.1]'j.2).toSubgraph (delGraph G X')) =
      (vOut.recordAt j).sSeq ++ vOut.xSeq := by
  change (vOut.recordAt (vOut.findMemberIdx _)).sSeq ++ vOut.xSeq = _
  rw [vOut.findMemberIdx_toSubgraph j]

@[simp]
theorem toGMVision_tildeA_at (j : Fin p.members.length) :
    vOut.toGMVision.tildeA ((p.members[j.1]'j.2).toSubgraph (delGraph G X')) =
      vOut.tildeAAt j := by
  change vOut.tildeAAt (vOut.findMemberIdx _) = vOut.tildeAAt j
  rw [vOut.findMemberIdx_toSubgraph j]

/-- Unpack the parsed `ParsedFolioAndModels` for an interior member index `j`. -/
theorem exists_parsedFolioAndModels_at (j : Fin p.members.length)
    (hInt : isMemberInterior p.wallSec.W (p.members[j.1]'j.2) = true) :
    let m := vOut.recordAt j
    ∃ folioOut : ParsedFolioAndModels
        (tildeAMultiDigraph m.tildeA_vList m.tildeA_eList)
        (prefixRootFinset m.tildeA_vList.length (m.sSeq ++ vOut.xSeq).length) δ,
      parseFolioAndModelsFull
        (tildeAMultiDigraph m.tildeA_vList m.tildeA_eList)
        (prefixRootFinset m.tildeA_vList.length (m.sSeq ++ vOut.xSeq).length)
        δ m.folioWords = some folioOut ∧
      m.folioCode = folioRepCode q folioOut.folio := by
  intro m
  have hval := vOut.hrecords_valid j
  change isValidVisionMemberRecord G X' p q δ vOut.xSeq (p.members[j.1]'j.2) m = true at hval
  unfold isValidVisionMemberRecord at hval
  rw [Bool.and_eq_true] at hval
  rcases hval with ⟨_, hbr⟩
  rw [ite_eq_left hInt] at hbr
  simp only [Bool.and_eq_true] at hbr
  have hfolio := hbr.2
  unfold isValidMemberFolioWords at hfolio
  cases hparse : parseFolioAndModelsFull
      (tildeAMultiDigraph m.tildeA_vList m.tildeA_eList)
      (prefixRootFinset m.tildeA_vList.length (m.sSeq ++ vOut.xSeq).length)
      δ m.folioWords with
  | none =>
    rw [hparse] at hfolio
    nomatch hfolio
  | some folioOut =>
    rw [hparse, decide_eq_true_eq] at hfolio
    exact ⟨folioOut, rfl, hfolio⟩

private theorem hasSameMemberDeltaFolio_iff_of_eq {α β : Type*}
    {G : GM13.Digraph α β} {X : Set α} {H : GM13.Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (vis : GM13.Vision G X H S_H 𝒜) (δ : ℕ) {A A' : Graph α β}
    {D₁ D₂ : GM13.Digraph α β} {r₁ r₂ : List α}
    (hD₁ : vis.tildeA A = D₁) (hr₁ : vis.pi A = r₁)
    (hD₂ : vis.tildeA A' = D₂) (hr₂ : vis.pi A' = r₂)
    (hroots₁ : ∀ x ∈ r₁, x ∈ D₁.vertexSet)
    (hroots₂ : ∀ x ∈ r₂, x ∈ D₂.vertexSet) :
    vis.HasSameMemberDeltaFolio δ A A' ↔
      ∃ (hlen : r₁.length = r₂.length),
        GM13.HasSameDeltaFolio
          (GM13.rootedDigraphOfList D₁ r₁ hroots₁)
          (hlen ▸ GM13.rootedDigraphOfList D₂ r₂ hroots₂) δ := by
  subst hD₁ hr₁ hD₂ hr₂
  unfold GM13.Vision.HasSameMemberDeltaFolio
  exact ⟨fun ⟨_, _, hlen, hsame⟩ => ⟨hlen, hsame⟩,
    fun ⟨hlen, hsame⟩ => ⟨hroots₁, hroots₂, hlen, hsame⟩⟩

/-- For any two interior members `j₁, j₂ : Fin p.members.length`, assuming the `FolioSetRep`s in
their `folioWords` satisfy `IsDeltaFolioRep` (as guaranteed by Algorithm (4.1) in Step 3 of
Algorithm (10.1)) and `vOut.xSeq.length ≤ q`, their integer codes `folioCode` are equal if and only
if they have the same member `δ`-folio under `vOut.toGMVision`
(`vOut.toGMVision.HasSameMemberDeltaFolio`). -/
theorem folioCode_eq_iff_hasSameMemberDeltaFolio
    (hx_len : vOut.xSeq.length ≤ q)
    {j₁ j₂ : Fin p.members.length}
    (hInt₁ : isMemberInterior p.wallSec.W (p.members[j₁.1]'j₁.2) = true)
    (hInt₂ : isMemberInterior p.wallSec.W (p.members[j₂.1]'j₂.2) = true)
    (hrep : ∀ (j : Fin p.members.length)
      (_ : isMemberInterior p.wallSec.W (p.members[j.1]'j.2) = true)
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
        folioOut.folio) :
    (vOut.recordAt j₁).folioCode = (vOut.recordAt j₂).folioCode ↔
      vOut.toGMVision.HasSameMemberDeltaFolio δ
        ((p.members[j₁.1]'j₁.2).toSubgraph (delGraph G X'))
        ((p.members[j₂.1]'j₂.2).toSubgraph (delGraph G X')) := by
  obtain ⟨out₁, hparse₁, hcode₁⟩ := vOut.exists_parsedFolioAndModels_at j₁ hInt₁
  obtain ⟨out₂, hparse₂, hcode₂⟩ := vOut.exists_parsedFolioAndModels_at j₂ hInt₂
  have hrep₁ := hrep j₁ hInt₁ out₁ hparse₁
  have hrep₂ := hrep j₂ hInt₂ out₂ hparse₂
  have hprop : ∀ (j : Fin p.members.length)
      (hInt : isMemberInterior p.wallSec.W (p.members[j.1]'j.2) = true),
      let r := p.members[j.1]'j.2
      let m := vOut.recordAt j
      let rList := m.sSeq ++ vOut.xSeq
      m.tildeA_vList.Nodup ∧
      {v : ℕ | v ∈ m.tildeA_vList} = (vOut.tildeAAt j).vertexSet ∧
      m.tildeA_eList.Nodup ∧
      {e : ℕ × ℕ × ℕ | e ∈ m.tildeA_eList} = (vOut.tildeAAt j).edgeSet ∧
      (∀ e ∈ m.tildeA_eList,
        (vOut.tildeAAt j).tail e = e.1 ∧ (vOut.tildeAAt j).head e = e.2.1 ∧
        e.1 ∈ m.tildeA_vList ∧ e.2.1 ∈ m.tildeA_vList) ∧
      rList.length ≤ m.tildeA_vList.length ∧
      m.tildeA_vList.take rList.length = rList ∧
      (∀ x ∈ rList, x ∈ (vOut.tildeAAt j).vertexSet) ∧
      rList.length ≤ q + 3 := by
    intro j hInt r m rList
    have hr : r ∈ p.members := List.getElem_mem j.2
    have hr_val := p.member_valid_iff hr
    have hs_sub := vOut.recordAt_sSeq_subset_vList j
    have hval := vOut.hrecords_valid j
    change isValidVisionMemberRecord G X' p q δ vOut.xSeq r m = true at hval
    unfold isValidVisionMemberRecord at hval
    rw [Bool.and_eq_true] at hval
    rcases hval with ⟨hbase, hbr⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbase
    rcases hbase with ⟨⟨⟨⟨⟨_, hv_eq⟩, he_nd⟩, _⟩, he_valid⟩, _⟩
    rw [ite_eq_left hInt] at hbr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbr
    have hs_nd : m.sSeq.Nodup := hbr.1.1.1.1.1.1
    have hs_len : m.sSeq.length ≤ 3 := hbr.1.1.1.1.2
    have hdisj_rx : ∀ v ∈ r.vList, v ∉ vOut.xSeq := by
      intro v hvr hvx
      have hv_del := p.K_vList_mem_delGraph (hr_val.2.2.1 v hvr)
      rw [vertexSet_delGraph] at hv_del
      exact hv_del.2 (vOut.xSeq_set_eq ▸ hvx)
    have hv_nd : m.tildeA_vList.Nodup := by
      rw [hv_eq]
      exact nodup_memberTildeAVList vOut.xSeq r m.sSeq vOut.hx_nodup hr_val.2.1 hs_nd hs_sub hdisj_rx
    have htilde := vOut.tildeAAt_valid j
    have hk : rList.length ≤ m.tildeA_vList.length := by
      rw [hv_eq]
      exact le_length_memberTildeAVList vOut.xSeq r m.sSeq
    have htake : m.tildeA_vList.take rList.length = rList := by
      rw [hv_eq]
      exact take_memberTildeAVList vOut.xSeq r m.sSeq
    have hroots : ∀ x ∈ rList, x ∈ (vOut.tildeAAt j).vertexSet := by
      intro x hx
      rw [htilde.2.2.2.2, Set.mem_ofPred_eq, hv_eq]
      exact List.mem_append_left _ hx
    have hr_le : rList.length ≤ q + 3 := by
      change (m.sSeq ++ vOut.xSeq).length ≤ q + 3
      rw [List.length_append]
      omega
    refine ⟨hv_nd, htilde.2.2.2.2.symm, he_nd, htilde.2.2.2.1.symm,
      fun e he => ⟨rfl, rfl, (he_valid e he).2.1, (he_valid e he).2.2⟩,
      hk, htake, hroots, hr_le⟩
  rcases hprop j₁ hInt₁ with ⟨hv_nd₁, hv_set₁, he_nd₁, he_set₁, he_ends₁, hk₁, htake₁, hroots₁, hr₁_le⟩
  rcases hprop j₂ hInt₂ with ⟨hv_nd₂, hv_set₂, he_nd₂, he_set₂, he_ends₂, hk₂, htake₂, hroots₂, hr₂_le⟩
  rw [hcode₁, hcode₂,
    folioRepCode_eq_iff_hasSameDeltaFolio
      (vOut.tildeAAt j₁) (vOut.recordAt j₁).tildeA_vList (vOut.recordAt j₁).tildeA_eList
      ((vOut.recordAt j₁).sSeq ++ vOut.xSeq)
      hv_nd₁ hv_set₁ he_nd₁ he_set₁ he_ends₁ hk₁ htake₁ hroots₁ hr₁_le out₁.folio hrep₁
      (vOut.tildeAAt j₂) (vOut.recordAt j₂).tildeA_vList (vOut.recordAt j₂).tildeA_eList
      ((vOut.recordAt j₂).sSeq ++ vOut.xSeq)
      hv_nd₂ hv_set₂ he_nd₂ he_set₂ he_ends₂ hk₂ htake₂ hroots₂ hr₂_le out₂.folio hrep₂,
    hasSameMemberDeltaFolio_iff_of_eq vOut.toGMVision δ
      (vOut.toGMVision_tildeA_at j₁) (vOut.toGMVision_pi_at j₁)
      (vOut.toGMVision_tildeA_at j₂) (vOut.toGMVision_pi_at j₂)
      hroots₁ hroots₂]

end ParsedVisionOutput

end GraphMinor.Compute
