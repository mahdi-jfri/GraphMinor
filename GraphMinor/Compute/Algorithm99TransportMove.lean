module

public import GraphMinor.Compute.Algorithm99TransportOrig

/-!
# Moving a wall of `G_i` to the labels of `G`

Algorithm (9.9) of Graph Minors XIII (page 104) finds walls in the renumbered graph `G_i` on
`Fin v_i`, but its output (iii) is a wall written in the labels of `G`. For an injective map
`orig : Fin v → Fin n` from the vertices of a graph `A` to those of a graph `B` that keeps
adjacency, `WallOfHeight.moveOrig` writes a wall `W` of `A` in the labels of `B`: its branch
vertices and internal vertices are mapped by `orig`.

The GM wall of the moved wall (`toGMWall`) is not the renamed GM wall of `W` (`relabelWall`):
between two adjacent vertices, `toGMWall` takes the edge `(u, w, 0)` or `(w, u, 0)` according to
the multiplicities of the graph it lives in (`adjEdgeTriple`), and these differ between `A` and
`B`. We prove that the two walls have the same corners, the same perimeter vertices and the same
inside vertices (`toGMWall_moveOrig_corner`, `vertexSet_perimeter_toGMWall_moveOrig`,
`insideVerts_toGMWall_moveOrig`). Both sides are computed from the vertex lists of the
subdivision paths (`vertexSet_perimeter_toGMWall_eq`, `insideVerts_toGMWall_eq` of `Specs9.lean`),
and the vertex lists of the moved wall are the mapped lists.

With the "same vertices" lemmas of `Algorithm99TransportOrig.lean`, this carries the compass,
flatness, the wall society and the interior members from the renamed wall to the moved wall
(`wallCompass_toGMWall_moveOrig`, `isFlatWallIn_toGMWall_moveOrig`,
`isWallSociety_toGMWall_moveOrig`, `isInteriorMember_toGMWall_moveOrig_iff`).
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph Function Set GraphMinor.GM09 GraphMinor.GM13 GraphMinor.Transport

variable {h v n : ℕ} {A : MultiDigraph v} {B : MultiDigraph n}

namespace WallOfHeight

/-- The wall `W` of `A` written in the labels of `B`: branch vertices and internal vertices of
the subdivision paths are mapped by `orig`. -/
def moveOrig (W : WallOfHeight h A) (B : MultiDigraph n) (orig : Fin v → Fin n) :
    WallOfHeight h B where
  branchVert := orig ∘ W.branchVert
  internalVerts k := (W.internalVerts k).map orig

variable (W : WallOfHeight h A) (orig : Fin v → Fin n)

@[simp]
theorem moveOrig_branchVert (u : Fin (elemWallNumVerts h)) :
    (W.moveOrig B orig).branchVert u = orig (W.branchVert u) := rfl

theorem subdivPathVerts_moveOrig (k : Fin (elemWallEdges h).length) :
    (W.moveOrig B orig).subdivPathVerts k = (W.subdivPathVerts k).map orig := by
  unfold subdivPathVerts moveOrig
  simp

/-- A walk list of `A` mapped by an adjacency-preserving map is a walk list of `B`. -/
theorem isSimpleWalkList_map
    (hadj : ∀ u w, A.toSimpleGraph.Adj u w → B.toSimpleGraph.Adj (orig u) (orig w)) :
    ∀ {L : List (Fin v)}, IsSimpleWalkList A L → IsSimpleWalkList B (L.map orig)
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: w :: rest, hL => ⟨hadj _ _ hL.1, isSimpleWalkList_map hadj (L := w :: rest) hL.2⟩

/-- The moved wall of a valid wall is valid, for an injective `orig` that keeps adjacency. -/
theorem IsValid.moveOrig {W : WallOfHeight h A} (hW : W.IsValid) (hinj : Injective orig)
    (hadj : ∀ u w, A.toSimpleGraph.Adj u w → B.toSimpleGraph.Adj (orig u) (orig w)) :
    (W.moveOrig B orig).IsValid := by
  obtain ⟨hbr, hpath, hint, hdisj⟩ := hW
  refine ⟨hinj.comp hbr, fun k => ?_, fun k u => ?_, fun k₁ k₂ hne => ?_⟩
  · rw [subdivPathVerts_moveOrig]
    exact ⟨(hpath k).1.map hinj, isSimpleWalkList_map orig hadj (hpath k).2⟩
  · change orig (W.branchVert u) ∉ (W.internalVerts k).map orig
    rw [List.mem_map]
    rintro ⟨x, hx, hxu⟩
    exact hint k u (hinj hxu ▸ hx)
  · change List.Disjoint ((W.internalVerts k₁).map orig) ((W.internalVerts k₂).map orig)
    intro x hx₁ hx₂
    obtain ⟨y₁, hy₁, rfl⟩ := List.mem_map.mp hx₁
    obtain ⟨y₂, hy₂, hy⟩ := List.mem_map.mp hx₂
    exact hdisj k₁ k₂ hne hy₁ (hinj hy ▸ hy₂)

theorem vertexFinset_moveOrig :
    (W.moveOrig B orig).vertexFinset = W.vertexFinset.image orig := by
  ext x
  simp only [mem_vertexFinset_iff, Finset.mem_image]
  constructor
  · rintro (⟨u, rfl⟩ | ⟨k, hk⟩)
    · exact ⟨W.branchVert u, Or.inl ⟨u, rfl⟩, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hk
      exact ⟨y, Or.inr ⟨k, hy⟩, rfl⟩
  · rintro ⟨y, (⟨u, rfl⟩ | ⟨k, hk⟩), rfl⟩
    · exact Or.inl ⟨u, rfl⟩
    · exact Or.inr ⟨k, List.mem_map_of_mem hk⟩

theorem perimeterFinset_moveOrig :
    (W.moveOrig B orig).perimeterFinset = W.perimeterFinset.image orig := by
  ext x
  simp only [mem_perimeterFinset_iff, subdivPathVerts_moveOrig, Finset.mem_image, List.mem_map]
  constructor
  · rintro ⟨k, hk, y, hy, rfl⟩
    exact ⟨y, ⟨k, hk, hy⟩, rfl⟩
  · rintro ⟨y, ⟨k, hk, hy⟩, rfl⟩
    exact ⟨k, hk, y, hy, rfl⟩

theorem insideFinset_moveOrig (hinj : Injective orig) :
    (W.moveOrig B orig).insideFinset = W.insideFinset.image orig := by
  unfold insideFinset
  rw [vertexFinset_moveOrig, perimeterFinset_moveOrig, Finset.image_sdiff_of_injOn hinj.injOn (perimeterFinset_subset_vertexFinset W)]

end WallOfHeight

/-- The natural-number image of a mapped finset is the image under `origVertexEmb`. -/
theorem toNatSet_image_orig {orig : Fin v → Fin n} (hinj : Injective orig) (F : Finset (Fin v)) :
    (F.image orig).toNatSet = origVertexEmb orig hinj '' F.toNatSet := by
  ext x
  simp only [Finset.toNatSet, Finset.coe_image, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y.1, ⟨y, hy, rfl⟩, origVertexEmb_apply_val orig hinj y⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨orig y, ⟨y, hy, rfl⟩, (origVertexEmb_apply_val orig hinj y).symm⟩

section Compare

variable {W : WallOfHeight h A} {orig : Fin v → Fin n} (h2 : 2 ≤ h) (he : Even h)
  (hW : W.IsValid) (hinj : Injective orig)
  (hadj : ∀ u w, A.toSimpleGraph.Adj u w → B.toSimpleGraph.Adj (orig u) (orig w))

/-- The renamed GM wall of `W`, along `orig`. -/
noncomputable abbrev relabelOrigWall : Wall ℕ (ℕ × ℕ × ℕ) :=
  relabelWall (origVertexEmb orig hinj) (origEdgeEmb orig hinj) (W.toGMWall h2 he hW)

/-- The moved wall and the renamed wall have the same corners. -/
theorem toGMWall_moveOrig_corner :
    ((W.moveOrig B orig).toGMWall h2 he (hW.moveOrig orig hinj hadj)).corner =
      (relabelOrigWall h2 he hW hinj).corner := by
  funext k
  rw [WallOfHeight.toGMWall_corner, relabelWall_corner, WallOfHeight.toGMWall_corner,
    WallOfHeight.moveOrig_branchVert, origVertexEmb_apply_val]

/-- The moved wall and the renamed wall have the same perimeter vertices. -/
theorem vertexSet_perimeter_toGMWall_moveOrig :
    V(((W.moveOrig B orig).toGMWall h2 he (hW.moveOrig orig hinj hadj)).perimeter) =
      V((relabelOrigWall h2 he hW hinj).perimeter) := by
  rw [WallOfHeight.vertexSet_perimeter_toGMWall_eq, relabelWall_perimeter, vertexSet_relabelGraph,
    WallOfHeight.vertexSet_perimeter_toGMWall_eq, WallOfHeight.perimeterFinset_moveOrig,
    toNatSet_image_orig hinj]

/-- The moved wall and the renamed wall have the same inside vertices. -/
theorem insideVerts_toGMWall_moveOrig :
    ((W.moveOrig B orig).toGMWall h2 he (hW.moveOrig orig hinj hadj)).insideVerts =
      (relabelOrigWall h2 he hW hinj).insideVerts := by
  rw [WallOfHeight.insideVerts_toGMWall_eq, relabelWall_insideVerts,
    WallOfHeight.insideVerts_toGMWall_eq, WallOfHeight.insideFinset_moveOrig _ _ hinj,
    toNatSet_image_orig hinj]

/-- The moved wall and the renamed wall have the same vertices. -/
theorem vertexSet_toGMWall_moveOrig :
    V(((W.moveOrig B orig).toGMWall h2 he (hW.moveOrig orig hinj hadj)).graph) =
      V((relabelOrigWall h2 he hW hinj).graph) := by
  rw [WallOfHeight.vertexSet_toGMWall_eq, relabelWall_graph, vertexSet_relabelGraph,
    WallOfHeight.vertexSet_toGMWall_eq, WallOfHeight.vertexFinset_moveOrig,
    toNatSet_image_orig hinj]

/-- In any graph, the moved wall and the renamed wall have the same compass. -/
theorem wallCompass_toGMWall_moveOrig (K : Graph ℕ (ℕ × ℕ × ℕ)) :
    wallCompass K ((W.moveOrig B orig).toGMWall h2 he (hW.moveOrig orig hinj hadj)) =
      wallCompass K (relabelOrigWall h2 he hW hinj) :=
  wallCompass_congr (vertexSet_perimeter_toGMWall_moveOrig h2 he hW hinj hadj)
    (insideVerts_toGMWall_moveOrig h2 he hW hinj hadj)

/-- If the renamed wall is flat in `K` and the moved wall is a subgraph of `K`, then the moved
wall is flat in `K`. -/
theorem isFlatWallIn_toGMWall_moveOrig {K : Graph ℕ (ℕ × ℕ × ℕ)}
    (hle : ((W.moveOrig B orig).toGMWall h2 he (hW.moveOrig orig hinj hadj)).graph ≤ K)
    (hflat : IsFlatWallIn K (relabelOrigWall h2 he hW hinj)) :
    IsFlatWallIn K ((W.moveOrig B orig).toGMWall h2 he (hW.moveOrig orig hinj hadj)) :=
  isFlatWallIn_congr hle (toGMWall_moveOrig_corner h2 he hW hinj hadj).symm
    (vertexSet_perimeter_toGMWall_moveOrig h2 he hW hinj hadj).symm
    (insideVerts_toGMWall_moveOrig h2 he hW hinj hadj).symm hflat

/-- A wall society of the renamed wall in `K` is a wall society of the moved wall in `K`. -/
theorem isWallSociety_toGMWall_moveOrig {K : Graph ℕ (ℕ × ℕ × ℕ)} {S : Society ℕ (ℕ × ℕ × ℕ)}
    (hS : IsWallSociety K (relabelOrigWall h2 he hW hinj) S) :
    IsWallSociety K ((W.moveOrig B orig).toGMWall h2 he (hW.moveOrig orig hinj hadj)) S :=
  isWallSociety_congr (toGMWall_moveOrig_corner h2 he hW hinj hadj).symm
    (vertexSet_perimeter_toGMWall_moveOrig h2 he hW hinj hadj).symm
    (insideVerts_toGMWall_moveOrig h2 he hW hinj hadj).symm hS

/-- The moved wall and the renamed wall have the same interior members. -/
theorem isInteriorMember_toGMWall_moveOrig_iff {𝒜 : Set (Graph ℕ (ℕ × ℕ × ℕ))}
    {M : Graph ℕ (ℕ × ℕ × ℕ)} :
    IsInteriorMember ((W.moveOrig B orig).toGMWall h2 he (hW.moveOrig orig hinj hadj)) 𝒜 M ↔
      IsInteriorMember (relabelOrigWall h2 he hW hinj) 𝒜 M :=
  isInteriorMember_congr (vertexSet_perimeter_toGMWall_moveOrig h2 he hW hinj hadj)

end Compare

end GraphMinor.Compute
