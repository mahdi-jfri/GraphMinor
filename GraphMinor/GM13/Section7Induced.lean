module

public import GraphMinor.GM13.Section7Elements
public import GraphMinor.GM13.Section7Figure1

/-!
# Graph Minors XIII, (7.3): the drawing of the new wall

Let `Γ` be a drawing of a graph in the plane. For a wall `W` whose graph is part of that graph,
the points of an element `m` of `W` (`elemPts Γ W m`) are the points of its vertices and of its
edges, and the drawing of `W` induced by `Γ` (`indU Γ W`) is the set of points of all vertices
and edges of `W`. We say that `W` is drawn on the cells of a cell wall `C` (`DrawnOnCells`) if the
points of each element `m` are the points of the cells `C.cells m`.

* A wall drawn as in Fig. 1 is drawn on the cells of `CellWall.fig1` (`drawnOnCells_fig1`). Each
  branch vertex is at its point, and the path of an edge `pq` lies on the open segment from `p`
  to `q`, since the closures of its edges cover the closed segment.
* If `W` is drawn on the cells of `C`, then the new wall of a realization of a shape `τ` is drawn
  on the cells of `C.transform τ` (`DrawnOnCells.wall`). This holds element by element, since the
  elements of the new wall are the unions of the old elements that `τ` sends to them.
* If `W` is drawn on the cells of `C`, then its induced drawing is the point set of `C.𝒰`
  (`DrawnOnCells.indU_eq`).

These three facts let us read the distance function of the induced drawing of the new wall off
the cell wall, where (7.3) was proved as a count on cells.
-/

@[expose] public section

namespace GraphMinor.GM13
open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09
open GraphMinor.GM16 (latticePoint)

open scoped Classical

universe u v
variable {α : Type u} {β : Type v} {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane)

/-- The point of a vertex in the drawing `Γ`. -/
noncomputable def ptV (x : α) : EuclideanPlane :=
  if hx : x ∈ V(G) then (Γ.iso.vertexEquiv ⟨x, hx⟩).1 else 0

/-- The points of an edge in the drawing `Γ` (an open arc). -/
noncomputable def arcE (f : β) : Set EuclideanPlane :=
  if hf : f ∈ E(G) then (Γ.iso.edgeEquiv ⟨f, hf⟩).1 else ∅

/-- The points of the element `m` of a wall `W` in the drawing `Γ`. -/
noncomputable def elemPts (W : Wall α β) (m : ℤ × ℤ) : Set EuclideanPlane :=
  ptV Γ '' W.elemV m ∪ ⋃ f ∈ W.elemE m, arcE Γ f

/-- The drawing of a wall `W` induced by `Γ`: the points of its vertices and its edges. -/
noncomputable def indU (W : Wall α β) : Set EuclideanPlane :=
  ptV Γ '' V(W.graph) ∪ ⋃ f ∈ E(W.graph), arcE Γ f

/-- The wall `W` is drawn by `Γ` on the cells of the cell wall `C`: the points of each element
are the points of its cells. -/
def DrawnOnCells (W : Wall α β) (C : CellWall W.height) : Prop :=
  ∀ m ∈ fig1WallCells W.height, elemPts Γ W m = fig1PlaneEquiv '' cellSet (C.cells m)

theorem indU_eq_iUnion (W : Wall α β) :
    indU Γ W = ⋃ m ∈ fig1WallCells W.height, elemPts Γ W m := by
  ext z
  simp only [indU, elemPts, mem_union, mem_image, mem_iUnion, exists_prop]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨f, hf, hz⟩)
    · obtain ⟨m, hm, hxm⟩ := W.exists_mem_elemV hx
      exact ⟨m, hm, Or.inl ⟨x, hxm, rfl⟩⟩
    · obtain ⟨m, hm, hfm⟩ := W.exists_mem_elemE hf
      exact ⟨m, hm, Or.inr ⟨f, hfm, hz⟩⟩
  · rintro ⟨m, -, ⟨x, hx, rfl⟩ | ⟨f, hf, hz⟩⟩
    · exact Or.inl ⟨x, W.elemV_subset m hx, rfl⟩
    · exact Or.inr ⟨f, W.elemE_subset m hf, hz⟩

variable {Γ} in
theorem DrawnOnCells.indU_eq {W : Wall α β} {C : CellWall W.height} (hD : DrawnOnCells Γ W C) :
    indU Γ W = fig1PlaneEquiv '' cellSet C.𝒰 := by
  rw [indU_eq_iUnion]
  ext z
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨m, hm, hz⟩
    rw [hD m hm] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, (C.mem_U_iff).mpr ⟨m, hm, hw⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨m, hm, hwm⟩ := (C.mem_U_iff).mp hw
    exact ⟨m, hm, by rw [hD m hm]; exact ⟨w, hwm, rfl⟩⟩

variable {Γ} in
/-- **The new wall of a realization is drawn on the cells of the new cell wall.** -/
theorem DrawnOnCells.wall {W : Wall α β} {C : CellWall W.height} (hD : DrawnOnCells Γ W C)
    {h' : ℕ} {τ : Shape W.height h'} (R : τ.Realization) (hh' : 1 ≤ h') (he' : Even h') :
    DrawnOnCells Γ (R.wall W hh' he') (C.transform τ hh' he') := by
  intro m' hm'
  ext z
  change z ∈ elemPts Γ (R.wall W hh' he') m' ↔ z ∈ fig1PlaneEquiv '' cellSet (C.tCells τ m')
  simp only [elemPts, mem_union, mem_image, mem_iUnion, exists_prop, cellSet, mem_ofPred_eq,
    C.mem_tCells]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨f, hf, hz⟩)
    · obtain ⟨m, hm, hown, hxm⟩ := (R.elemV_wall W hh' he' m').mp hx
      have h1 : ptV Γ x ∈ elemPts Γ W m := Or.inl ⟨x, hxm, rfl⟩
      rw [hD m hm] at h1
      obtain ⟨w, hw, e⟩ := h1
      exact ⟨w, ⟨m, hm, hown, hw⟩, e⟩
    · obtain ⟨m, hm, hown, hfm⟩ := (R.elemE_wall W hh' he' m').mp hf
      have h1 : z ∈ elemPts Γ W m := Or.inr (mem_iUnion₂.mpr ⟨f, hfm, hz⟩)
      rw [hD m hm] at h1
      obtain ⟨w, hw, e⟩ := h1
      exact ⟨w, ⟨m, hm, hown, hw⟩, e⟩
  · rintro ⟨w, ⟨m, hm, hown, hw⟩, rfl⟩
    have h1 : fig1PlaneEquiv w ∈ elemPts Γ W m := by rw [hD m hm]; exact ⟨w, hw, rfl⟩
    rcases h1 with ⟨x, hx, e⟩ | h1
    · exact Or.inl ⟨x, (R.elemV_wall W hh' he' m').mpr ⟨m, hm, hown, hx⟩, e⟩
    · obtain ⟨f, hf, hz⟩ := mem_iUnion₂.mp h1
      exact Or.inr ⟨f, (R.elemE_wall W hh' he' m').mpr ⟨m, hm, hown, hf⟩, hz⟩

/-! ## Points of a drawing -/

section Drawing

variable {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane)

theorem ptV_of_mem {x : α} (hx : x ∈ V(G)) : ptV Γ x = (Γ.iso.vertexEquiv ⟨x, hx⟩).1 := dite_eq_left hx

theorem arcE_of_mem {f : β} (hf : f ∈ E(G)) : arcE Γ f = (Γ.iso.edgeEquiv ⟨f, hf⟩).1 :=
  dite_eq_left hf

theorem ptV_mem_V {x : α} (hx : x ∈ V(G)) : ptV Γ x ∈ Γ.drawing.V := by
  rw [ptV_of_mem Γ hx]; exact (Γ.iso.vertexEquiv ⟨x, hx⟩).2

theorem arcE_mem_E {f : β} (hf : f ∈ E(G)) : arcE Γ f ∈ Γ.drawing.E := by
  rw [arcE_of_mem Γ hf]; exact (Γ.iso.edgeEquiv ⟨f, hf⟩).2

/-- An edge of a drawing contains no vertex point, since it is a part of `U \ V`. -/
theorem ptV_not_mem_arcE {x : α} (hx : x ∈ V(G)) (f : β) : ptV Γ x ∉ arcE Γ f := by
  intro h
  by_cases hf : f ∈ E(G)
  · rw [← Γ.drawing.closure_diff_V (arcE_mem_E Γ hf)] at h
    exact h.2 (ptV_mem_V Γ hx)
  · simp [arcE, hf] at h

/-- Distinct vertices are drawn at distinct points, since `Γ.iso.vertexEquiv` is a bijection. -/
theorem ptV_injOn : InjOn (ptV Γ) V(G) := by
  intro x hx y hy e
  rw [ptV_of_mem Γ hx, ptV_of_mem Γ hy] at e
  exact congrArg Subtype.val (Γ.iso.vertexEquiv.injective (Subtype.ext e))

/-- The closure of the edge `f` with ends `x, y` is the edge and the points of `x` and `y`: its
part outside `V` is the edge itself, and its part in `V` is the pair of its ends. -/
theorem closure_arcE {f : β} {x y : α} (hl : G.IsLink f x y) :
    closure (arcE Γ f) = arcE Γ f ∪ {ptV Γ x, ptV Γ y} := by
  have hl' := (Γ.iso.isLink_iff ⟨f, hl.edge_mem⟩ ⟨x, hl.left_mem⟩ ⟨y, hl.right_mem⟩).mp hl
  obtain ⟨he, -, -, hcap⟩ := hl'
  rw [arcE_of_mem Γ hl.edge_mem, ptV_of_mem Γ hl.left_mem, ptV_of_mem Γ hl.right_mem, ← hcap]
  calc closure _ = (closure _ \ Γ.drawing.V) ∪ (closure _ ∩ Γ.drawing.V) :=
        (sdiff_union_inter _ _).symm
    _ = _ := by rw [Γ.drawing.closure_diff_V he]

end Drawing

/-- Every vertex of a walk with an edge is an end of an edge of the walk. -/
theorem _root_.GraphMinor.Surface.GraphWalk.exists_isLink_of_mem_support {P : Graph α β} : ∀ {u v : α} (w : GraphWalk P u v),
    w.edges ≠ [] → ∀ {x : α}, x ∈ w.support → ∃ f ∈ w.edges, ∃ y, P.IsLink f x y
  | _, _, .nil _, hE, _, _ => absurd rfl hE
  | u, _, .cons (e := e) (v := v) hl rest, _, x, hx => by
    simp only [GraphWalk.support, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨e, by simp [GraphWalk.edges], v, hl⟩
    · cases rest with
      | nil _ =>
        simp only [GraphWalk.support, List.mem_singleton] at hx
        subst hx
        exact ⟨e, by simp [GraphWalk.edges], u, hl.symm⟩
      | cons hl' rest' =>
        obtain ⟨f, hf, y, hy⟩ :=
          exists_isLink_of_mem_support (.cons hl' rest') (by simp [GraphWalk.edges]) hx
        exact ⟨f, by simp only [GraphWalk.edges, List.mem_cons] at hf ⊢; tauto, y, hy⟩

/-- The closures of the edges of a path with an edge are the points of its vertices and its
edges: each closure adds the two ends (`closure_arcE`), and each vertex of the path is an end of
one of its edges (`GraphWalk.exists_isLink_of_mem_support`). -/
theorem iUnion_closure_arcE {G P : Graph α β} (Γ : GraphDrawing G EuclideanPlane) {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hE : E(P).Nonempty) :
    ⋃ f ∈ E(P), closure (arcE Γ f) = ptV Γ '' V(P) ∪ ⋃ f ∈ E(P), arcE Γ f := by
  obtain ⟨hle, w, -, hV, hEw⟩ := hP
  ext z
  simp only [mem_iUnion, mem_union, mem_image, exists_prop]
  constructor
  · rintro ⟨f, hf, hz⟩
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet hf
    rw [closure_arcE Γ (hle.isLink_mono hl)] at hz
    rcases hz with hz | rfl | rfl
    · exact Or.inr ⟨f, hf, hz⟩
    · exact Or.inl ⟨x, hl.left_mem, rfl⟩
    · exact Or.inl ⟨y, hl.right_mem, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨f, hf, hz⟩)
    · have hwE : w.edges ≠ [] := by
        obtain ⟨f, hf⟩ := hE
        rw [hEw] at hf
        exact List.ne_nil_of_mem hf
      rw [hV] at hx
      obtain ⟨f, hf, y, hl⟩ := w.exists_isLink_of_mem_support hwE hx
      refine ⟨f, by rw [hEw]; exact hf, ?_⟩
      rw [closure_arcE Γ (hle.isLink_mono hl)]
      exact Or.inr (Or.inl rfl)
    · exact ⟨f, hf, subset_closure hz⟩

/-! ## The base case: a wall drawn as in Fig. 1 -/

theorem cellCode_eq_vCell_iff {z : ℝ × ℝ} {p : ℕ × ℕ} : cellCode z = vCell p ↔ z = latticePoint p := by
  obtain ⟨z1, z2⟩ := z
  simp only [cellCode, vCell, latticePoint, Prod.mk.injEq, cellCode1_eq_even_iff]
  push_cast
  rfl

theorem cellSet_vCell (p : ℕ × ℕ) : cellSet {vCell p} = {latticePoint p} := by
  ext z
  simp only [cellSet, mem_ofPred_eq, mem_singleton_iff, cellCode_eq_vCell_iff]

/-- The three cells of the segment of an edge `pq`: its two ends and the open segment. -/
theorem fig1SegmentCells_eq {h : ℕ} {p q : ℕ × ℕ} (hpq : elementaryWallAdj h p q) :
    fig1SegmentCells p q = {vCell p, eCell p q, vCell q} := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  have h' : (p2 = q2 ∧ (p1 + 1 = q1 ∨ q1 + 1 = p1)) ∨ (p1 = q1 ∧ (p2 + 1 = q2 ∨ q2 + 1 = p2)) := by
    rcases hpq.2.2 with h | ⟨h1, ⟨h2, -⟩ | ⟨h2, -⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · exact Or.inr ⟨h1, Or.inr h2⟩
  unfold fig1SegmentCells horizontalCells verticalCells
  ext ⟨c1, c2⟩
  simp only [vCell, eCell] at *
  split_ifs <;> simp only [mem_insert_iff, mem_singleton_iff, Prod.mk.injEq] <;> omega

/-- The open segment of an edge `pq` is its closed segment without the two ends. -/
theorem cellSet_segment_diff {h : ℕ} {p q : ℕ × ℕ} (hpq : elementaryWallAdj h p q) :
    cellSet {vCell p, eCell p q, vCell q} \ {latticePoint p, latticePoint q} =
      cellSet {eCell p q} := by
  ext z
  simp only [cellSet, mem_sdiff, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff,
    ← cellCode_eq_vCell_iff]
  have h1 := eCell_ne_vCell hpq p
  have h2 := eCell_ne_vCell hpq q
  constructor
  · tauto
  · rintro e
    rw [e]
    tauto

variable {W : Wall α β} {Γ : GraphDrawing W.graph EuclideanPlane}

theorem ptV_branchVertex (hΓ : IsFigure1CoordDrawing W Γ) {p : ℕ × ℕ}
    (hp : p ∈ elementaryWallVerts W.height) :
    ptV Γ (W.branchVertex p hp) = fig1PlaneEquiv (latticePoint p) := by
  rw [ptV_of_mem Γ (W.branchVertex_mem_graph p hp)]
  exact hΓ.branchVertex_point p hp _

/-- The element of a branch vertex is drawn at its point. -/
theorem elemPts_vCell (hΓ : IsFigure1CoordDrawing W Γ) {p : ℕ × ℕ}
    (hp : p ∈ elementaryWallVerts W.height) :
    elemPts Γ W (vCell p) = fig1PlaneEquiv '' cellSet {vCell p} := by
  have hV : W.elemV (vCell p) = {W.branchVertex p hp} := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨-, rfl⟩ := W.mem_elemV_vCell hx
      rfl
    · rw [mem_singleton_iff.mp hx]
      exact W.branchVertex_mem_elemV hp
  rw [elemPts, hV, W.elemE_vCell, cellSet_vCell, image_singleton, image_singleton,
    ptV_branchVertex hΓ hp]
  simp

/-- The element of an edge `pq` is drawn on the open segment from `p` to `q`: the closures of
the edges of its path cover the closed segment (`path_on_segment`), and taking away the two ends
leaves its inner vertices and its edges. -/
theorem elemPts_eCell (hΓ : IsFigure1CoordDrawing W Γ) {p q : ℕ × ℕ}
    (hpq : elementaryWallAdj W.height p q) :
    elemPts Γ W (eCell p q) = fig1PlaneEquiv '' cellSet {eCell p q} := by
  set P := W.subdivisionPaths (W.baseEdge hpq) with hPdef
  have hP := W.isGraphPathWithEnds_baseEdge hpq
  have hseg : ⋃ f ∈ E(P), closure (arcE Γ f) =
      fig1PlaneEquiv '' cellSet {vCell p, eCell p q, vCell q} := by
    rw [← fig1SegmentCells_eq hpq, ← fig1Segment_eq_cellSet, ← hΓ.path_on_segment p q hpq]
    ext z
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨f, hf, hz⟩
      exact ⟨⟨f, hP.1.edgeSet_mono hf⟩, hf, by rwa [arcE_of_mem Γ (hP.1.edgeSet_mono hf)] at hz⟩
    · rintro ⟨f, hf, hz⟩
      exact ⟨f.1, hf, by rwa [arcE_of_mem Γ f.2]⟩
  rw [iUnion_closure_arcE Γ hP (W.subdivisionPaths_nonempty hpq)] at hseg
  rw [← cellSet_segment_diff hpq, image_sdiff fig1PlaneEquiv.injective, ← hseg, image_insert_eq,
    image_singleton, ← ptV_branchVertex hΓ hpq.1, ← ptV_branchVertex hΓ hpq.2.1]
  have hinter := W.vertexSet_baseEdge_inter hpq
  have hPV : V(P) ⊆ V(W.graph) := hP.1.vertexSet_mono
  have ha := W.branchVertex_mem_graph p hpq.1
  have hb := W.branchVertex_mem_graph q hpq.2.1
  ext z
  simp only [elemPts, mem_union, mem_image, mem_iUnion, exists_prop, mem_sdiff, mem_insert_iff,
    mem_singleton_iff, W.mem_elemV_eCell hpq, W.mem_elemE_eCell hpq]
  constructor
  · rintro (⟨x, ⟨hxP, hxB⟩, rfl⟩ | ⟨f, hf, hz⟩)
    · have hxa : x ≠ W.branchVertex p hpq.1 := fun e => hxB (e ▸ W.branchVertex_mem_baseGraph _ _)
      have hxb : x ≠ W.branchVertex q hpq.2.1 :=
        fun e => hxB (e ▸ W.branchVertex_mem_baseGraph _ _)
      refine ⟨Or.inl ⟨x, hxP, rfl⟩, ?_⟩
      rintro (e | e)
      · exact hxa (ptV_injOn Γ (hPV hxP) ha e)
      · exact hxb (ptV_injOn Γ (hPV hxP) hb e)
    · refine ⟨Or.inr ⟨f, hf, hz⟩, ?_⟩
      rintro (rfl | rfl)
      · exact ptV_not_mem_arcE Γ ha f hz
      · exact ptV_not_mem_arcE Γ hb f hz
  · rintro ⟨⟨x, hxP, rfl⟩ | ⟨f, hf, hz⟩, hne⟩
    · refine Or.inl ⟨x, ⟨hxP, fun hxB => hne ?_⟩, rfl⟩
      have : x ∈ V(P) ∩ V(W.baseGraph) := ⟨hxP, hxB⟩
      rw [hinter] at this
      rcases this with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr ⟨f, hf, hz⟩

/-- **A wall drawn as in Fig. 1 is drawn on the cells of `CellWall.fig1`.** -/
theorem drawnOnCells_fig1 (hΓ : IsFigure1CoordDrawing W Γ) (hh : 1 ≤ W.height)
    (he : Even W.height) : DrawnOnCells Γ W (CellWall.fig1 hh he) := by
  intro m hm
  simp only [fig1WallCells, mem_iUnion] at hm
  obtain ⟨p, q, hpq, hm⟩ := hm
  rw [fig1SegmentCells_eq hpq] at hm
  change elemPts Γ W m = fig1PlaneEquiv '' cellSet {m}
  rcases hm with rfl | rfl | rfl
  · exact elemPts_vCell hΓ hpq.1
  · exact elemPts_eCell hΓ hpq
  · exact elemPts_vCell hΓ hpq.2.1

end GraphMinor.GM13
