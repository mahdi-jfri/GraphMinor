module

public import GraphMinor.GM13.Section7ThreeWall

/-!
# Graph Minors XIII, (7.6) and (7.7): the walls `H_1, …, H_k` on cells

The proof of (7.6) applies (7.3) with `r = 0` once for each centre. This file does that on cells
(`DrawnOnCells.exists_iter`): after `k` steps we have a wall `W' ≤ W`, drawn on the cells of a
cell wall `C'`, with none of the given vertices, and with `d' ≥ d - 4k`.

For (7.7) we must compare two drawings of one wall `W'`: the drawing it gets from the wall `H` of
Fig. 1, and a drawing of `W'` itself as in Fig. 1. Both are drawings on cells, and both put each
element of `W'` on the cells named by that element. The distance of two points on a drawing on
cells depends only on the elements that hold them (`CellWall.planeWallDist_eq`): it is `2` for
two points of one element, and `2 + D(F, G)` otherwise, with `F, G` the closest faces at the two
elements. So the two drawings give the same distance between distinct vertices of `W'`
(`DrawnOnCells.planeWallDist_eq`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

variable {α : Type u} {β : Type v}

/-! ## `k` steps of (7.3) -/

/-- **`k` steps of (7.3) with `r = 0`, on cells.** Let `W` be drawn by `Γ` on the cells of `C`,
and let `L` be a list of `k` vertices with `2k + 2 ≤ h`, where `h` is the height of `W`. Then
there is a wall `W' ≤ W`, drawn on the cells of a cell wall `C'`, that contains no vertex of `L`,
whose distance function on cells is at least that of `C` minus `4k`. A vertex of `L` that is not
in the current wall needs no step. -/
theorem DrawnOnCells.exists_iter {G : Graph α β} {Γ : GraphDrawing G EuclideanPlane} :
    ∀ (L : List α) {W : Wall α β} {C : CellWall W.height}, DrawnOnCells Γ W C →
      2 * L.length + 2 ≤ W.height →
      ∃ (W' : Wall α β) (C' : CellWall W'.height), W'.graph ≤ W.graph ∧
        DrawnOnCells Γ W' C' ∧ (∀ x ∈ L, x ∉ V(W'.graph)) ∧
        DistGeSub (planeWallDist (fig1PlaneEquiv '' cellSet C'.𝒰))
          (planeWallDist (fig1PlaneEquiv '' cellSet C.𝒰)) (4 * L.length)
  | [], W, C, hD, _ => ⟨W, C, le_rfl, hD, by simp, fun s t => by simp⟩
  | x :: L, W, C, hD, hh => by
    simp only [List.length_cons] at hh
    -- first remove `x` (if it is in `W`), then the rest of the list
    obtain ⟨W₁, C₁, hle₁, hD₁, hx₁, hh₁, hd₁⟩ : ∃ (W₁ : Wall α β) (C₁ : CellWall W₁.height),
        W₁.graph ≤ W.graph ∧ DrawnOnCells Γ W₁ C₁ ∧ x ∉ V(W₁.graph) ∧
        2 * L.length + 2 ≤ W₁.height ∧
        DistGeSub (planeWallDist (fig1PlaneEquiv '' cellSet C₁.𝒰))
          (planeWallDist (fig1PlaneEquiv '' cellSet C.𝒰)) 4 := by
      by_cases hx : x ∈ V(W.graph)
      · have he' : Even (W.height - 2) := by
          obtain ⟨k, hk⟩ := W.even_height
          exact ⟨k - 1, by omega⟩
        obtain ⟨W₁, C₁, hle, hht, hD₁, -, hx₁, hd⟩ :=
          hD.exists_step (h' := W.height - 2) (by omega) (by omega) he' hx
        exact ⟨W₁, C₁, hle, hD₁, hx₁, by omega, hd⟩
      · exact ⟨W, C, le_rfl, hD, hx, by omega, fun s t => by omega⟩
    obtain ⟨W', C', hle', hD', hL', hd'⟩ := exists_iter L hD₁ hh₁
    refine ⟨W', C', hle'.trans hle₁, hD', ?_, fun s t => ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact fun h => hx₁ (hle'.vertexSet_mono h)
      · exact hL' y hy
    · have := hd₁ s t
      have := hd' s t
      simp only [List.length_cons]
      omega

/-! ## The distance of a drawing on cells depends only on the elements -/

namespace CellWall

variable {h : ℕ}

/-- Two distinct points of a drawing on cells, none of them a square, are at distance at least
`2`: a line between them that attains the distance contains both. -/
theorem two_le_planeWallDist {𝒰 : Set (ℤ × ℤ)} (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c)
    {s t : EuclideanPlane} (hst : s ≠ t) (hs : s ∈ fig1PlaneEquiv '' cellSet 𝒰)
    (ht : t ∈ fig1PlaneEquiv '' cellSet 𝒰) :
    2 ≤ planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) s t := by
  obtain ⟨L, hL, hfin, hcard⟩ := exists_line_ncard_eq_planeWallDist_cellSet h𝒰 hst
  rw [← hcard]
  have hsub : ({s, t} : Set EuclideanPlane) ⊆ L ∩ fig1PlaneEquiv '' cellSet 𝒰 := by
    obtain ⟨f, h0, h1⟩ := hL
    rintro z (rfl | rfl)
    · exact ⟨h0 ▸ (f 0).2, hs⟩
    · exact ⟨h1 ▸ (f 1).2, ht⟩
  calc 2 = ({s, t} : Set EuclideanPlane).ncard := (ncard_pair hst).symm
    _ ≤ _ := ncard_le_ncard hsub hfin

variable (C : CellWall h)

theorem mem_U_of_mem_cells {m c : ℤ × ℤ} (hm : m ∈ fig1WallCells h) (hc : c ∈ C.cells m) :
    c ∈ C.𝒰 :=
  (C.mem_U_iff).mpr ⟨m, hm, hc⟩

/-- Two distinct points in the cells of one element are at distance at most `2`: in one cell by
`FaceNaming.planeWallDist_le_two_of_cellCode_eq`, and in two cells because some face is named at
both cells (each cell sees the faces of the element). -/
theorem planeWallDist_le_two {m : ℤ × ℤ} (hm : m ∈ fig1WallCells h) {s t : ℝ × ℝ}
    (hs : cellCode s ∈ C.cells m) (ht : cellCode t ∈ C.cells m) :
    planeWallDist (fig1PlaneEquiv '' cellSet C.𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) ≤ 2 := by
  by_cases hst : cellCode s = cellCode t
  · exact C.naming.planeWallDist_le_two_of_cellCode_eq hst
  have hq := cellUp_mem_squaresAbove (cellCode s)
  obtain ⟨q', hq', e⟩ := C.exists_name_eq hm ht (C.name_mem_cellFaces hm hs hq)
  have h1 := C.naming.planeWallDist_le hst hq hq'
  rw [e, faceDist_self (C.naming.face _), cellInd_of_mem (C.mem_U_of_mem_cells hm hs),
    cellInd_of_mem (C.mem_U_of_mem_cells hm ht)] at h1
  omega

/-- The distance on `C₁` is at most the distance on `C₂`, for points in the cells of the same
two elements. For one element, the first is at most `2` (`planeWallDist_le_two`) and the second
at least `2` (`two_le_planeWallDist`). For two elements, the lower bound on `C₂` gives faces `F, G`
at the two points, the same faces are named at the points of `C₁`, and the upper bound on `C₁`
with these faces closes the gap. -/
theorem planeWallDist_le_of_cells (C₁ C₂ : CellWall h) {m m' : ℤ × ℤ}
    (hm : m ∈ fig1WallCells h) (hm' : m' ∈ fig1WallCells h) {s₁ t₁ s₂ t₂ : ℝ × ℝ}
    (hs₁ : cellCode s₁ ∈ C₁.cells m) (ht₁ : cellCode t₁ ∈ C₁.cells m')
    (hs₂ : cellCode s₂ ∈ C₂.cells m) (ht₂ : cellCode t₂ ∈ C₂.cells m') (hst₂ : s₂ ≠ t₂) :
    planeWallDist (fig1PlaneEquiv '' cellSet C₁.𝒰) (fig1PlaneEquiv s₁) (fig1PlaneEquiv t₁) ≤
      planeWallDist (fig1PlaneEquiv '' cellSet C₂.𝒰) (fig1PlaneEquiv s₂) (fig1PlaneEquiv t₂) := by
  by_cases hmm : m = m'
  · subst hmm
    have h1 := C₁.planeWallDist_le_two hm hs₁ ht₁
    have h2 := two_le_planeWallDist C₂.naming.not_square (fig1PlaneEquiv.injective.ne hst₂)
      ⟨s₂, C₂.mem_U_of_mem_cells hm hs₂, rfl⟩ ⟨t₂, C₂.mem_U_of_mem_cells hm ht₂, rfl⟩
    omega
  · have hne : ∀ (C : CellWall h) {s t : ℝ × ℝ}, cellCode s ∈ C.cells m →
        cellCode t ∈ C.cells m' → cellCode s ≠ cellCode t := fun C s t hs ht e =>
      disjoint_left.mp (C.disjoint m hm m' hm' hmm) hs (e ▸ ht)
    obtain ⟨q₂, hq₂, q₂', hq₂', hlow⟩ := C₂.naming.le_planeWallDist (hne C₂ hs₂ ht₂)
    obtain ⟨q₁, hq₁, e₁⟩ := C₁.exists_name_eq hm hs₁ (C₂.name_mem_cellFaces hm hs₂ hq₂)
    obtain ⟨q₁', hq₁', e₁'⟩ := C₁.exists_name_eq hm' ht₁ (C₂.name_mem_cellFaces hm' ht₂ hq₂')
    have hup := C₁.naming.planeWallDist_le (hne C₁ hs₁ ht₁) hq₁ hq₁'
    rw [e₁, e₁', cellInd_of_mem (C₁.mem_U_of_mem_cells hm hs₁),
      cellInd_of_mem (C₁.mem_U_of_mem_cells hm' ht₁)] at hup
    rw [cellInd_of_mem (C₂.mem_U_of_mem_cells hm hs₂),
      cellInd_of_mem (C₂.mem_U_of_mem_cells hm' ht₂)] at hlow
    have hnn := faceDist_nonneg (C₂.naming.face q₂) (C₂.naming.face q₂')
    have := Int.toNat_of_nonneg hnn
    omega

/-- **The distance of a drawing on cells depends only on the elements.** For distinct points in
the cells of the elements `m, m'` of two cell walls of the same height, the two distances are
equal. -/
theorem planeWallDist_eq (C₁ C₂ : CellWall h) {m m' : ℤ × ℤ}
    (hm : m ∈ fig1WallCells h) (hm' : m' ∈ fig1WallCells h) {s₁ t₁ s₂ t₂ : ℝ × ℝ}
    (hs₁ : cellCode s₁ ∈ C₁.cells m) (ht₁ : cellCode t₁ ∈ C₁.cells m')
    (hs₂ : cellCode s₂ ∈ C₂.cells m) (ht₂ : cellCode t₂ ∈ C₂.cells m') (hst₁ : s₁ ≠ t₁)
    (hst₂ : s₂ ≠ t₂) :
    planeWallDist (fig1PlaneEquiv '' cellSet C₁.𝒰) (fig1PlaneEquiv s₁) (fig1PlaneEquiv t₁) =
      planeWallDist (fig1PlaneEquiv '' cellSet C₂.𝒰) (fig1PlaneEquiv s₂) (fig1PlaneEquiv t₂) :=
  le_antisymm (planeWallDist_le_of_cells C₁ C₂ hm hm' hs₁ ht₁ hs₂ ht₂ hst₂)
    (planeWallDist_le_of_cells C₂ C₁ hm hm' hs₂ ht₂ hs₁ ht₁ hst₁)

end CellWall

/-- The point of a vertex of an element `m` of a wall drawn on cells lies in a cell of `m`. -/
theorem DrawnOnCells.exists_cell {G : Graph α β} {Γ : GraphDrawing G EuclideanPlane}
    {W : Wall α β} {C : CellWall W.height} (hD : DrawnOnCells Γ W C) {m : ℤ × ℤ}
    (hm : m ∈ fig1WallCells W.height) {x : α} (hx : x ∈ W.elemV m) :
    ∃ s : ℝ × ℝ, cellCode s ∈ C.cells m ∧ ptV Γ x = fig1PlaneEquiv s := by
  have h1 : ptV Γ x ∈ elemPts Γ W m := Or.inl ⟨x, hx, rfl⟩
  rw [hD m hm] at h1
  obtain ⟨s, hs, e⟩ := h1
  exact ⟨s, hs, e.symm⟩

/-- **Two drawings on cells of one wall give the same distance between distinct vertices.** -/
theorem DrawnOnCells.planeWallDist_eq {G₁ G₂ : Graph α β} {Γ₁ : GraphDrawing G₁ EuclideanPlane}
    {Γ₂ : GraphDrawing G₂ EuclideanPlane} {W : Wall α β} {C₁ C₂ : CellWall W.height}
    (hD₁ : DrawnOnCells Γ₁ W C₁) (hD₂ : DrawnOnCells Γ₂ W C₂) (hW₁ : W.graph ≤ G₁)
    (hW₂ : W.graph ≤ G₂) {x y : α} (hx : x ∈ V(W.graph)) (hy : y ∈ V(W.graph)) (hxy : x ≠ y) :
    planeWallDist (fig1PlaneEquiv '' cellSet C₁.𝒰) (ptV Γ₁ x) (ptV Γ₁ y) =
      planeWallDist (fig1PlaneEquiv '' cellSet C₂.𝒰) (ptV Γ₂ x) (ptV Γ₂ y) := by
  obtain ⟨m, hm, hxm⟩ := W.exists_mem_elemV hx
  obtain ⟨m', hm', hym⟩ := W.exists_mem_elemV hy
  obtain ⟨s₁, hs₁, e₁⟩ := hD₁.exists_cell hm hxm
  obtain ⟨t₁, ht₁, f₁⟩ := hD₁.exists_cell hm' hym
  obtain ⟨s₂, hs₂, e₂⟩ := hD₂.exists_cell hm hxm
  obtain ⟨t₂, ht₂, f₂⟩ := hD₂.exists_cell hm' hym
  have hne : ∀ {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane), W.graph ≤ G →
      ∀ s t : ℝ × ℝ, ptV Γ x = fig1PlaneEquiv s → ptV Γ y = fig1PlaneEquiv t → s ≠ t :=
    fun Γ hW s t es et hst => hxy (ptV_injOn Γ (hW.vertexSet_mono hx) (hW.vertexSet_mono hy)
      (by rw [es, et, hst]))
  rw [e₁, f₁, e₂, f₂]
  exact CellWall.planeWallDist_eq C₁ C₂ hm hm' hs₁ ht₁ hs₂ ht₂ (hne Γ₁ hW₁ _ _ e₁ f₁)
    (hne Γ₂ hW₂ _ _ e₂ f₂)

end GraphMinor.GM13
