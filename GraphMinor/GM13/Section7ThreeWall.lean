module

public import GraphMinor.GM13.Section7Induced
public import GraphMinor.GM13.Section7Three
public import GraphMinor.GM13.Section7Fig1Homeo

/-!
# Graph Minors XIII, (7.3) with `r = 0`, for a wall drawn as in Fig. 1

(7.6) uses (7.3) only with `r = 0`, and it uses it again and again on the walls it gets. So we
first prove one step for any wall `W` that is drawn on the cells of a cell wall `C`
(`DrawnOnCells.exists_step`): pick the element `mv` of `W` that holds `v`, pick a shape that
deletes `mv` (`exists_deleting_shape`), and take the new wall of a realization of it. The new wall
is drawn on the cells of the new cell wall (`DrawnOnCells.wall`), the vertex `v` is not in it
(`Shape.Realization.not_mem_wall_of_own_none`), and the distance drops by at most `4`
(`CellWall.transform_distGeSub`).

Then (7.3) with `r = 0` for a wall `H` drawn as in Fig. 1 (`theorem_7_3_zero`) is this step for
`CellWall.fig1`, with the drawing of the new wall `H'` induced by the drawing of `H`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

variable {α : Type u} {β : Type v}

/-- `exists_deleting_shape` for a height `h` that is equal to `h' + 2`. -/
theorem exists_deleting_shape_of_eq {h h' : ℕ} (e : h = h' + 2) (hh' : 1 ≤ h') (he' : Even h')
    {m : ℤ × ℤ} (hm : m ∈ fig1WallCells h) :
    ∃ τ : Shape h h', τ.KI 4 ∧ τ.own m = none ∧ ∃ R : τ.Realization, R.RayOK ∧ R.RowMono := by
  subst e
  obtain ⟨τ, hT, hown, hR⟩ := exists_deleting_shape hh' he' hm
  exact ⟨τ, hT.ki, hown, hR⟩

/-- **One step of (7.3) with `r = 0`, on cells.** Let `W` be a wall of height `h' + 2` drawn by
`Γ` on the cells of `C`, and let `v` be a vertex of `W`. Then there is a wall `W' ≤ W` of
height `h'`, drawn by `Γ` on the cells of a cell wall `C'`, with `v ∉ V(W')`, whose distance
function on cells is at least that of `C` minus `4`. If `C` is a homeomorphic image of Fig. 1,
so is `C'`. -/
theorem DrawnOnCells.exists_step {G : Graph α β} {Γ : GraphDrawing G EuclideanPlane}
    {W : Wall α β} {C : CellWall W.height} (hD : DrawnOnCells Γ W C) {h' : ℕ}
    (e : W.height = h' + 2) (hh' : 1 ≤ h') (he' : Even h') {v : α} (hv : v ∈ V(W.graph)) :
    ∃ (W' : Wall α β) (C' : CellWall W'.height), W'.graph ≤ W.graph ∧ W'.height = h' ∧
      DrawnOnCells Γ W' C' ∧ (C.IsFig1Homeo → C'.IsFig1Homeo) ∧ v ∉ V(W'.graph) ∧
      DistGeSub (planeWallDist (fig1PlaneEquiv '' cellSet C'.𝒰))
        (planeWallDist (fig1PlaneEquiv '' cellSet C.𝒰)) 4 := by
  obtain ⟨mv, hmv, hvm⟩ := W.exists_mem_elemV hv
  obtain ⟨τ, hKI, hown, R, hray, hmono⟩ := exists_deleting_shape_of_eq e hh' he' hmv
  exact ⟨R.wall W hh' he', C.transform τ hh' he', R.wall_graph_le W hh' he', rfl,
    hD.wall R hh' he', fun hC => hC.transform R (by omega) W.even_height hh' he' hray hmono,
    R.not_mem_wall_of_own_none W hh' he' hown hvm,
    C.transform_distGeSub τ hh' he' (by norm_num) hKI⟩

/-- The induced drawing of a wall lies in the drawing `Γ`: vertex points are in `V ⊆ U`, and
edges are parts of `U \ V`. -/
theorem indU_subset {G : Graph α β} (Γ : GraphDrawing G EuclideanPlane) (W : Wall α β)
    (hW : W.graph ≤ G) : indU Γ W ⊆ Γ.drawing.U := by
  rintro z (⟨x, hx, rfl⟩ | hz)
  · exact Γ.drawing.V_subset_U (ptV_mem_V Γ (hW.vertexSet_mono hx))
  · obtain ⟨f, hf, hz⟩ := mem_iUnion₂.mp hz
    have hE := arcE_mem_E Γ (hW.edgeSet_mono hf)
    rw [← Γ.drawing.closure_diff_V hE] at hz
    exact Γ.drawing.closure_subset_U hE hz.1

/-- Two distinct points `s ≠ t` with `s` on a drawing made of cells, none of them a square, are
at distance at least `1`: a line from `s` to `t` that attains the distance contains `s`. -/
theorem one_le_planeWallDist_cellSet {𝒰 : Set (ℤ × ℤ)} (h𝒰 : ∀ c ∈ 𝒰, ¬ IsSquareCell c)
    {s t : EuclideanPlane} (hst : s ≠ t) (hs : s ∈ fig1PlaneEquiv '' cellSet 𝒰) :
    1 ≤ planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) s t := by
  obtain ⟨L, hL, hfin, hcard⟩ := exists_line_ncard_eq_planeWallDist_cellSet h𝒰 hst
  rw [← hcard, Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero hfin]
  obtain ⟨f, h0, -⟩ := hL
  exact Set.nonempty_iff_ne_empty.mp ⟨s, h0 ▸ (f 0).2, hs⟩

/-- **A wall drawn on the cells of a homeomorphic image of Fig. 1 is drawn as in Fig. 1.** Let
`Γ` draw a graph `G` that contains the wall `H'`, and let `H'` be drawn on the cells of a cell
wall `C'` that is a homeomorphic image of Fig. 1. If the drawing of `H'` and its vertex points are
the images under a homeomorphism `φ` of the drawing that `Γ` induces on `H'`, then `H'` is drawn
as in Fig. 1: `exists_fig1_of_drawnOnCells` gives a drawing of Fig. 1 and a homeomorphism onto
the induced drawing, and we follow it by `φ`. -/
theorem DrawnWall.isFigure1_of_drawnOnCells {G : Graph α β} {Γ : GraphDrawing G EuclideanPlane}
    (H' : DrawnWall α β) (hle : H'.graph ≤ G) {C' : CellWall H'.height}
    (hD : DrawnOnCells Γ H'.toWall C') (hC : C'.IsFig1Homeo) (φ : EuclideanPlane ≃ₜ EuclideanPlane)
    (hU : H'.drawingU = φ '' indU Γ H'.toWall)
    (hP : ∀ u ∈ V(H'.graph), H'.vertexPoint u = φ (ptV Γ u)) : H'.IsFigure1 := by
  obtain ⟨Ψ, Γ', hΓ', hind, hpt⟩ := exists_fig1_of_drawnOnCells hle hD hC
  refine ⟨Ψ.trans φ, Γ', hΓ', ?_, fun u hu => ?_⟩
  · rw [hU, hind, image_image]
    rfl
  · rw [hP u hu, hpt u hu]
    rfl

/-- **Graph Minors XIII, (7.3) with `r = 0`, for a wall drawn as in Fig. 1** (Section 7, page 90):
"*Let $H$ be a wall of height $h$ with distance function $d$ and let $v \in V(H)$. Let $r \ge 0$
be an integer with $h \ge 2r + 4$. Then there is a subgraph $H'$ of $H$, which is a wall of
height $h - 2r - 2$, such that*

*(i) $d' \ge d - 4r - 4$, where $d'$ is the distance function in $H'$*

*(ii) there is no vertex $u$ of $H'$ with $d(u, v) \le r$.*" Here `r = 0`. The paper uses
for `H'` "the drawing of $H'$ obtained from the given drawing of $H$": `H'.drawingU` is the image
under `φ` of the points of the vertices and the edges of `H'` in the drawing `Γ` of Fig. 1 that
draws `H`. -/
theorem theorem_7_3_zero (H : DrawnWall α β) (v : α) (hF : H.IsFigure1) (hv : v ∈ V(H.graph))
    (hh : 4 ≤ H.height) :
    ∃ H' : DrawnWall α β,
      H'.IsFigure1 ∧
      H'.graph ≤ H.graph ∧ H'.drawingU ⊆ H.drawingU ∧ H'.vertexPoint = H.vertexPoint ∧
      H'.height = H.height - 2 ∧ DistGeSub H'.planeDist H.planeDist 4 ∧
      (∀ u ∈ V(H'.graph), ¬ H.dist u v ≤ 0) ∧
      ∃ (φ : EuclideanPlane ≃ₜ EuclideanPlane) (Γ : GraphDrawing H.graph EuclideanPlane),
        IsFigure1CoordDrawing H.toWall Γ ∧ H.drawingU = φ '' Γ.drawing.U ∧
        (∀ (u : α) (hu : u ∈ V(H.graph)), H.vertexPoint u = φ (Γ.iso.vertexEquiv ⟨u, hu⟩).1) ∧
        H'.drawingU = φ '' indU Γ H'.toWall := by
  obtain ⟨φ, Γ, hΓ, hU, hP⟩ := hF
  have hh1 : 1 ≤ H.height := by omega
  have hD := drawnOnCells_fig1 hΓ hh1 H.even_height
  have he' : Even (H.height - 2) := by
    obtain ⟨k, hk⟩ := H.even_height
    exact ⟨k - 1, by omega⟩
  obtain ⟨W', C', hle, hht, hD', hC', hvW', hdist⟩ :=
    hD.exists_step (h' := H.height - 2) (by omega) (by omega) he' hv
  have hP' : ∀ u ∈ V(H.graph), H.vertexPoint u = φ (ptV Γ u) := fun u hu => by
    rw [hP u hu, ptV_of_mem Γ hu]
  -- the drawing of `H` is the point set of the cells of Fig. 1
  have hUH : Γ.drawing.U = fig1PlaneEquiv '' cellSet (CellWall.fig1 hh1 H.even_height).𝒰 := by
    rw [hΓ.drawing_U_eq, fig1WallSet_eq_cellSet]
    rfl
  let H' : DrawnWall α β :=
    { W' with
      drawingU := φ '' indU Γ W'
      vertexPoint := H.vertexPoint
      vertexPoint_mem := fun u hu => by
        rw [hP' u (hle.vertexSet_mono hu)]
        exact ⟨ptV Γ u, Or.inl ⟨u, hu, rfl⟩, rfl⟩
      vertexPoint_injOn := H.vertexPoint_injOn.mono hle.vertexSet_mono }
  refine ⟨H', H'.isFigure1_of_drawnOnCells hle hD' (hC' (CellWall.isFig1Homeo_fig1 hh1 _)) φ rfl
    (fun u hu => hP' u (hle.vertexSet_mono hu)), hle, ?_, rfl, hht, ?_, ?_, φ, Γ, hΓ, hU, hP, rfl⟩
  · -- (the drawing of `H'` is part of that of `H`)
    rw [hU]
    exact image_mono (indU_subset Γ W' hle)
  · -- (i)
    intro s t
    obtain ⟨s₀, rfl⟩ := φ.surjective s
    obtain ⟨t₀, rfl⟩ := φ.surjective t
    change planeWallDist H.drawingU (φ s₀) (φ t₀) ≤ planeWallDist (φ '' indU Γ W') (φ s₀) (φ t₀) + 4
    rw [hU, planeWallDist_image_homeomorph, planeWallDist_image_homeomorph, hUH, hD'.indU_eq]
    exact hdist s₀ t₀
  · -- (ii)
    intro u hu
    have huH := hle.vertexSet_mono hu
    have hne : ptV Γ u ≠ ptV Γ v := fun e =>
      hvW' (ptV_injOn Γ huH hv e ▸ hu)
    have hs : ptV Γ u ∈ fig1PlaneEquiv '' cellSet (CellWall.fig1 hh1 H.even_height).𝒰 := by
      rw [← hUH]
      exact Γ.drawing.V_subset_U (ptV_mem_V Γ huH)
    have h1 : 1 ≤ planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells H.height)) (ptV Γ u)
        (ptV Γ v) := one_le_planeWallDist_cellSet (fig1WallCells_not_square _) hne hs
    rw [DrawnWall.dist, DrawnWall.planeDist, hP' u huH, hP' v hv, hU,
      planeWallDist_image_homeomorph, hUH]
    exact Nat.not_le.mpr h1

end GraphMinor.GM13
