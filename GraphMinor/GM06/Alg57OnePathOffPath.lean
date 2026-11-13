module

public import GraphMinor.GM06.Alg57OnePathCutIncidence
public import GraphMinor.GM06.Alg57OnePathFind4
import GraphMinor.GM06.Section5OpenCutSheet
import GraphMinor.GM06.Section5CoverRegion
import GraphMinor.GM06.Alg57CurrentCutCopyUnique
import GraphMinor.Compute.GM06CutRowEncoding
import GraphMinor.GM06.Alg57SubdrawingRegions

/-!
# The lifted incidence for `k = 1` off the one path

A point `p` of the cut disc whose projection `x` is off `P₁` has a neighbourhood that the
projection maps homeomorphically onto a neighbourhood of `x`, through the open sheet of
`exists_open_sheet_on_single_strip`. So `p` is in `cutRc` exactly when `x` is in the closure of
`R₁` (`cutRc_iff_off_path`). For a vertex this is read from the cut face orbit: such a vertex is not
split, its row is copied once, and the cut orbit of `c̄₁` visits that copy exactly when the old
orbit meets its row (`one_path_off_vertex_iff`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- **Points of the cut disc off the one path.** If the projection of `p` is off `P₁`, then `p` is
in `cutRc` exactly when its projection is in the closure of `R₁`. -/
theorem cutRc_iff_off_path (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hθ : L.HasTheta θ) (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) {p : D}
    (hp : cutProj D p ∉ (L.pathDrawing 0).U) :
    p ∈ cutRc G D ↔ cutProj D p ∈ closure (cylinderRegion 1 G 0) := by
  change cutCov D p ∈ closure (cylinderCoverRegion 1 G 0) ↔ _
  constructor
  · intro h
    have h' := image_closure_subset_closure_image continuous_cylinderCoverProjection ⟨_, h, rfl⟩
    exact closure_mono (image_cylinderCoverRegion_subset_region 1 G 0) h'
  · intro h
    obtain ⟨sh, hsh0, hproj, hrange⟩ := exists_open_sheet_on_single_strip L hG hθ hD hBd hstrip
    -- the lift of the projection of `p` by the sheet is `p`
    have hmem : cutCov D p ∈ range sh := by
      rw [hrange]
      exact ⟨⟨p.1, p.2, rfl⟩, hp⟩
    obtain ⟨y, hy⟩ := hmem
    have hyv : y.1 = cutProj D p := (hproj y).symm.trans (by rw [hy]; rfl)
    -- the projection is in the closure of the region inside `S`
    have hyT : y ∈ closure (Subtype.val ⁻¹' cylinderRegion 1 G 0 : Set ((L.pathDrawing 0).Uᶜ : Set ClosedCylinder)) := by
      have hRP : cylinderRegion 1 G 0 ⊆ (L.pathDrawing 0).Uᶜ := fun z hz hzP =>
        (connectedComponentIn_subset _ _ hz).2 ((L.isSubdrawing 0).2 hzP)
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
        Subtype.image_preimage_coe, inter_eq_right.mpr hRP]
      rw [mem_preimage, hyv]
      exact h
    have hmaps : MapsTo sh (Subtype.val ⁻¹' cylinderRegion 1 G 0) (cylinderCoverRegion 1 G 0) := by
      intro z hz
      have hzr : sh z ∈ range sh := mem_range_self z
      rw [hrange] at hzr
      exact lift_mem_coverRegion L hG hθ hD hBd hstrip hz hzr.1 (hproj z)
    rw [← hy]
    exact map_mem_closure sh.continuous hyT hmaps

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {L : CylinderLinkage 1 G} (rep : GM06CurrentDrawingRep x G L)

local notation "cutTables" => gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (gm06SplitRotationRows cutTables x.rotations)))
local notation "gapCut" => gm06CutDart (2 * rep.tagged.length + 1) 0

include rep in
/-- The label of a dart is in the row of a live slot exactly when the dart is at its vertex. -/
theorem label_mem_row_iff (a : Fin x.vertexCount) (ha : a ∈ rep.live)
    (d : DrawingDart (cylinderSphereDrawing rep.cuffed)) :
    persistentDartLabel rep.label d ∈ x.rotations.getD a.val [] ↔
      dartVertex rep.par d = cylinderToSphere (rep.vertex a) := by
  rw [rep.mem_row_iff]
  constructor
  · rintro ⟨-, h, hh⟩
    have hd : (⟨h.1, h.2.1⟩ : DrawingDart (cylinderSphereDrawing rep.cuffed)) = d :=
      persistentDartLabel_injective rep.label hh
    rw [← hd]
    exact h.2.2
  · intro hd
    exact ⟨ha, ⟨d.1, d.2, hd⟩, rfl⟩

include rep in
/-- **A vertex of the cut drawing off the one path, read from the cut orbit.** Let `a` be a live
slot whose vertex is off `P₁`, and `p` the point of the cut disc over it. Then `p` is in `cutRc`
exactly when the cut face orbit of `c̄₁` contains a dart of the (only) copy of `a`. -/
theorem one_path_off_vertex_iff (hG : IsCylinderSection5Drawing 1 G)
    (hno : ¬ Section5AnyReductionApplies 1 G L) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (a : Fin x.vertexCount) (ha : a ∈ rep.live) (haP : rep.vertex a ∉ (L.pathDrawing 0).U)
    {p : D} (hpa : cutProj D p = rep.vertex a) :
    p ∈ cutRc G D ↔ ∃ n, (cutNext)^[n] gapCut ∈
      (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex a.val true) [] := by
  rw [cutRc_iff_off_path L hG hθ hD hBd hstrip (hpa ▸ haP), hpa]
  obtain ⟨R, hR, hccw, -, hrot, heI, heO, hV, -, -, hface⟩ := rep.one_path_setting hG hno
  have hvS : cylinderToSphere (rep.vertex a) ∈ (cylinderSphereDrawing rep.cuffed).V := by
    rw [cylinderSphereDrawing_V, rep.cuffed_V]
    exact mem_image_of_mem _ (rep.vertex_mem a ha)
  rw [(region_incidence_of_no_reduction' L one_pos hG hno rep.cuffed_U rep.edgePar hR hccw 0
    (heI 0) (rep.inner_par 0)).1 _ hvS]
  have hproj := fun e => rep.cut_face_orbit_projection_iff hG 0 e
  simp only [Fin.val_zero, add_zero] at hproj
  simp only [hface, hproj]
  -- the vertex is not split
  have hpos : gm06CutPositionAt cutTables a.val = none := by
    rcases h : gm06CutPositionAt cutTables a.val with _ | p
    · rfl
    · exfalso
      obtain ⟨j, hj⟩ := rep.exists_path_of_cut_position a p h
      rw [Subsingleton.elim j 0] at hj
      exact haP ((L.pathDrawing 0).V_subset_U hj)
  have hlt : a.val < x.rotations.length := by rw [rep.rows_length]; exact a.isLt
  set row := x.rotations.getD a.val [] with hrow_def
  have hvr : x.rotations[a.val]? = some row := by
    rw [hrow_def, List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  have hslot : (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex a.val true) [] =
      row.map (fun d => gm06CutDart d 0) := by
    rw [splitRows_getD _ _ _ hlt true, hpos]
    have h := gm06SplitVertexRows_eq_selected none row
    simp only [gm06SplitVertexRows] at h
    exact (List.cons_eq_cons.mp h).1.symm
  rw [hslot]
  have hc : gapCut ∈ (gm06SplitRotationRows cutTables x.rotations).flatten := by
    have h := rep.reverse_inner_mem_cut hG 0
    simp only [Fin.val_zero, add_zero] at h
    exact h
  constructor
  · rintro ⟨d, hd, n, hn⟩
    refine ⟨n, ?_⟩
    have hlab : persistentDartLabel rep.label d ∈ row := (rep.label_mem_row_iff a ha d).mpr hd
    obtain ⟨v', row', r, hv', hr, hqr⟩ := exists_vertex_of_mem_split
      (cut_iterate_mem cutTables x.rotations rep.rows_flatten_nodup
        (fun _ h => rep.cut_rows_mate hG h) hc n)
    have hvv : v' = a.val := rows_index_eq_of_mem rep.rows_flatten_nodup hv' hvr
      (uncut_mem_of_mem_splitVertexRows hr hqr) (hn ▸ hlab)
    subst hvv
    rw [hvr] at hv'
    cases hv'
    rw [hpos] at hr
    simp only [gm06SplitVertexRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hqr
    · exact absurd hqr List.not_mem_nil
  · rintro ⟨n, hn⟩
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hn
    obtain ⟨-, h, hh⟩ := (rep.mem_row_iff a e).mp he
    refine ⟨⟨h.1, h.2.1⟩, h.2.2, n, ?_⟩
    rw [← heq, gm06UncutDart_cut e 0 (by decide)]
    exact hh.symm

include rep in
/-- **An edge of the cut drawing off the one path, read from the cut orbit.** Let `e` be an edge of
`G` not in `P₁`, and `d` a dart of `G⁺` along `e`. The points of the cut disc over `e` are in
`cutRc` exactly when the cut face orbit of `c̄₁` contains a copy of `d` or of its reverse. -/
theorem one_path_off_edge_iff (hG : IsCylinderSection5Drawing 1 G)
    (hno : ¬ Section5AnyReductionApplies 1 G L) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E)
    (d : DrawingDart (cylinderSphereDrawing rep.cuffed)) (hd : d.1.1 = cylinderToSphere '' e) :
    (fun p : D => radialCylinderProjection p.1) ⁻¹' e ⊆ cutRc G D ↔
      (∃ n, gm06UncutDart ((cutNext)^[n] gapCut) = persistentDartLabel rep.label d) ∨
        ∃ n, gm06UncutDart ((cutNext)^[n] gapCut) =
          gm06DartMate (persistentDartLabel rep.label d) := by
  have hdisj := deleted_edge_disjoint_subdrawing (L.isSubdrawing 0).1 he heP
  have hstep : (fun p : D => radialCylinderProjection p.1) ⁻¹' e ⊆ cutRc G D ↔
      e ⊆ closure (cylinderRegion 1 G 0) := by
    constructor
    · intro h y hy
      have hyP : y ∉ (L.pathDrawing 0).U := disjoint_left.mp hdisj hy
      obtain ⟨sh, -, hproj, hrange⟩ := exists_open_sheet_on_single_strip L hG hθ hD hBd hstrip
      have hmem : sh ⟨y, hyP⟩ ∈ range sh := mem_range_self _
      rw [hrange] at hmem
      obtain ⟨⟨q, hqD, hq⟩, -⟩ := hmem
      have hqy : radialCylinderProjection q = y := by
        have := hproj ⟨y, hyP⟩
        rw [← hq] at this
        exact this
      have hpe : (⟨q, hqD⟩ : D) ∈ (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
        change radialCylinderProjection q ∈ e
        rw [hqy]; exact hy
      have h' := (cutRc_iff_off_path L hG hθ hD hBd hstrip (p := ⟨q, hqD⟩)
        (by change radialCylinderProjection q ∉ _; rw [hqy]; exact hyP)).mp (h hpe)
      change radialCylinderProjection q ∈ _ at h'
      rwa [hqy] at h'
    · intro h p hp
      exact (cutRc_iff_off_path L hG hθ hD hBd hstrip (disjoint_left.mp hdisj hp)).mpr (h hp)
  obtain ⟨R, hR, hccw, hrev, hrot, heI, heO, hV, -, -, hface⟩ := rep.one_path_setting hG hno
  have hproj := fun e => rep.cut_face_orbit_projection_iff hG 0 e
  simp only [Fin.val_zero, add_zero] at hproj
  rw [hstep, ← image_subset_image_iff injective_cylinderToSphere, ← hd,
    (region_incidence_of_no_reduction' L one_pos hG hno rep.cuffed_U rep.edgePar hR hccw 0
      (heI 0) (rep.inner_par 0)).2 d, hface, hface, hrev, persistentDartLabel_flip, hproj, hproj]

end GM06CurrentDrawingRep

end GraphMinor.GM06
