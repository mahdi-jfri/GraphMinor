module

public import GraphMinor.GM08.Defs6to18
public import GraphMinor.Surface.Defs
import GraphMinor.GM08.Section9DiscMinor
import GraphMinor.GM08.Section9DiscMatch
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.GM08.Section9GraftDrawing
import GraphMinor.GM08.Section9Transport
import GraphMinor.GM07.Section3
import GraphMinor.Surface.Disc
import GraphMinor.GM06.DiscRegions

/-!
# Graph Minors VIII (9.3): a large boundary-linked nest simulates a graft

Fix a drawing of the target graft. Match its boundary roots to the host
roots by a disc homeomorphism. Parallel rings in a sufficiently large
boundary-linked nest satisfy VII (9.4), which gives a boundary-rooted
minor. Forget directions and transfer its branches through the drawing
isomorphisms to obtain the required graft simulation.
-/

public section

namespace GraphMinor.GM08

open Set Surface Graph

universe u v u' v' w

/-- Graph Minors VIII, (9.3), page 270: a sufficiently large
boundary-linked nest simulates any fixed disc-embeddable graft of the
same index. The proof applies Graph Minors VII (9.4). -/
theorem theorem_9_3_proof {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'} {S : Type w} [TopologicalSpace S]
    (hΔ : IsClosedDisc (univ : Set S)) (Y : Graft α β) (hY : EmbedsGraft S Y) :
    ∃ r s : ℕ, Y.index ≤ r ∧ Y.index ≤ s ∧
      ∀ (X : Graft α' β') (_hX : X.index = Y.index)
        (gd : GraftDrawing X.G X.T S) (N : DrawingNest gd.drawing univ r s),
        IsBoundaryLinkedNest gd.drawing univ N → IsGraftSimulatedIn Y X := by
  classical
  have hS := isSurface_of_closedDisc_univ hΔ
  have : T2Space S := hS.2.1
  obtain ⟨x, -⟩ := hΔ.isPathConnected.nonempty
  have : Nonempty S := ⟨x⟩
  obtain ⟨gdY⟩ := hY
  let R := GM07.rCylinderBound gdY.drawing * 5 ^ (gdY.drawing.V.ncard + gdY.drawing.E.ncard)
  refine ⟨max Y.index R, max Y.index (2 * R + 3), le_max_left _ _, le_max_left _ _, ?_⟩
  intro X hX gd N hBL
  obtain ⟨a, ha⟩ := exists_disc_boundary_match hΔ
    (gdY.drawing.finite_V.inter_of_left _) (gd.drawing.finite_V.inter_of_left _)
    (by rw [GM06.discBd_univ]; exact inter_subset_right)
    (by rw [GM06.discBd_univ]; exact inter_subset_right)
    (by rw [graftDrawing_boundary_ncard gdY, graftDrawing_boundary_ncard gd]; exact hX.symm)
  let H := GM07.mapDrawingHomeo a gdY.drawing
  have hbd : H.V ∩ bd S = gd.drawing.V ∩ bd S := by
    change (a '' gdY.drawing.V) ∩ bd S = _
    rw [← image_bd_homeomorph a, ← image_inter a.injective, image_bd_homeomorph a]
    exact ha
  have hV : H.V.ncard = gdY.drawing.V.ncard :=
    ncard_image_of_injective _ a.injective
  have hE : H.E.ncard = gdY.drawing.E.ncard := by
    rw [show H.E = (image a) '' gdY.drawing.E from GM07.mapDrawingHomeo_E a _]
    exact ncard_image_of_injective _ (image_injective.mpr a.injective)
  have hR : GM07.rCylinderBound H * 5 ^ (H.V.ncard + H.E.ncard) = R := by
    dsimp only [R, GM07.rCylinderBound]
    rw [hV, hE]
  obtain ⟨ηv, ηe, hm, hmroot⟩ := exists_minorModel_of_boundaryLinkedNest hΔ H gd.drawing
    (GM07.IsProper.map_homeo a gdY.isProper) gd.isProper hbd.symm
    (by rw [hR]; exact le_max_right _ _)
    (by rw [hR]; exact le_max_right _ _) N hBL
  obtain ⟨e, he⟩ := drawing_edges_nonempty_of_oArc
    (N.circuit ⟨0, by omega⟩).isOArc_U (N.circuit ⟨0, by omega⟩).U_sub_drawing
  have : Nonempty _ := ⟨(gd.iso.edgeEquiv.symm ⟨e, he⟩).1⟩
  apply isGraftSimulatedIn_of_drawing_model gd
    (gdY.iso.isGraphBij.trans (isGraphBij_mapDrawingHomeo a gdY.drawing)) hbd
    (fun v hv => ?_) hm hmroot hX
  change a (gdY.iso.fv v) ∈ bd S
  rw [← image_bd_homeomorph a]
  refine mem_image_of_mem a ?_
  rw [gdY.iso.fv_of_mem (Y.T_subset hv)]
  exact (gdY.mem_bd_iff v (Y.T_subset hv)).mpr hv

end GraphMinor.GM08
