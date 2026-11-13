module

public import GraphMinor.GM07.Defs
public import GraphMinor.GM19.CutMap
import GraphMinor.GM08.Section18TouchingCircleCut
import GraphMinor.GM08.Section18LoopCuts
import GraphMinor.GM08.Section18BranchCuts
import GraphMinor.GM08.Section18ArcCases

/-!
# Constructing the cut of a schism

Every one of the six shapes in VIII Section 18 admits a surface cut.
The circle construction marks its finite boundary contacts. The two
proper arc cases use the arc-cut construction. The remaining shapes use
their finite graph representations with their circles and joining lines.
The resulting map has finite fibres and is injective off the schism.
This establishes existence of the cut; the measure decrease in (18.2)
still needs the boundary-touching circle and branched cases.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- Every schism in a connected surface has a cut surface and a natural
finite-fibre cutting map. This constructs the cut referred to before
VIII (18.1) and in (18.2), pages 285–286. The measure bound is separate. -/
theorem exists_cutMap_of_schism {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {F : Set S} (hF : GM07.IsSchism F) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (ψ : Y → S), IsSurface Y ∧ GM19.IsCutMap ψ F := by
  rcases hF with hi | hii | hiii | hiv | hv | hvi
  · exact exists_cutMap_of_oArc_finite_boundary hS hi.1 hi.2.2.1
  · obtain ⟨hproper, C, hC, D, hD, hCD, hmC, hmD⟩ := hii
    obtain ⟨Y, tY, ψ, hY, hcut, _⟩ :=
      exists_cut_complexity_lt_of_schism_type_ii hS hproper hC hD hCD hmC hmD
    exact ⟨Y, tY, ψ, hY, GM19.IsCutting.isCutMap hcut⟩
  · obtain ⟨hproper, C, hC, hends, hnp⟩ := hiii
    obtain ⟨Y, tY, ψ, hY, hcut, _⟩ :=
      exists_cut_complexity_lt_of_schism_type_iii hS hproper hC hends hnp
    exact ⟨Y, tY, ψ, hY, GM19.IsCutting.isCutMap hcut⟩
  · obtain ⟨hshape, hoff, _⟩ := hiv
    rcases hshape with hbar | hwedge
    · obtain ⟨A, B, P, u, v, hA, hB, hAB, hP, hu, hv, hPA, hPB, rfl⟩ := hbar
      exact exists_cutMap_of_barbell_off_boundary hS hA hB hAB hP hu hv hPA hPB hoff
    · obtain ⟨A, B, u, hA, hB, hAB, rfl⟩ := hwedge
      exact exists_cutMap_of_meeting_circles_off_boundary hS hA hB hAB hoff
  · obtain ⟨hshape, hoff, _⟩ := hv
    obtain ⟨P, Q, R, u, v, huv, hP, hQ, hR, hPQ, hPR, hQR, rfl⟩ := hshape
    exact exists_cutMap_of_theta_off_boundary hS huv hP hQ hR hPQ hPR hQR hoff
  · obtain ⟨w, A, P, C, D, u, hA, hP, huw, hPA, rfl, hC, _, _, hwC, _, hbd⟩ := hvi
    exact exists_cutMap_of_whiskered_circle hS hA hP huw hPA hC hwC hbd

end GraphMinor.GM08
