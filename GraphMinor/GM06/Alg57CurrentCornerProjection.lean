module

public import GraphMinor.GM06.Alg57CurrentLinkageCuffRows
public import GraphMinor.GM06.Alg57NumericCornerProjection
public import GraphMinor.GM06.Alg57CurrentRegionOrbit
import GraphMinor.GM06.Alg57LinkageCuffSubdrawing
import GraphMinor.GM06.Alg57InnerCuffCorner

/-!
# Actual corner labels for the computed comparison rows

For Lemma 10 in the proof of VI (5.7), page 133, the actual current
rows and positive drawing rotation supply numeric corner labels in
the linkage-and-cuff subdrawing. They merge across every removed
end, and both full and filtered face successors preserve them.
The label at each reverse inner gap contains the prescribed region.
All these labels are constructed from the current drawing relation.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The full current numeric row table consists exactly of the
permanent labels of the actual cuffed drawing darts. -/
theorem row_label_cover (r : ℕ) : r ∈ x.rotations.flatten ↔
    ∃ d : DrawingDart (cylinderSphereDrawing rep.cuffed), persistentDartLabel rep.label d = r := by
  constructor
  · intro hr
    obtain ⟨row, hrow, hr⟩ := List.mem_flatten.mp hr
    obtain ⟨v, hv, heq⟩ := List.mem_iff_getElem.mp hrow
    let a : Fin x.vertexCount := ⟨v, rep.rows_length ▸ hv⟩
    have hm : r ∈ x.rotations.getD a.val [] := by
      simpa only [a, List.getD_eq_getElem _ _ hv, heq] using hr
    obtain ⟨d, _, hd⟩ := exists_persistentDart_of_mem_row (rep.rows a (rep.live_of_mem_row hm)) hm
    exact ⟨d, hd⟩
  · rintro ⟨d, rfl⟩
    obtain ⟨a, ha, hv⟩ := rep.sphere_vertex_cover (dartVertex_mem rep.edgePar d)
    have hm := persistentDartLabel_mem_row (rep.rows a ha) hv.symm
    have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
    rw [List.getD_eq_getElem _ _ hi] at hm
    exact List.mem_flatten.mpr ⟨_, List.getElem_mem hi, hm⟩

/-- The actual current arrays give comparison-region labels with
both numeric face invariances, the local merging rule at removed
ends, and the prescribed region at every reverse inner gap. -/
theorem exists_numeric_comparison_labels (hG : IsCylinderSection5Drawing k G) :
    ∃ (H : Drawing ClosedCylinder) (_hHF : H.IsSubdrawing rep.cuffed),
      H.U = (⋃ j : Fin k, (L.pathDrawing j).U) ∪ bd ClosedCylinder ∧
      H.V = ⋃ j : Fin k, (L.pathDrawing j).V ∧
      ∃ g : ℕ → Option (cylinderSphereDrawing H).R,
        (∀ r ∈ x.rotations.flatten, ∃ s, g r = some s) ∧
        (∀ row ∈ x.rotations, ∀ r ∈ row,
          gm06LinkageCuffKeep rep.tagged.length x.linkage r = false →
            g (row.formPerm.symm r) = g r) ∧
        (∀ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
          g ((dartMatePerm.trans (gm06RotationPermutation x.rotations).symm)
            (persistentDartLabel rep.label d)) = g (persistentDartLabel rep.label d)) ∧
        (∀ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
          gm06LinkageCuffKeep rep.tagged.length x.linkage (persistentDartLabel rep.label d) = true →
            g ((dartMatePerm.trans (gm06RotationPermutation
              (x.rotations.map (List.filter (gm06LinkageCuffKeep rep.tagged.length x.linkage)))).symm)
                (persistentDartLabel rep.label d)) = g (persistentDartLabel rep.label d)) ∧
        ∀ i : Fin k, ∃ s : (cylinderSphereDrawing H).R,
          g (2 * (rep.tagged.length + i.val) + 1) = some s ∧
            cylinderToSphere '' (cylinderRegion k G i \ bd ClosedCylinder) ⊆ s.val := by
  classical
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) :=
    IsClosedSurface.locallyConnectedSpace
      (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  obtain ⟨H, hHF, hHU, hHV, _, hHE⟩ := exists_linkage_cuff_subdrawing L hG
    rep.subdrawing rep.cuffed_U rep.cuffed_V
  have hS := cylinderSphereDrawing_isSubdrawing hHF
  obtain ⟨R, hR, hccw, hrev, hrot⟩ := rep.exists_ccwRotation
  have hinf := infty_notMem_cylinderSphereDrawing_U rep.cuffed
  obtain ⟨ρ, hρ, hform⟩ := exists_cornerLabel hinf rep.edgePar hR hccw
  have hkeep (d : DrawingDart (cylinderSphereDrawing rep.cuffed)) :
      gm06LinkageCuffKeep rep.tagged.length x.linkage (persistentDartLabel rep.label d) = true ↔
        d.val.1 ∈ (cylinderSphereDrawing H).E := by
    let f : (cylinderSphereDrawing rep.cuffed).E := ⟨d.val.1, d.property⟩
    have hf : f.val ∈ (image cylinderToSphere) '' rep.cuffed.E := by
      simpa only [cylinderSphereDrawing_E] using f.property
    obtain ⟨e, he, hef⟩ := hf
    let e' : rep.cuffed.E := ⟨e, he⟩
    change gm06LinkageCuffKeep rep.tagged.length x.linkage (2 * rep.label f + d.val.2.toNat) = true ↔ _
    rw [rep.linkage_cuff_keep_iff hG f e' hef.symm d.val.2]
    constructor
    · intro hh
      rw [cylinderSphereDrawing_E]
      exact ⟨e, (hHE e).mpr ⟨he, hh⟩, hef⟩
    · intro hh
      rw [cylinderSphereDrawing_E] at hh
      obtain ⟨q, hq, hqf⟩ := hh
      have hqe : q = e := Set.image_injective.mpr injective_cylinderToSphere (hqf.trans hef.symm)
      exact ((hHE e).mp (hqe ▸ hq)).2
  obtain ⟨g, hg, hskip, hfiltered⟩ := exists_numeric_subdrawing_corner_labels hS rep.label
    x.rotations rep.rows_flatten_nodup rep.row_label_cover R hR hrot ρ hρ
      (gm06LinkageCuffKeep rep.tagged.length x.linkage) hkeep
  refine ⟨H, hHF, hHU, hHV, g, ?_, hskip, ?_, hfiltered, ?_⟩
  · intro r hr
    obtain ⟨d, rfl⟩ := (rep.row_label_cover r).mp hr
    exact ⟨_, hg d⟩
  · intro d
    rw [← persistentDartLabel_face rep.label x.rotations R hrev hrot, hg, hg]
    apply congrArg some
    apply congrArg (regionInSubdrawing hS)
    exact Subtype.ext (hρ.coherent d)
  · intro i
    obtain ⟨f, hf, _⟩ := rep.inner_labels i
    have he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈
        (cylinderSphereDrawing rep.cuffed).E := hf ▸ f.property
    let c := reverseInnerGapDart k i rep.cuffed he
    have hregion : ρ c = cylinderToSphere '' (cylinderRegion k G i \ bd ClosedCylinder) := by
      have hh := face_reverse_inner_gap (i := i) hG rep.cuffed_U he (rep.inner_par i) hρ.label
        (fun d a ha Φm Ψm hpm hΨm hposm hDm Wm hWm δm hrunm => by
          rw [hρ.label_faceOf]
          exact cornerLabel_eq_mid hinf rep.edgePar hform d a ha Φm Ψm
            hpm hΨm hposm hDm Wm hWm δm hrunm)
      exact hh
    refine ⟨regionInSubdrawing hS ⟨ρ c, hρ.region c⟩, ?_, ?_⟩
    · have hh := hg c
      simpa only [c, rep.reverseInnerGapDart_label i he] using hh
    · have hh := subset_regionInSubdrawing hS ⟨ρ c, hρ.region c⟩
      intro p hp
      have hpc : p ∈ ρ c := by rw [hregion]; exact hp
      exact hh hpc

end GM06CurrentDrawingRep
end GraphMinor.GM06
