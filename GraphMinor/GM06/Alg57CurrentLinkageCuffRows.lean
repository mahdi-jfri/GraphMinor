module

public import GraphMinor.GM06.Alg57CurrentLinkageEdges
public import GraphMinor.GM06.Alg57RestrictedRotations
public import GraphMinor.GM06.Section5CappedInitialPath
import GraphMinor.GM06.Alg57LinkageCuffSubdrawing

/-!
# Positive rows of the linkage and cuff comparison

For the local side proof of VI (5.7), page 133, filter the current
rows to the linkage and cuffs. The finite keep test has exactly that
edge meaning. Restricting the actual chart therefore gives the
positive rows of the comparison drawing, with all retained permanent
labels and edge parametrizations unchanged.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The filtered current rows represent the actual linkage and cuff
comparison drawing, in the restricted positive charts. This supplies
the local comparison in Lemma 10 of the proof of VI (5.7). -/
theorem exists_linkage_cuff_rows (hG : IsCylinderSection5Drawing k G) :
    ∃ (H : Drawing ClosedCylinder) (hHF : H.IsSubdrawing rep.cuffed),
      H.U = (⋃ j : Fin k, (L.pathDrawing j).U) ∪ bd ClosedCylinder ∧
      H.V = ⋃ j : Fin k, (L.pathDrawing j).V ∧
      (∀ j : Fin k, (L.pathDrawing j).IsSubdrawing H) ∧
      (∀ e, e ∈ H.E ↔ e ∈ rep.cuffed.E ∧
        ((∃ j : Fin k, e ∈ (L.pathDrawing j).E) ∨ e ⊆ bd ClosedCylinder)) ∧
      ∀ a ∈ rep.live,
        GM06PersistentRotationRowRep
          (gm06RestrictEdgeLabels (cylinderSphereDrawing_isSubdrawing hHF) rep.label)
          rep.par (cylinderToSphere (rep.vertex a))
          ((x.rotations.getD a.val []).filter (gm06LinkageCuffKeep rep.tagged.length x.linkage)) := by
  obtain ⟨H, hHF, hHU, hHV, hPH, hHE⟩ := exists_linkage_cuff_subdrawing L hG
    rep.subdrawing rep.cuffed_U rep.cuffed_V
  have hS := cylinderSphereDrawing_isSubdrawing hHF
  have hkeep (f : (cylinderSphereDrawing rep.cuffed).E) (b : Bool) :
      gm06LinkageCuffKeep rep.tagged.length x.linkage (2 * rep.label f + b.toNat) = true ↔
        f.val ∈ (cylinderSphereDrawing H).E := by
    have hf : f.val ∈ (image cylinderToSphere) '' rep.cuffed.E := by
      simpa only [cylinderSphereDrawing_E] using f.property
    obtain ⟨e, he, hef⟩ := hf
    let e' : rep.cuffed.E := ⟨e, he⟩
    rw [rep.linkage_cuff_keep_iff hG f e' hef.symm b]
    constructor
    · intro h
      rw [cylinderSphereDrawing_E]
      exact ⟨e, (hHE e).mpr ⟨he, h⟩, hef⟩
    · intro h
      rw [cylinderSphereDrawing_E] at h
      obtain ⟨g, hg, hgf⟩ := h
      have hge : g = e := Set.image_injective.mpr injective_cylinderToSphere (hgf.trans hef.symm)
      exact ((hHE e).mp (hge ▸ hg)).2
  refine ⟨H, hHF, hHU, hHV, hPH, hHE, fun a ha => ?_⟩
  exact persistent_rotation_row_of_subdrawing hS rep.label (rep.rows a ha)
    (gm06LinkageCuffKeep rep.tagged.length x.linkage) hkeep

end GM06CurrentDrawingRep
end GraphMinor.GM06
