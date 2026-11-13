module

public import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5AttachmentLiftSheet

/-!
# Identifying a detoured attachment contact in the cover

For the attachment count in VI (5.5), page 130, follow the lifted
homotopy path over a new attachment contact. Its starting angle is
near an old attachment lift. If the projected path misses the
antipode, the endpoint has precisely that old lifted angle. Equality
of the projected endpoint also fixes its radial coordinate.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Surface

/-- A local homotopy path ending at an attachment returns to the
specified old cover point when it stays on the same side of the antipode. -/
theorem cover_contact_eq_of_misses_attachment_antipode
    (q : C(unitInterval, CylinderCover)) (p : CylinderCover)
    (h0 : |(q 0).2 - p.2| < Real.pi)
    (hmiss : ∀ t, Circle.exp (q t).2 ≠ Circle.exp (p.2 + Real.pi))
    (h1 : cylinderCoverProjection (q 1) = cylinderCoverProjection p) : q 1 = p := by
  let a : C(unitInterval, ℝ) := ⟨fun t => (q t).2, continuous_snd.comp q.continuous⟩
  have hangle : (q 1).2 = p.2 := lifted_attachment_endpoint_eq a p.2 h0 hmiss
    (congrArg (fun x : ClosedCylinder => x.1.2) h1)
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun x : ClosedCylinder => x.1.1) h1
  · exact hangle

/-- Identify the endpoint of a homotopy fibre with an existing
attachment visit using the small-fibre angular bounds. -/
theorem homotopy_attachment_contact_eq_old_lift
    (B : C(unitInterval × unitInterval, CylinderCover))
    (A : C(unitInterval, CylinderCover)) (hzero : ∀ t, B (t, 0) = A t)
    (t u : unitInterval) (hclose : |(A t).2 - (A u).2| < Real.pi)
    (hmiss : ∀ v, Circle.exp (B (t, v)).2 ≠ Circle.exp ((A u).2 + Real.pi))
    (hend : cylinderCoverProjection (B (t, 1)) = cylinderCoverProjection (A u)) :
    B (t, 1) = A u := by
  let q : C(unitInterval, CylinderCover) :=
    ⟨fun v => B (t, v), B.continuous.comp (continuous_const.prodMk continuous_id)⟩
  apply cover_contact_eq_of_misses_attachment_antipode q (A u) ?_ hmiss hend
  change |(B (t, 0)).2 - (A u).2| < Real.pi
  rw [hzero]
  exact hclose

end GraphMinor.GM06
