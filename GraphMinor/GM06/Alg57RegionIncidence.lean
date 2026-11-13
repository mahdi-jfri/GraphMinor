module

public import GraphMinor.GM06.Alg57CuffFace

/-!
# Incidence with `Rᵢ` read from one face orbit

This is the incidence part (10) of Lemma 11 of our proof of VI (5.7) (outlined in
`Alg57Algorithm.lean`), for the drawing `G⁺` of the cylinder with both cuffs, carried into the
sphere.

Let `R` be the counterclockwise rotation of `G⁺`. By Lemma 3 (`sphere_faceOrbits_ccw_corner`)
the face orbits are the regions, and by `face_reverse_inner_gap` the orbit of the reverse inner gap
dart `c̄ᵢ` is the region `Rᵢ`. So a vertex of `G` is incident with `Rᵢ` exactly when it is the
vertex of a dart in the orbit of `c̄ᵢ` (`vertex_mem_closure_region_iff`), and an edge lies in the
closure of `Rᵢ` exactly when one of its darts is in that orbit (`edge_subset_closure_region_iff`).

The hypotheses are those of Lemma 3: the rotation is connected (Lemma 4) and every
vertex has a dart.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {k : ℕ} {G F : Drawing ClosedCylinder}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing F))}

/-- The drawing of the cylinder misses the point at infinity of the sphere. -/
theorem infty_notMem_cylinderSphereDrawing_U (F : Drawing ClosedCylinder) :
    (OnePoint.infty : OnePoint EuclideanPlane) ∉ (cylinderSphereDrawing F).U := by
  rw [cylinderSphereDrawing_U]
  rintro ⟨p, -, hp⟩
  exact OnePoint.coe_ne_infty _ hp

/-- The reverse dart `c̄ᵢ` of the `i`th inner gap. -/
def reverseInnerGapDart (k : ℕ) (i : Fin k) (F : Drawing ClosedCylinder)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E) :
    DrawingDart (cylinderSphereDrawing F) :=
  ⟨(cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), true), he⟩

/-- **Lemma 11, incidence (10), for `G⁺`.** For the counterclockwise rotation of the cuffed
drawing, connected and with a dart at every vertex:
* a vertex `v` of `G` is in the closure of `Rᵢ` exactly when some dart at `v` is in the face orbit
  of `c̄ᵢ`;
* a dart's edge lies in the image of the closure of `Rᵢ` exactly when the dart or its reverse is
  in that orbit. -/
theorem region_incidence_of_ccw (hG : IsCylinderSection5Drawing k G)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hR : IsDrawingRotation (cylinderSphereDrawing F) γ R)
    (hccw : IsCcwRotation (cylinderSphereDrawing F) γ R) (hc : R.Connected)
    (hV : ∀ v ∈ (cylinderSphereDrawing F).V, ∃ d : DrawingDart (cylinderSphereDrawing F),
      dartVertex γ d = v)
    (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t)) :
    (∀ v : ClosedCylinder, cylinderToSphere v ∈ (cylinderSphereDrawing F).V →
      (v ∈ closure (cylinderRegion k G i) ↔
        ∃ d : DrawingDart (cylinderSphereDrawing F), dartVertex γ d = cylinderToSphere v ∧
          R.faceOf d = R.faceOf (reverseInnerGapDart k i F he))) ∧
    (∀ d : DrawingDart (cylinderSphereDrawing F),
      d.1.1 ⊆ cylinderToSphere '' closure (cylinderRegion k G i) ↔
        R.faceOf d = R.faceOf (reverseInnerGapDart k i F he) ∨
          R.faceOf (R.rev d) = R.faceOf (reverseInnerGapDart k i F he)) := by
  obtain ⟨L, -, hedge, hvert, hcorner⟩ := sphere_faceOrbits_ccw_corner
    (infty_notMem_cylinderSphereDrawing_U F) hγ hR hccw hc hV ⟨_, he⟩
  have hface := face_reverse_inner_gap i hG hFU he hγe L hcorner
  have hcl : closure (L (R.faceOf (reverseInnerGapDart k i F he))).1 =
      cylinderToSphere '' closure (cylinderRegion k G i) := by
    rw [reverseInnerGapDart, hface,
      closure_image_region_sdiff_boundary (cylinderRegion_mem_regions hG i)]
  refine ⟨fun v hv => ?_, fun d => ?_⟩
  · have h := hvert (R.faceOf (reverseInnerGapDart k i F he)) _ hv
    rw [hcl] at h
    rw [← h]
    exact ⟨fun hx => mem_image_of_mem _ hx, fun ⟨w, hw, hwv⟩ =>
      injective_cylinderToSphere hwv ▸ hw⟩
  · rw [← hcl]
    exact hedge _ d

end GraphMinor.GM06
