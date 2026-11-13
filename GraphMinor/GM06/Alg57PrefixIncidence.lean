module

public import GraphMinor.GM06.Alg57RegionIncidence

/-!
# The incidence tests of Reduction 4 read from one face orbit

Reduction 4 of VI, page 129, asks whether a path, or a prefix of a linkage path, lies in the closure
of the region `Rᵢ`. A drawing lies in a closed set exactly when its vertices and edges do. So by the
incidence statement (10) of Lemma 11 (`region_incidence_of_ccw`) this question is answered by the
face orbit of the reverse inner gap dart `c̄ᵢ`: every vertex of the path must be the vertex of a
dart in that orbit, and every edge must have a dart in that orbit
(`subset_closure_region_iff_of_ccw`). This is the geometric side of the prefix invariant (11) of our
proof of VI (5.7) (outlined in `Alg57Algorithm.lean`), and of the test that the path `Qᵢ` of
Reduction 4 lies in the closure of `Rᵢ`.

For `k ≥ 2` the corrected Reduction 4 is the printed one (`section5Reduction4Step_iff_of_two_le`),
whose incidence is incidence with `Rᵢ` in the cylinder. So for `k ≥ 2` no lift is needed: the
face orbit of `G⁺` in the sphere answers the printed tests directly.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A drawing lies in a closed set exactly when its vertices and its edges do. -/
theorem drawing_U_subset_iff_of_isClosed {S : Type*} [TopologicalSpace S] (P : Drawing S)
    {X : Set S} (hX : IsClosed X) : P.U ⊆ X ↔ (∀ v ∈ P.V, v ∈ X) ∧ ∀ e ∈ P.E, e ⊆ X := by
  rw [P.U_eq, union_subset_iff, iUnion₂_subset_iff]
  exact and_congr Iff.rfl (forall₂_congr fun e _ =>
    ⟨fun h => subset_closure.trans h, fun h => closure_minimal h hX⟩)

variable {k : ℕ} {G F : Drawing ClosedCylinder}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing F))}

/-- **Reduction 4 incidence from the face orbit.** Let `R` be the counterclockwise rotation of
the cuffed drawing `F` of `G`, connected and with a dart at every vertex. A subdrawing `P` of `G`
lies in the closure of `Rᵢ` exactly when every vertex of `P` is the vertex of a dart in the face
orbit of `c̄ᵢ`, and every edge of `P` has a dart in that orbit. -/
theorem subset_closure_region_iff_of_ccw (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hR : IsDrawingRotation (cylinderSphereDrawing F) γ R)
    (hccw : IsCcwRotation (cylinderSphereDrawing F) γ R) (hc : R.Connected)
    (hV : ∀ v ∈ (cylinderSphereDrawing F).V, ∃ d : DrawingDart (cylinderSphereDrawing F),
      dartVertex γ d = v)
    (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t))
    {P : Drawing ClosedCylinder} (hP : P.IsSubdrawing G) :
    P.U ⊆ closure (cylinderRegion k G i) ↔
      (∀ v ∈ P.V, ∃ d : DrawingDart (cylinderSphereDrawing F),
        dartVertex γ d = cylinderToSphere v ∧
          R.faceOf d = R.faceOf (reverseInnerGapDart k i F he)) ∧
      (∀ e ∈ P.E, ∃ (b : Bool) (he' : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E),
        R.faceOf ⟨(cylinderToSphere '' e, b), he'⟩ =
          R.faceOf (reverseInnerGapDart k i F he)) := by
  obtain ⟨hvert, hedge⟩ := region_incidence_of_ccw hG hFU hγ hR hccw hc hV i he hγe
  rw [drawing_U_subset_iff_of_isClosed P isClosed_closure]
  refine and_congr (forall₂_congr fun v hv => ?_) (forall₂_congr fun e heP => ?_)
  · refine hvert v ?_
    rw [cylinderSphereDrawing_V]
    exact mem_image_of_mem _ (hGF.1 (hP.1 hv))
  · have heF : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E := by
      rw [cylinderSphereDrawing_E]
      exact mem_image_of_mem _ (hGF.2 (hP.2 heP))
    have himg : e ⊆ closure (cylinderRegion k G i) ↔
        cylinderToSphere '' e ⊆ cylinderToSphere '' closure (cylinderRegion k G i) :=
      (image_subset_image_iff injective_cylinderToSphere).symm
    rw [himg, hedge ⟨(cylinderToSphere '' e, false), heF⟩]
    constructor
    · rintro (h | h)
      · exact ⟨false, heF, h⟩
      · rw [hR.rev_eq] at h
        exact ⟨true, heF, h⟩
    · rintro ⟨b, he', h⟩
      cases b
      · exact Or.inl h
      · right
        rw [hR.rev_eq]
        exact h

end GraphMinor.GM06
