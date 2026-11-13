module

public import GraphMinor.GM06.Alg57CurrentFaceRotation
public import GraphMinor.GM06.Alg57CurrentCutOrbit
public import GraphMinor.GM06.Alg57RotationConnected
import GraphMinor.GM06.Alg57OnePathConnected

/-!
# Region incidence through the actual current cut orbit

For VI (5.7), page 133, failure of Reduction 2 implies that incidence with the
region adjoining the chosen inner gap is incidence with its drawing
face. Permanent labels turn that face into the old numeric orbit.
The proved cut projection then turns it into the projected orbit of
the actual split rows. No cut or face representation is assumed.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The reverse inner gap carries its prescribed permanent directed
label in the cuffed drawing. -/
theorem reverseInnerGapDart_label (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈
      (cylinderSphereDrawing rep.cuffed).E) :
    persistentDartLabel rep.label (reverseInnerGapDart k i rep.cuffed he) =
      2 * (rep.tagged.length + i.val) + 1 := by
  obtain ⟨f, hf, hl⟩ := rep.inner_labels i
  have heq : (⟨cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), he⟩ :
      (cylinderSphereDrawing rep.cuffed).E) = f := Subtype.ext hf.symm
  simp only [persistentDartLabel, reverseInnerGapDart, heq, hl, Bool.toNat_true]

/-- Region incidence is the old numeric face orbit selected by the
actual reverse inner gap. This is the uncut part of equation (10)
in the proof of VI (5.7), for at least two linkage paths. -/
theorem region_incidence_old_orbit (_hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (i : Fin k) :
    let next := dartMatePerm.trans (gm06RotationPermutation x.rotations).symm
    (∀ v : ClosedCylinder, v ∈ G.V →
      (v ∈ closure (cylinderRegion k G i) ↔
        ∃ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
          dartVertex rep.par d = cylinderToSphere v ∧
          ∃ n : ℕ, next^[n] (2 * (rep.tagged.length + i.val) + 1) =
            persistentDartLabel rep.label d)) ∧
    (∀ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
      d.val.1 ⊆ cylinderToSphere '' closure (cylinderRegion k G i) ↔
        (∃ n : ℕ, next^[n] (2 * (rep.tagged.length + i.val) + 1) =
          persistentDartLabel rep.label d) ∨
        ∃ n : ℕ, next^[n] (2 * (rep.tagged.length + i.val) + 1) =
          gm06DartMate (persistentDartLabel rep.label d)) := by
  dsimp only
  obtain ⟨R, hR, hccw, hrev, hrot⟩ := rep.exists_ccwRotation
  obtain ⟨f, hf, _⟩ := rep.inner_labels i
  have he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈
      (cylinderSphereDrawing rep.cuffed).E := hf ▸ f.property
  have hU : IsPreconnected (cylinderSphereDrawing rep.cuffed).U := by
    rw [cylinderSphereDrawing_U, rep.cuffed_U, union_comm]
    exact ((isConnected_drawing_and_cuffs_of_no_reduction2 L hG.1 hG hno).image _
      continuous_cylinderToSphere.continuousOn).isPreconnected
  obtain ⟨hV, hE⟩ := region_incidence_of_ccw hG rep.cuffed_U rep.edgePar hR hccw
    (DartRotation.connected_of_isPreconnected_U rep.edgePar hR hU)
    (exists_dart_of_isPreconnected_U rep.edgePar hU ⟨_, he⟩) i he (rep.inner_par i)
  have hface (d : DrawingDart (cylinderSphereDrawing rep.cuffed)) :=
    faceOf_eq_iff_permanent_orbit rep.label x.rotations R hrev hrot
      (reverseInnerGapDart k i rep.cuffed he) d
  simp only [rep.reverseInnerGapDart_label i he] at hface
  constructor
  · intro v hv
    have hvS : cylinderToSphere v ∈ (cylinderSphereDrawing rep.cuffed).V := by
      rw [cylinderSphereDrawing_V, rep.cuffed_V]
      exact mem_image_of_mem _ hv
    rw [hV v hvS]
    exact exists_congr (fun d => and_congr_right (fun _ => hface d))
  · intro d
    rw [hE, hface d, hface (R.rev d), hrev, persistentDartLabel_flip]

/-- Region incidence is read from the projected orbit of the split
rows built from the actual current arrays. This discharges the cut
projection and geometric incidence premises in equation (10). -/
theorem region_incidence_cut_orbit (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (i : Fin k) :
    let marks := gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
      x.innerCuff x.outerCuff
    let next := dartMatePerm.trans
      (gm06RotationPermutation (gm06SplitRotationRows marks x.rotations)).symm
    let c := gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0
    (∀ v : ClosedCylinder, v ∈ G.V →
      (v ∈ closure (cylinderRegion k G i) ↔
        ∃ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
          dartVertex rep.par d = cylinderToSphere v ∧
          ∃ n : ℕ, gm06UncutDart (next^[n] c) = persistentDartLabel rep.label d)) ∧
    (∀ d : DrawingDart (cylinderSphereDrawing rep.cuffed),
      d.val.1 ⊆ cylinderToSphere '' closure (cylinderRegion k G i) ↔
        (∃ n : ℕ, gm06UncutDart (next^[n] c) = persistentDartLabel rep.label d) ∨
        ∃ n : ℕ, gm06UncutDart (next^[n] c) =
          gm06DartMate (persistentDartLabel rep.label d)) := by
  dsimp only
  have hproj := rep.cut_face_orbit_projection_iff hG i
  have hc : gm06UncutDart (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) =
      2 * (rep.tagged.length + i.val) + 1 := by
    simp [gm06UncutDart, gm06CutDart, Nat.add_div, Nat.add_mod]
    omega
  simp only [hc] at hproj
  obtain ⟨hV, hE⟩ := rep.region_incidence_old_orbit hk hG hno i
  constructor
  · intro v hv
    rw [hV v hv]
    exact exists_congr (fun d => and_congr_right (fun _ => hproj _))
  · intro d
    rw [hE, hproj, hproj]

end GM06CurrentDrawingRep
end GraphMinor.GM06
