module

public import GraphMinor.GM06.Alg57CurrentRows
public import GraphMinor.GM06.Alg57PersistentRowRotation
public import GraphMinor.GM06.Alg57CutEquations
import GraphMinor.GM06.Alg57RegionIncidence

/-!
# Face successors in current permanent rows

For VI (5.7), page 133, the positive rows determine a counterclockwise
rotation of the cuffed drawing. Its face successor agrees with the
numeric face successor on permanent directed labels. Thus the numeric
orbit test reads exactly equality of drawing faces, even when deleted
edges leave gaps among the labels.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- Reversing a drawing dart reverses its permanent directed label. -/
theorem persistentDartLabel_flip {Γ : Drawing (OnePoint EuclideanPlane)}
    (label : Γ.E ↪ ℕ) (d : DrawingDart Γ) :
    persistentDartLabel label (dartFlip Γ d) = gm06DartMate (persistentDartLabel label d) := by
  rcases d with ⟨⟨e, b⟩, he⟩
  cases b <;> simp [persistentDartLabel, dartFlip, gm06DartMate]

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- The counterclockwise drawing rotation agrees with the global
permutation of the current permanent rows. -/
theorem exists_ccwRotation :
    ∃ R : DartRotation (DrawingDart (cylinderSphereDrawing rep.cuffed)),
      IsDrawingRotation (cylinderSphereDrawing rep.cuffed) rep.par R ∧
      IsCcwRotation (cylinderSphereDrawing rep.cuffed) rep.par R ∧
      R.rev = dartFlip (cylinderSphereDrawing rep.cuffed) ∧
      ∀ d, persistentDartLabel rep.label (R.rot d) =
        gm06RotationPermutation x.rotations (persistentDartLabel rep.label d) := by
  classical
  let A := {a : Fin x.vertexCount // a ∈ rep.live}
  let vertex : A → OnePoint EuclideanPlane := fun a => cylinderToSphere (rep.vertex a.val)
  have hinj : Function.Injective vertex := by
    intro a b hab
    apply Subtype.ext
    exact rep.vertex_inj a.property b.property (injective_cylinderToSphere hab)
  let rows : OnePoint EuclideanPlane → List ℕ :=
    Function.extend vertex (fun a => x.rotations.getD a.val.val []) (fun _ => [])
  have hrows_at (a : Fin x.vertexCount) (ha : a ∈ rep.live) :
      rows (cylinderToSphere (rep.vertex a)) = x.rotations.getD a.val [] :=
    hinj.extend_apply _ _ ⟨a, ha⟩
  have hrows : ∀ v ∈ (cylinderSphereDrawing rep.cuffed).V,
      GM06PersistentRotationRowRep rep.label rep.par v (rows v) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := rep.sphere_vertex_cover hv
    rw [hrows_at a ha]
    exact rep.rows a ha
  have hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ (cylinderSphereDrawing rep.cuffed).V :=
    fun h => infty_notMem_cylinderSphereDrawing_U rep.cuffed
      ((cylinderSphereDrawing rep.cuffed).V_subset_U h)
  obtain ⟨R, hR, hccw, hrev, hrot⟩ :=
    exists_ccwRotation_of_persistent_rows rep.edgePar hinf rows hrows
  refine ⟨R, hR, hccw, hrev, fun d => ?_⟩
  obtain ⟨a, ha, hv⟩ := rep.sphere_vertex_cover (dartVertex_mem rep.edgePar d)
  have hd : persistentDartLabel rep.label d ∈ x.rotations.getD a.val [] :=
    persistentDartLabel_mem_row (rep.rows a ha) hv.symm
  rw [hrot, ← hv, hrows_at a ha]
  have hi : a.val < x.rotations.length := rep.rows_length.symm ▸ a.isLt
  exact (gm06RotationPermutation_apply_row x.rotations rep.rows_flatten_nodup
    (x.rotations.getD a.val []) (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
    _ hd).symm

end GM06CurrentDrawingRep

/-- Numeric and geometric face successors commute under permanent
labels whenever the row rotation does. -/
theorem persistentDartLabel_face {Γ : Drawing (OnePoint EuclideanPlane)}
    (label : Γ.E ↪ ℕ) (rows : List (List ℕ)) (R : DartRotation (DrawingDart Γ))
    (hrev : R.rev = dartFlip Γ)
    (hrot : ∀ d, persistentDartLabel label (R.rot d) =
      gm06RotationPermutation rows (persistentDartLabel label d)) (d : DrawingDart Γ) :
    persistentDartLabel label (R.face d) =
      (dartMatePerm.trans (gm06RotationPermutation rows).symm) (persistentDartLabel label d) := by
  rw [DartRotation.face_apply]
  apply (gm06RotationPermutation rows).injective
  rw [← hrot, Equiv.apply_symm_apply]
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply, hrev,
    persistentDartLabel_flip, dartMatePerm_apply]

/-- Iterating either face successor gives the same permanent word. -/
theorem persistentDartLabel_face_iterate {Γ : Drawing (OnePoint EuclideanPlane)}
    (label : Γ.E ↪ ℕ) (rows : List (List ℕ)) (R : DartRotation (DrawingDart Γ))
    (hrev : R.rev = dartFlip Γ)
    (hrot : ∀ d, persistentDartLabel label (R.rot d) =
      gm06RotationPermutation rows (persistentDartLabel label d)) (n : ℕ) (d : DrawingDart Γ) :
    persistentDartLabel label (R.face^[n] d) =
      (dartMatePerm.trans (gm06RotationPermutation rows).symm)^[n] (persistentDartLabel label d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', persistentDartLabel_face label rows R hrev hrot,
      ih, Function.iterate_succ_apply']

/-- Equality of geometric faces is exactly the numeric face-orbit
test on permanent labels. -/
theorem faceOf_eq_iff_permanent_orbit {Γ : Drawing (OnePoint EuclideanPlane)}
    (label : Γ.E ↪ ℕ) (rows : List (List ℕ)) (R : DartRotation (DrawingDart Γ))
    (hrev : R.rev = dartFlip Γ)
    (hrot : ∀ d, persistentDartLabel label (R.rot d) =
      gm06RotationPermutation rows (persistentDartLabel label d)) (c d : DrawingDart Γ) :
    R.faceOf d = R.faceOf c ↔
      ∃ n : ℕ, (dartMatePerm.trans (gm06RotationPermutation rows).symm)^[n]
        (persistentDartLabel label c) = persistentDartLabel label d := by
  constructor
  · intro h
    have hcycle : R.face.SameCycle c d := Quotient.exact h.symm
    obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
    refine ⟨n, ?_⟩
    rw [← persistentDartLabel_face_iterate label rows R hrev hrot]
    simpa only [Equiv.Perm.coe_pow] using congrArg (persistentDartLabel label) hn
  · rintro ⟨n, hn⟩
    rw [← persistentDartLabel_face_iterate label rows R hrev hrot] at hn
    have heq := persistentDartLabel_injective label hn
    rw [← heq]
    clear hn heq
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', R.faceOf_face, ih]

end GraphMinor.GM06
