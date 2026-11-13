module

public import GraphMinor.GM06.Alg57PersistentRowRotation
public import GraphMinor.Compute.GM06RotationPredecessors

/-!
# Drawing rotations from rows in a permanent vertex space

The row interpretation in VI (5.7), page 133, can have unused slots.
Extend rows from the injectively labelled live vertices to the whole
sphere. The positive-row construction then gives a counterclockwise
rotation. At every actual dart the global list permutation agrees
with the form permutation of its unique row.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- Positive rows indexed by an injective live vertex labelling give
an actual counterclockwise drawing rotation and its global numeric
successor. Unused slots need no vertex interpretation. -/
theorem exists_ccwRotation_of_indexed_rows {n : ℕ} {Γ : Drawing (OnePoint EuclideanPlane)}
    (label : Γ.E ↪ ℕ) {γ : Set (OnePoint EuclideanPlane) → unitInterval → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.V)
    (vertex : Fin n → OnePoint EuclideanPlane) (live : Finset (Fin n))
    (hinj : InjOn vertex (↑live : Set (Fin n)))
    (hcover : ∀ v ∈ Γ.V, ∃ a ∈ live, vertex a = v)
    (rows : List (List ℕ)) (hlen : rows.length = n) (hnd : rows.flatten.Nodup)
    (hrows : ∀ a ∈ live, GM06PersistentRotationRowRep label γ (vertex a) (rows.getD a.val [])) :
    ∃ R : DartRotation (DrawingDart Γ), IsDrawingRotation Γ γ R ∧ IsCcwRotation Γ γ R ∧
      R.rev = dartFlip Γ ∧
      ∀ d, persistentDartLabel label (R.rot d) =
        gm06RotationPermutation rows (persistentDartLabel label d) := by
  classical
  let A := {a : Fin n // a ∈ live}
  let point : A → OnePoint EuclideanPlane := fun a => vertex a.val
  have hi : Function.Injective point := by
    intro a b hab
    exact Subtype.ext (hinj a.property b.property hab)
  let rowAt : OnePoint EuclideanPlane → List ℕ :=
    Function.extend point (fun a => rows.getD a.val.val []) (fun _ => [])
  have hat (a : Fin n) (ha : a ∈ live) : rowAt (vertex a) = rows.getD a.val [] :=
    hi.extend_apply _ _ ⟨a, ha⟩
  have hrowAt : ∀ v ∈ Γ.V, GM06PersistentRotationRowRep label γ v (rowAt v) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hcover v hv
    rw [hat a ha]
    exact hrows a ha
  obtain ⟨R, hR, hccw, hrev, hrot⟩ :=
    exists_ccwRotation_of_persistent_rows hγ hinf rowAt hrowAt
  refine ⟨R, hR, hccw, hrev, fun d => ?_⟩
  obtain ⟨a, ha, hv⟩ := hcover _ (dartVertex_mem hγ d)
  have hd : persistentDartLabel label d ∈ rows.getD a.val [] :=
    persistentDartLabel_mem_row (hrows a ha) hv.symm
  rw [hrot, ← hv, hat a ha]
  have hai : a.val < rows.length := hlen.symm ▸ a.isLt
  exact (gm06RotationPermutation_apply_row rows hnd (rows.getD a.val [])
    (by rw [List.getD_eq_getElem _ _ hai]; exact List.getElem_mem hai) _ hd).symm

end GraphMinor.GM06
