module

public import GraphMinor.GM06.Alg57SubdrawingRegions
public import GraphMinor.GM06.Alg57CurrentFaceRotation
public import GraphMinor.GM06.Alg57FilterCornerLabels

/-!
# Numeric corner labels in the comparison subdrawing

In the local side proof of VI (5.7), page 133, send each full-drawing
corner to its containing region of the linkage-and-cuff subdrawing.
Deleted ends merge adjacent labels. Filtering a row therefore skips
those ends without changing the predecessor's region. The resulting
numeric labels are constant on the comparison face orbits.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- Inverse drawing rotation commutes with permanent numeric labels
whenever the forward rotation does. -/
theorem persistentDartLabel_rot_symm {Γ : Drawing (OnePoint EuclideanPlane)}
    (label : Γ.E ↪ ℕ) (rows : List (List ℕ)) (R : DartRotation (DrawingDart Γ))
    (hrot : ∀ d, persistentDartLabel label (R.rot d) =
      gm06RotationPermutation rows (persistentDartLabel label d)) (d : DrawingDart Γ) :
    persistentDartLabel label (R.rot.symm d) =
      (gm06RotationPermutation rows).symm (persistentDartLabel label d) := by
  apply (gm06RotationPermutation rows).injective
  rw [← hrot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Sending actual corners to their containing comparison regions
produces numeric labels that skip every removed row end and remain
constant along every retained comparison face orbit. -/
theorem exists_numeric_subdrawing_corner_labels
    {Γ H : Drawing (OnePoint EuclideanPlane)} (hH : H.IsSubdrawing Γ)
    (label : Γ.E ↪ ℕ) (rows : List (List ℕ)) (hn : rows.flatten.Nodup)
    (hcover : ∀ r : ℕ, r ∈ rows.flatten ↔ ∃ d : DrawingDart Γ, persistentDartLabel label d = r)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (R : DartRotation (DrawingDart Γ)) (hR : IsDrawingRotation Γ γ R)
    (hrot : ∀ d, persistentDartLabel label (R.rot d) =
      gm06RotationPermutation rows (persistentDartLabel label d))
    (ρ : DrawingDart Γ → Set (OnePoint EuclideanPlane)) (hρ : IsCornerLabel Γ γ R ρ)
    (keep : ℕ → Bool)
    (hkeep : ∀ d : DrawingDart Γ, keep (persistentDartLabel label d) = true ↔ d.val.1 ∈ H.E) :
    ∃ g : ℕ → Option H.R,
      (∀ d : DrawingDart Γ, g (persistentDartLabel label d) =
        some (regionInSubdrawing hH ⟨ρ d, hρ.region d⟩)) ∧
      (∀ row ∈ rows, ∀ r ∈ row, keep r = false → g (row.formPerm.symm r) = g r) ∧
      ∀ d : DrawingDart Γ, keep (persistentDartLabel label d) = true →
        g ((dartMatePerm.trans (gm06RotationPermutation (rows.map (List.filter keep))).symm)
            (persistentDartLabel label d)) = g (persistentDartLabel label d) := by
  classical
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) :=
    IsClosedSurface.locallyConnectedSpace
      (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  let values := fun d : DrawingDart Γ => some (regionInSubdrawing hH ⟨ρ d, hρ.region d⟩)
  let g : ℕ → Option H.R := Function.extend (persistentDartLabel label) values (fun _ => none)
  have hg (d : DrawingDart Γ) : g (persistentDartLabel label d) = values d :=
    (persistentDartLabel_injective label).extend_apply _ _ d
  have hskip : ∀ row ∈ rows, ∀ r ∈ row, keep r = false → g (row.formPerm.symm r) = g r := by
    intro row hr r hrr hkr
    obtain ⟨d, hd⟩ := (hcover r).mp (List.mem_flatten.mpr ⟨row, hr, hrr⟩)
    have heH : d.val.1 ∉ H.E := by
      intro he
      have hk := (hkeep d).mpr he
      rw [hd, hkr] at hk
      cases hk
    have hword := persistentDartLabel_rot_symm label rows R hrot d
    rw [hd, rotationPermutation_symm_apply_row rows hn row hr r hrr] at hword
    rw [← hword, ← hd, hg, hg]
    exact congrArg some (hρ.regionInSubdrawing_rot_symm hH hR d heH)
  refine ⟨g, hg, hskip, fun d hkd => ?_⟩
  have hrev : R.rev = dartFlip Γ := Equiv.ext hR.rev_eq
  have hdrev : persistentDartLabel label (R.rev d) = gm06DartMate (persistentDartLabel label d) := by
    rw [hrev, persistentDartLabel_flip]
  have hm := (hcover _).mpr ⟨R.rev d, rfl⟩
  obtain ⟨row, hr, hmr⟩ := List.mem_flatten.mp hm
  have hkm : keep (persistentDartLabel label (R.rev d)) = true := by
    apply (hkeep _).mpr
    simpa only [hrev, dartFlip_apply] using (hkeep d).mp hkd
  have hrf : row.filter keep ∈ rows.map (List.filter keep) := List.mem_map.mpr ⟨row, hr, rfl⟩
  have hmrf : persistentDartLabel label (R.rev d) ∈ row.filter keep :=
    List.mem_filter.mpr ⟨hmr, hkm⟩
  have hnf : (rows.map (List.filter keep)).flatten.Nodup := by
    rw [← List.filter_flatten]
    exact hn.filter keep
  simp only [Equiv.trans_apply, dartMatePerm_apply, ← hdrev]
  rw [rotationPermutation_symm_apply_row _ hnf _ hrf _ hmrf,
    formPerm_filter_symm_label row ((List.nodup_flatten.mp hn).1 row hr) keep g
      (hskip row hr) hmr hkm,
    ← rotationPermutation_symm_apply_row rows hn row hr _ hmr,
    ← persistentDartLabel_rot_symm label rows R hrot]
  change g (persistentDartLabel label (R.face d)) = g (persistentDartLabel label d)
  rw [hg, hg]
  change some (regionInSubdrawing hH ⟨ρ (R.face d), hρ.region _⟩) =
    some (regionInSubdrawing hH ⟨ρ d, hρ.region _⟩)
  apply congrArg some
  apply congrArg (regionInSubdrawing hH)
  exact Subtype.ext (hρ.coherent d)

end GraphMinor.GM06
