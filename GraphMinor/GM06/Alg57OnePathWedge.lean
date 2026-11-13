module

public import GraphMinor.GM06.Alg57PathChartExists
public import GraphMinor.GM06.Alg57OnePathSides
public import GraphMinor.GM06.Alg57RegionIncidence
import GraphMinor.GM06.Section5CappedInitialPath

/-!
# The left side of the one path

For `k = 1` we follow the left side of `P₁` on the sphere. The path is the arc `spherePath L`, the
image of `L.curve 0` on the sphere, and its point set is a nice set of the capped drawing. So at
each inner point there are path charts as small as we like (`exists_isPathChart_in`), and near each
inner point the side does not change off the path (`sphere_sideDich`). By `exists_wedgeQ_path`
one proposition decides whether the left wedges of all path charts are on side one
(`exists_left_side`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- The one path on the sphere, as a map of the real line (constant outside `[0, 1]`). -/
noncomputable def spherePath (L : CylinderLinkage 1 G) (t : ℝ) : OnePoint EuclideanPlane :=
  cylinderToSphere (L.curve 0 (projIcc 0 1 zero_le_one t))

section Path

variable (L : CylinderLinkage 1 G)

theorem continuous_spherePath : Continuous (spherePath L) :=
  continuous_cylinderToSphere.comp ((L.curve 0).continuous.comp continuous_projIcc)

theorem spherePath_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    spherePath L t = cylinderToSphere (L.curve 0 ⟨t, ht⟩) := by
  simp only [spherePath, projIcc_of_mem _ ht]

theorem injOn_spherePath : InjOn (spherePath L) (Icc 0 1) := by
  intro s hs t ht h
  rw [spherePath_of_mem L hs, spherePath_of_mem L ht] at h
  have := (L.curve_parametrizes 0).1 (injective_cylinderToSphere h)
  exact congrArg Subtype.val this

theorem image_spherePath :
    spherePath L '' Icc 0 1 = cylinderToSphere '' (L.pathDrawing 0).U := by
  rw [← (L.curve_parametrizes 0).2.1]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨_, mem_range_self _, (spherePath_of_mem L ht).symm⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, t.2, spherePath_of_mem L t.2⟩

theorem spherePath_subset_U {H : Drawing ClosedCylinder} (hGH : G.IsSubdrawing H) :
    cylinderToSphere '' (L.pathDrawing 0).U ⊆ (cylinderSphereDrawing H).U := by
  rw [cylinderSphereDrawing_U]
  exact image_mono ((L.isSubdrawing 0).2.trans hGH.U_subset)

theorem isGammaNice_spherePath {H : Drawing ClosedCylinder} (hGH : G.IsSubdrawing H) :
    IsGammaNice (cylinderSphereDrawing H) (cylinderToSphere '' (L.pathDrawing 0).U) := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) :=
    IsClosedSurface.locallyConnectedSpace hS
  have hP := cylinderSphereDrawing_isSubdrawing ((L.isSubdrawing 0).1.trans hGH)
  rw [← cylinderSphereDrawing_U]
  exact isGammaNice_of_frontier hP subset_rfl (frontier_subset_closure.trans
    (by rw [(cylinderSphereDrawing (L.pathDrawing 0)).isClosed_U.closure_eq]))

end Path

section Side

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
  {U₁ U₂ : Set CylinderCover} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
  (h₁ : ∀ t, coverLift L hG 1 t ∈ U₁) (h₂ : ∀ t, coverLift L hG 2 t ∈ U₂)
  {H : Drawing ClosedCylinder} (hGH : G.IsSubdrawing H)
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing H))}
  (hγ : EdgePar (cylinderSphereDrawing H) γ) (hccw : IsCcwRotation (cylinderSphereDrawing H) γ R)
  (hV : ∀ v ∈ (cylinderSphereDrawing H).V, ∃ a : DrawingDart (cylinderSphereDrawing H),
    dartVertex γ a = v)

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hγ hccw hV in
/-- **Path charts along `P₁` inside the sets where the side does not change.** -/
theorem exists_side_pathChart {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψ : C(ClosedUnitDisc, EuclideanPlane))
      (F B : Circle), IsPathChart (cylinderSphereDrawing H) (cylinderToSphere '' (L.pathDrawing 0).U)
        (spherePath L) t Φ Ψ F B ∧
      SideDich (cylinderToSphere '' (L.pathDrawing 0).U) (sphereSide D U₁) (range Φ) := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  obtain ⟨N, hN, hxN, hdich⟩ := sphere_sideDich L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂
    (t := ⟨t, ht'⟩) (fun h => ht.1.ne' (congrArg Subtype.val h))
    (fun h => ht.2.ne (congrArg Subtype.val h))
  rw [← spherePath_of_mem L ht'] at hxN
  obtain ⟨Φ, Ψ, F, B, hc, hsub⟩ := exists_isPathChart_in hS
    (infty_notMem_cylinderSphereDrawing_U H) hγ hccw hV (isGammaNice_spherePath L hGH)
    (spherePath_subset_U L hGH) (continuous_spherePath L) (injOn_spherePath L)
    (image_spherePath L).subset (image_spherePath L).symm.subset ht hN hxN
  exact ⟨Φ, Ψ, F, B, hc, hdich.mono hsub⟩

end Side

end GraphMinor.GM06
