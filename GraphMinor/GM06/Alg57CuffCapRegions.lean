module

public import GraphMinor.GM06.Alg57CuffFace
import GraphMinor.GM06.Alg57RegionIncidence
import GraphMinor.GM06.Section5Red

/-!
# The regions on the two sides of a cuff circle

The cuff-adjacency step in the cut construction of VI (5.7),
page 133, uses the discs attached to the two cuffs. A region which
misses a complete round circle stays on one side of that circle.
Its closure stays in the corresponding closed side. The capped
cylinder drawing contains the complete circles of radii one half
and one. These observations identify the cap side without a
connectedness assumption on the whole drawing.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- A region of a sphere drawing containing a round circle stays
entirely on one side of that circle. The exterior includes infinity. -/
theorem region_side_of_round_circle {Γ : Drawing (OnePoint EuclideanPlane)}
    (radius : ℝ) (hcircle : ∀ z : ℂ, ‖z‖ = radius → toSph z ∈ Γ.U)
    {r : Set (OnePoint EuclideanPlane)} (hr : r ∈ Γ.R) :
    r ⊆ toSph '' ball (0 : ℂ) radius ∨
      r ⊆ (toSph '' closedBall (0 : ℂ) radius)ᶜ := by
  have hi : IsOpen (toSph '' ball (0 : ℂ) radius) :=
    isOpenEmbedding_toSph.isOpenMap _ isOpen_ball
  have ho : IsOpen (toSph '' closedBall (0 : ℂ) radius)ᶜ :=
    ((isCompact_closedBall (0 : ℂ) radius).image continuous_toSph).isClosed.isOpen_compl
  have hd : Disjoint (toSph '' ball (0 : ℂ) radius)
      (toSph '' closedBall (0 : ℂ) radius)ᶜ := disjoint_left.mpr (by
    rintro p ⟨z, hz, rfl⟩ hp
    exact hp (mem_image_of_mem _ (ball_subset_closedBall hz)))
  apply (region_isPreconnected hr).subset_or_subset hi ho hd
  intro p hp
  by_cases hpi : p ∈ toSph '' ball (0 : ℂ) radius
  · exact Or.inl hpi
  · right
    rintro ⟨z, hz, rfl⟩
    have hle : ‖z‖ ≤ radius := mem_closedBall_zero_iff.mp hz
    have hge : radius ≤ ‖z‖ := le_of_not_gt (fun hlt =>
      hpi (mem_image_of_mem _ (mem_ball_zero_iff.mpr hlt)))
    exact region_subset hr hp (hcircle z (hle.antisymm hge))

/-- A region meeting the open inner disc has closure in its closed
inner disc, when the boundary circle is in the drawing. -/
theorem closure_region_subset_inner_round_disc {Γ : Drawing (OnePoint EuclideanPlane)}
    (radius : ℝ) (hcircle : ∀ z : ℂ, ‖z‖ = radius → toSph z ∈ Γ.U)
    {r : Set (OnePoint EuclideanPlane)} (hr : r ∈ Γ.R)
    {z : ℂ} (hz : ‖z‖ < radius) (hzr : toSph z ∈ r) :
    closure r ⊆ toSph '' closedBall (0 : ℂ) radius := by
  have hsub : r ⊆ toSph '' ball (0 : ℂ) radius := by
    rcases region_side_of_round_circle radius hcircle hr with h | h
    · exact h
    · exact False.elim (h hzr (mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hz.le)))
  apply closure_minimal (hsub.trans (image_mono ball_subset_closedBall))
  exact ((isCompact_closedBall (0 : ℂ) radius).image continuous_toSph).isClosed

/-- A region meeting the exterior of a round disc has closure
outside its open inner disc. -/
theorem closure_region_subset_outer_round_disc {Γ : Drawing (OnePoint EuclideanPlane)}
    (radius : ℝ) (hcircle : ∀ z : ℂ, ‖z‖ = radius → toSph z ∈ Γ.U)
    {r : Set (OnePoint EuclideanPlane)} (hr : r ∈ Γ.R)
    {z : ℂ} (hz : radius < ‖z‖) (hzr : toSph z ∈ r) :
    closure r ⊆ (toSph '' ball (0 : ℂ) radius)ᶜ := by
  have hsub : r ⊆ (toSph '' closedBall (0 : ℂ) radius)ᶜ := by
    rcases region_side_of_round_circle radius hcircle hr with h | h
    · obtain ⟨w, hw, hweq⟩ := h hzr
      have hwz := toSph_injective hweq
      subst w
      exact False.elim ((not_lt_of_ge hz.le) (mem_ball_zero_iff.mp hw))
    · exact h
  apply closure_minimal
  · intro p hp hpi
    exact hsub hp (image_mono ball_subset_closedBall hpi)
  · exact (isOpenEmbedding_toSph.isOpenMap _ isOpen_ball).isClosed_compl

/-- A capped cylinder drawing contains each point of either
boundary circle, in the plane's norm coordinates. -/
theorem round_cuff_mem_cylinderSphereDrawing {G F : Drawing ClosedCylinder}
    (hFU : F.U = G.U ∪ bd ClosedCylinder) {radius : ℝ}
    (hradius : radius = 1 / 2 ∨ radius = 1) (z : ℂ) (hz : ‖z‖ = radius) :
    toSph z ∈ (cylinderSphereDrawing F).U := by
  have hplane : complexPlane z ∈ range cylToPlane := by
    rw [range_cylToPlane]
    change 1 / 2 ≤ ‖complexPlane z‖ ∧ ‖complexPlane z‖ ≤ 1
    rw [LinearIsometryEquiv.norm_map, hz]
    rcases hradius with rfl | rfl <;> constructor <;> norm_num
  obtain ⟨p, hp⟩ := hplane
  have hnorm : p.val.1 / 2 = radius := by
    have hh := congrArg norm hp
    rw [norm_cylToPlane, LinearIsometryEquiv.norm_map, hz] at hh
    exact hh
  have hpbd : p ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    rcases hradius with hr | hr
    · left
      change p.val.1 = 1
      linarith
    · right
      change p.val.1 = 2
      linarith
  rw [cylinderSphereDrawing_U, hFU]
  refine ⟨p, Or.inr hpbd, ?_⟩
  change (cylToPlane p : OnePoint EuclideanPlane) =
    (complexPlane z : OnePoint EuclideanPlane)
  exact congrArg ((↑) : EuclideanPlane → OnePoint EuclideanPlane) hp

/-- The corner after a dart contains the next edge in the vertex
rotation as well as its own edge. This follows from face coherence
applied to the reverse of that next dart. -/
theorem IsCornerLabel.next_edge_subset {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart Γ)} {ρ : DrawingDart Γ → Set (OnePoint EuclideanPlane)}
    (hρ : IsCornerLabel Γ γ R ρ) (hR : IsDrawingRotation Γ γ R) (d : DrawingDart Γ) :
    (R.rot d).val.1 ⊆ closure (ρ d) := by
  have hface : R.face (R.rev (R.rot d)) = d := by
    rw [DartRotation.face_apply, R.rev_rev, Equiv.symm_apply_apply]
  have hh := hρ.edge (R.rev (R.rot d))
  have hlabel := hρ.coherent (R.rev (R.rot d))
  rw [hface] at hlabel
  rw [← hlabel] at hh
  simpa only [hR.rev_eq, dartFlip_apply] using hh

end GraphMinor.GM06
