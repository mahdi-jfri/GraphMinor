module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverSides

/-!
# Neighbourhoods of the existing attachment visits

For the attachment count in VI (5.5), page 130, a sufficiently
small neighbourhood of a vertex is visited only at parameters
whose lifted angles are close to an existing visit to that vertex.
The parameters with this closeness form an open set containing
the whole vertex fibre. The image of its compact complement is
closed and misses the vertex, giving the required neighbourhood.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface Metric

/-- A small spatial neighbourhood of an attachment confines its
visiting parameters to angular neighbourhoods of the existing visits. -/
theorem exists_attachment_neighbourhood_near_old_lift_visits
    (f : Curve ClosedCylinder) (A : C(unitInterval, CylinderCover))
    {s : ClosedCylinder} {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set ClosedCylinder, IsOpen U ∧ s ∈ U ∧
      ∀ t, f t ∈ U → ∃ u : unitInterval, f u = s ∧ |(A t).2 - (A u).2| < ε := by
  let T : Set unitInterval := ⋃ u : unitInterval, ⋃ (_ : f u = s),
    (fun t => (A t).2) ⁻¹' ball (A u).2 ε
  have hTo : IsOpen T := isOpen_iUnion (fun _ => isOpen_iUnion
    (fun _ => isOpen_ball.preimage (continuous_snd.comp A.continuous)))
  have hcontains (t) (ht : f t = s) : t ∈ T :=
    mem_iUnion₂.mpr ⟨t, ht, mem_ball_self hε⟩
  let U := (f '' Tᶜ)ᶜ
  have hUo : IsOpen U := (hTo.isClosed_compl.isCompact.image f.continuous).isClosed.isOpen_compl
  have hsU : s ∈ U := by
    rintro ⟨t, ht, he⟩
    exact ht (hcontains t he)
  refine ⟨U, hUo, hsU, ?_⟩
  intro t ht
  have htT : t ∈ T := by
    by_contra hnot
    exact ht (mem_image_of_mem f hnot)
  obtain ⟨u, hu, hclose⟩ := mem_iUnion₂.mp htT
  exact ⟨u, hu, by simpa only [mem_preimage, mem_ball, Real.dist_eq] using hclose⟩

end GraphMinor.GM06
