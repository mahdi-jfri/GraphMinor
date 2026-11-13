module

public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5PolarAngularProjection
import GraphMinor.GM06.Section5PolarRay
import GraphMinor.GM06.Section5PolarEdgeAccess

/-!
# Moving a local side point to the polar rim

For VI (5.7), page 133, a point of the chosen local side away
from the linkage-and-cuff barrier gives a rim point of that side.
The atom containing its positive radial ray misses the barrier.
Inside the chart the side's frontier is contained in the barrier,
so connectedness keeps the ray in the same closed side all the way
to the rim. The rim point still misses the barrier.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A point of a closed local side off a nice barrier moves to a
rim point in that same side and still off the barrier. -/
theorem exists_polar_rim_point_of_closed_local_side
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ v Φ)
    {T B O : Set S} (hT : IsGammaNice Γ T) (hvT : v ∈ T)
    (hB : IsClosed B) (hΦO : range Φ ⊆ O) (hfr : frontier B ∩ O ⊆ T)
    {y : S} (hyΦ : y ∈ range Φ) (hyB : y ∈ B) (hyT : y ∉ T) :
    ∃ w : Circle, polarRimMap Φ w ∈ B ∧ polarRimMap Φ w ∉ T := by
  have hyv : y ≠ v := fun hh => hyT (hh.symm ▸ hvT)
  obtain ⟨q, _, _, hrepr⟩ := exists_polar_angular_projection hp
  obtain ⟨c, hc, hcy⟩ := hrepr y ⟨hyΦ, hyv⟩
  let w := q y
  obtain ⟨a, ha, hwa, hca⟩ := hp.ray (polarDiscPoint 1 w)
    (polarDiscPoint_one_ne_centre w) c hc
  rw [discScale_polarDiscPoint_one, hcy] at hca
  have haT : Disjoint a T := by
    apply disjoint_left.mpr
    intro z hza hzT
    exact hyT (nice_atom hT ha ⟨z, hza, hzT⟩ hca)
  have hrayT (t : I) (ht : 0 < t) : polarRayMap Φ w t ∉ T := by
    have hta := (polar_ray_mem_atom_iff hp ha (polarDiscPoint_one_ne_centre w) t ht).mp hwa
    rw [discScale_polarDiscPoint_one] at hta
    exact fun hh => disjoint_left.mp haT hta hh
  let A := polarRayMap Φ w '' Ioi (0 : I)
  have hA : IsPreconnected A := isPreconnected_Ioi.image (polarRayMap Φ w)
    (polarRayMap Φ w).continuous.continuousOn
  have hyA : y ∈ A := ⟨c, hc, hcy⟩
  have hAoff : Disjoint A (frontier B) := by
    apply disjoint_left.mpr
    rintro z ⟨t, ht, htz⟩ hzfr
    have hzO : z ∈ O := hΦO ⟨polarDiscPoint t w, htz⟩
    have hzT := hfr ⟨hzfr, hzO⟩
    exact hrayT t ht (htz.symm ▸ hzT)
  have hAB : A ⊆ B := by
    intro z hzA
    by_contra hzB
    have hcover : A ⊆ B ∪ (interior B)ᶜ := by
      intro x _
      by_cases hx : x ∈ B
      · exact Or.inl hx
      · exact Or.inr (fun hi => hx (interior_subset hi))
    obtain ⟨x, hxA, hxB, hxint⟩ := isPreconnected_closed_iff.mp hA _ _ hB
      isOpen_interior.isClosed_compl hcover ⟨y, hyA, hyB⟩
      ⟨z, hzA, fun hi => hzB (interior_subset hi)⟩
    have hxfr : x ∈ frontier B := by rw [frontier, hB.closure_eq]; exact ⟨hxB, hxint⟩
    exact disjoint_left.mp hAoff hxA hxfr
  exact ⟨w, hAB ⟨1, zero_lt_one, rfl⟩, hrayT 1 zero_lt_one⟩

end GraphMinor.GM06
