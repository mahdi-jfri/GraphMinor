module

public import GraphMinor.GM06.Section5DiscFrontierPaths
import GraphMinor.GM06.Section5RegionSectorEdge
import GraphMinor.Surface.DiscNbhd
import GraphMinor.Surface.Wedge
import GraphMinor.GM11.PerimeterPull

/-!
# Two boundary edges determine the inside corner of a disc

At a vertex whose punctured drawing is connected, corners belong
to distinct regions. If a region is incident with the two boundary
edges at that vertex, no third incident edge can lie inside the
disc. Embed the disc in a sphere and apply the proved sector
comparison there. This is the local initial-edge argument for the
one-path cut drawing in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u

/-- In a disc drawing with connected puncture, two incident boundary
edges of a region exclude every third incident edge at the same vertex. -/
theorem eq_or_eq_of_two_boundary_edges_incident_disc_region
    {S : Type u} [TopologicalSpace S] (hDisc : IsClosedDiscSpace S)
    {F : Drawing S} (hbd : bd S ⊆ F.U) {s : S} (hs : s ∈ F.V)
    (hpun : IsPreconnected (F.U \ {s})) {r : Set S} (hr : r ∈ F.R)
    (hsr : s ∈ closure r) {a b : Set S} (ha : a ∈ F.E) (hb : b ∈ F.E)
    (hab : a ≠ b) (hsa : s ∈ closure a) (hsb : s ∈ closure b)
    (har : a ⊆ closure r) (hbr : b ⊆ closure r)
    (haBd : closure a ⊆ bd S) (hbBd : closure b ⊆ bd S)
    {e : Set S} (he : e ∈ F.E) (hse : s ∈ closure e) : e = a ∨ e = b := by
  let : CompactSpace S := compactSpace_of_isClosedDiscSpace hDisc
  let : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  let : Nonempty S := ⟨s⟩
  have hS : IsSurface S := ⟨inferInstance, inferInstance,
    fun p => isManifoldPoint_of_disc hDisc.isClosedDisc_univ Filter.univ_mem⟩
  obtain ⟨j, hj, hopen, _⟩ := exists_closedDisc_sphere_embedding hDisc
  let H := GM07.embedDrawing hj F
  let R := j '' r
  have hR : R ∈ H.R := image_region_of_boundary_subset hS hj hopen hbd hr
  have hpunH : IsPreconnected (H.U \ {j s}) := by
    rw [GM07.embedDrawing_U,
      show ({j s} : Set (OnePoint EuclideanPlane)) = j '' {s} from (image_singleton : j '' {s} = {j s}).symm,
      ← image_sdiff hj.injective]
    exact hpun.image j hj.continuous.continuousOn
  obtain ⟨hD, hDb⟩ := isClosedDisc_image_injOn hDisc.isClosedDisc_univ isCompact_univ
    hj.continuous.continuousOn hj.injective.injOn
  rw [image_univ] at hD hDb
  rw [discBd_univ] at hDb
  have hedge (d : Set S) (hd : d ∈ F.E) : j '' d ∈ H.E := by
    rw [GM07.embedDrawing_E]
    exact mem_image_of_mem _ hd
  have hclos (d : Set S) : closure (j '' d) = j '' closure d := hj.closure_image_eq d
  have hinc (d : Set S) (hd : s ∈ closure d) : j s ∈ closure (j '' d) := by
    rw [hclos]
    exact mem_image_of_mem j hd
  have hbdimage (d : Set S) (hd : closure d ⊆ bd S) :
      closure (j '' d) ⊆ discBd (range j) := by
    rw [hclos, hDb]
    exact image_mono hd
  have harH : j '' a ⊆ closure R := by
    change j '' a ⊆ closure (j '' r)
    rw [hclos]
    exact image_mono har
  have hbrH : j '' b ⊆ closure R := by
    change j '' b ⊆ closure (j '' r)
    rw [hclos]
    exact image_mono hbr
  have hsH : j s ∈ H.V := by rw [GM07.embedDrawing_V]; exact mem_image_of_mem j hs
  have hsR : j s ∈ closure R := hinc r hsr
  have hinj : Function.Injective (image j) := hj.injective.image_injective
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hSphere := IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hSphere.2
  by_contra hn
  have hea : e ≠ a := fun h => hn (Or.inl h)
  have heb : e ≠ b := fun h => hn (Or.inr h)
  have hnot := not_subset_disc_of_two_incident_boundary_edges hSphere.1 hsph hsH hpunH hR hsR
    hD (image_subset_range _ _) (hedge a ha) (hedge b hb) (fun h => hab (hinj h))
    (hinc a hsa) (hinc b hsb) harH hbrH (hbdimage a haBd) (hbdimage b hbBd)
    (hedge e he) (fun h => hea (hinj h)) (fun h => heb (hinj h)) (hinc e hse)
  exact hnot (image_subset_range _ _)

end GraphMinor.GM06
