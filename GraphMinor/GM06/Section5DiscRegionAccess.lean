module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5DiscFrontierPaths
import GraphMinor.GM06.Section5DiscSphereEmbedding
import GraphMinor.GM06.RegionLocal
import GraphMinor.GM11.Theorem75
import GraphMinor.GM11.RadialChord
import GraphMinor.GM11.DrawingOps
import GraphMinor.GM11.Walks
import GraphMinor.Surface.DiscNbhd

/-!
# Access to an incident vertex in a cut disc

For the side conditions in VI (5.5), page 131, the approach curve
can be chosen in the cut disc. Embed the disc in the sphere and
apply vertex access there. Pull the curve back and join it to the
specified region point. The chord lemma makes the resulting curve
injective, with all points before its endpoint in the region.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u

/-- Approach an incident drawing vertex from a specified point of
a cut-disc region. This allows the side of the approach in VI (5.5)
to be fixed before projection to the cylinder. -/
theorem exists_curve_from_disc_region_point_to_vertex
    {S : Type u} [TopologicalSpace S] (hDisc : IsClosedDiscSpace S)
    {F : Drawing S} (hbd : bd S ⊆ F.U) {r : Set S} (hr : r ∈ F.R)
    {x v : S} (hx : x ∈ r) (hv : v ∈ F.V) (hvr : v ∈ closure r) :
    ∃ f : Curve S, Function.Injective f ∧ f 0 = x ∧ f 1 = v ∧
      ∀ t : unitInterval, t < 1 → f t ∈ r := by
  classical
  let : CompactSpace S := compactSpace_of_isClosedDiscSpace hDisc
  let : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  let : Nonempty S := ⟨x⟩
  let : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hDisc
  have hS : IsSurface S := ⟨inferInstance, inferInstance,
    fun p => isManifoldPoint_of_disc hDisc.isClosedDisc_univ Filter.univ_mem⟩
  obtain ⟨j, hj, hopen, _⟩ := exists_closedDisc_sphere_embedding hDisc
  let H := GM07.embedDrawing hj F
  have hJv : j v ∈ H.V := by
    rw [GM07.embedDrawing_V]
    exact mem_image_of_mem j hv
  have hJr : j '' r ∈ H.R := image_region_of_boundary_subset hS hj hopen hbd hr
  have hvcl : j v ∈ closure (j '' r) := by
    rw [hj.closure_image_eq]
    exact mem_image_of_mem j hvr
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hSphere := GM11.IsSphere.isClosedSurface hsph
  obtain ⟨g, hg, hg0, hgp⟩ := exists_path_into_region hSphere.1 H hJv hJr hvcl
  have him (t : unitInterval) : ∃ p : S, j p = g t := by
    by_cases ht : t = 0
    · exact ⟨v, by rw [ht, hg0]⟩
    · obtain ⟨p, _, hp⟩ := hgp t (unitInterval.pos_iff_ne_zero.mpr ht)
      exact ⟨p, hp⟩
  choose a ha using him
  have hac : Continuous a := hj.isEmbedding.continuous_iff.mpr (by
    have he : j ∘ a = g := funext ha
    rw [he]
    exact hg)
  have ha0 : a 0 = v := hj.injective ((ha 0).trans hg0)
  have hap (t : unitInterval) (ht : 0 < t) : a t ∈ r := by
    obtain ⟨p, hp, hpeq⟩ := hgp t ht
    exact hj.injective ((ha t).trans hpeq.symm) ▸ hp
  have hrpath : IsPathConnected r := (region_isOpen hr).isConnected_iff_isPathConnected.mp
    ⟨⟨x, hx⟩, region_isPreconnected hr⟩
  have hvoff : v ∉ r := fun h => region_subset hr h (F.V_subset_U hv)
  obtain ⟨e, hec, hei, he0, he1, hep, _⟩ :=
    exists_chord_to_point hrpath hvoff hx hac ha0 hap
  let f : Curve S := ⟨fun t => e (unitInterval.symm t), hec.comp (by fun_prop)⟩
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro s t h
    simpa using congrArg unitInterval.symm (hei h)
  · change e (unitInterval.symm 0) = x
    simpa using he1
  · change e (unitInterval.symm 1) = v
    simpa using he0
  · intro t ht
    apply hep
    intro hh
    have ht1 : t = 1 := by simpa using congrArg unitInterval.symm hh
    exact ht.ne ht1

/-- Approach any incident point of the cut-disc drawing, including
an outer cuff point which is not a drawing vertex. Adding subdivision
vertices keeps the regions unchanged. This is the terminal-join case
of the prescribed-side construction in VI (5.5), page 131. -/
theorem exists_curve_from_disc_region_point_to_drawing_point
    {S : Type u} [TopologicalSpace S] (hDisc : IsClosedDiscSpace S)
    {F : Drawing S} (hbd : bd S ⊆ F.U) {r : Set S} (hr : r ∈ F.R)
    {x v : S} (hx : x ∈ r) (hv : v ∈ F.U) (hvr : v ∈ closure r) :
    ∃ f : Curve S, Function.Injective f ∧ f 0 = x ∧ f 1 = v ∧
      ∀ t : unitInterval, t < 1 → f t ∈ r := by
  classical
  let : T2Space S := t2Space_of_isClosedDiscSpace hDisc
  by_cases hvV : v ∈ F.V
  · exact exists_curve_from_disc_region_point_to_vertex hDisc hbd hr hx hvV hvr
  · let m : Set S → S := fun e => if h : v ∈ e then v else
        if hne : e.Nonempty then Classical.choose hne else v
    have hm : ∀ e ∈ F.E, m e ∈ e := by
      intro e he
      dsimp [m]
      split_ifs with h hne
      · exact h
      · exact Classical.choose_spec hne
      · exact (hne he.1).elim
    obtain ⟨F₂, hU, hV⟩ := exists_added_vertices F hm
    obtain ⟨e, he, hve⟩ := F.exists_edge_of_mem hv hvV
    have hv₂ : v ∈ F₂.V := by
      rw [hV]
      exact Or.inr ⟨e, he, by simp only [m, dite_eq_left hve]⟩
    have hr₂ : r ∈ F₂.R := by
      change r ∈ componentsIn (univ \ F₂.U)
      rw [hU]
      exact hr
    have hbd₂ : bd S ⊆ F₂.U := hU.symm ▸ hbd
    exact exists_curve_from_disc_region_point_to_vertex hDisc hbd₂ hr₂ hx hv₂ hvr

end GraphMinor.GM06
