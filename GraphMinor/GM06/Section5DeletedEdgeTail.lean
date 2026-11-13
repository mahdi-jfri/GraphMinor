module

public import GraphMinor.GM06.Defs
public import Mathlib.Topology.Subpath
import GraphMinor.GM06.Section5RegionVisit

/-!
# The unchanged tail after the last deleted-edge region visit

In VI (5.5), page 131, the replacement retains the helix after its
last visit to the region containing the deleted edge. A later visit
to the edge would contradict maximality. At the joining parameter,
normality makes the point a vertex unless it is the terminal point.
Thus the retained tail misses the deleted edge and is normal in the
original drawing.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- After the last region visit, a normal curve misses the edge
contained in that region, including at the joining parameter.
This justifies retaining the tail in VI (5.5), page 131. -/
theorem tail_avoids_deleted_edge
    {S : Type*} [TopologicalSpace S] [LocallyConnectedSpace S]
    {G G' : Drawing S} {e : Set S} (he : e ∈ G.E) (hV : G'.V = G.V)
    (f : Curve S) (hf : IsNormalCurve G' f) (hend : f 1 ∉ e)
    {R : Set S} (hR : R ∈ G'.R) (heR : e ⊆ R)
    {z : unitInterval} (hz : IsGreatest (closure (f ⁻¹' R)) z) :
    ∀ t : unitInterval, z ≤ t → f t ∉ e := by
  intro t hzt hte
  by_cases htz : t = z
  · obtain hvertex | hz1 := (last_region_visit_mem_vertex_or_terminal f hf hR hz).2
    · have htV : f t ∈ G.V := by rw [htz, ← hV]; exact hvertex
      exact (he.2.1 hte).2 htV
    · exact hend (htz.trans hz1 ▸ hte)
  · have htz' : t ≤ z := hz.2 (subset_closure (heR hte))
    exact htz (le_antisymm htz' hzt)

/-- The retained suffix of the helix is normal in the original
drawing in the Reduction 1 case of VI (5.5), page 131. -/
theorem isNormalCurve_tail_of_deleted_edge
    {S : Type*} [TopologicalSpace S] [LocallyConnectedSpace S]
    {G G' : Drawing S} {e : Set S} (he : e ∈ G.E)
    (hV : G'.V = G.V) (hU : G'.U = G.U \ e)
    (f : Curve S) (hf : IsNormalCurve G' f) (hend : f 1 ∉ e)
    {R : Set S} (hR : R ∈ G'.R) (heR : e ⊆ R)
    {z : unitInterval} (hz : IsGreatest (closure (f ⁻¹' R)) z) :
    IsNormalCurve G ((⟨f, rfl, rfl⟩ : Path (f 0) (f 1)).subpath z 1).toContinuousMap := by
  intro x hx
  obtain ⟨t, rfl⟩ := hx.1
  let u := Icc.convexComb z 1 t
  have hu : z ≤ u := Icc.le_convexComb le_top t
  have hno : f u ∉ e := tail_avoids_deleted_edge he hV f hf hend hR heR hz u hu
  have hmem : f u ∈ G'.U := by
    rw [hU]
    exact ⟨hx.2, hno⟩
  rw [← hV]
  exact hf ⟨mem_range_self u, hmem⟩

end GraphMinor.GM06
