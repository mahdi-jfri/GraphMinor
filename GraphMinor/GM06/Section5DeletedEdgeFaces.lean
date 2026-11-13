module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.Defs
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Section4c

/-!
# Old faces in the region of a deleted edge

The Reduction 1 proof of VI (5.5), page 131, chooses an old region
incident with the initial vertex and with the last helix point.
In a closed surface an edge has at most two incident regions.
Every old region inside the new edge-containing region is one of
these two: a region not incident with the edge survives deletion.
Taking closures therefore gives the required old region at every
point of the new region closure. This fact is used after capping
the cylinder cuffs.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- A point in the closure of the region containing a deleted edge
is incident with an old region containing that edge in its closure.
This is the face choice in VI (5.5), page 131, on a closed surface. -/
theorem exists_old_region_at_deleted_edge_region_closure
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {G : Drawing S} {e R : Set S} (he : e ∈ G.E)
    (hR : R ∈ (G.deleteEdge e).R) (heR : e ⊆ R)
    {w : S} (hw : w ∈ closure R) :
    ∃ r ∈ G.R, r ⊆ R ∧ e ⊆ closure r ∧ w ∈ closure r := by
  classical
  let : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨p, hp⟩ := he.1
  obtain ⟨r₁, hr₁, hi₁⟩ := exists_region_incident hS he
  have hpair : ∃ r₂ ∈ G.R, e ⊆ closure r₂ ∧
      ∀ r ∈ G.R, e ⊆ closure r → r = r₁ ∨ r = r₂ := by
    by_cases hother : ∃ r₂ ∈ G.R, e ⊆ closure r₂ ∧ r₂ ≠ r₁
    · obtain ⟨r₂, hr₂, hi₂, hne⟩ := hother
      refine ⟨r₂, hr₂, hi₂, ?_⟩
      intro r hr hi
      rcases region_incident_two hS he hr₁ hr₂ hr hi₁ hi₂ hi with h | h | h
      · exact (hne h.symm).elim
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · refine ⟨r₁, hr₁, hi₁, ?_⟩
      intro r hr hi
      by_cases h : r = r₁
      · exact Or.inl h
      · exact (hother ⟨r, hr, hi, h⟩).elim
  obtain ⟨r₂, hr₂, hi₂, hall⟩ := hpair
  have hinside (r : Set S) (hr : r ∈ G.R) (hi : e ⊆ closure r) : r ⊆ R := by
    obtain ⟨x, hxR, hxr⟩ := mem_closure_iff.mp (hi hp) R (region_isOpen hR) (heR hp)
    apply subset_region hR (region_isPreconnected hr) _ hxr hxR
    refine disjoint_left.mpr ?_
    intro y hyr hyU
    rw [deleteEdge_U G he] at hyU
    exact region_subset hr hyr hyU.1
  have hcover : R ⊆ closure r₁ ∪ closure r₂ := by
    intro x hxR
    by_cases hxe : x ∈ e
    · exact Or.inl (hi₁ hxe)
    · have hxU : x ∉ G.U := by
        intro hxG
        have hx := region_subset hR hxR
        rw [deleteEdge_U G he] at hx
        exact hx ⟨hxG, hxe⟩
      obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
      have hi : e ⊆ closure r := by
        rcases edge_incident_or_disjoint hS he hr with hi | hdis
        · exact hi
        · have hrDel := region_deleteEdge_of_not_incident he hr hdis
          have heq : r = R := region_eq_of_mem hrDel hR hxr hxR
          have hpR : p ∈ r := heq.symm ▸ heR hp
          exact (region_subset hr hpR (he.2.1 hp).1).elim
      rcases hall r hr hi with rfl | rfl
      · exact Or.inl (subset_closure hxr)
      · exact Or.inr (subset_closure hxr)
  have hw' : w ∈ closure r₁ ∪ closure r₂ :=
    closure_minimal hcover (isClosed_closure.union isClosed_closure) hw
  rcases hw' with hw₁ | hw₂
  · exact ⟨r₁, hr₁, hinside r₁ hr₁ hi₁, hi₁, hw₁⟩
  · exact ⟨r₂, hr₂, hinside r₂ hr₂ hi₂, hi₂, hw₂⟩

end GraphMinor.GM06
