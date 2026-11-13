module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5CylinderEdgeIncidence
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM07.Section11f
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Walks
import GraphMinor.Surface.CutComp

/-!
# Region incidence at the initial end of a contracted edge

For Reduction 3 in VI (5.5), page 130, a region incident with the
valency-one initial vertex is also incident with its neighbour.
Otherwise its closure misses the sole incident edge. In a small
connected neighbourhood, removing the surface boundary would then
leave two separated nonempty open parts, which is impossible.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- At a valency-one initial vertex, every incident region is also
incident with the other end of its unique edge. -/
theorem neighbour_mem_closure_region_of_initial_valency_one
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {e R : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i) (hR : R ∈ G.R)
    (hsR : cylinderM1Point k i ∈ closure R) : v ∈ closure R := by
  classical
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  let s := cylinderM1Point k i
  by_contra hvR
  have hvcl : v ∈ closure e := by
    have hh : v ∈ closure e ∩ G.V := hl.2.2.2 ▸ (mem_insert_of_mem s rfl)
    exact hh.1
  have heR : Disjoint e (closure R) := by
    apply disjoint_left.mpr
    intro x hxe hxR
    exact hvR (closure_edge_subset_closure_region_of_incident L hG hl.1 hR ⟨x, hxe, hxR⟩ hvcl)
  let B : Set ClosedCylinder := (G.V \ {s}) ∪ ⋃ a ∈ G.E \ {e}, closure a
  have hBc : IsClosed B :=
    (G.finite_V.sdiff (t := {s})).isClosed.union
      ((G.finite_edges.sdiff (t := {e})).isClosed_biUnion fun _ _ => isClosed_closure)
  have hsB : s ∉ B := by
    rintro (hs | hs)
    · exact hs.2 rfl
    · obtain ⟨a, ha, hsa⟩ := mem_iUnion₂.mp hs
      exact not_mem_closure_edge_of_ne_red3 hval hl hv ha.1
        (fun heq => ha.2 (mem_singleton_iff.mpr heq)) hsa
  let N := connectedComponentIn Bᶜ s
  have hNo : IsOpen N := hBc.isOpen_compl.connectedComponentIn
  have hsN : s ∈ N := mem_connectedComponentIn hsB
  have hNsub : N ⊆ Bᶜ := connectedComponentIn_subset _ _
  have hconn : IsPreconnected (N \ bd ClosedCylinder) :=
    GM07.isPreconnected_diff_bd isSurface_closedCylinder hNo isPreconnected_connectedComponentIn
  have hlocal : ∀ x ∈ N \ bd ClosedCylinder, x ∈ closure R → x ∈ R := by
    intro x hx hxR
    rcases GM11.closure_region_subset hR hxR with hxr | hxU
    · exact hxr
    · rw [G.U_eq] at hxU
      rcases hxU with hxV | hxa
      · have hxs : x = s := by
          by_contra hne
          exact hNsub hx.1 (Or.inl ⟨hxV, hne⟩)
        exact False.elim (hx.2 (hxs ▸ cylinderM1Point_mem_bd k i))
      · obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hxa
        have hae : a = e := by
          by_contra hne
          exact hNsub hx.1 (Or.inr (mem_iUnion₂.mpr ⟨a, ⟨ha, hne⟩, hxa⟩))
        subst a
        by_cases hxV : x ∈ G.V
        · exact False.elim (hNsub hx.1 (Or.inl ⟨hxV, fun heq =>
            hx.2 (heq ▸ cylinderM1Point_mem_bd k i)⟩))
        · have hxe : x ∈ e := G.closure_diff_V hl.1 ▸ ⟨hxa, hxV⟩
          exact False.elim (disjoint_left.mp heR hxe hxR)
  have hscl : s ∈ closure (R \ bd ClosedCylinder) :=
    (region_sdiff_boundary_connected_and_closure isSurface_closedCylinder hR).2.symm ▸ hsR
  obtain ⟨x, hxN, hxR, hxbd⟩ := mem_closure_iff.mp hscl N hNo hsN
  have hsE : s ∈ closure e := by
    have hh : s ∈ closure e ∩ G.V := hl.2.2.2 ▸ mem_insert s {v}
    exact hh.1
  obtain ⟨y, hyN, hye⟩ := mem_closure_iff.mp hsE N hNo hsN
  have hybd : y ∉ bd ClosedCylinder := by
    intro hy
    exact (hl.1.2.1 hye).2 (hG.2.1 ⟨hy, (hl.1.2.1 hye).1⟩)
  have hyR : y ∉ closure R := disjoint_left.mp heR hye
  obtain ⟨z, _, hzR, hznot⟩ := hconn R (closure R)ᶜ
    (GM11.region_isOpen hR) isClosed_closure.isOpen_compl
    (fun z hz => by
      by_cases hzr : z ∈ closure R
      · exact Or.inl (hlocal z hz hzr)
      · exact Or.inr hzr)
    ⟨x, ⟨hxN, hxbd⟩, hxR⟩ ⟨y, ⟨hyN, hybd⟩, hyR⟩
  exact hznot (subset_closure hzR)

end GraphMinor.GM06
