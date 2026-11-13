module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section9Foundation
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.GM08.Section6
import GraphMinor.GM11.Regions
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.Disc

/-!
# The discs used to thicken cellular loops

For a cellular loop, take its bounded region together with its boundary.
The resulting closed disc meets the drawing exactly in the closed loop
edge. Two different loop discs meet only in their loop boundaries,
since their interiors are different regions. These are the loop pieces
of the derived portrait on VIII, page 272, used in Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

private theorem closure_discInt_eq {S : Type u} [TopologicalSpace S] [T2Space S]
    {B : Set S} (hB : IsClosedDisc B) : closure (discInt B) = B :=
  Subset.antisymm (closure_minimal (discInt_subset B) hB.isClosed) hB.subset_closure_discInt

/-- A cellular loop disc meets the drawing exactly in the closed loop
edge, as required in the thickening construction on VIII, page 272. -/
theorem loop_disc_inter_drawing {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {e B : Set S} (he : e ∈ D.E)
    (hB : IsInsideDisc univ (closure e) B) (hr : discInt B ∈ D.R) :
    B ∩ D.U = closure e := by
  apply Subset.antisymm
  · rintro x ⟨hxB, hxD⟩
    by_contra hn
    exact GM11.region_subset hr ⟨hxB, hB.2.2.1.symm ▸ hn⟩ hxD
  · intro x hx
    exact ⟨discBd_subset B (hB.2.2.1.symm ▸ hx), D.closure_subset_U he hx⟩

/-- Distinct cellular loops have distinct bounded regions. Equal
interiors would have equal closures and hence equal edge boundaries. -/
theorem loop_regions_ne_of_edges_ne {S : Type u} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {e f B C : Set S} (he : e ∈ D.E) (hf : f ∈ D.E) (hne : e ≠ f)
    (hB : IsInsideDisc univ (closure e) B) (hC : IsInsideDisc univ (closure f) C) :
    discInt B ≠ discInt C := by
  intro h
  have hBC : B = C := by
    rw [← closure_discInt_eq hB.2.1, ← closure_discInt_eq hC.2.1, h]
  have hcl : closure e = closure f := by
    rw [← hB.2.2.1, ← hC.2.2.1, hBC]
  apply hne
  calc
    e = closure e \ D.V := (D.closure_diff_V he).symm
    _ = closure f \ D.V := congrArg (fun A => A \ D.V) hcl
    _ = f := D.closure_diff_V hf

/-- Two loop discs meet only in the common points of their closed
edges. This verifies the pairwise thickening condition on VIII, page 272. -/
theorem loop_discs_inter_subset_edges {S : Type u} [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {e f B C : Set S} (he : e ∈ D.E) (hf : f ∈ D.E) (hne : e ≠ f)
    (hB : IsInsideDisc univ (closure e) B) (hC : IsInsideDisc univ (closure f) C)
    (hrB : discInt B ∈ D.R) (hrC : discInt C ∈ D.R) :
    B ∩ C ⊆ closure e ∩ closure f := by
  rintro x ⟨hxB, hxC⟩
  have hxe : x ∈ closure e := by
    by_contra hn
    have hxintB : x ∈ discInt B := ⟨hxB, hB.2.2.1.symm ▸ hn⟩
    have hxnotD : x ∉ D.U := GM11.region_subset hrB hxintB
    have hxintC : x ∈ discInt C := ⟨hxC, fun hxBd =>
      hxnotD (D.closure_subset_U hf (hC.2.2.1 ▸ hxBd))⟩
    exact loop_regions_ne_of_edges_ne he hf hne hB hC
      (GM11.region_eq_of_mem hrB hrC hxintB hxintC)
  exact ⟨hxe, loop_disc_inter_drawing hf hC hrC ▸
    (show x ∈ C ∩ D.U from ⟨hxC, D.closure_subset_U he hxe⟩)⟩

/-- A boss ring cannot enter the empty region of a cellular loop.
A normal ring can meet the loop boundary only at its end. If it entered
the region, the whole ring and its boss circuit would lie in that empty
region, which contains no drawing point. -/
theorem boss_ring_disjoint_loop_interior {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) {D : Drawing S} {e B F : Set S}
    (he : e ∈ D.E) {v : S} (hcap : closure e ∩ D.V = {v})
    (hB : IsInsideDisc univ (closure e) B) (hr : discInt B ∈ D.R)
    {C : DiscCircuit D univ} (hC : IsBoss D univ C) (hF : IsCRing C F) :
    Disjoint F (discInt B) := by
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  have : ConnectedSpace S := connectedSpace_iff_univ.mpr hS.isPathConnected.isConnected
  have hvcl : v ∈ closure e := (show v ∈ closure e ∩ D.V from hcap.symm ▸ mem_singleton v).1
  have hvBd : v ∈ discBd B := hB.2.2.1.symm ▸ hvcl
  have hmeet : F ∩ discBd B ⊆ {v} := by
    rintro x ⟨hxF, hxBd⟩
    have hxcl : x ∈ closure e := hB.2.2.1 ▸ hxBd
    have hxV := hF.2.2.1 ⟨hxF, D.closure_subset_U he hxcl⟩
    exact hcap ▸ And.intro hxcl hxV
  apply disjoint_left.mpr
  intro x hxF hxB
  have hxv : x ≠ v := fun h => hxB.2 (h.symm ▸ hvBd)
  have hdis : Disjoint (F \ {v}) (discBd B) := disjoint_left.mpr fun y hy hyB =>
    hy.2 (hmeet ⟨hy.1, hyB⟩)
  have hprec := isPreconnected_oArc_sdiff_singleton hF.2.1 v
  have hFsubB : F ⊆ B := by
    rcases side_of_closedDisc hS hB.1 (subset_univ _) hB.2.1 hprec hdis with hin | hout
    · intro y hy
      by_cases hyv : y = v
      · exact hyv.symm ▸ discBd_subset B hvBd
      · exact (hin ⟨hy, hyv⟩).1
    · exact False.elim (disjoint_left.mp hout ⟨hxF, hxv⟩ hxB.1)
  obtain ⟨K, hK, -⟩ := disc_oArc univ F hS (subset_univ _) hF.2.1
  have henc : OArcEncloses univ (closure e) F := (oArcEncloses_iff_subset hS hB).mpr hFsubB
  have hmono := (insideDisc_subset_of_oArcEncloses hS hB hK henc).2
  obtain ⟨φ⟩ := C.isOArc_U
  have hc := (φ (1 : Circle)).2
  have hcin := (insideOArc_iff_mem_discInt hS hK).mp (hC.inside_cRing hS (subset_univ _) hF _ hc)
  exact GM11.region_subset hr (hmono hcin) (C.U_sub_drawing hc)

/-- A cellular loop outside a boss ring has its whole loop disc outside
that ring disc except at the closed loop edge. This verifies the ring
avoidance condition for loop thickenings on VIII, page 272. -/
theorem loop_disc_inter_ring_disc_subset {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) {D : Drawing S} {e B F K : Set S}
    (he : e ∈ D.E) {v : S} (hcap : closure e ∩ D.V = {v})
    (hB : IsInsideDisc univ (closure e) B) (hr : discInt B ∈ D.R)
    {C : DiscCircuit D univ} (hC : IsBoss D univ C) (hF : IsCRing C F)
    (hK : IsInsideDisc univ F K) (hout : ¬ SetInsideOArc univ F e) :
    B ∩ K ⊆ closure e := by
  have hd := boss_ring_disjoint_loop_interior hS he hcap hB hr hC hF
  rintro x ⟨hxB, hxK⟩
  by_contra hxcl
  have hxintB : x ∈ discInt B := ⟨hxB, hB.2.2.1.symm ▸ hxcl⟩
  have hsep : Disjoint (discInt B) (discBd K) := by
    rw [hK.2.2.1]
    exact hd.symm
  have hxintK : x ∈ discInt K := ⟨hxK, fun hxbd => disjoint_left.mp hd
    (hK.2.2.1 ▸ hxbd) hxintB⟩
  have hBK := (subset_of_discInt_meets hS hB.1 hK.1 hB.2.1 hK.2.1 hsep ⟨x, hxB, hxintK⟩).1
  apply hout
  intro y hye
  have hyK : y ∈ K := hBK (discBd_subset B (hB.2.2.1.symm ▸ subset_closure hye))
  exact (insideOArc_iff_mem_discInt hS hK).mpr ⟨hyK, fun hybd =>
    (he.2.1 hye).2 (hF.2.2.1 ⟨hK.2.2.1 ▸ hybd, (he.2.1 hye).1⟩)⟩

end GraphMinor.GM08
