module

public import GraphMinor.GM06.Alg34GapDualOrder
public import GraphMinor.GM06.Alg34DualDataLabels
import GraphMinor.GM06.Alg34ListOrderTransfer

/-!
# Complete cyclic order of the finite dual drawing

The supplied gap labels cover exactly the dual boundary vertices.
Their injectivity and the proved gap crossing order give the crossing
test for all finite dual vertex labels, including those not on the
boundary. This supplies the order field of the dual representation.
-/

public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- A dual vertex is on the boundary exactly when its region label occurs
in the supplied gap list. -/
theorem dualVertex_mem_boundary_iff (g : GM06CuffGapRep h c R)
    (hS : IsClosedDiscSpace S) (hd : IsDiscDualDrawing G D) (a : Fin x.regions.length) :
    (h.dualVertexLabel hd a).val ∈ bd S ↔ a ∈ List.ofFn g.region := by
  constructor
  · intro ha
    obtain ⟨i, hi⟩ := (g.dualPoint_range hS hd).symm.subset
      ⟨(h.dualVertexLabel hd a).property, ha⟩
    exact List.mem_ofFn.mpr ⟨i, (h.dualVertexLabel_bijective hd).1 (Subtype.ext hi)⟩
  · intro ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact ((g.dualPoint_range hS hd).subset ⟨i, rfl⟩).2

/-- The assembled dual payload gives exactly the geometric crossing test
on every cuff, for every four dual vertex labels. -/
theorem dualData_order (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hconn : IsGraphConnected G.toGraph) (hd : IsDiscDualDrawing G D)
    (hR : 0 < x.regions.length) (a b i j : Fin x.regions.length) :
    (x.dualData x.cuffs[c] hR g.region).crosses a b i j = true ↔
      ∃ C ∈ cuffs S,
        CrossesOn C (h.dualDataVertexEquiv hd x.cuffs[c] hR g.region a).val
          (h.dualDataVertexEquiv hd x.cuffs[c] hR g.region b).val
          (h.dualDataVertexEquiv hd x.cuffs[c] hR g.region i).val
          (h.dualDataVertexEquiv hd x.cuffs[c] hR g.region j).val := by
  change _ ↔ ∃ C ∈ cuffs S, CrossesOn C
    (h.dualVertexLabel hd a).val (h.dualVertexLabel hd b).val
    (h.dualVertexLabel hd i).val (h.dualVertexLabel hd j).val
  have ht := gm06_crossesOnList_ofFn_iff g.region (g.region_injective hS hd.1 hconn)
    (fun a => (h.dualVertexLabel hd a).val) (bd S)
    (g.dualVertex_mem_boundary_iff hS hd) (g.dualPoint_gap_order hS hd) a b i j
  simpa only [GM06DrawingData.crosses, GM06DrawingData.dualData,
    List.any_cons, List.any_nil, Bool.or_false,
    alg34_gap_disc_cuffs_eq hS, mem_singleton_iff, exists_eq_left] using ht

end GraphMinor.Compute.GM06CuffGapRep
