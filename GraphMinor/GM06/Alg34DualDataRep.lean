module

public import GraphMinor.GM06.Alg34DualDataOrder
public import GraphMinor.Compute.GM06Alg34DiscRep

/-!
# Representation of the computed dual drawing

Combine the supplied region labels, retained edge labels and transposed
region boundaries with the gap order at the actual dual vertices. The
result is the full drawing representation of the computed finite dual
payload. All maps in this proof interpret the data and are never read
by the algorithm.
-/

public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- The computed dual division, transported through the region labels,
is the paper's dual division on the complete actual dual boundary. -/
theorem dualData_division_image (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hd : IsDiscDualDrawing G D) (hR : 0 < x.regions.length) :
    (Set.image (fun v => (h.dualDataVertexEquiv hd x.cuffs[c] hR g.region v).val)) ''
        (x.dualData x.cuffs[c] hR g.region).divisionSet =
      dualDivision (bd S) (D.V ∩ bd S) Δ := by
  rw [GM06DrawingData.dualData_divisionSet]
  have he :
      (Set.image (fun v => (h.dualDataVertexEquiv hd x.cuffs[c] hR g.region v).val)) ''
          (Set.image g.region) '' x.dualGapDivisionSet x.cuffs[c] =
        (Set.image (g.dualPoint hd)) '' x.dualGapDivisionSet x.cuffs[c] := by
    simp only [Set.image_image]
    rfl
  exact he.trans ((g.dualDivision_image hS hd).trans
    (congrArg (fun B => dualDivision (bd S) B Δ) (g.dualPoint_range hS hd)))

/-- The dual division equation in the explicit block-image form used by
an input representation. -/
theorem dualData_division (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hd : IsDiscDualDrawing G D) (hR : 0 < x.regions.length) :
    dualDivision (bd S) (D.V ∩ bd S) Δ =
      (fun L => (fun v => (h.dualDataVertexEquiv hd x.cuffs[c] hR g.region v).val) ''
        GM06DrawingData.block L) '' {L | L ∈ (x.dualData x.cuffs[c] hR g.region).division} := by
  have he := (g.dualData_division_image hS hd hR).symm
  change dualDivision (bd S) (D.V ∩ bd S) Δ =
    (Set.image (fun v => (h.dualDataVertexEquiv hd x.cuffs[c] hR g.region v).val)) ''
      (GM06DrawingData.block '' {L | L ∈ (x.dualData x.cuffs[c] hR g.region).division}) at he
  exact he.trans (Set.image_image _ _ _)

/-- The canonical interpretation of the assembled finite dual drawing,
with region, edge and transposed vertex labels as its explicit maps. -/
@[expose] noncomputable def dualDataRep (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hconn : IsGraphConnected G.toGraph) (hd : IsDiscDualDrawing G D)
    (hR : 0 < x.regions.length) :
    GM06DrawingRep (x.dualData x.cuffs[c] hR g.region) D
      (dualDivision (bd S) (D.V ∩ bd S) Δ) := by
  let y := x.dualData x.cuffs[c] hR g.region
  have hlen : y.cuffs.length = x.cuffs.length := by
    change [List.ofFn g.region].length = x.cuffs.length
    exact (h.cuffs_length_one hS).symm
  let C : Fin y.cuffs.length ≃ cuffs S := (finCongr hlen).trans h.cuff
  have hC (j : Fin y.cuffs.length) : (C j).val = bd S :=
    mem_singleton_iff.mp ((alg34_gap_disc_cuffs_eq hS) ▸ (C j).property)
  refine {
    vertex := h.dualDataVertexEquiv hd x.cuffs[c] hR g.region
    edge := h.dualDataEdgeEquiv hd x.cuffs[c] hR g.region
    region := h.dualDataRegionEquiv hS hconn hd x.cuffs[c] hR g.region
    ends := h.dualData_ends hd x.cuffs[c] hR g.region
    boundary := h.dualData_boundary hS hconn hd x.cuffs[c] hR g.region
    cuff := C
    cuff_vertices := ?_
    cuff_nodup := ?_
    order := g.dualData_order hS hconn hd hR
    division := g.dualData_division hS hd hR }
  · intro j
    have hj : j.val = 0 := by have hh := j.isLt; change j.val < [List.ofFn g.region].length at hh; simp only [List.length_cons, List.length_nil] at hh; omega
    have hget : y.cuffs[j] = List.ofFn g.region := by
      change [List.ofFn g.region][j.val] = _
      simp only [hj, List.getElem_cons_zero]
    rw [hget, hC]
    have hs := g.segment_mem
    have hcover := g.segment_cover
    rw [h.disc_cuff_eq_bd hS c] at hs hcover
    exact h.gap_region_labels_cuff hS hd g.segment g.region hs hcover g.region_meets
  · intro L hL
    have hL' : L = List.ofFn g.region := List.mem_singleton.mp hL
    rw [hL']
    exact List.nodup_ofFn.mpr (g.region_injective hS hd.1 hconn)

/-- The assembled finite dual array represents the actual dual drawing
and the computed geometric dual division. -/
theorem dualData_rep (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hconn : IsGraphConnected G.toGraph) (hd : IsDiscDualDrawing G D)
    (hR : 0 < x.regions.length) :
    Nonempty (GM06DrawingRep (x.dualData x.cuffs[c] hR g.region) D
      (dualDivision (bd S) (D.V ∩ bd S) Δ)) :=
  ⟨g.dualDataRep hS hconn hd hR⟩

end GraphMinor.Compute.GM06CuffGapRep
