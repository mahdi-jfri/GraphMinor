module

public import GraphMinor.GM06.Alg34DualCuffGapRep

/-!
# Full augmented representation of a computed disc dual

The computed dual drawing has its canonical vertex, edge and region
maps. The next primal cuff labels give a correct gap interpretation at
its unique cuff. Combining these witnesses proves that the augmented
dual data again represents an intended disc input, so the same finite
reduction programs can continue on it.
-/

public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- The finite augmented dual, including its computed following-gap
region labels, represents the actual dual with the paper's dual division. -/
theorem dualGapInput_rep (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hconn : IsGraphConnected G.toGraph) (hd : IsDiscDualDrawing G D)
    (hR : 0 < x.regions.length) :
    Nonempty (GM06GapInputRep (x.dualGapInput x.cuffs[c] hR g.region) D
      (dualDivision (bd S) (D.V ∩ bd S) Δ)) := by
  classical
  refine ⟨{
    drawing := g.dualDataRep hS hconn hd hR
    gap_count := rfl
    gap := fun j => ?_ }⟩
  have hj : j.val = 0 := by
    have hh := j.isLt
    change j.val < [List.ofFn g.region].length at hh
    simp only [List.length_cons, List.length_nil] at hh
    omega
  have hgap := Classical.choice (g.dualCuffGapRep hS hconn hd hR j)
  change GM06CuffGapRep (g.dualDataRep hS hconn hd hR) j
    ([List.ofFn (x.dualGapRegionLabel x.cuffs[c] hR g.region)][j.val])
  simpa only [hj, List.getElem_cons_zero] using hgap

end GraphMinor.Compute.GM06CuffGapRep
