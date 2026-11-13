module

public import GraphMinor.GM06.Alg34DualGapInputRep
public import GraphMinor.Compute.GM06Alg34Graph
import GraphMinor.GM06.Section3Dual

/-!
# Feasibility and validity of the computed augmented dual

The proved duality theorem of VI (3.2) identifies the primal and dual
answers. Transport both answers through their explicit drawing
representations. The computed gap classes also give a valid division,
and their interpreted union is exactly the dual boundary. These are
the conditions needed to resume the same reductions after dualization.
-/

public section
namespace GraphMinor.Compute.GM06CuffGapRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {G D : Drawing S} {Δ : Set (Set S)}
  {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
  {R : List (Fin x.regions.length)}

/-- The computed augmented dual preserves feasibility and all geometric
input conditions for continuing the reductions, using the proved VI (3.2). -/
theorem dualGapInput_correct (g : GM06CuffGapRep h c R) (hS : IsClosedDiscSpace S)
    (hconn : IsGraphConnected G.toGraph) (hd : IsDiscDualDrawing G D)
    (hR : 0 < x.regions.length) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (hCF : IsCrossFree (bd S) Δ) :
    let Y := x.dualGapInput x.cuffs[c] hR g.region
    let Δ' := dualDivision (bd S) (D.V ∩ bd S) Δ
    Nonempty (GM06GapInputRep Y D Δ') ∧ D.IsProper ∧ IsDivision Δ' ∧
      divisionUnion Δ' = D.V ∩ bd S ∧
      (IsFeasible x.graph x.divisionSet ↔ IsFeasible Y.drawing.graph Y.drawing.divisionSet) := by
  let hy := g.dualDataRep hS hconn hd hR
  have hYD := alg34_division_image (f := hy.vertexEmbedding)
    (x.dualData_isDivision x.cuffs[c] hR g.region (g.region_injective hS hd.1 hconn))
  have hYD' : IsDivision (dualDivision (bd S) (D.V ∩ bd S) Δ) :=
    hy.division_map_eq ▸ hYD
  refine ⟨g.dualGapInput_rep hS hconn hd hR, hd.2.1, hYD',
    divisionUnion_dualDivision _ _ _, ?_⟩
  exact (h.feasible_iff hD).symm.trans
    ((GraphMinor.GM06.theorem_3_2_proof G D Δ hS hconn hD hbd hCF hd).trans (hy.feasible_iff hYD'))

end GraphMinor.Compute.GM06CuffGapRep
