module

public import GraphMinor.Compute.GM06Alg34DualSelect
public import GraphMinor.Compute.GM06Alg34DualIncidenceExpr
public import GraphMinor.Compute.GM06Alg34DualIncidenceLists

/-!
# Computing the incident-region list of a primal edge

Scan the supplied region labels in order. The prepared closure matrix
selects exactly those whose boundary contains the chosen edge. The
resulting buffer therefore holds the regions used by the paper's dual
endpoint operation, with its exact live count.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Select the incident regions of edge register 7600 into array 54. -/
def gm06DualIncidentRegionsProg : Cmd :=
  gm06DualSelectProg 52 (gm06DualRegionEdgeExpr 7603 7600) (.reg 7603)

/-- The incidence scan computes the exact supplied incident-region list,
with linear scan work after the closure matrix has been prepared. -/
theorem gm06DualIncidentRegionsProg_exec {w : ℕ} (x : GM06DrawingData)
    (e : Fin x.ends.length) {s : State}
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hspan : x.regions.length + 2 < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hedge : s.regs 7600 = e.val) (hsource : s.arrs 52 = List.range x.regions.length) :
    ∃ s' t, Exec w gm06DualIncidentRegionsProg s s' t ∧
      t ≤ 100 * (x.regions.length + 1) ∧
      s'.arrs 54 = (x.incidentRegions e).map Fin.val ++
        List.replicate (x.regions.length - (x.incidentRegions e).length) 0 ∧
      s'.regs 7604 = (x.incidentRegions e).length ∧
      (∀ A, A ≠ 54 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7601 ∨ 7605 < r → s'.regs r = s.regs r) := by
  have hrN : x.regions.length ≤ x.cellCount := by
    dsimp only [GM06DrawingData.cellCount]
    omega
  have hwords : ∀ y ∈ List.range x.regions.length, y < 2 ^ w :=
    fun y hy => ((List.mem_range.mp hy).trans_le hrN).trans hN
  obtain ⟨s', t, he, ht, hb, hc, ha, hr⟩ := gm06DualSelectProg_exec
    (gm06DualRegionEdgeExpr 7603 7600) (.reg 7603) (gm06DualIncidentRegionKeep x e) id
    (by decide : 52 ≠ 54) hw hsource (by simpa only [List.length_range] using hspan) hwords
    (fun z y hy ha hr hry => by
      have hyr : y < x.regions.length := List.mem_range.mp hy
      let r : Fin x.regions.length := ⟨y, hyr⟩
      have ht := gm06DualRegionEdgeExpr_eval x r e hw hN hsquare
        ((ha 12 (by decide)).trans hmat) ((hr 170 (Or.inl (by decide))).trans hstride)
        ((hr 100 (Or.inl (by decide))).trans hn) ((hr 101 (Or.inl (by decide))).trans hm)
        hry ((hr 7600 (Or.inl (by decide))).trans hedge)
      simpa only [gm06DualIncidentRegionKeep, hyr, ↓reduceDIte, decide_eq_true_eq, Fin.getElem_fin, r] using ht)
    (fun z y hy _ _ _ hry => eval_reg hry (hwords y hy))
  have hcost : (gm06DualRegionEdgeExpr 7603 7600).cost + (Expr.reg 7603).cost + 6 ≤ 80 := by decide
  have hmul := Nat.mul_le_mul_left x.regions.length (Nat.add_le_add_left hcost 10)
  simp only [List.length_range] at ht
  refine ⟨s', t, he, by omega, ?_, ?_, ha, hr⟩
  · simpa only [id_eq, gm06DualIncidentRegionWords, List.length_map, List.length_range] using hb
  · simpa only [id_eq, gm06DualIncidentRegionWords, List.length_map] using hc

end GraphMinor.Compute
