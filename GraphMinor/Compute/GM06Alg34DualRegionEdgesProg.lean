module

public import GraphMinor.Compute.GM06Alg34DualSelect
public import GraphMinor.Compute.GM06Alg34DualIncidenceExpr
public import GraphMinor.Compute.GM06Alg34DualIncidenceLists

/-!
# Computing one dual region edge list

Scan the supplied edge labels in order. The prepared closure matrix
selects exactly those having the chosen vertex as an end. The
resulting buffer therefore holds the edges of the paper's transposed
dual region boundary, with its exact live count.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Select the incident edges of vertex register 7600 into array 54. -/
def gm06DualRegionEdgesProg : Cmd :=
  gm06DualSelectProg 51 (gm06DualEdgeVertexExpr 7603 7600) (.reg 7603)

/-- The incidence scan computes the exact supplied dual region edge list,
with linear scan work after the closure matrix has been prepared. -/
theorem gm06DualRegionEdgesProg_exec {w : ℕ} (x : GM06DrawingData)
    (v : Fin x.n) {s : State}
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hspan : x.ends.length + 2 < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n)
    (hvertex : s.regs 7600 = v.val) (hsource : s.arrs 51 = List.range x.ends.length) :
    ∃ s' t, Exec w gm06DualRegionEdgesProg s s' t ∧
      t ≤ 100 * (x.ends.length + 1) ∧
      s'.arrs 54 = (x.dualRegionEdges v).map Fin.val ++
        List.replicate (x.ends.length - (x.dualRegionEdges v).length) 0 ∧
      s'.regs 7604 = (x.dualRegionEdges v).length ∧
      (∀ A, A ≠ 54 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7601 ∨ 7605 < r → s'.regs r = s.regs r) := by
  have hrN : x.ends.length ≤ x.cellCount := by
    dsimp only [GM06DrawingData.cellCount]
    omega
  have hwords : ∀ y ∈ List.range x.ends.length, y < 2 ^ w :=
    fun y hy => ((List.mem_range.mp hy).trans_le hrN).trans hN
  obtain ⟨s', t, he, ht, hb, hc, ha, hr⟩ := gm06DualSelectProg_exec
    (gm06DualEdgeVertexExpr 7603 7600) (.reg 7603) (gm06DualRegionEdgeKeep x v) id
    (by decide : 51 ≠ 54) hw hsource (by simpa only [List.length_range] using hspan) hwords
    (fun z y hy ha hr hry => by
      have hyr : y < x.ends.length := List.mem_range.mp hy
      let r : Fin x.ends.length := ⟨y, hyr⟩
      have ht := gm06DualEdgeVertexExpr_eval x r v hw hN hsquare
        ((ha 12 (by decide)).trans hmat) ((hr 170 (Or.inl (by decide))).trans hstride)
        ((hr 100 (Or.inl (by decide))).trans hn)
        hry ((hr 7600 (Or.inl (by decide))).trans hvertex)
      simpa only [gm06DualRegionEdgeKeep, hyr, ↓reduceDIte, decide_eq_true_eq, Fin.getElem_fin, r] using ht)
    (fun z y hy _ _ _ hry => eval_reg hry (hwords y hy))
  have hcost : (gm06DualEdgeVertexExpr 7603 7600).cost + (Expr.reg 7603).cost + 6 ≤ 80 := by decide
  have hmul := Nat.mul_le_mul_left x.ends.length (Nat.add_le_add_left hcost 10)
  simp only [List.length_range] at ht
  refine ⟨s', t, he, by omega, ?_, ?_, ha, hr⟩
  · simpa only [id_eq, gm06DualRegionEdgeWords, List.length_map, List.length_range] using hb
  · simpa only [id_eq, gm06DualRegionEdgeWords, List.length_map] using hc

end GraphMinor.Compute
