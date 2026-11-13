module

public import GraphMinor.Compute.Case3StepsEdgeLabels
import Mathlib.Data.List.GetD

/-!
# Reading one simple edge's owner label

Once the edge endpoints have been read, two core-bit tests select either an
outside endpoint's component representative or the edge's core representative.
The result goes in register 44. The graph and all arrays remain unchanged.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Select a routing label from the component and core-edge tables. -/
def case3EdgeLabelProg : Cmd :=
  .ite (.read 10 (.reg 42))
    (.ite (.read 10 (.reg 43))
      (.assign 44 (.read 28 (.reg 18)))
      (.assign 44 (.read 27 (.reg 43))))
    (.assign 44 (.read 27 (.reg 42)))

/-- Core bit, component label, and core-edge label reads compute the exact owner. -/
theorem case3EdgeLabelProg_exec {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (j : Fin (case3InputEdges x).length) (hw : 1 < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hZ : IsBitSet Z 10 s) (hreps : s.arrs 27 = case3ComponentRepList x Z)
    (hedges : s.arrs 28 = case3CoreEdgeRepList x Z)
    (hrj : s.regs 18 = j.1)
    (hru : s.regs 42 = ((case3InputEdges x)[j.1]).1.1)
    (hrv : s.regs 43 = ((case3InputEdges x)[j.1]).2.1) :
    ∃ t, Exec w case3EdgeLabelProg s (s.setReg 44 (case3EdgeLabel x Z j)) t ∧ t ≤ 7 := by
  classical
  let u := ((case3InputEdges x)[j.1]).1
  let v := ((case3InputEdges x)[j.1]).2
  have hn : x.n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  have hbit (z : Fin x.n) (r : ℕ) (hr : s.regs r = z.1) :
      (Expr.read 10 (.reg r)).eval w s = some (if z ∈ Z then 1 else 0) := by
    have hi : z.1 < (s.arrs 10).length := by rw [hZ.1]; exact z.2
    have hg : (s.arrs 10)[z.1]'hi = if z ∈ Z then 1 else 0 := by
      simpa only [hZ.arr_eq_bitSetList] using getElem_bitSetList Z z.1 z.2
    by_cases hz : z ∈ Z <;>
      simp [Expr.eval, checkWord, hr, z.2.trans hn, hi, hg, hz, hw, h0]
  have hrep (z : Fin x.n) (r : ℕ) (hz : z ∉ Z) (hr : s.regs r = z.1) :
      (Expr.read 27 (.reg r)).eval w s = some (case3ComponentRepresentative x Z z) := by
    have hi : z.1 < (s.arrs 27).length := by rw [hreps, case3ComponentRepList_length]; exact z.2
    have hg : (s.arrs 27)[z.1]'hi = case3ComponentRepresentative x Z z := by
      simp only [hreps, case3ComponentRepList, List.getElem_ofFn, hz, ↓reduceIte]
    have hwz := (case3ComponentRepresentative_lt x Z z hz).trans hn
    simp [Expr.eval, checkWord, hr, z.2.trans hn, hi, hg, hwz]
  have hedge : (Expr.read 28 (.reg 18)).eval w s = some (case3CoreEdgeRepEntry x Z j) := by
    have hi : j.1 < (s.arrs 28).length := by
      rw [hedges, case3CoreEdgeRepList_length]; exact j.2
    have hg : (s.arrs 28)[j.1]'hi = case3CoreEdgeRepEntry x Z j := by
      simp only [hedges, case3CoreEdgeRepList, List.getElem_ofFn]
    have hwj : j.1 < 2 ^ w := by have hj := j.2; omega
    have hwe := (case3CoreEdgeRepEntry_le x Z j).trans_lt hsize
    simp [Expr.eval, checkWord, hrj, hwj, hi, hg, hwe]
  by_cases hu : u ∈ Z
  · have hcu : (Expr.read 10 (.reg 42)).eval w s = some 1 := by
      simpa only [hu, ↓reduceIte] using hbit u 42 hru
    by_cases hv : v ∈ Z
    · have hcv : (Expr.read 10 (.reg 43)).eval w s = some 1 := by
        simpa only [hv, ↓reduceIte] using hbit v 43 hrv
      have hl : case3EdgeLabel x Z j = case3CoreEdgeRepEntry x Z j := by
        simp only [case3EdgeLabel, show ((case3InputEdges x)[j.1]).1 = u from rfl,
          show ((case3InputEdges x)[j.1]).2 = v from rfl, hu, hv, ↓reduceIte]
      rw [hl]
      exact ⟨7, .ite_true hcu (by decide) (.ite_true hcv (by decide) (.assign hedge)), by decide⟩
    · have hcv : (Expr.read 10 (.reg 43)).eval w s = some 0 := by
        simpa only [hv, ↓reduceIte] using hbit v 43 hrv
      have hl : case3EdgeLabel x Z j = case3ComponentRepresentative x Z v := by
        simp only [case3EdgeLabel, show ((case3InputEdges x)[j.1]).1 = u from rfl,
          show ((case3InputEdges x)[j.1]).2 = v from rfl, hu, hv, ↓reduceIte]
      rw [hl]
      exact ⟨7, .ite_true hcu (by decide) (.ite_false hcv (.assign (hrep v 43 hv hrv))), by decide⟩
  · have hcu : (Expr.read 10 (.reg 42)).eval w s = some 0 := by
      simpa only [hu, ↓reduceIte] using hbit u 42 hru
    have hl : case3EdgeLabel x Z j = case3ComponentRepresentative x Z u := by
      simp only [case3EdgeLabel, show ((case3InputEdges x)[j.1]).1 = u from rfl, hu, ↓reduceIte]
    rw [hl]
    exact ⟨5, .ite_false hcu (.assign (hrep u 42 hu hru)), by decide⟩

end GraphMinor.Compute
