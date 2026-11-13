module

public import GraphMinor.Compute.Case3StepsPairOwner
import Mathlib.Data.List.GetD

/-!
# Looking up one directed pair's owner on the RAM

Equal endpoints select the loop-owner table. Distinct endpoints select the
row-major endpoint matrix. Both branches read one stored label and preserve
all arrays, so each positive multigraph pair is routed without expanding its
multiplicity.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Route endpoints in registers 66 and 67, returning the owner in register 68. -/
def case3PairOwnerProg : Cmd :=
  .ite (.op .eq (.reg 66) (.reg 67))
    (.assign 68 (.read 33 (.reg 66)))
    (.assign 68 (.read 34 (.op .add (.op .mul (.reg 66) (.reg 14)) (.reg 67))))

/-- One valid pair's owner is read in at most ten RAM steps. -/
theorem case3PairOwnerProg_exec {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (u v : Fin x.n) (hvalid : u = v ∨ x.G.Adj u v)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hloop : s.arrs 33 = List.ofFn (case3OrderedLoopLabel x Z))
    (hmat : s.arrs 34 = case3EdgeMatrixPrefix x Z (case3InputEdges x).length)
    (hrn : s.regs 14 = x.n) (hru : s.regs 66 = u.1) (hrv : s.regs 67 = v.1) :
    ∃ t, Exec w case3PairOwnerProg s (s.setReg 68 (case3PairOwner x Z u v)) t ∧ t ≤ 10 := by
  classical
  have h0 : 0 < 2 ^ w := by omega
  have huw := u.2.trans hn
  have hvw := v.2.trans hn
  by_cases he : u = v
  · subst v
    have hc : (Expr.op .eq (.reg 66) (.reg 67)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrv, huw, hw]
    have hi : u.1 < (s.arrs 33).length := by rw [hloop, List.length_ofFn]; exact u.2
    have hg : (s.arrs 33)[u.1]'hi = case3OrderedLoopLabel x Z u := by
      simp only [hloop, List.getElem_ofFn]
    have hlw := (case3OrderedLoopLabel_lt x Z hdiv u).trans hsize
    have hv : (Expr.read 33 (.reg 66)).eval w s = some (case3OrderedLoopLabel x Z u) := by
      simp [Expr.eval, checkWord, hru, huw, hi, hg, hlw]
    rw [case3PairOwner_loop]
    exact ⟨6, .ite_true hc (by decide) (.assign hv), by decide⟩
  · have hadj : x.G.Adj u v := hvalid.resolve_left he
    have hne : u.1 ≠ v.1 := fun h => he (Fin.ext h)
    have hc : (Expr.op .eq (.reg 66) (.reg 67)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrv, huw, hvw, hne, h0]
    have hpos := (case3PairPosition_lt u v).trans hsquare
    have hmul : u.1 * x.n < 2 ^ w := by dsimp only [case3PairPosition] at hpos; omega
    have hi : case3PairPosition u v < (s.arrs 34).length := by
      rw [hmat, case3EdgeMatrixPrefix_length]
      exact case3PairPosition_lt u v
    have hg : (s.arrs 34)[case3PairPosition u v]'hi = case3PairOwner x Z u v := by
      have hh : (s.arrs 34).getD (case3PairPosition u v) 0 = case3PairOwner x Z u v := by
        simp only [hmat, case3PairOwner, he, ↓reduceIte]
      simpa only [List.getD_eq_getElem _ 0 hi] using hh
    have hlw := (case3PairOwner_lt_of_adj x Z u v hadj).trans hsize
    have hv : (Expr.read 34 (.op .add (.op .mul (.reg 66) (.reg 14)) (.reg 67))).eval w s =
        some (case3PairOwner x Z u v) := by
      dsimp only [case3PairPosition] at hpos hi hg
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrv, hrn,
        huw, hvw, hn, hmul, hpos, hi, hg, hlw]
    exact ⟨10, .ite_false hc (.assign hv), by decide⟩

end GraphMinor.Compute
