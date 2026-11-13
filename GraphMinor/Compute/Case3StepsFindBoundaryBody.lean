module

public import GraphMinor.Compute.Case3StepsFirstIndex

/-!
# One iteration of the boundary search

While the result is the missing sentinel, the program compares the selected
component with the target boundary. The first successful comparison stores
its seed. Later iterations retain that result.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Retain the first matching outside-component seed. -/
def case3FindBoundaryBody (a_Z a_keys a_target r_n r_i r_res : ℕ) : Cmd :=
  .ite (.op .eq (.reg r_res) (.reg r_n))
    (.ite (case3BoundaryMatchExpr a_Z a_keys a_target r_i) (.assign r_res (.reg r_i)) .skip)
    .skip

/-- A search iteration changes only the result register and takes at most
49 steps, independent of the graph size. -/
theorem case3FindBoundaryBody_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (bd : Finset (Fin x.n)) (hbd : bd.card ≤ 3)
    (a_Z a_keys a_target r_n r_i r_res : ℕ)
    (hw : 4 < 2 ^ w) (hn : x.n < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (k r : ℕ) (hk : k < x.n) (hr : r ≤ x.n) {s : State}
    (hZ : IsBitSet d.core.Z a_Z s) (htab : s.arrs a_keys = case3AttachmentKeys x d.core.Z)
    (htarget : s.arrs a_target = case3BoundaryKey bd)
    (hrn : s.regs r_n = x.n) (hri : s.regs r_i = k) (hrres : s.regs r_res = r) :
    ∃ s' t, Exec w (case3FindBoundaryBody a_Z a_keys a_target r_n r_i r_res) s s' t ∧
      t ≤ 49 ∧ s'.regs r_res =
        (if r = x.n ∧ (⟨k, hk⟩ : Fin x.n) ∉ d.core.Z ∧
          case3AttachmentRowSet x d.core.Z ⟨k, hk⟩ = bd then k else r) ∧
      (∀ a, s'.arrs a = s.arrs a) ∧ (∀ q, q ≠ r_res → s'.regs q = s.regs q) := by
  classical
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hrw : r < 2 ^ w := hr.trans_lt hn
  have hkw : k < 2 ^ w := hk.trans hn
  by_cases hrn' : r = x.n
  · have hc : (Expr.op .eq (.reg r_res) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrres, hrn, hrn', hn, h1]
    have hmatch := case3BoundaryMatchExpr_eval x d hd bd hbd ⟨k, hk⟩
      a_Z a_keys a_target r_i hw hn hkeys hZ htab htarget hri
    by_cases hP : (⟨k, hk⟩ : Fin x.n) ∉ d.core.Z ∧ case3AttachmentRowSet x d.core.Z ⟨k, hk⟩ = bd
    · have hm : (case3BoundaryMatchExpr a_Z a_keys a_target r_i).eval w s = some 1 := by
        simpa [hP] using hmatch
      have ha : Exec w (.assign r_res (.reg r_i)) s (s.setReg r_res k) 2 :=
        .assign (by simp only [Expr.eval, checkWord, hri, hkw, ↓reduceIte])
      refine ⟨s.setReg r_res k, 49, .ite_true (t := 46) hc (by decide)
        (.ite_true (t := 2) hm (by decide) ha), by omega, ?_, fun _ => rfl, ?_⟩
      · simp [State.setReg_regs_self, hrn', hP.1, hP.2]
      · intro q hq
        exact State.setReg_regs_ne _ _ hq
    · have hm : (case3BoundaryMatchExpr a_Z a_keys a_target r_i).eval w s = some 0 := by
        simpa [hP] using hmatch
      refine ⟨s, 48, .ite_true (t := 45) hc (by decide)
        (.ite_false (t := 1) hm (.skip s)), by omega, ?_, fun _ => rfl, fun _ _ => rfl⟩
      simpa [hrn', hP] using hrres
  · have hc : (Expr.op .eq (.reg r_res) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrres, hrn, hrn', hrw, hn, h0]
    refine ⟨s, 4, .ite_false (t := 1) hc (.skip s), by omega, ?_, fun _ => rfl, fun _ _ => rfl⟩
    simpa only [hrn', false_and, ↓reduceIte] using hrres

end GraphMinor.Compute
