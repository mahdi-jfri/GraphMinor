module

public import GraphMinor.Compute.GM06DartMate

/-!
# Deleting an edge while retaining its directed labels

The cylinder reduction scans retain the original edge labels. Deleting
an edge sets its activity flag to zero. Both directed ends index that
same flag, so no boundary walk or rotation needs to be renumbered.
This file verifies the constant-time RAM update.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Delete the edge containing the directed end in register 23. -/
def gm06DeleteEdgeProg (active : Arr) : Cmd :=
  .write active (.op .div (.reg 23) (.const 2)) (.const 0)

/-- Setting the activity flag to zero takes exactly five RAM steps. -/
theorem gm06DeleteEdgeProg_exec {w j : ℕ} (active : ℕ) (mask : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : 2 * mask.length < 2 ^ w)
    (hj : j < 2 * mask.length) (ha : s.arrs active = mask) (hr : s.regs 23 = j) :
    Exec w (gm06DeleteEdgeProg active) s (s.writeArr active (j / 2) 0) 5 := by
  have hjw : j < 2 ^ w := hj.trans hn
  have hid : j / 2 < 2 ^ w := (Nat.div_le_self j 2).trans_lt hjw
  have hi : j / 2 < (s.arrs active).length := by rw [ha]; omega
  have he : (Expr.op .div (.reg 23) (.const 2)).eval w s = some (j / 2) := by
    simp [Expr.eval, hr, checkWord, hjw, hw, BinOp.eval, BinOp.raw, hid]
  exact .write he (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)) hi

/-- The two directed ends see the same deleted flag. -/
theorem gm06DeletedEdge_mate_flag {j : ℕ} {mask : List ℕ}
    (hj : j < 2 * mask.length) :
    (mask.set (j / 2) 0)[gm06DartMate j / 2]? = some 0 := by
  rw [gm06DartMate_edge]
  have hi : j / 2 < mask.length := by omega
  have hi' : j / 2 < (mask.set (j / 2) 0).length := by simpa only [List.length_set] using hi
  rw [List.getElem?_eq_getElem hi']
  exact congrArg some (List.getElem_set_self hi')

/-- Deleting an edge preserves every register and all other arrays. -/
theorem gm06DeletedEdge_frame (s : State) (active j : ℕ) :
    (∀ r, (s.writeArr active (j / 2) 0).regs r = s.regs r) ∧
      (∀ a, a ≠ active → (s.writeArr active (j / 2) 0).arrs a = s.arrs a) := by
  exact ⟨fun _ => by simp, fun a ha => State.writeArr_arrs_ne _ _ _ ha⟩

end GraphMinor.Compute
