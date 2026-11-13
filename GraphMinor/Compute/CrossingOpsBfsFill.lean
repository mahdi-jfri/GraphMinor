module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Filling parent arrays with a dynamic sentinel

The sentinel is the array length, read from memory. Filling by that value prepares a
parent array for a search without specializing the command to the number of vertices.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Fill an array with its length. Both the bound and the value are read from memory. -/
def fillLengthProg (a r : ℕ) : Cmd := fillArr a (.len a) (.len a) r

/-- Filling with the array length costs at most five plus ten times its length. -/
theorem fillLengthProg_exec {w N : ℕ} (a r : ℕ) {s : State}
    (hlen : (s.arrs a).length = N) (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (fillLengthProg a r) s s' t ∧ t ≤ 5 + 10 * N ∧
      s'.arrs a = List.replicate N N ∧
      (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → s'.regs q = s.regs q) := by
  let I (i : ℕ) (z : State) : Prop := z.regs r = i ∧ (z.arrs a).length = N ∧
    ∀ j (hj : j < (z.arrs a).length), j < i → (z.arrs a)[j] = N
  have h0 : I 0 (s.setReg r 0) := ⟨by simp, hlen, fun _ _ h => by omega⟩
  obtain ⟨s', t, he, ht, hI⟩ := Triple.forUp_const I N 3 (r_i := r) (hi := .len a)
    (body := .write a (.reg r) (.len a)) hw hN
    (fun i _ z h => ⟨h.1, by simp [Expr.eval, checkWord, h.2.1, hN]⟩)
    (fun i hi z h => by
      let z' := z.writeArr a i N
      have hlen' : (z'.arrs a).length = N := by simp [z', h.2.1]
      refine ⟨z', 3, .write (eval_reg h.1 (by omega))
        (by simp [Expr.eval, checkWord, h.2.1, hN]) (by omega), le_rfl, ?_, ?_⟩
      · refine ⟨by simp, hlen', ?_⟩
        intro j hj hji
        simp only [State.setReg_arrs, z', State.writeArr_arrs_self, List.getElem_set]
        by_cases heq : i = j
        · simp [heq]
        · simp only [heq, ite_false]
          exact h.2.2 j (by omega) (by omega)
      · simpa [z'] using h.1)
    (s.setReg r 0) h0
  refine ⟨s', 2 + t, .seq (.assign (eval_const (by omega))) he, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · exact List.ext_getElem (by simp [hI.2.1]) (fun j hj hj' => by
      rw [List.getElem_replicate]; exact hI.2.2 j hj (by omega))
  · intro b hba
    exact he.arrs_eq_of_not_mem_writtenArrs (by simp [forUp, Cmd.writtenArrs, hba])
  · intro q hqr
    have hh := he.regs_eq_of_not_mem_writtenRegs (r := q)
      (by simp [forUp, Cmd.writtenRegs, hqr])
    simpa [State.setReg_regs, hqr] using hh

end GraphMinor.Compute.Crossing
