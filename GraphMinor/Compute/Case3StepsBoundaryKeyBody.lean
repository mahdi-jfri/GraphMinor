module

public import GraphMinor.Compute.Case3StepsBoundaryKeys

/-!
# Filling one boundary-key slot

The boundary scan writes the current vertex in the next slot when its bit is
set, and then advances the count. There are at most three such writes.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Count and append a present vertex; leave the key unchanged otherwise. -/
def case3BoundaryKeyBody (a_set a_key r_i r_cnt : ℕ) : Cmd :=
  .ite (.read a_set (.reg r_i))
    (.seq (.write a_key (.op .add (.reg r_cnt) (.const 1)) (.reg r_i))
      (.assign r_cnt (.op .add (.reg r_cnt) (.const 1)))) .skip

/-- One scan iteration produces the next partial key and collected count. -/
theorem case3BoundaryKeyBody_exec {w n : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (a_set a_key r_i r_cnt : ℕ) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (k : ℕ) (hk : k < n) {s : State} (hset : IsBitSet S a_set s)
    (hkey : s.arrs a_key = case3BoundaryKeyPrefix S k)
    (hri : s.regs r_i = k) (hrcnt : s.regs r_cnt = (case3BoundaryPrefix S k).length) :
    ∃ s' t, Exec w (case3BoundaryKeyBody a_set a_key r_i r_cnt) s s' t ∧
      t ≤ 12 ∧ s'.arrs a_key = case3BoundaryKeyPrefix S (k + 1) ∧
      s'.regs r_cnt = (case3BoundaryPrefix S (k + 1)).length ∧
      (∀ a, a ≠ a_key → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_cnt → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hkw : k < 2 ^ w := hk.trans hn
  have hidx : k < (s.arrs a_set).length := by rw [hset.1]; exact hk
  have hbit : (s.arrs a_set)[k]'hidx = if (⟨k, hk⟩ : Fin n) ∈ S then 1 else 0 := by
    simpa only [hset.arr_eq_bitSetList] using getElem_bitSetList S k hk
  by_cases hmem : (⟨k, hk⟩ : Fin n) ∈ S
  · have hc : (Expr.read a_set (.reg r_i)).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hri, hkw, hidx, hbit, hmem, h1]
    have hcount : (case3BoundaryPrefix S k).length < 3 := by
      have hle := (case3BoundaryPrefix_length_le S (k + 1)).trans hS
      rw [case3BoundaryPrefix_succ S k hk] at hle
      simp only [hmem, ↓reduceIte, List.length_append, List.length_singleton] at hle
      omega
    have hcw : (case3BoundaryPrefix S k).length < 2 ^ w := by omega
    have hcpw : (case3BoundaryPrefix S k).length + 1 < 2 ^ w := by omega
    let s₁ := s.writeArr a_key ((case3BoundaryPrefix S k).length + 1) k
    let s₂ := s₁.setReg r_cnt ((case3BoundaryPrefix S k).length + 1)
    have hex₁ : Exec w (.write a_key (.op .add (.reg r_cnt) (.const 1)) (.reg r_i)) s s₁ 5 :=
      .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrcnt, hcw, h1, hcpw])
        (by simp only [Expr.eval, checkWord, hri, hkw, ↓reduceIte])
        (by rw [hkey, case3BoundaryKeyPrefix_length S hS k]; omega)
    have hex₂ : Exec w (.assign r_cnt (.op .add (.reg r_cnt) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hrcnt, hcw, h1, hcpw])
    refine ⟨s₂, 11, .ite_true (t := 9) hc (by decide) (.seq hex₁ hex₂), by omega, ?_, ?_, ?_, ?_⟩
    · simp only [s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hkey,
        case3BoundaryKeyPrefix_set S hS k hk hmem]
    · rw [show s₂.regs r_cnt = (case3BoundaryPrefix S k).length + 1 from State.setReg_regs_self ..,
        case3BoundaryPrefix_succ S k hk]
      simp only [hmem, ↓reduceIte, List.length_append, List.length_singleton]
    · intro a ha
      exact State.writeArr_arrs_ne _ _ _ ha
    · intro r hr
      rw [State.setReg_regs_ne _ _ hr]
      rfl
  · have hc : (Expr.read a_set (.reg r_i)).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hri, hkw, hidx, hbit, hmem, h0]
    refine ⟨s, 3, .ite_false (t := 1) hc (.skip s), by omega, ?_, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    · rw [case3BoundaryKeyPrefix_skip S k hk hmem]
      exact hkey
    · rw [case3BoundaryPrefix_succ S k hk]
      simpa only [hmem, ↓reduceIte, List.append_nil] using hrcnt

end GraphMinor.Compute
