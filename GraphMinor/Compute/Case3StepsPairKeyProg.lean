module

public import GraphMinor.Compute.Case3StepsPairKey

/-!
# Writing a core-edge boundary key

The ordered endpoints of a canonical simple edge give its four-word boundary
key directly. Three writes after allocation supply its size and endpoints,
while the padding word remains zero.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Write the key of a canonical edge from its endpoint registers. -/
def case3PairKeyProg (a_key r_u r_v : ℕ) : Cmd :=
  .seq (.alloc a_key (.const 4))
    (.seq (.write a_key (.const 0) (.const 2))
      (.seq (.write a_key (.const 1) (.reg r_u)) (.write a_key (.const 2) (.reg r_v))))

/-- The target key of a core edge is written in fourteen steps. No register
or other array changes. -/
theorem case3PairKeyProg_exec {w n : ℕ} (u v : Fin n) (huv : u < v)
    (a_key r_u r_v : ℕ) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    {s : State} (hru : s.regs r_u = u.1) (hrv : s.regs r_v = v.1) :
    ∃ s', Exec w (case3PairKeyProg a_key r_u r_v) s s' 14 ∧
      s'.arrs a_key = case3BoundaryKey ({u, v} : Finset (Fin n)) ∧
      (∀ a, a ≠ a_key → s'.arrs a = s.arrs a) ∧ (∀ r, s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have huw : u.1 < 2 ^ w := u.2.trans hn
  have hvw : v.1 < 2 ^ w := v.2.trans hn
  let s₁ := s.setArr a_key (List.replicate 4 0)
  let s₂ := s₁.writeArr a_key 0 2
  let s₃ := s₂.writeArr a_key 1 u.1
  let s₄ := s₃.writeArr a_key 2 v.1
  have hex₁ : Exec w (.alloc a_key (.const 4)) s s₁ 5 :=
    .alloc (by simp only [Expr.eval, checkWord, hw, ↓reduceIte])
  have hex₂ : Exec w (.write a_key (.const 0) (.const 2)) s₁ s₂ 3 :=
    .write (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
      (by simp only [Expr.eval, checkWord, h2, ↓reduceIte])
      (by simp only [s₁, State.setArr_arrs_self, List.length_replicate]; omega)
  have hex₃ : Exec w (.write a_key (.const 1) (.reg r_u)) s₂ s₃ 3 :=
    .write (by simp only [Expr.eval, checkWord, h1, ↓reduceIte])
      (by simp only [Expr.eval, checkWord, s₂, s₁, State.writeArr_regs, State.setArr_regs,
        hru, huw, ↓reduceIte])
      (by simp only [s₂, s₁, State.writeArr_arrs_self, List.length_set,
        State.setArr_arrs_self, List.length_replicate]; omega)
  have hex₄ : Exec w (.write a_key (.const 2) (.reg r_v)) s₃ s₄ 3 :=
    .write (by simp only [Expr.eval, checkWord, h2, ↓reduceIte])
      (by simp only [Expr.eval, checkWord, s₃, s₂, s₁, State.writeArr_regs, State.setArr_regs,
        hrv, hvw, ↓reduceIte])
      (by simp only [s₃, s₂, s₁, State.writeArr_arrs_self, List.length_set,
        State.setArr_arrs_self, List.length_replicate]; omega)
  have hex : Exec w (case3PairKeyProg a_key r_u r_v) s s₄ 14 :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, hex, ?_, ?_, ?_⟩
  · rw [case3BoundaryKey_pair u v huv]
    simp only [s₄, s₃, s₂, s₁, State.writeArr_arrs_self, State.setArr_arrs_self]
    rfl
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3PairKeyProg, Cmd.writtenArrs, ha])
  · intro r
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [case3PairKeyProg, Cmd.writtenRegs])

end GraphMinor.Compute
