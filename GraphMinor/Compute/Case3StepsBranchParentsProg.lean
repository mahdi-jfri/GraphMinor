module

public import GraphMinor.Compute.Case3StepsBranchCodeSlices
public import GraphMinor.Compute.Case3StepsBranchSliceProg

/-!
# Copying the branch-code parent list

A nonempty parent tree is copied from the returned code. For the paper's
at-most-one-edge convention, the record instead uses a one-vertex tree with
parent zero. Both cases produce exactly the parent section of the record.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Normalize the tree size and write its parent list at array 48. -/
def case3BranchParentsProg : Cmd :=
  .ite (.reg 115)
    (.seq (.assign 102 (.reg 115))
      (.seq (.assign 112 (.reg 115))
        (.seq (.assign 114 (.const 3)) (case3BranchSliceProg 48))))
    (.seq (.assign 102 (.const 1)) (.alloc 48 (.const 1)))

/-- The copied or one-vertex parent list is exactly the branch record's
parent list. Register 102 holds the normalized tree size. -/
theorem case3BranchParentsProg_exec {w n B : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (hw : 3 < 2 ^ w)
    (hlen : (0 :: code).length < 2 ^ w) (hwords : ∀ x ∈ code, x < 2 ^ w)
    {s : State} (hsrc : s.arrs 129 = 0 :: code) (hrt : s.regs 115 = bdNumTreeVerts code) :
    ∃ s' t, Exec w case3BranchParentsProg s s' t ∧ t ≤ 18 * bdNumTreeVerts code + 17 ∧
      s'.arrs 48 = (case3BranchRecord G f g code).parList ∧
      s'.regs 102 = (case3BranchRecord G f g code).t_len ∧
      (∀ a, a ≠ 48 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 102 → r ≠ 112 → r ≠ 114 → r < 120 ∨ 123 < r → s'.regs r = s.regs r) := by
  have hs := case3BranchCode_slices G code hcode
  have hcodelen : code.length = 2 + bdNumTreeVerts code + G.numEdges := by
    simpa only [hcode.1] using hcode.2.2.1
  have h1 : 1 < 2 ^ w := by omega
  have htw : bdNumTreeVerts code < 2 ^ w := by simp only [List.length_cons] at hlen; omega
  have htest : (Expr.reg 115).eval w s = some (bdNumTreeVerts code) := by
    simp only [Expr.eval, checkWord, hrt, htw, ↓reduceIte]
  by_cases ht : 0 < bdNumTreeVerts code
  · let s₁ := s.setReg 102 (bdNumTreeVerts code)
    let s₂ := s₁.setReg 112 (bdNumTreeVerts code)
    let s₃ := s₂.setReg 114 3
    have hex₁ : Exec w (.assign 102 (.reg 115)) s s₁ 2 := .assign htest
    have hex₂ : Exec w (.assign 112 (.reg 115)) s₁ s₂ 2 :=
      .assign (by simp only [Expr.eval, checkWord, s₁, State.setReg_regs_ne _ _ (show (115 : ℕ) ≠ 102 by decide), hrt, htw, ↓reduceIte])
    have hex₃ : Exec w (.assign 114 (.const 3)) s₂ s₃ 2 :=
      .assign (by simp only [Expr.eval, checkWord, hw, ↓reduceIte])
    let par := (code.drop 2).take (bdNumTreeVerts code)
    let leaves := code.drop (2 + bdNumTreeVerts code)
    obtain ⟨s₄, t₄, hex₄, ht₄, hpar₄, harr₄, hreg₄⟩ := case3BranchSliceProg_exec 48 (by decide)
      [0, bdNumTreeVerts code, G.numEdges] par leaves h1
      (by simp only [List.length_cons, List.length_nil, hs.2.1, par] at *; omega)
      (by intro x hx; exact hwords x (List.mem_of_mem_drop (List.mem_of_mem_take hx)))
      (s := s₃)
      (by simpa only [s₃, s₂, s₁, State.setReg_arrs, hsrc, par, leaves,
        List.cons_append, List.nil_append, List.append_assoc] using congrArg (List.cons 0) hs.1)
      (by rw [State.setReg_regs_ne _ _ (show (112 : ℕ) ≠ 114 by decide), State.setReg_regs_self]; exact hs.2.1.symm)
      (by simp only [s₃, State.setReg_regs_self, List.length_cons, List.length_nil])
    have hex : Exec w case3BranchParentsProg s s₄ (1 + (2 + (2 + (2 + t₄)))) :=
      .ite_true htest (by omega) (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)))
    refine ⟨s₄, 1 + (2 + (2 + (2 + t₄))), hex, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show par.length = bdNumTreeVerts code from hs.2.1] at ht₄
      omega
    · exact hpar₄.trans (case3BranchRecord_parent_slice G f g code hcode ht).symm
    · rw [hreg₄ 102 (by decide), State.setReg_regs_ne _ _ (show (102 : ℕ) ≠ 114 by decide),
        State.setReg_regs_ne _ _ (show (102 : ℕ) ≠ 112 by decide), State.setReg_regs_self]
      exact (Nat.max_eq_left ht).symm
    · intro a ha
      exact harr₄ a ha
    · intro r h102 h112 h114 hr
      rw [hreg₄ r hr, State.setReg_regs_ne _ _ h114, State.setReg_regs_ne _ _ h112,
        State.setReg_regs_ne _ _ h102]
  · have ht0 : bdNumTreeVerts code = 0 := by omega
    let s₁ := s.setReg 102 1
    let s₂ := s₁.setArr 48 [0]
    have hex₁ : Exec w (.assign 102 (.const 1)) s s₁ 2 :=
      .assign (by simp only [Expr.eval, checkWord, h1, ↓reduceIte])
    have hex₂ : Exec w (.alloc 48 (.const 1)) s₁ s₂ 2 :=
      .alloc (m := 1) (by simp only [Expr.eval, checkWord, h1, ↓reduceIte])
    have hex : Exec w case3BranchParentsProg s s₂ 5 :=
      .ite_false (ht0 ▸ htest) (.seq hex₁ hex₂)
    refine ⟨s₂, 5, hex, by omega, ?_, ?_, ?_, ?_⟩
    · simp only [s₂, State.setArr_arrs_self, case3BranchRecord, ht0, Nat.zero_max,
        List.ofFn_succ, List.ofFn_zero, Nat.not_lt_zero, ↓reduceIte]
    · simp only [s₂, s₁, State.setArr_regs, State.setReg_regs_self, case3BranchRecord, ht0, Nat.zero_max]
    · intro a ha
      exact State.setArr_arrs_ne _ _ ha
    · intro r h102 _ _ _
      exact State.setReg_regs_ne _ _ h102

end GraphMinor.Compute
