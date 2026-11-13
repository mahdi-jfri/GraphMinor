module

public import GraphMinor.Compute.Case3StepsBranchCodeSlices
public import GraphMinor.Compute.Case3StepsBranchSliceProg

/-!
# Copying the branch-code leaf list

The leaf words follow the parent words in the supplied (7.2) output. They
are copied without reordering to match the expanded directed-copy list of
the member record, including the zero words used for small graphs.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Copy the leaf section to array 49 using the raw tree and edge counts. -/
def case3BranchLeavesProg : Cmd :=
  .seq (.assign 112 (.reg 111))
    (.seq (.assign 114 (.op .add (.const 3) (.reg 115))) (case3BranchSliceProg 49))

/-- The leaf record is exactly the supplied branch code's final section,
and the tree-size registers and parent array are retained. -/
theorem case3BranchLeavesProg_exec {w n B : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (hw : 3 < 2 ^ w)
    (hlen : (0 :: code).length < 2 ^ w) (hwords : ∀ x ∈ code, x < 2 ^ w)
    {s : State} (hsrc : s.arrs 129 = 0 :: code)
    (hrt : s.regs 115 = bdNumTreeVerts code) (hrm : s.regs 111 = G.numEdges) :
    ∃ s' t, Exec w case3BranchLeavesProg s s' t ∧ t ≤ 18 * G.numEdges + 16 ∧
      s'.arrs 49 = (case3BranchRecord G f g code).tauList ∧
      (∀ a, a ≠ 49 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 112 → r ≠ 114 → r < 120 ∨ 123 < r → s'.regs r = s.regs r) := by
  have hs := case3BranchCode_slices G code hcode
  have hcodelen : code.length = 2 + bdNumTreeVerts code + G.numEdges := by
    simpa only [hcode.1] using hcode.2.2.1
  have htw : bdNumTreeVerts code < 2 ^ w := by simp only [List.length_cons] at hlen; omega
  have hmw : G.numEdges < 2 ^ w := by simp only [List.length_cons] at hlen; omega
  have hoff : 3 + bdNumTreeVerts code < 2 ^ w := by simp only [List.length_cons] at hlen; omega
  let s₁ := s.setReg 112 G.numEdges
  let s₂ := s₁.setReg 114 (3 + bdNumTreeVerts code)
  have hex₁ : Exec w (.assign 112 (.reg 111)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hrm, hmw, ↓reduceIte])
  have hex₂ : Exec w (.assign 114 (.op .add (.const 3) (.reg 115))) s₁ s₂ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁,
      hrt, hw, htw, hoff])
  let par := (code.drop 2).take (bdNumTreeVerts code)
  let leaves := code.drop (2 + bdNumTreeVerts code)
  obtain ⟨s₃, t₃, hex₃, ht₃, hdst₃, harr₃, hreg₃⟩ := case3BranchSliceProg_exec (w := w) 49 (by decide)
    ([0, bdNumTreeVerts code, G.numEdges] ++ par) leaves [] (by omega)
    (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      rw [show par.length = bdNumTreeVerts code from hs.2.1, show leaves.length = G.numEdges from hs.2.2]
      simp only [List.length_cons] at hlen
      omega)
    (by intro x hx; exact hwords x (List.mem_of_mem_drop hx))
    (s := s₂)
    (by simpa only [s₂, s₁, State.setReg_arrs, hsrc, par, leaves, List.append_nil,
      List.cons_append, List.nil_append, List.append_assoc] using congrArg (List.cons 0) hs.1)
    (by rw [State.setReg_regs_ne _ _ (show (112 : ℕ) ≠ 114 by decide), State.setReg_regs_self]; exact hs.2.2.symm)
    (by simp only [s₂, State.setReg_regs_self, List.length_append, List.length_cons, List.length_nil]
        rw [show par.length = bdNumTreeVerts code from hs.2.1])
  refine ⟨s₃, 2 + (4 + t₃), .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, ?_, ?_⟩
  · rw [show leaves.length = G.numEdges from hs.2.2] at ht₃
    omega
  · exact hdst₃.trans (case3BranchRecord_tau_slice G f g code hcode).symm
  · intro a ha
    exact harr₃ a ha
  · intro r h112 h114 hr
    rw [hreg₃ r hr, State.setReg_regs_ne _ _ h114, State.setReg_regs_ne _ _ h112]

end GraphMinor.Compute
