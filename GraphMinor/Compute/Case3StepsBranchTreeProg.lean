module

public import GraphMinor.Compute.Case3StepsBranchParentsProg
public import GraphMinor.Compute.Case3StepsBranchLeavesProg

/-!
# Computing the branch record's tree sections

The program reads the tree and edge counts from the tagged (7.2) output,
normalizes the small-graph parent tree, and copies both tree sections.
The code's tree-size bound gives linear time in the member's edge count.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Read the branch code's counts and compute parent and leaf arrays. -/
def case3BranchTreeProg : Cmd :=
  .seq (.assign 115 (.read 129 (.const 1)))
    (.seq (.assign 111 (.read 129 (.const 2)))
      (.seq case3BranchParentsProg case3BranchLeavesProg))

/-- The two record sections and their counts are computed in at most
`54 m + 39` steps, preserving the graph and vertex-list data. -/
theorem case3BranchTreeProg_exec {w n B : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (hw : 3 < 2 ^ w)
    (hlen : (0 :: code).length < 2 ^ w) (hwords : ∀ x ∈ code, x < 2 ^ w)
    {s : State} (hsrc : s.arrs 129 = 0 :: code) :
    ∃ s' t, Exec w case3BranchTreeProg s s' t ∧ t ≤ 54 * G.numEdges + 39 ∧
      s'.arrs 48 = (case3BranchRecord G f g code).parList ∧
      s'.arrs 49 = (case3BranchRecord G f g code).tauList ∧
      s'.regs 102 = (case3BranchRecord G f g code).t_len ∧ s'.regs 111 = G.numEdges ∧
      (∀ a, a ≠ 48 → a ≠ 49 → s'.arrs a = s.arrs a) ∧
      (∀ r < 102, s'.regs r = s.regs r) := by
  have hs := case3BranchCode_slices G code hcode
  have hcodelen : code.length = 2 + bdNumTreeVerts code + G.numEdges := by
    simpa only [hcode.1] using hcode.2.2.1
  have htw : bdNumTreeVerts code < 2 ^ w := by simp only [List.length_cons] at hlen; omega
  have hmw : G.numEdges < 2 ^ w := by simp only [List.length_cons] at hlen; omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hsplit : s.arrs 129 =
      [0, bdNumTreeVerts code, G.numEdges] ++ (code.drop 2).take (bdNumTreeVerts code) ++
        code.drop (2 + bdNumTreeVerts code) := by
    rw [hsrc]
    exact congrArg (List.cons 0) hs.1
  let s₁ := s.setReg 115 (bdNumTreeVerts code)
  let s₂ := s₁.setReg 111 G.numEdges
  have hex₁ : Exec w (.assign 115 (.read 129 (.const 1))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hsplit, h1, htw])
  have hex₂ : Exec w (.assign 111 (.read 129 (.const 2))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁, hsplit, h2, hmw])
  obtain ⟨s₃, t₃, hex₃, ht₃, hpar₃, htree₃, harr₃, hreg₃⟩ :=
    case3BranchParentsProg_exec G f g code hcode hw hlen hwords (s := s₂) hsrc
      (by rw [State.setReg_regs_ne _ _ (show (115 : ℕ) ≠ 111 by decide), State.setReg_regs_self])
  obtain ⟨s₄, t₄, hex₄, ht₄, htau₄, harr₄, hreg₄⟩ :=
    case3BranchLeavesProg_exec G f g code hcode hw hlen hwords (s := s₃)
      ((harr₃ 129 (by decide)).trans hsrc)
      (by rw [hreg₃ 115 (by decide) (by decide) (by decide) (by decide),
          State.setReg_regs_ne _ _ (show (115 : ℕ) ≠ 111 by decide), State.setReg_regs_self])
      (by rw [hreg₃ 111 (by decide) (by decide) (by decide) (by decide), State.setReg_regs_self])
  have hex : Exec w case3BranchTreeProg s s₄ (3 + (3 + (t₃ + t₄))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, 3 + (3 + (t₃ + t₄)), hex, ?_, ?_, htau₄, ?_, ?_, ?_, ?_⟩
  · have htle : bdNumTreeVerts code ≤ 2 * G.numEdges := by simpa only [hcode.1] using hcode.2.1
    omega
  · exact (harr₄ 48 (by decide)).trans hpar₃
  · exact (hreg₄ 102 (by decide) (by decide) (by decide)).trans htree₃
  · rw [hreg₄ 111 (by decide) (by decide) (by decide),
      hreg₃ 111 (by decide) (by decide) (by decide) (by decide), State.setReg_regs_self]
  · intro a h48 h49
    exact (harr₄ a h49).trans (harr₃ a h48)
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3BranchTreeProg, case3BranchParentsProg, case3BranchLeavesProg, case3BranchSliceProg,
        writeSliceProg, writeSliceBody, forUp, Cmd.writtenRegs]
      dsimp only [Reg] at *
      omega)

end GraphMinor.Compute
