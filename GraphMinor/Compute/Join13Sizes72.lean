module

public import GraphMinor.Compute.Join13BDSlice72
public import GraphMinor.Compute.TwoPathsRotate

/-!
# Reading the graph and decomposition sizes

The (7.2) adapter reads its three sizes from the caller's graph and valid
branch-decomposition codes. The graph edge count comes from the decomposition
header, so no additional pass over the graph is needed.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read vertex, edge, and tree counts into the core preparation registers. -/
def initializeSizes72Prog : Cmd :=
  .seq (.assign 26 (.read 12 (.const 0)))
    (.seq (.assign 28 (.read 13 (.const 1)))
      (.assign 52 (.read 13 (.const 0))))

/-- Valid input headers give the graph's actual sizes. -/
theorem initializeSizes72Prog_exec {w n B : ℕ} (G : MultiDigraph n)
    (bdCode : List ℕ) (hbd : IsValidBranchDecompCode B G bdCode) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hm : G.numEdges < 2 ^ w)
    (ht : bdNumTreeVerts bdCode < 2 ^ w)
    (hG : s.arrs 12 = G.enc) (hBD : s.arrs 13 = bdCode) :
    ∃ s' t, Exec w initializeSizes72Prog s s' t ∧ t = 9 ∧
      s'.regs 26 = n ∧ s'.regs 28 = G.numEdges ∧
      s'.regs 52 = bdNumTreeVerts bdCode ∧ Keeps [26, 28, 52] [] s s' := by
  have h0 : 0 < 2 ^ w := by omega
  have hlen : bdCode.length = 2 + bdNumTreeVerts bdCode + G.numEdges := by
    rw [← hbd.1]
    exact hbd.2.2.1
  let s₁ := s.setReg 26 n
  have he₁ : Exec w (.assign 26 (.read 12 (.const 0))) s s₁ 3 := by
    apply Exec.assign
    simp [Expr.eval, checkWord, hG, MultiDigraph.enc, h0, hn]
  let s₂ := s₁.setReg 28 G.numEdges
  have he₂ : Exec w (.assign 28 (.read 13 (.const 1))) s₁ s₂ 3 := by
    apply Exec.assign
    have hl : 1 < (s₁.arrs 13).length := by simp only [s₁, State.setReg_arrs, hBD, hlen]; omega
    have hg : (s₁.arrs 13)[1]'hl = G.numEdges := by
      rw [← List.getD_eq_getElem (d := 0) _ hl]
      change bdNumGraphEdges (s₁.arrs 13) = G.numEdges
      simpa [s₁, hBD] using hbd.1
    simp [Expr.eval, checkWord, hw, hl, hg, hm]
  let s₃ := s₂.setReg 52 (bdNumTreeVerts bdCode)
  have he₃ : Exec w (.assign 52 (.read 13 (.const 0))) s₂ s₃ 3 := by
    apply Exec.assign
    have hl : 0 < (s₂.arrs 13).length := by simp [s₂, s₁, hBD, hlen]
    have hg : (s₂.arrs 13)[0]'hl = bdNumTreeVerts bdCode := by
      rw [← List.getD_eq_getElem (d := 0) _ hl]
      simp [s₂, s₁, hBD, bdNumTreeVerts]
    simp [Expr.eval, checkWord, h0, hl, hg, ht]
  refine ⟨s₃, 9, .seq he₁ (.seq he₂ he₃), rfl, ?_, ?_, ?_, ?_⟩
  · simp [s₃, s₂, s₁]
  · simp [s₃, s₂]
  · simp [s₃]
  · constructor
    · intro j hj
      simp only [List.mem_cons, not_or] at hj
      simp [s₃, s₂, s₁, hj.1, hj.2.1, hj.2.2]
    · intro a _
      simp [s₃, s₂, s₁]

end GraphMinor.Compute
