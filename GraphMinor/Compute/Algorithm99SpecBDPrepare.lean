module

public import GraphMinor.Compute.Algorithm99SpecBDWritten
public import GraphMinor.Compute.Algorithm99State
import GraphMinor.Compute.Algorithm72

/-!
# Preparing the decomposition branch of Algorithm (9.9)

The branch removes the output tag, reads the two code-header words, and splits
the parent and leaf arrays. The leaf array still has active-pair edge order.
The following stage changes only that order.
-/

@[expose] public section
namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Read the code and its header, then extract parent and leaf words. -/
def alg99PrepareBDProg : Cmd :=
  .seq (copyTailProg outArr 10 80 81)
    (.seq (.assign 28 (.read 10 (.const 1)))
      (.seq (.assign 30 (.read 10 (.const 0)))
        (prepareBD72Prog 10 2 13 28 30 80)))

/-- Code extraction takes linear time. It leaves the effective tree size in
register 30, the edge count in register 28, parents in array 2 and leaves in
array 13. -/
theorem alg99PrepareBDProg_exec {w n B : ℕ} (G : MultiDigraph n) (code : List ℕ)
    (hbd : IsValidBranchDecompCode B G code) (hw : 3 + 3 * G.numEdges < 2 ^ w)
    (s : State) (hout : s.arrs outArr = 0 :: code) :
    let x := multiCoreInput72 G code hbd
    ∃ s' t, Exec w alg99PrepareBDProg s s' t ∧ t ≤ 400 * (G.numEdges + 1) ∧
      s'.arrs 2 = List.ofFn (fun z : Fin x.t => x.p z.1) ∧
      s'.arrs 13 = List.ofFn (fun e : Fin G.numEdges => (x.τ e).1) ∧
      s'.regs 30 = x.t ∧ s'.regs 28 = G.numEdges ∧
      (∀ a : ℕ, a ≠ 10 → a ≠ 2 → a ≠ 13 → s'.arrs a = s.arrs a) ∧
      (∀ j < 28, s'.regs j = s.regs j) := by
  let x := multiCoreInput72 G code hbd
  have hb := hbd.length_and_words_le
  have hlen : code.length = 2 + bdNumTreeVerts code + G.numEdges := by
    rw [← hbd.1]
    exact hbd.2.2.1
  have hwords : ∀ v ∈ code, v < 2 ^ w := fun v hv => (hb.2 v hv).trans_lt (by romega)
  obtain ⟨s₁, t₁, he₁, ht₁, hc₁, ha₁, hr₁⟩ :=
    copyTailProg_exec (w := w) outArr 10 80 81 (by decide) (by decide) (by romega)
      hout (by romega) hwords
  let s₂ := s₁.setReg 28 G.numEdges
  have he₂ : Exec w (.assign 28 (.read 10 (.const 1))) s₁ s₂ 3 := by
    apply Exec.assign
    have hh : 1 < (s₁.arrs 10).length := by rw [hc₁, hlen]; omega
    have hval : (s₁.arrs 10)[1]'hh = G.numEdges := by
      apply (list_getD_eq_getElem (s₁.arrs 10) 1 0 hh).symm.trans
      rw [hc₁]
      exact hbd.1
    simp [Expr.eval, checkWord, show 1 < 2 ^ w by romega, hh, hval,
      show G.numEdges < 2 ^ w by romega]
  let s₃ := s₂.setReg 30 (bdNumTreeVerts code)
  have he₃ : Exec w (.assign 30 (.read 10 (.const 0))) s₂ s₃ 3 := by
    apply Exec.assign
    have hh : 0 < (s₂.arrs 10).length := by simp [s₂, hc₁, hlen]
    have hval : (s₂.arrs 10)[0]'hh = bdNumTreeVerts code := by
      apply (list_getD_eq_getElem (s₂.arrs 10) 0 0 hh).symm.trans
      simp only [s₂, State.setReg_arrs, hc₁, bdNumTreeVerts]
    have ht_w : bdNumTreeVerts code < 2 ^ w := by
      have h := hbd.2.1
      rw [hbd.1] at h
      romega
    simp [Expr.eval, checkWord, hh, hval, ht_w]
  obtain ⟨s₄, t₄, he₄, ht₄, hpar, hτ, ht, ha₄, hr₄⟩ :=
    prepareBD72Prog_exec (w := w) G code hbd 10 2 13 28 30 80
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s₃
      (by romega) (by romega) (by simp [s₃, s₂, hc₁])
      (by simp [s₃, s₂]) (by simp [s₃])
  refine ⟨s₄, t₁ + (3 + (3 + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)),
    by romega, hpar, hτ, ht, ?_, ?_, ?_⟩
  · rw [hr₄ 28 (by decide) (by decide)]
    simp [s₃, s₂]
  · intro a ha10 ha2 ha13
    rw [ha₄ a ha2 ha13]
    simp only [s₃, s₂, State.setReg_arrs]
    exact ha₁ a ha10
  · intro j hj
    rw [hr₄ j (by romega) (by romega)]
    simp only [s₃, s₂, State.setReg_regs_ne _ _ (show j ≠ 30 by romega),
      State.setReg_regs_ne _ _ (show j ≠ 28 by romega)]
    exact hr₁ j (by romega) (by romega)

end GraphMinor.Compute
