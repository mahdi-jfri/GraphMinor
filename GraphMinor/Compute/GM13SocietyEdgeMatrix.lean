module

public import GraphMinor.Compute.GM13SocietyInput
import GraphMinor.Compute.Algorithm94Init

/-!
# Actual edge directions for the society reduction

For an adjacent ordered pair of distinct vertices, use edge number zero in
that direction when it exists, and edge number zero in the reverse direction
otherwise. The direction table records which choice to use. It is built
from the original multigraph, whose encoding has been retained by the simple
program call.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A table containing one exactly when an ordered pair has a directed edge. -/
def GM13DirectionMatrix {n : ℕ} (G : MultiDigraph n) (L : List ℕ) : Prop :=
  ∃ hlen : L.length = n * n, ∀ u v : Fin n,
    L[u.1 * n + v.1]'(by rw [hlen]; exact mul_add_lt_sq u.2 v.2) =
      if 0 < G.edgeMult u v then 1 else 0

/-- Extract the graph prefix and build its ordered-pair direction table.
The full plain society input in array zero is preserved. -/
def gm13SocietyEdgeMatrixProg : Cmd :=
  .seq (.assign 0 (.read 0 (.const 0)))
    (.seq (.assign 1 (.read 0 (.const 1)))
      (.seq (.assign 2 (.op .add (.const 2) (.op .mul (.const 3) (.reg 1))))
        (.seq (readSliceProg 0 (.const 0) 4 (.reg 2) 3)
          (buildDirMatProg 4 5 0 1 3))))

/-- The edge-direction table costs O(n² + ε) time. Since ε is at least n,
this fits the O(vε) time of the Section 8 algorithms. -/
theorem gm13SocietyEdgeMatrixProg_exec {w : ℕ} (x : GM13SocietyInput)
    (hw : 8 + x.n * x.n + 3 * x.G.numActivePairs + x.G.numEdges + x.n < 2 ^ w)
    {s : State} (hin : s.arrs 0 = x.enc) :
    ∃ s' t, Exec w gm13SocietyEdgeMatrixProg s s' t ∧
      t ≤ x.n * x.n + 76 * x.G.numActivePairs + 80 ∧
      GM13DirectionMatrix x.G (s'.arrs 5) ∧
      (∀ a : ℕ, a ≠ 4 → a ≠ 5 → s'.arrs a = s.arrs a) ∧ s'.regs 0 = x.n := by
  let suffix := x.omega.length :: x.omega.map Fin.val
  have hw1 : 1 < 2 ^ w := by omega
  have hn : x.n < 2 ^ w := by omega
  have hm : x.G.numActivePairs < 2 ^ w := by omega
  have hlen : x.G.enc.length < 2 ^ w := by rw [x.G.length_enc]; omega
  have hencw := all_lt_enc_multiDigraph x.G hn hm (show x.G.numEdges < 2 ^ w by omega)
  have hget0 : (s.arrs 0)[0]? = some x.n := by
    obtain ⟨hi, hv⟩ := enc_getElem_zero x.G suffix hin
    exact List.getElem?_eq_some_iff.mpr ⟨hi, hv⟩
  let s₁ := s.setReg 0 x.n
  have hex₁ : Exec w (.assign 0 (.read 0 (.const 0))) s s₁ 3 :=
    .assign (gm13_read_eval (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega]) hget0 hn)
  have hget1 : (s₁.arrs 0)[1]? = some x.G.numActivePairs := by
    obtain ⟨hi, hv⟩ := enc_getElem_one x.G suffix hin
    exact List.getElem?_eq_some_iff.mpr ⟨hi, hv⟩
  let s₂ := s₁.setReg 1 x.G.numActivePairs
  have hex₂ : Exec w (.assign 1 (.read 0 (.const 1))) s₁ s₂ 3 :=
    .assign (gm13_read_eval (by simp [Expr.eval, checkWord, hw1]) hget1 hm)
  let s₃ := s₂.setReg 2 x.G.enc.length
  have hex₃ : Exec w (.assign 2 (.op .add (.const 2) (.op .mul (.const 3) (.reg 1))))
      s₂ s₃ 6 := by
    apply Exec.assign
    simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, x.G.length_enc,
      show 2 < 2 ^ w by omega, show 3 < 2 ^ w by omega, hm,
      show 3 * x.G.numActivePairs < 2 ^ w by omega,
      show 2 + 3 * x.G.numActivePairs < 2 ^ w by omega]
  obtain ⟨s₄, t₄, hex₄, ht₄, hout₄, harr₄, hreg₄⟩ :=
    readSliceProg_exec (s := s₃) 0 4 (.const 0) 2 3 (by decide) (by decide)
      [] x.G.enc suffix rfl rfl hencw hw1 (by simpa using hlen)
      (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
      (by simpa [s₃, s₂, s₁, List.nil_append, GM13SocietyInput.enc] using hin)
      (by simp [s₃])
  obtain ⟨s₅, t₅, hex₅, ht₅, hlen₅, hcell₅, harr₅, hreg₅⟩ :=
    buildDirMatProg_exec (w := w) x.G 4 5 0 1 3 (by decide) (by decide) (by decide)
      (by omega) hn (by omega) (by omega) hout₄
      (by rw [hreg₄ 0 (by decide)]; simp [s₃, s₂, s₁])
      (by rw [hreg₄ 1 (by decide)]; simp [s₃, s₂])
  refine ⟨s₅, 3 + (3 + (6 + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_, ⟨hlen₅, hcell₅⟩, ?_, ?_⟩
  · simp only [Expr.cost_const, x.G.length_enc] at ht₄
    omega
  · intro a ha4 ha5
    rw [harr₅ a ha5, harr₄ a ha4]
    rfl
  · rw [hreg₅ 0 (by decide), hreg₄ 0 (by decide)]
    simp [s₃, s₂, s₁]

end GraphMinor.Compute
