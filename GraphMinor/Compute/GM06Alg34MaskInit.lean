module

public import GraphMinor.Compute.GM06Alg34VertexMask
public import GraphMinor.Compute.Array

/-!
# Initializing the active-vertex array

The input header supplies the vertex count in register 100. Allocate
that many mask entries and fill them with ones using the verified array
fill loop. All vertices start active, all other arrays stay unchanged,
and the cost is linear in the supplied count.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Allocate array 4 from the supplied vertex count and mark every label active. -/
def gm06InitVertexMaskProg : Cmd :=
  .seq (.alloc 4 (.reg 100)) (fillArr 4 (.len 4) (.const 1) 115)

/-- The initial mask is exactly the mask of all supplied vertex labels,
with a linear bound and arbitrary initial mask contents. -/
theorem gm06InitVertexMaskProg_exec {w n : ℕ} (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    {s : State} (hcount : s.regs 100 = n) :
    ∃ s' t, Exec w gm06InitVertexMaskProg s s' t ∧ t ≤ 13 * n + 6 ∧
      s'.arrs 4 = gm06VertexMask (List.finRange n) ∧
      (∀ a : ℕ, a ≠ 4 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 115 → s'.regs q = s.regs q) := by
  let s₁ := s.setArr 4 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 4 (.reg 100)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hcount, hn])
  obtain ⟨s₂, t₂, hex₂, ht₂, harr₂, _⟩ :=
    Triple.fillArr_const 4 1 115 (List.replicate n 0) hw
      (by simpa only [List.length_replicate] using hn) hw s₁ rfl
  have hex : Exec w gm06InitVertexMaskProg s s₂ ((1 + n) + t₂) := .seq hex₁ hex₂
  refine ⟨s₂, _, hex, by simp only [List.length_replicate] at ht₂; omega, ?_, ?_, ?_⟩
  · rw [gm06VertexMask_all]
    simpa only [List.length_replicate] using harr₂
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simpa [gm06InitVertexMaskProg, fillArr, forUp, Cmd.writtenArrs] using ha)
  · intro q hq
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simpa [gm06InitVertexMaskProg, fillArr, forUp, Cmd.writtenRegs] using hq)

end GraphMinor.Compute
