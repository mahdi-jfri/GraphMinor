module

public import GraphMinor.Compute.Case3StepsBucketBounds
import Mathlib.Data.List.GetD

/-!
# Initializing one member's multigraph encoding

The owner tables supply the exact pair count and first pair index. The
program allocates space for that many triples, writes the vertex and pair
count headers, and initializes the traversal registers. Shared vertices are
kept separately in the already computed ordered vertex list.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Read a bucket's count and head, then allocate its exact member record buffer. -/
def case3MemberEdgesInitProg : Cmd :=
  .seq (.assign 70 (.read 37 (.reg 54)))
    (.seq (.assign 71 (.read 35 (.reg 54)))
      (.seq (.alloc 39 (.op .add (.const 2) (.op .mul (.const 3) (.reg 70))))
        (.seq (.write 39 (.const 0) (.reg 14))
          (.seq (.write 39 (.const 1) (.reg 70))
            (.seq (.assign 72 (.const 0)) (.assign 73 (.const 3)))))))

/-- Exact bucket counts allocate exactly the member's header and record slots. -/
theorem case3MemberEdgesInitProg_exec {w A L : ℕ} (owner : Fin A → ℕ)
    (n label : ℕ) (hb : label < L) (hw : 3 < 2 ^ w)
    (hn : n < 2 ^ w) (hA : 2 + 3 * A < 2 ^ w) (hL : L < 2 ^ w)
    {s : State} (hheads : s.arrs 35 = case3BucketHeads owner L 0)
    (hcounts : s.arrs 37 = case3BucketCounts owner L 0)
    (hrn : s.regs 14 = n) (hrb : s.regs 54 = label) :
    ∃ s' t, Exec w case3MemberEdgesInitProg s s' t ∧
      t ≤ 3 * (case3BucketIndices owner label 0).length + 23 ∧
      s'.arrs 39 = [n, (case3BucketIndices owner label 0).length] ++
        List.replicate (3 * (case3BucketIndices owner label 0).length) 0 ∧
      s'.regs 70 = (case3BucketIndices owner label 0).length ∧
      s'.regs 71 = (case3BucketIndices owner label 0).headD A ∧
      s'.regs 72 = 0 ∧ s'.regs 73 = 3 ∧
      (∀ a, a ≠ 39 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 70 ∨ 74 ≤ r → s'.regs r = s.regs r) := by
  let count := (case3BucketIndices owner label 0).length
  let head := (case3BucketIndices owner label 0).headD A
  have hcA : count ≤ A := case3BucketIndices_length_le owner label 0
  have hhA : head ≤ A := case3BucketIndices_head_le owner label 0
  have hcw : count < 2 ^ w := by omega
  have hhw : head < 2 ^ w := by omega
  have hlenw : 2 + 3 * count < 2 ^ w := by omega
  have hmulw : 3 * count < 2 ^ w := by omega
  have hbw : label < 2 ^ w := hb.trans hL
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hiC : label < (s.arrs 37).length := by
    rw [hcounts]; simpa only [case3BucketCounts, List.length_ofFn] using hb
  have hiH : label < (s.arrs 35).length := by
    rw [hheads]; simpa only [case3BucketHeads, List.length_ofFn] using hb
  have hgC : (s.arrs 37)[label]'hiC = count := by
    rw [← List.getD_eq_getElem _ 0 hiC, hcounts, case3BucketCounts_getD owner L 0 label hb]
  have hgH : (s.arrs 35)[label]'hiH = head := by
    rw [← List.getD_eq_getElem _ 0 hiH, hheads, case3BucketHeads_getD owner L 0 label hb]
  let s₁ := s.setReg 70 count
  let s₂ := s₁.setReg 71 head
  let s₃ := s₂.setArr 39 (List.replicate (2 + 3 * count) 0)
  let s₄ := s₃.writeArr 39 0 n
  let s₅ := s₄.writeArr 39 1 count
  let s₆ := s₅.setReg 72 0
  let s₇ := s₆.setReg 73 3
  have hex₁ : Exec w (.assign 70 (.read 37 (.reg 54))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hrb, hbw, hiC, hgC, hcw])
  have hex₂ : Exec w (.assign 71 (.read 35 (.reg 54))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, s₁, State.setReg_regs_ne, hrb, hbw, hiH, hgH, hhw])
  have hex₃ : Exec w (.alloc 39 (.op .add (.const 2) (.op .mul (.const 3) (.reg 70))))
      s₂ s₃ (5 + (2 + 3 * count)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁,
      State.setReg_regs_ne, h2, hw, hcw, hmulw, hlenw])
  have hex₄ : Exec w (.write 39 (.const 0) (.reg 14)) s₃ s₄ 3 :=
    .write (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
      (by simp [Expr.eval, checkWord, s₃, s₂, s₁, State.setReg_regs_ne, hrn, hn])
      (by simp only [s₃, State.setArr_arrs_self, List.length_replicate]; omega)
  have hex₅ : Exec w (.write 39 (.const 1) (.reg 70)) s₄ s₅ 3 :=
    .write (by simp only [Expr.eval, checkWord, h1, ↓reduceIte])
      (by simp [Expr.eval, checkWord, s₄, s₃, s₂, s₁, State.setReg_regs_ne, hcw])
      (by simp only [s₄, s₃, State.writeArr_arrs_self, List.length_set,
        State.setArr_arrs_self, List.length_replicate]; omega)
  have hex₆ : Exec w (.assign 72 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have hex₇ : Exec w (.assign 73 (.const 3)) s₆ s₇ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hw, ↓reduceIte])
  have hex : Exec w case3MemberEdgesInitProg s s₇ (3 + (3 + ((5 + (2 + 3 * count)) + (3 + (3 + (2 + 2)))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
  refine ⟨s₇, _, hex, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [s₇, s₆, s₅, s₄, s₃, State.setReg_arrs, State.writeArr_arrs_self, State.setArr_arrs_self]
    rw [show 2 + 3 * count = (3 * count + 1) + 1 by omega, List.replicate_succ,
      List.set_cons_zero, List.replicate_succ, List.set_cons_succ, List.set_cons_zero]
    rfl
  · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg_regs_ne, count]
  · simp [s₇, s₆, s₅, s₄, s₃, s₂, State.setReg_regs_ne, head]
  · simp [s₇, s₆, State.setReg_regs_ne]
  · exact State.setReg_regs_self ..
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3MemberEdgesInitProg, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [case3MemberEdgesInitProg, Cmd.writtenRegs]
      romega)

end GraphMinor.Compute
