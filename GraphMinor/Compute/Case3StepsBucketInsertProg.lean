module

public import GraphMinor.Compute.Case3StepsBucketBounds
import Mathlib.Data.List.GetD

/-!
# Executing one reverse bucket insertion

The current pair points to its owner's old head. It then becomes the new
head, and the owner's count increases by one. Three RAM writes advance the
exact head, count, and next-pointer tables in constant time.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Insert the pair in register 65 into the owner bucket in register 68. -/
def case3BucketInsertProg : Cmd :=
  .seq (.write 36 (.reg 65) (.read 35 (.reg 68)))
    (.seq (.write 35 (.reg 68) (.reg 65))
      (.write 37 (.reg 68) (.op .add (.read 37 (.reg 68)) (.const 1))))

/-- One pair advances all three exact bucket tables in thirteen steps. -/
theorem case3BucketInsertProg_exec {w A L : ℕ} (owner : Fin A → ℕ)
    (k : ℕ) (hk : k < A) (howner : owner ⟨k, hk⟩ < L)
    (hw : 1 < 2 ^ w) (hA : A + 1 < 2 ^ w) (hL : L < 2 ^ w)
    {s : State} (hheads : s.arrs 35 = case3BucketHeads owner L (k + 1))
    (hnext : s.arrs 36 = case3BucketNext owner (k + 1))
    (hcounts : s.arrs 37 = case3BucketCounts owner L (k + 1))
    (hrk : s.regs 65 = k) (hrb : s.regs 68 = owner ⟨k, hk⟩) :
    ∃ s', Exec w case3BucketInsertProg s s' 13 ∧
      s'.arrs 35 = case3BucketHeads owner L k ∧
      s'.arrs 36 = case3BucketNext owner k ∧ s'.arrs 37 = case3BucketCounts owner L k ∧
      (∀ a, a ≠ 35 → a ≠ 36 → a ≠ 37 → s'.arrs a = s.arrs a) ∧
      (∀ r, s'.regs r = s.regs r) := by
  let b := owner ⟨k, hk⟩
  let head := (case3BucketHeads owner L (k + 1)).getD b 0
  let count := (case3BucketCounts owner L (k + 1)).getD b 0
  have hrb' : s.regs 68 = b := hrb
  have hb : b < L := howner
  have hbw : b < 2 ^ w := hb.trans hL
  have hkw : k < 2 ^ w := by omega
  have hhead : head ≤ A := by
    rw [show head = (case3BucketHeads owner L (k + 1)).getD b 0 from rfl,
      case3BucketHeads_getD owner L (k + 1) b hb]
    exact case3BucketIndices_head_le owner b (k + 1)
  have hcount : count ≤ A := by
    rw [show count = (case3BucketCounts owner L (k + 1)).getD b 0 from rfl,
      case3BucketCounts_getD owner L (k + 1) b hb]
    exact case3BucketIndices_length_le owner b (k + 1)
  have hheadw : head < 2 ^ w := by omega
  have hcountw : count < 2 ^ w := by omega
  have hcountpw : count + 1 < 2 ^ w := by omega
  have hiH : b < (s.arrs 35).length := by rw [hheads]; simpa only [case3BucketHeads, List.length_ofFn] using hb
  have hiN : k < (s.arrs 36).length := by rw [hnext]; simpa only [case3BucketNext, List.length_ofFn] using hk
  have hiC : b < (s.arrs 37).length := by rw [hcounts]; simpa only [case3BucketCounts, List.length_ofFn] using hb
  have hgH : (s.arrs 35)[b]'hiH = head := by
    rw [← List.getD_eq_getElem _ 0 hiH, hheads]
  have hgC : (s.arrs 37)[b]'hiC = count := by
    rw [← List.getD_eq_getElem _ 0 hiC, hcounts]
  have hek : (Expr.reg 65).eval w s = some k := by
    simp only [Expr.eval, checkWord, hrk, hkw, ↓reduceIte]
  have heb : (Expr.reg 68).eval w s = some b := by
    simp only [Expr.eval, checkWord, hrb', hbw, ↓reduceIte]
  have hehead : (Expr.read 35 (.reg 68)).eval w s = some head := by
    simp [Expr.eval, checkWord, hrb', hbw, hiH, hgH, hheadw]
  let s₁ := s.writeArr 36 k head
  let s₂ := s₁.writeArr 35 b k
  let s₃ := s₂.writeArr 37 b (count + 1)
  have hex₁ : Exec w (.write 36 (.reg 65) (.read 35 (.reg 68))) s s₁ 4 := .write hek hehead hiN
  have hex₂ : Exec w (.write 35 (.reg 68) (.reg 65)) s₁ s₂ 3 :=
    .write heb hek (by simpa only [s₁, State.writeArr_arrs_ne _ _ _ (show (35 : ℕ) ≠ 36 by decide)] using hiH)
  have hiC₂ : b < (s₂.arrs 37).length := by
    simpa only [s₂, s₁, State.writeArr_arrs_ne _ _ _ (show (37 : ℕ) ≠ 35 by decide),
      State.writeArr_arrs_ne _ _ _ (show (37 : ℕ) ≠ 36 by decide)] using hiC
  have hex₃ : Exec w
      (.write 37 (.reg 68) (.op .add (.read 37 (.reg 68)) (.const 1))) s₂ s₃ 6 :=
    .write heb (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁,
      hrb', hbw, hiC, hgC, hcountw, hcountpw, hw]) hiC₂
  have hex : Exec w case3BucketInsertProg s s₃ 13 := .seq hex₁ (.seq hex₂ hex₃)
  refine ⟨s₃, hex, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ (show (35 : ℕ) ≠ 37 by decide),
      State.writeArr_arrs_self, State.writeArr_arrs_ne _ _ _ (show (35 : ℕ) ≠ 36 by decide), hheads]
    exact case3BucketHeads_set owner L k hk howner
  · simp only [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ (show (36 : ℕ) ≠ 37 by decide),
      State.writeArr_arrs_ne _ _ _ (show (36 : ℕ) ≠ 35 by decide), State.writeArr_arrs_self, hnext]
    exact case3BucketNext_set owner L k hk howner
  · simp only [s₃, s₂, s₁, State.writeArr_arrs_self,
      State.writeArr_arrs_ne _ _ _ (show (37 : ℕ) ≠ 35 by decide),
      State.writeArr_arrs_ne _ _ _ (show (37 : ℕ) ≠ 36 by decide), hcounts]
    exact case3BucketCounts_set owner L k hk howner
  · intro a h35 h36 h37
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [case3BucketInsertProg, Cmd.writtenArrs, h35, h36, h37])
  · intro r
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [case3BucketInsertProg, Cmd.writtenRegs])

end GraphMinor.Compute
