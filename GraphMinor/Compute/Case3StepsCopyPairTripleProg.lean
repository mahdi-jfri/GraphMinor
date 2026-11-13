module

public import GraphMinor.Compute.Case3StepsPairTriples
public import GraphMinor.Compute.Algorithm94Aux

/-!
# Copying one full positive-pair record into a member

Three adjacent words are copied from the compact multigraph into the next
member record slot. The multiplicity word is copied exactly. The surrounding
member records remain in place, and only four scratch registers change.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Copy pair index 71 to member record position 72; register 73 contains three. -/
def case3CopyPairTripleProg : Cmd :=
  writeSliceProg 3 (.op .add (.const 2) (.op .mul (.const 3) (.reg 71)))
    39 (.op .add (.const 2) (.op .mul (.const 3) (.reg 72))) 73 74

/-- One record, including its complete multiplicity, is copied in at most
sixty-eight steps with all surrounding member data preserved. -/
theorem case3CopyPairTripleProg_exec {w n : ℕ} (D : MultiDigraph n)
    (j : Fin D.numActivePairs) (q : ℕ) (pre suf : List ℕ)
    (hpre : pre.length = 2 + 3 * q)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (he : D.numEdges < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) (hQ : 2 + 3 * (q + 1) < 2 ^ w)
    {s : State} (hD : s.arrs 3 = D.enc)
    (hdst : s.arrs 39 = pre ++ List.replicate 3 0 ++ suf)
    (hrj : s.regs 71 = j.1) (hrq : s.regs 72 = q) (hr3 : s.regs 73 = 3) :
    ∃ s' t, Exec w case3CopyPairTripleProg s s' t ∧ t ≤ 68 ∧
      s'.arrs 39 = pre ++ case3PairTriple D j ++ suf ∧
      (∀ a, a ≠ 39 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 74 ∨ 78 ≤ r → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hj := j.2
  have hjw : j.1 < 2 ^ w := by omega
  have hq : q < 2 ^ w := by omega
  have hmulj : 3 * j.1 < 2 ^ w := by omega
  have hmulq : 3 * q < 2 ^ w := by omega
  have hoffj : 2 + 3 * j.1 < 2 ^ w := by omega
  have hoffq : 2 + 3 * q < 2 ^ w := by omega
  obtain ⟨s', t, hex, ht, hdst', harr, hreg⟩ :=
    writeSliceProg_exec (len := 3) (src_off := 2 + 3 * j.1) (dst_off := 2 + 3 * q)
      3 39 (.op .add (.const 2) (.op .mul (.const 3) (.reg 71)))
      (.op .add (.const 2) (.op .mul (.const 3) (.reg 72))) 73 74 (by decide) (by decide)
      ([n, D.numActivePairs] ++ MultiDigraph.flatTriples D (D.activePairsList.take j.1))
      (case3PairTriple D j) (MultiDigraph.flatTriples D (D.activePairsList.drop (j.1 + 1)))
      pre (List.replicate 3 0) suf (case3PairTriple_prefix_length D j)
      (case3PairTriple_length D j) hpre (List.length_replicate ..)
      (case3PairTriple_words D j hn he) (by omega) (by omega) (by omega) (s := s)
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, h2, hw, hjw, hmulj, hoffj])
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, State.setReg_regs_ne,
        hrq, h2, hw, hq, hmulq, hoffq])
      (hD.trans (case3PairTriple_enc_split D j)) hdst hr3
  dsimp only [Expr.cost] at ht
  exact ⟨s', t, hex, by omega, hdst', harr, fun r hr => hreg r (by dsimp only [Reg] at *; omega)⟩

end GraphMinor.Compute
