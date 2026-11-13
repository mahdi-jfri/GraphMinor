module

public import GraphMinor.Compute.Case3StepsEncodingWords
public import GraphMinor.Compute.Specs9

/-!
# Saving the compact member below the isolated program workspace

The supplied program of (7.2) may use its input array as scratch. A copy of
the compact input is retained below that workspace, so the record-writing
scan can later expand precisely its directed pairs in their original order.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Save compact input 128 at array 38 before the call to (7.2). -/
def case3SaveMemberInputProg : Cmd := copyArrLoopProg 128 38 118 119

/-- Saving the member is linear in its positive-pair count and preserves
all other arrays, including the isolated call's input. -/
theorem case3SaveMemberInputProg_exec {w n : ℕ} (G : MultiDigraph n)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hA : 2 + 3 * G.numActivePairs < 2 ^ w)
    (he : G.numEdges < 2 ^ w) {s : State} (hin : s.arrs 128 = G.enc) :
    ∃ s' t, Exec w case3SaveMemberInputProg s s' t ∧ t ≤ 45 * G.numActivePairs + 38 ∧
      s'.arrs 38 = G.enc ∧ (∀ a, a ≠ 38 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 118 → r ≠ 119 → s'.regs r = s.regs r) := by
  obtain ⟨s', t, hex, ht, hdst, harr, hreg⟩ := copyArrLoopProg_exec 128 38 118 119
    (by decide) (by decide) hw s (by rw [hin, G.length_enc]; exact hA)
    (by rw [hin]; exact case3Multigraph_enc_words_lt G hn (by omega) he)
  refine ⟨s', t, hex, ?_, hdst.trans hin, harr, hreg⟩
  rw [hin, G.length_enc] at ht
  omega

end GraphMinor.Compute
