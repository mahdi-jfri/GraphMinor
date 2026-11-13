module

public import GraphMinor.Compute.GM06Alg34Stream

/-!
# Updating a reserved section count word

Save the count-word position before writing a variable number of
retained blocks. Once the scan has computed the new count, one RAM
write replaces that reserved word and preserves the following section.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Replace the count at the saved position in register 146 by register 145. -/
def gm06CountPatchProg : Cmd := .write 10 (.reg 146) (.reg 145)

/-- Updating the reserved count word preserves all following words,
all other arrays, and every register, and takes three steps. -/
theorem gm06CountPatchProg_exec {w cap oldCount newCount : ℕ} (pfx body : List ℕ)
    (hposw : pfx.length < 2 ^ w) (hcountw : newCount < 2 ^ w) {s : State}
    (hbuf : IsPrefixBuffer 10 (pfx ++ (oldCount :: body)) cap s)
    (hpos : s.regs 146 = pfx.length) (hcount : s.regs 145 = newCount) :
    ∃ s', Exec w gm06CountPatchProg s s' 3 ∧
      IsPrefixBuffer 10 (pfx ++ (newCount :: body)) cap s' ∧
      (∀ a : ℕ, a ≠ 10 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, s'.regs q = s.regs q) := by
  have hcap : pfx.length < (s.arrs 10).length := by
    rw [hbuf]
    simp
  let s' := s.writeArr 10 pfx.length newCount
  have hex : Exec w gm06CountPatchProg s s' 3 :=
    .write (by simp [Expr.eval, checkWord, hpos, hposw])
      (by simp [Expr.eval, checkWord, hcount, hcountw]) hcap
  refine ⟨s', hex, ?_, ?_, fun _ => rfl⟩
  · change ((s.arrs 10).set pfx.length newCount) = _
    rw [hbuf, List.append_assoc, List.set_append_right _ _ le_rfl]
    simp [IsPrefixBuffer, List.append_assoc]
  · intro a ha
    exact State.writeArr_arrs_ne _ _ _ ha

end GraphMinor.Compute
