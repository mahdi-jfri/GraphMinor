module

public import GraphMinor.Compute.Basic

/-!
# Marking one supplied closure incidence

A closure row has a row offset, and its vertex or edge entries have a
fixed kind offset. Add these offsets to the supplied label and mark
that matrix position. This is the common write used for endpoint and
region-boundary incidence lists.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Mark the incidence at row offset 173, kind offset 174, and label 109. -/
def gm06MarkCellProg : Cmd :=
  .write 12 (.op .add (.op .add (.reg 173) (.reg 174)) (.reg 109)) (.const 1)

/-- The closure-incidence marker writes exactly its computed matrix
position in seven steps, preserving all registers and other arrays. -/
theorem gm06MarkCellProg_exec {w row shift v : ℕ} (hw : 1 < 2 ^ w)
    (hword : row + shift + v < 2 ^ w) {s : State}
    (hrow : s.regs 173 = row) (hshift : s.regs 174 = shift) (hlabel : s.regs 109 = v)
    (hcap : row + shift + v < (s.arrs 12).length) :
    ∃ s', Exec w gm06MarkCellProg s s' 7 ∧
      s'.arrs 12 = (s.arrs 12).set (row + shift + v) 1 ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, s'.regs q = s.regs q) := by
  have hrw : row < 2 ^ w := by omega
  have hsw : shift < 2 ^ w := by omega
  have hvw : v < 2 ^ w := by omega
  have hrsw : row + shift < 2 ^ w := by omega
  let s' := s.writeArr 12 (row + shift + v) 1
  have hex : Exec w gm06MarkCellProg s s' 7 :=
    .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrow, hshift, hlabel,
      hrw, hsw, hvw, hrsw, hword]) (by simp [Expr.eval, checkWord, hw]) hcap
  exact ⟨s', hex, rfl, fun a ha => State.writeArr_arrs_ne _ _ _ ha, fun _ => rfl⟩

end GraphMinor.Compute
