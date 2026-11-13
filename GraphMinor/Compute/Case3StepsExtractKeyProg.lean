module

public import GraphMinor.Compute.Case3StepsFindBoundaryProg
public import GraphMinor.Compute.Case3StepsComponentRowProg

/-!
# Extracting a target boundary key

The representative search compares a selected row of the attachment-key
table with all component keys. Copying its four words into the target array
uses a fixed amount of work, independent of the graph size.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Copy the key of seed register 15 from array 26 to target array 25.
Register 13 contains four. -/
def case3ExtractKeyProg : Cmd :=
  .seq (.alloc 25 (.const 4))
    (writeSliceProg 26 (.op .mul (.reg 15) (.const 4)) 25 (.const 0) 13 36)

/-- Extracting one target key takes at most 84 steps and retains the source
key table and all registers below 36. -/
theorem case3ExtractKeyProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d) (u : Fin x.n)
    (hw : 4 < 2 ^ w) (hn : x.n < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    {s : State} (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hru : s.regs 15 = u.1) (hr4 : s.regs 13 = 4) :
    ∃ s' t, Exec w case3ExtractKeyProg s s' t ∧ t ≤ 84 ∧
      s'.arrs 25 = case3BoundaryKey (case3AttachmentRowSet x d.core.Z u) ∧
      (∀ a, a ≠ 25 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 36 ∨ 40 ≤ r → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have huw : u.1 < 2 ^ w := u.2.trans hn
  have hend : u.1 * 4 + 4 ≤ x.n * 4 := by omega
  have hoff : u.1 * 4 < 2 ^ w := by omega
  let s₁ := s.setArr 25 (List.replicate 4 0)
  have hex₁ : Exec w (.alloc 25 (.const 4)) s s₁ 5 :=
    .alloc (by simp only [Expr.eval, checkWord, hw, ↓reduceIte])
  have hsrc : s₁.arrs 26 =
      (((List.finRange x.n).take u.1).flatMap
        (fun v => case3BoundaryKey (case3AttachmentRowSet x d.core.Z v))) ++
        case3BoundaryKey (case3AttachmentRowSet x d.core.Z u) ++
      (((List.finRange x.n).drop (u.1 + 1)).flatMap
        (fun v => case3BoundaryKey (case3AttachmentRowSet x d.core.Z v))) := by
    rw [State.setArr_arrs_ne _ _ (by decide), htab]
    exact case3AttachmentKeys_split x d.core.Z u
  have hcard := case3AttachmentRowSet_card_le_three x d hd u
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂, harr₂, hreg₂⟩ :=
    writeSliceProg_exec (len := 4) (src_off := u.1 * 4) (dst_off := 0)
      26 25 (.op .mul (.reg 15) (.const 4)) (.const 0) 13 36 (by decide) (by decide)
      _ (case3BoundaryKey (case3AttachmentRowSet x d.core.Z u)) _ [] (List.replicate 4 0) []
      (case3AttachmentKeys_prefix_length x d hd u.1 u.2.le) (case3BoundaryKey_length _ hcard)
      rfl (List.length_replicate ..) (case3BoundaryKey_words _ hcard hw hn) (by omega)
      (hend.trans_lt hkeys) (by simpa only [Nat.zero_add] using hw) (s := s₁)
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, State.setArr_regs, hru, huw, hw, hoff])
      (by simp only [Expr.eval, checkWord, h0, ↓reduceIte]) hsrc
      (by simp only [s₁, State.setArr_arrs_self, List.nil_append, List.append_nil]) hr4
  dsimp only [Expr.cost] at ht₂
  refine ⟨s₂, 5 + t₂, .seq hex₁ hex₂, by omega, ?_, ?_, ?_⟩
  · simpa only [List.nil_append, List.append_nil] using hdst₂
  · intro a ha
    exact (harr₂ a ha).trans (State.setArr_arrs_ne _ _ ha)
  · intro r hr
    exact hreg₂ r (by dsimp only [Reg] at *; omega)

end GraphMinor.Compute
