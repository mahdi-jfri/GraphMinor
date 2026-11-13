module

public import GraphMinor.Compute.Algorithm94Aux

/-!
# Storing a member record without recopying earlier records

The member scan writes each serialized record into a preallocated buffer.
Only the new record is copied. Registers 1 and 2 hold the used prefix
length and number of records. Thus the total copying cost is linear in
the sum of the record lengths.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Append record array 51 into buffer 57 and advance its two counters. -/
def case3StoreMemberRecordProg : Cmd :=
  .seq (.assign 112 (.len 51))
    (.seq (writeSliceProg 51 (.const 0) 57 (.reg 1) 112 120)
      (.seq (.assign 1 (.op .add (.reg 1) (.reg 112)))
        (.assign 2 (.op .add (.reg 2) (.const 1)))))

/-- Copying one record costs only its own length and preserves all earlier
records, the remaining buffer, and the member result flag. -/
theorem case3StoreMemberRecordProg_exec {w count : ℕ} (pre record rest : List ℕ)
    (hw : 1 < 2 ^ w) (hlen : pre.length + record.length < 2 ^ w)
    (hcount : count + 1 < 2 ^ w) (hwords : ∀ z ∈ record, z < 2 ^ w)
    {s : State} (hrec : s.arrs 51 = record)
    (hbuf : s.arrs 57 = pre ++ List.replicate record.length 0 ++ rest)
    (hused : s.regs 1 = pre.length) (hnum : s.regs 2 = count) :
    ∃ s' t, Exec w case3StoreMemberRecordProg s s' t ∧
      t ≤ 17 * record.length + 19 ∧
      s'.arrs 57 = pre ++ record ++ rest ∧
      s'.regs 1 = pre.length + record.length ∧ s'.regs 2 = count + 1 ∧
      (∀ a, a ≠ 57 → s'.arrs a = s.arrs a) ∧
      (∀ r < 112, r ≠ 1 → r ≠ 2 → s'.regs r = s.regs r) := by
  have hrecw : record.length < 2 ^ w := by omega
  have hprew : pre.length < 2 ^ w := by omega
  have hc : count < 2 ^ w := by omega
  let s₁ := s.setReg 112 record.length
  have hex₁ : Exec w (.assign 112 (.len 51)) s s₁ 2 :=
    .assign (by simp only [Expr.eval, hrec, checkWord, hrecw, ↓reduceIte])
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, harr₂, hreg₂⟩ := writeSliceProg_exec
    (len := record.length) (src_off := 0) (dst_off := pre.length)
    51 57 (.const 0) (.reg 1) 112 120 (by decide) (by decide)
    [] record [] pre (List.replicate record.length 0) rest rfl rfl rfl
    (List.length_replicate ..) hwords hw (by simpa only [Nat.zero_add] using hrecw) hlen
    (s := s₁)
    (by simp only [Expr.eval, checkWord, Nat.two_pow_pos, ↓reduceIte])
    (by simp only [Expr.eval, checkWord, s₁, State.setReg_regs_ne _ _ (show (1 : Reg) ≠ 120 by decide),
      State.setReg_regs_ne _ _ (show (1 : Reg) ≠ 112 by decide), hused, hprew, ↓reduceIte])
    (by simpa only [s₁, State.setReg_arrs, List.nil_append, List.append_nil] using hrec)
    hbuf (State.setReg_regs_self ..)
  have h71 : s₂.regs 1 = pre.length := (hreg₂ 1 (Or.inl (by decide))).trans
    ((State.setReg_regs_ne s _ (show (1 : Reg) ≠ 112 by decide)).trans hused)
  have h72 : s₂.regs 2 = count := (hreg₂ 2 (Or.inl (by decide))).trans
    ((State.setReg_regs_ne s _ (show (2 : Reg) ≠ 112 by decide)).trans hnum)
  have h112 : s₂.regs 112 = record.length := (hreg₂ 112 (Or.inl (by decide))).trans
    (State.setReg_regs_self ..)
  let s₃ := s₂.setReg 1 (pre.length + record.length)
  let s₄ := s₃.setReg 2 (count + 1)
  have hex₃ : Exec w (.assign 1 (.op .add (.reg 1) (.reg 112))) s₂ s₃ 4 :=
    .assign (by simp only [Expr.eval, checkWord, h71, h112, hprew, hrecw,
      BinOp.eval, BinOp.raw, hlen, ↓reduceIte])
  have hex₄ : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₃ s₄ 4 :=
    .assign (by simp only [Expr.eval, checkWord, s₃,
      State.setReg_regs_ne _ _ (show (2 : Reg) ≠ 1 by decide), h72, hc, hw,
      BinOp.eval, BinOp.raw, hcount, ↓reduceIte])
  refine ⟨s₄, 2 + (t₂ + (4 + 4)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_,
    hbuf₂, ?_, State.setReg_regs_self .., ?_, ?_⟩
  · norm_num only [Expr.cost] at ht₂
    omega
  · exact State.setReg_regs_ne s₃ _ (show (1 : Reg) ≠ 2 by decide) |>.trans (State.setReg_regs_self ..)
  · intro a ha
    exact harr₂ a ha
  · intro r hr h71ne h72ne
    rw [State.setReg_regs_ne _ _ h72ne, State.setReg_regs_ne _ _ h71ne,
      hreg₂ r (Or.inl (by romega)), State.setReg_regs_ne _ _ (by romega)]

end GraphMinor.Compute
