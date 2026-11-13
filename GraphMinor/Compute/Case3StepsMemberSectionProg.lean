module

public import GraphMinor.Compute.Case3StepsCountedPrefixProg

/-!
# Finishing the member section

The scans keep their concatenated records in reserved buffer 57. The used
prefix is copied once and prefixed by the member count. This produces the
last section of a case (iii) block without copying its unused capacity.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Copy the retained records and put their count before them. -/
def case3MemberSectionProg : Cmd :=
  .seq (case3CountedPrefixProg 57 52 1)
    (.seq (.assign 124 (.reg 1)) (prependWordProg (.reg 2) 52 51 124 128))

/-- The completed member section is exact and keeps all member data. -/
theorem case3MemberSectionProg_exec {w : ℕ} (records unused : List ℕ) (count : ℕ)
    (hw : 1 < 2 ^ w) (hlen : 1 + records.length < 2 ^ w)
    (hcount : count < 2 ^ w) (hwords : ∀ x ∈ records, x < 2 ^ w)
    {s : State} (hbuf : s.arrs 57 = records ++ unused)
    (hrlen : s.regs 1 = records.length) (hrcount : s.regs 2 = count) :
    ∃ s' t, Exec w case3MemberSectionProg s s' t ∧
      t ≤ 40 * records.length + 50 ∧ s'.arrs 51 = count :: records ∧
      (∀ a, a ≠ 51 → a ≠ 52 → s'.arrs a = s.arrs a) ∧
      (∀ r < 120, s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, harr₁, hreg₁⟩ :=
    case3CountedPrefixProg_exec 57 52 1 (by decide) (by decide) records unused hw
      (by omega) hwords hbuf hrlen
  let s₂ := s₁.setReg 124 records.length
  have hr1 : s₁.regs 1 = records.length := (hreg₁ 1 (Or.inl (by dsimp only [Reg]; omega))).trans hrlen
  have hr2 : s₁.regs 2 = count := (hreg₁ 2 (Or.inl (by dsimp only [Reg]; omega))).trans hrcount
  have hex₂ : Exec w (.assign 124 (.reg 1)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hr1, show records.length < 2 ^ w by omega, ↓reduceIte])
  obtain ⟨s₃, t₃, hex₃, ht₃, hbuf₃, harr₃, hreg₃⟩ := prependWordProg_exec
    (.reg 2) 52 51 124 128 (by decide) (by decide) records hwords hw hlen
    (s := s₂) (tag := count)
    (by intro v; simp only [Expr.eval, checkWord, State.setArr_regs,
        State.setReg_regs_ne _ _ (show (2 : ℕ) ≠ 128 by decide), s₂,
        State.setReg_regs_ne _ _ (show (2 : ℕ) ≠ 124 by decide), hr2, hcount, ↓reduceIte])
    hbuf₁ (State.setReg_regs_self ..)
  refine ⟨s₃, t₁ + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), ?_, hbuf₃, ?_, ?_⟩
  · norm_num only [Expr.cost] at ht₃
    omega
  · intro a h51 h52
    exact (harr₃ a h51).trans (harr₁ a h52)
  · intro r hr
    rw [hreg₃ r (Or.inl (by romega)), State.setReg_regs_ne _ _ (by romega),
      hreg₁ r (Or.inl hr)]

end GraphMinor.Compute
