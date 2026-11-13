module

public import GraphMinor.Compute.Case3StepsRecordPrefixProg

/-!
# Joining an uncounted section to the block buffer

The wall section and the four corners have their lengths fixed by the
format. They are joined to the current suffix without adding a count word.
The existing prefix operation uses separate scratch, after which the joined
list is copied back into the suffix buffer.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Insert an uncounted section before buffer 51. -/
def case3JoinRecordProg (a_pre : ℕ) : Cmd :=
  .seq (case3RecordPrefixProg a_pre) (copyArrLoopProg 52 51 125 126)

/-- Joining an uncounted section costs linear time and retains its source. -/
theorem case3JoinRecordProg_exec {w : ℕ} (a_pre : ℕ) (hne : a_pre ≠ 52)
    (pre suf : List ℕ) (hw : 1 < 2 ^ w) (hlen : pre.length + suf.length < 2 ^ w)
    (hprew : ∀ x ∈ pre, x < 2 ^ w) (hsufw : ∀ x ∈ suf, x < 2 ^ w)
    {s : State} (hpre : s.arrs a_pre = pre) (hsuf : s.arrs 51 = suf) :
    ∃ s' t, Exec w (case3JoinRecordProg a_pre) s s' t ∧
      t ≤ 100 * (pre.length + suf.length + 1) ∧ s'.arrs 51 = pre ++ suf ∧
      (∀ a, a ≠ 51 → a ≠ 52 → a ≠ 53 → s'.arrs a = s.arrs a) ∧
      (∀ r < 124, s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, _, harr₁, hreg₁⟩ :=
    case3RecordPrefixProg_exec a_pre hne pre suf hw hlen hprew hsufw hpre hsuf
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, harr₂, hreg₂⟩ := copyArrLoopProg_exec 52 51 125 126
    (by decide) (by decide) hw s₁ (by rw [hbuf₁, List.length_append]; exact hlen)
    (by rw [hbuf₁]; intro x hx; rcases List.mem_append.mp hx with hx | hx
        exact hprew x hx
        exact hsufw x hx)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, hbuf₂.trans hbuf₁, ?_, ?_⟩
  · rw [hbuf₁, List.length_append] at ht₂
    omega
  · intro a h51 h52 h53
    exact (harr₂ a h51).trans (harr₁ a h52 h53)
  · intro r hr
    rw [hreg₂ r (by romega) (by romega), hreg₁ r hr]

end GraphMinor.Compute
