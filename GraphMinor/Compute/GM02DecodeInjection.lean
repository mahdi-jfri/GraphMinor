module

public import GraphMinor.Compute.GM02DecodeSlots
public import GraphMinor.Compute.GM02ValidateInjection

/-!
# Decoding and validating one injection candidate

Use the existing positional decoder with the host vertex count as its
base parameter. The fixed Boolean validator then checks the decoded
slots. Both commands preserve the original graph array and the candidate
counter, so an outer counting loop can test all candidates in turn.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- Decode the fixed pattern's vertex choices and check injection validity. -/
@[expose] def gm02DecodeInjectionProg (p : ℕ) : Cmd :=
  .seq (gm02DecodeSlots p) (gm02ValidateInjectionProg p)

/-- One candidate is decoded and validated in time depending only on the fixed pattern. -/
theorem gm02DecodeInjectionProg_exec {W n code : ℕ} (p : ℕ) (s : State)
    (hrn : s.regs 40 = n) (hcode : s.regs 190 = code)
    (hw : 1 < 2 ^ W) (hn : n + 1 < 2 ^ W) (hc : code < 2 ^ W)
    (hp : (n + 1) ^ p < 2 ^ W) :
    ∃ s' t, Exec W (gm02DecodeInjectionProg p) s s' t ∧
      t ≤ 2 + p * (8 + 4 * p) + (gm02InjectionValidExpr p).cost ∧
      s'.regs 193 = (if gm02InjectionCodeValid n p code then 1 else 0) ∧
      (∀ i : Fin p, s'.regs (200 + i.val) = gm02InjectionDigit n p code i) ∧
      s'.arrs = s.arrs ∧
      (∀ r, r ≠ 193 → (r < 200 ∨ 200 + p ≤ r) → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hslots, hr₁, ha₁⟩ :=
    gm02DecodeSlots_exec p s hrn hcode hn hc hp
  obtain ⟨s₂, he₂, hvalid, ha₂, hr₂⟩ := gm02ValidateInjectionProg_exec p s₁ hw hn
    ((hr₁ 40 (Or.inl (by decide))).trans hrn) hslots
  refine ⟨s₂, t₁ + ((gm02InjectionValidExpr p).cost + 1), .seq he₁ he₂,
    by omega, hvalid, ?_, ha₂.trans ha₁, ?_⟩
  · intro i
    exact (hr₂ (200 + i.val) (Nat.ne_of_gt ((by decide : 193 < 200).trans_le (Nat.le_add_right 200 i.val)))).trans (hslots i)
  · intro r hr hrange
    exact (hr₂ r hr).trans (hr₁ r hrange)

end GraphMinor.Compute
