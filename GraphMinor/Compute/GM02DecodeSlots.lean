module

public import GraphMinor.Compute.GM02CodeExpressions
public import GraphMinor.Compute.TwoPathsCyc

/-!
# Decoding candidate separator slots on the RAM

Expand the fixed number of digit assignments into a straight-line
program. It reads the graph's vertex count and a candidate integer code,
and writes the code's digits into the candidate-slot registers. All
other registers and every array are preserved. This supplies candidate
slots to the component test in II (3.1), page 316.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Decode successive base digits into the candidate-slot registers. -/
def gm02DecodeSlots : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (gm02DecodeSlots k) (.assign (200 + k) (gm02CodeDigitExpr k))

/-- The decoder writes precisely the required digits, preserving the input
and the code register. The bound depends only on the fixed slot count. -/
theorem gm02DecodeSlots_exec {w n code : ℕ} (k : ℕ) (s : State)
    (hrn : s.regs 40 = n) (hcode : s.regs 190 = code)
    (hb : n + 1 < 2 ^ w) (hc : code < 2 ^ w) (hp : (n + 1) ^ k < 2 ^ w) :
    ∃ s' t, Exec w (gm02DecodeSlots k) s s' t ∧ t ≤ 1 + k * (8 + 4 * k) ∧
      (∀ i : Fin k, s'.regs (200 + i.val) = gm02SeparatorDigit n code i.val) ∧
      (∀ r : Reg, r < 200 ∨ 200 + k ≤ r → s'.regs r = s.regs r) ∧ s'.arrs = s.arrs := by
  induction k with
  | zero =>
    exact ⟨s, 1, .skip s, le_rfl, fun i => Fin.elim0 i, fun _ _ => rfl, rfl⟩
  | succ k ih =>
    have hpk : (n + 1) ^ k < 2 ^ w :=
      (Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_succ k)).trans_lt hp
    obtain ⟨s₁, t₁, he₁, ht₁, hslots₁, hframe₁, harr₁⟩ := ih hpk
    have heval := gm02CodeDigitExpr_eval k s₁
      ((hframe₁ 40 (Or.inl (by decide))).trans hrn)
      ((hframe₁ 190 (Or.inl (by decide))).trans hcode) hb hc hpk
    let s₂ := s₁.setReg (200 + k) (gm02SeparatorDigit n code k)
    have he₂ : Exec w (.assign (200 + k) (gm02CodeDigitExpr k)) s₁ s₂ (8 + 4 * k) := by
      convert (Exec.assign (r := 200 + k) heval) using 1
      rw [gm02CodeDigitExpr_cost]
      omega
    refine ⟨s₂, t₁ + (8 + 4 * k), .seq he₁ he₂, ?_, ?_, ?_, ?_⟩
    · have heq : 1 + (k + 1) * (8 + 4 * (k + 1)) =
          (1 + k * (8 + 4 * k)) + (8 + 4 * k) + 4 * (k + 1) := by ring
      rw [heq]
      omega
    · intro i
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ i.isLt) with hi | hi
      · have hne : (200 + i.val : Reg) ≠ 200 + k := by dsimp only [Reg]; omega
        rw [show s₂.regs (200 + i.val) = s₁.regs (200 + i.val) from
          State.setReg_regs_ne _ _ hne]
        exact hslots₁ ⟨i.val, hi⟩
      · simp only [s₂, hi, State.setReg_regs_self]
    · intro r hr
      have hne : r ≠ 200 + k := by dsimp only [Reg] at hr ⊢; omega
      have hr' : r < 200 ∨ 200 + k ≤ r := by dsimp only [Reg] at hr ⊢; omega
      exact (State.setReg_regs_ne _ _ hne).trans (hframe₁ r hr')
    · exact harr₁

/-- The fixed list of registers holding the decoded candidate. -/
def gm02SlotRegs (k : ℕ) : List ℕ := List.ofFn (fun i : Fin k => 200 + i.val)

/-- The decoder's register bounds give an exact frame for composition. -/
theorem gm02DecodeSlots_keeps {k : ℕ} {s s' : State}
    (hframe : ∀ r : Reg, r < 200 ∨ 200 + k ≤ r → s'.regs r = s.regs r)
    (harr : s'.arrs = s.arrs) : TwoPaths.Keeps (gm02SlotRegs k) [] s s' := by
  constructor
  · intro r hr
    apply hframe r
    dsimp only [Reg]
    by_cases hlo : r < 200
    · exact Or.inl hlo
    · by_cases hhi : 200 + k ≤ r
      · exact Or.inr hhi
      · exfalso
        apply hr
        have hi : r - 200 < k := by omega
        exact List.mem_ofFn.2 ⟨⟨r - 200, hi⟩, by change 200 + (r - 200) = r; omega⟩
  · intro a _
    exact congrFun harr a

/-- Candidate slots do not overlap any register below 200. -/
theorem not_mem_gm02SlotRegs {k r : ℕ} (hr : r < 200) : r ∉ gm02SlotRegs k := by
  intro hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.1 hmem
  change 200 + i.val = r at hi
  omega

end GraphMinor.Compute
