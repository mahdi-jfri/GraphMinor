module

public import GraphMinor.Compute.CrossingOpsBasic
public import GraphMinor.Compute.TwoPathsCyc
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Counting selected vertices on the RAM

The component test in II (3.1) counts vertices satisfying membership
conditions. Sum a zero/one expression over the numbered vertices. The
loop keeps the prefix sum in a register and leaves all arrays unchanged.
All partial sums are bounded by the number of vertices, so the same word
bound suffices throughout the scan.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths Classical

/-- Scan vertex indices and add a zero/one expression to the output counter. -/
def gm02CountBitsProg (idx count : Reg) (limit value : Expr) : Cmd :=
  .seq (.assign count (.const 0)) (.seq (.assign idx (.const 0))
    (forUp idx limit (.assign count (.op .add (.reg count) value))))

/-- A zero/one list's prefix sum is at most the prefix length. -/
theorem gm02BitPrefix_sum_le (words : List ℕ) (hb : ∀ v ∈ words, v ≤ 1) (i : ℕ) :
    (words.take i).sum ≤ i := by
  have h := List.sum_le_length_nsmul (words.take i) 1
    (fun v hv => hb v (List.mem_of_mem_take hv))
  simpa only [smul_eq_mul, Nat.mul_one] using h.trans
    (by simpa only [smul_eq_mul, Nat.mul_one] using List.length_take_le i words)

/-- A scan computes exactly the sum of its bit values, in linear time.
The expression hypotheses specify the local data read by this loop. -/
theorem gm02CountBitsProg_exec {w : ℕ} (idx count : Reg) (hne : idx ≠ count)
    (limit value : Expr) (words : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : words.length < 2 ^ w)
    (hb : ∀ v ∈ words, v ≤ 1)
    (hlimit : ∀ st, Keeps [idx, count] [] s st → limit.eval w st = some words.length)
    (hvalue : ∀ st i (hi : i < words.length), Keeps [idx, count] [] s st →
      st.regs idx = i → value.eval w st = some words[i]) :
    ∃ s' t, Exec w (gm02CountBitsProg idx count limit value) s s' t ∧
      t ≤ 6 + limit.cost + words.length * (limit.cost + value.cost + 9) ∧
      Keeps [idx, count] [] s s' ∧ s'.regs count = words.sum := by
  let s₁ := s.setReg count 0
  let s₂ := s₁.setReg idx 0
  have hk₁ : Keeps [idx, count] [] s s₁ := (Keeps.refl _ _ s).setReg (by simp) _
  have hk₂ : Keeps [idx, count] [] s s₂ := hk₁.setReg (by simp) _
  let I : ℕ → State → Prop := fun i st => st.regs idx = i ∧
    Keeps [idx, count] [] s st ∧ st.regs count = (words.take i).sum
  have hI₀ : I 0 s₂ := by
    exact ⟨by simp [s₂], hk₂, by simp [s₂, s₁, Ne.symm hne]⟩
  obtain ⟨s', t, hex, ht, hI⟩ := forUp_exec' I words.length (value.cost + 3) hw hn
    (fun i hi st hI => ⟨hI.1, hlimit st hI.2.1⟩)
    (fun i hi st hI => by
      have hsum := gm02BitPrefix_sum_le words hb i
      have hnext := gm02BitPrefix_sum_le words hb (i + 1)
      have hsplit : (words.take (i + 1)).sum = (words.take i).sum + words[i] := by
        rw [List.take_succ_eq_append_getElem hi, List.sum_append, List.sum_singleton]
      have hfit : (words.take i).sum + words[i] < 2 ^ w := by
        rw [← hsplit]
        exact hnext.trans_lt ((Nat.succ_le_of_lt hi).trans_lt hn)
      have he : (.op .add (.reg count) value : Expr).eval w st =
          some ((words.take i).sum + words[i]) :=
        eval_add (eval_reg hI.2.2 (hsum.trans_lt (hi.trans hn)))
          (hvalue st i hi hI.2.1 hI.1) hfit
      let st' := st.setReg count ((words.take i).sum + words[i])
      have hexe : Exec w (.assign count (.op .add (.reg count) value)) st st'
          (value.cost + 3) := by
        convert (Exec.assign (r := count) he) using 1
        simp only [Expr.cost]
        omega
      refine ⟨st', value.cost + 3, hexe, le_rfl, ?_, ?_⟩
      · refine ⟨by simp, (hI.2.1.setReg (by simp) _).setReg (by simp) _, ?_⟩
        simp only [st', State.setReg_regs_ne _ _ (Ne.symm hne), State.setReg_regs_self]
        exact hsplit.symm
      · simpa only [st', State.setReg_regs_ne _ _ hne] using hI.1)
    s₂ hI₀
  have hinit₁ : Exec w (.assign count (.const 0)) s s₁ 2 := .assign (eval_const (Nat.two_pow_pos w))
  have hinit₂ : Exec w (.assign idx (.const 0)) s₁ s₂ 2 := .assign (eval_const (Nat.two_pow_pos w))
  refine ⟨s', 2 + (2 + t), .seq hinit₁ (.seq hinit₂ hex), ?_, hI.2.1, ?_⟩
  · have hc : limit.cost + 6 + (value.cost + 3) = limit.cost + value.cost + 9 := by omega
    rw [hc] at ht
    omega
  · simpa only [List.take_length] using hI.2.2

end GraphMinor.Compute
