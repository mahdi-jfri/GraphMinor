module

public import GraphMinor.Compute.GM06Alg34BranchRoots
public import GraphMinor.Compute.GM06Alg34BranchInit
public import GraphMinor.Compute.GM06Alg34BranchLoop
import GraphMinor.Compute.GM06Alg34RowEnumeration
import Mathlib.Tactic.Ring

/-!
# Computing the complete component branch queue

Compute and retain canonical component roots, save the original parent
input, allocate the queue, and emit each component's complete input in
root order. The resulting live queue prefix is exactly the finite list
of length-prefixed component payloads. The whole operation has polynomial
time and logarithmic words in the original array size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the complete canonical component branch queue from array 0 alone. -/
def gm06BranchProg : Cmd :=
  .seq gm06BranchRootsProg (.seq gm06BranchInitProg gm06BranchLoopProg)

private theorem branch_budget (n : ℕ) :
    300 * (n + 1) ^ 3 + ((n + 2) ^ 5 + 16 * n + 44) +
      ((1300 * (n + 2) ^ 3 + 11) * n + 1) ≤ 2000 * (n + 2) ^ 5 := by
  ring_nf
  omega

/-- The full component branching program emits exactly its canonical
component input records in polynomial time, from the original array
with arbitrary scratch contents. -/
theorem gm06BranchProg_exec (x : GM06DrawingData) {c : ℕ} (hc : 5 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06BranchProg s s' t ∧
      t ≤ 2000 * (x.size + 2) ^ 5 ∧
      IsPrefixBuffer 42 (gm06ComponentQueueWords x (List.finRange x.n))
        (gm06BranchCapacity x - (gm06ComponentQueueWords x (List.finRange x.n)).length) s' ∧
      s'.regs 5002 = (gm06ComponentQueueWords x (List.finRange x.n)).length ∧
      s'.regs 5005 = x.componentRoots.length ∧ s'.arrs 41 = x.words := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hin₁, hm₁, hn₁, hhead₁, hcount₁⟩ :=
    gm06BranchRootsProg_exec x (by omega : 2 ≤ c) hinput
  obtain ⟨s₂, t₂, hex₂, ht₂, _, hparent₂, hm₂, hb₂, _, hi₂, hp₂, hlen₂, hk₂, hleft₂⟩ :=
    gm06BranchInitProg_exec x hc hin₁ hn₁ hhead₁ hcount₁ hm₁
  have hqlen := gm06ComponentQueueWords_length_lt_capacity x
  have hqword := hqlen.trans (gm06BranchCapacity_lt_wordSize x hc)
  have hbuf : IsPrefixBuffer 42 []
      ((gm06ComponentQueueWords x (List.finRange x.n)).length +
        (gm06BranchCapacity x - (gm06ComponentQueueWords x (List.finRange x.n)).length)) s₂ := by
    simpa only [Nat.add_sub_of_le hqlen.le] using hb₂
  obtain ⟨s₃, t₃, hex₃, ht₃, hb₃, hp₃, _, _, ha₃, hg₃⟩ :=
    gm06BranchLoopProg_exec x (List.finRange x.n) (by omega : 3 ≤ c)
      (i := 0) (pfx := []) (by simp)
      (by simpa only [List.length_finRange] using (gm06Range_eq_finRange x.n).symm)
      hparent₂ hlen₂ hm₂ hi₂ (by simpa only [List.length_finRange] using hleft₂)
      (by simpa only [List.length_nil, Nat.zero_add] using hqword) hbuf hp₂
  have hprod := Nat.mul_le_mul_left (1300 * (x.size + 2) ^ 3 + 11) x.counts_le_size.1
  simp only [List.length_finRange] at ht₃
  have hcap := gm06BranchCapacity_le_power x
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃),
    (show t₁ + (t₂ + t₃) ≤ 300 * (x.size + 1) ^ 3 +
      ((x.size + 2) ^ 5 + 16 * x.size + 44) +
      ((1300 * (x.size + 2) ^ 3 + 11) * x.size + 1) by omega).trans (branch_budget x.size),
    by simpa only [List.nil_append] using hb₃,
    by simpa only [List.nil_append] using hp₃,
    (hg₃ 5005 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hk₂,
    (ha₃ 41 (by decide) (by decide)).trans hparent₂⟩

end GraphMinor.Compute
