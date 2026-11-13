module

public import GraphMinor.Compute.GM06Alg34VertexMask
public import GraphMinor.Compute.Algorithm99OrderPrefix

/-!
# Numbering the surviving vertices on the RAM

An exclusive prefix sum of the zero-one active mask counts surviving
labels before each old label. These counts give the new vertex numbers
when the deletion payload is written. The prefix-sum pass reads only
the mask and leaves its total count in a register.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The number of active labels before each old vertex label. -/
def gm06VertexRanks {n : ℕ} (vs : List (Fin n)) : List ℕ :=
  List.ofFn (fun a : Fin n => ((gm06VertexMask vs).take a.val).sum)

/-- Every mask entry is zero or one, so its sum is at most the label count. -/
theorem gm06VertexMask_sum_le {n : ℕ} (vs : List (Fin n)) :
    (gm06VertexMask vs).sum ≤ n := by
  have hb : ∀ a ∈ gm06VertexMask vs, a ≤ 1 := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    split <;> omega
  have hh := List.sum_le_length_nsmul (gm06VertexMask vs) 1 hb
  simpa only [gm06VertexMask_length, smul_eq_mul, Nat.mul_one] using hh

/-- Build vertex ranks in array 5 from the active mask in array 4.
Registers 130 and 131 hold the scan counter and surviving count. -/
def gm06VertexRanksProg : Cmd := alg99BucketStartProg 4 5 130

/-- Vertex numbering takes linear time, preserves the active mask and
input, and returns the exact active count and exclusive prefix sums. -/
theorem gm06VertexRanksProg_exec {w n : ℕ} (vs : List (Fin n))
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    {s : State} (hmask : s.arrs 4 = gm06VertexMask vs) :
    ∃ s' t, Exec w gm06VertexRanksProg s s' t ∧ t ≤ 23 * n + 8 ∧
      s'.arrs 5 = gm06VertexRanks vs ∧ s'.regs 131 = (gm06VertexMask vs).sum ∧
      (∀ a : ℕ, a ≠ 5 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 130 → q ≠ 131 → s'.regs q = s.regs q) := by
  have hlen : (gm06VertexMask vs).length < 2 ^ w := by
    simpa only [gm06VertexMask_length] using hn
  have hsum := (gm06VertexMask_sum_le vs).trans_lt hn
  obtain ⟨s', t, hex, ht, hout, htotal, ha, hr⟩ :=
    alg99BucketStartProg_exec (gm06VertexMask vs) 4 5 130 (by decide) hw hlen hsum s hmask
  refine ⟨s', t, hex, ?_, ?_, htotal, ha, hr⟩
  · simpa only [gm06VertexMask_length] using ht
  · rw [hout]
    apply List.ext_getElem (by simp [gm06VertexRanks, gm06VertexMask_length])
    intro i hi hi'
    simp only [gm06VertexRanks, List.getElem_ofFn]

end GraphMinor.Compute
