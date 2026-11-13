module

public import GraphMinor.Compute.GM06Alg34PayloadSpace

/-!
# Allocating the induced payload buffer

The capacity expression reads the original header and array length.
Its cubic reservation covers the complete new payload. Allocation
preserves the original input and all computed deletion tables.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Reserve array 10 for the induced payload and start its output cursor. -/
def gm06PayloadAllocProg : Cmd := initPrefixBufferProg 10 gm06PayloadCapacityExpr 143

/-- Allocation reserves the exact new payload length plus unused capacity,
using only the original supplied array and its vertex count. -/
theorem gm06PayloadAllocProg_exec (x : GM06DrawingData) (vs : List (Fin x.n))
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = x.words)
    (hn : s.regs 100 = x.n) :
    ∃ s' t, Exec (wordSize c x.size) gm06PayloadAllocProg s s' t ∧
      t ≤ gm06PayloadCapacity x + 19 ∧
      IsPrefixBuffer 10 [] ((x.inducedData vs).words.length +
        (gm06PayloadCapacity x - (x.inducedData vs).words.length)) s' ∧
      s'.regs 143 = 0 ∧
      (∀ a : ℕ, a ≠ 10 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ 143 → s'.regs r = s.regs r) := by
  have hcap := gm06PayloadCapacity_lt_wordSize x hc
  have hbase : 1 < gm06PayloadCapacity x := by
    unfold gm06PayloadCapacity
    have h := Nat.le_self_pow (by decide : 3 ≠ 0) (x.size + 2)
    omega
  have hlen := (gm06Induced_words_le_serializationBudget x vs).trans
    (gm06SerializationBudget_le_capacity x)
  obtain ⟨s', t, hex, ht, hbuf, hpos, harr, hreg⟩ :=
    initPrefixBufferProg_exec 10 gm06PayloadCapacityExpr 143 (by omega)
      (gm06PayloadCapacityExpr_eval x hc hinput hn)
  refine ⟨s', t, hex, ?_, ?_, hpos, harr, hreg⟩
  · have hcost : gm06PayloadCapacityExpr.cost = 17 := by decide
    omega
  · simpa only [Nat.add_sub_of_le hlen] using hbuf

end GraphMinor.Compute
