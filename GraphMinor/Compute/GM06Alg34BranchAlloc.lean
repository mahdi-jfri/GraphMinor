module

public import GraphMinor.Compute.GM06Alg34BranchSpace

/-!
# Allocating the component branch queue

Evaluate the verified reservation using the original input and its
saved vertex count. Initialize the queue's live cursor to zero. The
reservation fits a logarithmic word and covers all component records.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Reserve the component queue in array 42 and initialize cursor 5002. -/
def gm06BranchAllocProg : Cmd := initPrefixBufferProg 42 gm06BranchCapacityExpr 5002

/-- Queue allocation computes exactly the reservation from the supplied
parent array and count, preserving all other arrays and registers. -/
theorem gm06BranchAllocProg_exec (x : GM06DrawingData) {c : ℕ} (hc : 5 ≤ c)
    {s : State} (hinput : s.arrs 0 = x.words) (hn : s.regs 100 = x.n)
    (hcount : s.regs 5000 = x.n) :
    ∃ s' t, Exec (wordSize c x.size) gm06BranchAllocProg s s' t ∧
      t ≤ gm06BranchCapacity x + 25 ∧
      IsPrefixBuffer 42 [] (gm06BranchCapacity x) s' ∧ s'.regs 5002 = 0 ∧
      (∀ A : ℕ, A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 5002 → s'.regs q = s.regs q) := by
  have hcap := gm06BranchCapacity_lt_wordSize x hc
  have hw : 1 < 2 ^ wordSize c x.size := by
    have hh := x.five_le_words_length
    have hh' := x.words_length_le_size
    have hh'' := lt_two_pow_wordSize_of_le (by omega : 1 ≤ c) (n := x.size) (Nat.le_succ _)
    omega
  obtain ⟨s', t, hex, ht, hb, hp, ha, hg⟩ :=
    initPrefixBufferProg_exec 42 gm06BranchCapacityExpr 5002 hw
      (gm06BranchCapacityExpr_eval x hw hcap hcount
        (gm06PayloadCapacityExpr_eval x (by omega : 3 ≤ c) hinput hn))
  have hcost : gm06BranchCapacityExpr.cost = 23 := by decide
  exact ⟨s', t, hex, by omega, hb, hp, ha, hg⟩

end GraphMinor.Compute
