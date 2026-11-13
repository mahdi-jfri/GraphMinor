module

public import GraphMinor.Compute.GM06Alg34ComplementMatEntry

/-!
# Scanning complement entries in row-major order

Divide the current flat matrix position by the cell count to obtain
its row, and take its remainder for the column. The existing entry
writer then updates precisely that position. A valid flat position
ensures the divisor is positive, even when the input may have no cells.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Derive the pair of packed labels from flat index 186 and write its
complement adjacency entry. -/
def gm06ComplementFlatEntryProg : Cmd :=
  .seq (.assign 180 (.op .div (.reg 186) (.reg 170)))
    (.seq (.assign 181 (.op .mod (.reg 186) (.reg 170))) gm06ComplementMatEntryProg)

/-- A valid flat position is filled with exactly its adjacency bit in
at most 115 steps, preserving all source arrays and the flat index. -/
theorem gm06ComplementFlatEntryProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (i : Fin (x.cellCount * x.cellCount)) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = gm06ClosureMatrixData x)
    (hc : s.regs 170 = x.cellCount) (hi : s.regs 186 = i.val)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hv : s.arrs 4 = gm06VertexMask vs) (he : s.arrs 6 = gm06EdgeMask x vs)
    (hcap : (s.arrs 28).length = x.cellCount * x.cellCount) :
    ∃ s' t, Exec w gm06ComplementFlatEntryProg s s' t ∧ t ≤ 115 ∧
      s'.arrs 28 = (s.arrs 28).set i.val
        (if (x.complementGraph vs).Adj i.divNat i.modNat then 1 else 0) ∧
      (∀ k : ℕ, k ≠ 28 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 180 → q ≠ 181 → q ≠ 182 → q ≠ 183 → q ≠ 184 →
        s'.regs q = s.regs q) := by
  have hpos : 0 < x.cellCount := by
    by_contra h
    have hzero : x.cellCount = 0 := by omega
    have hi' : i.val < 0 := by simpa only [hzero, Nat.zero_mul] using i.isLt
    omega
  have hiw := i.isLt.trans hsquare
  have hdivw := i.divNat.isLt.trans hN
  change i.val / x.cellCount < 2 ^ w at hdivw
  have hmodw := i.modNat.isLt.trans hN
  change i.val % x.cellCount < 2 ^ w at hmodw
  let s₁ := s.setReg 180 i.divNat.val
  let s₂ := s₁.setReg 181 i.modNat.val
  have hdiv : (Expr.op .div (.reg 186) (.reg 170)).eval w s = some i.divNat.val := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi, hc, hiw, hN,
      Nat.ne_of_gt hpos, hdivw]
  have hmod : (Expr.op .mod (.reg 186) (.reg 170)).eval w s₁ = some i.modNat.val := by
    simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi, hc, hiw, hN,
      Nat.ne_of_gt hpos, hmodw]
  have hex₁ : Exec w (.assign 180 (.op .div (.reg 186) (.reg 170))) s s₁ 4 := .assign hdiv
  have hex₂ : Exec w (.assign 181 (.op .mod (.reg 186) (.reg 170))) s₁ s₂ 4 := .assign hmod
  obtain ⟨s₃, t, hex₃, ht₃, hbuf, harr, hreg⟩ :=
    gm06ComplementMatEntryProg_exec x vs i.divNat i.modNat hw hN hsquare (s := s₂)
      hmat (by simpa [s₂, s₁] using hc) (by simp [s₂, s₁]) (by simp [s₂])
      (by simpa [s₂, s₁] using hn) (by simpa [s₂, s₁] using hm) hv he hcap
  refine ⟨s₃, 4 + (4 + t), Exec.seq hex₁ (Exec.seq hex₂ hex₃), by omega, ?_, harr, ?_⟩
  · have haddr : x.cellCount * i.divNat.val + i.modNat.val = i.val := by
      exact (Nat.add_comm _ _).trans (Nat.mod_add_div i.val x.cellCount)
    simpa only [haddr, s₂, s₁, State.setReg] using hbuf
  · intro q hq₁ hq₂ hq₃ hq₄ hq₅
    rw [hreg q hq₃ hq₄ hq₅]
    simp [s₂, s₁, State.setReg, Function.update_of_ne hq₁, Function.update_of_ne hq₂]

end GraphMinor.Compute
