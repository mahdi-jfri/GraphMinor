module

public import GraphMinor.Compute.GM06Alg34ComplementAdjRead

/-!
# Writing a complement adjacency matrix entry

For one packed cell pair, compute its adjacency bit from the original
masks and closure matrix and write that bit to matrix 28. The input,
closure matrix, and survival masks remain available for later pairs.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Write the complement adjacency bit for labels 180 and 181 to matrix 28. -/
def gm06ComplementMatEntryProg : Cmd :=
  .seq gm06ComplementAdjReadProg
    (.write 28 (.op .add (.op .mul (.reg 170) (.reg 180)) (.reg 181)) (.reg 184))

/-- One complement matrix entry takes at most 107 steps and changes
only that entry and the three active-bit scratch registers. -/
theorem gm06ComplementMatEntryProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a b : Fin x.cellCount) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = gm06ClosureMatrixData x)
    (hc : s.regs 170 = x.cellCount) (ha : s.regs 180 = a.val) (hb : s.regs 181 = b.val)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hv : s.arrs 4 = gm06VertexMask vs) (he : s.arrs 6 = gm06EdgeMask x vs)
    (hcap : (s.arrs 28).length = x.cellCount * x.cellCount) :
    ∃ s' t, Exec w gm06ComplementMatEntryProg s s' t ∧ t ≤ 107 ∧
      s'.arrs 28 = (s.arrs 28).set (x.cellCount * a.val + b.val)
        (if (x.complementGraph vs).Adj a b then 1 else 0) ∧
      (∀ k : ℕ, k ≠ 28 → s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 182 → q ≠ 183 → q ≠ 184 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t, hex, ht, hbit, harr, hreg⟩ :=
    gm06ComplementAdjReadProg_exec x vs a b hw hN hsquare hmat hc ha hb hn hm hv he
  have hc₁ : s₁.regs 170 = x.cellCount := (hreg _ (by decide) (by decide) (by decide)).trans hc
  have ha₁ : s₁.regs 180 = a.val := (hreg _ (by decide) (by decide) (by decide)).trans ha
  have hb₁ : s₁.regs 181 = b.val := (hreg _ (by decide) (by decide) (by decide)).trans hb
  have hidx : x.cellCount * a.val + b.val < x.cellCount * x.cellCount :=
    (Nat.add_lt_add_left b.isLt _).trans_le (by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ a.isLt)
  have hidxw := hidx.trans hsquare
  have hmulw : x.cellCount * a.val < 2 ^ w := (Nat.le_add_right _ _).trans_lt hidxw
  have haddr : (Expr.op .add (.op .mul (.reg 170) (.reg 180)) (.reg 181)).eval w s₁ =
      some (x.cellCount * a.val + b.val) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, ha₁, hb₁, hN,
      a.isLt.trans hN, b.isLt.trans hN, hmulw, hidxw]
  have hval : (Expr.reg 184).eval w s₁ =
      some (if (x.complementGraph vs).Adj a b then 1 else 0) := by
    by_cases hadj : (x.complementGraph vs).Adj a b <;>
      simp [Expr.eval, checkWord, hbit, hadj, hw, Nat.zero_lt_of_lt hw]
  let s₂ := s₁.writeArr 28 (x.cellCount * a.val + b.val)
    (if (x.complementGraph vs).Adj a b then 1 else 0)
  have hwrite : Exec w
      (.write 28 (.op .add (.op .mul (.reg 170) (.reg 180)) (.reg 181)) (.reg 184)) s₁ s₂ 7 :=
    .write haddr hval (by rw [harr, hcap]; exact hidx)
  refine ⟨s₂, t + 7, Exec.seq hex hwrite, by omega, ?_, ?_, ?_⟩
  · simp only [s₂, State.writeArr_arrs_self, harr]
  · intro k hk
    exact (State.writeArr_arrs_ne _ _ _ hk).trans (harr k)
  · exact hreg

end GraphMinor.Compute
