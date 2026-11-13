module

public import GraphMinor.Compute.GM06Alg34ComplementAdjExpr

/-!
# A RAM lookup of complement adjacency

Read the two active flags, then combine them with the touching test
and the distinct-label test. The lookup leaves the input and all
computed arrays unchanged, so it can be repeated to fill a matrix.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the complement edge bit for packed labels 180 and 181 in
register 184, using active-flag scratch registers 182 and 183. -/
def gm06ComplementAdjReadProg : Cmd :=
  .seq (gm06ActiveCellReadProg 180 182)
    (.seq (gm06ActiveCellReadProg 181 183) (.assign 184 gm06ComplementAdjExpr))

/-- Complement adjacency is computed from the original masks and
closure matrix in at most one hundred steps, preserving every array. -/
theorem gm06ComplementAdjReadProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a b : Fin x.cellCount) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    {s : State} (hmat : s.arrs 12 = gm06ClosureMatrixData x)
    (hc : s.regs 170 = x.cellCount) (ha : s.regs 180 = a.val) (hb : s.regs 181 = b.val)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hv : s.arrs 4 = gm06VertexMask vs) (he : s.arrs 6 = gm06EdgeMask x vs) :
    ∃ s' t, Exec w gm06ComplementAdjReadProg s s' t ∧ t ≤ 100 ∧
      s'.regs 184 = (if (x.complementGraph vs).Adj a b then 1 else 0) ∧
      (∀ k, s'.arrs k = s.arrs k) ∧
      (∀ q : ℕ, q ≠ 182 → q ≠ 183 → q ≠ 184 → s'.regs q = s.regs q) := by
  let bitA : ℕ := if x.activeCell vs (x.cellNumbering.symm a) then 1 else 0
  let bitB : ℕ := if x.activeCell vs (x.cellNumbering.symm b) then 1 else 0
  let bit : ℕ := if (x.complementGraph vs).Adj a b then 1 else 0
  let s₁ := s.setReg 182 bitA
  let s₂ := s₁.setReg 183 bitB
  let s₃ := s₂.setReg 184 bit
  obtain ⟨t₁, hex₁, ht₁⟩ := gm06ActiveCellReadProg_exec x vs (x.cellNumbering.symm a) 180 182
    hw hN hn hm (by simpa only [Equiv.apply_symm_apply] using ha) hv he
  have hex₁' : Exec w (gm06ActiveCellReadProg 180 182) s s₁ t₁ := hex₁
  obtain ⟨t₂, hex₂, ht₂⟩ := gm06ActiveCellReadProg_exec x vs (x.cellNumbering.symm b) 181 183
    hw hN (s := s₁) (by simpa [s₁] using hn) (by simpa [s₁] using hm)
    (by simpa [s₁] using hb) hv he
  have hex₂' : Exec w (gm06ActiveCellReadProg 181 183) s₁ s₂ t₂ := hex₂
  have heval : gm06ComplementAdjExpr.eval w s₂ = some bit :=
    gm06ComplementAdjExpr_eval x vs a b hw hN hsquare hmat
      (by simpa [s₂, s₁] using hc) (by simpa [s₂, s₁] using ha)
      (by simpa [s₂, s₁] using hb) (by simp [s₂, s₁, bitA]) (by simp [s₂, bitB])
  have hex₃ : Exec w (.assign 184 gm06ComplementAdjExpr) s₂ s₃
      (gm06ComplementAdjExpr.cost + 1) := .assign heval
  refine ⟨s₃, t₁ + (t₂ + (gm06ComplementAdjExpr.cost + 1)),
    Exec.seq hex₁' (Exec.seq hex₂' hex₃), ?_, ?_, ?_, ?_⟩
  · have hcost : gm06ComplementAdjExpr.cost = 33 := by rfl
    rw [hcost]
    omega
  · simp [s₃, bit]
  · intro k; rfl
  · intro q hq₁ hq₂ hq₃
    simp [s₃, s₂, s₁, State.setReg, Function.update_of_ne hq₁,
      Function.update_of_ne hq₂, Function.update_of_ne hq₃]

end GraphMinor.Compute
