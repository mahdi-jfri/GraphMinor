module

public import GraphMinor.Compute.GM06Alg34MarkRegionBoundary

/-!
# Writing one complete region closure row

Compute the current row's offset in the square cell matrix. Mark the
region's own cell, then its supplied vertex and edge boundary lists.
The proof bounds every matrix address by the allocated square size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A row and column below the matrix size give an address in its square allocation. -/
theorem gm06MatrixAddress_lt {N i j : ℕ} (hi : i < N) (hj : j < N) : N * i + j < N * N := by
  calc
    N * i + j < N * i + N := Nat.add_lt_add_left hj _
    _ = N * (i + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ N * N := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hi)

/-- Write the region row indexed by register 171, with cell count in register 170. -/
def gm06RegionRowProg : Cmd :=
  .seq (.assign 173 (.op .mul (.reg 170) (.reg 171)))
    (.seq (.assign 174 (.const 0))
      (.seq (.assign 109 (.reg 171)) (.seq gm06MarkCellProg gm06MarkRegionBoundaryProg)))

/-- One region row receives its own cell and exactly the supplied
boundary incidences, with linear work in the two boundary lists. -/
theorem gm06RegionRowProg_exec {w off N i n : ℕ} (V E tail : List ℕ)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hn : n < 2 ^ w)
    (hi : i < N) (hsquare : N * N < 2 ^ w)
    (hoff : off + 2 + V.length + E.length < 2 ^ w) {s : State}
    (hs : AtStream 0 off (GM06DrawingData.listWords V ++ GM06DrawingData.listWords E ++ tail) s)
    (hp : s.regs 103 = off) (hNr : s.regs 170 = N) (hir : s.regs 171 = i)
    (hnr : s.regs 100 = n) (hcap : (s.arrs 12).length = N * N)
    (hV : ∀ v ∈ V, v < N) (hE : ∀ e ∈ E, n + e < N) :
    ∃ s' t, Exec w gm06RegionRowProg s s' t ∧ t ≤ 20 * (V.length + E.length) + 37 ∧
      s'.arrs 12 = gm06MarkCells (N * i) n E
        (gm06MarkCells (N * i) 0 V ((s.arrs 12).set (N * i + i) 1)) ∧
      s'.regs 103 = off + 2 + V.length + E.length ∧
      AtStream 0 (off + 2 + V.length + E.length) tail s' ∧
      s'.regs 173 = N * i ∧ s'.regs 174 = n ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 109 → q ≠ 172 → q ≠ 173 → q ≠ 174 →
        s'.regs q = s.regs q) := by
  have hindex : N * i + i < N * N := gm06MatrixAddress_lt hi hi
  have hindexw := hindex.trans hsquare
  have hroww : N * i < 2 ^ w := by omega
  have hiw := hi.trans hN
  let s₀ := s.setReg 173 (N * i)
  have he₀ : Exec w (.assign 173 (.op .mul (.reg 170) (.reg 171))) s s₀ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hNr, hir, hN, hiw, hroww])
  let s₁ := s₀.setReg 174 0
  have he₁ : Exec w (.assign 174 (.const 0)) s₀ s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let s₂ := s₁.setReg 109 i
  have he₂ : Exec w (.assign 109 (.reg 171)) s₁ s₂ 2 :=
    .assign (by simp [s₁, s₀, Expr.eval, checkWord, hir, hiw])
  obtain ⟨s₃, he₃, hbuf₃, ha₃, hr₃⟩ := gm06MarkCellProg_exec (s := s₂) (row := N * i) (shift := 0) (v := i) hw
    (by simpa using hindexw) (by simp [s₂, s₁, s₀]) (by simp [s₂, s₁])
      (by simp [s₂]) (by simpa [s₂, s₁, s₀, hcap] using hindex)
  have hrow₃ : s₃.regs 173 = N * i := by rw [hr₃ 173]; simp [s₂, s₁, s₀]
  have hn₃ : s₃.regs 100 = n := by rw [hr₃ 100]; simpa [s₂, s₁, s₀] using hnr
  have hp₃ : s₃.regs 103 = off := by rw [hr₃ 103]; simpa [s₂, s₁, s₀] using hp
  have hs₃ : AtStream 0 off
      (GM06DrawingData.listWords V ++ GM06DrawingData.listWords E ++ tail) s₃ :=
    hs.of_arr_eq (ha₃ 0 (by decide))
  have hcap₃ : (s₃.arrs 12).length = N * N := by
    rw [hbuf₃, List.length_set]
    exact hcap
  obtain ⟨s₄, t₄, he₄, ht₄, hbuf₄, hp₄, hs₄, hshift₄, _, hr₄⟩ :=
    gm06MarkRegionBoundaryProg_exec V E tail hw hn hoff hs₃ hp₃ hrow₃ hn₃
      (hcap₃ ▸ hsquare)
      (fun v hv => by rw [hcap₃]; simpa using gm06MatrixAddress_lt hi (hV v hv))
      (fun e he => by rw [hcap₃]; have hh := gm06MatrixAddress_lt hi (hE e he); omega)
  have hex : Exec w gm06RegionRowProg s s₄ (4 + (2 + (2 + (7 + t₄)))) :=
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄)))
  refine ⟨s₄, _, hex, by omega, ?_, hp₄, hs₄, ?_, hshift₄, ?_, ?_⟩
  · rw [hbuf₄, hbuf₃]
    rfl
  · exact (hr₄ 173 (by decide) (by decide) (by decide) (by decide)).trans hrow₃
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [gm06RegionRowProg, gm06MarkRegionBoundaryProg, gm06MarkCellListProg, gm06MarkCellLoopProg,
        gm06MarkCellProg, readStreamWordProg, Cmd.writtenArrs, ha])
  · intro q hqp hqv hqc hqr hqs
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [gm06RegionRowProg, gm06MarkRegionBoundaryProg, gm06MarkCellListProg, gm06MarkCellLoopProg,
        gm06MarkCellProg, readStreamWordProg, Cmd.writtenRegs, hqp, hqv, hqc, hqr, hqs])

end GraphMinor.Compute
