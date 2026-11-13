module

public import GraphMinor.Compute.GM06Alg34Prepare
public import GraphMinor.Compute.GM06Alg34ClosureMatrixProg
import Mathlib.Tactic.Ring

/-!
# Preparing supplied incidence and division data for dual construction

Parse the cuff and division labels, then build the supplied closure
matrix. Restore the cuff count from its retained array after the matrix
scan. The header counts, label tables and matrix are exact finite
functions of the input array, with quadratic preparation time.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Parse the cuff and tags, build the matrix, and restore the cuff length. -/
def gm06DualSourcePrepareProg : Cmd :=
  .seq gm06PrepareCrossingProg (.seq gm06ClosureMatrixProg (.assign 105 (.len 2)))

private theorem source_registers : gm06DualSourcePrepareProg.writtenRegs ⊆ Finset.range 300 := by decide

private theorem source_budget (S : ℕ) :
    200 * (S + 1) + (120 * (S + 1) ^ 2 + 2) ≤ 400 * (S + 2) ^ 2 := by
  ring_nf
  omega

/-- A supplied disc cuff has no more positions than the encoded drawing size. -/
theorem gm06Dual_cuff_length_le_size (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) : L.length ≤ x.size := by
  have hcw := x.cuffWords_singleton_length hL
  have hw := x.words_length
  have hsize := x.words_length_le_size
  omega

/-- Complete source preparation yields exact header counts, supplied
cuff and division tables, and the incidence matrix in quadratic time. -/
theorem gm06DualSourcePrepareProg_exec (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) {c : ℕ} (hc : 2 ≤ c) {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06DualSourcePrepareProg s s' t ∧
      t ≤ 400 * (x.size + 2) ^ 2 ∧ s'.arrs 0 = x.words ∧
      s'.arrs 2 = L.map Fin.val ∧
      s'.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0) ∧
      s'.arrs 12 = gm06ClosureMatrixData x ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧ s'.regs 102 = x.regions.length ∧
      s'.regs 105 = L.length ∧ s'.regs 170 = x.cellCount ∧
      (∀ A : ℕ, A ≠ 2 → A ≠ 3 → A ≠ 12 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, 300 ≤ q → s'.regs q = s.regs q) := by
  have hc1 : 1 ≤ c := by omega
  have hkw : L.length < 2 ^ wordSize c x.size :=
    (gm06Dual_cuff_length_le_size x hL).trans_lt
      (lt_two_pow_wordSize_of_le hc1 (n := x.size) (Nat.le_succ _))
  obtain ⟨s₁, t₁, he₁, ht₁, hL₁, hD₁, _, _, _, _, _, _, _, ha₁, _⟩ :=
    gm06PrepareCrossingProg_exec x hL hc1 hinput
  obtain ⟨s₂, t₂, he₂, ht₂, hmat₂, hN₂, _, _, hn₂, hm₂, hr₂, ha₂, _⟩ :=
    gm06ClosureMatrixProg_exec x hc ((ha₁ 0 (by decide) (by decide)).trans hinput)
  have hL₂ : s₂.arrs 2 = L.map Fin.val := (ha₂ 2 (by decide)).trans hL₁
  let s₃ := s₂.setReg 105 L.length
  have he₃ : Exec (wordSize c x.size) (.assign 105 (.len 2)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hL₂, hkw])
  have he : Exec (wordSize c x.size) gm06DualSourcePrepareProg s s₃ (t₁ + (t₂ + 2)) :=
    .seq he₁ (.seq he₂ he₃)
  refine ⟨s₃, t₁ + (t₂ + 2), he,
    (show t₁ + (t₂ + 2) ≤ 200 * (x.size + 1) + (120 * (x.size + 1) ^ 2 + 2) by omega).trans
      (source_budget x.size), ?_, hL₂, (ha₂ 3 (by decide)).trans hD₁, hmat₂,
    hn₂, hm₂, hr₂, by simp [s₃], hN₂, ?_, ?_⟩
  · exact (ha₂ 0 (by decide)).trans ((ha₁ 0 (by decide) (by decide)).trans hinput)
  · intro A h2 h3 h12
    exact (ha₂ A h12).trans (ha₁ A h2 h3)
  · intro q hq
    apply he.regs_eq_of_not_mem_writtenRegs
    intro hm
    have hh := Finset.mem_range.mp (source_registers hm)
    omega

end GraphMinor.Compute
