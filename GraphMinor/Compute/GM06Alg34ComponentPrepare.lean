module

public import GraphMinor.Compute.GM06Alg34VertexAdjList
public import GraphMinor.Compute.GM06Alg34CuffParse
import Mathlib.Tactic.Ring

/-!
# Preparing repeated component queries

Build the finite endpoint graph's adjacency lists and read the one
supplied disc cuff. Save its label offset by subtracting the cuff
length from the parser's final cursor. The saved offset and length
allow each component query to scan the same supplied cuff words.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Prepare the component CSR and save the supplied cuff-label offset in 261. -/
def gm06ComponentPrepareProg : Cmd :=
  .seq gm06VertexAdjListProg (.seq gm06ReadDiscCuffProg
    (.assign 261 (.op .sub (.reg 103) (.reg 105))))

private theorem preparation_budget (n : ℕ) :
    27 * (n * n) + 62 * n + 54 + 100 * (n + 1) + 4 ≤ 250 * (n + 1) ^ 2 := by
  ring_nf
  omega

/-- The complete preparation reads only the original array and returns
all source data for repeated component queries, in quadratic time. -/
theorem gm06ComponentPrepareProg_exec (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) {c : ℕ} (hc : 2 ≤ c) {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06ComponentPrepareProg s s' t ∧
      t ≤ 250 * (x.size + 1) ^ 2 ∧ s'.arrs 0 = x.words ∧
      IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s' ∧
      (s'.arrs 32).length = x.n * x.n ∧ s'.regs 4 = x.n ∧ s'.regs 100 = x.n ∧
      s'.regs 105 = L.length ∧ s'.regs 261 = x.cuffOffset + 2 := by
  have hc1 : 1 ≤ c := by omega
  have hwordlen := x.words_length_lt_wordSize hc1
  have hclen := x.cuffWords_singleton_length hL
  have hoff : x.divisionOffset - L.length = x.cuffOffset + 2 := by
    unfold GM06DrawingData.divisionOffset
    omega
  have hposw := x.divisionOffset_lt_length.trans hwordlen
  have hlenw : L.length < 2 ^ wordSize c x.size := by
    unfold GM06DrawingData.divisionOffset at hposw
    omega
  have hstartw : x.cuffOffset + 2 < 2 ^ wordSize c x.size := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hadj₁, hlen₁, hsize₁, _, _, _, ha₁⟩ :=
    gm06VertexAdjListProg_exec x hc hinput
  obtain ⟨s₂, t₂, hex₂, ht₂, _, hn₂, _, _, hlen₂, hpos₂, _, ha₂, hg₂⟩ :=
    gm06ReadDiscCuffProg_exec x hL hc1 ((ha₁ 0 (by decide)).trans hinput)
  let s₃ := s₂.setReg 261 (x.cuffOffset + 2)
  have hex₃ : Exec (wordSize c x.size) (.assign 261 (.op .sub (.reg 103) (.reg 105))) s₂ s₃ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hpos₂, hlen₂,
      hposw, hlenw, hoff, hstartw])
  have hnsize := x.counts_le_size.1
  have hmsize := x.counts_le_size.2.1
  have hsquare := Nat.mul_le_mul hnsize hnsize
  have ht₁' : t₁ ≤ 27 * (x.size * x.size) + 62 * x.size + 54 := by omega
  refine ⟨s₃, t₁ + (t₂ + 4), .seq hex₁ (.seq hex₂ hex₃),
    (show t₁ + (t₂ + 4) ≤ 27 * (x.size * x.size) + 62 * x.size + 54 +
      100 * (x.size + 1) + 4 by omega).trans (preparation_budget x.size),
    (ha₂ 0 (by decide)).trans ((ha₁ 0 (by decide)).trans hinput),
    hadj₁.of_arrs_eq (ha₂ 30 (by decide)) (ha₂ 31 (by decide)) (ha₂ 32 (by decide)),
    ?_, (hg₂ 4 (by decide)).trans hsize₁, hn₂, hlen₂, by simp [s₃]⟩
  change (s₂.arrs 32).length = _
  rw [ha₂ 32 (by decide)]
  exact hlen₁

end GraphMinor.Compute
