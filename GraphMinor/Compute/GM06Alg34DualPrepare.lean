module

public import GraphMinor.Compute.GM06Alg34DualInputBounds
public import GraphMinor.Compute.GM06Alg34DualGapPrepare
public import GraphMinor.Compute.GM06Alg34DualIndexArrays
import Mathlib.Tactic.Ring

/-!
# Complete supplied-data preparation for dual serialization

Prepare the cuff tags and incidence matrix, compute the canonical gap
classes, restore the matrix stride from the header counts and allocate
the source-label arrays. All tables needed by the dual serializer now
come from the original word input alone. The pending queue and its
outer cursors remain unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Recompute the packed cell stride after the gap-class preparation. -/
def gm06DualRestoreStrideProg : Cmd :=
  .assign 170 (.op .add (.reg 100) (.op .add (.reg 101) (.reg 102)))

/-- Build every source table required by the finite dual serializer. -/
def gm06DualPrepareProg : Cmd :=
  .seq gm06DualSourcePrepareProg (.seq gm06GapPrepareProg
    (.seq gm06DualRestoreStrideProg gm06DualIndexArraysProg))

private theorem prepare_budget (S : ℕ) :
    400 * (S + 2) ^ 2 + (440 * (S + 1) ^ 4 + (48 * S + 38)) ≤ 1000 * (S + 2) ^ 4 := by
  ring_nf
  omega

/-- All exact dual source tables and counters are prepared within a
quartic bound, with the supplied gap array and pending queue retained. -/
theorem gm06DualPrepareProg_exec (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    {c : ℕ} (hc : 4 ≤ c) {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06DualPrepareProg s s' t ∧
      t ≤ 1000 * (x.size + 2) ^ 4 ∧ s'.arrs 0 = x.words ∧
      s'.arrs 2 = L.map Fin.val ∧
      s'.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0) ∧
      s'.arrs 12 = gm06ClosureMatrixData x ∧ s'.arrs 45 = gm06GapRootMask x L ∧
      s'.arrs 50 = List.range x.n ∧ s'.arrs 51 = List.range x.ends.length ∧
      s'.arrs 52 = List.range x.regions.length ∧ s'.arrs 53 = List.range L.length ∧
      s'.regs 100 = x.n ∧ s'.regs 101 = x.ends.length ∧ s'.regs 102 = x.regions.length ∧
      s'.regs 105 = L.length ∧ s'.regs 170 = x.cellCount ∧
      s'.regs 275 = (x.dualGapDivision L).length ∧
      s'.arrs 47 = s.arrs 47 ∧ s'.arrs 42 = s.arrs 42 ∧
      (∀ A : ℕ, 58 ≤ A → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, 300 ≤ q → q ≠ 7900 → s'.regs q = s.regs q) := by
  have hc1 : 1 ≤ c := by omega
  have hc2 : 2 ≤ c := by omega
  have hsize := lt_two_pow_wordSize_of_le hc1 (n := x.size) (Nat.le_succ _)
  have hS := x.five_le_words_length.trans x.words_length_le_size
  have hw : 2 < 2 ^ wordSize c x.size := by omega
  have hw1 : 1 < 2 ^ wordSize c x.size := by omega
  have hcounts := x.counts_le_size
  have hnw := hcounts.1.trans_lt hsize
  have hmw := hcounts.2.1.trans_lt hsize
  have hrw := hcounts.2.2.trans_lt hsize
  have hkS := gm06Dual_cuff_length_le_size x hL
  have hkw := hkS.trans_lt hsize
  have hdouble := gm06Dual_double_cuff_lt_wordSize x hc2 hkS
  have hdw := (gm06Dual_division_length_le_size x).trans_lt hsize
  have hN := x.cellCount_le_size.trans_lt hsize
  obtain ⟨s₁, t₁, he₁, ht₁, hin₁, hL₁, hD₁, hmat₁, hn₁, hm₁, hr₁, hk₁, _, ha₁, hg₁⟩ :=
    gm06DualSourcePrepareProg_exec x hL hc2 hinput
  obtain ⟨s₂, t₂, he₂, ht₂, hmask₂, _, hcount₂, ha₂, hg₂⟩ :=
    gm06GapPrepareProg_exec x L hLN hDiv hw hkw hdouble hnw hdw hL₁ hD₁ hk₁
  have hn₂ : s₂.regs 100 = x.n := (hg₂ 100 (Or.inl (by decide)) (by decide)).trans hn₁
  have hm₂ : s₂.regs 101 = x.ends.length := (hg₂ 101 (Or.inl (by decide)) (by decide)).trans hm₁
  have hr₂ : s₂.regs 102 = x.regions.length := (hg₂ 102 (Or.inl (by decide)) (by decide)).trans hr₁
  have hk₂ : s₂.regs 105 = L.length := (hg₂ 105 (Or.inl (by decide)) (by decide)).trans hk₁
  let s₃ := s₂.setReg 170 x.cellCount
  have he₃ : Exec (wordSize c x.size) gm06DualRestoreStrideProg s₂ s₃ 6 := by
    refine .assign ?_
    have hN' : x.n + (x.ends.length + x.regions.length) < 2 ^ wordSize c x.size := hN
    have hmr : x.ends.length + x.regions.length < 2 ^ wordSize c x.size := by
      dsimp only [GM06DrawingData.cellCount] at hN
      omega
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hn₂, hm₂, hr₂,
      hnw, hmw, hrw, hmr, hN', GM06DrawingData.cellCount]
  obtain ⟨s₄, t₄, he₄, ht₄, h50, h51, h52, h53, ha₄, hg₄⟩ :=
    gm06DualIndexArraysProg_exec (s := s₃) hw1 hnw hmw hrw hkw hn₂ hm₂ hr₂ hk₂
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hkS 1) 4
  have ht₄' : t₄ ≤ 48 * x.size + 32 := by omega
  refine ⟨s₄, t₁ + (t₂ + (6 + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)),
    (show t₁ + (t₂ + (6 + t₄)) ≤
      400 * (x.size + 2) ^ 2 + (440 * (x.size + 1) ^ 4 + (48 * x.size + 38)) by omega).trans
        (prepare_budget x.size), ?_, ?_, ?_, ?_, ?_, h50, h51, h52, h53,
    (hg₄ 100 (by decide)).trans hn₂, (hg₄ 101 (by decide)).trans hm₂,
    (hg₄ 102 (by decide)).trans hr₂, (hg₄ 105 (by decide)).trans hk₂,
    (hg₄ 170 (by decide)).trans (State.setReg_regs_self _ _ _),
    (hg₄ 275 (by decide)).trans hcount₂, ?_, ?_, ?_, ?_⟩
  · exact (ha₄ 0 (by decide) (by decide) (by decide) (by decide)).trans
      ((ha₂ 0 (by decide) (by decide) (by decide) (by decide)).trans hin₁)
  · exact (ha₄ 2 (by decide) (by decide) (by decide) (by decide)).trans
      ((ha₂ 2 (by decide) (by decide) (by decide) (by decide)).trans hL₁)
  · exact (ha₄ 3 (by decide) (by decide) (by decide) (by decide)).trans
      ((ha₂ 3 (by decide) (by decide) (by decide) (by decide)).trans hD₁)
  · exact (ha₄ 12 (by decide) (by decide) (by decide) (by decide)).trans
      ((ha₂ 12 (by decide) (by decide) (by decide) (by decide)).trans hmat₁)
  · exact (ha₄ 45 (by decide) (by decide) (by decide) (by decide)).trans hmask₂
  · exact (ha₄ 47 (by decide) (by decide) (by decide) (by decide)).trans
      ((ha₂ 47 (by decide) (by decide) (by decide) (by decide)).trans (ha₁ 47 (by decide) (by decide) (by decide)))
  · exact (ha₄ 42 (by decide) (by decide) (by decide) (by decide)).trans
      ((ha₂ 42 (by decide) (by decide) (by decide) (by decide)).trans (ha₁ 42 (by decide) (by decide) (by decide)))
  · intro A hA
    exact (ha₄ A (by omega) (by omega) (by omega) (by omega)).trans
      ((ha₂ A (by omega) (by omega) (by omega) (by omega)).trans
        (ha₁ A (by omega) (by omega) (by omega)))
  · intro q hq h7900
    exact (hg₄ q h7900).trans ((State.setReg_regs_ne _ _ (by omega : q ≠ 170)).trans
      ((hg₂ q (Or.inr (by omega)) (by omega)).trans (hg₁ q hq)))

end GraphMinor.Compute
