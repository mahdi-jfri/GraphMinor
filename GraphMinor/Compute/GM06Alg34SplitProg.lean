module

public import GraphMinor.Compute.GM06Alg34SplitLoop
public import GraphMinor.Compute.GM06Alg34VertexAdjList
public import GraphMinor.Compute.GM06Alg34CuffParse
import GraphMinor.Compute.GM06Alg34Prepare
import Mathlib.Tactic.Ring

/-!
# The component-split test from the original drawing array

Build the endpoint graph's adjacency lists and locate the supplied
division after the disc cuff. Initialize a conjunction and scan all
length-prefixed blocks. The result is exactly the complement of the
finite split test, in cubic time and logarithmic words.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Decide that no division block meets two components, using array 0 alone. -/
def gm06SplitProg : Cmd :=
  .seq gm06VertexAdjListProg (.seq gm06ReadDiscCuffProg
    (.seq (.assign 263 (.const 1))
      (.seq (readStreamWordProg 0 103 107) gm06SplitLoopProg)))

private theorem split_budget (n : ℕ) :
    (27 * (n * n) + 62 * n + 54) + (100 * (n + 1) +
      (2 + (8 + ((26 * (n * n) + 23 * n + 70) * n + 1)))) ≤
      500 * (n + 1) ^ 3 := by
  ring_nf
  omega

/-- The full component-split scan reads only the original supplied array,
returns exactly its finite rejection test, and takes cubic time. -/
theorem gm06SplitProg_exec (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) {c : ℕ} (hc : 2 ≤ c) {s : State}
    (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06SplitProg s s' t ∧
      t ≤ 500 * (x.size + 1) ^ 3 ∧
      s'.regs 263 = (if !x.hasSplitBlock then 1 else 0) ∧ s'.arrs 0 = x.words ∧
      IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s' ∧
      (s'.arrs 32).length = x.n * x.n ∧ s'.regs 4 = x.n := by
  have hc1 : 1 ≤ c := by omega
  have hwordlen := x.words_length_lt_wordSize hc1
  have hsz := x.words_length_le_size
  have hw : 1 < 2 ^ wordSize c x.size := by have h := x.five_le_words_length; omega
  have hn : x.n < 2 ^ wordSize c x.size :=
    x.counts_le_size.1.trans_lt (lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _))
  have hsquare : x.n * x.n < 2 ^ wordSize c x.size :=
    (Nat.mul_le_mul (x.counts_le_size.1.trans (by omega))
      (x.counts_le_size.1.trans (by omega))).trans_lt (sq_lt_two_pow_wordSize (n := x.size) hc)
  have hdiv : x.divisionWords = x.division.length :: gm06BlockStream x.division := by
    rw [x.divisionWords_eq]
    simp only [GM06DrawingData.raw, List.length_map, gm06BlockStream, List.flatMap_map]
  have hoff : x.divisionOffset + 1 + (gm06BlockStream x.division).length = x.words.length := by
    have hh := x.divisionOffset_add_length
    rw [hdiv, List.length_cons] at hh
    omega
  have hcnt := gm06BlockStream_count_le x.division
  have hcntw : x.division.length < 2 ^ wordSize c x.size := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hadj₁, hlen₁, hsize₁, _, _, _, ha₁⟩ :=
    gm06VertexAdjListProg_exec x hc hinput
  obtain ⟨s₂, t₂, hex₂, ht₂, _, _, _, _, _, hp₂, hs₂, ha₂, hg₂⟩ :=
    gm06ReadDiscCuffProg_exec x hL hc1 ((ha₁ 0 (by decide)).trans hinput)
  let s₃ := s₂.setReg 263 1
  have hex₃ : Exec (wordSize c x.size) (.assign 263 (.const 1)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  obtain ⟨s₄, t₄, hex₄, ht₄, hcnt₄, hp₄, hs₄, ha₄, hg₄⟩ :=
    readStreamWordProg_exec (x := x.division.length) (off := x.divisionOffset) (a_src := 0) (s := s₃) 103 107 (by decide) hw (by omega) hcntw
      (by simpa only [hdiv, List.append_nil] using hs₂.of_arr_eq (s' := s₃) rfl)
      (by simpa [s₃] using hp₂)
  have hadj₄ : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s₄ :=
    hadj₁.of_arrs_eq ((ha₄ 30).trans (ha₂ 30 (by decide)))
      ((ha₄ 31).trans (ha₂ 31 (by decide))) ((ha₄ 32).trans (ha₂ 32 (by decide)))
  have hlen₄ : (s₄.arrs 32).length = x.n * x.n := by
    rw [ha₄ 32, show s₃.arrs 32 = s₂.arrs 32 from rfl, ha₂ 32 (by decide)]
    exact hlen₁
  have hsize₄ : s₄.regs 4 = x.n := by
    rw [hg₄ 4 (by decide) (by decide)]
    exact (State.setReg_regs_ne _ _ (by decide)).trans ((hg₂ 4 (by decide)).trans hsize₁)
  obtain ⟨s₅, t₅, hex₅, ht₅, hans₅, _, _, _, ha₅, hg₅⟩ :=
    gm06SplitLoopProg_exec x x.division [] true hw hn hsquare (hoff.symm ▸ hwordlen)
      hsize₄ hadj₄ hlen₄ (by simpa only [List.append_nil] using hs₄) hp₄ hcnt₄
      (by rw [hg₄ 263 (by decide) (by decide)]; simp [s₃])
  have hneg : x.division.all (fun B => !x.isSplitBlock B) = !x.hasSplitBlock := by
    unfold GM06DrawingData.hasSplitBlock
    generalize x.division = D
    induction D with
    | nil => rfl
    | cons B D ih =>
      simp only [List.all_cons, List.any_cons, ih]
      cases x.isSplitBlock B <;> cases D.any x.isSplitBlock <;> rfl
  have hnsize := x.counts_le_size.1
  have hmsize := x.counts_le_size.2.1
  have hnsquare := Nat.mul_le_mul hnsize hnsize
  have ht₁' : t₁ ≤ 27 * (x.size * x.size) + 62 * x.size + 54 := by omega
  have hbytes : (gm06BlockStream x.division).length ≤ x.size := by omega
  have hprod := Nat.mul_le_mul
    (show 26 * (x.n * x.n) + 23 * x.n + 70 ≤
      26 * (x.size * x.size) + 23 * x.size + 70 by omega) hbytes
  refine ⟨s₅, t₁ + (t₂ + (2 + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    (show t₁ + (t₂ + (2 + (t₄ + t₅))) ≤
      (27 * (x.size * x.size) + 62 * x.size + 54) +
        (100 * (x.size + 1) + (2 + (8 +
          ((26 * (x.size * x.size) + 23 * x.size + 70) * x.size + 1)))) by omega).trans
      (split_budget x.size), ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Bool.true_and, hneg] using hans₅
  · exact (ha₅ 0 (by decide) (by decide)).trans
      ((ha₄ 0).trans ((ha₂ 0 (by decide)).trans ((ha₁ 0 (by decide)).trans hinput)))
  · exact hadj₄.of_arrs_eq (ha₅ 30 (by decide) (by decide))
      (ha₅ 31 (by decide) (by decide)) (ha₅ 32 (by decide) (by decide))
  · rw [ha₅ 32 (by decide) (by decide)]
    exact hlen₄
  · exact (hg₅ 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hsize₄

end GraphMinor.Compute
