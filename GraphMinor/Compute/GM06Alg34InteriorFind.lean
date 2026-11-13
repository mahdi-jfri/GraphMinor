module

public import GraphMinor.Compute.GM06Alg34InteriorFindLoop
public import GraphMinor.Compute.GM06Alg34ComponentPrepare
import GraphMinor.Compute.GM06Alg34RowEnumeration
import Mathlib.Tactic.Ring

/-!
# Finding a cuff-disjoint component from the supplied array

Prepare the endpoint CSR and cuff cursor, then scan every supplied
source label while retaining the first successful component query.
The resulting flag and label are exactly the finite first-component
search, with cubic time and logarithmic words in the original input.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Prepare and scan all vertex sources for a component away from the cuff. -/
def gm06InteriorFindProg : Cmd :=
  .seq gm06ComponentPrepareProg (.seq (.assign 187 (.const 0))
    (.seq (.assign 262 (.reg 100)) (.seq (.assign 113 (.const 0)) gm06InteriorFindLoopProg)))

private theorem find_budget (n : ℕ) :
    250 * (n + 1) ^ 2 + 6 + (26 * (n * n) + 45 * n + 50) * n + 1 ≤
      600 * (n + 1) ^ 3 := by
  ring_nf
  omega

/-- The RAM finds exactly the first finite cuff-disjoint component from
array 0, preserving the supplied input and computed CSR for deletion. -/
theorem gm06InteriorFindProg_exec (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) {c : ℕ} (hc : 2 ≤ c) {s : State} (hinput : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06InteriorFindProg s s' t ∧
      t ≤ 600 * (x.size + 1) ^ 3 ∧
      gm06SingletonRegs (x.findInteriorComponent.map Fin.val) s' ∧ s'.arrs 0 = x.words ∧
      IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s' ∧
      (s'.arrs 32).length = x.n * x.n ∧ s'.regs 4 = x.n ∧
      s'.regs 105 = L.length ∧ s'.regs 261 = x.cuffOffset + 2 := by
  have hc1 : 1 ≤ c := by omega
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hn := x.counts_le_size.1.trans_lt hsize
  have hw : 1 < 2 ^ wordSize c x.size := by
    have h := x.five_le_words_length
    have hh := x.words_length_le_size
    omega
  have hsquare := (Nat.mul_le_mul (x.counts_le_size.1.trans (by omega))
    (x.counts_le_size.1.trans (by omega))).trans_lt (sq_lt_two_pow_wordSize (n := x.size) hc)
  have hlen := x.words_length_lt_wordSize hc1
  have hLsize : L.length ≤ x.size := by
    have hclen := x.cuffWords_singleton_length hL
    have hwords := x.words_length
    have htotal := x.words_length_le_size
    omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hin₁, hadj₁, hlen₁, hsize₁, hn₁, hcount₁, hstart₁⟩ :=
    gm06ComponentPrepareProg_exec x hL hc hinput
  let s₂ := s₁.setReg 187 0
  let s₃ := s₂.setReg 262 x.n
  let s₄ := s₃.setReg 113 0
  have hex₂ : Exec (wordSize c x.size) (.assign 187 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hex₃ : Exec (wordSize c x.size) (.assign 262 (.reg 100)) s₂ s₃ 2 :=
    .assign (by simp [s₂, Expr.eval, checkWord, hn₁, hn])
  have hex₄ : Exec (wordSize c x.size) (.assign 113 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  obtain ⟨s₅, t₅, hex₅, ht₅, hfound₅, _, _, ha₅, hg₅⟩ :=
    gm06InteriorFindLoopProg_exec x hL (List.finRange x.n) none hw hn hsquare hlen
      (i := 0) (by simp)
      (by simpa only [List.length_finRange] using (gm06Range_eq_finRange x.n).symm)
      (s := s₄) hin₁ (by simpa [s₄, s₃, s₂] using hsize₁)
      (by simp [s₄, s₃, s₂]) (by simp [s₄, s₃])
      (by simpa [s₄, s₃, s₂] using hcount₁) (by simpa [s₄, s₃, s₂] using hstart₁)
      hadj₁ hlen₁ (by simp [gm06SingletonRegs, s₄])
  simp only [List.length_finRange] at ht₅
  have hnsize := x.counts_le_size.1
  have hsq := Nat.mul_le_mul hnsize hnsize
  have hscan := Nat.mul_le_mul (show
      26 * (x.n * x.n) + 23 * x.n + 22 * L.length + 50 ≤
      26 * (x.size * x.size) + 45 * x.size + 50 by omega) hnsize
  have htime : t₅ ≤ (26 * (x.size * x.size) + 45 * x.size + 50) * x.size + 1 := by omega
  have hkeep : ∀ q : ℕ, q = 4 ∨ q = 105 ∨ q = 261 → s₅.regs q = s₁.regs q := by
    intro q hq
    rcases hq with rfl | rfl | rfl <;>
      exact hg₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
  refine ⟨s₅, t₁ + (2 + (2 + (2 + t₅))), .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    (show t₁ + (2 + (2 + (2 + t₅))) ≤ 250 * (x.size + 1) ^ 2 + 6 +
      (26 * (x.size * x.size) + 45 * x.size + 50) * x.size + 1 by omega).trans (find_budget x.size),
    ?_, (ha₅ 0 (by decide) (by decide)).trans hin₁,
    hadj₁.of_arrs_eq (ha₅ 30 (by decide) (by decide)) (ha₅ 31 (by decide) (by decide)) (ha₅ 32 (by decide) (by decide)),
    ?_, (hkeep _ (by decide)).trans hsize₁, (hkeep _ (by decide)).trans hcount₁,
    (hkeep _ (by decide)).trans hstart₁⟩
  · simpa [GM06DrawingData.findInteriorComponent] using hfound₅
  · rw [ha₅ 32 (by decide) (by decide)]
    exact hlen₁

end GraphMinor.Compute
