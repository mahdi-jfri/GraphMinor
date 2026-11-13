module

public import GraphMinor.Compute.GM06Alg34BoundaryFilterProg
public import GraphMinor.Compute.BitSet

/-!
# Exact output arrays for recomputed boundary lists

The boundary filter reserves the old label count and returns its live
length. Copy only that prefix into exact array 11. The resulting array
is ready for the length-prefixed stream writer, including an empty
boundary list. Both the finite selection and copy costs are bounded.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute a boundary list and copy its live words into exact array 11. -/
def gm06BoundaryListProg (mask ranks count : ℕ) : Cmd :=
  .seq (gm06BoundaryFilterProg mask ranks count)
    (readSliceProg 9 (.const 0) 11 (.reg 142) 210)

/-- The complete boundary-list program computes the exact selected
new-label array in at most `(18 * N + 55) * oldCount + 17` steps. -/
theorem gm06BoundaryListProg_exec {w n shift : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (mask ranks count : ℕ)
    (active : Fin n → Bool) (labels : Fin n → ℕ)
    (hmask9 : mask ≠ 9) (hranks9 : ranks ≠ 9)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hfit : shift + n ≤ x.cellCount)
    (hlabel : ∀ v, active v = true → labels v < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hmask : s.arrs mask = List.ofFn (fun u : Fin n => if active u then 1 else 0))
    (hranks : s.arrs ranks = List.ofFn labels) (hcount : s.regs count = n)
    (hshift : s.regs 208 = shift) :
    let words := gm06BoundaryWords (gm06BoundarySelection x vs a shift hfit active)
      labels (List.finRange n)
    ∃ s' t, Exec w (gm06BoundaryListProg mask ranks count) s s' t ∧
      t ≤ (18 * x.cellCount + 55) * n + 17 ∧ s'.arrs 11 = words ∧
      s'.regs 142 = words.length ∧
      (∀ j : ℕ, j ≠ 9 → j ≠ 11 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, q < 210 → q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 204 → q ≠ 205 → q ≠ 206 →
        q ≠ 207 → q ≠ 209 → s'.regs q = s.regs q) := by
  dsimp only
  let selected := gm06BoundarySelection x vs a shift hfit active
  let words := gm06BoundaryWords selected labels (List.finRange n)
  have hn : n < 2 ^ w := (by omega : n ≤ x.cellCount).trans_lt hN
  obtain ⟨s₁, t₁, hex₁, ht₁, hprefix, htotal, hlen, harr₁, hreg₁⟩ :=
    gm06BoundaryFilterProg_exec x vs a mask ranks count active labels hmask9 hranks9
      hw hN hsquare hfit hlabel ha hmarks hmat hc hmask hranks hcount hshift
  have hpfx : (s₁.arrs 9).take words.length = words := by rw [htotal] at hprefix; exact hprefix
  have hsplit : s₁.arrs 9 = [] ++ words ++ (s₁.arrs 9).drop words.length := by
    simpa only [List.nil_append, hpfx] using (List.take_append_drop words.length (s₁.arrs 9)).symm
  have hlength : words.length ≤ n := by
    simpa only [List.length_finRange] using gm06BoundaryWords_length_le selected labels (List.finRange n)
  have hwords : ∀ j ∈ words, j < 2 ^ w := by
    intro j hj
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hj
    have hs := (List.mem_filter.mp hv).2
    have hav : active v = true := by
      cases hh : active v with
      | false => simp only [selected, gm06BoundarySelection, hh, Bool.false_and, Bool.false_eq_true] at hs
      | true => rfl
    exact hlabel v hav
  obtain ⟨s₂, t₂, hex₂, ht₂, hout, harr₂, hreg₂⟩ := readSliceProg_exec
    (n := words.length) (off := 0) 9 11 (.const 0) 142 210 (by decide) (by decide)
    [] words ((s₁.arrs 9).drop words.length) rfl rfl hwords hw (by omega)
    (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw]) hsplit htotal
  refine ⟨s₂, t₁ + t₂, Exec.seq hex₁ hex₂, ?_, hout,
    (hreg₂ 142 (by decide)).trans htotal, ?_, ?_⟩
  · have hcost : (18 * x.cellCount + 55) * n = (18 * x.cellCount + 39) * n + 16 * n := by
      rw [show 18 * x.cellCount + 55 = (18 * x.cellCount + 39) + 16 by omega, Nat.add_mul]
    rw [hcost]
    simp only [Expr.cost_const] at ht₂
    omega
  · intro j hj₁ hj₂; exact (harr₂ j hj₂).trans (harr₁ j hj₁)
  · intro q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈
    exact (hreg₂ q hq).trans (hreg₁ q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈)

end GraphMinor.Compute
