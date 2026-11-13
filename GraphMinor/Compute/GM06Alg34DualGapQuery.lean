module

public import GraphMinor.Compute.GM06Alg34DualGapScanTwo

/-!
# A RAM query for the dual gap relation

Initialize the answer and scan all pairs of primal cuff positions. The
answer remains one precisely when no block pair separates the supplied
gaps. The two counted loops give a quadratic time bound.
-/

@[expose] public section
namespace GraphMinor.Compute

private theorem anyPrefix_fin_false {N : ℕ} (f : Fin N → Bool) :
    gm06AnyPrefix (fun v => if h : v < N then f ⟨v, h⟩ else false) N = false ↔
      ∀ i, f i = false := by
  rw [gm06AnyPrefix_eq_false]
  constructor
  · intro h i
    simpa only [dif_pos i.isLt] using h i.val i.isLt
  · intro h i hi
    simpa only [dif_pos hi] using h ⟨i, hi⟩

/-- The nested scan finds no separating pair exactly when the gaps are related. -/
theorem gm06GapScanTwoFlag_false_iff (x : GM06DrawingData)
    (L : List (Fin x.n)) (hL : L.Nodup) (hD : GM06.IsDivision x.divisionSet)
    (i j : Fin L.length) :
    gm06GapScanTwoFlag x L i j = false ↔ x.dualGapRelated L i j = true := by
  have hp : gm06GapScanTwoFlag x L i j = false ↔ gm06GapPairScan x L i j = false := by
    have hn : gm06GapScanTwoFlag x L i j = false ↔
        ∀ a b, gm06GapPairTest x L i j a b = false := by
      change gm06AnyPrefix _ L.length = false ↔ _
      rw [anyPrefix_fin_false]
      apply forall_congr'
      intro a
      change gm06AnyPrefix _ L.length = false ↔ _
      rw [anyPrefix_fin_false]
      apply forall_congr'
      intro b
      rw [gm06GapQuadTest, gm06GapPairPattern_eq x hL]
    rw [hn]
    constructor
    · intro h
      apply Bool.eq_false_iff.mpr
      intro ha
      obtain ⟨a, _, ha⟩ := List.any_eq_true.mp ha
      obtain ⟨b, _, hb⟩ := List.any_eq_true.mp ha
      rw [h a b] at hb
      cases hb
    · intro h a b
      apply Bool.eq_false_iff.mpr
      intro hb
      have ht : gm06GapPairScan x L i j = true :=
        List.any_eq_true.mpr ⟨a, List.mem_finRange a,
          List.any_eq_true.mpr ⟨b, List.mem_finRange b, hb⟩⟩
      rw [h] at ht
      cases ht
  rw [hp, gm06GapPairScan_eq_not_related x L hD i j]
  cases x.dualGapRelated L i j <;> decide

/-- Initialize the answer and test the two supplied gaps. -/
def gm06GapRelationProg : Cmd := .seq (.assign 0 (.const 1)) gm06GapScanTwoProg

/-- The RAM query computes the dual gap relation in quadratic time,
preserving every array and the two supplied gap registers. -/
theorem gm06GapRelationProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (i j : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) (hi : s.regs 120 = i.val)
    (hj : s.regs 121 = j.val) :
    ∃ s' t, Exec w gm06GapRelationProg s s' t ∧ t ≤ 250 * (L.length + 1) ^ 2 ∧
      s'.regs 0 = (if x.dualGapRelated L i j then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 122 → q ≠ 123 → q ≠ 124 → q ≠ 125 →
        s'.regs q = s.regs q) := by
  let s₀ := s.setReg 0 1
  have he₀ : Exec w (.assign 0 (.const 1)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, show 1 < 2 ^ w by omega])
  obtain ⟨s', t, he, ht, ha, harr, hreg⟩ := gm06GapScanTwoProg_exec x L i j
    (s := s₀) hw hk hdouble hn hd hL hD (by simpa [s₀] using hbound)
    (by simpa [s₀] using hi) (by simpa [s₀] using hj)
  have htime : 2 + (5 + L.length * (7 + (5 + L.length * 207))) ≤
      250 * (L.length + 1) ^ 2 := by ring_nf; omega
  refine ⟨s', 2 + t, .seq he₀ he, by omega, ?_, harr, ?_⟩
  · rw [ha]
    have hf := gm06GapScanTwoFlag_false_iff x L hLN hDiv i j
    cases hs : gm06GapScanTwoFlag x L i j <;>
      cases hr : x.dualGapRelated L i j <;> simp_all [s₀]
  · intro q hq hq122 hq123 hq124 hq125
    exact (hreg q hq hq122 hq123 hq124 hq125).trans
      (State.setReg_regs_ne _ _ hq)

end GraphMinor.Compute
