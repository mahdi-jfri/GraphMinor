module

public import GraphMinor.Compute.GM06Alg34DualDivisionLoop

/-!
# The complete canonical dual division section

Write the computed number of classes, then scan all supplied gap
positions and append the records of their canonical roots. The final
word list is exactly the division section of the finite dual drawing.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Write the dual block count and all canonical mapped gap classes. -/
def gm06DualDivisionProg : Cmd :=
  .seq (appendWordProg 55 7804 (.reg 275))
    (.seq (.assign 7701 (.const 0))
      (.seq (.assign 7702 (.reg 105)) gm06DualDivisionLoopProg))

/-- The canonical mapped block scan writes the entire dual division
section with cubic work per supplied gap position. -/
theorem gm06DualDivisionProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (g : Fin L.length → Fin x.regions.length) {pre : List ℕ} {s : State}
    (hw : 2 < 2 ^ w) (hspan : L.length + 2 < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w) (hrw : x.regions.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length)
    (hregions : s.arrs 47 = List.ofFn (fun j => (g j).val))
    (hsource : s.arrs 53 = List.range L.length) (hmask : s.arrs 45 = gm06GapRootMask x L)
    (hcount : s.regs 275 = (x.dualGapDivision L).length)
    (hbuf : IsPrefixBuffer 55 pre
      (1 + (gm06DualDivisionRecordWords x L g (List.finRange L.length)).length + cap) s)
    (hpos : s.regs 7804 = pre.length)
    (hfit : pre.length + 1 + (gm06DualDivisionRecordWords x L g (List.finRange L.length)).length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualDivisionProg s s' t ∧
      t ≤ (500 * (L.length + 1) ^ 3 + 16) * L.length + 20 ∧
      IsPrefixBuffer 55 (pre ++ ((x.dualGapDivision L).length ::
        gm06DualDivisionRecordWords x L g (List.finRange L.length))) cap s' ∧
      s'.regs 7804 = (pre ++ ((x.dualGapDivision L).length ::
        gm06DualDivisionRecordWords x L g (List.finRange L.length))).length ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 54 → A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 7600 → q < 120 ∨ 126 ≤ q → q ≠ 0 → s'.regs q = s.regs q) := by
  have hk : L.length < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hclasses : (x.dualGapDivision L).length ≤ L.length := by
    simp only [GM06DrawingData.dualGapDivision, gm06ClassBlocks, List.length_map, gm06ClassRoots]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
    appendWordProg_exec (cap := (gm06DualDivisionRecordWords x L g (List.finRange L.length)).length + cap)
      (val := (x.dualGapDivision L).length) 55 7804 (.reg 275) hw1 (by omega)
      (by have heq : 1 + (gm06DualDivisionRecordWords x L g (List.finRange L.length)).length + cap =
        ((gm06DualDivisionRecordWords x L g (List.finRange L.length)).length + cap) + 1 := by omega
          exact heq ▸ hbuf) hpos
      (GraphMinor.Compute.Crossing.eval_reg hcount (hclasses.trans_lt hk))
  let s₂ := s₁.setReg 7701 0
  let s₃ := s₂.setReg 7702 L.length
  have he₂ : Exec w (.assign 7701 (.const 0)) s₁ s₂ 2 := .assign (GraphMinor.Compute.Crossing.eval_const (Nat.zero_lt_of_lt hw))
  have he₃ : Exec w (.assign 7702 (.reg 105)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg ((hg₁ 105 (by decide)).trans hbound) hk)
  obtain ⟨s₄, t₄, he₄, ht₄, hb₄, hp₄, _, _, ha₄, hg₄⟩ :=
    gm06DualDivisionLoopProg_exec (s := s₃) x L hLN hDiv g (List.finRange L.length)
      (i := 0) (by simp [List.range_eq_range']) (by simp) hw hspan hdouble hn hd hrw
      ((ha₁ 2 (by decide)).trans hL) ((ha₁ 3 (by decide)).trans hD)
      ((hg₁ 105 (by decide)).trans hbound) ((ha₁ 47 (by decide)).trans hregions)
      ((ha₁ 53 (by decide)).trans hsource) ((ha₁ 45 (by decide)).trans hmask)
      (by simp [s₃, s₂]) (by simp [s₃]) (hb₁.of_arr_eq rfl)
      (by simpa [s₃, s₂] using hp₁)
      (by simp only [List.length_append, List.length_singleton]; omega)
  refine ⟨s₄, t₁ + (2 + (2 + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_finRange] at ht₄
    simp only [Expr.cost] at ht₁
    omega
  · simpa only [List.append_assoc, List.singleton_append] using hb₄
  · simpa only [List.append_assoc, List.singleton_append] using hp₄
  · intro A h43 h54 h55 h56
    exact (ha₄ A h43 h54 h55 h56).trans (ha₁ A h55)
  · intro q hq hrange h0
    exact (hg₄ q hq hrange h0).trans (by
      simp only [s₃, s₂, State.setReg, Function.update_of_ne (by omega : q ≠ 7702),
        Function.update_of_ne (by omega : q ≠ 7701)]
      exact hg₁ q (by omega))

end GraphMinor.Compute
