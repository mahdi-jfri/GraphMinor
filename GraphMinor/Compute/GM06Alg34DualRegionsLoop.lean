module

public import GraphMinor.Compute.GM06Alg34DualRegionRecord

/-!
# Serializing the transposed dual region section

Scan the old vertices in order, emitting their two transposed boundary
lists. The output invariant reserves the exact words of all remaining
records. Thus records may have different lengths while the already
written prefix and the final spare capacity remain explicit.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- The dual region records contributed by the supplied old vertex list. -/
def gm06DualRegionWords (x : GM06DrawingData) (L : List (Fin x.n)) : List ℕ :=
  L.flatMap (gm06DualRegionRecordWords x)

/-- Scan the remaining old vertex count 7702, starting at label 7701. -/
def gm06DualRegionsLoopProg : Cmd :=
  .while (.reg 7702) (.seq (.assign 7600 (.reg 7701))
    (.seq gm06DualRegionRecordProg
      (.seq (.assign 7701 (.op .add (.reg 7701) (.const 1)))
        (.assign 7702 (.op .sub (.reg 7702) (.const 1))))))

/-- Every transposed dual region record is appended in original vertex
order, preserving the exact remaining buffer capacity. -/
theorem gm06DualRegionsLoopProg_exec {w i cap : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hlabels : L.map Fin.val = List.range' i L.length)
    (hfitLabels : i + L.length ≤ x.n) {pre : List ℕ} {s : State}
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hRspan : x.regions.length + 2 < 2 ^ w) (hEspan : x.ends.length + 2 < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hregions : s.arrs 52 = List.range x.regions.length) (hedges : s.arrs 51 = List.range x.ends.length)
    (hindex : s.regs 7701 = i) (hleft : s.regs 7702 = L.length)
    (hbuf : IsPrefixBuffer 55 pre ((gm06DualRegionWords x L).length + cap) s)
    (hpos : s.regs 7804 = pre.length)
    (hfit : pre.length + (gm06DualRegionWords x L).length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualRegionsLoopProg s s' t ∧
      t ≤ (200 * (x.regions.length + x.ends.length + 2) + 13) * L.length + 1 ∧
      IsPrefixBuffer 55 (pre ++ gm06DualRegionWords x L) cap s' ∧
      s'.regs 7804 = (pre ++ gm06DualRegionWords x L).length ∧
      s'.regs 7701 = i + L.length ∧ s'.regs 7702 = 0 ∧
      (∀ A : ℕ, A ≠ 54 → A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7600 → s'.regs r = s.regs r) := by
  have hnN : x.n ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hnw := hnN.trans_lt hN
  induction L generalizing i pre s with
  | nil =>
    have hz : s.regs 7702 = 0 := hleft
    refine ⟨s, 1, .while_false (by simp [Expr.eval, checkWord, hz, Nat.zero_lt_of_lt hw]),
      by simp, ?_, ?_, by simpa using hindex, hz, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    · simpa only [gm06DualRegionWords, List.flatMap_nil, List.length_nil, Nat.zero_add,
        List.append_nil] using hbuf
    · simpa only [gm06DualRegionWords, List.flatMap_nil, List.append_nil] using hpos
  | cons v L ih =>
    have hcons := List.cons.inj (by
      simpa only [List.map_cons, List.length_cons, List.range'_succ] using hlabels)
    have hvval : v.val = i := hcons.1
    have htail : L.map Fin.val = List.range' (i + 1) L.length := hcons.2
    have hrec : gm06DualRegionWords x (v :: L) =
        gm06DualRegionRecordWords x v ++ gm06DualRegionWords x L := rfl
    have hrecLen := congrArg List.length hrec
    simp only [List.length_append] at hrecLen
    have hiw : i < 2 ^ w := hvval ▸ v.isLt.trans hnw
    have hi1w : i + 1 < 2 ^ w := (by simp only [List.length_cons] at hfitLabels; omega : i + 1 ≤ x.n).trans_lt hnw
    have hleftw : L.length + 1 < 2 ^ w := (by simp only [List.length_cons] at hfitLabels; omega : L.length + 1 ≤ x.n).trans_lt hnw
    let s₀ := s.setReg 7600 i
    have he₀ : Exec w (.assign 7600 (.reg 7701)) s s₀ 2 := .assign (eval_reg hindex hiw)
    obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
      gm06DualRegionRecordProg_exec (s := s₀) x v hw hN hsquare hRspan hEspan
        hmat hstride hn hm (by simpa [s₀] using hvval.symm) hregions hedges
        (cap := (gm06DualRegionWords x L).length + cap)
        (by simpa only [hrecLen, Nat.add_assoc] using
          (hbuf.of_arr_eq (show s₀.arrs 55 = s.arrs 55 from rfl))) hpos (by omega)
    have hi₁ : s₁.regs 7701 = i :=
      (hg₁ 7701 (by decide) (Or.inr (by decide)) (by decide)).trans hindex
    have hl₁ : s₁.regs 7702 = L.length + 1 :=
      (hg₁ 7702 (by decide) (Or.inr (by decide)) (by decide)).trans hleft
    let s₂ := s₁.setReg 7701 (i + 1)
    have he₂ : Exec w (.assign 7701 (.op .add (.reg 7701) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi₁, hiw, hi1w, hw])
    let s₃ := s₂.setReg 7702 L.length
    have hl₂ : s₂.regs 7702 = L.length + 1 := hl₁
    have he₃ : Exec w (.assign 7702 (.op .sub (.reg 7702) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hl₂, hleftw,
        show L.length < 2 ^ w by omega, hw])
    obtain ⟨s₄, t₄, he₄, ht₄, hb₄, hp₄, hi₄, hz₄, ha₄, hg₄⟩ :=
      ih (s := s₃) (i := i + 1) (pre := pre ++ gm06DualRegionRecordWords x v)
        htail (by simp only [List.length_cons] at hfitLabels; omega)
        ((ha₁ 12 (by decide) (by decide) (by decide)).trans hmat)
        ((hg₁ 170 (by decide) (Or.inl (by decide)) (by decide)).trans hstride)
        ((hg₁ 100 (by decide) (Or.inl (by decide)) (by decide)).trans hn)
        ((hg₁ 101 (by decide) (Or.inl (by decide)) (by decide)).trans hm)
        ((ha₁ 52 (by decide) (by decide) (by decide)).trans hregions)
        ((ha₁ 51 (by decide) (by decide) (by decide)).trans hedges)
        (by simp [s₃, s₂]) (by simp [s₃]) hb₁ (by simpa [s₃, s₂] using hp₁)
        (by simp only [List.length_append]; omega)
    have hcond : (Expr.reg 7702).eval w s = some (L.length + 1) := by
      simp [Expr.eval, checkWord, hleft, hleftw]
    refine ⟨s₄, 1 + (2 + (t₁ + (4 + 4))) + t₄,
      .while_true hcond (by omega) (.seq he₀ (.seq he₁ (.seq he₂ he₃))) he₄,
      ?_, ?_, ?_, ?_, hz₄, ?_, ?_⟩
    · change _ ≤ (200 * (x.regions.length + x.ends.length + 2) + 13) * (L.length + 1) + 1
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · simpa only [hrec, List.append_assoc] using hb₄
    · simpa only [hrec, List.append_assoc] using hp₄
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hi₄
    · intro A h54 h55 h56
      exact (ha₄ A h54 h55 h56).trans (ha₁ A h54 h55 h56)
    · intro r hr
      exact (hg₄ r hr).trans (by
        simp only [s₃, s₂, State.setReg, Function.update_of_ne (by omega : r ≠ 7702),
          Function.update_of_ne (by omega : r ≠ 7701)]
        exact (hg₁ r (by omega) (Or.inl (by omega)) (by omega)).trans
          (State.setReg_regs_ne _ _ (by omega : r ≠ 7600)))

end GraphMinor.Compute
