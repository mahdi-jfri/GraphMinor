module

public import GraphMinor.Compute.GM06Alg34DualDivisionCandidate

/-!
# Serializing all canonical dual division blocks

Scan the supplied gap positions. The retained root mask chooses one
source for each class, whose mapped region labels are appended as a
record. The exact remaining-record reservation gives a polynomial
scan bound while preserving the input cuff, tags and gap incidence.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Scan gap sources counted in 7702, starting at 7701. -/
def gm06DualDivisionLoopProg : Cmd :=
  .while (.reg 7702) (.seq (.assign 7600 (.reg 7701))
    (.seq gm06DualDivisionCandidateProg
      (.seq (.assign 7701 (.op .add (.reg 7701) (.const 1)))
        (.assign 7702 (.op .sub (.reg 7702) (.const 1))))))

/-- The complete source scan emits exactly its canonical mapped class
records, with cubic work per source and a fixed outer memory frame. -/
theorem gm06DualDivisionLoopProg_exec {w i cap : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (g : Fin L.length → Fin x.regions.length) (V : List (Fin L.length))
    (hlabels : V.map Fin.val = List.range' i V.length) (hfitLabels : i + V.length ≤ L.length)
    {pre : List ℕ} {s : State} (hw : 2 < 2 ^ w) (hspan : L.length + 2 < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w) (hrw : x.regions.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length)
    (hregions : s.arrs 47 = List.ofFn (fun j => (g j).val))
    (hsource : s.arrs 53 = List.range L.length) (hmask : s.arrs 45 = gm06GapRootMask x L)
    (hindex : s.regs 7701 = i) (hleft : s.regs 7702 = V.length)
    (hbuf : IsPrefixBuffer 55 pre ((gm06DualDivisionRecordWords x L g V).length + cap) s)
    (hpos : s.regs 7804 = pre.length)
    (hfit : pre.length + (gm06DualDivisionRecordWords x L g V).length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualDivisionLoopProg s s' t ∧
      t ≤ (500 * (L.length + 1) ^ 3 + 16) * V.length + 1 ∧
      IsPrefixBuffer 55 (pre ++ gm06DualDivisionRecordWords x L g V) cap s' ∧
      s'.regs 7804 = (pre ++ gm06DualDivisionRecordWords x L g V).length ∧
      s'.regs 7701 = i + V.length ∧ s'.regs 7702 = 0 ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 54 → A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 7600 → q < 120 ∨ 126 ≤ q → q ≠ 0 → s'.regs q = s.regs q) := by
  have hkw : L.length < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  induction V generalizing i pre s with
  | nil =>
    have hz : s.regs 7702 = 0 := hleft
    refine ⟨s, 1, .while_false (by simp [Expr.eval, checkWord, hz, Nat.zero_lt_of_lt hw]),
      by simp, ?_, ?_, by simpa using hindex, hz, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    · simpa only [gm06DualDivisionRecordWords, List.filter_nil, List.flatMap_nil,
        List.length_nil, Nat.zero_add, List.append_nil] using hbuf
    · simpa only [gm06DualDivisionRecordWords, List.filter_nil, List.flatMap_nil, List.append_nil] using hpos
  | cons a V ih =>
    have hcons := List.cons.inj (by
      simpa only [List.map_cons, List.length_cons, List.range'_succ] using hlabels)
    have haval : a.val = i := hcons.1
    have htail : V.map Fin.val = List.range' (i + 1) V.length := hcons.2
    have hrec := gm06DualDivisionRecordWords_cons x L g a V
    have hrecLen := congrArg List.length hrec
    simp only [List.length_append] at hrecLen
    have hiw : i < 2 ^ w := haval ▸ a.isLt.trans hkw
    have hi1w : i + 1 < 2 ^ w := (by simp only [List.length_cons] at hfitLabels; omega : i + 1 ≤ L.length).trans_lt hkw
    have hleftw : V.length + 1 < 2 ^ w := (by simp only [List.length_cons] at hfitLabels; omega : V.length + 1 ≤ L.length).trans_lt hkw
    let s₀ := s.setReg 7600 i
    have he₀ : Exec w (.assign 7600 (.reg 7701)) s s₀ 2 := .assign (eval_reg hindex hiw)
    obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
      gm06DualDivisionCandidateProg_exec (s := s₀) x L hLN hDiv g a hw hspan hdouble hn hd hrw
        hL hD hbound (by simpa [s₀] using haval.symm) hregions hsource hmask
        (cap := (gm06DualDivisionRecordWords x L g V).length + cap)
        (by simpa only [hrecLen, Nat.add_assoc] using
          (hbuf.of_arr_eq (show s₀.arrs 55 = s.arrs 55 from rfl))) hpos (by omega)
    have hi₁ : s₁.regs 7701 = i :=
      (hg₁ 7701 (by decide) (Or.inr (by decide)) (by decide) (Or.inr (by decide)) (by decide)).trans hindex
    have hl₁ : s₁.regs 7702 = V.length + 1 :=
      (hg₁ 7702 (by decide) (Or.inr (by decide)) (by decide) (Or.inr (by decide)) (by decide)).trans hleft
    let s₂ := s₁.setReg 7701 (i + 1)
    have he₂ : Exec w (.assign 7701 (.op .add (.reg 7701) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi₁, hiw, hi1w, hw1])
    let s₃ := s₂.setReg 7702 V.length
    have hl₂ : s₂.regs 7702 = V.length + 1 := hl₁
    have he₃ : Exec w (.assign 7702 (.op .sub (.reg 7702) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hl₂, hleftw,
        show V.length < 2 ^ w by omega, hw1])
    obtain ⟨s₄, t₄, he₄, ht₄, hb₄, hp₄, hi₄, hz₄, ha₄, hg₄⟩ :=
      ih (s := s₃) (i := i + 1) (pre := pre ++ gm06DualSelectedClassWords x L g a)
        htail (by simp only [List.length_cons] at hfitLabels; omega)
        ((ha₁ 2 (by decide) (by decide) (by decide) (by decide)).trans hL)
        ((ha₁ 3 (by decide) (by decide) (by decide) (by decide)).trans hD)
        ((hg₁ 105 (by decide) (Or.inl (by decide)) (by decide) (Or.inl (by decide)) (by decide)).trans hbound)
        ((ha₁ 47 (by decide) (by decide) (by decide) (by decide)).trans hregions)
        ((ha₁ 53 (by decide) (by decide) (by decide) (by decide)).trans hsource)
        ((ha₁ 45 (by decide) (by decide) (by decide) (by decide)).trans hmask)
        (by simp [s₃, s₂]) (by simp [s₃]) hb₁ (by simpa [s₃, s₂] using hp₁)
        (by simp only [List.length_append]; omega)
    have hcond : (Expr.reg 7702).eval w s = some (V.length + 1) := by
      simp [Expr.eval, checkWord, hleft, hleftw]
    refine ⟨s₄, 1 + (2 + (t₁ + (4 + 4))) + t₄,
      .while_true hcond (by omega) (.seq he₀ (.seq he₁ (.seq he₂ he₃))) he₄,
      ?_, ?_, ?_, ?_, hz₄, ?_, ?_⟩
    · change _ ≤ (500 * (L.length + 1) ^ 3 + 16) * (V.length + 1) + 1
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · simpa only [hrec, List.append_assoc] using hb₄
    · simpa only [hrec, List.append_assoc] using hp₄
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hi₄
    · intro A h43 h54 h55 h56
      exact (ha₄ A h43 h54 h55 h56).trans (ha₁ A h43 h54 h55 h56)
    · intro q hq hrange h0
      exact (hg₄ q hq hrange h0).trans (by
        simp only [s₃, s₂, State.setReg, Function.update_of_ne (by omega : q ≠ 7702),
          Function.update_of_ne (by omega : q ≠ 7701)]
        exact (hg₁ q (by omega) hrange h0 (Or.inl (by omega)) (by omega)).trans
          (State.setReg_regs_ne _ _ (by omega : q ≠ 7600)))

end GraphMinor.Compute
