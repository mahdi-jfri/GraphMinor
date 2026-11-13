module

public import GraphMinor.Compute.GM06CutRowEncoding
public import GraphMinor.Compute.GM06CutRowPositions
public import GraphMinor.Compute.GM06Alg34FilterMapArray

/-!
# Computing one induced cut row on the RAM

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) forms the
induced rotation on each vertex copy. This program filters the original row
using the computed local marks and positions, relabels every retained
end, and returns exactly the resulting row. The filter preserves order.
An unsplit vertex has its entire row in its left slot and an empty
right slot. The proof counts the scan and exact prefix extraction.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- An induced copied rotation cannot be longer than its original row. -/
theorem gm06CutSelectedRow_length_le (position : Option GM06CutPosition) (row : List ℕ) (left : Bool) :
    (gm06CutSelectedRow position row left).length ≤ row.length := by
  simp only [gm06CutSelectedRow, List.length_map]
  exact List.length_filter_le _ _

/-- Both path and nonpath output labels lie in the copied dart space. -/
theorem gm06CutOutputDart_lt {m d : ℕ} (position : Option GM06CutPosition) (left : Bool)
    (hd : d < 2 * m) : gm06CutOutputDart position left d < 4 * m := by
  cases position with
  | none => exact gm06CutDart_lt hd (by decide)
  | some p =>
    unfold gm06CutOutputDart gm06CutRowDart
    apply gm06CutDart_lt hd
    split_ifs <;> cases left <;> decide

private theorem selected_flatMap (position : Option GM06CutPosition) (row : List ℕ) (left : Bool) :
    row.flatMap (fun d => if gm06CutRetain position row left d then [gm06CutOutputDart position left d] else []) =
      gm06CutSelectedRow position row left := by
  unfold gm06CutSelectedRow
  generalize gm06CutRetain position row left = keep
  generalize gm06CutOutputDart position left = label
  induction row with
  | nil => rfl
  | cons d ds ih => cases h : keep d <;> simp [h, ih]

/-- Fixed expressions reading the current local cut metadata. -/
def gm06CutRowTest : Expr :=
  gm06CutEmitTestExpr (.reg 668) (.reg 652) (.reg 669) (.reg 670)
    (.reg 671) (.reg 672) (.reg 676) (.reg 677) (.read 614 (.reg 652)) (.reg 656)

/-- Fixed expression for the corresponding copied dart label. -/
def gm06CutRowLabel : Expr :=
  gm06CutEmitLabelExpr (.reg 652) (.reg 669) (.reg 670) (.reg 656)

/-- Read original rotation 611 and computed position table 614.
Return the exact selected row in 616, using buffer 615. Register 656
holds zero for the left copy and one for the right copy. -/
def gm06CutSelectRowProg : Cmd :=
  .seq (.alloc 615 (.len 611))
    (.seq (.assign 653 (.const 0))
      (.seq (gm06FilterMapArrayProg 611 615 650 651 652 653 gm06CutRowTest gm06CutRowLabel)
        (gm13TabulateProg 650 (.reg 653) (.read 615 (.reg 650)) 616)))

/-- Given the computed local metadata, the row program returns the
exact induced rotation in linear time. Its premises describe stored
input words and row positions, not a supplied side-assignment table. -/
theorem gm06CutSelectRowProg_exec {w m : ℕ}
    (position : Option GM06CutPosition) (row : List ℕ) (left : Bool) (s : State)
    (hw : 4 < 2 ^ w) (hm : 4 * m < 2 ^ w) (hl : row.length + 2 < 2 ^ w)
    (hnd : row.Nodup) (hkeys : ∀ d ∈ row, d < 2 * m)
    (h611 : s.arrs 611 = row) (h614 : s.arrs 614 = gm06RowPositions (2 * m) row)
    (h656 : s.regs 656 = (!left).toNat)
    (h668 : s.regs 668 = gm06CutPositionKind position)
    (h669 : s.regs 669 = gm06CutPositionIncoming position)
    (h670 : s.regs 670 = gm06CutPositionOutgoing position)
    (h671 : s.regs 671 = (gm06CutPositionCuffs position).1)
    (h672 : s.regs 672 = (gm06CutPositionCuffs position).2)
    (h676 : s.regs 676 = row.idxOf (gm06CutPositionBounds position).1)
    (h677 : s.regs 677 = row.idxOf (gm06CutPositionBounds position).2)
    (hwords : ∀ r ∈ [656, 668, 669, 670, 671, 672, 676, 677], s.regs r < 2 ^ w) :
    ∃ sf t, Exec w gm06CutSelectRowProg s sf t ∧ t ≤ 2000 * (row.length + 1) ∧
      Keeps [650, 651, 652, 653] [615, 616] s sf ∧
      sf.arrs 616 = gm06CutSelectedRow position row left := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hlen : row.length < 2 ^ w := by omega
  let out := gm06CutSelectedRow position row left
  have houtlen : out.length ≤ row.length := gm06CutSelectedRow_length_le _ _ _
  have houtwords : ∀ q ∈ out, q < 2 ^ w := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    exact (gm06CutOutputDart_lt position left (hkeys _ (List.mem_filter.mp hd).1)).trans hm
  let s₁ := s.setArr 615 (List.replicate row.length 0)
  let s₂ := s₁.setReg 653 0
  have he₁ : Exec w (.alloc 615 (.len 611)) s s₁ (1 + row.length) :=
    .alloc (GraphMinor.Compute.Crossing.eval_len h611 hlen)
  have he₂ : Exec w (.assign 653 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hinit : Keeps [650, 651, 652, 653] [615] s s₂ :=
    ((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _
  have hevals : ∀ z d, d ∈ row → (∀ A, A ≠ 615 → z.arrs A = s₂.arrs A) →
      (∀ r, r ≠ 650 → r ≠ 651 → r ≠ 652 → r ≠ 653 → z.regs r = s₂.regs r) →
      z.regs 652 = d →
      gm06CutRowTest.eval w z = some (if gm06CutRetain position row left d then 1 else 0) ∧
      gm06CutRowLabel.eval w z = some (gm06CutOutputDart position left d) := by
    intro z d hd harr hreg hcurrent
    have hfields : ∀ r ∈ [656, 668, 669, 670, 671, 672, 676, 677],
        (Expr.reg r).eval w z = some (s.regs r) := by
      intro r hr
      have hnot : r ≠ 650 ∧ r ≠ 651 ∧ r ≠ 652 ∧ r ≠ 653 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact GraphMinor.Compute.Crossing.eval_reg
        ((hreg _ hnot.1 hnot.2.1 hnot.2.2.1 hnot.2.2.2).trans
          (hinit.1 r (by simp [hnot]))) (hwords r hr)
    have hreadD : (Expr.reg 652).eval w z = some d :=
      GraphMinor.Compute.Crossing.eval_reg hcurrent ((hkeys d hd).trans (by omega))
    have hposArr : z.arrs 614 = gm06RowPositions (2 * m) row :=
      (harr 614 (by decide)).trans ((hinit.2 614 (by decide)).trans h614)
    have hidx : d < (z.arrs 614).length := by simpa [hposArr, gm06RowPositions_length] using hkeys d hd
    have hget : (z.arrs 614)[d]'hidx = row.idxOf d := by
      have hlookup := gm06RowPositions_getElem? (2 * m) row hnd d (hkeys d hd)
      rw [← hposArr, List.getElem?_eq_getElem hidx] at hlookup
      exact Option.some.inj hlookup
    have hreadPos : (Expr.read 614 (.reg 652)).eval w z = some (row.idxOf d) := by
      have he := GraphMinor.Compute.Crossing.eval_read hreadD hidx
        (by rw [hget]; exact List.idxOf_le_length.trans_lt hlen)
      simpa only [hget] using he
    have htag : (Expr.reg 656).eval w z = some (!left).toNat := by
      simpa only [h656] using hfields 656 (by simp)
    have ha : (Expr.reg 669).eval w z = some (gm06CutPositionIncoming position) := by
      simpa only [h669] using hfields 669 (by simp)
    have hb : (Expr.reg 670).eval w z = some (gm06CutPositionOutgoing position) := by
      simpa only [h670] using hfields 670 (by simp)
    exact ⟨gm06CutEmitTestExpr_eval position row left hw2 (by have := hkeys d hd; omega)
        (by simpa only [h668] using hfields 668 (by simp)) hreadD ha hb
        (by simpa only [h671] using hfields 671 (by simp))
        (by simpa only [h672] using hfields 672 (by simp))
        (by simpa only [h676] using hfields 676 (by simp))
        (by simpa only [h677] using hfields 677 (by simp)) hreadPos htag,
      gm06CutEmitLabelExpr_eval position left hw hm (hkeys d hd) hreadD ha hb htag⟩
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, ha₃, hr₃⟩ := gm06FilterMapArrayProg_exec
    (l := row) (pre := []) (cap := row.length) (s := s₂)
    611 615 650 651 652 653 gm06CutRowTest gm06CutRowLabel
    (gm06CutRetain position row left) (gm06CutOutputDart position left)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hw1 ((hinit.2 611 (by decide)).trans h611) hlen
    (fun d hd => (hkeys d hd).trans (by omega)) (by simp [GraphMinor.Compute.Crossing.IsBuf, s₂, s₁])
    (by rw [selected_flatMap]; exact houtlen) (by simpa using hl)
    (fun z d hd ha hr hc => (hevals z d hd ha hr hc).1)
    (fun z d hd _ ha hr hc => (hevals z d hd ha hr hc).2)
  have hbuffer : s₃.arrs 615 = out ++ List.replicate (row.length - out.length) 0 := by
    simpa only [selected_flatMap, List.nil_append] using hb₃.1
  have hcursor : s₃.regs 653 = out.length := by simpa only [selected_flatMap, List.nil_append] using hb₃.2
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm13TabulateProg_exec 650 (.reg 653) (.read 615 (.reg 650))
    616 out s₃ hw1 (houtlen.trans_lt hlen)
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg ((hk.1 653 (by decide)).trans hcursor)
      (houtlen.trans_lt hlen))
    (fun st i hi hk hidx => by
      have hbuf : st.arrs 615 = out ++ List.replicate (row.length - out.length) 0 :=
        (hk.2 615 (by decide)).trans hbuffer
      have he := GraphMinor.Compute.Crossing.eval_read (a := 615)
        (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans (houtlen.trans_lt hlen)))
        (by simp only [hbuf, List.length_append, List.length_replicate]; omega)
        (by simpa [hbuf, List.getElem_append_left hi] using houtwords _ (List.getElem_mem hi))
      simpa [hbuf, List.getElem_append_left hi] using he)
  have hk₃ : Keeps [650, 651, 652, 653] [615] s₂ s₃ := ⟨by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact hr₃ r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2, by
    intro A hA
    exact ha₃ A (by simpa using hA)⟩
  refine ⟨sf, (1 + row.length) + (2 + (t₃ + tf)), .seq he₁ (.seq he₂ (.seq he₃ hef)), ?_,
    ((hinit.trans hk₃ (fun _ h => h) (fun _ h => h)).mono (fun _ h => h) (by simp)).trans hkf
      (by simp) (by simp), hdf⟩
  have hcost : 31 + gm06CutRowTest.cost + gm06CutRowLabel.cost ≤ 2000 := by decide
  simp only [Expr.cost] at htf
  nlinarith

end GraphMinor.Compute
