module

public import GraphMinor.Compute.GM06MarkLabelRow
public import GraphMinor.Compute.GM06ListEncoding
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Marking labels from all given linkage rows

Scan the length-prefixed rows of the given linkage in VI (5.7), page 133.
A loop reads each row and adds its directed edge labels to a bitset.
The time is linear in the number of rows and their total length.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Mark the remaining rows, with their number in register 283. -/
def gm06MarkLabelRowsLoopProg (src dst : Arr) : Cmd :=
  .while (.reg 283)
    (.seq (gm06MarkLabelRowProg src dst)
      (.assign 283 (.op .sub (.reg 283) (.const 1))))

/-- The row loop marks exactly the labels in the supplied rows and
preserves every source array. -/
theorem gm06MarkLabelRowsLoopProg_exec {w N off : ℕ} (src dst : Arr) (hne : src ≠ dst)
    (rows : List (List (Fin N))) (tail : List ℕ) (S : Finset (Fin N))
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hcw : rows.length < 2 ^ w)
    (hend : off + (gm06EncodeRowsPayload (rows.map (List.map Fin.val))).length < 2 ^ w)
    {s : State}
    (hs : AtStream src off
      (gm06EncodeRowsPayload (rows.map (List.map Fin.val)) ++ tail) s)
    (hp : s.regs 280 = off) (hc : s.regs 283 = rows.length)
    (hbits : s.arrs dst = bitSetList S) :
    ∃ s' t, Exec w (gm06MarkLabelRowsLoopProg src dst) s s' t ∧
      t ≤ 22 * rows.length + 14 * rows.flatten.length + 1 ∧
      s'.arrs dst = bitSetList (S ∪ rows.flatten.toFinset) ∧
      s'.regs 280 = off + (gm06EncodeRowsPayload (rows.map (List.map Fin.val))).length ∧
      s'.regs 283 = 0 ∧
      AtStream src
        (off + (gm06EncodeRowsPayload (rows.map (List.map Fin.val))).length) tail s' ∧
      (∀ a : ℕ, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 280 → q ≠ 281 → q ≠ 282 → q ≠ 283 → s'.regs q = s.regs q) := by
  induction rows generalizing off S s with
  | nil =>
    refine ⟨s, 1, .while_false (eval_reg hc (Nat.two_pow_pos w)), by simp, ?_, ?_,
      hc, ?_, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
    · simpa using hbits
    · simpa [gm06EncodeRowsPayload] using hp
    · simpa [gm06EncodeRowsPayload] using hs
  | cons row rows ih =>
    have hsucc : rows.length + 1 < 2 ^ w := hcw
    have hlength : (gm06EncodeRowsPayload ((row :: rows).map (List.map Fin.val))).length =
        1 + row.length + (gm06EncodeRowsPayload (rows.map (List.map Fin.val))).length := by
      simp [gm06EncodeRowsPayload, gm06EncodeNatList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    have htotal : off + 1 + row.length +
        (gm06EncodeRowsPayload (rows.map (List.map Fin.val))).length < 2 ^ w := by
      rw [hlength] at hend
      omega
    have hs₀ : AtStream src off (row.length :: (row.map Fin.val ++
        (gm06EncodeRowsPayload (rows.map (List.map Fin.val)) ++ tail))) s := by
      simpa only [List.map_cons, gm06EncodeRowsPayload, List.flatMap_cons,
        gm06EncodeNatList, List.length_map, List.cons_append, List.append_assoc] using hs
    obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, hs₁, ha₁, hr₁⟩ :=
      gm06MarkLabelRowProg_exec src dst hne row _ S hw hN (by omega) hs₀ hp hbits
    have hc₁ : s₁.regs 283 = rows.length + 1 :=
      (hr₁ 283 (by decide) (by decide) (by decide)).trans hc
    let s₂ := s₁.setReg 283 rows.length
    have he₂ : Exec w (.assign 283 (.op .sub (.reg 283) (.const 1))) s₁ s₂ 4 := by
      apply Exec.assign
      simpa using eval_sub (eval_reg hc₁ hcw) (eval_const hw)
    have hp₂ : s₂.regs 280 = off + 1 + row.length := by
      simpa [s₂] using hp₁
    obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hp₃, hc₃, hs₃, ha₃, hr₃⟩ :=
      ih (off := off + 1 + row.length) (S := S ∪ row.toFinset) (s := s₂)
        (Nat.lt_of_succ_lt hsucc) htotal (hs₁.of_arr_eq rfl) hp₂ rfl hb₁
    have hoff : off + (gm06EncodeRowsPayload ((row :: rows).map (List.map Fin.val))).length =
        off + 1 + row.length + (gm06EncodeRowsPayload (rows.map (List.map Fin.val))).length := by
      rw [hlength]
      omega
    refine ⟨s₃, 1 + (t₁ + 4) + t₃,
      .while_true (eval_reg hc hcw) (Nat.succ_ne_zero _) (.seq he₁ he₂) he₃, ?_, ?_,
      hp₃.trans hoff.symm, hc₃, hoff.symm ▸ hs₃, ?_, ?_⟩
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
    · simpa only [List.flatten_cons, List.toFinset_append, Finset.union_assoc] using hb₃
    · intro a ha
      exact (ha₃ a ha).trans (ha₁ a ha)
    · intro q h280 h281 h282 h283
      rw [hr₃ q h280 h281 h282 h283]
      exact (State.setReg_regs_ne _ _ h283).trans (hr₁ q h280 h281 h282)

end GraphMinor.Compute
