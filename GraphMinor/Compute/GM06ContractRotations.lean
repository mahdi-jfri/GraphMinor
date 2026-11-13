module

public import GraphMinor.Compute.GM06ReplaceRotationRow
import GraphMinor.Compute.GM06RowPositions
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Updating both rotation rows of an initial-edge contraction

For Reduction 3 in VI (5.7), page 133, the edge-end labels stay in
their original positions. Read the two endpoint rotations, splice
out the contracted edge, install the merged order at the initial
vertex and empty the retired vertex's row. Every other rotation
row stays fixed. The encoding loses exactly two directed ends.
The temporary table and all work arrays have linear size.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

private theorem row_length_lt_code (rows : List (List ℕ)) {i : ℕ} (hi : i < rows.length) :
    rows[i].length < (gm06EncodeRows rows).length := by
  have hh := gm06RowsPrefixLength_le rows (i + 1)
  rw [gm06RowsPrefixLength_succ rows hi] at hh
  simp only [gm06EncodeRows, List.length_cons]
  omega

private theorem row_count_lt_code (rows : List (List ℕ)) :
    rows.length < (gm06EncodeRows rows).length := by
  have hh : rows.length ≤ (gm06EncodeRowsPayload rows).length := by
    induction rows with
    | nil => simp [gm06EncodeRowsPayload]
    | cons row rows ih =>
      simp only [gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons] at *
      omega
  simp only [gm06EncodeRows, List.length_cons]
  omega

private theorem row_word_mem_code (rows : List (List ℕ)) {i x : ℕ}
    (hi : i < rows.length) (hx : x ∈ rows[i]) : x ∈ gm06EncodeRows rows := by
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  exact ⟨rows[i], List.getElem_mem hi, by simp [gm06EncodeNatList, hx]⟩

/-- Merge the rotation at initial vertex 22 with that at neighbour
301, using contracted directed ends 23 and 24, and retire row 301. -/
@[expose] def gm06ContractRotationsProg : Cmd :=
  .seq (.assign 31 (.reg 22))
    (.seq (gm06SelectRowProg 4 25)
      (.seq (.assign 31 (.reg 301))
        (.seq (gm06SelectRowProg 4 26)
          (.seq gm06SpliceRotationRowsProg
            (.seq (.assign 31 (.reg 22))
              (.seq gm06ReplaceRotationRowProg
                (.seq (.alloc 27 (.const 0))
                  (.seq (.assign 31 (.reg 301)) gm06ReplaceRotationRowProg))))))))

/-- The contraction's two rotation-table writes preserve the other
rows and remove exactly two directed ends. Both searches use only
the input rows, and the full update has a linear time bound. -/
theorem gm06ContractRotationsProg_exec {w : ℕ} (rows : List (List ℕ))
    (a b d e : ℕ) (ha : a < rows.length) (hb : b < rows.length) (hab : a ≠ b)
    (hnda : rows[a].Nodup) (hndb : rows[b].Nodup) (hd : d ∈ rows[a]) (he : e ∈ rows[b])
    (s : State) (hw : 2 < 2 ^ w) (hn : 4 * (gm06EncodeRows rows).length < 2 ^ w)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (h4 : s.arrs 4 = gm06EncodeRows rows) (h22 : s.regs 22 = a) (h301 : s.regs 301 = b)
    (h23 : s.regs 23 = d) (h24 : s.regs 24 = e) :
    ∃ s' t, Exec w gm06ContractRotationsProg s s' t ∧
      t ≤ 600 + 1000 * (gm06EncodeRows rows).length ∧
      Keeps [31, 7, 8, 9, 11, 320, 317, 319, 313, 323, 324, 98] [25, 26, 27, 4, 28] s s' ∧
      s'.arrs 4 = gm06EncodeRows ((rows.set a
        (gm06SplicedRotation rows[a] rows[b] (rows[a].idxOf d) (rows[b].idxOf e))).set b []) ∧
      (s'.arrs 4).length + 2 = (gm06EncodeRows rows).length := by
  let merged := gm06SplicedRotation rows[a] rows[b] (rows[a].idxOf d) (rows[b].idxOf e)
  let rows₁ := rows.set a merged
  have hxlen := row_length_lt_code rows ha
  have hylen := row_length_lt_code rows hb
  have hcount := row_count_lt_code rows
  have hN : (gm06EncodeRows rows).length < 2 ^ w := by omega
  have haw : a < 2 ^ w := ha.trans hcount |>.trans hN
  have hbw : b < 2 ^ w := hb.trans hcount |>.trans hN
  have hxy : rows[a].length + rows[b].length < 2 ^ w := by omega
  have hax : ∀ x ∈ rows[a], x < 2 ^ w := fun x h => hx x (row_word_mem_code rows ha h)
  have hbx : ∀ x ∈ rows[b], x < 2 ^ w := fun x h => hx x (row_word_mem_code rows hb h)
  have hp : rows[a].idxOf d < rows[a].length := List.idxOf_lt_length_iff.mpr hd
  have hq : rows[b].idxOf e < rows[b].length := List.idxOf_lt_length_iff.mpr he
  have hmerged : merged.length + 2 = rows[a].length + rows[b].length :=
    gm06SplicedRotation_length rows[a] rows[b] hp hq
  have hmwords : ∀ x ∈ merged, x < 2 ^ w := by
    intro x hm
    rcases gm06SplicedRotation_mem hm with hm | hm
    · exact hax x hm
    · exact hbx x hm
  have hmlen : merged.length < 2 ^ w := by omega
  have hrow₁len : (gm06EncodeRows rows₁).length + rows[a].length =
      (gm06EncodeRows rows).length + merged.length := gm06EncodeRows_set_length rows a ha merged
  have hN₁ : (gm06EncodeRows rows₁).length < 2 ^ w := by omega
  have hwords₁ : ∀ x ∈ gm06EncodeRows rows₁, x < 2 ^ w :=
    gm06EncodeRows_set_words rows a ha merged hx hmwords hmlen
  have hb₁ : b < rows₁.length := by simpa only [rows₁, List.length_set] using hb
  have hrowb : rows₁[b] = rows[b] := by
    simp only [rows₁, List.getElem_set, hab, ite_false]
  have hrow₂len := gm06EncodeRows_set_length rows₁ b hb₁ []
  rw [hrowb, List.length_nil, Nat.add_zero] at hrow₂len
  have hN₂ : (gm06EncodeRows (rows₁.set b [])).length < 2 ^ w := by omega
  let R := [31, 7, 8, 9, 11, 320, 317, 319, 313, 323, 324, 98]
  let A := [25, 26, 27, 4, 28]
  let s₀ := s.setReg 31 a
  have he₀ : Exec w (.assign 31 (.reg 22)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h22 haw)
  have hk₀ : Keeps R A s s₀ := (Keeps.refl _ _ s).setReg (by simp [R]) _
  obtain ⟨s₁, t₁, he₁, ht₁, hrowa, _, hsrc₁, hk₁⟩ := gm06SelectRowProg_exec
    4 25 (by decide) rows a ha s₀ (by omega) (by simpa [s₀] using h4) hN hx (by simp [s₀])
  have hk₁' : Keeps R A s s₁ := hk₀.trans hk₁ (by simp [R]) (by simp [A])
  have h4₁ : s₁.arrs 4 = gm06EncodeRows rows := by simpa [s₀] using hsrc₁.trans h4
  let s₂ := s₁.setReg 31 b
  have he₂ : Exec w (.assign 31 (.reg 301)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg ((hk₁'.1 301 (by decide)).trans h301) hbw)
  have hk₂ : Keeps R A s s₂ := hk₁'.setReg (by simp [R]) _
  obtain ⟨s₃, t₃, he₃, ht₃, hrowb', _, hsrc₃, hk₃⟩ := gm06SelectRowProg_exec
    4 26 (by decide) rows b hb s₂ (by omega) (by simpa [s₂] using h4₁) hN hx (by simp [s₂])
  have hk₃' : Keeps R A s s₃ := hk₂.trans hk₃ (by simp [R]) (by simp [A])
  have h4₃ : s₃.arrs 4 = gm06EncodeRows rows := by simpa [s₂] using hsrc₃.trans h4₁
  have h25₃ : s₃.arrs 25 = rows[a] := by
    simpa [s₂] using (hk₃.2 25 (by decide)).trans (show s₂.arrs 25 = rows[a] by simpa [s₂] using hrowa)
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hmerge, _⟩ := gm06SpliceRotationRowsProg_exec
    rows[a] rows[b] d e hnda hndb hd he s₃ hw hxy hax hbx h25₃ hrowb'
    ((hk₃'.1 23 (by decide)).trans h23) ((hk₃'.1 24 (by decide)).trans h24)
  have hk₄' : Keeps R A s s₄ := hk₃'.trans hk₄ (by simp [R]) (by simp [A])
  have h4₄ : s₄.arrs 4 = gm06EncodeRows rows := (hk₄.2 4 (by decide)).trans h4₃
  let s₅ := s₄.setReg 31 a
  have he₅ : Exec w (.assign 31 (.reg 22)) s₄ s₅ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg ((hk₄'.1 22 (by decide)).trans h22) haw)
  have hk₅ : Keeps R A s s₅ := hk₄'.setReg (by simp [R]) _
  obtain ⟨s₆, t₆, he₆, ht₆, hk₆, htable, _⟩ := gm06ReplaceRotationRowProg_exec
    rows a ha merged s₅ (by omega) hN hN₁ hx hmwords
    (by simpa [s₅] using h4₄) (by simpa [s₅] using hmerge) (by simp [s₅])
  have hk₆' : Keeps R A s s₆ := hk₅.trans hk₆ (by simp [R]) (by simp [A])
  let s₇ := s₆.setArr 27 []
  have he₇ : Exec w (.alloc 27 (.const 0)) s₆ s₇ 1 := by
    simpa only [List.replicate_zero, Expr.cost, Nat.add_zero] using Exec.alloc (a := 27) (s := s₆)
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk₇ : Keeps R A s s₇ := hk₆'.setArr (by simp [A]) _
  let s₈ := s₇.setReg 31 b
  have he₈ : Exec w (.assign 31 (.reg 301)) s₇ s₈ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg ((hk₇.1 301 (by decide)).trans h301) hbw)
  have hk₈ : Keeps R A s s₈ := hk₇.setReg (by simp [R]) _
  obtain ⟨s₉, t₉, he₉, ht₉, hk₉, hout, _⟩ := gm06ReplaceRotationRowProg_exec
    rows₁ b hb₁ [] s₈ (by omega) hN₁ hN₂ hwords₁ (by simp)
    (by simpa [s₈, s₇] using htable) (by simp [s₈, s₇]) (by simp [s₈])
  refine ⟨s₉, 2 + (t₁ + (2 + (t₃ + (t₄ + (2 + (t₆ + (1 + (2 + t₉)))))))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ (.seq he₇ (.seq he₈ he₉)))))))),
    ?_, hk₈.trans hk₉ (by simp [R]) (by simp [A]), hout, ?_⟩
  · rw [hrowb, List.length_nil, Nat.add_zero] at ht₉
    omega
  · rw [hout]
    omega

end GraphMinor.Compute
