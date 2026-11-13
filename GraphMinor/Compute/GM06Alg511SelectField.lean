module

public import GraphMinor.Compute.GM06SelectRow
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Selecting the input fields of VI (5.11)

The signed target is nested inside length-prefixed drawing rows.
Select a fixed row while preserving every other array. The bounds
below also transfer the word and length bounds of an encoded input
to any of its supplied rows. They concern only finite serialization.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Every supplied row word also occurs in its complete finite code. -/
theorem gm06Alg511_mem_encoded_row {rows : List (List ℕ)} {row : List ℕ} {v : ℕ}
    (hrow : row ∈ rows) (hv : v ∈ row) : v ∈ gm06EncodeRows rows := by
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨row, hrow, List.mem_cons_of_mem _ hv⟩

/-- Every supplied row is no longer than its complete finite code. -/
theorem gm06Alg511_encoded_row_length_le {rows : List (List ℕ)} {row : List ℕ}
    (hrow : row ∈ rows) : row.length ≤ (gm06EncodeRows rows).length := by
  have hp : row.length ≤ (gm06EncodeRowsPayload rows).length := by
    induction rows with
    | nil => simp at hrow
    | cons r rs ih =>
      have he : (gm06EncodeRowsPayload (r :: rs)).length =
          1 + r.length + (gm06EncodeRowsPayload rs).length := by
        simp [gm06EncodeRowsPayload, gm06EncodeNatList]
        omega
      rw [he]
      rcases List.mem_cons.mp hrow with rfl | h
      · omega
      · have hh := ih h
        omega
  simp only [gm06EncodeRows, List.length_cons]
  omega

/-- Select a fixed supplied field into a work array. -/
def gm06Alg511SelectFieldProg (src dst row : ℕ) : Cmd :=
  .seq (.assign 31 (.const row)) (gm06SelectRowProg src dst)

/-- The field selector reads the exact supplied row and preserves
all arrays except its destination, with a linear bound. -/
theorem gm06Alg511SelectFieldProg_exec {w : ℕ} (src dst : ℕ) (hne : src ≠ dst)
    (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs src = gm06EncodeRows rows)
    (hn : (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeRows rows, v < 2 ^ w) :
    ∃ s' t, Exec w (gm06Alg511SelectFieldProg src dst i) s s' t ∧
      t ≤ 18 + 17 * i + 22 * rows[i].length ∧ s'.arrs dst = rows[i] ∧
      ∀ a ≠ dst, s'.arrs a = s.arrs a := by
  have hcount : rows.length < 2 ^ w := hwords _ (by simp [gm06EncodeRows])
  let s₁ := s.setReg 31 i
  obtain ⟨s', t, he, ht, hrow, _, _, hkeep⟩ := gm06SelectRowProg_exec src dst hne
    rows i hi s₁ hw (by simpa only [s₁, State.setReg_arrs] using ha)
    hn hwords (by simp [s₁])
  refine ⟨s', 2 + t, .seq (.assign (GraphMinor.Compute.Crossing.eval_const (hi.trans hcount))) he,
    by omega, hrow, ?_⟩
  intro a hadst
  simpa only [s₁, State.setReg_arrs] using hkeep.2 a (by simpa using hadst)

end GraphMinor.Compute
