module

public import GraphMinor.Compute.GM06Alg34MarkCellFacts

/-!
# Reading a matrix after several closure rows

Rows are supplied as a row number and a list of column numbers. Folding
the marking operation over these lists marks an entry exactly when one
of the supplied row lists contains its address. The statement permits
repeated labels and rows, as can occur in boundary descriptions.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Mark the columns supplied for a numbered row. -/
def gm06MatrixMarkRow (N : ℕ) (dst : List ℕ) (r : ℕ × List ℕ) : List ℕ :=
  gm06MarkCells (N * r.1) 0 r.2 dst

/-- Row marking preserves the allocated matrix size. -/
theorem gm06MatrixMarkRows_length (N : ℕ) (rows : List (ℕ × List ℕ))
    (dst : List ℕ) :
    (rows.foldl (gm06MatrixMarkRow N) dst).length = dst.length := by
  induction rows generalizing dst with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.foldl_cons, ih, gm06MatrixMarkRow, gm06MarkCells_length]

/-- The folded row writer sets an entry exactly when a supplied row
addresses it, and otherwise keeps the original entry. -/
theorem gm06MatrixMarkRows_getElem (N : ℕ) (rows : List (ℕ × List ℕ))
    (dst : List ℕ) (j : ℕ) (hj : j < dst.length) :
    (rows.foldl (gm06MatrixMarkRow N) dst)[j]'(by
      rw [gm06MatrixMarkRows_length]; exact hj) =
      if rows.any (fun r => r.2.any (fun v => decide (N * r.1 + v = j)))
      then 1 else dst[j] := by
  induction rows generalizing dst with
  | nil => simp
  | cons r rows ih =>
    have hb : j < (gm06MatrixMarkRow N dst r).length := by
      simpa only [gm06MatrixMarkRow, gm06MarkCells_length] using hj
    simp only [List.foldl_cons]
    rw [ih _ hb]
    have hh := gm06MarkCells_getElem (N * r.1) 0 r.2 dst j hj
    simp only [Nat.add_zero] at hh
    unfold gm06MatrixMarkRow at hb ⊢
    change (if rows.any _ then 1 else (gm06MarkCells (N * r.1) 0 r.2 dst)[j]) = _
    rw [hh]
    cases ha : rows.any (fun s => s.2.any (fun v => decide (N * s.1 + v = j))) <;>
      cases hr : r.2.any (fun v => decide (N * r.1 + v = j)) <;>
      simp [List.any_cons, ha, hr]

/-- Bounded matrix columns make row-major addresses unique. -/
theorem gm06MatrixAddress_eq_iff {N r i c j : ℕ} (hc : c < N) (hj : j < N) :
    N * r + c = N * i + j ↔ r = i ∧ c = j := by
  constructor
  · intro he
    have hN : 0 < N := Nat.zero_lt_of_lt hc
    have hr := congrArg (fun a => a / N) he
    simp only [Nat.mul_add_div hN, Nat.div_eq_of_lt hc, Nat.div_eq_of_lt hj,
      Nat.add_zero] at hr
    have hcol := congrArg (fun a => a % N) he
    simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hj] at hcol
    exact ⟨hr, hcol⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- From a zero allocation, the supplied rows give an exact Boolean
incidence matrix, with duplicate boundary labels allowed. -/
theorem gm06MatrixMarkRows_replicate_getElem (N : ℕ) (rows : List (ℕ × List ℕ))
    (r c : ℕ) (hr : r < N) (hc : c < N)
    (hcols : ∀ p ∈ rows, ∀ v ∈ p.2, v < N) :
    (rows.foldl (gm06MatrixMarkRow N) (List.replicate (N * N) 0))[N * r + c]'(by
      rw [gm06MatrixMarkRows_length, List.length_replicate]
      exact (Nat.add_lt_add_left hc _).trans_le (by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left N hr)) =
      if ∃ p ∈ rows, p.1 = r ∧ c ∈ p.2 then 1 else 0 := by
  have haddr : N * r + c < (List.replicate (N * N) 0).length := by
    rw [List.length_replicate]
    exact (Nat.add_lt_add_left hc _).trans_le (by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left N hr)
  rw [gm06MatrixMarkRows_getElem N rows _ _ haddr, List.getElem_replicate]
  have he : (rows.any (fun p => p.2.any (fun v => decide (N * p.1 + v = N * r + c)))) =
      decide (∃ p ∈ rows, p.1 = r ∧ c ∈ p.2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨p, hp, v, hv, he⟩
      obtain ⟨he₁, he₂⟩ := (gm06MatrixAddress_eq_iff (hcols p hp v hv) hc).mp he
      exact ⟨p, hp, he₁, he₂ ▸ hv⟩
    · rintro ⟨p, hp, he, hv⟩
      exact ⟨p, hp, c, hv, by rw [he]⟩
  rw [he]
  simp only [decide_eq_true_eq]

end GraphMinor.Compute
