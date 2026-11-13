module

public import GraphMinor.Compute.GM06ListEncoding

/-!
# Positions of the cylinder input rows

A row begins after the codes of the preceding rows. The length prefix
at that position is the row's actual length. The formulas below connect
a RAM cursor advanced by counted row skips to the supplied row index.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Row payloads concatenate without adding an extra row count. -/
theorem gm06EncodeRowsPayload_append (xs ys : List (List ℕ)) :
    gm06EncodeRowsPayload (xs ++ ys) = gm06EncodeRowsPayload xs ++ gm06EncodeRowsPayload ys := by
  simp [gm06EncodeRowsPayload]

/-- Adding one row adds its prefix and its entries to the consumed length. -/
theorem gm06RowsPrefixLength_succ (rows : List (List ℕ)) {i : ℕ} (hi : i < rows.length) :
    (gm06EncodeRowsPayload (rows.take (i + 1))).length =
      (gm06EncodeRowsPayload (rows.take i)).length + 1 + rows[i].length := by
  rw [List.take_succ_eq_append_getElem hi, gm06EncodeRowsPayload_append]
  simp [gm06EncodeRowsPayload, gm06EncodeNatList]
  omega

/-- Reading after the preceding rows gives the next row's length prefix. -/
theorem gm06RowHeader_at_split (pre : List (List ℕ)) (row : List ℕ)
    (post : List (List ℕ)) :
    (gm06EncodeRows (pre ++ row :: post))[1 + (gm06EncodeRowsPayload pre).length]? =
      some row.length := by
  simp only [gm06EncodeRows, gm06EncodeRowsPayload, List.flatMap_append,
    List.flatMap_cons, gm06EncodeNatList, List.cons_append]
  rw [Nat.add_comm 1, List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- The row at any valid index has its length at the cursor after the preceding row codes. -/
theorem gm06RowHeader_get (rows : List (List ℕ)) {i : ℕ} (hi : i < rows.length) :
    (gm06EncodeRows rows)[1 + (gm06EncodeRowsPayload (rows.take i)).length]? =
      some rows[i].length := by
  have hs : rows.take i ++ rows[i] :: rows.drop (i + 1) = rows := by
    rw [← List.drop_eq_getElem_cons hi]
    exact List.take_append_drop i rows
  have hh := gm06RowHeader_at_split (rows.take i) rows[i] (rows.drop (i + 1))
  rw [hs] at hh
  exact hh

/-- Every prefix payload is no longer than the complete payload. -/
theorem gm06RowsPrefixLength_le (rows : List (List ℕ)) (i : ℕ) :
    (gm06EncodeRowsPayload (rows.take i)).length ≤ (gm06EncodeRowsPayload rows).length := by
  have hh := congrArg (fun rs => (gm06EncodeRowsPayload rs).length) (List.take_append_drop i rows)
  rw [gm06EncodeRowsPayload_append, List.length_append] at hh
  omega

end GraphMinor.Compute
