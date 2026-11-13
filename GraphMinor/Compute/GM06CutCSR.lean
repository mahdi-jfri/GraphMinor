module

public import GraphMinor.Compute.GM06CutAdjacencyRows
public import GraphMinor.Compute.GM06CutAdjacencyMath

/-!
# Interpreting the computed cut adjacency buffers

The row loop for Section 9 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) returns start offsets, end offsets and concatenated neighbour
rows. This file proves that these lists are a CSR representation, including
when the entries buffer has unused trailing space. It then identifies
the represented graph with the graph of the computed cut rotations.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The start of row i follows precisely the earlier rows. -/
theorem gm06CSRStarts_getElem (rows : List (List ℕ)) (cursor i : ℕ) (hi : i < rows.length) :
    (gm06CSRStarts cursor rows)[i]'(by rw [gm06CSRStarts_length]; exact hi) =
      cursor + (rows.take i).flatten.length := by
  induction rows generalizing cursor i with
  | nil => simp at hi
  | cons row rows ih =>
    cases i with
    | zero => simp [gm06CSRStarts]
    | succ i =>
      simpa only [gm06CSRStarts, List.getElem_cons_succ, List.take_succ_cons,
        List.flatten_cons, List.length_append, Nat.add_assoc] using ih (cursor + row.length) i (by simpa using hi)

/-- The end of row i is its start plus its length. -/
theorem gm06CSREnds_getElem (rows : List (List ℕ)) (cursor i : ℕ) (hi : i < rows.length) :
    (gm06CSREnds cursor rows)[i]'(by rw [gm06CSREnds_length]; exact hi) =
      cursor + (rows.take i).flatten.length + rows[i].length := by
  induction rows generalizing cursor i with
  | nil => simp at hi
  | cons row rows ih =>
    cases i with
    | zero => simp [gm06CSREnds]
    | succ i =>
      simpa only [gm06CSREnds, List.getElem_cons_succ, List.take_succ_cons,
        List.flatten_cons, List.length_append, Nat.add_assoc] using ih (cursor + row.length) i (by simpa using hi)

/-- Concatenated rows split at each indexed row. -/
theorem gm06Flatten_split (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length) :
    rows.flatten = (rows.take i).flatten ++ (rows[i] ++ (rows.drop (i + 1)).flatten) := by
  conv_lhs => rw [← List.take_append_drop i rows, List.drop_eq_getElem_cons hi]
  simp only [List.flatten_append, List.flatten_cons]

/-- Exact CSR layout, allowing any padding after the entries prefix. -/
theorem gm06CSR_isListFamily {n : ℕ} (rows : List (List ℕ)) (padding : List ℕ) (s : State)
    (hlen : rows.length = n)
    (hs : s.arrs 620 = gm06CSRStarts 0 rows) (he : s.arrs 621 = gm06CSREnds 0 rows)
    (ha : s.arrs 622 = rows.flatten ++ padding) :
    IsListFamily n 620 621 622 (fun u => rows[u.val]'(by rw [hlen]; exact u.isLt)) s := by
  refine ⟨by simp only [hs, gm06CSRStarts_length, hlen],
    by simp only [he, gm06CSREnds_length, hlen], ?_⟩
  intro u
  have hu : u.val < rows.length := hlen ▸ u.isLt
  let st := (rows.take u.val).flatten.length
  let en := st + rows[u.val].length
  have hsplit := gm06Flatten_split rows u.val hu
  have hentries : s.arrs 622 = (rows.take u.val).flatten ++
      (rows[u.val] ++ ((rows.drop (u.val + 1)).flatten ++ padding)) := by
    rw [ha, hsplit, List.append_assoc, List.append_assoc]
  have hcap : en ≤ (s.arrs 622).length := by
    simp only [hentries, List.length_append]
    dsimp only [en, st]
    omega
  refine ⟨st, en, by simp only [hs, gm06CSRStarts_length]; exact hu,
    by simp only [he, gm06CSREnds_length]; exact hu, hcap, by dsimp [en]; omega,
    ?_, ?_, by dsimp [en]; omega, ?_⟩
  · simpa only [hs, st, Nat.zero_add] using gm06CSRStarts_getElem rows 0 u.val hu
  · simpa only [he, en, st, Nat.zero_add] using gm06CSREnds_getElem rows 0 u.val hu
  · intro k hk
    change k < rows[u.val].length at hk
    dsimp only [st]
    rw [List.getElem_of_eq hentries, List.getElem_append_right (by omega),
      List.getElem_append_left (by omega)]
    simp only [Nat.add_sub_cancel_left]

/-- Each copied rotation produces the corresponding finite neighbour row. -/
theorem gm06CutAdjacencyRowsFrom_getElem (n base : ℕ) (origins active live : List ℕ)
    (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length) :
    (gm06CutAdjacencyRowsFrom n base origins active live rows)[i]'
        (by rw [gm06CutAdjacencyRowsFrom_length]; exact hi) =
      gm06CutRowNeighbours n origins active live (base + i) rows[i] := by
  simp only [gm06CutAdjacencyRowsFrom, List.getElem_map, List.getElem_zipIdx]

/-- The computed row list equals the stable cut-graph adjacency family. -/
theorem gm06CutAdjacencyRowsFrom_eq_ofFn {n : ℕ} (data : GM06CutData) (hlen : data.rotations.length = n) :
    gm06CutAdjacencyRowsFrom n 0 data.origins data.activeDarts data.vertices data.rotations =
      List.ofFn (gm06CutAdjacencyLists n data) := by
  apply List.ext_getElem
  · simp only [gm06CutAdjacencyRowsFrom_length, List.length_ofFn, hlen]
  · intro i hi hi'
    have hir : i < data.rotations.length := by simpa only [gm06CutAdjacencyRowsFrom_length] using hi
    simp only [gm06CutAdjacencyRowsFrom_getElem _ _ _ _ _ _ _ hir, Nat.zero_add, List.getElem_ofFn,
      gm06CutAdjacencyLists, gm06CutRowNeighbours, List.getElem?_eq_getElem hir, Option.getD_some]

/-- The full computed CSR row layout represents exactly the cut graph.
The row-origin condition is discharged by the cut-data construction. -/
theorem gm06CutCSR_isAdjList {n : ℕ} (data : GM06CutData) (padding : List ℕ) (s : State)
    (hlen : data.rotations.length = n)
    (hproper : ∀ d ∈ data.activeDarts, ∀ u : Fin n,
      data.origins[d]?.getD 0 = u.val ↔ d ∈ data.rotations[u.val]?.getD [])
    (hs : s.arrs 620 = gm06CSRStarts 0
      (gm06CutAdjacencyRowsFrom n 0 data.origins data.activeDarts data.vertices data.rotations))
    (he : s.arrs 621 = gm06CSREnds 0
      (gm06CutAdjacencyRowsFrom n 0 data.origins data.activeDarts data.vertices data.rotations))
    (ha : s.arrs 622 =
      (gm06CutAdjacencyRowsFrom n 0 data.origins data.activeDarts data.vertices data.rotations).flatten ++ padding) :
    IsAdjList (gm06CutGraph n data) 620 621 622 (gm06CutAdjacencyLists n data) s := by
  have hrows := gm06CutAdjacencyRowsFrom_eq_ofFn data hlen
  rw [hrows] at hs he ha
  refine ⟨?_, gm06CutAdjacencyLists_spec data hproper⟩
  have hf := gm06CSR_isListFamily (n := n) (List.ofFn (gm06CutAdjacencyLists n data)) padding s (by simp) hs he ha
  simpa only [List.getElem_ofFn] using hf

/-- The complete cut-data pass keeps its rotation buffer at the
allocated size and preserves word bounds for every stored field. -/
theorem gm06CutDataProg_output_bounds {w : ℕ} (rows : List (List ℕ)) (s sf : State) (t : ℕ)
    (hw : 2 < 2 ^ w) (h600 : s.arrs 600 = gm06EncodeRows rows)
    (hfit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (he : Exec w gm06CutDataProg s sf t) :
    (sf.arrs 625).length = 1 + 2 * (gm06EncodeRows rows).length ∧
      ∀ x ∈ sf.arrs 625, x < 2 ^ w := by
  change Exec w (.seq gm06CutMarkProg (.seq gm06CutVertexProg
    (.seq (.assign 647 (gm06CutSizeExpr 2)) (.seq gm06CutRowsProg _)))) s sf t at he
  cases he with
  | seq hm hvrest =>
    cases hvrest with
    | seq hv harest =>
      cases harest with
      | seq ha hrrest =>
        cases hrrest with
        | seq hr hs =>
          have hsource := (ha.arrs_eq_of_not_mem_writtenArrs (a := 600) (by decide)).trans
            ((hv.arrs_eq_of_not_mem_writtenArrs (a := 600) (by decide)).trans
              ((hm.arrs_eq_of_not_mem_writtenArrs (a := 600) (by decide)).trans h600))
          obtain ⟨hlen, hwords⟩ := gm06CutRowsProg_output_bounds rows _ _ _ hw hsource hfit hr
          exact ⟨(gm06Exec_length_eq hs 625 (by decide)).trans hlen, hs.arrs_lt 625 hwords⟩

/-- An initially valid register remains a word throughout execution. -/
theorem gm06Exec_reg_lt {w : ℕ} {c : Cmd} {s sf : State} {t : ℕ}
    (he : Exec w c s sf t) (r : ℕ) (hr : s.regs r < 2 ^ w) : sf.regs r < 2 ^ w := by
  induction he with
  | skip => exact hr
  | @assign r' e s v hv =>
    by_cases hrr : r = r'
    · subst r
      simpa only [State.setReg_regs_self] using Expr.eval_lt hv
    · simpa only [State.setReg_regs_ne _ _ hrr] using hr
  | write => exact hr
  | alloc => exact hr
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hr)
  | ite_true _ _ _ ih => exact ih hr
  | ite_false _ _ ih => exact ih hr
  | while_false => exact hr
  | while_true _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hr)

/-- The initialized row pass sets its cursor to one before appending,
so its final cursor is a word for any initial cursor value. -/
theorem gm06CutRowsProg_cursor_lt {w : ℕ} (rows : List (List ℕ)) (s sf : State) (t : ℕ)
    (hw : 2 < 2 ^ w) (h600 : s.arrs 600 = gm06EncodeRows rows)
    (hfit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (he : Exec w gm06CutRowsProg s sf t) : sf.regs 655 < 2 ^ w := by
  change Exec w (.seq gm06CutInitRowsProg gm06CutSplitRowsLoop) s sf t at he
  cases he with
  | @seq _ _ _ sm _ _ _ hi hl =>
    obtain ⟨si, _, hei, _, _, hbuf, _, _, _⟩ := gm06CutInitRowsProg_exec rows s hw hfit h600
    have hsame := (hei.deterministic hi).1
    subst si
    have hcursor : sm.regs 655 = 1 := by simpa only [List.length_singleton] using hbuf.2
    exact gm06Exec_reg_lt hl 655 (by rw [hcursor]; omega)

/-- The full cut-data pipeline retains the row pass's valid cursor. -/
theorem gm06CutDataProg_cursor_lt {w : ℕ} (rows : List (List ℕ)) (s sf : State) (t : ℕ)
    (hw : 2 < 2 ^ w) (h600 : s.arrs 600 = gm06EncodeRows rows)
    (hfit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (he : Exec w gm06CutDataProg s sf t) : sf.regs 655 < 2 ^ w := by
  change Exec w (.seq gm06CutMarkProg (.seq gm06CutVertexProg
    (.seq (.assign 647 (gm06CutSizeExpr 2)) (.seq gm06CutRowsProg _)))) s sf t at he
  cases he with
  | seq hm hvrest =>
    cases hvrest with
    | seq hv harest =>
      cases harest with
      | seq ha hrrest =>
        cases hrrest with
        | seq hr hs =>
          have hsource := (ha.arrs_eq_of_not_mem_writtenArrs (a := 600) (by decide)).trans
            ((hv.arrs_eq_of_not_mem_writtenArrs (a := 600) (by decide)).trans
              ((hm.arrs_eq_of_not_mem_writtenArrs (a := 600) (by decide)).trans h600))
          exact gm06Exec_reg_lt hs 655 (gm06CutRowsProg_cursor_lt rows _ _ _ hw hsource hfit hr)

end GraphMinor.Compute
