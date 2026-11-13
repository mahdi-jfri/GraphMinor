module

public import GraphMinor.GM06.Alg57CurrentBoundaryRows
public import GraphMinor.GM06.Alg57FilteredRowCycles

/-!
# The local boundary comparison rotation

For Lemma 10 in the proof of VI (5.7), page 133, filtering a linkage
row to its path and cuff ends leaves the boundary rotation. At a
cuff, the prescribed consecutive pair fixes its three-end cycle.
At an interior vertex the two ends are interchanged. Thus each
retained block's last end is preceded by its first boundary end.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- All boundary comparison ends are actual members of a valid
local cut row. -/
theorem cutBoundaryEnds_subset {p : GM06CutPosition} {row : List ℕ} (h : CutBlockOK p row) :
    ∀ d ∈ cutBoundaryEnds p, d ∈ row := by
  cases p with
  | interior a b =>
    obtain ⟨ha, hb, _⟩ := (cutBlockOK_interior_iff _ _ _).mp h
    intro d hd
    simp only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false] at hd
    exact hd.elim (fun e => e.symm ▸ ha) (fun e => e.symm ▸ hb)
  | start b cp cn =>
    obtain ⟨hb, hcp, hcn, _⟩ := (cutBlockOK_start_iff _ _ _ _).mp h
    intro d hd
    simp only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false] at hd
    exact hd.elim (fun e => e.symm ▸ hb) (fun hh => hh.elim (fun e => e.symm ▸ hcp) (fun e => e.symm ▸ hcn))
  | terminal a cp cn =>
    obtain ⟨ha, hcp, hcn, _⟩ := (cutBlockOK_terminal_iff _ _ _ _).mp h
    intro d hd
    simp only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false] at hd
    exact hd.elim (fun e => e.symm ▸ ha) (fun hh => hh.elim (fun e => e.symm ▸ hcp) (fun e => e.symm ▸ hcn))

private theorem formPerm_eq_of_idx_next {row : List ℕ} (hn : row.Nodup)
    {a b : ℕ} (ha : a ∈ row) (_hb : b ∈ row)
    (hnext : row.idxOf b = (row.idxOf a + 1) % row.length) : row.formPerm a = b := by
  have hi := List.idxOf_lt_length_of_mem ha
  have hh := List.formPerm_apply_getElem row hn (row.idxOf a) hi
  simpa only [List.getElem_idxOf, ← hnext] using hh

/-- The complete successor table of the boundary comparison at
an interior, starting, or terminal linkage vertex. -/
theorem boundaryRow_rotation {p : GM06CutPosition} {row : List ℕ}
    (hn : row.Nodup) (h : CutBlockOK p row) :
    let xs := row.filter (fun d => decide (d ∈ cutBoundaryEnds p))
    match p with
    | .interior a b => xs.formPerm a = b ∧ xs.formPerm b = a
    | .start b cp cn => xs.formPerm b = cp ∧ xs.formPerm cp = cn ∧ xs.formPerm cn = b
    | .terminal a cp cn => xs.formPerm a = cn ∧ xs.formPerm cn = cp ∧ xs.formPerm cp = a := by
  classical
  let keep := fun d => decide (d ∈ cutBoundaryEnds p)
  have hmem (d : ℕ) : d ∈ row.filter keep ↔ d ∈ cutBoundaryEnds p := by
    simp only [List.mem_filter, keep, decide_eq_true_eq]
    exact and_iff_right_of_imp (cutBoundaryEnds_subset h d)
  have hnf := hn.filter keep
  cases p with
  | interior a b =>
    obtain ⟨ha, hb, hab⟩ := (cutBlockOK_interior_iff _ _ _).mp h
    have hma : a ∈ row.filter keep := (hmem a).mpr (by simp [cutBoundaryEnds])
    have hmb : b ∈ row.filter keep := (hmem b).mpr (by simp [cutBoundaryEnds])
    exact formPerm_of_two_ends _ hnf hab hma hmb (fun d hd => by
      simpa only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false] using (hmem d).mp hd)
  | start b cp cn =>
    obtain ⟨hb, hcp, hcn, hbp, hbn, hpn, hnext⟩ := (cutBlockOK_start_iff _ _ _ _).mp h
    have hcpn := formPerm_eq_of_idx_next hn hcp hcn hnext
    have hk (d : ℕ) (hd : d ∈ cutBoundaryEnds (.start b cp cn)) : keep d = true := decide_eq_true hd
    have hfpn := formPerm_filter_apply_of_keep_next row hn keep hcp (hk cp (by simp [cutBoundaryEnds]))
      (by rw [hcpn]; exact hk cn (by simp [cutBoundaryEnds]))
    have hthree := formPerm_of_three_ends (row.filter keep) hnf hbp hbn hpn
      ((hmem b).mpr (by simp [cutBoundaryEnds])) ((hmem cp).mpr (by simp [cutBoundaryEnds]))
      ((hmem cn).mpr (by simp [cutBoundaryEnds]))
      (fun d hd => by simpa only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false]
        using (hmem d).mp hd) (hfpn.trans hcpn)
    exact ⟨hthree.1, hfpn.trans hcpn, hthree.2⟩
  | terminal a cp cn =>
    obtain ⟨ha, hcp, hcn, hap, han, hpn, hnext⟩ := (cutBlockOK_terminal_iff _ _ _ _).mp h
    have hcnp := formPerm_eq_of_idx_next hn hcn hcp hnext
    have hk (d : ℕ) (hd : d ∈ cutBoundaryEnds (.terminal a cp cn)) : keep d = true := decide_eq_true hd
    have hfnp := formPerm_filter_apply_of_keep_next row hn keep hcn (hk cn (by simp [cutBoundaryEnds]))
      (by rw [hcnp]; exact hk cp (by simp [cutBoundaryEnds]))
    have hthree := formPerm_of_three_ends (row.filter keep) hnf han hap hpn.symm
      ((hmem a).mpr (by simp [cutBoundaryEnds])) ((hmem cn).mpr (by simp [cutBoundaryEnds]))
      ((hmem cp).mpr (by simp [cutBoundaryEnds]))
      (fun d hd => by
        have hh := (hmem d).mp hd
        simp only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false] at hh
        exact hh.elim Or.inl (fun hc => Or.inr hc.symm)) (hfnp.trans hcnp)
    exact ⟨hthree.1, hfnp.trans hcnp, hthree.2⟩

/-- In the comparison rotation, each cut block's last end is
preceded by the first end of that block. -/
theorem boundaryRow_prev_last {p : GM06CutPosition} {row : List ℕ}
    (hn : row.Nodup) (h : CutBlockOK p row) (left : Bool) :
    (row.filter (fun d => decide (d ∈ cutBoundaryEnds p))).formPerm.symm (cutLast p left) =
      cutFirst p left := by
  have hh := boundaryRow_rotation hn h
  cases p <;> cases left <;> simp only [cutFirst_eq, cutLast_eq] <;>
    rw [Equiv.symm_apply_eq] <;> first
    | exact hh.1.symm
    | exact hh.2.symm
    | exact hh.2.1.symm
    | exact hh.2.2.symm

end GraphMinor.GM06
