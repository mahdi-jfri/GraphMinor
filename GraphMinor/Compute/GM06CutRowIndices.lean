module

public import GraphMinor.Compute.GM06CutRowPositions
public import GraphMinor.Compute.GM06FindLabel

/-!
# Preparing the interval positions of a copied row

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) compares ends
by their positions in an original rotation. The preparation pass
builds the position table for all outgoing ends and finds the two
left-interval bounds. A label absent from the row gets the row-length
sentinel, so empty rows and isolated permanent slots are supported.
The inputs contain the row and the two bound labels, not their indices.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- In a repetition-free row, a complete label search returns idxOf,
with the length sentinel when the label is absent. -/
theorem gm06FindLabelProg_exec_idxOf {w : ℕ} (a needle idx res : ℕ)
    (hir : idx ≠ res) (hni : needle ≠ idx) (hnr : needle ≠ res)
    (xs : List ℕ) (v : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hv : v < 2 ^ w)
    (hnd : xs.Nodup) (ha : s.arrs a = xs) (hr : s.regs needle = v) :
    ∃ sf t, Exec w (gm06FindLabelProg a needle idx res) s sf t ∧
      t ≤ 7 + 13 * xs.length ∧ Keeps [idx, res] [] s sf ∧ sf.regs res = xs.idxOf v := by
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm06FindLabelProg_exec
    a needle idx res hir hni hnr xs v s hw hn hx hv ha hr
  refine ⟨sf, t, he, ht, hk, ?_⟩
  rcases hd with hnone | hsome
  · have hnot : v ∉ xs := by
      intro hmem
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
      exact hnone.2 i hi heq
    simpa only [List.idxOf_eq_length hnot] using hnone.1
  · obtain ⟨i, hi, hres, heq⟩ := hsome
    have hv' : v ∈ xs := List.mem_iff_getElem.mpr ⟨i, hi, heq⟩
    have hiv := List.idxOf_lt_length_of_mem hv'
    have hie : i = xs.idxOf v :=
      hnd.getElem_inj_iff.mp (heq.trans (List.getElem_idxOf hiv).symm)
    exact hres.trans hie

/-- Build end positions in 614 and find the two interval-bound
labels from registers 673/674, returning their indices in 676/677. -/
def gm06CutRowIndicesProg : Cmd :=
  .seq gm06RowPositionsProg
    (.seq (gm06FindLabelProg 611 673 675 676) (gm06FindLabelProg 611 674 675 677))

/-- The complete index preparation has exact output and linear cost
in the row and permanent dart space. It works for empty rows. -/
theorem gm06CutRowIndicesProg_exec {w n : ℕ} (row : List ℕ) (first last : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hl : row.length < 2 ^ w)
    (hfirst : first < 2 ^ w) (hlast : last < 2 ^ w)
    (hnd : row.Nodup) (hkeys : ∀ d ∈ row, d < n)
    (h611 : s.arrs 611 = row) (h647 : s.regs 647 = n)
    (h673 : s.regs 673 = first) (h674 : s.regs 674 = last) :
    ∃ sf t, Exec w gm06CutRowIndicesProg s sf t ∧
      t ≤ 25 + 13 * n + 37 * row.length ∧
      Keeps [650, 675, 676, 677] [614] s sf ∧
      sf.arrs 614 = gm06RowPositions n row ∧
      sf.regs 676 = row.idxOf first ∧ sf.regs 677 = row.idxOf last := by
  have hrowWords : ∀ d ∈ row, d < 2 ^ w := fun d hd => (hkeys d hd).trans hn
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06RowPositionsProg_exec
    row s hw hn hl hkeys h611 h647
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06FindLabelProg_exec_idxOf
    611 673 675 676 (by decide) (by decide) (by decide) row first s₁ hw hl hrowWords hfirst hnd
    ((hk₁.2 611 (by decide)).trans h611) ((hk₁.1 673 (by decide)).trans h673)
  have hk₁₂ : Keeps [650, 675, 676, 677] [614] s s₂ :=
    (hk₁.mono (by simp) (fun _ h => h)).trans hk₂ (by simp) (by simp)
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06FindLabelProg_exec_idxOf
    611 674 675 677 (by decide) (by decide) (by decide) row last s₂ hw hl hrowWords hlast hnd
    ((hk₁₂.2 611 (by decide)).trans h611) ((hk₁₂.1 674 (by decide)).trans h674)
  refine ⟨sf, t₁ + (t₂ + tf), .seq he₁ (.seq he₂ hef), by omega,
    hk₁₂.trans hkf (by simp) (by simp), ?_, (hkf.1 676 (by decide)).trans hd₂, hdf⟩
  exact (hkf.2 614 (by simp)).trans ((hk₂.2 614 (by simp)).trans hd₁)

end GraphMinor.Compute
