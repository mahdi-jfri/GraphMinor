module

public import GraphMinor.Compute.GM06Alg34Cells
public import Mathlib.Data.List.FinRange

/-!
# Numbering surviving drawing labels by their supplied lists

Use a label's list index as its new number. For a list without repeated
labels this gives a bijection to its positions, with no selection from
geometric data. Filtering the complete finite vertex and edge lists
therefore gives canonical new labels after vertex deletion.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The position of a known member of a finite supplied label list. -/
def gm06ListIndex {α : Type*} [DecidableEq α] (L : List α) (a : α) (ha : a ∈ L) : Fin L.length :=
  ⟨L.idxOf a, List.idxOf_lt_length_iff.mpr ha⟩

/-- Reading the computed position gives exactly the original supplied label. -/
theorem gm06ListIndex_get {α : Type*} [DecidableEq α] (L : List α) (a : α) (ha : a ∈ L) :
    L.get (gm06ListIndex L a ha) = a := List.idxOf_get (List.idxOf_lt_length_iff.mpr ha)

/-- For a list without repetitions, numbering a label read at a position
returns exactly that position. -/
theorem gm06ListIndex_get_index {α : Type*} [DecidableEq α] (L : List α) (hL : L.Nodup)
    (i : Fin L.length) : gm06ListIndex L (L.get i) (List.get_mem L i) = i := by
  apply hL.get_inj_iff.mp
  exact gm06ListIndex_get L (L.get i) (List.get_mem L i)

/-- List indices give a canonical bijection between supplied labels and new positions. -/
def gm06ListNumbering {α : Type*} [DecidableEq α] (L : List α) (hL : L.Nodup) :
    {a // a ∈ L} ≃ Fin L.length where
  toFun a := gm06ListIndex L a.val a.property
  invFun i := ⟨L.get i, List.get_mem L i⟩
  left_inv a := Subtype.ext (gm06ListIndex_get L a.val a.property)
  right_inv i := gm06ListIndex_get_index L hL i

namespace GM06DrawingData

/-- Surviving original vertex labels, in their original numerical order. -/
def activeVertices (x : GM06DrawingData) (vs : List (Fin x.n)) : List (Fin x.n) :=
  (List.finRange x.n).filter (fun v => decide (v ∈ vs))

/-- Surviving original edge labels, in their original numerical order. -/
def activeEdges (x : GM06DrawingData) (vs : List (Fin x.n)) : List (Fin x.ends.length) :=
  (List.finRange x.ends.length).filter (fun e => x.activeCell vs (.inr (.inl e)))

theorem mem_activeVertices_iff (x : GM06DrawingData) (vs : List (Fin x.n)) (v : Fin x.n) :
    v ∈ x.activeVertices vs ↔ v ∈ vs := by
  simp only [activeVertices, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

theorem mem_activeEdges_iff (x : GM06DrawingData) (vs : List (Fin x.n)) (e : Fin x.ends.length) :
    e ∈ x.activeEdges vs ↔ x.ends[e].1 ∈ vs ∧ x.ends[e].2 ∈ vs := by
  simp only [activeEdges, List.mem_filter, List.mem_finRange, true_and, activeCell, decide_eq_true_eq]

theorem activeVertices_nodup (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.activeVertices vs).Nodup := (List.nodup_finRange _).filter _

theorem activeEdges_nodup (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (x.activeEdges vs).Nodup := (List.nodup_finRange _).filter _

end GM06DrawingData
end GraphMinor.Compute
