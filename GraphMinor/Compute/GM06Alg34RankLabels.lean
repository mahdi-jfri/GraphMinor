module

public import GraphMinor.Compute.GM06Alg34VertexRanks
public import GraphMinor.Compute.GM06Alg34LabelList

/-!
# Prefix counts equal the new finite vertex labels

The active-mask prefix counts surviving entries before an old label.
Filtering the ordered label list assigns exactly this position to that
label. Thus the RAM rank array agrees with the labels used in the
proved induced drawing payload.
-/

public section
namespace GraphMinor.Compute

/-- Filtering a retained label counts the retained entries before its first position. -/
theorem gm06_idxOf_filter_eq_length_take {α : Type*} [DecidableEq α]
    (p : α → Bool) (L : List α) (a : α) (ha : a ∈ L) (hp : p a = true) :
    (L.filter p).idxOf a = ((L.take (L.idxOf a)).filter p).length := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    by_cases heq : b = a
    · subst b
      simp [hp]
    · have haL : a ∈ L := (List.mem_cons.mp ha).resolve_left (Ne.symm heq)
      have hba : (b == a) = false := beq_eq_false_iff_ne.mpr heq
      have hh := ih haL
      cases hpb : p b <;> simp [List.idxOf_cons, hba, hpb, hh]

private theorem alg34_indicator_sum {α : Type*} (L : List α) (p : α → Bool) :
    (L.map (fun a => if p a then (1 : ℕ) else 0)).sum = (L.filter p).length := by
  induction L with
  | nil => rfl
  | cons a L ih => cases hpa : p a <;> simp [hpa, ih, Nat.add_comm]

namespace GM06DrawingData

/-- The active count returned by the RAM pass is the new vertex count. -/
theorem vertexMask_sum_eq_activeVertices_length (x : GM06DrawingData)
    (vs : List (Fin x.n)) :
    (gm06VertexMask vs).sum = (x.activeVertices vs).length := by
  rw [gm06VertexMask, List.ofFn_eq_map]
  simpa only [decide_eq_true_eq, activeVertices] using
    alg34_indicator_sum (List.finRange x.n) (fun a => decide (a ∈ vs))

/-- Each prefix-sum entry at a surviving old label is exactly its new
position in the induced payload's vertex list. -/
theorem vertexRanks_get (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.n) (ha : a ∈ vs) :
    (gm06VertexRanks vs)[a.val]'(by simp [gm06VertexRanks]) =
      (gm06ListIndex (x.activeVertices vs) a ((x.mem_activeVertices_iff vs a).mpr ha)).val := by
  simp only [gm06VertexRanks, List.getElem_ofFn, gm06ListIndex]
  rw [gm06VertexMask, List.ofFn_eq_map, ← List.map_take]
  have hs := alg34_indicator_sum ((List.finRange x.n).take a.val)
    (fun a => decide (a ∈ vs))
  simp only [decide_eq_true_eq] at hs
  rw [hs]
  have hh := gm06_idxOf_filter_eq_length_take (fun a => decide (a ∈ vs)) (List.finRange x.n) a
    (List.mem_finRange a) (by simp [ha])
  simpa [activeVertices] using hh.symm

end GM06DrawingData
end GraphMinor.Compute
