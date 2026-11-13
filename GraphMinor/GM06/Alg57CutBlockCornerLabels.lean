module

public import GraphMinor.GM06.Alg57BoundaryRowRotation
public import GraphMinor.GM06.Alg57OpenBlockLabels

/-!
# Corner labels at each copy of a linkage vertex

In VI (5.7), page 133, a cut block lies between two consecutive
boundary ends of the linkage and cuffs. Its strict interior ends
are deleted in the boundary comparison. Their adjacent labels
agree, so every corner in the block except its last end has the
label of its first end.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- The boundary ends retained in one cut block are exactly its
two endpoints. -/
theorem cutKeep_boundaryEnd_iff {p : GM06CutPosition} {row : List ℕ}
    (h : CutBlockOK p row) (left : Bool) {d : ℕ} (hd : d ∈ cutBoundaryEnds p) :
    cutKeep p row left d = true ↔ d = cutFirst p left ∨ d = cutLast p left := by
  cases p with
  | interior a b =>
    obtain ⟨_, _, hab⟩ := (cutBlockOK_interior_iff _ _ _).mp h
    simp only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> cases left <;>
      simp [cutKeep, GM06CutPosition.pathEnds, cutFirst_eq, cutLast_eq]
  | start b cp cn =>
    obtain ⟨_, _, _, hbp, hbn, hpn, _⟩ := (cutBlockOK_start_iff _ _ _ _).mp h
    simp only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> cases left <;>
      simp [cutKeep, GM06CutPosition.pathEnds, gm06CutDartLeft,
        cutFirst_eq, cutLast_eq, hbp, hbn, hpn, Ne.symm hbp, Ne.symm hbn, Ne.symm hpn]
  | terminal a cp cn =>
    obtain ⟨_, _, _, hap, han, hpn, _⟩ := (cutBlockOK_terminal_iff _ _ _ _).mp h
    simp only [cutBoundaryEnds, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> cases left <;>
      simp [cutKeep, GM06CutPosition.pathEnds, gm06CutDartLeft,
        cutFirst_eq, cutLast_eq, hap, han, hpn, Ne.symm hap, Ne.symm han, Ne.symm hpn]

/-- Deleting nonboundary ends makes the corner label constant in
each cut block up to, but excluding, its last end. -/
theorem cutBlock_corner_label {β : Type*} {p : GM06CutPosition} {row : List ℕ}
    (hn : row.Nodup) (hok : CutBlockOK p row) (g : ℕ → β)
    (hskip : ∀ d ∈ row, d ∉ cutBoundaryEnds p → g (row.formPerm.symm d) = g d)
    (left : Bool) {d : ℕ} (hd : d ∈ row) (hkeep : cutKeep p row left d = true)
    (hlast : d ≠ cutLast p left) : g d = g (cutFirst p left) := by
  obtain ⟨hf, hl, hfl, hinterval⟩ := cutBlock_spec hok left
  have hstrict (d : ℕ) (hd : d ∈ row)
      (hi : GM06DrawingData.cyclicBetween (row.idxOf (cutFirst p left))
        (row.idxOf (cutLast p left)) (row.idxOf d) = true) :
      d ∉ cutBoundaryEnds p := by
    intro hb
    have he := (cutKeep_boundaryEnd_iff hok left hb).mp
      ((hinterval d hd).mpr (Or.inr (Or.inr hi)))
    rcases he with he | he <;> rw [he] at hi <;>
      unfold GM06DrawingData.cyclicBetween at hi <;>
      split_ifs at hi <;> simp only [decide_eq_true_eq] at hi <;> omega
  apply label_eq_first_of_cyclic_interval row hn g hf hl hfl hd
  · rcases (hinterval d hd).mp hkeep with h | h | h
    · exact Or.inl h
    · exact False.elim (hlast h)
    · exact Or.inr h
  · intro e he hi
    exact hskip e he (hstrict e he hi)

end GraphMinor.GM06
