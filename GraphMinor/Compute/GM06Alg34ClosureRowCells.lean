module

public import GraphMinor.Compute.GM06Alg34RowEnumeration

/-!
# Supplied closure rows correspond to cells

The executable row lists contain precisely the numbered closure list
of every vertex, edge, and region cell. Enumerating finite positions
makes the correspondence explicit without extracting any new input
from geometric proofs.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The row number and numbered closure list of a finite input cell. -/
def gm06CellClosureRow (x : GM06DrawingData) (c : GM06CellIndex x) : ℕ × List ℕ :=
  ((x.cellNumbering c).val, (x.cellClosure c).map (fun d => (x.cellNumbering d).val))

/-- The supplied row lists enumerate exactly the finite vertex, edge,
and region closure rows. -/
theorem gm06ClosureRowLists_eq_cells (x : GM06DrawingData) :
    gm06ClosureRowLists x =
      ((List.finRange x.n).map (fun v => gm06CellClosureRow x (.inl v))) ++
      ((List.finRange x.ends.length).map (fun e => gm06CellClosureRow x (.inr (.inl e)))) ++
      ((List.finRange x.regions.length).map (fun r => gm06CellClosureRow x (.inr (.inr r)))) := by
  simp only [gm06ClosureRowLists, GM06DrawingData.raw]
  rw [List.zipIdx_map, List.zipIdx_map]
  simp only [
    gm06ZipIdx_eq_finRange, gm06Range_eq_finRange, List.map_map, Function.comp_def,
    Prod.map, gm06CellClosureRow, GM06DrawingData.numbered_cellClosure_vertex,
    GM06DrawingData.numbered_cellClosure_edge, GM06DrawingData.numbered_cellClosure_region,
    GM06DrawingData.cellNumbering_vertex_val, GM06DrawingData.cellNumbering_edge_val,
    GM06DrawingData.cellNumbering_region_val, Nat.add_assoc, id_eq]

/-- Every supplied row is the numbered closure of a cell, and every
finite cell supplies such a row. -/
theorem gm06ClosureRowLists_mem_iff (x : GM06DrawingData) (p : ℕ × List ℕ) :
    p ∈ gm06ClosureRowLists x ↔ ∃ c : GM06CellIndex x, gm06CellClosureRow x c = p := by
  rw [gm06ClosureRowLists_eq_cells]
  simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ((⟨v, hv⟩ | ⟨e, he⟩) | ⟨r, hr⟩)
    · exact ⟨.inl v, hv⟩
    · exact ⟨.inr (.inl e), he⟩
    · exact ⟨.inr (.inr r), hr⟩
  · rintro ⟨v | (e | r), he⟩
    · exact Or.inl (Or.inl ⟨v, he⟩)
    · exact Or.inl (Or.inr ⟨e, he⟩)
    · exact Or.inr ⟨r, he⟩

/-- All supplied row columns fit the original cell range. -/
theorem gm06ClosureRowLists_cols_lt (x : GM06DrawingData) :
    ∀ p ∈ gm06ClosureRowLists x, ∀ v ∈ p.2, v < x.cellCount := by
  intro p hp v hv
  obtain ⟨c, rfl⟩ := (gm06ClosureRowLists_mem_iff x p).mp hp
  exact x.numbered_cellClosure_lt c v hv

/-- A supplied row contains a numbered column exactly when that cell
lies in the closure of the row's cell. -/
theorem gm06ClosureRowLists_incidence_iff (x : GM06DrawingData) (a b : GM06CellIndex x) :
    (∃ p ∈ gm06ClosureRowLists x, p.1 = (x.cellNumbering a).val ∧
      (x.cellNumbering b).val ∈ p.2) ↔ b ∈ x.cellClosure a := by
  constructor
  · rintro ⟨p, hp, ha, hb⟩
    obtain ⟨c, rfl⟩ := (gm06ClosureRowLists_mem_iff x p).mp hp
    have hca : c = a := x.cellNumbering.injective (Fin.ext ha)
    subst c
    obtain ⟨d, hd, he⟩ := List.mem_map.mp hb
    have hdb : d = b := x.cellNumbering.injective (Fin.ext he)
    exact hdb ▸ hd
  · intro hb
    refine ⟨gm06CellClosureRow x a, (gm06ClosureRowLists_mem_iff x _).mpr ⟨a, rfl⟩,
      rfl, ?_⟩
    exact List.mem_map.mpr ⟨b, hb, rfl⟩

end GraphMinor.Compute
