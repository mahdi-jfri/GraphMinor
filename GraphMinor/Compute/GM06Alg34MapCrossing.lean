module

public import GraphMinor.Compute.GM06Alg34FilterCrossing

/-!
# Crossing order is unchanged by injective label maps

An injective map changes the names of labels but leaves their positions
in a list unchanged. The membership, distinctness, and index comparisons
in the finite crossing test are therefore preserved. This connects
canonical new vertex numbers to their old surviving cuff labels.
-/

public section
namespace GraphMinor.Compute

/-- Injectively changing list labels leaves each label's index unchanged. -/
theorem gm06_idxOf_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (L : List α) (a : α) :
    (L.map f).idxOf (f a) = L.idxOf a := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    by_cases hba : b = a
    · subst b; simp
    · have hfba : f b ≠ f a := fun h => hba (hf h)
      simp only [List.map_cons, List.idxOf_cons_ne _ hba, List.idxOf_cons_ne _ hfba, ih]

/-- Injective relabelling preserves the finite cuff crossing test. -/
theorem gm06_crossesOnList_map {n m : ℕ} (f : Fin n → Fin m) (hf : Function.Injective f)
    (L : List (Fin n)) (a c b d : Fin n) :
    GM06DrawingData.crossesOnList (L.map f) (f a) (f c) (f b) (f d) =
      GM06DrawingData.crossesOnList L a c b d := by
  have hmem (v : Fin n) : f v ∈ L.map f ↔ v ∈ L := by
    constructor
    · intro hv
      obtain ⟨w, hw, heq⟩ := List.mem_map.mp hv
      exact hf heq ▸ hw
    · exact fun hv => List.mem_map.mpr ⟨v, hv, rfl⟩
  simp only [GM06DrawingData.crossesOnList, hmem, ne_eq, hf.eq_iff, gm06_idxOf_map f hf]

end GraphMinor.Compute
