module

public import GraphMinor.Compute.GM06Alg34MapCrossing

/-!
# Extending listed crossing order to all labels

An injective list labelling supplies the cyclic order on the boundary.
For labels on the list, pull back to positions and use that order.
Labels outside the list cannot cross on the boundary because the list
covers exactly the boundary labels. This gives the complete order
condition required of a drawing representation.
-/

public section
namespace GraphMinor.Compute

open Set Surface GM06

/-- Crossing order on listed positions extends to every label when list
membership agrees with membership of its represented point in the cuff. -/
theorem gm06_crossesOnList_ofFn_iff {S : Type*} [TopologicalSpace S]
    {n k : ℕ} (f : Fin k → Fin n) (hf : Function.Injective f)
    (z : Fin n → S) (C : Set S)
    (hmem : ∀ a, z a ∈ C ↔ a ∈ List.ofFn f)
    (horder : ∀ a b i j, GM06DrawingData.crossesOnList (List.finRange k) a b i j = true ↔
      CrossesOn C (z (f a)) (z (f b)) (z (f i)) (z (f j)))
    (a b i j : Fin n) :
    GM06DrawingData.crossesOnList (List.ofFn f) a b i j = true ↔
      CrossesOn C (z a) (z b) (z i) (z j) := by
  have hlisted (ha : a ∈ List.ofFn f) (hb : b ∈ List.ofFn f)
      (hi : i ∈ List.ofFn f) (hj : j ∈ List.ofFn f) :
      GM06DrawingData.crossesOnList (List.ofFn f) a b i j = true ↔
        CrossesOn C (z a) (z b) (z i) (z j) := by
    obtain ⟨a', rfl⟩ := List.mem_ofFn.mp ha
    obtain ⟨b', rfl⟩ := List.mem_ofFn.mp hb
    obtain ⟨i', rfl⟩ := List.mem_ofFn.mp hi
    obtain ⟨j', rfl⟩ := List.mem_ofFn.mp hj
    rw [List.ofFn_eq_map, gm06_crossesOnList_map f hf]
    exact horder a' b' i' j'
  constructor
  · intro hc
    have hm := hc
    simp only [GM06DrawingData.crossesOnList, Bool.and_eq_true, decide_eq_true_eq] at hm
    exact (hlisted hm.1.1 hm.1.2.1 hm.1.2.2.1 hm.1.2.2.2.1).mp hc
  · intro hc
    exact (hlisted ((hmem a).mp hc.1) ((hmem b).mp hc.2.2.1)
      ((hmem i).mp hc.2.1) ((hmem j).mp hc.2.2.2.1)).mpr hc

end GraphMinor.Compute
