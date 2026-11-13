module

public import GraphMinor.GM06.Alg34GapListOrder

/-!
# Crossing order for labels occurring in a cuff list

Each occurring label has a list position. Substituting those positions
in the proved circle-order identities gives the same comparisons on
the original vertex labels. This avoids imposing an order on labels
outside the cuff.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

/-- Four occurring labels have the geometric crossing order of their sorted circle list. -/
theorem alg34_mem_vertex_circle_order {n : ℕ} {L : List (Fin n)} (hL : L.Nodup)
    (z : Fin n → Circle) (c : Circle)
    (hm : StrictMono (fun i : Fin L.length => c.angleDiff (z (L.get i))))
    {a b i j : Fin n} (ha : a ∈ L) (hb : b ∈ L) (hi : i ∈ L) (hj : j ∈ L) :
    GM06DrawingData.crossesOnList L a b i j = true ↔
      CrossesOn (univ : Set Circle) (z a) (z b) (z i) (z j) := by
  obtain ⟨a', ha'⟩ := List.mem_iff_get.mp ha
  obtain ⟨b', hb'⟩ := List.mem_iff_get.mp hb
  obtain ⟨i', hi'⟩ := List.mem_iff_get.mp hi
  obtain ⟨j', hj'⟩ := List.mem_iff_get.mp hj
  simpa only [ha', hb', hi', hj'] using alg34_listed_vertex_circle_order hL z c hm a' b' i' j'

/-- An occurring primal pair has exactly the geometric crossing order with the following gaps. -/
theorem alg34_mem_primal_gap_order {n : ℕ} {L : List (Fin n)} (hL : L.Nodup)
    (z : Fin n → Circle) (c : Circle) (hc : c ∈ z '' GM06DrawingData.block L)
    (p : Fin L.length → Circle)
    (hm : StrictMono (fun i : Fin L.length => c.angleDiff (z (L.get i))))
    (hp : ∀ i, p i ∈ nextSegment (z '' GM06DrawingData.block L) (z (L.get i)))
    {a b : Fin n} (ha : a ∈ L) (hb : b ∈ L) (i j : Fin L.length) :
    GM06DrawingData.pairCrossesGaps L a b i j = true ↔
      CrossesOn (univ : Set Circle) (z a) (z b) (p i) (p j) := by
  obtain ⟨a', ha'⟩ := List.mem_iff_get.mp ha
  obtain ⟨b', hb'⟩ := List.mem_iff_get.mp hb
  simpa only [ha', hb'] using alg34_listed_primal_gap_order hL z c hc p hm hp a' b' i j

end GraphMinor.GM06
