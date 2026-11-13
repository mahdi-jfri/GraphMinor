module

public import GraphMinor.GM06.Alg34GapCircleOrder
public import GraphMinor.Compute.GM06Alg34GapListPositions

/-!
# Crossing interpretations for an ordered list of circle labels

Identify each list position with its supplied vertex label. The ordered
circle construction then interprets the primal crossing test and both
gap crossing tests on those labels. The geometric existence proof can
use these identities before transferring the circle chart to a cuff.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

/-- The primal crossing test on a sorted label list is its geometric circle order. -/
theorem alg34_listed_vertex_circle_order {n : ℕ} {L : List (Fin n)} (hL : L.Nodup)
    (z : Fin n → Circle) (c : Circle)
    (hm : StrictMono (fun i : Fin L.length => c.angleDiff (z (L.get i))))
    (a b i j : Fin L.length) :
    GM06DrawingData.crossesOnList L (L.get a) (L.get b) (L.get i) (L.get j) = true ↔
      CrossesOn (univ : Set Circle) (z (L.get a)) (z (L.get b)) (z (L.get i)) (z (L.get j)) := by
  rw [gm06CrossesOnList_get hL]
  exact (alg34_gap_coordinate_order (circleCoordFrom c) (fun k => z (L.get k)) hm a b i j).trans
    (crossesOn_univ_iff_circleCoordFrom c).symm

/-- Listed primal pairs and their following gap pairs have exactly the supplied alternating order. -/
theorem alg34_listed_primal_gap_order {n : ℕ} {L : List (Fin n)} (hL : L.Nodup)
    (z : Fin n → Circle) (c : Circle) (hc : c ∈ z '' GM06DrawingData.block L)
    (p : Fin L.length → Circle)
    (hm : StrictMono (fun i : Fin L.length => c.angleDiff (z (L.get i))))
    (hp : ∀ i, p i ∈ nextSegment (z '' GM06DrawingData.block L) (z (L.get i)))
    (a b i j : Fin L.length) :
    GM06DrawingData.pairCrossesGaps L (L.get a) (L.get b) i j = true ↔
      CrossesOn (univ : Set Circle) (z (L.get a)) (z (L.get b)) (p i) (p j) := by
  rw [gm06PairCrossesGaps_get hL]
  exact alg34_primal_gap_circle_order hc (fun k => z (L.get k)) p
    (fun k => ⟨L.get k, L.get_mem k, rfl⟩) hm hp a b i j

/-- Gap points following a sorted label list have the cyclic order of the list positions. -/
theorem alg34_listed_gap_circle_order {n : ℕ} (L : List (Fin n))
    (z : Fin n → Circle) (c : Circle) (hc : c ∈ z '' GM06DrawingData.block L)
    (p : Fin L.length → Circle)
    (hm : StrictMono (fun i : Fin L.length => c.angleDiff (z (L.get i))))
    (hp : ∀ i, p i ∈ nextSegment (z '' GM06DrawingData.block L) (z (L.get i)))
    (a b i j : Fin L.length) :
    GM06DrawingData.crossesOnList (List.finRange L.length) a b i j = true ↔
      CrossesOn (univ : Set Circle) (p a) (p b) (p i) (p j) :=
  alg34_gap_circle_order hc (fun k => z (L.get k)) p
    (fun k => ⟨L.get k, L.get_mem k, rfl⟩) hm hp a b i j

end GraphMinor.GM06
