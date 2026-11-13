module

public import GraphMinor.Compute.SpecsCrossingRec

/-!
# The data needed for a contraction lift

Section 11 of the crossing note `docs/crossing/crossing_extractor.tex` lifts a path by testing old
edges incident with the retained vertex. The record encoding stores exactly these neighbours and
the two cycle membership flags. This file shows that those data suffice to compute the same list as
the mathematical contraction lift. No other edge of the old graph is needed.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- The star whose centre is the retained vertex and whose leaves are its recorded neighbours.
It supplies the adjacency tests used by Section 11, rather than reconstructing the old graph. -/
def liftNeighbourGraph {N : ℕ} (v : Fin N) (Nv : List (Fin N)) : SimpleGraph (Fin N) where
  Adj a b := a ≠ b ∧ ((a = v ∧ b ∈ Nv) ∨ (b = v ∧ a ∈ Nv))
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim (fun h => Or.inr h) (fun h => Or.inl h)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {N : ℕ} (v : Fin N) (Nv : List (Fin N)) :
    DecidableRel (liftNeighbourGraph v Nv).Adj :=
  fun a b => inferInstanceAs (Decidable (a ≠ b ∧ ((a = v ∧ b ∈ Nv) ∨ (b = v ∧ a ∈ Nv))))

/-- The star gives exactly the old adjacency tests at its centre. -/
theorem liftNeighbourGraph_adj {N : ℕ} {G : SimpleGraph (Fin N)} {v : Fin N}
    {Nv : List (Fin N)} (hNv : ∀ y, y ∈ Nv ↔ G.Adj v y) (y : Fin N) :
    (liftNeighbourGraph v Nv).Adj v y ↔ G.Adj v y := by
  change (v ≠ y ∧ ((v = v ∧ y ∈ Nv) ∨ (y = v ∧ v ∈ Nv))) ↔ _
  have hv : v ∉ Nv := fun h => G.loopless.irrefl v ((hNv v).1 h)
  simp only [hv, and_false, or_false, true_and, hNv]
  exact ⟨And.right, fun h => ⟨G.ne_of_adj h, h⟩⟩

/-- The three contraction lift formulas use only the adjacency row of the retained vertex. -/
theorem contraction_lift_row_congr {V : Type*} [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (u v : V) (hrow : ∀ y, G.Adj v y ↔ H.Adj v y) (L : List V) :
    liftOffOff G u v L = liftOffOff H u v L ∧
      liftOneOn G u v L = liftOneOn H u v L ∧
      liftBothOn G u v L = liftBothOn H u v L := by
  have hstartOne : ∀ L : List V, liftStartOneOn G u v L = liftStartOneOn H u v L := by
    intro L
    cases L with
    | nil => rfl
    | cons a L =>
      cases L with
      | nil => rfl
      | cons b L => simp only [liftStartOneOn, hrow]
  have hstartBoth : ∀ L : List V, liftStartBothOn G u v L = liftStartBothOn H u v L := by
    intro L
    cases L with
    | nil => rfl
    | cons a L =>
      cases L with
      | nil => rfl
      | cons b L => simp only [liftStartBothOn, hrow]
  refine ⟨?_, ?_, ?_⟩
  · simp only [liftOffOff, hrow]
  · simp only [liftOneOn, hstartOne]
  · simp only [liftBothOn, hstartBoth]

/-- Compute a contraction lift from the two endpoints, their cycle flags, and the neighbour
list. These are all fields of `IsRecordEnc` for a contraction. -/
def liftContractData {N : ℕ} (u v : Fin N) (uOn vOn : Bool)
    (Nv : List (Fin N)) (L : List (Fin N)) : List (Fin N) :=
  if uOn then liftBothOn (liftNeighbourGraph v Nv) u v L
  else if vOn then liftOneOn (liftNeighbourGraph v Nv) u v L
  else liftOffOff (liftNeighbourGraph v Nv) u v L

/-- The list computed from the recorded neighbours is exactly the Section 11 lift.
No validity or crossing hypothesis is needed for this equality of the two computations. -/
theorem liftContractData_eq {N : ℕ} (r : ContractRecord (Fin N))
    [DecidableRel r.graph.Adj] (Nv : List (Fin N))
    (hNv : ∀ y, y ∈ Nv ↔ r.graph.Adj r.v y) (L : List (Fin N)) :
    liftContractData r.u r.v (decide (r.u ∈ r.cycle)) (decide (r.v ∈ r.cycle)) Nv L =
      r.lift L := by
  obtain ⟨hOff, hOne, hBoth⟩ := contraction_lift_row_congr
    (liftNeighbourGraph r.v Nv) r.graph r.u r.v (liftNeighbourGraph_adj hNv) L
  simp only [liftContractData, ContractRecord.lift, decide_eq_true_eq, hOff, hOne, hBoth]

end GraphMinor.Compute.Crossing
