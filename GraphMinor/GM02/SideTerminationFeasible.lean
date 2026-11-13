module

public import GraphMinor.GM02.SideTermination
public import GraphMinor.GM02.SidePiecePaths

/-!
# Realizing the side terminations

Select the unique maximal-run piece with each endpoint pair. Its assigned
side path realizes that pair. The original linkage makes distinct pieces
on the same side disjoint, so both new terminations are feasible in their
side graphs. The same construction applies after reservation deletions
once their paths have been shown to avoid the deleted vertices.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

/-- Select the piece that supplied a pair of the side termination. -/
noncomputable def sidePairPiece (side : Bool)
    (p : {p // p ∈ (sideTermination A G H P hP side).pairs}) : RunPieceIndex A G H P :=
  ((mem_sideTermination_pairs A G H P hP side p.val).1 p.property).choose

/-- A selected representative has the required side color. -/
theorem sidePairPiece_color (side : Bool)
    (p : {p // p ∈ (sideTermination A G H P hP side).pairs}) :
    (sidePairPiece A G H P hP side p).color A G H P = side :=
  ((mem_sideTermination_pairs A G H P hP side p.val).1 p.property).choose_spec.1

/-- A selected representative has exactly the prescribed pair. -/
theorem sidePairPiece_pair (side : Bool)
    (p : {p // p ∈ (sideTermination A G H P hP side).pairs}) :
    (sidePairPiece A G H P hP side p).pair A G H P = p.val :=
  ((mem_sideTermination_pairs A G H P hP side p.val).1 p.property).choose_spec.2

/-- Paths realizing every piece on a side, with their original supports,
make the corresponding side termination feasible. -/
theorem sideTermination_feasible_of_paths (side : Bool) (K : Graph α β)
    (R : ∀ i : RunPieceIndex A G H P, i.color A G H P = side →
      PairPath (pathGraph K) (i.pair A G H P))
    (hR : ∀ i hc, (R i hc).vertices = (i.path A G H P).vertices) :
    (sideTermination A G H P hP side).Feasible K := by
  let J := {p // p ∈ (sideTermination A G H P hP side).pairs}
  let Q : ∀ p : J, PairPath (pathGraph K) p.val := fun p =>
    let i := sidePairPiece A G H P hP side p
    let hc := sidePairPiece_color A G H P hP side p
    { start := (R i hc).start
      finish := (R i hc).finish
      ends_eq := (R i hc).ends_eq.trans (sidePairPiece_pair A G H P hP side p)
      walk := (R i hc).walk
      isPath := (R i hc).isPath }
  refine ⟨Q, ?_⟩
  intro p q hpq
  let i := sidePairPiece A G H P hP side p
  let j := sidePairPiece A G H P hP side q
  have hi := sidePairPiece_color A G H P hP side p
  have hj := sidePairPiece_color A G H P hP side q
  have heI := sidePairPiece_pair A G H P hP side p
  have heJ := sidePairPiece_pair A G H P hP side q
  have hij : i ≠ j := by
    intro heq
    apply hpq
    apply Subtype.ext
    exact heI.symm.trans ((congrArg (fun k => k.pair A G H P) heq).trans heJ)
  change Disjoint (R i hi).vertices (R j hj).vertices
  rw [hR i hi, hR j hj]
  exact RunPieceIndex.same_color_disjoint A G H P hP i j hij (hi.trans hj.symm)

/-- The termination on the first side is feasible in that side's graph,
before the reservation deletions. -/
theorem sideTermination_left_feasible : (sideTermination A G H P hP true).Feasible H := by
  apply sideTermination_feasible_of_paths A G H P hP true H
    (fun i hc => i.leftPath A G H P hc)
  exact fun i hc => i.leftPath_vertices A G H P hc

/-- The termination on the second side is feasible in that side's graph,
before the reservation deletions. -/
theorem sideTermination_right_feasible {H' : Graph α β} (hsep : IsSeparation G H H') :
    (sideTermination A G H P hP false).Feasible H' := by
  apply sideTermination_feasible_of_paths A G H P hP false H'
    (fun i hc => i.rightPath A G H P hsep hc)
  exact fun i hc => i.rightPath_vertices A G H P hsep hc

end GraphMinor.GM02
