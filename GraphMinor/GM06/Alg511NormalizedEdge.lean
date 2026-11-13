module

public import GraphMinor.GM06.Alg511NormalizedTurns
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Oriented edge paths from the normalized finite input

The turn list of VI (5.11) is indexed by the supplied edge labels.
Interpreting an actual edge traversal chooses its label through the
supplied bijection and changes the integer's sign when traversing it
backwards. Every non-loop traversal has a path with exactly that
relative turn. The interpretation below is mathematical only. It
is not a geometric encoder or a word-array field.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set Real

/-- Interpret the integer contribution of an actual oriented edge
using the supplied edge and endpoint bijections. -/
noncomputable def alg511InterpretedEdgeTurn {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) (turns : List ℤ)
    {e : Set ClosedCylinder} {u v : ClosedCylinder} (he : G.toGraph.IsLink e u v) : ℤ := by
  classical
  let i := rep.edge.symm ⟨e, he.edge_mem⟩
  exact if u = (rep.vertex rep.pairs[i.val].1).val then turns.getD i.val 0 else -turns.getD i.val 0

/-- The normalized geometric input supplies an oriented path for
every non-loop edge, with precisely its interpreted integer turn. -/
theorem alg511_normalized_edge_paths {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (turns : List ℤ) (hrep : Alg511NormalizedTurnsRep rep turns) :
    ∃ reference : ClosedCylinder → ℝ,
      (∀ p, Circle.exp (reference p) = p.val.2) ∧
      (∀ i : Fin x.pathCount,
        reference (cylinderM1Point x.pathCount i) = 2 * ((i.val + 1 : ℕ) : ℝ) * π / x.pathCount) ∧
      (∀ i : Fin x.pathCount,
        reference (cylinderM2Point x.pathCount i) = 2 * ((i.val + 1 : ℕ) : ℝ) * π / x.pathCount) ∧
      ∀ {e : Set ClosedCylinder} {u v : ClosedCylinder} (he : G.toGraph.IsLink e u v),
        u ≠ v → ∃ p : Path u v, range p = closure e ∧
          Alg511RelativeCurveTurn p.toContinuousMap (reference u) (reference v)
            (alg511InterpretedEdgeTurn rep turns he) := by
  classical
  obtain ⟨reference, hexp, hM1, hM2, hlen, hturns⟩ := hrep
  refine ⟨reference, hexp, hM1, hM2, ?_⟩
  intro e u v he hne
  let i := rep.edge.symm ⟨e, he.edge_mem⟩
  have heq : (rep.edge i).val = e := congrArg Subtype.val (rep.edge.apply_symm_apply _)
  have hcanon := rep.link i
  rw [heq] at hcanon
  have hends := he.eq_and_eq_or_eq_and_eq hcanon
  have hAB : (rep.vertex rep.pairs[i.val].1).val ≠ (rep.vertex rep.pairs[i.val].2).val := by
    intro h
    rcases hends with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact hne (hu.trans (h.trans hv.symm))
    · exact hne (hu.trans (h.symm.trans hv.symm))
  have hindices : rep.pairs[i.val].1 ≠ rep.pairs[i.val].2 :=
    fun h => hAB (congrArg (fun a => (rep.vertex a).val) h)
  have hdata := hturns i
  rw [ite_eq_right hindices] at hdata
  obtain ⟨f, hf, ht⟩ := hdata
  let p : Path (rep.vertex rep.pairs[i.val].1).val (rep.vertex rep.pairs[i.val].2).val := {
    toContinuousMap := f
    source' := hf.2.2.1
    target' := hf.2.2.2 }
  have hget : turns.getD i.val 0 = turns[i.val]'(by rw [hlen]; exact i.isLt) := by
    simp only [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show i.val < turns.length by rw [hlen]; exact i.isLt), Option.getD_some]
  have hp : Alg511RelativeCurveTurn p.toContinuousMap
      (reference (rep.vertex rep.pairs[i.val].1).val)
      (reference (rep.vertex rep.pairs[i.val].2).val) (turns.getD i.val 0) := by
    rw [hget]
    exact ht
  have hrange : range p = closure e := hf.2.1.trans (congrArg closure heq)
  rcases hends with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hweight : alg511InterpretedEdgeTurn rep turns he = turns.getD i.val 0 := by
      change (if u = (rep.vertex rep.pairs[i.val].1).val then turns.getD i.val 0 else -turns.getD i.val 0) = _
      exact ite_eq_left hu
    refine ⟨p.cast hu hv, hrange, ?_⟩
    change Alg511RelativeCurveTurn p.toContinuousMap (reference u) (reference v) _
    rw [hweight, congrArg reference hu, congrArg reference hv]
    exact hp
  · have hnot : u ≠ (rep.vertex rep.pairs[i.val].1).val :=
      fun h => hAB (h.symm.trans hu)
    have hweight : alg511InterpretedEdgeTurn rep turns he = -turns.getD i.val 0 := by
      change (if u = (rep.vertex rep.pairs[i.val].1).val then turns.getD i.val 0 else -turns.getD i.val 0) = _
      exact ite_eq_right hnot
    refine ⟨p.symm.cast hu hv, ?_, ?_⟩
    · change range p.symm = closure e
      rw [Path.symm_range]
      exact hrange
    · change Alg511RelativeCurveTurn p.symm.toContinuousMap (reference u) (reference v) _
      rw [hweight, congrArg reference hu, congrArg reference hv]
      exact alg511_relative_curveTurn_symm p hp

end GraphMinor.GM06
