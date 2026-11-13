module

public import GraphMinor.GM06.Alg511EdgeTurns
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Reading an edge winding from its supplied turn

A non-loop edge has an injective parametrization, and any other
parametrization with the same orientation is homotopic to it within
its closure. Consequently the edge turn supplied to (5.11) determines
the winding of every traversal in that orientation. This removes any
dependence on the parametrization witnessing the input relation.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Complex Real Set

/-- The supplied turn determines the winding of any parametrization
of the non-loop edge in its supplied endpoint orientation. -/
theorem alg511_edge_winding_of_turn {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (turns : List ℤ) (hrep : Alg511EdgeTurnsRep rep turns)
    (hlen : turns.length = rep.pairs.length) (i : Fin rep.pairs.length)
    (hi : rep.pairs[i.val].1 ≠ rep.pairs[i.val].2)
    (g : Curve ClosedCylinder)
    (hg : ParametrizesSet g (closure (rep.edge i).val)
      (rep.vertex rep.pairs[i.val].1).val (rep.vertex rep.pairs[i.val].2).val) :
    windingNumber g =
      (arg ((rep.vertex rep.pairs[i.val].2).val.val.2 : ℂ) -
        arg ((rep.vertex rep.pairs[i.val].1).val.val.2 : ℂ)) / (2 * π) +
      (turns[i.val]'(by rw [hlen]; exact i.isLt) : ℝ) := by
  obtain ⟨_, hturns⟩ := hrep
  have he := hturns i
  rw [ite_eq_right hi] at he
  obtain ⟨f, hf, ht⟩ := he
  have hhom := curvesHomotopicIn_of_range_subset_parametrizesSet hf
    (show range g ⊆ closure (rep.edge i).val by rw [hg.2.1]) hg.2.2.1 hg.2.2.2
  have hhom' : CurvesHomotopic g f := by
    obtain ⟨H, _, h0, h1, h00, h01, h10, h11⟩ := hhom
    exact ⟨H, fun _ => trivial, h0, h1, h00, h01, h10, h11⟩
  rw [windingNumber_eq_of_homotopic hhom', alg511_windingNumber_of_curveTurn ht,
    hf.2.2.1, hf.2.2.2]

end GraphMinor.GM06
