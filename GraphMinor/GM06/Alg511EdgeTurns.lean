module

public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06SuccessorGraphRep
public import GraphMinor.GM06.Alg511CurveTurns
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Interpreting supplied edge turns in a cylinder drawing

The integer on a non-loop edge records its angular lift when traversed
from the first supplied endpoint to the second. A simple linkage path
never traverses a loop, so loop entries are zero. The interpretation
uses actual parametrizations of the edge closures. These are witnesses
in the representation relation, not fields in the finite input.
Every already labelled cylinder graph admits this supplementary data.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set

/-- Geometric meaning of the supplied edge-turn list. Non-loop edges
are parametrized from their first endpoint to their second, and the
integer is the full-turn part of that parametrization's angular lift. -/
def Alg511EdgeTurnsRep {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) (turns : List ℤ) : Prop :=
  ∃ hlen : turns.length = rep.pairs.length, ∀ i : Fin rep.pairs.length,
    if rep.pairs[i.val].1 = rep.pairs[i.val].2 then
      turns[i.val]'(by rw [hlen]; exact i.isLt) = 0
    else ∃ f : Curve ClosedCylinder,
      ParametrizesSet f (closure (rep.edge i).val)
        (rep.vertex rep.pairs[i.val].1).val (rep.vertex rep.pairs[i.val].2).val ∧
      Alg511CurveTurn f (turns[i.val]'(by rw [hlen]; exact i.isLt))

/-- Every graph with supplied vertex, edge and endpoint bijections
admits a finite list of geometric turn labels. Choices occur only in
this existence proof, never in an executable encoder. -/
theorem alg511_exists_edgeTurns {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) :
    ∃ turns : List ℤ, Alg511EdgeTurnsRep rep turns := by
  classical
  have hex : ∀ i : Fin rep.pairs.length, ∃ turn : ℤ,
      if rep.pairs[i.val].1 = rep.pairs[i.val].2 then turn = 0
      else ∃ f : Curve ClosedCylinder,
        ParametrizesSet f (closure (rep.edge i).val)
          (rep.vertex rep.pairs[i.val].1).val (rep.vertex rep.pairs[i.val].2).val ∧
        Alg511CurveTurn f turn := by
    intro i
    by_cases hi : rep.pairs[i.val].1 = rep.pairs[i.val].2
    · exact ⟨0, by simp only [hi, ↓reduceIte]⟩
    · have hinj : Function.Injective (fun j => (rep.vertex j).val) :=
        Subtype.val_injective.comp rep.vertex.injective
      obtain ⟨f, hf⟩ := exists_parametrizesSet_closure_edge G (rep.link i) (hinj.ne hi)
      obtain ⟨turn, ht⟩ := alg511_exists_curveTurn f
      exact ⟨turn, by simpa only [hi, ↓reduceIte] using Exists.intro f (And.intro hf ht)⟩
  choose turn ht using hex
  refine ⟨List.ofFn turn, List.length_ofFn, ?_⟩
  intro i
  simpa only [List.getElem_ofFn] using ht i

/-- A supplied finite graph input can be extended by turn data for its
actual cylinder drawing, while preserving all original supplied fields. -/
theorem alg511_exists_windingInput {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) :
    ∃ y : GM06Alg511WindingInput, y.drawing = x ∧ Alg511EdgeTurnsRep rep y.edgeTurns := by
  obtain ⟨turns, ht⟩ := alg511_exists_edgeTurns rep
  exact ⟨⟨x, turns⟩, rfl, ht⟩

end GraphMinor.GM06
