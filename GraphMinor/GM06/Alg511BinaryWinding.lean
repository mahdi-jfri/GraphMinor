module

public import GraphMinor.Compute.GM06Alg511BinaryWinding
public import GraphMinor.GM06.Alg511ChosenWinding
import GraphMinor.GM06.Alg511CuffIndices
import Mathlib.Tactic

/-!
# The binary numerator is the actual linkage winding

After maximum flow, the retained labelled first path and its
actual path drawing have the same normalized edge turns. The
first path starts at source index zero. The normalized winding
formula therefore gives k times its turn sum plus the terminal
cuff index. The binary program computes exactly that integer.
All curves of the same cylinder linkage have the same winding,
so this computes the value used in VI (5.11), page 134.

The hypotheses describe the retained path and its ordinary graph
interpretation. The geometric transfer and program execution are
proved here. No winding value, magnitude word bound, or successor
result is supplied as a hypothesis.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

private theorem binary_dart_sum_eq_labelled_turn {x : GM06Alg511WindingInput}
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (turns : List GM06Alg511BinaryInteger) (hturns : x.edgeTurns = turns.map GM06Alg511BinaryInteger.value)
    {a b : Fin x.drawing.vertexCount} (W : GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) a b) :
    ((gm06Alg511LabelWalkDarts rep.graph.pairs W).map (gm06Alg511BinaryDartTurn turns)).sum =
      gm06Alg511LabelWalkTurn rep.graph.pairs x.edgeTurns W := by
  have hlen : x.edgeTurns.length = rep.graph.pairs.length := by
    obtain ⟨_, _, _, _, h, _⟩ := rep.turns
    exact h
  have hnewLen : turns.length = rep.graph.pairs.length := by simpa only [hturns, List.length_map] using hlen
  rw [gm06Alg511LabelWalkTurn_eq_dartSum rep.graph.pairs x.edgeTurns hlen W, hturns]
  congr 1
  apply List.map_congr_left
  intro d hd
  exact gm06Alg511BinaryDartTurn_eq_old turns d (by
    have hh := gm06Alg511LabelWalkDarts_lt rep.graph.pairs W d hd
    omega)

/-- The actual binary winding program returns the winding of the
retained linkage. The supplied data are its computed first path,
ordinary graph interpretation and terminal cuff index. The proof
uses the normalized winding formula of VI, pages 127–128, and the
binary arithmetic implementation of (5.11), page 134. -/
theorem alg511_binary_winding_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (turns : List GM06Alg511BinaryInteger) (hturns : x.edgeTurns = turns.map GM06Alg511BinaryInteger.value)
    (hk : 0 < x.drawing.pathCount)
    (b : Fin x.drawing.vertexCount) (hb : b ∈ x.drawing.flowInput.B)
    (j : Fin x.drawing.pathCount) (hj : rep.target j = b)
    (W : GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source ⟨0, hk⟩) b)
    (actual : GraphWalk G.toGraph (rep.graph.vertex (rep.source ⟨0, hk⟩)).val (rep.graph.vertex b).val)
    (hs : actual.IsSimple)
    (hturn : alg511InterpretedWalkTurn rep.graph x.edgeTurns actual =
      gm06Alg511LabelWalkTurn rep.graph.pairs x.edgeTurns W)
    (L : CylinderLinkage x.drawing.pathCount G)
    (hparam : ParametrizesSet (L.curve ⟨0, hk⟩) (walkDrawing G actual).U
      (rep.graph.vertex (rep.source ⟨0, hk⟩)).val (rep.graph.vertex b).val)
    (s : State) (hw : 3 < 2 ^ w)
    (hsize : x.drawing.pathCount + j.val + (gm06Alg511LabelWalkDarts rep.graph.pairs W).length +
      2 * (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 10 < 2 ^ w)
    (hTurns : s.arrs 2900 = gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words))
    (hPath : s.arrs 12 = gm06Alg511LabelWalkDarts rep.graph.pairs W)
    (hK : s.regs 52 = x.drawing.pathCount) (hJ : s.regs 46 = j.val) :
    ∃ t u out sign, Exec w gm06Alg511BinaryWindingProg s t u ∧
      u ≤ 4000 * (x.drawing.pathCount + j.val + (gm06Alg511LabelWalkDarts rep.graph.pairs W).length +
        (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 3) ^ 2 ∧
      t.arrs 2804 = sign :: out ∧ sign < 2 ∧
      out.length ≤ x.drawing.pathCount + j.val + (gm06Alg511LabelWalkDarts rep.graph.pairs W).length +
        (gm06EncodeRows (turns.map GM06Alg511BinaryInteger.words)).length + 3 ∧
      (∀ d ∈ out, d < 2) ∧ L.HasTheta ((gm06Alg511BinaryRowValue (t.arrs 2804) : ℝ) / x.drawing.pathCount) ∧
      t.regs 52 = s.regs 52 ∧ t.arrs 2900 = s.arrs 2900 ∧ t.arrs 12 = s.arrs 12 ∧
      TwoPaths.Keeps [0, 7, 8, 9, 11, 20, 31, 313, 2100, 2101, 2102, 2103, 2104, 2105, 2230, 2231, 2232, 2233, 2235, 2400, 2401, 2402, 2404, 2600, 2601, 2910, 2911, 2920]
        [2000, 2001, 2002, 2003, 2004, 2005, 2300, 2301, 2302, 2600, 2804, 2901, 2902, 2903, 2904] s t := by
  have hlen : x.edgeTurns.length = rep.graph.pairs.length := by
    obtain ⟨_, _, _, _, h, _⟩ := rep.turns
    exact h
  have hnewLen : turns.length = rep.graph.pairs.length := by simpa only [hturns, List.length_map] using hlen
  have hdarts : ∀ d ∈ gm06Alg511LabelWalkDarts rep.graph.pairs W, d < 2 * turns.length := by
    intro d hd
    have hh := gm06Alg511LabelWalkDarts_lt rep.graph.pairs W d hd
    omega
  obtain ⟨t, u, out, sign, he, ht, hkeep, hout, hsign, houtLen, hbits, hvalue⟩ :=
    gm06Alg511BinaryWindingProg_exec x.drawing.pathCount j.val turns
      (gm06Alg511LabelWalkDarts rep.graph.pairs W) s hw hsize hdarts hTurns hPath hK hJ
  obtain ⟨j', hj', htheta⟩ := alg511_linkage_hasTheta_of_labelled_path x rep hk ⟨0, hk⟩ b hb W actual hs hturn L hparam
  have hjEq : j' = j := rep.target_injective hk (hj'.trans hj.symm)
  subst j'
  have hsum := binary_dart_sum_eq_labelled_turn rep turns hturns W
  refine ⟨t, u, out, sign, he, ht, hout, hsign, houtLen, hbits, ?_,
    hkeep.1 52 (by decide), hkeep.2 2900 (by decide), hkeep.2 12 (by decide), hkeep⟩
  rw [hout, hvalue, hsum]
  simpa only [Fin.val_zero, Nat.cast_zero, sub_zero] using htheta

end GraphMinor.GM06
