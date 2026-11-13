module

public import GraphMinor.GM06.Alg511NormalizedWalk
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Winding of a path from its finite edge-turn sum

In the winding phase of VI (5.11), page 134, the joined edge paths
have the integer turn sum. Any injective parametrization of the same
simple walk drawing is homotopic to that joined curve inside the path.
Its winding is therefore the same. For prescribed cuff endpoints, the
scaled winding is the integer turn sum times the path count, plus the
difference between the two endpoint indices.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11 Set Real

/-- The finite turn sum determines the winding of every injective
parametrization of a simple walk drawing, for one common choice of
reference angles agreeing with the input on both cuffs. -/
theorem alg511_normalized_walk_winding {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (turns : List ℤ) (hrep : Alg511NormalizedTurnsRep rep turns) :
    ∃ reference : ClosedCylinder → ℝ,
      (∀ i : Fin x.pathCount,
        reference (cylinderM1Point x.pathCount i) = 2 * ((i.val + 1 : ℕ) : ℝ) * π / x.pathCount) ∧
      (∀ i : Fin x.pathCount,
        reference (cylinderM2Point x.pathCount i) = 2 * ((i.val + 1 : ℕ) : ℝ) * π / x.pathCount) ∧
      ∀ {u v : ClosedCylinder} (W : GraphWalk G.toGraph u v), W.IsSimple →
        ∀ f : Curve ClosedCylinder, ParametrizesSet f (walkDrawing G W).U u v →
          windingNumber f = (reference v - reference u) / (2 * π) +
            (alg511InterpretedWalkTurn rep turns W : ℝ) := by
  obtain ⟨reference, _, hM1, hM2, hpaths⟩ := alg511_normalized_walk_paths rep turns hrep
  refine ⟨reference, hM1, hM2, ?_⟩
  intro u v W hs f hf
  obtain ⟨p, hpRange, hpTurn⟩ := hpaths W hs
  have hhom := curvesHomotopicIn_of_range_subset_parametrizesSet hf hpRange p.source p.target
  have hhom' : CurvesHomotopic p.toContinuousMap f := by
    obtain ⟨H, _, h0, h1, h00, h01, h10, h11⟩ := hhom
    exact ⟨H, fun _ => trivial, h0, h1, h00, h01, h10, h11⟩
  rw [← windingNumber_eq_of_homotopic hhom', alg511_relative_curveTurn_iff.mp hpTurn]

/-- For a path between the prescribed cuffs, the finite integer sum
computes its scaled winding exactly. -/
theorem alg511_scaled_walk_winding {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (hk : 0 < x.pathCount)
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (turns : List ℤ) (hrep : Alg511NormalizedTurnsRep rep turns)
    (i j : Fin x.pathCount)
    (W : GraphWalk G.toGraph (cylinderM1Point x.pathCount i) (cylinderM2Point x.pathCount j))
    (hs : W.IsSimple) (f : Curve ClosedCylinder)
    (hf : ParametrizesSet f (walkDrawing G W).U
      (cylinderM1Point x.pathCount i) (cylinderM2Point x.pathCount j)) :
    (x.pathCount : ℝ) * windingNumber f =
      (((x.pathCount : ℤ) * alg511InterpretedWalkTurn rep turns W +
        (j.val : ℤ) - (i.val : ℤ) : ℤ) : ℝ) := by
  obtain ⟨reference, hM1, hM2, hw⟩ := alg511_normalized_walk_winding rep turns hrep
  have h := hw W hs f hf
  rw [hM1, hM2] at h
  exact alg511_scaled_winding_of_relative_turn hk i j f
    (alg511InterpretedWalkTurn rep turns W) (alg511_relative_curveTurn_iff.mpr h)

end GraphMinor.GM06
