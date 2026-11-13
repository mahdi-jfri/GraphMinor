module

public import GraphMinor.GM06.Alg511ReflectedReferences
public import GraphMinor.GM06.Alg511ReflectedGraph
public import GraphMinor.GM06.Alg511NormalizedTurns
import GraphMinor.Compute.GM06Alg511DartKeys
import Mathlib.Tactic

/-!
# Correctness of the finite reflected edge turns

For the orientation reversal in VI (5.11), page 134, reflect an
actual edge curve. Its winding is negated. The normalized reference
at each endpoint has the computed whole-turn correction, so its new
integer edge turn is the old negative turn plus the source correction
minus the target correction. This is exactly the finite input map.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set Real

private theorem turn_arithmetic (C u v : ℝ) (z a b : ℤ) :
    -((v - u) / (2 * π) + (z : ℝ)) =
      ((C - v + 2 * π * (b : ℝ)) - (C - u + 2 * π * (a : ℝ))) / (2 * π) +
        ((-z + a - b : ℤ) : ℝ) := by
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

/-- The reflected turn row describes precisely the actual reflected
edges, with the same edge labels and canonical cuff references. -/
theorem alg511_normalized_turns_reflected {x : GM06Alg511WindingInput}
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) :
    Alg511NormalizedTurnsRep (alg511ReflectedGraphRep rep.graph) x.reflected.edgeTurns := by
  obtain ⟨reference, hexp, hM1, hM2, hlen, hturns⟩ := rep.turns
  obtain ⟨reference', hexp', hM1', hM2', hreflect⟩ :=
    alg511_reflected_references rep hk reference hexp hM1 hM2
  have hlen' : x.reflected.edgeTurns.length = rep.graph.pairs.length := by
    simpa [GM06Alg511WindingInput.reflected] using hlen
  have hentry (i : Fin rep.graph.pairs.length) :
      x.reflected.edgeTurns[i.val]'(by rw [hlen']; exact i.isLt) =
        -x.edgeTurns[i.val]'(by rw [hlen]; exact i.isLt) +
          (gm06Alg511CuffOffset x.drawing rep.graph.pairs[i.val].1.val : ℤ) -
          (gm06Alg511CuffOffset x.drawing rep.graph.pairs[i.val].2.val : ℤ) := by
    have hend : x.drawing.endpoints = gm06EndpointWords
        (rep.graph.pairs.map fun p => (p.1.val, p.2.val)) := rep.graph.endpoints
    obtain ⟨h0, h1⟩ := gm06Alg511EndpointWords_getD
      (rep.graph.pairs.map fun p => (p.1.val, p.2.val)) i.val (by simp)
    simp only [List.getElem_map] at h0 h1
    let update := fun (j : ℕ) (t : ℤ) => -t +
      (gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (2 * j) 0) : ℤ) -
      (gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (2 * j + 1) 0) : ℤ)
    change (x.edgeTurns.mapIdx update)[i.val]'(by simp only [List.length_mapIdx]; rw [hlen]; exact i.isLt) = _
    rw [List.getElem_mapIdx]
    dsimp only [update]
    rw [hend, h0, h1]
  refine ⟨reference', hexp', hM1', hM2', hlen', ?_⟩
  change ∀ i : Fin rep.graph.pairs.length, (if rep.graph.pairs[i.val].1 = rep.graph.pairs[i.val].2 then
    x.reflected.edgeTurns[i.val]'(by rw [hlen']; exact i.isLt) = 0
    else ∃ f : Curve ClosedCylinder,
      ParametrizesSet f (closure (section5CylinderReflection x.drawing.pathCount '' (rep.graph.edge i).val))
        (section5CylinderReflection x.drawing.pathCount (rep.graph.vertex rep.graph.pairs[i.val].1).val)
        (section5CylinderReflection x.drawing.pathCount (rep.graph.vertex rep.graph.pairs[i.val].2).val) ∧
      Alg511RelativeCurveTurn f
        (reference' (section5CylinderReflection x.drawing.pathCount
          (rep.graph.vertex rep.graph.pairs[i.val].1).val))
        (reference' (section5CylinderReflection x.drawing.pathCount
          (rep.graph.vertex rep.graph.pairs[i.val].2).val))
        (x.reflected.edgeTurns[i.val]'(by rw [hlen']; exact i.isLt)))
  intro i
  by_cases heq : rep.graph.pairs[i.val].1 = rep.graph.pairs[i.val].2
  · simp only [heq, ite_true]
    have ht := hturns i
    simp only [heq, ite_true] at ht
    rw [hentry, ht, heq]
    omega
  · simp only [heq, ite_false]
    have ht := hturns i
    simp only [heq, ite_false] at ht
    obtain ⟨f, hf, hz⟩ := ht
    refine ⟨section5ReflectedCurve x.drawing.pathCount f, ?_, ?_⟩
    · refine ⟨(section5CylinderReflection x.drawing.pathCount).injective.comp hf.1, ?_, ?_, ?_⟩
      · change range (section5CylinderReflection x.drawing.pathCount ∘ f) = _
        rw [range_comp, hf.2.1, ← (section5CylinderReflection x.drawing.pathCount).image_closure]
      · change section5CylinderReflection x.drawing.pathCount (f 0) = _
        exact congrArg _ hf.2.2.1
      · change section5CylinderReflection x.drawing.pathCount (f 1) = _
        exact congrArg _ hf.2.2.2
    · apply alg511_relative_curveTurn_iff.mpr
      have hsource := hreflect rep.graph.pairs[i.val].1
      have htarget := hreflect rep.graph.pairs[i.val].2
      rw [windingNumber_section5ReflectedCurve, alg511_relative_curveTurn_iff.mp hz,
        htarget, hsource, hentry i]
      simpa only [Int.cast_natCast] using turn_arithmetic (4 * π / x.drawing.pathCount)
        (reference (rep.graph.vertex rep.graph.pairs[i.val].1).val)
        (reference (rep.graph.vertex rep.graph.pairs[i.val].2).val)
        (x.edgeTurns[i.val]'(by rw [hlen]; exact i.isLt))
        (gm06Alg511CuffOffset x.drawing rep.graph.pairs[i.val].1.val : ℤ)
        (gm06Alg511CuffOffset x.drawing rep.graph.pairs[i.val].2.val : ℤ)

end GraphMinor.GM06
