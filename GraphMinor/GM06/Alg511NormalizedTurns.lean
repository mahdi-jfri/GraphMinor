module

public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06SuccessorGraphRep
public import GraphMinor.GM06.Alg511RelativeTurns
public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Alg511ReferenceAngles
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Finite edge turns with prescribed cuff references

In the input for VI (5.11), describe each non-loop edge by its integer
whole turns relative to reference angles at its endpoint vertices.
The reference angles agree with the fixed cuff coordinates of page
127. They are witnesses in the geometric interpretation, not values
stored in the word array. Internal reference angles cancel along
paths, leaving only the known cuff indices and the integer turn sum.
Every already labelled cylinder drawing admits such finite edge data.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface Set Real

/-- Geometric interpretation of supplied edge turns, with references
fixed to the prescribed Section 5 angles on both cuffs. Only the
integer list is supplied to the finite program. -/
def Alg511NormalizedTurnsRep {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) (turns : List ℤ) : Prop :=
  ∃ reference : ClosedCylinder → ℝ,
    (∀ p, Circle.exp (reference p) = p.val.2) ∧
    (∀ i : Fin x.pathCount,
      reference (cylinderM1Point x.pathCount i) = 2 * ((i.val + 1 : ℕ) : ℝ) * π / x.pathCount) ∧
    (∀ i : Fin x.pathCount,
      reference (cylinderM2Point x.pathCount i) = 2 * ((i.val + 1 : ℕ) : ℝ) * π / x.pathCount) ∧
    ∃ hlen : turns.length = rep.pairs.length, ∀ i : Fin rep.pairs.length,
      if rep.pairs[i.val].1 = rep.pairs[i.val].2 then
        turns[i.val]'(by rw [hlen]; exact i.isLt) = 0
      else ∃ f : Curve ClosedCylinder,
        ParametrizesSet f (closure (rep.edge i).val)
          (rep.vertex rep.pairs[i.val].1).val (rep.vertex rep.pairs[i.val].2).val ∧
        Alg511RelativeCurveTurn f (reference (rep.vertex rep.pairs[i.val].1).val)
          (reference (rep.vertex rep.pairs[i.val].2).val)
          (turns[i.val]'(by rw [hlen]; exact i.isLt))

/-- Every already labelled cylinder drawing with a positive path
count admits finite edge turns normalized at the prescribed cuffs. -/
theorem alg511_exists_normalized_turns {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (hk : 0 < x.pathCount)
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph) :
    ∃ turns : List ℤ, Alg511NormalizedTurnsRep rep turns := by
  classical
  obtain ⟨reference, hexp, hM1, hM2⟩ := alg511_exists_reference_angles hk
  have hex : ∀ i : Fin rep.pairs.length, ∃ turn : ℤ,
      if rep.pairs[i.val].1 = rep.pairs[i.val].2 then turn = 0
      else ∃ f : Curve ClosedCylinder,
        ParametrizesSet f (closure (rep.edge i).val)
          (rep.vertex rep.pairs[i.val].1).val (rep.vertex rep.pairs[i.val].2).val ∧
        Alg511RelativeCurveTurn f (reference (rep.vertex rep.pairs[i.val].1).val)
          (reference (rep.vertex rep.pairs[i.val].2).val) turn := by
    intro i
    by_cases hi : rep.pairs[i.val].1 = rep.pairs[i.val].2
    · exact ⟨0, by simp only [hi, ↓reduceIte]⟩
    · have hinj : Function.Injective (fun j => (rep.vertex j).val) :=
        Subtype.val_injective.comp rep.vertex.injective
      obtain ⟨f, hf⟩ := exists_parametrizesSet_closure_edge G (rep.link i) (hinj.ne hi)
      obtain ⟨turn, ht⟩ := alg511_exists_relative_curveTurn f
        (reference (rep.vertex rep.pairs[i.val].1).val)
        (reference (rep.vertex rep.pairs[i.val].2).val)
        (by rw [hf.2.2.1]; exact hexp _)
        (by rw [hf.2.2.2]; exact hexp _)
      exact ⟨turn, by simpa only [hi, ↓reduceIte] using Exists.intro f (And.intro hf ht)⟩
  choose turn ht using hex
  refine ⟨List.ofFn turn, reference, hexp, hM1, hM2, List.length_ofFn, ?_⟩
  intro i
  simpa only [List.getElem_ofFn] using ht i

/-- Once the turns along a cuff-to-cuff path have been added, its
scaled winding is the integer `k * turn + endIndex - startIndex`.
This is the scalar computed in the winding phase of VI (5.11). -/
theorem alg511_scaled_winding_of_relative_turn {k : ℕ} (hk : 0 < k)
    (i j : Fin k) (f : Curve ClosedCylinder) (turn : ℤ)
    (ht : Alg511RelativeCurveTurn f (2 * ((i.val + 1 : ℕ) : ℝ) * π / k)
      (2 * ((j.val + 1 : ℕ) : ℝ) * π / k) turn) :
    (k : ℝ) * windingNumber f = (((k : ℤ) * turn + (j.val : ℤ) - (i.val : ℤ) : ℤ) : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
  rw [alg511_relative_curveTurn_iff.mp ht]
  push_cast
  field_simp [hk0, Real.pi_ne_zero]
  ring

end GraphMinor.GM06
