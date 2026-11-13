module

public import GraphMinor.Compute.GM06Alg511ReflectedInput
public import GraphMinor.Compute.GM06Alg511TurnWords
import Mathlib.Tactic

/-!
# Unsigned arithmetic for reflected integer edge turns

The orientation step of VI (5.11), page 134, replaces an edge turn
by its negative plus the source correction minus the target
correction. Swap its two magnitude parts, add the two correction
bits, and subtract the resulting naturals in both orders. This gives
exactly the canonical two-word encoding of the new integer.
-/

public section
namespace GraphMinor.Compute

/-- Reflected signed magnitude words are computed by two natural
subtractions after adding the endpoint corrections. -/
theorem gm06Alg511ReflectedTurn_parts (t : ℤ) (a b : ℕ) :
    (-t + (a : ℤ) - (b : ℤ)).toNat =
      ((-t).toNat + a) - (t.toNat + b) ∧
    (-(-t + (a : ℤ) - (b : ℤ))).toNat =
      (t.toNat + b) - ((-t).toNat + a) := by
  omega

/-- Every directed position in the new signed word row has the
uniform unsigned formula used by the reflection loop. -/
theorem gm06Alg511ReflectedTurnWords_getD (x : GM06Alg511WindingInput)
    (d : ℕ)
    (hd : d < 2 * x.edgeTurns.length) :
    (gm06Alg511TurnWords x.reflected.edgeTurns).getD d 0 =
      ((gm06Alg511TurnWords x.edgeTurns).getD (gm06DartMate d) 0 +
        gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD d 0)) -
      ((gm06Alg511TurnWords x.edgeTurns).getD d 0 +
        gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (gm06DartMate d) 0)) := by
  let i := d / 2
  have hi : i < x.edgeTurns.length := by dsimp [i]; omega
  have hr : i < x.reflected.edgeTurns.length := by
    simpa only [GM06Alg511WindingInput.reflected, List.length_mapIdx] using hi
  have hnew : x.reflected.edgeTurns.getD i 0 =
      -x.edgeTurns.getD i 0 +
        (gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (2 * i) 0) : ℤ) -
        (gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (2 * i + 1) 0) : ℤ) := by
    let update := fun (j : ℕ) (t : ℤ) => -t +
      (gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (2 * j) 0) : ℤ) -
      (gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (2 * j + 1) 0) : ℤ)
    change (x.edgeTurns.mapIdx update).getD i 0 = _
    have hm : i < (x.edgeTurns.mapIdx update).length := by simpa using hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, List.getElem_mapIdx,
      Option.getD_some, List.getElem?_eq_getElem hi]
    rfl
  obtain ⟨hp, hn⟩ := gm06Alg511TurnWords_getD x.edgeTurns i hi
  obtain ⟨hp', hn'⟩ := gm06Alg511TurnWords_getD x.reflected.edgeTurns i hr
  obtain ⟨hpos, hneg⟩ := gm06Alg511ReflectedTurn_parts (x.edgeTurns.getD i 0)
    (gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (2 * i) 0))
    (gm06Alg511CuffOffset x.drawing (x.drawing.endpoints.getD (2 * i + 1) 0))
  by_cases he : d % 2 = 0
  · have hd' : d = 2 * i := by dsimp [i]; omega
    have hm : gm06DartMate d = 2 * i + 1 := by rw [hd']; simp [gm06DartMate]
    rw [hm, hd', hp', hnew, hn, hp]
    exact hpos
  · have hd' : d = 2 * i + 1 := by dsimp [i]; omega
    have hm : gm06DartMate d = 2 * i := by
      rw [hd']; unfold gm06DartMate; split <;> omega
    rw [hm, hd', hn', hnew, hp, hn]
    exact hneg

end GraphMinor.Compute
