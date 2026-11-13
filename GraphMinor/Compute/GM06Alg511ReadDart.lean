module

public import GraphMinor.Compute.GM06Alg511LabelGraph
public import GraphMinor.Compute.GM06Alg511DartKeys
import Mathlib.Tactic

/-!
# Interpreting selected directed edge positions

For VI (5.11), page 134, the RAM scan returns positions in the
consecutive endpoint array. Such a position determines its edge by
division by two and its orientation by parity. Between distinct
vertices, this is exactly the dart used by the finite labelled-walk
winding formula.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Surface

/-- A selected directed position with the requested distinct
endpoints gives a finite labelled edge with exactly that dart. -/
theorem gm06Alg511LabelEdge_of_dart {n : ℕ} (pairs : List (Fin n × Fin n))
    (a b : Fin n) (hab : a ≠ b) (d : ℕ) (hd : d < 2 * pairs.length)
    (hleft : (gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))).getD d 0 = a.val)
    (hright : (gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))).getD
      (gm06DartMate d) 0 = b.val) :
    ∃ (e : Fin pairs.length) (he : (gm06Alg511LabelGraph pairs).IsLink e a b),
      gm06Alg511LabelDart pairs he = d := by
  let q := d / 2
  have hq : q < pairs.length := by dsimp [q]; omega
  let e : Fin pairs.length := ⟨q, hq⟩
  obtain ⟨h0, h1⟩ := gm06Alg511EndpointWords_getD
    (pairs.map fun p => (p.1.val, p.2.val)) q (by simpa using hq)
  simp only [List.getElem_map] at h0 h1
  by_cases hp : d % 2 = 0
  · have hd' : d = 2 * q := by dsimp [q]; omega
    have hm : gm06DartMate d = 2 * q + 1 := by rw [hd']; simp [gm06DartMate]
    have ha : a = pairs[q].1 := Fin.ext (hleft.symm.trans (hd' ▸ h0))
    have hb : b = pairs[q].2 := Fin.ext (hright.symm.trans (hm ▸ h1))
    have he : (gm06Alg511LabelGraph pairs).IsLink e a b := Or.inl ⟨ha, hb⟩
    refine ⟨e, he, ?_⟩
    simp only [gm06Alg511LabelDart, e, ha, ite_true, Nat.add_zero]
    exact hd'.symm
  · have hd' : d = 2 * q + 1 := by dsimp [q]; omega
    have hm : gm06DartMate d = 2 * q := by
      rw [hd']; unfold gm06DartMate; split <;> omega
    have ha : a = pairs[q].2 := Fin.ext (hleft.symm.trans (hd' ▸ h1))
    have hb : b = pairs[q].1 := Fin.ext (hright.symm.trans (hm ▸ h0))
    have hne : a ≠ pairs[q].1 := fun h => hab (h.trans hb.symm)
    have he : (gm06Alg511LabelGraph pairs).IsLink e a b := Or.inr ⟨ha, hb⟩
    refine ⟨e, he, ?_⟩
    simp only [gm06Alg511LabelDart, e, hne, ite_false]
    exact hd'.symm

end GraphMinor.Compute
