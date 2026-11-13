module

public import GraphMinor.Compute.GM06Alg34SingletonBounds
import Mathlib.Tactic.Ring

/-!
# A uniform space reservation for singleton exhaustion

The region charge bounds the number of cells that can generate a new
region after any later deletion. Multiplying it by the largest boundary
record bounds every later region section. The endpoint, cuff, and
division sections cannot grow. Thus one polynomial reservation covers
every encoded drawing visited by the singleton loop.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Size reservation that cannot increase under singleton deletion. -/
def gm06SingletonSpace (x : GM06DrawingData) : ℕ :=
  x.n + 3 + 2 * x.ends.length +
    gm06SingletonRegionCharge x * (2 + x.n + x.ends.length) +
    x.cuffWords.length + x.divisionWords.length

/-- Deleting one vertex produces an input within the previous space reservation. -/
theorem gm06SingletonData_size_le_space (x : GM06DrawingData) (v : Fin x.n) :
    (x.singletonData v).size ≤ gm06SingletonSpace x := by
  have hn := gm06SingletonData_n_lt x v
  have he := gm06SingletonData_edges_le x v
  have hr := gm06Induced_regionWords_length_le x (x.singletonSurvivors v)
  have hc := gm06Induced_cuffWords_length_le x (x.singletonSurvivors v)
  have hd := gm06Induced_divisionWords_length_le x (x.singletonSurvivors v)
  have hpay := Nat.mul_le_mul_right (x.n + x.ends.length) (show 1 ≤ x.n by omega)
  have hN : x.cellCount ≤ gm06SingletonRegionCharge x := by
    simp only [GM06DrawingData.cellCount, gm06SingletonRegionCharge, Nat.one_mul] at *
    omega
  have hregions := hr.trans (Nat.mul_le_mul_right (2 + x.n + x.ends.length) hN)
  change (x.singletonData v).regionWords.length ≤ _ at hregions
  change (x.singletonData v).cuffWords.length ≤ _ at hc
  change (x.singletonData v).divisionWords.length ≤ _ at hd
  have hw := (x.singletonData v).words_length
  unfold gm06SingletonSpace GM06DrawingData.size
  omega

/-- The reservation itself cannot increase after a singleton deletion. -/
theorem gm06SingletonSpace_le (x : GM06DrawingData) (v : Fin x.n) :
    gm06SingletonSpace (x.singletonData v) ≤ gm06SingletonSpace x := by
  have hn := gm06SingletonData_n_lt x v
  have he := gm06SingletonData_edges_le x v
  have hr := gm06SingletonRegionCharge_le x v
  have hc := gm06Induced_cuffWords_length_le x (x.singletonSurvivors v)
  have hd := gm06Induced_divisionWords_length_le x (x.singletonSurvivors v)
  change (x.singletonData v).cuffWords.length ≤ _ at hc
  change (x.singletonData v).divisionWords.length ≤ _ at hd
  have hprod := Nat.mul_le_mul hr (show
    2 + (x.singletonData v).n + (x.singletonData v).ends.length ≤ 2 + x.n + x.ends.length by omega)
  unfold gm06SingletonSpace
  omega

private theorem space_budget (n : ℕ) :
    5 * n + 3 + (n + n * n) * (n + 2) ≤ 10 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- The uniform reservation is bounded by a cubic in the original input size. -/
theorem gm06SingletonSpace_le_cubic (x : GM06DrawingData) :
    gm06SingletonSpace x ≤ 10 * (x.size + 2) ^ 3 := by
  have hcounts := x.counts_le_size
  have hN := x.cellCount_le_size
  have hnm : x.n + x.ends.length ≤ x.size := by
    simp only [GM06DrawingData.cellCount] at hN
    omega
  have hprod := Nat.mul_le_mul hcounts.1 hnm
  have hcharge : gm06SingletonRegionCharge x ≤ x.size + x.size * x.size := by
    unfold gm06SingletonRegionCharge
    omega
  have hrecord : 2 + x.n + x.ends.length ≤ x.size + 2 := by omega
  have hregions := Nat.mul_le_mul hcharge hrecord
  have hwords := x.words_length
  have hlen := x.words_length_le_size
  exact (show gm06SingletonSpace x ≤
      5 * x.size + 3 + (x.size + x.size * x.size) * (x.size + 2) by
    unfold gm06SingletonSpace
    omega).trans (space_budget x.size)

end GraphMinor.Compute
