module

public import GraphMinor.Compute.GM06Alg34SingletonSpace
public import GraphMinor.Compute.GM06Alg34InteriorComponent

/-!
# Uniform space control for component deletion

The same region charge used for singleton deletion applies whenever
an induced payload loses at least one vertex. Edges and list sections
cannot grow, and each new region comes from an old cell. Consequently
the charge and space reservation remain valid when a whole component
is deleted at once.
-/

public section
namespace GraphMinor.Compute

/-- Any strict vertex deletion has non-increasing region charge. -/
theorem gm06Induced_regionCharge_le (x : GM06DrawingData) (vs : List (Fin x.n))
    (hdrop : (x.inducedData vs).n < x.n) :
    gm06SingletonRegionCharge (x.inducedData vs) ≤ gm06SingletonRegionCharge x := by
  have he : (x.inducedData vs).ends.length ≤ x.ends.length := by
    rw [x.inducedData_ends_length, ← gm06EdgeMask_sum]; exact gm06EdgeMask_sum_le x vs
  have hr : (x.inducedData vs).regions.length ≤ x.cellCount := by
    rw [x.inducedData_regions_length, ← gm06RootMask_sum]; exact gm06RootMask_sum_le x vs
  have hmul := Nat.mul_le_mul (show (x.inducedData vs).n ≤ x.n - 1 by omega)
    (show (x.inducedData vs).n + (x.inducedData vs).ends.length ≤ x.n + x.ends.length by omega)
  have hpay : (x.n - 1) * (x.n + x.ends.length) + (x.n + x.ends.length) =
      x.n * (x.n + x.ends.length) := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  simp only [gm06SingletonRegionCharge, GM06DrawingData.cellCount] at *
  omega

/-- A strict induced vertex deletion fits the previous uniform reservation. -/
theorem gm06Induced_size_le_space (x : GM06DrawingData) (vs : List (Fin x.n))
    (hdrop : (x.inducedData vs).n < x.n) :
    (x.inducedData vs).size ≤ gm06SingletonSpace x := by
  have he : (x.inducedData vs).ends.length ≤ x.ends.length := by
    rw [x.inducedData_ends_length, ← gm06EdgeMask_sum]; exact gm06EdgeMask_sum_le x vs
  have hr := gm06Induced_regionWords_length_le x vs
  have hc := gm06Induced_cuffWords_length_le x vs
  have hd := gm06Induced_divisionWords_length_le x vs
  have hpay := Nat.mul_le_mul_right (x.n + x.ends.length) (show 1 ≤ x.n by omega)
  have hN : x.cellCount ≤ gm06SingletonRegionCharge x := by
    simp only [GM06DrawingData.cellCount, gm06SingletonRegionCharge, Nat.one_mul] at *
    omega
  have hregions := hr.trans (Nat.mul_le_mul_right (2 + x.n + x.ends.length) hN)
  have hw := (x.inducedData vs).words_length
  unfold gm06SingletonSpace GM06DrawingData.size
  omega

/-- The uniform reservation cannot increase after any strict induced deletion. -/
theorem gm06Induced_space_le (x : GM06DrawingData) (vs : List (Fin x.n))
    (hdrop : (x.inducedData vs).n < x.n) :
    gm06SingletonSpace (x.inducedData vs) ≤ gm06SingletonSpace x := by
  have he : (x.inducedData vs).ends.length ≤ x.ends.length := by
    rw [x.inducedData_ends_length, ← gm06EdgeMask_sum]; exact gm06EdgeMask_sum_le x vs
  have hr := gm06Induced_regionCharge_le x vs hdrop
  have hc := gm06Induced_cuffWords_length_le x vs
  have hd := gm06Induced_divisionWords_length_le x vs
  have hprod := Nat.mul_le_mul hr (show
    2 + (x.inducedData vs).n + (x.inducedData vs).ends.length ≤ 2 + x.n + x.ends.length by omega)
  unfold gm06SingletonSpace
  omega

/-- Deleting a component strictly reduces the supplied vertex count,
since its source belongs to that component. -/
theorem gm06InteriorComponentData_n_lt (x : GM06DrawingData) (a : Fin x.n) :
    (x.interiorComponentData a).n < x.n := by
  let vs := x.interiorComponentSurvivors a
  have hle : (x.activeVertices vs).length ≤ (List.finRange x.n).length := List.length_filter_le _ _
  have hne : (x.activeVertices vs).length ≠ (List.finRange x.n).length := by
    intro heq
    have hh := (List.length_filter_eq_length_iff.mp heq) a (List.mem_finRange a)
    have hself : x.vertexGraph.Reachable a a := .refl a
    have hnot : ¬ x.vertexGraph.Reachable a a := by
      simpa only [vs, decide_eq_true_eq, x.mem_interiorComponentSurvivors_iff] using hh
    exact hnot hself
  change (x.activeVertices vs).length < x.n
  simpa only [List.length_finRange] using lt_of_le_of_ne hle hne

/-- A single cuff remains a single cuff under component deletion. -/
theorem gm06InteriorComponentData_single_cuff (x : GM06DrawingData) (a : Fin x.n)
    {L : List (Fin x.n)} (hL : x.cuffs = [L]) :
    ∃ L', (x.interiorComponentData a).cuffs = [L'] := by
  simp only [GM06DrawingData.interiorComponentData, GM06DrawingData.inducedData, hL,
    List.map_cons, List.map_nil]
  exact ⟨_, rfl⟩

end GraphMinor.Compute
