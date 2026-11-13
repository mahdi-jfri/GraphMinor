module

public import GraphMinor.Compute.GM06Alg34SingletonData
public import GraphMinor.Compute.GM06Alg34InducedSizeBounds

/-!
# Size control under repeated singleton deletion

Deleting a selected vertex strictly lowers the vertex count. Edges and
the two final list sections cannot grow. New regions are indexed by
old cells. Charging each remaining vertex for one possible increase of
the region count gives a quantity that cannot increase through repeated
singleton deletions, even for finite data without a geometric realization.
-/

@[expose] public section
namespace GraphMinor.Compute

private theorem filter_length_lt {α : Type*} (L : List α) (p : α → Bool)
    (a : α) (ha : a ∈ L) (hp : p a = false) : (L.filter p).length < L.length := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)
    · have ht := ih ha
      cases hb : p b
      · simpa only [List.filter_cons, hb, Bool.false_eq_true, ↓reduceIte, List.length_cons]
          using Nat.lt_succ_of_lt ht
      · simpa only [List.filter_cons, hb, ↓reduceIte, List.length_cons]
          using Nat.succ_lt_succ ht

/-- A singleton payload has strictly fewer vertices than the original input. -/
theorem gm06SingletonData_n_lt (x : GM06DrawingData) (v : Fin x.n) :
    (x.singletonData v).n < x.n := by
  change (x.activeVertices (x.singletonSurvivors v)).length < x.n
  have h := filter_length_lt (List.finRange x.n)
    (fun w => decide (w ∈ x.singletonSurvivors v)) v (List.mem_finRange v)
    (by simp [GM06DrawingData.mem_singletonSurvivors_iff])
  simpa only [GM06DrawingData.activeVertices, List.length_finRange] using h

/-- The singleton payload cannot gain edges. -/
theorem gm06SingletonData_edges_le (x : GM06DrawingData) (v : Fin x.n) :
    (x.singletonData v).ends.length ≤ x.ends.length := by
  rw [GM06DrawingData.singletonData, x.inducedData_ends_length, ← gm06EdgeMask_sum]
  exact gm06EdgeMask_sum_le x _

/-- Each new singleton-payload region is represented by an old cell. -/
theorem gm06SingletonData_regions_le (x : GM06DrawingData) (v : Fin x.n) :
    (x.singletonData v).regions.length ≤ x.n + x.ends.length + x.regions.length := by
  rw [GM06DrawingData.singletonData, x.inducedData_regions_length, ← gm06RootMask_sum]
  simpa only [GM06DrawingData.cellCount, Nat.add_assoc] using gm06RootMask_sum_le x (x.singletonSurvivors v)

/-- Region-count charge sufficient for every later singleton deletion. -/
def gm06SingletonRegionCharge (x : GM06DrawingData) : ℕ :=
  x.regions.length + x.n * (x.n + x.ends.length)

/-- Decreasing the vertex count pays for the maximum possible increase
of regions, so the region charge cannot increase. -/
theorem gm06SingletonRegionCharge_le (x : GM06DrawingData) (v : Fin x.n) :
    gm06SingletonRegionCharge (x.singletonData v) ≤ gm06SingletonRegionCharge x := by
  have hn := gm06SingletonData_n_lt x v
  have he := gm06SingletonData_edges_le x v
  have hr := gm06SingletonData_regions_le x v
  have hmul := Nat.mul_le_mul (show (x.singletonData v).n ≤ x.n - 1 by omega)
    (show (x.singletonData v).n + (x.singletonData v).ends.length ≤ x.n + x.ends.length by omega)
  have hpay : (x.n - 1) * (x.n + x.ends.length) + (x.n + x.ends.length) =
      x.n * (x.n + x.ends.length) := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  unfold gm06SingletonRegionCharge
  omega

/-- A single cuff remains a single cuff after the singleton update. -/
theorem gm06SingletonData_single_cuff (x : GM06DrawingData) (v : Fin x.n)
    {L : List (Fin x.n)} (hL : x.cuffs = [L]) :
    ∃ L', (x.singletonData v).cuffs = [L'] := by
  simp only [GM06DrawingData.singletonData, GM06DrawingData.inducedData, hL,
    List.map_cons, List.map_nil]
  exact ⟨_, rfl⟩

end GraphMinor.Compute
