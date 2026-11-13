module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM19.CircleOrder
import Mathlib.Data.Finset.Sort

/-!
# Aligning finite sets on a cuff

Equal-sized finite sets on the circle can be matched by a homeomorphism
preserving the orientation. Sort their angles and use the proved circle
interpolation theorem. This is the circle step in aligning the boundary
vertices before the application of VII (9.1) in VIII (18.1).
-/

public section

namespace GraphMinor.GM08

open Set Function GraphMinor.Surface

private theorem exists_unit_angle (z : Circle) :
    ∃ a : ℝ, 0 ≤ a ∧ a < 1 ∧ ee a = z := by
  by_cases hz : z = 1
  · exact ⟨0, le_rfl, zero_lt_one, by simp [ee, hz]⟩
  · obtain ⟨s, hs0, hs1, hs⟩ := GM19.exists_angle hz
    refine ⟨s / (2 * Real.pi), (div_pos hs0 (by positivity)).le,
      (div_lt_one (by positivity)).mpr hs1, ?_⟩
    rw [ee, mul_div_cancel₀ _ (by positivity), ← hs]

private theorem ee_injectiveOn_unit : InjOn ee (Ico (0 : ℝ) 1) := by
  intro x hx y hy hxy
  obtain ⟨m, hm⟩ := ee_eq_iff.mp hxy
  have hlo : (-1 : ℝ) < (m : ℝ) := by linarith [hx.1, hx.2, hy.1, hy.2]
  have hhi : (m : ℝ) < 1 := by linarith [hx.1, hx.2, hy.1, hy.2]
  have hlo' : (-1 : ℤ) < m := by exact_mod_cast hlo
  have hhi' : m < (1 : ℤ) := by exact_mod_cast hhi
  have hm0 : m = 0 := by omega
  simpa only [hm0, Int.cast_zero, add_zero] using hm

/-- Equal-sized finite subsets of the circle can be matched preserving its
orientation. This is the cuff alignment step used in VIII (18.1). -/
theorem exists_circle_homeomorph_image_eq {A B : Set Circle} (hA : A.Finite) (hB : B.Finite)
    (hcard : A.ncard = B.ncard) :
    ∃ τ : Circle ≃ₜ Circle, PreservesCircleOrientation τ ∧ τ '' A = B := by
  classical
  choose angle h0 h1 hee using exists_unit_angle
  have hinj : Injective angle := fun x y h => by rw [← hee x, ← hee y, h]
  let LA := (hA.image angle).toFinset
  let LB := (hB.image angle).toFinset
  have hc : LB.card = LA.card := by
    change (hB.image angle).toFinset.card = (hA.image angle).toFinset.card
    rw [← ncard_eq_toFinset_card (angle '' B) (hB.image angle),
      ← ncard_eq_toFinset_card (angle '' A) (hA.image angle),
      ncard_image_of_injective B hinj, ncard_image_of_injective A hinj, hcard]
  let fA := LA.orderEmbOfFin rfl
  let fB := LB.orderEmbOfFin hc
  have hmemA (i : Fin LA.card) : fA i ∈ angle '' A := by
    have h := LA.orderEmbOfFin_mem rfl i
    simpa only [LA, Set.Finite.mem_toFinset] using h
  have hmemB (i : Fin LA.card) : fB i ∈ angle '' B := by
    have h := LB.orderEmbOfFin_mem hc i
    simpa only [LB, Set.Finite.mem_toFinset] using h
  have hbA (i : Fin LA.card) : 0 ≤ fA i ∧ fA i < 1 := by
    obtain ⟨z, _, hz⟩ := hmemA i
    exact hz ▸ ⟨h0 z, h1 z⟩
  have hbB (i : Fin LA.card) : 0 ≤ fB i ∧ fB i < 1 := by
    obtain ⟨z, _, hz⟩ := hmemB i
    exact hz ▸ ⟨h0 z, h1 z⟩
  have hwA (i j : Fin LA.card) : fA i < fA j + 1 := by linarith [(hbA i).2, (hbA j).1]
  have hwB (i j : Fin LA.card) : fB i < fB j + 1 := by linarith [(hbB i).2, (hbB j).1]
  have hti : Injective (fun i => ee (fB i)) := fun i j heq =>
    fB.injective (ee_injectiveOn_unit (hbB i) (hbB j) heq)
  have hcyc : ∀ i j k : Fin LA.card, i ≠ j → j ≠ k → i ≠ k →
      (GM19.CircleCyclic (ee (fB i)) (ee (fB j)) (ee (fB k)) ↔
        GM19.CycOrder (fA i) (fA j) (fA k)) := by
    intro i j k hij hjk hik
    rw [GM19.circleCyclic_ee_iff (hwB i j) (hwB j i) (hwB j k) (hwB k j)
      (hwB i k) (hwB k i) (fB.injective.ne hij) (fB.injective.ne hjk) (fB.injective.ne hik)]
    simp only [GM19.CycOrder, fA.lt_iff_lt, fB.lt_iff_lt]
  obtain ⟨τ, hor, hτ⟩ := GM19.exists_circle_interp fA fA.injective hwA
    (fun i => ee (fB i)) hti hcyc
  have hrA : range (fun i => ee (fA i)) = A := by
    rw [show (fun i => ee (fA i)) = ee ∘ fA from rfl, range_comp,
      Finset.range_orderEmbOfFin]
    simp only [LA, Set.Finite.coe_toFinset]
    rw [← image_comp]
    simp only [comp_def, hee, image_id']
  have hrB : range (fun i => ee (fB i)) = B := by
    rw [show (fun i => ee (fB i)) = ee ∘ fB from rfl, range_comp,
      Finset.range_orderEmbOfFin]
    simp only [LB, Set.Finite.coe_toFinset]
    rw [← image_comp]
    simp only [comp_def, hee, image_id']
  refine ⟨τ, hor, ?_⟩
  rw [← hrA, ← range_comp' τ (fun i => ee (fA i)), show (fun i => τ (ee (fA i))) = (fun i => ee (fB i)) from funext hτ]
  exact hrB

end GraphMinor.GM08
