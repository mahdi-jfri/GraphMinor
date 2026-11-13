module

public import GraphMinor.GM11.LocalCone

/-!
# Plane coordinates on a polar disc

The seed discs in VI (5.5), page 130, are first constructed in the
complex plane. A polar chart has the Euclidean closed disc as its
domain. Change between these two coordinate spaces and extend the
map outside the unit disc by its centre value. Only continuity and
injectivity on the closed disc are needed to transport seed discs.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11

/-- Express an embedded polar disc as a plane map, retaining its
formula, continuity and injectivity on the closed unit ball. -/
theorem exists_plane_map_of_polar_chart
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ) :
    ∃ F : ℂ → S, ContinuousOn F (closedBall 0 1) ∧
      InjOn F (closedBall 0 1) ∧ F 0 = s ∧
      ∀ (z : ℂ) (hz : z ∈ closedBall 0 1),
        F z = Φ ⟨planeOf z, by
          simpa only [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
            using mem_closedBall_zero_iff.mp hz⟩ := by
  classical
  let j : ℂ → ClosedUnitDisc := fun z =>
    if hz : z ∈ closedBall 0 1 then
      ⟨planeOf z, by
        simpa only [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
          using mem_closedBall_zero_iff.mp hz⟩
    else polarCentre
  have hj (z : ℂ) (hz : z ∈ closedBall 0 1) :
      (j z).1 = planeOf z := by simp only [j, dite_eq_left hz]
  have hjc : ContinuousOn j (closedBall 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let q : closedBall (0 : ℂ) 1 → ClosedUnitDisc := fun z =>
      ⟨planeOf z.1, by
        simpa only [ClosedUnitDisc, mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
          using mem_closedBall_zero_iff.mp z.2⟩
    have hqc : Continuous q := (planeOf.continuous.comp continuous_subtype_val).subtype_mk _
    apply hqc.congr
    intro z
    apply Subtype.ext
    exact (hj z z.2).symm
  refine ⟨fun z => Φ (j z), Φ.continuous.comp_continuousOn hjc, ?_, ?_, ?_⟩
  · intro z hz w hw he
    apply planeOf.injective
    have heq := congrArg Subtype.val (hp.inj he)
    simpa only [hj z hz, hj w hw] using heq
  · have he : j 0 = polarCentre := by
      apply Subtype.ext
      rw [hj 0 (mem_closedBall_self zero_le_one)]
      simp [polarCentre]
    change Φ (j 0) = s
    rw [he, hp.centre]
  · intro z hz
    change Φ (j z) = Φ _
    apply congrArg Φ
    apply Subtype.ext
    exact hj z hz

end GraphMinor.GM06
