module

public import GraphMinor.Surface.ArcErase

/-!
# Finite pieces left after removing interval segments

The finite-graph construction for the homotopic rerouting in XII
(3.1)'s Section 8 reduction uses subarcs of one fixed original arc.
In its interval parameter, deleting a closed segment cuts each connected
piece into at most two pieces. Iterating over finitely many segments
and points therefore leaves finitely many connected pieces. Continuous
images carry this property to the original arc.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Continuous images of finite unions of connected sets are finite
unions of connected sets. -/
theorem finConn_image_of_continuousOn
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    {B : Set S} (hB : FinConn B) {f : S → T} (hf : ContinuousOn f B) : FinConn (f '' B) := by
  obtain ⟨G, hG, hpre, hGB⟩ := hB
  refine ⟨(fun J => f '' J) '' G, hG.image _, ?_, ?_⟩
  · rintro _ ⟨J, hJ, rfl⟩
    apply (hpre J hJ).image
    exact hf.mono ((subset_sUnion_of_mem hJ).trans hGB.le)
  · rw [← image_sUnion, hGB]

/-- Intersecting finitely many connected pieces of the interval with
an order-connected set preserves finite connectedness. -/
theorem finConn_inter_ordConnected_unitInterval
    {B C : Set unitInterval} (hB : FinConn B) (hC : C.OrdConnected) : FinConn (B ∩ C) := by
  have h := hB.inter_arc (a := id) ⟨continuous_id, Function.injective_id⟩
    (by simp) hC
  simpa only [image_id] using h

/-- Deleting one closed parameter segment leaves at most twice as
many connected pieces. -/
theorem finConn_diff_Icc_unitInterval
    {B : Set unitInterval} (hB : FinConn B) (s t : unitInterval) : FinConn (B \ Icc s t) := by
  have heq : B \ Icc s t = (B ∩ Iio s) ∪ (B ∩ Ioi t) := by
    ext x
    simp only [mem_sdiff, mem_Icc, not_and_or, not_le, mem_union, mem_inter_iff, mem_Iio, mem_Ioi]
    exact and_or_left
  rw [heq]
  exact (finConn_inter_ordConnected_unitInterval hB ordConnected_Iio).union
    (finConn_inter_ordConnected_unitInterval hB ordConnected_Ioi)

/-- Deleting a finite set of parameter points leaves finitely many
connected pieces. -/
theorem finConn_diff_finite_unitInterval
    {B K : Set unitInterval} (hB : FinConn B) (hK : K.Finite) : FinConn (B \ K) := by
  induction K, hK using Set.Finite.induction_on generalizing B with
  | empty => simpa only [sdiff_empty] using hB
  | @insert x K hx hK ih =>
    rw [← singleton_union, ← Set.sdiff_sdiff]
    apply ih
    simpa only [Icc_self] using finConn_diff_Icc_unitInterval hB x x

/-- Deleting a finite family of closed parameter segments leaves
finitely many connected pieces. -/
theorem finConn_diff_finite_intervals
    {ι : Type*} (J : Finset ι) (s t : ι → unitInterval) {B : Set unitInterval}
    (hB : FinConn B) : FinConn (B \ ⋃ i ∈ J, Icc (s i) (t i)) := by
  classical
  induction J using Finset.induction_on generalizing B with
  | empty => simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, sdiff_empty] using hB
  | @insert i J hi ih =>
    have heq : (⋃ j ∈ insert i J, Icc (s j) (t j)) = Icc (s i) (t i) ∪ ⋃ j ∈ J, Icc (s j) (t j) := by
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
    rw [heq, ← Set.sdiff_sdiff]
    exact ih (finConn_diff_Icc_unitInterval hB (s i) (t i))

end GraphMinor.GM12
