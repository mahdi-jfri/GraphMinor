module

public import GraphMinor.GM12.Section3IntervalPieces

/-!
# Retained subarcs meet the growing graph in finitely many pieces

The rerouting construction for the Section 8 reduction used by XII
(3.1), page 245, retains finitely many pieces of one injective original
arc. A new retained piece meets the original solid set in finitely many
points. The rest of the growing graph consists of earlier parameter
segments of that same arc. Pulling back to the interval reduces its
complement to deleting finitely many points and closed intervals.
The proved interval lemmas then give the finite connectedness needed
to add the retained piece to a finite graph.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A subarc with finitely many contacts with `F` has finitely many
connected pieces left after deleting `F` and any finite family of
segments of the same injective arc. -/
theorem finConn_subarc_diff_set_and_segments
    {S ι : Type*} [TopologicalSpace S] {p : unitInterval → S} (hp : IsArcMap p)
    {F : Set S} (r s : unitInterval) (hF : ((p '' Icc r s) ∩ F).Finite)
    (J : Finset ι) (a b : ι → unitInterval) :
    FinConn ((p '' Icc r s) \ (F ∪ ⋃ i ∈ J, p '' Icc (a i) (b i))) := by
  let A := Icc r s
  let K := A ∩ p ⁻¹' F
  have hKimage : (p '' K).Finite := hF.subset (by
    rintro x ⟨t, ⟨htA, htF⟩, rfl⟩
    exact ⟨⟨t, htA, rfl⟩, htF⟩)
  have hK : K.Finite := hKimage.of_finite_image hp.2.injOn
  have hA : FinConn A := finConn_of_isPreconnected ordConnected_Icc.isPreconnected
  have hdomain := finConn_diff_finite_intervals J a b (finConn_diff_finite_unitInterval hA hK)
  have heq : p '' ((A \ K) \ ⋃ i ∈ J, Icc (a i) (b i)) =
      (p '' Icc r s) \ (F ∪ ⋃ i ∈ J, p '' Icc (a i) (b i)) := by
    ext x
    constructor
    · rintro ⟨t, ⟨⟨htA, htK⟩, htJ⟩, rfl⟩
      refine ⟨⟨t, htA, rfl⟩, ?_⟩
      rintro (htF | htUnion)
      · exact htK ⟨htA, htF⟩
      · obtain ⟨i, hi, z, hz, he⟩ := mem_iUnion₂.mp htUnion
        have hzt : z = t := hp.2 he
        exact htJ (mem_iUnion₂.mpr ⟨i, hi, hzt ▸ hz⟩)
    · rintro ⟨⟨t, htA, rfl⟩, ht⟩
      refine ⟨t, ⟨⟨htA, ?_⟩, ?_⟩, rfl⟩
      · intro htK
        exact ht (Or.inl htK.2)
      · intro htJ
        obtain ⟨i, hi, hti⟩ := mem_iUnion₂.mp htJ
        exact ht (Or.inr (mem_iUnion₂.mpr ⟨i, hi, t, hti, rfl⟩))
  rw [← heq]
  exact finConn_image_of_continuousOn hdomain hp.1.continuousOn

end GraphMinor.GM12
