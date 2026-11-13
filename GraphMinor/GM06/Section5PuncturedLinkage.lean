module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5Red
import GraphMinor.Surface.Fan
import GraphMinor.GM11.Defs

/-!
# The linkage and cuffs after deleting an initial vertex

In the region argument of VI (5.1), page 129, the linkage together
with both cuffs stays connected after one initial vertex is removed.
Every remaining path joins the outer cuff, and a second path joins
the punctured inner cuff to that connected set.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

private theorem connected_of_oArc {C : Set ClosedCylinder} (hC : IsOArc C) :
    IsConnected C := by
  obtain ⟨e⟩ := hC
  exact isConnected_iff_connectedSpace.mpr (e.surjective.connectedSpace e.continuous)

/-- With at least two linkage paths, deleting one initial vertex from
both cuffs and the linkage leaves a connected set, as used in the
region argument of VI (5.1). -/
theorem isConnected_punctured_linkage_and_cuffs
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (i : Fin k) :
    IsConnected ((bd ClosedCylinder ∪ ⋃ j, (L.pathDrawing j).U) \
      {cylinderM1Point k i}) := by
  let s := cylinderM1Point k i
  have hs2 : s ∉ cylinderCuff2 := by
    intro h
    change (1 : ℝ) = 2 at h
    norm_num at h
  have ht (j : Fin k) : L.curve j 1 ∈ cylinderCuff2 := by
    obtain ⟨n, hn⟩ := L.curve_one_mem j
    rw [← hn]
    rfl
  have hstart (j : Fin k) : cylinderM1Point k j ∈ (L.pathDrawing j).U := by
    rw [← (L.curve_parametrizes j).2.1]
    exact ⟨0, (L.curve_parametrizes j).2.2.1⟩
  have hend (j : Fin k) : L.curve j 1 ∈ (L.pathDrawing j).U \
      {s} := by
    refine ⟨?_, ?_⟩
    · rw [← (L.curve_parametrizes j).2.1]
      exact ⟨1, rfl⟩
    · intro h
      exact hs2 (mem_singleton_iff.mp h ▸ ht j)
  have hp (j : Fin k) : IsConnected ((L.pathDrawing j).U \ {s}) := by
    refine ⟨⟨L.curve j 1, hend j⟩, ?_⟩
    by_cases hji : j = i
    · subst j
      obtain ⟨f, hf⟩ := (L.isPath i).2
      let e : unitInterval ≃ₜ range f := Continuous.homeoOfEquivCompactToT2
        (f := Equiv.ofInjective f hf.1) f.continuous.rangeFactorization
      have hl : IsLineWithEnds (L.pathDrawing i).U s (L.curve i 1) :=
        ⟨e.trans (Homeomorph.setCongr hf.2.1), hf.2.2.1, hf.2.2.2⟩
      exact hl.isPreconnected_diff_left
    · have hs : s ∉ (L.pathDrawing j).U := by
        intro h
        exact Set.disjoint_left.mp (L.pairwise_disjoint hji) h (hstart i)
      rw [sdiff_singleton_eq_self hs, ← (L.curve_parametrizes j).2.1]
      exact (isConnected_range (L.curve j).continuous).isPreconnected
  let D := cylinderCuff2 ∪ ⋃ j, ((L.pathDrawing j).U \ {s})
  have hC2 := connected_of_oArc isOArc_cylinderCuff2
  obtain ⟨a, ha⟩ := hC2.nonempty
  have hD : IsConnected D := by
    refine ⟨⟨a, Or.inl ha⟩, ?_⟩
    apply isPreconnected_of_forall a
    intro x hx
    rcases hx with hx | hx
    · exact ⟨cylinderCuff2, subset_union_left, ha, hx, hC2.isPreconnected⟩
    · obtain ⟨j, hx⟩ := mem_iUnion.mp hx
      have hj := hC2.union ⟨L.curve j 1, ht j, hend j⟩ (hp j)
      exact ⟨cylinderCuff2 ∪ ((L.pathDrawing j).U \ {s}),
        union_subset_union_right _ (fun y hy => mem_iUnion.mpr ⟨j, hy⟩), Or.inl ha, Or.inr hx,
        hj.isPreconnected⟩
  have hC1 : IsConnected (cylinderCuff1 \ {s}) :=
    (isPathConnected_oArc_diff isOArc_cylinderCuff1 (show s ∈ cylinderCuff1 from rfl)).isConnected
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j, hji⟩ := exists_ne i
  have hsj : cylinderM1Point k j ≠ s :=
    (cylinderM1Point_injective (lt_trans Nat.zero_lt_one hk)).ne hji
  have hjoin : (D ∩ (cylinderCuff1 \ {s})).Nonempty :=
    ⟨cylinderM1Point k j, Or.inr (mem_iUnion.mpr ⟨j, hstart j, hsj⟩), rfl, hsj⟩
  have hconn := hD.union hjoin hC1
  convert hconn using 1
  rw [bd_closedCylinder]
  ext x
  constructor
  · rintro ⟨(hx | hx) | hx, hn⟩
    · exact Or.inr ⟨hx, hn⟩
    · exact Or.inl (Or.inl hx)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact Or.inl (Or.inr (mem_iUnion.mpr ⟨j, hj, hn⟩))
  · rintro ((hx | hx) | hx)
    · exact ⟨Or.inl (Or.inr hx), fun he => hs2 (by
        change cylinderM1Point k i ∈ cylinderCuff2
        rw [← mem_singleton_iff.mp he]
        exact hx)⟩
    · obtain ⟨j, hj, hn⟩ := mem_iUnion.mp hx
      exact ⟨Or.inr (mem_iUnion.mpr ⟨j, hj⟩), hn⟩
    · exact ⟨Or.inl (Or.inl hx.1), hx.2⟩

end GraphMinor.GM06
