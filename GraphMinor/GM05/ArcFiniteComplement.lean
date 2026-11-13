module

public import GraphMinor.Surface.ArcErase
import GraphMinor.Surface.ArcTools

/-!
# An arc minus finitely many points has finitely many connected pieces

For the union drawing in GM V, (8.14), a new arc meets the old graph
in finitely many points. Removing finitely many parameters splits its
interval into finitely many convex sets. Their continuous images give
the finite connected decomposition required by the library graph
construction.
-/

public section
namespace GraphMinor.GM05
open Set Surface
universe u

private theorem finite_convex_cover_sdiff {C : Set ℝ} (hC : Convex ℝ C)
    {F : Set ℝ} (hF : F.Finite) :
    ∃ A : Set (Set ℝ), A.Finite ∧ (∀ B ∈ A,Convex ℝ B) ∧ ⋃₀ A=C\F := by
  induction F,hF using Set.Finite.induction_on with
  | empty => exact ⟨{C},finite_singleton _,by simpa using hC,by simp⟩
  | @insert x F hx hF ih =>
    obtain ⟨A,hA,hconv,hcov⟩ := ih
    let L : Set (Set ℝ) := (fun B ↦ B∩Iio x) '' A
    let R : Set (Set ℝ) := (fun B ↦ B∩Ioi x) '' A
    refine ⟨L∪R,(hA.image _).union (hA.image _),?_,?_⟩
    · intro B hB
      rcases hB with ⟨B,hB,rfl⟩|⟨B,hB,rfl⟩
      · exact (hconv B hB).inter (convex_Iio x)
      · exact (hconv B hB).inter (convex_Ioi x)
    · ext y
      constructor
      · rintro ⟨B,(⟨D,hD,rfl⟩|⟨D,hD,rfl⟩),hy⟩
        · have hh : y∈C\F := hcov ▸ mem_sUnion.mpr ⟨D,hD,hy.1⟩
          exact ⟨hh.1,fun hm ↦ (mem_insert_iff.mp hm).elim (fun he ↦ (ne_of_lt hy.2) he) hh.2⟩
        · have hh : y∈C\F := hcov ▸ mem_sUnion.mpr ⟨D,hD,hy.1⟩
          exact ⟨hh.1,fun hm ↦ (mem_insert_iff.mp hm).elim (fun he ↦ (ne_of_gt hy.2) he) hh.2⟩
      · intro hy
        have hyF : y∉F := fun hm ↦ hy.2 (mem_insert_of_mem x hm)
        have hyCF : y∈C\F := ⟨hy.1,hyF⟩
        rw [← hcov] at hyCF
        obtain ⟨B,hB,hyB⟩ := mem_sUnion.mp hyCF
        have hyx : y≠x := fun he ↦ hy.2 (he.symm ▸ mem_insert x F)
        rcases lt_or_gt_of_ne hyx with hlt|hgt
        · exact ⟨B∩Iio x,.inl ⟨B,hB,rfl⟩,hyB,hlt⟩
        · exact ⟨B∩Ioi x,.inr ⟨B,hB,rfl⟩,hyB,hgt⟩

/-- The finite-point-removal step used to planarize the union of the
drawings in GM V, proof of (8.14), page 113. -/
theorem finConn_arc_sdiff_finite {S : Type u} [TopologicalSpace S]
    {a : unitInterval → S} (ha : IsArcMap a) {F : Set S} (hF : F.Finite) :
    FinConn (range a\F) := by
  let R : Set ℝ := Subtype.val '' (a ⁻¹' F)
  have hR : R.Finite := (hF.preimage ha.2.injOn).image _
  obtain ⟨A,hA,hconv,hcov⟩ := finite_convex_cover_sdiff (convex_Icc (0 : ℝ) 1) hR
  have himage : extI a '' (Icc (0 : ℝ) 1\R)=range a\F := by
    ext x
    constructor
    · rintro ⟨t,⟨ht,htR⟩,rfl⟩
      rw [extI_of_mem a ht]
      exact ⟨⟨⟨t,ht⟩,rfl⟩,fun h ↦ htR ⟨⟨t,ht⟩,h,rfl⟩⟩
    · rintro ⟨⟨t,rfl⟩,htF⟩
      refine ⟨t.val,⟨t.prop,?_⟩,extI_coe a t⟩
      rintro ⟨s,hs,he⟩
      have hst : s=t := Subtype.ext he
      exact htF (hst ▸ hs)
  refine ⟨(fun B ↦ extI a '' B) '' A,hA.image _,?_,?_⟩
  · rintro _ ⟨B,hB,rfl⟩
    exact (hconv B hB).isPreconnected.image _ (continuous_extI ha.1).continuousOn
  · rw [← image_sUnion,hcov,himage]

end GraphMinor.GM05
