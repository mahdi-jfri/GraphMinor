module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4OpenSubarc

/-!
# From cuff intervals to boundary segments

The final argument of VI (4.2) uses consecutive vertices in a cuff
base. The open arc between them is a component of the whole surface
boundary with its vertices removed: a connected set cannot leave its
cuff or cross either of the two removed end vertices.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

universe u

/-- A component of a cuff minus two vertices is a boundary component
after deleting a larger vertex set, provided its interior avoids that set. -/
theorem cuff_component_mem_boundary_components
    {S : Type u} [TopologicalSpace S] {C A V : Set S} {a b : S}
    (hC : C ∈ cuffs S) (hA : A ∈ componentsIn (C \ {a, b}))
    (ha : a ∈ V) (hb : b ∈ V) (hAV : Disjoint A V) :
    A ∈ componentsIn (bd S \ V) := by
  obtain ⟨c, hc, hcc⟩ := hC
  obtain ⟨x, hx, hxA⟩ := hA
  have hAx : x ∈ A := hxA ▸ mem_connectedComponentIn hx
  have hsub : A ⊆ C \ {a, b} := hxA ▸ connectedComponentIn_subset _ x
  have hpre : IsPreconnected A := hxA ▸ isPreconnected_connectedComponentIn
  have hCBD : C ⊆ bd S := hcc ▸ connectedComponentIn_subset _ c
  have hAF : A ⊆ bd S \ V := fun z hz =>
    ⟨hCBD (hsub hz).1, fun hzV => Set.disjoint_left.mp hAV hz hzV⟩
  refine ⟨x, hAF hAx, Subset.antisymm ?_ ?_⟩
  · have hBpre : IsPreconnected (connectedComponentIn (bd S \ V) x) :=
      isPreconnected_connectedComponentIn
    have hxB := mem_connectedComponentIn (hAF hAx)
    have hBbd : connectedComponentIn (bd S \ V) x ⊆ bd S :=
      (connectedComponentIn_subset _ x).trans sdiff_subset
    have hBC : connectedComponentIn (bd S \ V) x ⊆ C := by
      have hxC : x ∈ connectedComponentIn (bd S) c := hcc.symm ▸ (hsub hAx).1
      rw [← hcc, connectedComponentIn_eq hxC]
      exact hBpre.subset_connectedComponentIn hxB hBbd
    have hBsmall : connectedComponentIn (bd S \ V) x ⊆ C \ {a, b} := by
      intro z hz
      refine ⟨hBC hz, ?_⟩
      have hzV := (connectedComponentIn_subset (bd S \ V) x hz).2
      rintro (rfl | heq)
      · exact hzV ha
      · exact hzV (heq ▸ hb)
    rw [← hxA]
    exact hBpre.subset_connectedComponentIn hxB hBsmall
  · exact hpre.subset_connectedComponentIn hAx hAF

/-- An open arc whose closure is parameterized by a line has the
open-interval homeomorphism required for a segment. -/
theorem nonempty_homeomorph_Ioo_of_component_arc
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A : Set S} {a b : S} (hA : A ∈ componentsIn (C \ {a, b}))
    (f : Curve S) (hf : ParametrizesSet f (closure A) a b) :
    Nonempty (Ioo (0 : ℝ) 1 ≃ₜ A) := by
  let e : unitInterval ≃ₜ range f := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective f hf.1) f.continuous.rangeFactorization
  have hemb : IsEmbedding f := IsEmbedding.subtypeVal.comp e.isEmbedding
  let r : Ioo (0 : ℝ) 1 ≃ₜ Ioo (0 : unitInterval) 1 :=
    { toFun := fun x => ⟨⟨x.1, x.2.1.le, x.2.2.le⟩, x.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hpre := preimage_component_of_parametrizes_closure hA f hf
  have him : f '' Ioo 0 1 = A := by
    rw [← hpre]
    apply image_preimage_eq_of_subset
    rw [hf.2.1]
    exact subset_closure
  exact ⟨r.trans ((hemb.homeomorphImage (Ioo 0 1)).trans (Homeomorph.setCongr him))⟩

/-- An open cuff arc between two removed vertices is a segment of the
whole boundary whenever it contains none of the other removed vertices. -/
theorem isSegmentOf_boundary_of_cuff_component
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A V : Set S} {a b : S} (hC : C ∈ cuffs S)
    (hA : A ∈ componentsIn (C \ {a, b}))
    (ha : a ∈ V) (hb : b ∈ V) (hAV : Disjoint A V)
    (f : Curve S) (hf : ParametrizesSet f (closure A) a b) :
    IsSegmentOf (bd S) V A :=
  ⟨cuff_component_mem_boundary_components hC hA ha hb hAV,
    nonempty_homeomorph_Ioo_of_component_arc hA f hf⟩

end GraphMinor.GM06
