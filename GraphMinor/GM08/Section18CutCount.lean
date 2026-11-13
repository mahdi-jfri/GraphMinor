module

public import GraphMinor.GM08.Section18CutStep
public import GraphMinor.GM08.Section18X1Cut
import GraphMinor.GM08.Section18CircleCut
import GraphMinor.GM08.Section18Theorem182
import GraphMinor.GM12.Section3BarbellCircles
import GraphMinor.GM12.Section3MeetingLoopSchismatic
import GraphMinor.GM12.Section3ThetaCircles
import GraphMinor.GM07.CuffStep
import GraphMinor.GM07.Section5a
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.CutLoop
import GraphMinor.Surface.Cuffs

/-!
# (18.2) with lift counts, from the `X₂` case

`CutCountStatement` asks for a cut along a schism `F` that misses the boundary
and is an `X₁`-, `X₂`- or `X₃`-arc, with a smaller measure and with lift
counts. Such a schism has type (iv) or (v) (VIII, page 286). The `X₁` case is
`hasCountedCut_X1`, and the `X₃` case is `hasCountedCut_X3`. Here we read the
data of the schism: its circles are exactly the circles of the arc, and two of
them that surround different cuffs are different circles. The case of a circle
of type (i) that misses the boundary is the circle cut. The `X₂` case is left
as the hypothesis `X2CutCountStatement` (`cutCountStatement_of_X2`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- The `X₂` case of `CutCountStatement`: two circles that meet at one point,
miss the boundary, and surround different cuffs. -/
def X2CutCountStatement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [ConnectedSpace S], IsSurface S →
    ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2) → 3 ≤ surfaceComplexity S →
    ∀ (A₁ A₂ C₁ C₂ : Set S) (u : S), IsOArc A₁ → IsOArc A₂ → A₁ ∩ A₂ = {u} →
      Disjoint (A₁ ∪ A₂) (bd S) → GM07.SurroundsCuff A₁ C₁ → GM07.SurroundsCuff A₂ C₂ →
      C₁ ≠ C₂ → HasCountedCut S (A₁ ∪ A₂)

variable {S : Type w} [TopologicalSpace S]

/-- A surface with a model of index at least three and two cuffs is not a
cylinder, and its measure is at least three. -/
theorem not_cylinder_and_three_le [ConnectedSpace S] {a b c : ℕ}
    (habc : 3 ≤ 3 * a + 3 * b + c) (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hcuffs : 2 ≤ (cuffs S).ncard) :
    ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2) ∧ 3 ≤ surfaceComplexity S := by
  obtain ⟨e⟩ := hmodel
  have hc : (cuffs S).ncard = c := GM07.ncard_cuffs_of_homeomorph_surfaceModel ⟨e⟩
  refine ⟨fun ⟨e'⟩ => ?_, ?_⟩
  · obtain ⟨h1, h2, -⟩ := (modelCriterion.2 a b c 0 0 2).mp ⟨e.symm.trans e'⟩
    omega
  · rw [surfaceComplexity_eq_connected, connectedSurfaceComplexity_eq ⟨e⟩]
    omega

/-- Two different cuffs make at least two cuffs. -/
theorem two_le_ncard_cuffs (hS : IsSurface S) {C₁ C₂ : Set S} (hC₁ : C₁ ∈ cuffs S)
    (hC₂ : C₂ ∈ cuffs S) (hC : C₁ ≠ C₂) : 2 ≤ (cuffs S).ncard := by
  have h := ncard_le_ncard (show ({C₁, C₂} : Set (Set S)) ⊆ cuffs S by
    rintro C (rfl | rfl)
    · exact hC₁
    · exact hC₂) (cuff_statement S hS).2.1
  rwa [ncard_pair hC] at h

/-- Two circles that surround different cuffs of a surface that is not a
cylinder are different. -/
theorem ne_of_surrounds [ConnectedSpace S] (hS : IsSurface S)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) {A₁ A₂ C₁ C₂ : Set S} (hA₁ : IsOArc A₁)
    (hs₁ : GM07.SurroundsCuff A₁ C₁) (hs₂ : GM07.SurroundsCuff A₂ C₂) (hC : C₁ ≠ C₂) :
    A₁ ≠ A₂ := by
  rintro rfl
  exact hncyl (GM07.surroundsCuff_and_planarInCappedCuff_imp_cylinder hS hs₁.1 hs₂.1 hC hA₁ hs₁
    hs₂.2.1)

/-- A circle in the union of two circles that meet in at most one point is one
of them. -/
theorem eq_or_eq_of_oArc_subset [T2Space S] {B₁ B₂ Z : Set S} (hB₁ : IsOArc B₁) (hB₂ : IsOArc B₂)
    (hZ : IsOArc Z) (h : Z ⊆ B₁ ∨ Z ⊆ B₂) : Z = B₁ ∨ Z = B₂ := by
  obtain ⟨φ₁⟩ := hB₁
  obtain ⟨φ₂⟩ := hB₂
  rcases h with h | h
  · exact Or.inl (oarc_eq φ₁ hZ h)
  · exact Or.inr (oarc_eq φ₂ hZ h)

/-- **(18.2) with lift counts for type (iv)**, from the `X₂` case. -/
theorem hasCountedCut_typeIV (hX2 : X2CutCountStatement.{w}) [ConnectedSpace S]
    (hS : IsSurface S) (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    (h3 : 3 ≤ surfaceComplexity S) {F : Set S} (hX : GM07.IsX1Arc F ∨ GM07.IsX2Arc F)
    (hoff : F ∩ bd S = ∅) {A₁ A₂ C₁ C₂ : Set S} (hA₁ : IsOArc A₁) (hA₂ : IsOArc A₂)
    (hA₁X : A₁ ⊆ F) (hA₂X : A₂ ⊆ F) (hC : C₁ ≠ C₂) (hs₁ : GM07.SurroundsCuff A₁ C₁)
    (hs₂ : GM07.SurroundsCuff A₂ C₂) : HasCountedCut S F := by
  have : T2Space S := hS.2.1
  have hoff' : Disjoint F (bd S) := disjoint_iff_inter_eq_empty.mpr hoff
  have hne := ne_of_surrounds hS hncyl hA₁ hs₁ hs₂ hC
  rcases hX with ⟨B₁, B₂, P, u, v, hB₁, hB₂, hdis, hP, hu, hv, hPB₁, hPB₂, rfl⟩ |
    ⟨B₁, B₂, u, hB₁, hB₂, hcap, rfl⟩
  · have hcl : ∀ Z, IsOArc Z → Z ⊆ B₁ ∪ B₂ ∪ P → Z = B₁ ∨ Z = B₂ := fun Z hZ hZX =>
      eq_or_eq_of_oArc_subset hB₁ hB₂ hZ
        (GM12.oArc_subset_disjoint_circle_or hB₁ hB₂ hdis hP hu hv hPB₁ hPB₂ hZ hZX)
    rcases hcl A₁ hA₁ hA₁X with rfl | rfl <;> rcases hcl A₂ hA₂ hA₂X with rfl | rfl
    · exact absurd rfl hne
    · exact hasCountedCut_X1 hS hncyl h3 hA₁ hA₂ hdis hP hu hv hPB₁ hPB₂ hoff' hs₁ hs₂ hC
    · have h := hasCountedCut_X1 hS hncyl h3 hA₁ hA₂ hdis.symm hP.symm hv hu hPB₂ hPB₁
        (by rwa [union_comm A₁ A₂]) hs₁ hs₂ hC
      rwa [union_comm A₁ A₂] at h
    · exact absurd rfl hne
  · have hcl : ∀ Z, IsOArc Z → Z ⊆ B₁ ∪ B₂ → Z = B₁ ∨ Z = B₂ := fun Z hZ hZX =>
      eq_or_eq_of_oArc_subset hB₁ hB₂ hZ (GM12.oArc_subset_meeting_circle_or hB₁ hB₂ hcap hZ hZX)
    rcases hcl A₁ hA₁ hA₁X with rfl | rfl <;> rcases hcl A₂ hA₂ hA₂X with rfl | rfl
    · exact absurd rfl hne
    · exact hX2 S hS hncyl h3 A₁ A₂ C₁ C₂ u hA₁ hA₂ hcap hoff' hs₁ hs₂ hC
    · have h := hX2 S hS hncyl h3 A₁ A₂ C₁ C₂ u hA₁ hA₂ (by rw [inter_comm]; exact hcap)
        (by rwa [union_comm A₁ A₂]) hs₁ hs₂ hC
      rwa [union_comm A₁ A₂] at h
    · exact absurd rfl hne

/-- **(18.2) with lift counts for type (v).** -/
theorem hasCountedCut_typeV [ConnectedSpace S] (hS : IsSurface S)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (h3 : 3 ≤ surfaceComplexity S)
    {F : Set S} (hX : GM07.IsX3Arc F) (hoff : F ∩ bd S = ∅) {A₁ A₂ A₃ C₁ C₂ C₃ : Set S}
    (hA₁ : IsOArc A₁) (hA₂ : IsOArc A₂) (hA₃ : IsOArc A₃) (hA₁X : A₁ ⊆ F) (hA₂X : A₂ ⊆ F)
    (hA₃X : A₃ ⊆ F) (h12 : C₁ ≠ C₂) (h13 : C₁ ≠ C₃) (h23 : C₂ ≠ C₃)
    (hs₁ : GM07.SurroundsCuff A₁ C₁) (hs₂ : GM07.SurroundsCuff A₂ C₂)
    (hs₃ : GM07.SurroundsCuff A₃ C₃) : HasCountedCut S F := by
  have : T2Space S := hS.2.1
  have hoff' : Disjoint F (bd S) := disjoint_iff_inter_eq_empty.mpr hoff
  have n12 := ne_of_surrounds hS hncyl hA₁ hs₁ hs₂ h12
  have n13 := ne_of_surrounds hS hncyl hA₁ hs₁ hs₃ h13
  have n23 := ne_of_surrounds hS hncyl hA₂ hs₂ hs₃ h23
  obtain ⟨P₁, P₂, P₃, u, v, huv, hP₁, hP₂, hP₃, hi12, hi13, hi23, rfl⟩ := hX
  have hcl := fun Z (hZ : IsOArc Z) (hZX : Z ⊆ P₁ ∪ P₂ ∪ P₃) =>
    GM12.oArc_eq_pair_of_three_branches huv hP₁ hP₂ hP₃ hi12 hi13 hi23 hZ hZX
  have key : (∃ C C', C ≠ C' ∧ GM07.SurroundsCuff (P₁ ∪ P₂) C ∧ GM07.SurroundsCuff (P₁ ∪ P₃) C') ∧
      ¬ IsPlanar (P₁ ∪ P₂) ∧ ¬ IsPlanar (P₁ ∪ P₃) ∧ ¬ IsPlanar (P₂ ∪ P₃) := by
    rcases hcl A₁ hA₁ hA₁X with rfl | rfl | rfl <;> rcases hcl A₂ hA₂ hA₂X with rfl | rfl | rfl <;>
      rcases hcl A₃ hA₃ hA₃X with rfl | rfl | rfl <;>
      first
      | exact absurd rfl n12
      | exact absurd rfl n13
      | exact absurd rfl n23
      | exact ⟨⟨_, _, h12, hs₁, hs₂⟩, hs₁.2.2, hs₂.2.2, hs₃.2.2⟩
      | exact ⟨⟨_, _, h13, hs₁, hs₃⟩, hs₁.2.2, hs₃.2.2, hs₂.2.2⟩
      | exact ⟨⟨_, _, h12.symm, hs₂, hs₁⟩, hs₂.2.2, hs₁.2.2, hs₃.2.2⟩
      | exact ⟨⟨_, _, h23, hs₂, hs₃⟩, hs₂.2.2, hs₃.2.2, hs₁.2.2⟩
      | exact ⟨⟨_, _, h13.symm, hs₃, hs₁⟩, hs₃.2.2, hs₁.2.2, hs₂.2.2⟩
      | exact ⟨⟨_, _, h23.symm, hs₃, hs₂⟩, hs₃.2.2, hs₂.2.2, hs₁.2.2⟩
  obtain ⟨⟨C, C', hCC, hsur, hsur'⟩, np12, np13, np23⟩ := key
  refine hasCountedCut_X3 hS hncyl h3 huv hP₁ hP₂ hP₃ hi12 hi13 hi23 hoff' hsur hsur' hCC
    fun Z hZX hZ => ?_
  rcases hcl Z hZ hZX with rfl | rfl | rfl
  · exact np12
  · exact np13
  · exact np23

/-- A circle of type (i) that misses the boundary has a counted cut. -/
theorem hasCountedCut_oArc [ConnectedSpace S] (hS : IsSurface S) {F : Set S} (hO : IsOArc F)
    (hnp : ¬ GM07.IsNearPlanar F) (hoff : F ∩ bd S = ∅) : HasCountedCut S F := by
  have : T2Space S := hS.2.1
  obtain ⟨T, tT, ψ, hT, hcut, hlt⟩ := exists_cut_complexity_lt_of_non_nearPlanar_oArc hS hO
    (disjoint_iff_inter_eq_empty.mpr hoff) hnp
  refine ⟨T, tT, ψ, isCutAlongSet_of_isCutting hS hT hO.isCompact.isClosed hcut,
    GM19.IsCutting.isCutMap hcut, hlt, fun x hx => by rw [hcut.2.2.2.1 x hx]; norm_num,
    fun B hBF hB => ?_⟩
  rw [IsCutting.ncard_preimage hcut hB, inter_eq_left.mpr hBF]
  omega

/-- **`CutCountStatement` from its `X₂` case.** -/
theorem cutCountStatement_of_X2 (hX2 : X2CutCountStatement.{w}) : CutCountStatement.{w} := by
  intro S _ _ hS a b c habc hmodel F hF hoff hX
  rcases hF with ⟨hO, hnp, -⟩ | ⟨⟨u, v, -, hbd, -⟩, -⟩ | ⟨⟨u, v, -, hbd, -⟩, -⟩ |
      ⟨hX12, -, A₁, A₂, C₁, C₂, hA₁, hA₂, hA₁X, hA₂X, hC₁, hC₂, hC, hs₁, hs₂⟩ |
      ⟨hX3, -, A₁, A₂, A₃, C₁, C₂, C₃, hA₁, hA₂, hA₃, hA₁X, hA₂X, hA₃X, hC₁, hC₂, hC₃, h12, h13,
        h23, hs₁, hs₂, hs₃⟩ | ⟨w, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbd⟩
  · exact hasCountedCut_oArc hS hO hnp hoff
  · exact absurd (hbd.symm.trans hoff) (insert_nonempty _ _).ne_empty
  · exact absurd (hbd.symm.trans hoff) (insert_nonempty _ _).ne_empty
  · obtain ⟨hncyl, h3⟩ := not_cylinder_and_three_le habc hmodel (two_le_ncard_cuffs hS hC₁ hC₂ hC)
    exact hasCountedCut_typeIV hX2 hS hncyl h3 hX12 hoff hA₁ hA₂ hA₁X hA₂X hC hs₁ hs₂
  · obtain ⟨hncyl, h3⟩ := not_cylinder_and_three_le habc hmodel
      (two_le_ncard_cuffs hS hC₁ hC₂ h12)
    exact hasCountedCut_typeV hS hncyl h3 hX3 hoff hA₁ hA₂ hA₃ hA₁X hA₂X hA₃X h12 h13 h23
      hs₁ hs₂ hs₃
  · exact absurd (hbd.symm.trans hoff) (singleton_nonempty _).ne_empty

end GraphMinor.GM08
