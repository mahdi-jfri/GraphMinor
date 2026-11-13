module

public import GraphMinor.GM08.Section18Theorem182All
import GraphMinor.GM08.Section18PinchedCut
import GraphMinor.GM08.Section18DiscPiece
import GraphMinor.GM08.Section18X2Disc
import GraphMinor.GM08.Section18CutBoundary

/-!
# (18.2) for a circle that touches the boundary once

Let `Z` be a circle that meets `bd(Σ)` only at `p`, and is not near-planar.
The pinched cut (`exists_pinched_cut`) either lowers `g`, or has a piece `D`
that is a closed disc. Its complement `Dᶜ` is connected, and both hold points
over `p`. Every other point of `Z` has one point over it in `D` and one in
`Dᶜ`. There are three points over `p`, so `D` or `Dᶜ` holds exactly one.

* If `D` holds one point over `p`, the cut map is one to one on `D`. So it
  maps `D` onto a closed disc that holds `Z`, and `Z` is planar.
* If `D` holds two points over `p`, then `Z` and the cuff `C` through `p` bound
  the image of `D`, a disc pinched at `p`. Then `Z` is planar after `C` is
  capped. This is `PinchedDiscStatement`, proved in `Section18PinchedDisc`.

Either way `Z` is near-planar, which is false. So the cut lowers `g`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- The disc case of the pinched cut in which the disc holds two points over
the touched point `p`. Then the circle is near-planar: with the cuff through
`p` it bounds a disc pinched at `p`, so it is planar after that cuff is capped.
This is not a result of the paper. It is proved as `pinchedDiscStatement` in
`Section18PinchedDisc`. -/
def PinchedDiscStatement : Prop :=
  ∀ (S T : Type w) [TopologicalSpace S] [TopologicalSpace T] [ConnectedSpace S],
    IsSurface S → IsSurface T →
    ∀ (Z : Set S) (p : S) (ρ : T → S) (D : Set T), IsOArc Z → Z ∩ bd S = {p} →
      GM19.IsCutMap ρ Z → (ρ ⁻¹' {p}).ncard = 3 →
      (∀ z ∈ Z, z ≠ p → (ρ ⁻¹' {z}).ncard = 2) →
      IsClopen D → IsClosedDisc D → ConnectedSpace (Dᶜ : Set T) →
      (D ∩ ρ ⁻¹' {p}).ncard = 2 → (Dᶜ ∩ ρ ⁻¹' {p}).ncard = 1 →
      (∀ z ∈ Z, z ≠ p → (∃ w ∈ D, ρ w = z) ∧ (∃ w ∈ Dᶜ, ρ w = z)) →
      GM07.IsNearPlanar Z

/-- **The disc that holds one point over `p`.** If the disc piece of the
pinched cut holds exactly one point over `p`, the circle is planar. -/
theorem isPlanar_of_pinched_disc {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    (hS : IsSurface S) {Z : Set S} {p : S} {ρ : T → S} {D : Set T}
    (hρ : GM19.IsCutMap ρ Z) (hρ2 : ∀ z ∈ Z, z ≠ p → (ρ ⁻¹' {z}).ncard = 2)
    (hDdisc : IsClosedDisc D) (hD1 : (D ∩ ρ ⁻¹' {p}).ncard = 1)
    (hsides : ∀ z ∈ Z, z ≠ p → (∃ w ∈ D, ρ w = z) ∧ (∃ w ∈ Dᶜ, ρ w = z)) :
    GM11.IsPlanar Z := by
  have : T2Space S := hS.2.1
  have hinj : InjOn ρ D := by
    intro a ha b hb hab
    by_cases hZ : ρ a ∈ Z
    · by_cases hp : ρ a = p
      · obtain ⟨c, hc⟩ := ncard_eq_one.mp hD1
        have ha' : a ∈ D ∩ ρ ⁻¹' {p} := ⟨ha, hp⟩
        have hb' : b ∈ D ∩ ρ ⁻¹' {p} := ⟨hb, show ρ b = p from hab ▸ hp⟩
        rw [hc] at ha' hb'
        exact ha'.trans hb'.symm
      · obtain ⟨w, hw, hwz⟩ := (hsides _ hZ hp).2
        have hs := subsingleton_of_two (hρ.2.2.2.1 _) (hρ2 _ hZ hp) hwz hw
        exact hs ⟨rfl, ha⟩ ⟨show ρ b = ρ a from hab.symm, hb⟩
    · exact hρ.2.2.1 hZ (show ρ b ∈ Zᶜ from hab ▸ hZ) hab
  refine ⟨ρ '' D, (isClosedDisc_image_of_injOn hρ.1 hDdisc hinj).1, fun z hz => ?_⟩
  by_cases hzp : z = p
  · subst hzp
    obtain ⟨w, hwD, hw⟩ := nonempty_of_ncard_ne_zero (by rw [hD1]; norm_num : (D ∩ ρ ⁻¹' {z}).ncard ≠ 0)
    exact ⟨w, hwD, hw⟩
  · obtain ⟨w, hw, hwz⟩ := (hsides z hz hzp).1
    exact ⟨w, hw, hwz⟩

/-- **(18.2) for a circle that touches the boundary once**, from the open case
`PinchedDiscStatement`. -/
theorem circleTouchCutStatement_of_pinchedDisc (hpd : PinchedDiscStatement.{w}) :
    CircleTouchCutStatement.{w} := by
  intro S _ _ hS a b c habc hmodel Z p hZ hnp hZp
  have : T2Space S := hS.2.1
  have hZc : IsClosed Z := hZ.isCompact.isClosed
  obtain ⟨T, tT, ρ, hT, hρ, hρ3, hρ2, hcase⟩ := exists_pinched_cut hS hZ hZp
  refine ⟨T, tT, ρ, isCutAlongSet_of_cutMap hS hT hZc hρ, ?_⟩
  rcases hcase with hlt | ⟨D, hD, hDdisc, hDc, hDp, hDcp, hsides⟩
  · exact hlt
  exfalso
  have hfin : (ρ ⁻¹' {p}).Finite := hρ.2.2.2.1 p
  have hsplit := ncard_inter_add_ncard_sdiff_eq_ncard (ρ ⁻¹' {p}) D hfin
  have e₁ : ρ ⁻¹' {p} ∩ D = D ∩ ρ ⁻¹' {p} := inter_comm _ _
  have e₂ : ρ ⁻¹' {p} \ D = Dᶜ ∩ ρ ⁻¹' {p} := by
    rw [sdiff_eq, inter_comm]
  rw [e₁, e₂, hρ3] at hsplit
  have h1 : 0 < (D ∩ ρ ⁻¹' {p}).ncard := (ncard_pos (hfin.subset inter_subset_right)).mpr hDp
  have h2 : 0 < (Dᶜ ∩ ρ ⁻¹' {p}).ncard :=
    (ncard_pos (hfin.subset inter_subset_right)).mpr hDcp
  by_cases hD1 : (D ∩ ρ ⁻¹' {p}).ncard = 1
  · exact hnp (Or.inl (isPlanar_of_pinched_disc hS hρ hρ2 hDdisc hD1 hsides))
  · exact hnp (hpd S T hS hT Z p ρ D hZ hZp hρ hρ3 hρ2 hD hDdisc hDc (by omega) (by omega)
      hsides)

/-- **VIII (18.2)** from the open case `PinchedDiscStatement`. -/
theorem theorem182Statement_of_pinchedDisc (hpd : PinchedDiscStatement.{w}) :
    Theorem182Statement.{w} :=
  theorem182Statement_of_circleTouch (circleTouchCutStatement_of_pinchedDisc hpd)

end GraphMinor.GM08
