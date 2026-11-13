module

public import GraphMinor.GM08.Section18SurroundSides
public import GraphMinor.GM19.CutMap
import GraphMinor.GM07.Section5a
import GraphMinor.GM07.Section8

/-!
# The rest of a schism lies on the far side of the first cut

For a schism of type (iv) (VIII (18.2), page 286) we first cut along the
circle `A₁` that surrounds the cuff `C₁` (`exists_surround_sides`). This
gives a cylinder side `W` around `C₁` and a far side `Wᶜ`. The second circle
`A₂` surrounds another cuff `C₂`, so it is not planar in `Σ + Ĉ₁`, while
every part of `W` is. So the lift of `A₂` lies on the far side
(`preimage_subset_compl_of_surrounds`). A connected set that misses `A₁` and
comes close to `A₂`, such as the inside of the line of an `X₁`-arc, also lifts
to the far side (`preimage_subset_compl_of_closure`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- Off the cut set, a cut map is one to one, so a connected set that misses
the cut set has a connected preimage. -/
theorem isPreconnected_preimage_of_isCutMap {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] [CompactSpace T] [T2Space S] {ψ : T → S} {F B : Set S}
    (hc : GM19.IsCutMap ψ F) (hB : IsPreconnected B) (hBF : Disjoint B F) :
    IsPreconnected (ψ ⁻¹' B) := by
  let f : ψ ⁻¹' B → B := B.restrictPreimage ψ
  have hinj : Function.Injective f := fun x y hxy => Subtype.ext <|
    hc.2.2.1 (show ψ x.1 ∈ Fᶜ from fun h => disjoint_left.mp hBF x.2 h)
      (show ψ y.1 ∈ Fᶜ from fun h => disjoint_left.mp hBF y.2 h) (congrArg Subtype.val hxy)
  have hcl : IsClosedMap f := (hc.1.isClosedMap).restrictPreimage B
  have hsurj : Function.Surjective f := fun b => by
    obtain ⟨x, hx⟩ := hc.2.1 b.1
    exact ⟨⟨x, show ψ x ∈ B from hx ▸ b.2⟩, Subtype.ext hx⟩
  have hBs : PreconnectedSpace B := isPreconnected_iff_preconnectedSpace.mp hB
  have h := (isPreconnected_univ (α := B)).preimage_of_isClosedMap hinj hcl
    (fun b _ => hsurj b)
  rw [preimage_univ] at h
  have : PreconnectedSpace (ψ ⁻¹' B) := ⟨h⟩
  exact isPreconnected_iff_preconnectedSpace.mpr this

variable {S T : Type w} [TopologicalSpace S] [TopologicalSpace T] [ConnectedSpace S]

/-- **The second circle lifts to the far side.** -/
theorem preimage_subset_compl_of_surrounds (hS : IsSurface S) (hT : IsSurface T)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {A₁ C₁ A₂ C₂ : Set S} {ψ : T → S} {W : Set T} (hcut : IsCutting ψ A₁)
    (hs : SurroundSides ψ A₁ C₁ W) (hA₂ : IsOArc A₂) (hdis : Disjoint A₁ A₂)
    (hsur₂ : GM07.SurroundsCuff A₂ C₂) (hC₁ : C₁ ∈ cuffs S) (hC : C₁ ≠ C₂) :
    ψ ⁻¹' A₂ ⊆ Wᶜ := by
  have : CompactSpace T := hT.1
  have : T2Space S := hS.2.1
  obtain ⟨hO, hbij⟩ := isOArc_preimage_of_isCutting hcut hA₂ hdis.symm
  have hcov : ψ ⁻¹' A₂ ⊆ W ∪ Wᶜ := fun z _ => (em (z ∈ W)).elim Or.inl Or.inr
  rcases (GM07.IsOArc.isConnected hO).isPreconnected.subset_or_subset hs.isClopen.isOpen
      hs.isClopen.compl.isOpen disjoint_compl_right hcov with h | h
  · exfalso
    have hp : GM07.IsPlanarInCappedCuff C₁ A₂ := hbij.image_eq ▸ hs.planar _ h
    exact hncyl (GM07.surroundsCuff_and_planarInCappedCuff_imp_cylinder hS hsur₂.1 hC₁
      hC.symm hA₂ hsur₂ hp)
  · exact h

/-- **A connected set near the second circle lifts to the far side.** A
connected set that misses `A₁` and has a limit point on `A₂` lifts to the
side that holds the lift of `A₂`. -/
theorem preimage_subset_compl_of_closure (hS : IsSurface S) (hT : IsSurface T)
    {A₁ C₁ A₂ : Set S} {ψ : T → S} {W : Set T} (hcut : IsCutting ψ A₁)
    (hs : SurroundSides ψ A₁ C₁ W) (hA₂W : ψ ⁻¹' A₂ ⊆ Wᶜ) {B : Set S}
    (hB : IsPreconnected B) (hBA : Disjoint B A₁) (hcl : (closure B ∩ A₂).Nonempty) :
    ψ ⁻¹' B ⊆ Wᶜ := by
  have : CompactSpace T := hT.1
  have : T2Space S := hS.2.1
  have hpre := isPreconnected_preimage_of_isCutMap (GM19.IsCutting.isCutMap hcut) hB hBA
  have hcov : ψ ⁻¹' B ⊆ W ∪ Wᶜ := fun z _ => (em (z ∈ W)).elim Or.inl Or.inr
  rcases hpre.subset_or_subset hs.isClopen.isOpen hs.isClopen.compl.isOpen disjoint_compl_right
      hcov with h | h
  · exfalso
    obtain ⟨a, haB, haA⟩ := hcl
    have himg : ψ '' closure (ψ ⁻¹' B) = closure B := by
      rw [← hcut.1.isClosedMap.closure_image_eq_of_continuous hcut.1,
        image_preimage_eq _ hcut.2.1]
    obtain ⟨z, hz, rfl⟩ := (himg.symm ▸ haB : a ∈ ψ '' closure (ψ ⁻¹' B))
    exact hA₂W haA (closure_minimal h hs.isClopen.isClosed hz)
  · exact h

end GraphMinor.GM08
