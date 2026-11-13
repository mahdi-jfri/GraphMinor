module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.SphereDisc
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM08.Section6SharedArc

/-!
# The common-exterior enclosure comparison in the plane

The lens comparison for VIII (6.2), page 264, is applied on the model
sphere. This file transports plane discs and their shared boundary arc by
stereographic inclusion, applies that comparison, and pulls inclusion back
to the plane. The chosen exterior is preserved throughout.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

local notation "𝕀" => unitInterval

private theorem two_arcs_sph {a b : 𝕀 → ℂ} (hab : IsTwoArcs a b) :
    IsTwoArcs (sph ∘ a) (sph ∘ b) := by
  have hc := isOpenEmbedding_sph.continuous
  have hi := isOpenEmbedding_sph.injective
  refine ⟨⟨hc.comp hab.1.1, hi.comp hab.1.2⟩,
    ⟨hc.comp hab.2.1, hi.comp hab.2.2⟩,
    congrArg sph hab.3, congrArg sph hab.4, ?_⟩
  intro s t he
  exact hab.5 s t (hi he)

/-- The plane form of the retained-arc enclosure step in VIII (6.2).
The common exterior determines the same interior side on the shared arc. -/
theorem plane_disc_subset_of_shared_arc_and_common_exterior
    {D E : Set ℂ} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    {q f g : 𝕀 → ℂ} (hqf : IsTwoArcs q f) (hqg : IsTwoArcs q g)
    (hDb : discBd D = range q ∪ range f) (hEb : discBd E = range q ∪ range g)
    {p : ℂ} (hp : p ∈ q '' Ioo (0 : 𝕀) 1)
    (hpcl : p ∈ closure ((D ∪ E)ᶜ))
    (hdis : Disjoint (discInt D) (discBd E)) : D ⊆ E := by
  have hc := isOpenEmbedding_sph.continuous
  have hi := isOpenEmbedding_sph.injective
  obtain ⟨s', hs'c, hs'l⟩ := exists_inv_of_isEmbedding isOpenEmbedding_sph.isEmbedding
  obtain ⟨hDS, hDSb⟩ := hD.image hc.continuousOn
    (hs'c.mono (image_subset_range _ _)) (fun _ _ => hs'l _)
  obtain ⟨hES, hESb⟩ := hE.image hc.continuousOn
    (hs'c.mono (image_subset_range _ _)) (fun _ _ => hs'l _)
  have hDSint : discInt (sph '' D) = sph '' discInt D := by
    rw [discInt, hDSb, ← image_sdiff hi]
    rfl
  have hDbS : discBd (sph '' D) = range (sph ∘ q) ∪ range (sph ∘ f) := by
    rw [hDSb, hDb, image_union, ← range_comp, ← range_comp]
  have hEbS : discBd (sph '' E) = range (sph ∘ q) ∪ range (sph ∘ g) := by
    rw [hESb, hEb, image_union, ← range_comp, ← range_comp]
  have hpS : sph p ∈ (sph ∘ q) '' Ioo (0 : 𝕀) 1 := by
    obtain ⟨r, hr, he⟩ := hp
    exact ⟨r, hr, congrArg sph he⟩
  have hpScl : sph p ∈ closure ((sph '' D ∪ sph '' E)ᶜ) := by
    apply closure_mono (show sph '' (D ∪ E)ᶜ ⊆ (sph '' D ∪ sph '' E)ᶜ from ?_)
      (mem_closure_image hc.continuousAt hpcl)
    rintro _ ⟨x, hx, rfl⟩ (⟨y, hy, he⟩ | ⟨y, hy, he⟩)
    · exact hx (Or.inl (hi he ▸ hy))
    · exact hx (Or.inr (hi he ▸ hy))
  have hdisS : Disjoint (discInt (sph '' D)) (discBd (sph '' E)) := by
    rw [hDSint, hESb]
    apply Set.disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    exact Set.disjoint_left.mp hdis hx (hi he ▸ hy)
  have hSphere : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := (GM11.IsSphere.isClosedSurface hSphere).1
  have hsub := disc_subset_of_shared_arc_and_common_exterior hS hDS hES
    (two_arcs_sph hqf) (two_arcs_sph hqg) hDbS hEbS hpS hpScl hdisS
  intro x hx
  obtain ⟨y, hy, he⟩ := hsub ⟨x, hx, rfl⟩
  exact hi he ▸ hy

end GraphMinor.GM08
