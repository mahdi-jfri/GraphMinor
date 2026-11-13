module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.SphereDisc
import GraphMinor.GM08.Section9Coordinates
import GraphMinor.GM08.Section6CoverPlane

/-!
# The unrestricted sphere covering step

For VIII (6.2), page 264, remove the specified exterior point and put the
first curve on the unit circle in plane coordinates. The unrestricted
plane covering theorem supplies a closed disc with boundary in the two
curves. Mapping it back preserves both curves and misses the removed point.
-/

public section

namespace GraphMinor.GM08

open Set Topology Metric Surface

universe u

/-- Closed-disc form of Graph Minors VIII (6.2), without a finiteness
hypothesis on the crossings of the two curves. -/
theorem exists_disc_cover_sphere_unrestricted {S : Type u} [TopologicalSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {F₁ F₂ : Set S} (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    (hcard : (F₁ ∩ F₂).Nontrivial) {z : S} (hz : z ∉ F₁ ∪ F₂) :
    ∃ E : Set S, IsClosedDisc E ∧ z ∉ E ∧ F₁ ∪ F₂ ⊆ E ∧ discBd E ⊆ F₁ ∪ F₂ := by
  have : T2Space S := hS.2.1
  obtain ⟨φ⟩ := hF₁
  obtain ⟨g, hg, hgc, _, hgr⟩ := exists_plane_embedding_for_ring hsph ⟨φ⟩
    (fun hx => hz (Or.inl hx)) (φ (1 : Circle)).2
  obtain ⟨f, hfc, hfg⟩ := exists_inv_of_isEmbedding hg.isEmbedding
  have hgf : ∀ x ∈ range g, g (f x) = x := by
    rintro _ ⟨w, rfl⟩
    rw [hfg]
  have hF₁r : F₁ ⊆ range g := hgc ▸ image_subset_range _ _
  have hF₂r : F₂ ⊆ range g := by
    intro x hx
    rw [hgr]
    intro hxz
    have he : x = z := hxz
    exact hz (Or.inr (he ▸ hx))
  have hF₂p : IsOArc (f '' F₂) := hF₂.image (hfc.mono hF₂r) hg.continuous.continuousOn
    (fun x hx => hgf x (hF₂r hx))
  have hcardp : (discBd (closedBall (0 : ℂ) 1) ∩ f '' F₂).Nontrivial := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hcard
    have hxsp : f x ∈ sphere (0 : ℂ) 1 := by
      obtain ⟨w, hw, he⟩ := hgc.symm ▸ hx.1
      have hfx : f x = w := by rw [← he, hfg]
      exact hfx ▸ hw
    have hysp : f y ∈ sphere (0 : ℂ) 1 := by
      obtain ⟨w, hw, he⟩ := hgc.symm ▸ hy.1
      have hfy : f y = w := by rw [← he, hfg]
      exact hfy ▸ hw
    rw [isClosedDisc_closedBall.2]
    refine ⟨f x, ⟨hxsp, ⟨x, hx.2, rfl⟩⟩, f y, ⟨hysp, ⟨y, hy.2, rfl⟩⟩, ?_⟩
    intro he
    exact hxy ((hgf x (hF₁r hx.1)).symm.trans
      ((congrArg g he).trans (hgf y (hF₁r hy.1))))
  obtain ⟨E, hE, hDE, hFE, hEb⟩ := exists_plane_disc_cover isClosedDisc_closedBall.1 hF₂p hcardp
  rw [isClosedDisc_closedBall.2] at hEb
  obtain ⟨hES, hESb⟩ := hE.image hg.continuous.continuousOn
    (hfc.mono (image_subset_range _ _)) (fun x _ => hfg x)
  have hgfF : g '' (f '' F₂) = F₂ := by
    apply subset_antisymm
    · rintro _ ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      rw [hgf x (hF₂r hx)]
      exact hx
    · intro x hx
      exact ⟨f x, ⟨x, hx, rfl⟩, hgf x (hF₂r hx)⟩
  refine ⟨g '' E, hES, ?_, ?_, ?_⟩
  · rintro ⟨w, hw, he⟩
    have hzr : z ∈ range g := ⟨w, he⟩
    rw [hgr] at hzr
    exact hzr rfl
  · apply union_subset
    · intro x hx
      obtain ⟨w, hw, rfl⟩ := hgc.symm ▸ hx
      exact ⟨w, hDE (sphere_subset_closedBall hw), rfl⟩
    · intro x hx
      exact ⟨f x, hFE ⟨x, hx, rfl⟩, hgf x (hF₂r hx)⟩
  · rw [hESb]
    have htarget : g '' (sphere (0 : ℂ) 1 ∪ f '' F₂) = F₁ ∪ F₂ := by
      rw [image_union, hgc, hgfF]
    exact htarget ▸ image_mono hEb

end GraphMinor.GM08
