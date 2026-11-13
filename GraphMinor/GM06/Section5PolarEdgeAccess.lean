module

public import GraphMinor.GM11.LocalCone
import GraphMinor.GM11.PolarChart

/-!
# Pulling a polar edge ray back through an embedding

The local side test in VI (5.7), page 133, reads directions in a
polar chart of the capped drawing. A positive radial segment through
an edge point stays in that edge. If the edge is the image of an
embedded space, the segment pulls back continuously to that space,
including its initial vertex.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u v

/-- Membership in any drawing atom is unchanged at positive radial scales. -/
theorem polar_ray_mem_atom_iff
    {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    {a : Set S} (ha : a ∈ Γ.A) {x : ClosedUnitDisc} (hx : x ≠ polarCentre)
    (c : I) (hc : 0 < c) : Φ x ∈ a ↔ Φ (discScale c x) ∈ a := by
  have hn : IsGammaNice Γ a := ⟨{a}, by simpa using ha, by simp⟩
  obtain ⟨b, hb, hxb, hcb⟩ := hp.ray x hx c hc
  exact ⟨fun h => nice_atom hn hb ⟨Φ x, hxb, h⟩ hcb,
    fun h => nice_atom hn hb ⟨Φ (discScale c x), hcb, h⟩ hxb⟩

/-- An edge ray in a polar chart pulls back to an access curve through
any embedding that contains the edge and its initial vertex. -/
theorem exists_polar_edge_access_of_embedding
    {X : Type u} {S : Type v} [TopologicalSpace X] [TopologicalSpace S] [T2Space S]
    {j : X → S} (hj : IsEmbedding j) {Γ : Drawing S} {s y : X}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ (j s) Φ)
    {e : Set X} (he : j '' e ∈ Γ.E) {x : ClosedUnitDisc}
    (hx : x ≠ polarCentre) (hxy : Φ x = j y) (hy : y ∈ e) :
    ∃ g : C(I, X), g 0 = s ∧ g 1 = y ∧
      (∀ t, 0 < t → g t ∈ e) ∧
      ∀ t, j (g t) = Φ (discScale t x) := by
  classical
  have hrad (t : I) (ht : 0 < t) : Φ (discScale t x) ∈ j '' e := by
    apply (polar_ray_mem_atom_iff hp (Or.inl (Or.inr he)) hx t ht).mp
    exact hxy.symm ▸ mem_image_of_mem j hy
  have hex (t : I) : ∃ z, j z = Φ (discScale t x) := by
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht | ht
    · have ht0 : t = 0 := Subtype.ext ht.symm
      exact ⟨s, by rw [ht0, discScale_zero, hp.centre]⟩
    · obtain ⟨z, _, hz⟩ := hrad t ht
      exact ⟨z, hz⟩
  choose g hg using hex
  have hgc : Continuous g := hj.continuous_iff.mpr (by
    have heq : j ∘ g = fun t : I => Φ (discScale t x) := funext hg
    rw [heq]
    exact Φ.continuous.comp (continuous_discScale.comp
      (continuous_id.prodMk continuous_const)))
  refine ⟨⟨g, hgc⟩, ?_, ?_, ?_, hg⟩
  · apply hj.injective
    change j (g 0) = j s
    rw [hg, discScale_zero, hp.centre]
  · apply hj.injective
    change j (g 1) = j y
    rw [hg, discScale_one, hxy]
  · intro t ht
    obtain ⟨z, hz, hze⟩ := hrad t ht
    have hzg : z = g t := hj.injective (hze.trans (hg t).symm)
    change g t ∈ e
    exact hzg ▸ hz

end GraphMinor.GM06
