module

public import GraphMinor.GM06.Alg511CollarHeight
import GraphMinor.GM11.Regions
import Mathlib.Tactic

/-!
# Retaining the actual region beside a component boundary

For the ordered region-boundary input of VI (5.11), page 134,
a walk around one connected component is first obtained in that
component's drawing. The other components form a disjoint closed
set. Shorten its boundary collar to miss that set. If the original
region approaches this component, it meets the shortened collar.
The collar is connected and misses the full drawing, so it lies in
the original region. Its whole bottom boundary is therefore part
of that region's frontier.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.GM11 GraphMinor.Surface unitInterval
universe u

/-- A component's region collar incident with an actual region stays
beside that same region after the other closed components are restored. -/
theorem alg511_component_region_collar_height
    {S : Type u} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {G D : Drawing S} {Q r R : Set S}
    (hU : G.U = D.U ∪ Q) (hQ : IsClosed Q) (hDQ : Disjoint D.U Q)
    (hr : r ∈ G.R) (hR : R ∈ D.R) (hrR : r ⊆ R)
    {x : S} (hxD : x ∈ D.U) (hxr : x ∈ closure r)
    (h : C(Circle × I, S)) (hinj : InjOn h {p | 0 < p.2})
    (hpos : ∀ p : Circle × I, 0 < p.2 → h p ∈ R)
    (hbot : range (fun z : Circle => h (z, 0)) = frontier R)
    (hop : IsOpen (Rᶜ ∪ h '' {p | p.2 < 1})) :
    ∃ ε : I, 0 < ε ∧ (∀ z t, 0 < t → t ≤ ε → h (z, t) ∈ r) ∧
      frontier R ⊆ frontier r := by
  have hRo : IsOpen R := region_isOpen hR
  have hro : IsOpen r := region_isOpen hr
  have hbotD (z : Circle) : h (z, 0) ∈ D.U := by
    have hp : h (z, 0) ∈ frontier R := hbot ▸ mem_range_self z
    have hpR : h (z, 0) ∉ R := by simpa only [hRo.interior_eq] using hp.2
    exact (closure_region_subset hR hp.1).resolve_left hpR
  have hbotR (z : Circle) : h (z, 0) ∈ Rᶜ :=
    fun hp => region_subset hR hp (hbotD z)
  obtain ⟨ε, hε, havoid⟩ := alg511_exists_collar_height_avoiding_closed h hQ
    (fun z hzQ => disjoint_left.mp hDQ (hbotD z) hzQ)
  let A := h '' ((univ : Set Circle) ×ˢ Ioc (0 : I) ε)
  have hAconn : IsPreconnected A :=
    ((isPreconnected_univ : IsPreconnected (univ : Set Circle)).prod isPreconnected_Ioc).image
      h h.continuous.continuousOn
  have hAoff : Disjoint A G.U := by
    apply disjoint_left.mpr
    rintro _ ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩ hpU
    rw [hU] at hpU
    rcases hpU with hpD | hpQ
    · exact region_subset hR (hpos (z, t) ht.1) hpD
    · exact havoid z t ht.2 hpQ
  have hshort : IsOpen (Rᶜ ∪ h '' {p | p.2 < ε}) :=
    isOpen_shrink hRo.isClosed_compl h hinj
      (fun p hp => by simpa only [mem_compl_iff, not_not] using hpos p hp) hbotR hop hε
  have hxR : x ∉ R := fun hx => region_subset hR hx hxD
  obtain ⟨y, hy, hyr⟩ := mem_closure_iff.mp hxr
    (Rᶜ ∪ h '' {p | p.2 < ε}) hshort (Or.inl hxR)
  have hyImage : y ∈ h '' {p | p.2 < ε} := hy.resolve_left (fun hyR => hyR (hrR hyr))
  obtain ⟨⟨z, t⟩, ht, hzy⟩ := hyImage
  have htpos : 0 < t := unitInterval.pos_iff_ne_zero.mpr (by
    intro htzero
    have hyD : y ∈ D.U := by rw [← hzy, htzero]; exact hbotD z
    exact region_subset hr hyr (hU.symm ▸ Or.inl hyD))
  have hyA : y ∈ A := ⟨(z, t), ⟨mem_univ _, htpos, ht.le⟩, hzy⟩
  have hAr : A ⊆ r := subset_region hr hAconn hAoff hyA hyr
  have hbottomClosure (z : Circle) : h (z, 0) ∈ closure r := by
    have hz : (0 : I) ∈ closure (Ioc (0 : I) ε) := by
      rw [closure_Ioc hε.ne]
      exact ⟨le_rfl, hε.le⟩
    exact map_mem_closure (f := fun t : I => h (z, t))
      (h.continuous.comp (continuous_const.prodMk continuous_id)) hz
      (fun t ht => hAr ⟨(z, t), ⟨mem_univ _, ht⟩, rfl⟩)
  refine ⟨ε, hε, ?_, ?_⟩
  · intro z t ht hte
    exact hAr ⟨(z, t), ⟨mem_univ _, ht, hte⟩, rfl⟩
  intro p hp
  obtain ⟨z, rfl⟩ := (show p ∈ range (fun z : Circle => h (z, 0)) from hbot.symm ▸ hp)
  refine ⟨hbottomClosure z, ?_⟩
  rw [hro.interior_eq]
  exact fun hp => region_subset hr hp (hU.symm ▸ Or.inl (hbotD z))

/-- A component's region frontier remains on the same actual region
when the other disjoint closed drawing components are restored. -/
theorem alg511_component_region_frontier_subset
    {S : Type u} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S]
    {G D : Drawing S} {Q r R : Set S}
    (hU : G.U = D.U ∪ Q) (hQ : IsClosed Q) (hDQ : Disjoint D.U Q)
    (hr : r ∈ G.R) (hR : R ∈ D.R) (hrR : r ⊆ R)
    {x : S} (hxD : x ∈ D.U) (hxr : x ∈ closure r)
    (h : C(Circle × I, S)) (hinj : InjOn h {p | 0 < p.2})
    (hpos : ∀ p : Circle × I, 0 < p.2 → h p ∈ R)
    (hbot : range (fun z : Circle => h (z, 0)) = frontier R)
    (hop : IsOpen (Rᶜ ∪ h '' {p | p.2 < 1})) :
    frontier R ⊆ frontier r := by
  obtain ⟨_, _, _, hfront⟩ := alg511_component_region_collar_height hU hQ hDQ hr hR hrR
    hxD hxr h hinj hpos hbot hop
  exact hfront

end GraphMinor.GM06
