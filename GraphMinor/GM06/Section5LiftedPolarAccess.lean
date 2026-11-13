module

public import GraphMinor.GM11.LocalCone
public import Mathlib.Topology.IsLocalHomeomorph
import GraphMinor.GM11.StarChart

/-!
# Access to a lifted vertex in a prescribed component

The Reduction 3 surgery in VI (5.5), page 130, needs a curve from
the old neighbour into the selected lifted region. A polar chart
of the finite base drawing supplies radial curves. A small star
neighbourhood inside a cover chart keeps such a curve in the chosen
sheet. Its positive part is connected and meets the selected
complementary component, so all of that part stays in the component.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u v

/-- A polar vertex chart lifts to an access curve in any incident
complementary component, retaining the specified cover point. -/
theorem exists_access_curve_in_lifted_component_of_polar
    {X : Type u} {S : Type v} [TopologicalSpace X] [TopologicalSpace S] [T2Space S]
    (Γ : Drawing S) (f : X → S) (p : X) (hpV : f p ∈ Γ.V)
    {Φ : C(ClosedUnitDisc, S)} (hpolar : IsPolar Γ (f p) Φ)
    (hlocal : IsLocalHomeomorphOn f {p})
    {r : Set X} (hr : r ∈ componentsIn (f ⁻¹' Γ.Uᶜ)) (hpr : p ∈ closure r) :
    ∃ g : C(unitInterval, X), g 0 = p ∧ ∀ t, 0 < t → g t ∈ r := by
  obtain ⟨η, hpη, hη⟩ := hlocal p rfl
  have hηapp (x) : η x = f x := congrFun hη.symm x
  have hpT : f p ∈ η.target := hηapp p ▸ η.map_source hpη
  obtain ⟨D, hDo, hpD, hDT, _, hstar⟩ := exists_star_nbhd hpolar η.open_target hpT
  have hUo : IsOpen (η.source ∩ η ⁻¹' D) := η.isOpen_inter_preimage hDo
  have hpU : p ∈ η.source ∩ η ⁻¹' D := ⟨hpη, by change η p ∈ D; rw [hηapp]; exact hpD⟩
  obtain ⟨y, hyU, hyr⟩ := mem_closure_iff.mp hpr _ hUo hpU
  have hyoff : f y ∉ Γ.U := by
    obtain ⟨x, _, rfl⟩ := hr
    exact connectedComponentIn_subset _ _ hyr
  have hyD : f y ∈ D := hηapp y ▸ hyU.2
  obtain ⟨a, hay, harad⟩ := hstar _ hyD
  have ha : a ≠ polarCentre := by
    intro he
    have hfp : f y = f p := hay.symm.trans (he ▸ hpolar.centre)
    exact hyoff (hfp ▸ Γ.V_subset_U hpV)
  have hradc : Continuous (fun t : unitInterval => Φ (discScale t a)) :=
    Φ.continuous.comp (continuous_discScale.comp (continuous_id.prodMk continuous_const))
  let g : C(unitInterval, X) :=
    ⟨fun t => η.symm (Φ (discScale t a)),
      η.symm.continuousOn.comp_continuous hradc (fun t => hDT (harad t))⟩
  have hg0 : g 0 = p := by
    change η.symm (Φ (discScale 0 a)) = p
    rw [discScale_zero, hpolar.centre, ← hηapp, η.left_inv hpη]
  have hg1 : g 1 = y := by
    change η.symm (Φ (discScale 1 a)) = y
    rw [discScale_one, hay, ← hηapp, η.left_inv hyU.1]
  have hgoff : ∀ t, 0 < t → f (g t) ∉ Γ.U := by
    intro t ht
    have he : f (g t) = Φ (discScale t a) := by
      change f (η.symm (Φ (discScale t a))) = _
      rw [← hηapp, η.right_inv (hDT (harad t))]
    rw [he]
    obtain ⟨b, hb, hyb, htb⟩ := hpolar.ray a ha t ht
    have hyb' : f y ∈ b := hay ▸ hyb
    rcases hb with (⟨v, hv, rfl⟩ | hbE) | hbR
    · have hyv : f y = v := mem_singleton_iff.mp hyb'
      exact False.elim (hyoff (hyv ▸ Γ.V_subset_U hv))
    · exact False.elim (hyoff ((hbE.2.1 hyb').1))
    · exact region_subset hbR htb
  have hsub : g '' Ioi 0 ⊆ r := by
    obtain ⟨x, _, heq⟩ := hr
    have hycomp : y ∈ connectedComponentIn (f ⁻¹' Γ.Uᶜ) x := heq.symm ▸ hyr
    rw [← heq, connectedComponentIn_eq hycomp]
    exact (isPreconnected_Ioi.image g g.continuous.continuousOn).subset_connectedComponentIn
      ⟨1, zero_lt_one, hg1⟩ (by rintro _ ⟨t, ht, rfl⟩; exact hgoff t ht)
  exact ⟨g, hg0, fun t ht => hsub (mem_image_of_mem g ht)⟩

end GraphMinor.GM06
