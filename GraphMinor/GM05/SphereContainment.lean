module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.SphereDisc
import GraphMinor.Surface.OpenDisc
import GraphMinor.Surface.TriLocal

/-!
# The proper-subset sphere case of the disc-containment claim

Graph Minors V, (8.11), fails for the whole sphere. Any proper subset
of a sphere does fit in an open disc: choose a missed point and use
the punctured sphere. Each circle there bounds one of the two spherical
discs that misses the point, so the library open-disc theorem applies.
This proves the sphere case after excluding the whole-sphere exception.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

/-- A sphere without one point is an open disc. Choose, for every
circle, the spherical disc that does not contain the removed point. -/
theorem punctured_sphere_isOpenDisc {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (hsphere : IsSphere S) (p : S) : IsOpenDisc ({p}ᶜ : Set S) := by
  let : CompactSpace S := hS.1
  let : T2Space S := hS.2.1
  obtain ⟨e⟩ := hsphere
  let : ConnectedSpace S := e.connectedSpace_iff.mpr inferInstance
  let : Infinite S := Infinite.of_injective e.symm e.symm.injective
  have hne : ({p}ᶜ : Set S).Nonempty := by
    obtain ⟨q,hq⟩ := (finite_singleton p).exists_notMem
    exact ⟨q,hq⟩
  have hc : IsConnected ({p}ᶜ : Set S) := ⟨hne,isPreconnected_compl_finite hS (finite_singleton p)⟩
  have H : ∀ F : Set S,F ⊆ {p}ᶜ → IsOArc F →
      ∃ D : Set S,D ⊆ {p}ᶜ ∧ IsClosedDisc D ∧ discBd D=F := by
    intro F hF hO
    obtain ⟨D₁,D₂,-,hD₁,hD₂,hb₁,hb₂,-,hinter,-⟩ := sphere_disc S ⟨e⟩ F hO
    by_cases hp : p ∈ D₁
    · refine ⟨D₂,?_,hD₂,hb₂⟩
      intro x hx hxp
      have he : x=p := hxp
      subst x
      have hpf : p ∈ F := hinter ▸ (⟨hp,hx⟩ : p ∈ D₁ ∩ D₂)
      exact hF hpf rfl
    · refine ⟨D₁,?_,hD₁,hb₁⟩
      intro x hx hxp
      have he : x=p := hxp
      exact hp (he ▸ hx)
  rcases open_disc S {p}ᶜ hS inferInstance hc isOpen_compl_singleton H with ⟨-,he⟩|hdisc
  · have hp : p ∈ ({p}ᶜ : Set S) := he.symm ▸ mem_univ p
    exact (hp rfl).elim
  · exact hdisc

/-- Every proper subset of a sphere is contained in an open disc. This
is the sphere case of the corrected GM V, (8.11). -/
theorem proper_sphere_set_openDisc_container {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) (hsphere : IsSphere S) {r : Set S} (hr : r ≠ univ) :
    ∃ D : Set S,IsOpenDisc D ∧ r ⊆ D := by
  obtain ⟨p,hp⟩ := (Set.ne_univ_iff_exists_notMem r).mp hr
  refine ⟨{p}ᶜ,punctured_sphere_isOpenDisc hS hsphere p,?_⟩
  intro x hx hxp
  have he : x=p := hxp
  exact hp (he ▸ hx)

end GraphMinor.GM05
