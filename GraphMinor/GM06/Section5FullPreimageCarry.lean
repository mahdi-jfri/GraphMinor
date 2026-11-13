module

public import GraphMinor.GM06.Section5CutLinks
public import GraphMinor.GM07.Matched
import GraphMinor.GM11.Walks

/-!
# Carrying a cut subdrawing through projection

For a closed continuous quotient, full lifted edges project to
original edges with the correct ends. If projection is injective
on a subdrawing, these edge correspondences give an actual carrying
map on its vertices. This transports the first-contact path from
the cut disc to the original cylinder in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u v

/-- A subdrawing with full lifted edges and injective projection is
carried into the original drawing by that projection. -/
theorem isCarry_of_full_preimage_edges
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] {f : X → Y} (hc : Continuous f) (hclosed : IsClosedMap f)
    (hsurj : Function.Surjective f) {F Q : Drawing X} {G : Drawing Y}
    (hFV : F.V = f ⁻¹' G.V) (hQF : Q.IsSubdrawing F) (hinj : InjOn f Q.U)
    (hEdges : ∀ ec ∈ Q.E, ∃ e ∈ G.E, ec = f ⁻¹' e) : GM07.IsCarry Q G f Q.V := by
  refine ⟨hc.continuousOn, hinj, ?_, ?_⟩
  · intro x hx
    refine ⟨hx, ?_⟩
    have hxF := hQF.1 hx
    rw [hFV] at hxF
    exact hxF
  · intro ec hec x y hcap hx
    have hy : y ∈ Q.V :=
      (show y ∈ closure ec ∩ Q.V from hcap.symm ▸ mem_insert_of_mem x rfl).2
    have hlQ : Q.toGraph.IsLink ec x y := ⟨hec, hx, hy, hcap⟩
    have hlF := (hQF.isLink_iff hec).mp hlQ
    obtain ⟨e, he, heq⟩ := hEdges ec hec
    have hlG := isLink_of_full_preimage_edge hc hclosed hsurj hFV he heq hlF
    have him : f '' ec = e := by rw [heq, image_preimage_eq _ hsurj]
    refine ⟨hy, ?_, ?_, ?_⟩
    · rw [him]
      exact he
    · rw [him]
      exact hlG.2.2.2
    · exact image_closure_subset_closure_image hc

end GraphMinor.GM06
