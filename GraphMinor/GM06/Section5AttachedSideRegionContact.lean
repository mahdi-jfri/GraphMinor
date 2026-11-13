module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM11.Regions
import GraphMinor.Surface.Cylinder
import GraphMinor.Surface.CutComp

/-!
# Regions meeting a connected discarded side

For the attached-side case of Reduction 2 in VI (5.5), page 130,
a region of the retained drawing meeting a connected discarded
side must be incident with the attachment. Otherwise the region's
intersection with that side is both open and closed there: its
frontier can meet the side only at the attachment. This contradicts
connectedness, since the attachment itself is outside the region.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Every retained region meeting a preconnected discarded side
is incident with its sole attachment vertex. -/
theorem attachment_mem_closure_region_meeting_discarded_side
    {G G₁ G₂ : Drawing ClosedCylinder}
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    {s : ClosedCylinder} (hs₁ : s ∈ G₁.V) (hs₂ : s ∈ G₂.U)
    (hover : G₁.V ∩ G₂.V ⊆ {s}) (hconn : IsPreconnected G₂.U)
    {r : Set ClosedCylinder} (hr : r ∈ G₁.R) (hmeet : (G₂.U ∩ r).Nonempty) :
    s ∈ closure r := by
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  by_contra hscl
  have hro := GraphMinor.GM11.region_isOpen hr
  have hinter : G₁.U ∩ G₂.U ⊆ {s} := (point_sets_of_graph_separation hsep).2 ▸ hover
  have hcover : G₂.U ⊆ r ∪ (closure r)ᶜ := by
    intro x hx₂
    by_cases hxr : x ∈ r
    · exact Or.inl hxr
    · refine Or.inr ?_
      intro hxcl
      have hx₁ : x ∈ G₁.U := (GraphMinor.GM11.closure_region_subset hr hxcl).resolve_left hxr
      have hxs : x = s := hinter ⟨hx₁, hx₂⟩
      exact hscl (hxs ▸ hxcl)
  have hdis : Disjoint r (closure r)ᶜ :=
    disjoint_left.mpr (fun x hx hxc => hxc (subset_closure hx))
  rcases hconn.subset_or_subset hro isClosed_closure.isOpen_compl hdis hcover with h | h
  · exact GraphMinor.GM11.region_subset hr (h hs₂) (G₁.V_subset_U hs₁)
  · obtain ⟨x, hx₂, hxr⟩ := hmeet
    exact h hx₂ (subset_closure hxr)

end GraphMinor.GM06
