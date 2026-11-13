module

public import GraphMinor.Surface.DiscGrow
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM06.Section5AttachedRegionCircles
import GraphMinor.GM06.Section5RelativeCompactEnclosure
import GraphMinor.GM11.Regions

/-!
# Compact enclosures retaining their boundary attachment

For Reduction 2 of VI (5.5), page 130, a small seed disc at the
attachment can be enlarged inside a complementary region with that
point added. The punctured retained barrier accumulates there, so
no such disc can put the attachment in its interior. The enlargement
therefore retains a boundary attachment while enclosing the compact
part of the discarded branch away from it.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A disc contained in a complementary region with one barrier
point added has its whole interior in the region, provided the
punctured barrier accumulates at that point. -/
theorem discInt_subset_region_of_attachment_accumulation
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x)
    {T r D : Set S} {s : S} (hrT : r ⊆ Tᶜ)
    (hscl : s ∈ closure (T \ {s}))
    (hD : IsClosedDisc D) (hDZ : D ⊆ r ∪ {s}) : discInt D ⊆ r := by
  have hdis : Disjoint D (T \ {s}) := by
    apply disjoint_left.mpr
    rintro x hxD ⟨hxT, hxne⟩
    rcases hDZ hxD with hxr | hxs
    · exact hrT hxr hxT
    · exact hxne hxs
  have hsnot : s ∉ discInt D := by
    intro hsD
    obtain ⟨x, hxD, hxT⟩ := mem_closure_iff.mp hscl (discInt D) (hD.isOpen_discInt hman) hsD
    exact disjoint_left.mp hdis hxD.1 hxT
  intro x hxD
  rcases hDZ hxD.1 with hxr | hxs
  · exact hxr
  · exact False.elim (hsnot (mem_singleton_iff.mp hxs ▸ hxD))

/-- Enlarge an attached seed disc to enclose a compact part of its
region, retaining the attachment on the boundary and avoiding the
rest of the retained barrier. -/
theorem exists_attached_disc_enclosing_compact_in_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {T r K D : Set S} {s : S} (hTc : IsClosed T)
    (hTp : IsPreconnected (T \ {s})) (hscl : s ∈ closure (T \ {s}))
    (hr : r ∈ componentsIn Tᶜ) (hK : IsCompact K) (hKr : K ⊆ r)
    (hD : IsClosedDisc D) (hDZ : D ⊆ r ∪ {s}) (hsD : s ∈ D) :
    ∃ E : Set S, IsClosedDisc E ∧ D ⊆ E ∧ K ⊆ discInt E ∧
      s ∈ discBd E ∧ E ⊆ r ∪ {s} ∧ E ∩ T ⊆ {s} := by
  have : LocallyConnectedSpace S := GraphMinor.GM11.IsClosedSurface.locallyConnectedSpace hS
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨p, hp, hre⟩ := hr
  have hrT : r ⊆ Tᶜ := hre.symm ▸ connectedComponentIn_subset Tᶜ p
  have hro : IsOpen r := hre.symm ▸ hTc.isOpen_compl.connectedComponentIn
  have hrp : IsPreconnected r := hre.symm ▸ isPreconnected_connectedComponentIn
  have H : ∀ F : Set S, F ⊆ r ∪ {s} → IsOArc F →
      ∃ E : Set S, E ⊆ r ∪ {s} ∧ IsClosedDisc E ∧ discBd E = F := by
    intro F hF hFo
    exact exists_disc_for_circle_in_region_with_attachment hS hsph hTp hscl ⟨p, hp, hre⟩ hF hFo
  have hnonempty : (T \ {s}).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn, closure_empty] at hscl
    exact hscl
  have hns : ¬ (IsSphere S ∧ r ∪ {s} = univ) := by
    rintro ⟨_, hall⟩
    obtain ⟨x, hxT, hxne⟩ := hnonempty
    have hx : x ∈ r ∪ {s} := hall ▸ mem_univ x
    rcases hx with hxr | hxs
    · exact hrT hxr hxT
    · exact hxne hxs
  have hseedmeet : (discInt D ∩ r).Nonempty := by
    obtain ⟨x, hx⟩ := hD.nonempty_discInt
    exact ⟨x, hx, discInt_subset_region_of_attachment_accumulation hman hrT hscl hD hDZ hx⟩
  obtain ⟨E, hEZ, hE, hDE, hKE⟩ := exists_relative_disc_enclosing_compact hS
    (subset_union_left : r ⊆ r ∪ {s}) hro hrp H hns hK hKr hDZ hD hseedmeet
  have hEint : discInt E ⊆ r :=
    discInt_subset_region_of_attachment_accumulation hman hrT hscl hE hEZ
  have hsnotr : s ∉ r := by
    intro hsr
    have hsrcl : s ∈ closure (T \ {s}) := hscl
    obtain ⟨x, hxr, hxT⟩ := mem_closure_iff.mp hsrcl r hro hsr
    exact hrT hxr hxT.1
  have hsbd : s ∈ discBd E := by
    by_contra hnot
    exact hsnotr (hEint ⟨hDE hsD, hnot⟩)
  refine ⟨E, hE, hDE, hKE, hsbd, hEZ, ?_⟩
  rintro x ⟨hxE, hxT⟩
  exact (hEZ hxE).resolve_left (fun hxr => hrT hxr hxT)

end GraphMinor.GM06
