module

public import GraphMinor.Surface.DiscGrow
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM11.SphereRegion
import GraphMinor.GM11.PaintingFacts

/-!
# Circles in a complementary region with its attachment added

For the attached enclosures in VI (5.5), page 130, let the retained
barrier stay connected after its attachment is removed. A circle in
a complementary region together with that point bounds a disc on
the side missing the punctured barrier. The barrier accumulates at
the attachment, so the disc cannot contain the attachment in its
interior. Removing it leaves a preconnected set in the same region.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Adding an accessible attachment to a complementary region
retains the bounding-disc condition, when the punctured barrier is
preconnected and accumulates at the attachment. -/
theorem exists_disc_for_circle_in_region_with_attachment
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {T : Set S} {s : S}
    (hTp : IsPreconnected (T \ {s})) (hscl : s ∈ closure (T \ {s}))
    {r F : Set S} (hr : r ∈ componentsIn Tᶜ)
    (hFr : F ⊆ r ∪ {s}) (hF : IsOArc F) :
    ∃ D : Set S, D ⊆ r ∪ {s} ∧ IsClosedDisc D ∧ discBd D = F := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨p, hp, rfl⟩ := hr
  let r := connectedComponentIn Tᶜ p
  have hrT : r ⊆ Tᶜ := connectedComponentIn_subset _ _
  have hdis : Disjoint (T \ {s}) F := by
    apply disjoint_left.mpr
    rintro x ⟨hxT, hxs⟩ hxF
    rcases hFr hxF with hxr | hxs'
    · exact hrT hxr hxT
    · exact hxs hxs'
  obtain ⟨D, hD, hbd, hDT⟩ := GraphMinor.GM11.exists_disc_missing hS hsph hF hTp hdis
  have hsnot : s ∉ discInt D := by
    intro hsD
    obtain ⟨x, hxD, hxT⟩ := mem_closure_iff.mp hscl (discInt D) (hD.isOpen_discInt hman) hsD
    exact disjoint_left.mp hDT hxD.1 hxT
  have hIntsub : discInt D ⊆ D \ {s} := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxs
    exact hsnot (mem_singleton_iff.mp hxs ▸ hx)
  have hDpre : IsPreconnected (D \ {s}) := hD.isPreconnected_discInt.subset_closure
    hIntsub (sdiff_subset.trans hD.subset_closure_discInt)
  have hDoff : D \ {s} ⊆ Tᶜ := by
    rintro x ⟨hxD, hxs⟩ hxT
    exact disjoint_left.mp hDT hxD ⟨hxT, hxs⟩
  obtain ⟨v, hvF, hvne⟩ := (GraphMinor.GM11.infinite_of_isOArc hF).exists_notMem_finite (finite_singleton s)
  have hvD : v ∈ D \ {s} := ⟨discBd_subset D (hbd.symm ▸ hvF), hvne⟩
  have hvr : v ∈ r := (hFr hvF).resolve_right hvne
  have hcomp : connectedComponentIn Tᶜ v = r := (connectedComponentIn_eq hvr).symm
  have hDsub : D \ {s} ⊆ r := by
    have h := hDpre.subset_connectedComponentIn hvD hDoff
    rwa [hcomp] at h
  refine ⟨D, ?_, hD, hbd⟩
  intro x hxD
  by_cases hxs : x = s
  · exact Or.inr hxs
  · exact Or.inl (hDsub ⟨hxD, hxs⟩)

end GraphMinor.GM06
