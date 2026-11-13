module

public import GraphMinor.Surface.DiscGrow
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# A common retained point for the excursion boundaries

In VIII (6.2), page 264, choose the component outside both curves that
contains the specified point. Unless one disc already contains the other
curve, its closure meets the first boundary away from the second disc.
Such a point is retained by every excursion enlargement that misses the
specified point. This supplies a common place to cut the parameter circle.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u

/-- A component of an open set is closed relative to that open set.
Here local connectivity gives a connected open neighbourhood at a putative
additional closure point. Its intersection with the component identifies
the two components. -/
theorem closure_component_inter_open_subset {X : Type u} [TopologicalSpace X]
    [LocallyConnectedSpace X] {U : Set X} (hU : IsOpen U) {z : X} :
    closure (connectedComponentIn U z) ∩ U ⊆ connectedComponentIn U z := by
  rintro x ⟨hxcl, hxU⟩
  obtain ⟨y, hyx, hyz⟩ := mem_closure_iff.mp hxcl
    (connectedComponentIn U x) hU.connectedComponentIn (mem_connectedComponentIn hxU)
  have heq : connectedComponentIn U x = connectedComponentIn U z :=
    (connectedComponentIn_eq hyx).trans (connectedComponentIn_eq hyz).symm
  exact heq ▸ mem_connectedComponentIn hxU

/-- If the first disc has a point outside the second, the exterior component
has a closure point on the first boundary outside the second disc. This
uses only connectedness of the second complement, rather than a bound on
crossings. -/
theorem exists_exterior_access_point {S : Type u} [TopologicalSpace S] [T2Space S]
    [LocallyConnectedSpace S] (hman : ∀ x : S, IsManifoldPoint x)
    {A B : Set S} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (hBc : IsPreconnected Bᶜ) {z : S} (hzA : z ∉ A) (hzB : z ∉ B)
    (hw : (A \ B).Nonempty) :
    ∃ p ∈ discBd A \ B, p ∈ closure (connectedComponentIn ((A ∪ B)ᶜ) z) := by
  let U := (A ∪ B)ᶜ
  let K := connectedComponentIn U z
  have hU : IsOpen U := (hA.isClosed.union hB.isClosed).isOpen_compl
  have hzU : z ∈ U := fun h => h.elim hzA hzB
  have hzK : z ∈ K := mem_connectedComponentIn hzU
  have hKopen : IsOpen K := hU.connectedComponentIn
  have hex : ∃ p, p ∈ closure K ∧ p ∉ B ∧ p ∉ K := by
    by_contra hn
    have hcover : Bᶜ ⊆ K ∪ (closure K)ᶜ := by
      intro p hpB
      by_cases hpK : p ∈ K
      · exact Or.inl hpK
      · exact Or.inr (fun hpcl => hn ⟨p, hpcl, hpB, hpK⟩)
    have hdis : Disjoint K ((closure K)ᶜ) :=
      Set.disjoint_left.mpr (fun _ hx hxcl => hxcl (subset_closure hx))
    rcases hBc.subset_or_subset hKopen isClosed_closure.isOpen_compl hdis hcover with h | h
    · obtain ⟨w, hwA, hwB⟩ := hw
      exact connectedComponentIn_subset U z (h hwB) (Or.inl hwA)
    · exact h hzB (subset_closure hzK)
  obtain ⟨p, hpcl, hpB, hpK⟩ := hex
  have hpA : p ∈ A := by
    by_contra hpA
    have hpU : p ∈ U := fun h => h.elim hpA hpB
    exact hpK (closure_component_inter_open_subset hU ⟨hpcl, hpU⟩)
  have hpbd : p ∈ discBd A := by
    by_contra hpbd
    obtain ⟨y, hyA, hyK⟩ := mem_closure_iff.mp hpcl
      (discInt A) (hA.isOpen_discInt hman) ⟨hpA, hpbd⟩
    exact connectedComponentIn_subset U z hyK (Or.inl hyA.1)
  exact ⟨p, ⟨hpbd, hpB⟩, hpcl⟩

/-- A point approached from the exterior component is retained by every
excursion enlargement whose boundary stays in the original two curves
and whose disc misses the specified exterior point. -/
theorem exterior_access_point_on_enlarged_boundary
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {A B E : Set S}
    (hE : IsClosedDisc E) (hAE : A ⊆ E) (hbd : discBd E ⊆ A ∪ B)
    {z p : S} (hzU : z ∈ (A ∪ B)ᶜ) (hzE : z ∉ E)
    (hpA : p ∈ A) (hpcl : p ∈ closure (connectedComponentIn ((A ∪ B)ᶜ) z)) :
    p ∈ discBd E := by
  let K := connectedComponentIn ((A ∪ B)ᶜ) z
  have hKbd : Disjoint K (discBd E) := Set.disjoint_left.mpr
    (fun _ hx hb => connectedComponentIn_subset _ z hx (hbd hb))
  have hKE : Disjoint K E := by
    rcases hE.side hman isPreconnected_connectedComponentIn hKbd with hin | hout
    · exact False.elim (hzE (hin (mem_connectedComponentIn hzU)).1)
    · exact hout
  by_contra hpbd
  obtain ⟨y, hyE, hyK⟩ := mem_closure_iff.mp hpcl
    (discInt E) (hE.isOpen_discInt hman) ⟨hAE hpA, hpbd⟩
  exact Set.disjoint_left.mp hKE hyK hyE.1

end GraphMinor.GM08
