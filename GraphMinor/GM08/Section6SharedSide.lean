module

public import GraphMinor.Surface.DiscGrow

/-!
# Choosing the same side along a shared boundary arc

The glued boundary in VIII (6.2), page 264, must enclose the old disc.
A lens about their common retained arc has two connected sides. If a
point of that arc is approached from outside both discs, one lens side
is outside both, so the other side meets both interiors. Separation then
puts the old disc inside the new one.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u

private theorem inside_point_of_one_exterior_side
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D E T U V L : Set S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hT : IsClosedDisc T)
    (hcover : T = U ∪ V ∪ L) (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hUL : Disjoint U L) (hVL : Disjoint V L)
    (hDL : T ∩ discBd D = L) (hEL : T ∩ discBd E = L)
    {p w : S} (hpL : p ∈ L) (hpT : p ∈ discInt T)
    (hwU : w ∈ U) (hwD : w ∉ D) (hwE : w ∉ E) :
    (discInt D ∩ discInt E).Nonempty := by
  have hUT : U ⊆ T := hcover ▸ subset_trans subset_union_left subset_union_left
  have hVT : V ⊆ T := hcover ▸ subset_trans subset_union_right subset_union_left
  have hLDb : L ⊆ discBd D := fun _ hx => (hDL.symm ▸ hx).2
  have hLEb : L ⊆ discBd E := fun _ hx => (hEL.symm ▸ hx).2
  have hUDb : Disjoint U (discBd D) := Set.disjoint_left.mpr
    (fun _ hx hb => Set.disjoint_left.mp hUL hx (hDL ▸ ⟨hUT hx, hb⟩))
  have hUEb : Disjoint U (discBd E) := Set.disjoint_left.mpr
    (fun _ hx hb => Set.disjoint_left.mp hUL hx (hEL ▸ ⟨hUT hx, hb⟩))
  have hVEb : Disjoint V (discBd E) := Set.disjoint_left.mpr
    (fun _ hx hb => Set.disjoint_left.mp hVL hx (hEL ▸ ⟨hVT hx, hb⟩))
  have hUD : Disjoint U D := by
    rcases hD.side hman hU hUDb with hin | hout
    · exact False.elim (hwD (hin hwU).1)
    · exact hout
  have hUE : Disjoint U E := by
    rcases hE.side hman hU hUEb with hin | hout
    · exact False.elim (hwE (hin hwU).1)
    · exact hout
  have hpDcl : p ∈ closure (discInt D) :=
    hD.subset_closure_discInt (discBd_subset D (hLDb hpL))
  obtain ⟨y, hyT, hyD⟩ := mem_closure_iff.mp hpDcl
    (discInt T) (hT.isOpen_discInt hman) hpT
  have hyV : y ∈ V := by
    have hycov : y ∈ U ∪ V ∪ L := hcover ▸ hyT.1
    rcases hycov with (hyU | hyV) | hyL
    · exact False.elim (Set.disjoint_left.mp hUD hyU hyD.1)
    · exact hyV
    · exact False.elim (hyD.2 (hLDb hyL))
  have hpEcl : p ∈ closure (discInt E) :=
    hE.subset_closure_discInt (discBd_subset E (hLEb hpL))
  obtain ⟨v, hvT, hvE⟩ := mem_closure_iff.mp hpEcl
    (discInt T) (hT.isOpen_discInt hman) hpT
  have hvV : v ∈ V := by
    have hvcov : v ∈ U ∪ V ∪ L := hcover ▸ hvT.1
    rcases hvcov with (hvU | hvV) | hvL
    · exact False.elim (Set.disjoint_left.mp hUE hvU hvE.1)
    · exact hvV
    · exact False.elim (hvE.2 (hLEb hvL))
  have hVE : V ⊆ discInt E := by
    rcases hE.side hman hV hVEb with hin | hout
    · exact hin
    · exact False.elim (Set.disjoint_left.mp hout hvV hvE.1)
  exact ⟨y, hyD, hVE hyV⟩

/-- Two discs with the same boundary arc across a lens have overlapping
interiors if a point of that arc can be approached from outside both.
The connected lens sides distinguish the shared exterior from the shared
interior. -/
theorem interiors_meet_of_shared_lens_and_common_exterior
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D E T A B L : Set S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hT : IsClosedDisc T)
    (hcover : T = A ∪ B ∪ L) (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hAL : Disjoint A L) (hBL : Disjoint B L)
    (hDL : T ∩ discBd D = L) (hEL : T ∩ discBd E = L)
    {p : S} (hpL : p ∈ L) (hpT : p ∈ discInt T)
    (hpcl : p ∈ closure ((D ∪ E)ᶜ)) :
    (discInt D ∩ discInt E).Nonempty := by
  obtain ⟨w, hwT, hwext⟩ := mem_closure_iff.mp hpcl
    (discInt T) (hT.isOpen_discInt hman) hpT
  have hwD : w ∉ D := fun h => hwext (Or.inl h)
  have hwE : w ∉ E := fun h => hwext (Or.inr h)
  have hwcov : w ∈ A ∪ B ∪ L := hcover ▸ hwT.1
  rcases hwcov with (hwA | hwB) | hwL
  · exact inside_point_of_one_exterior_side hman hD hE hT hcover hA hB hAL hBL
      hDL hEL hpL hpT hwA hwD hwE
  · have hcover' : T = B ∪ A ∪ L := by rw [union_comm B A]; exact hcover
    exact inside_point_of_one_exterior_side hman hD hE hT hcover' hB hA hBL hAL
      hDL hEL hpL hpT hwB hwD hwE
  · exact False.elim (hwD (discBd_subset D ((hDL.symm ▸ hwL).2)))

/-- If the old interior misses the new boundary, a shared interior point
forces inclusion of the old disc in the new disc. This is the separation
step after choosing the shared side in VIII (6.2). -/
theorem disc_subset_of_interior_meets_and_boundary_disjoint
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D E : Set S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hdis : Disjoint (discInt D) (discBd E))
    (hmeet : (discInt D ∩ discInt E).Nonempty) : D ⊆ E := by
  rcases hE.side hman hD.isPreconnected_discInt hdis with hin | hout
  · exact hD.subset_closure_discInt.trans
      (closure_minimal (hin.trans (discInt_subset E)) hE.isClosed)
  · obtain ⟨x, hxD, hxE⟩ := hmeet
    exact False.elim (Set.disjoint_left.mp hout hxD hxE.1)

end GraphMinor.GM08
