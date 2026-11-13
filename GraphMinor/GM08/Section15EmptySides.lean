module

public import GraphMinor.Surface.Defs
import GraphMinor.Surface.TriPath
public import GraphMinor.Surface.DiscGrow

/-!
# Extending a normal connector through empty disc sides

Attach the interiors of two empty discs to a normal arc at its ends.
The union remains preconnected and normal, and its drawing vertices are
exactly those of the arc. This supplies a connector reaching the capped
cuffs without increasing the short-tube length count in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- Empty disc interiors can be attached at the ends of a normal arc
without changing its drawing vertices. This is the connector used to
extend a short tube witness to the cylinder cuffs in VIII (15.4),
page 282. -/
theorem exists_normal_connector_with_empty_sides {S : Type} [TopologicalSpace S] [T2Space S]
    {G : Drawing S} {I E D : Set S} {u v : S} (hI : IsLineWithEnds I u v)
    (hE : IsClosedDisc E) (hD : IsClosedDisc D) (hu : u ∈ E) (hv : v ∈ D)
    (hEoff : Disjoint (discInt E) G.U) (hDoff : Disjoint (discInt D) G.U)
    (hn : G.IsNormal I) :
    ∃ A : Set S, IsPreconnected A ∧ G.IsNormal A ∧ I ⊆ A ∧
      discInt E ⊆ A ∧ discInt D ⊆ A ∧ A ∩ G.V = I ∩ G.V := by
  let L := insert u (discInt E)
  let R := insert v (discInt D)
  have hLc : IsPreconnected L := hE.isPreconnected_discInt.subset_closure
    (subset_insert _ _) (insert_subset (hE.subset_closure_discInt hu) subset_closure)
  have hRc : IsPreconnected R := hD.isPreconnected_discInt.subset_closure
    (subset_insert _ _) (insert_subset (hD.subset_closure_discInt hv) subset_closure)
  let A := (L ∪ I) ∪ R
  have hconn : IsPreconnected A :=
    (hLc.union' ⟨u, mem_insert _ _, hI.left_mem⟩ hI.isPreconnected_self).union'
      ⟨v, .inr hI.right_mem, mem_insert _ _⟩ hRc
  have hIA : I ⊆ A := fun x hx => .inl (.inr hx)
  have hAU : A ∩ G.U ⊆ I := by
    rintro x ⟨((hxL | hxI) | hxR), hxU⟩
    · rcases hxL with rfl | hxE
      · exact hI.left_mem
      · exact (disjoint_left.mp hEoff hxE hxU).elim
    · exact hxI
    · rcases hxR with rfl | hxD
      · exact hI.right_mem
      · exact (disjoint_left.mp hDoff hxD hxU).elim
  refine ⟨A, hconn, (fun x hx => hn ⟨hAU hx, hx.2⟩), hIA, ?_, ?_, ?_⟩
  · exact fun x hx => .inl (.inl (mem_insert_of_mem u hx))
  · exact fun x hx => .inr (mem_insert_of_mem v hx)
  · apply subset_antisymm
    · exact fun x hx => ⟨hAU ⟨hx.1, G.V_subset_U hx.2⟩, hx.2⟩
    · exact inter_subset_inter_left _ hIA

end GraphMinor.GM08
