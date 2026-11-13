module

public import GraphMinor.GM08.Section16PrintedDefs
import GraphMinor.GM08.Section17Cylinder
import GraphMinor.GM08.Section17Length
import GraphMinor.GM07.Section9Cylinder

/-!
# A free cuff-joining arc rules out a long subtube

Every hoop separates the two cylinder cuffs, so a connected arc
joining the cuffs meets it. A subtube of length at least two has
disjoint boundary hoops. Its length is therefore bounded by the
vertex count on any normal cuff-joining arc. In particular, an arc
off the drawing rules out all such subtubes. This supplies an unlinked
framing in the empty-cuff case of VIII (17.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v

/-- A cuff-joining line meets every hoop of the cylinder. -/
theorem line_meets_hoop_of_ends_on_cuffs {S : Type} [TopologicalSpace S]
    (hS : IsCylinder S) {C D H I : Set S} {a b : S}
    (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    (hH : IsHoop H) (hI : IsLineWithEnds I a b) (ha : a ∈ C) (hb : b ∈ D) :
    (I ∩ H).Nonempty := by
  obtain ⟨cap, rfl, rfl⟩ := CylinderSphereCap.exists_with_cuffs hS hC hD hCD
  by_contra hn
  have hoff : ∀ x ∈ I, x ∉ H := fun x hxI hxH => hn ⟨x, hxI, hxH⟩
  have hcov : I ⊆ cap.side₁ hS.1 hH ∪ cap.side₂ hS.1 hH := by
    rw [cap.side₁_union_side₂ hS.1 hH]
    exact fun x hx => ⟨mem_univ x, hoff x hx⟩
  have ha₁ := cap.C₁_diff_subset_side₁ hS.1 hH ⟨ha, hoff a hI.left_mem⟩
  have hb₂ := cap.C₂_diff_subset_side₂ hS.1 hH ⟨hb, hoff b hI.right_mem⟩
  have hpc := (GM07.IsLine.isPathConnected (GM07.IsLineWithEnds.isLine hI)).isConnected.isPreconnected
  rcases hpc.subset_or_subset (cap.isOpen_side₁ hS.1 hH)
      (cap.isOpen_side₂ hS.1 hH) (cap.disjoint_side₁_side₂ hS.1 hH) hcov with h | h
  · exact disjoint_left.mp (cap.disjoint_side₁_side₂ hS.1 hH) (h hI.right_mem) hb₂
  · exact disjoint_left.mp (cap.disjoint_side₁_side₂ hS.1 hH) ha₁ (h hI.left_mem)

/-- A framing with a cuff-joining arc off the drawing is not
`(r,2)`-boundary-linked, for any `r`. This is the short-framing
alternative used in VIII (17.2), page 284. -/
theorem Tube.not_printedBoundaryLinked_of_free_cuff_arc {S : Type}
    [TopologicalSpace S] (τ : Tube S)
    (hC : τ.F₁ ∈ cuffs S) (hD : τ.F₂ ∈ cuffs S) (hCD : τ.F₁ ≠ τ.F₂)
    {I : Set S} {a b : S} (hI : IsLineWithEnds I a b)
    (ha : a ∈ τ.F₁) (hb : b ∈ τ.F₂) (hoff : Disjoint I τ.Γ.U) (r : ℕ) :
    ¬ τ.IsPrintedBoundaryLinked r 2 := by
  rintro ⟨A, B, hlam, _, _, hNA, hNB, _, _, _, hlen, _⟩
  have hA := line_meets_hoop_of_ends_on_cuffs τ.isCylinder hC hD hCD hlam.2.1 hI ha hb
  have hB := line_meets_hoop_of_ends_on_cuffs τ.isCylinder hC hD hCD hlam.2.2.1 hI ha hb
  have hN : τ.Γ.IsNormal I := fun x hx => False.elim (disjoint_left.mp hoff hx.1 hx.2)
  have hbound := τ.subTube_length_le_ncard_of_line hlam hNA hNB
    (GM07.IsLineWithEnds.isLine hI) hN hA hB
    ((τ.subTube hlam hNA hNB).disjoint_of_two_le_length hlen)
  have hzero : τ.Γ.V ∩ I = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact disjoint_left.mp hoff hx.2 (τ.Γ.V_subset_U hx.1)
  rw [hzero, ncard_empty] at hbound
  exact Nat.not_succ_le_zero 1 (hlen.trans hbound)

end GraphMinor.GM08
