module

public import GraphMinor.Surface.Defs
import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.PlaneOrientation

/-!
# Leaf attachment for a thin tree neighborhood

Part IV, Section 7b of the planarity note attaches one strip and then its
new vertex polygon. The old neighborhood and the new polygon are disjoint.
The strip meets each in one boundary interval. Applying the disc gluing
lemma twice gives a closed disc and the explicit updated boundary. Points
in the interior of a glued interval become interior points of the union.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Topology Surface

/-- The two gluing operations at one leaf attachment in Part IV, Section 7b.
The resulting boundary is obtained by deleting the interiors of the two
attachment intervals from the union of the old boundaries. -/
theorem attach_tree_leaf_discs {N R P L K : Set ℂ} {a b c d : ℂ}
    (hN : IsClosedDisc N) (hR : IsClosedDisc R) (hP : IsClosedDisc P)
    (hL : IsLineWithEnds L a b) (hK : IsLineWithEnds K c d)
    (hNR : N ∩ R = L) (hRP : R ∩ P = K) (hNP : Disjoint N P)
    (hLN : L ⊆ discBd N) (hLR : L ⊆ discBd R)
    (hKR : K ⊆ discBd R) (hKP : K ⊆ discBd P) :
    IsClosedDisc (N ∪ R ∪ P) ∧
      discBd (N ∪ R ∪ P) =
        (((discBd N ∪ discBd R) \ (L \ {a, b})) ∪ discBd P) \ (K \ {c, d}) := by
  obtain ⟨hNRdisc, hNRbd⟩ := disc_union N R L a b hN hR hL hNR hLN hLR
  have hmeet : (N ∪ R) ∩ P = K := by
    rw [union_inter_distrib_right, hNP.inter_eq, hRP, empty_union]
  have hKunion : K ⊆ discBd (N ∪ R) := by
    rw [hNRbd]
    intro x hx
    refine ⟨Or.inr (hKR hx), ?_⟩
    intro hcut
    have hxN : x ∈ N ∩ R := hNR.symm ▸ hcut.1
    have hxP : x ∈ R ∩ P := hRP.symm ▸ hx
    exact disjoint_left.mp hNP hxN.1 hxP.2
  obtain ⟨hunion, hboundary⟩ :=
    disc_union (N ∪ R) P K c d hNRdisc hP hK hmeet hKunion hKP
  exact ⟨hunion, hNRbd ▸ hboundary⟩

/-- Part IV, Section 7b: after gluing two discs along a boundary interval,
every nonendpoint point of that interval is inside their union. -/
theorem disc_union_glued_interval_interior {A B L : Set ℂ} {a b x : ℂ}
    (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hL : IsLineWithEnds L a b)
    (hAB : A ∩ B = L) (hLA : L ⊆ discBd A) (hLB : L ⊆ discBd B)
    (hx : x ∈ L) (hxa : x ≠ a) (hxb : x ≠ b) : x ∈ interior (A ∪ B) := by
  obtain ⟨hdisc, hbd⟩ := disc_union A B L a b hA hB hL hAB hLA hLB
  have hfrontier : discBd (A ∪ B) = frontier (A ∪ B) :=
    (subBd_eq_discBd_complex hdisc).symm.trans (Surface.subBd_eq_frontier _)
  rw [← self_sdiff_frontier]
  have hxAB : x ∈ A ∩ B := hAB.symm ▸ hx
  refine ⟨Or.inl hxAB.1, ?_⟩
  rw [← hfrontier, hbd]
  intro hm
  exact hm.2 ⟨hx, fun he => he.elim hxa hxb⟩

end GraphMinor.LRPlanarity
