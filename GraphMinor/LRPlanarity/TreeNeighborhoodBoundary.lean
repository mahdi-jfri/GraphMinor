module

public import GraphMinor.Surface.Defs
import GraphMinor.LRPlanarity.TreeNeighborhoodGluing

/-!
# Boundary intervals retained by a leaf attachment

Part IV, Section 7b of the planarity note keeps the explicit boundary at
each disc gluing. A subset of an old boundary survives if it avoids both
attachment intervals. A subset of the new polygon boundary survives if
it avoids its own attachment interval. These are the invariants needed
when more strips are attached later.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- An old boundary subset disjoint from both gluing intervals remains on
the boundary after the two gluings of Part IV, Section 7b. -/
theorem old_boundary_survives_leaf_attachment {N R P L K A : Set ℂ} {a b c d : ℂ}
    (hN : IsClosedDisc N) (hR : IsClosedDisc R) (hP : IsClosedDisc P)
    (hL : IsLineWithEnds L a b) (hK : IsLineWithEnds K c d)
    (hNR : N ∩ R = L) (hRP : R ∩ P = K) (hNP : Disjoint N P)
    (hLN : L ⊆ discBd N) (hLR : L ⊆ discBd R)
    (hKR : K ⊆ discBd R) (hKP : K ⊆ discBd P)
    (hA : A ⊆ discBd N) (hAL : Disjoint A L) (hAK : Disjoint A K) :
    A ⊆ discBd (N ∪ R ∪ P) := by
  rw [(attach_tree_leaf_discs hN hR hP hL hK hNR hRP hNP hLN hLR hKR hKP).2]
  intro x hx
  refine ⟨Or.inl ⟨Or.inl (hA hx), ?_⟩, ?_⟩
  · intro hcut
    exact disjoint_left.mp hAL hx hcut.1
  · intro hcut
    exact disjoint_left.mp hAK hx hcut.1

/-- A subset of the new polygon boundary remains on the boundary after
attachment when it avoids that polygon's gluing interval. -/
theorem new_boundary_survives_leaf_attachment {N R P L K A : Set ℂ} {a b c d : ℂ}
    (hN : IsClosedDisc N) (hR : IsClosedDisc R) (hP : IsClosedDisc P)
    (hL : IsLineWithEnds L a b) (hK : IsLineWithEnds K c d)
    (hNR : N ∩ R = L) (hRP : R ∩ P = K) (hNP : Disjoint N P)
    (hLN : L ⊆ discBd N) (hLR : L ⊆ discBd R)
    (hKR : K ⊆ discBd R) (hKP : K ⊆ discBd P)
    (hA : A ⊆ discBd P) (hAK : Disjoint A K) :
    A ⊆ discBd (N ∪ R ∪ P) := by
  rw [(attach_tree_leaf_discs hN hR hP hL hK hNR hRP hNP hLN hLR hKR hKP).2]
  intro x hx
  exact ⟨Or.inr (hA hx), fun hcut => disjoint_left.mp hAK hx hcut.1⟩

end GraphMinor.LRPlanarity
