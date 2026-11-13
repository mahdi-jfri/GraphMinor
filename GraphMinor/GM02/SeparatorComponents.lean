module

public import GraphMinor.GM02.BagSeparation
public import GraphMinor.GM02.BranchRegions

/-!
# Component bounds from a separated partition

The balancing step of II (2.5) gives two sides of equal size in `Q` after
removing a separator. A component of the remaining graph cannot meet both
sides. Its `Q` vertices are therefore bounded by one side. The same argument
works for unequal side bounds and for an enlarged separator.
-/

public section
namespace GraphMinor.GM02
open Graph Set Relation
universe u v

/-- Separation is symmetric in its two sides. -/
theorem Separates.symm {α : Type u} {β : Type v} {G : Graph α β}
    {X Y Y' : Set α} (h : Separates G X Y Y') : Separates G X Y' Y := by
  intro a ha b hb haX hbX hpath
  have hrev := (inferInstance : Std.Symm (ReflTransGen (G.induce (V(G) \ X)).Adj)).symm _ _ hpath
  exact h b hb a ha hbX haX hrev

/-- Enlarging a separator preserves separation of the two sides. -/
theorem Separates.mono_separator {α : Type u} {β : Type v} {G : Graph α β}
    {X X' Y Y' : Set α} (h : Separates G X Y Y') (hXX' : X ⊆ X') :
    Separates G X' Y Y' := by
  have hremaining : V(G) \ X' ⊆ V(G) \ X :=
    fun _ hx => ⟨hx.1, fun hX => hx.2 (hXX' hX)⟩
  have hG : G.induce (V(G) \ X') ≤ G.induce (V(G) \ X) := by
    constructor
    · exact hremaining
    · intro e a b hab
      exact ⟨hab.1, hremaining hab.2.1, hremaining hab.2.2⟩
  intro a ha b hb haX hbX hpath
  have hpath' := Relation.ReflTransGen.mono (fun _ _ hadj => Graph.Adj.mono hG hadj) _ _ hpath
  exact h a ha b hb (hremaining haX) (hremaining hbX) hpath'

private theorem deletedComponent_subset_side {α : Type u} {β : Type v} {G : Graph α β}
    {X Y Y' : Set α} (hcover : ∀ a ∈ V(G) \ X, a ∈ Y ∨ a ∈ Y')
    (hsep : Separates G X Y Y') {a : α} (haX : a ∈ V(G) \ X) (ha : a ∈ Y) :
    deletedComponent G X a ⊆ Y := by
  intro b hb
  rcases hcover b hb.1 with hbY | hbY'
  · exact hbY
  · exact (hsep a ha b hbY' haX hb.1 hb.2).elim

/-- If the two separated sides each contain at most half the remaining
`Q` vertices, every remaining component has the same bound. This is the
last step in both cases of II (2.5), pages 312–313. -/
theorem component_bound_of_separated_partition {α : Type u} {β : Type v}
    {G : Graph α β} {X Y Y' Q : Set α} (hQ : Q.Finite)
    (hcover : ∀ a ∈ V(G) \ X, a ∈ Y ∨ a ∈ Y')
    (hsep : Separates G X Y Y')
    (hY : 2 * (Y ∩ Q).ncard ≤ (Q \ X).ncard)
    (hY' : 2 * (Y' ∩ Q).ncard ≤ (Q \ X).ncard) :
    ∀ a ∈ V(G) \ X, 2 * (deletedComponent G X a ∩ Q).ncard ≤ (Q \ X).ncard := by
  intro a ha
  rcases hcover a ha with haY | haY'
  · have hsub := deletedComponent_subset_side hcover hsep ha haY
    have hsubQ : deletedComponent G X a ∩ Q ⊆ Y ∩ Q :=
      fun _ hx => ⟨hsub hx.1, hx.2⟩
    exact (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard hsubQ (hQ.subset Set.inter_subset_right))).trans hY
  · have hcover' : ∀ a ∈ V(G) \ X, a ∈ Y' ∨ a ∈ Y :=
      fun a ha => (hcover a ha).symm
    have hsub := deletedComponent_subset_side hcover' hsep.symm ha haY'
    have hsubQ : deletedComponent G X a ∩ Q ⊆ Y' ∩ Q :=
      fun _ hx => ⟨hsub hx.1, hx.2⟩
    exact (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard hsubQ (hQ.subset Set.inter_subset_right))).trans hY'

end GraphMinor.GM02
