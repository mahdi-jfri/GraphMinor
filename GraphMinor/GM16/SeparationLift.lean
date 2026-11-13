module

public import GraphMinor.GM16.Defs
import GraphMinor.GM16.TorsoEdgePiece
import GraphMinor.GM09.Basic

/-!
# Restoring exceptional vertices to a separation

In XVI (1.3), pages 51–52, a separation of `G` with `Z` deleted is
lifted by putting `Z` into both vertex sets. Its right side contains
all edges outside the original left side whose ends lie in the new
right vertex set. The remaining edges form the lifted left side.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09
universe u v

/-- The side `B⁺` in the proof of XVI (1.3), page 51. -/
def liftSeparationRight {α : Type u} {β : Type v}
    (G : Graph α β) (Z : Set α) (p : Graph α β × Graph α β) : Graph α β :=
  (G.induce (V(p.2) ∪ Z)).restrict (E(G) \ E(p.1))

/-- The side `A⁺` in the proof of XVI (1.3), page 51. -/
def liftSeparationLeft {α : Type u} {β : Type v}
    (G : Graph α β) (Z : Set α) (p : Graph α β × Graph α β) : Graph α β :=
  (G.induce (V(p.1) ∪ Z)).restrict (E(G) \ E(liftSeparationRight G Z p))

/-- The lifted pair with the exceptional set in both sides. -/
def liftLocationPair {α : Type u} {β : Type v}
    (G : Graph α β) (Z : Set α) (p : Graph α β × Graph α β) :
    Graph α β × Graph α β :=
  (liftSeparationLeft G Z p, liftSeparationRight G Z p)

/-- Both lifted sides are subgraphs of the original graph. -/
theorem liftLocationPair_le {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    {p : Graph α β × Graph α β} (hp : IsGraphSeparation (deleteVertices G Z) p.1 p.2) :
    liftSeparationLeft G Z p ≤ G ∧ liftSeparationRight G Z p ≤ G := by
  have hAG := hp.1.trans (deleteVertices_le G Z)
  have hBG := hp.2.1.trans (deleteVertices_le G Z)
  exact ⟨restrict_le.trans (G.induce_le (union_subset hAG.vertexSet_mono hZ)),
    restrict_le.trans (G.induce_le (union_subset hBG.vertexSet_mono hZ))⟩

/-- Every edge outside the lifted right side has all its ends in the
lifted left vertex set. -/
theorem liftSeparationLeft_edgeSet {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α}
    {p : Graph α β × Graph α β} (hp : IsGraphSeparation (deleteVertices G Z) p.1 p.2) :
    E(liftSeparationLeft G Z p) = E(G) \ E(liftSeparationRight G Z p) := by
  have hAG := hp.1.trans (deleteVertices_le G Z)
  have hBG := hp.2.1.trans (deleteVertices_le G Z)
  apply edgeSet_induce_restrict_eq_of_ends_subset sdiff_subset
  rintro e ⟨heG, heNot⟩ x ⟨y, hxy⟩
  by_contra hx
  have hxA : x ∉ V(p.1) := fun hxA => hx (Or.inl hxA)
  have hxZ : x ∉ Z := fun hxZ => hx (Or.inr hxZ)
  have hxB : x ∈ V(p.2) := by
    have hxSource : x ∈ V(deleteVertices G Z) := ⟨hxy.left_mem, hxZ⟩
    rw [← hp.2.2.1] at hxSource
    exact hxSource.resolve_left hxA
  have heNotA : e ∉ E(p.1) := by
    intro heA
    exact hxA ((hAG.isLink_iff heA).mpr hxy).left_mem
  have hyRight : y ∈ V(p.2) ∪ Z := by
    by_cases hyZ : y ∈ Z
    · exact Or.inr hyZ
    · have hxySource : (deleteVertices G Z).IsLink e x y :=
        (deleteVertices_isLink G Z).mpr ⟨hxy, hxZ, hyZ⟩
      have heUnion : e ∈ E(p.1) ∪ E(p.2) := hp.2.2.2.1.symm ▸ hxySource.edge_mem
      have heB : e ∈ E(p.2) := heUnion.resolve_left heNotA
      exact Or.inl ((hBG.isLink_iff heB).mpr hxy).right_mem
  apply heNot
  exact ⟨⟨x, y, hxy, Or.inl hxB, hyRight⟩, heG, heNotA⟩

/-- The lifted pair is a separation, with separator equal to the
old separator together with the exceptional set. -/
theorem liftLocationPair_isSeparation {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    {p : Graph α β × Graph α β} (hp : IsGraphSeparation (deleteVertices G Z) p.1 p.2) :
    IsGraphSeparation G (liftSeparationLeft G Z p) (liftSeparationRight G Z p) ∧
      V(liftSeparationLeft G Z p) ∩ V(liftSeparationRight G Z p) =
        Z ∪ (V(p.1) ∩ V(p.2)) := by
  obtain ⟨hLeft, hRight⟩ := liftLocationPair_le hZ hp
  have hEL := liftSeparationLeft_edgeSet hp
  refine ⟨⟨hLeft, hRight, ?_, ?_, ?_⟩, ?_⟩
  · ext x
    change ((x ∈ V(p.1) ∨ x ∈ Z) ∨ x ∈ V(p.2) ∨ x ∈ Z) ↔ x ∈ V(G)
    constructor
    · rintro ((hx | hx) | hx | hx)
      · exact (hp.1.trans (deleteVertices_le G Z)).vertexSet_mono hx
      · exact hZ hx
      · exact (hp.2.1.trans (deleteVertices_le G Z)).vertexSet_mono hx
      · exact hZ hx
    · intro hx
      by_cases hxZ : x ∈ Z
      · exact Or.inl (Or.inr hxZ)
      · have hxUnion : x ∈ V(p.1) ∪ V(p.2) := hp.2.2.1.symm ▸ And.intro hx hxZ
        exact hxUnion.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h))
  · rw [hEL]
    exact sdiff_union_of_subset hRight.edgeSet_mono
  · rw [hEL]
    exact disjoint_sdiff_self_left
  · ext x
    change ((x ∈ V(p.1) ∨ x ∈ Z) ∧ (x ∈ V(p.2) ∨ x ∈ Z)) ↔
      (x ∈ Z ∨ x ∈ V(p.1) ∧ x ∈ V(p.2))
    tauto

end GraphMinor.GM16
