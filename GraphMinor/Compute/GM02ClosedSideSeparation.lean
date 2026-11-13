module

public import GraphMinor.Compute.GM02FiniteComponents
public import GraphMinor.GM02.Separation

/-!
# From a balanced union of components to the two output sides

The successful-output construction for II (3.1) collects whole components
into a vertex set. Once its terminal count is between one third and two
thirds of the remaining total, its complement has at most two thirds too.
Put the separator on both sides and partition the edges as in II (2.6).
-/

public section
namespace GraphMinor.Compute
open Graph Set Relation GraphMinor.GM02 Classical

/-- A component-closed side with a one-third to two-thirds terminal count
produces the balanced separation, with explicit output vertex sets. -/
theorem gm02BalancedSeparation_of_closed_side {n : ℕ} (G : SimpleGraph (Fin n))
    (Q X Y : Finset (Fin n)) (hXY : Disjoint X Y)
    (hclosed : ∀ a ∈ Y, gm02FiniteComponent G X a ⊆ Y)
    (hlo : (Q \ X).card ≤ 3 * (Y ∩ Q).card)
    (hhi : 3 * (Y ∩ Q).card ≤ 2 * (Q \ X).card) :
    ∃ H H' : Graph (Fin n) (Sym2 (Fin n)),
      IsSeparation (Graph.ofSimpleGraph G) H H' ∧
      V(H) = (↑(X ∪ Y) : Set (Fin n)) ∧ V(H') = (↑(Finset.univ \ Y) : Set (Fin n)) ∧
      V(H) ∩ V(H') = (X : Set (Fin n)) ∧
      3 * ((V(H) \ V(H')) ∩ (Q : Set (Fin n))).ncard ≤
        2 * ((Q : Set (Fin n)) \ (V(H) ∩ V(H'))).ncard ∧
      3 * ((V(H') \ V(H)) ∩ (Q : Set (Fin n))).ncard ≤
        2 * ((Q : Set (Fin n)) \ (V(H) ∩ V(H'))).ncard := by
  let Z := Finset.univ \ (X ∪ Y)
  have hpart : (Y : Set (Fin n)) ∪ (Z : Set (Fin n)) =
      V(Graph.ofSimpleGraph G) \ (X : Set (Fin n)) := by
    ext a
    have hdis := Finset.disjoint_left.1 hXY
    simp only [Z, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Set.mem_union, Set.mem_sdiff, Graph.ofSimpleGraph, Set.mem_univ, true_and]
    constructor
    · rintro (hy | h)
      · exact fun hx => hdis hx hy
      · exact fun hx => h (Or.inl hx)
    · intro hx
      by_cases hy : a ∈ Y
      · exact Or.inl hy
      · exact Or.inr (fun h => h.elim hx hy)
  have hsep : Separates (Graph.ofSimpleGraph G) (X : Set (Fin n))
      (Y : Set (Fin n)) (Z : Set (Fin n)) := by
    intro a ha b hb haX hbX hp
    have hbC : b ∈ gm02FiniteComponent G X a :=
      (mem_gm02FiniteComponent G X a b).2 ⟨hbX, hp⟩
    have hbY := hclosed a ha hbC
    exact (Finset.mem_sdiff.1 hb).2 (Finset.mem_union_right _ hbY)
  obtain ⟨H, H', hHH', hHV, hH'V⟩ := exists_separation_of_partition (Set.subset_univ _)
    hpart hsep
  have hright : (X : Set (Fin n)) ∪ (Z : Set (Fin n)) =
      (↑(Finset.univ \ Y) : Set (Fin n)) := by
    ext a
    simp only [Z, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Set.mem_union]
    constructor
    · rintro (hx | hz)
      · exact fun hy => Finset.disjoint_left.1 hXY hx hy
      · exact fun hy => hz (Or.inr hy)
    · intro hy
      by_cases hx : a ∈ X
      · exact Or.inl hx
      · exact Or.inr (fun h => h.elim hx hy)
  have hleft : V(H) = (↑(X ∪ Y) : Set (Fin n)) := by simpa only [Finset.coe_union] using hHV
  have hrightV := hH'V.trans hright
  have hinter : V(H) ∩ V(H') = (X : Set (Fin n)) := by
    rw [hleft, hrightV]
    ext a
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Set.mem_inter_iff]
    exact ⟨fun h => h.1.elim id (fun hy => (h.2 hy).elim),
      fun hx => ⟨Or.inl hx, fun hy => Finset.disjoint_left.1 hXY hx hy⟩⟩
  have hleftEx : V(H) \ V(H') = (Y : Set (Fin n)) := by
    rw [hleft, hrightV]
    ext a
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Set.mem_sdiff, not_not]
    exact ⟨And.right, fun hy => ⟨Or.inr hy, hy⟩⟩
  have hrightEx : V(H') \ V(H) = (Z : Set (Fin n)) := by
    rw [hrightV, hleft]
    ext a
    simp only [Z, Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Set.mem_sdiff]
    exact ⟨fun h => h.2, fun h => ⟨fun hy => h (Or.inr hy), h⟩⟩
  have hcount : (Y ∩ Q).card + (Z ∩ Q).card = (Q \ X).card := by
    have hdis : Disjoint (Y ∩ Q) (Z ∩ Q) := by
      apply Finset.disjoint_left.2
      intro a ha hb
      exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 hb).1).2
        (Finset.mem_union_right _ (Finset.mem_inter.1 ha).1)
    rw [← Finset.card_union_of_disjoint hdis]
    congr 1
    apply Finset.coe_injective
    simp only [Finset.coe_union, Finset.coe_inter, ← Set.union_inter_distrib_right, hpart]
    ext a
    simp only [Graph.ofSimpleGraph, Set.mem_univ, Set.mem_sdiff, true_and, Set.mem_inter_iff,
      Finset.mem_coe, Finset.mem_sdiff]
    exact and_comm
  refine ⟨H, H', hHH', hleft, hrightV, hinter, ?_, ?_⟩
  · simpa only [hinter, hleftEx, ← Finset.coe_inter, ← Finset.coe_sdiff, Set.ncard_coe_finset] using hhi
  · have hb : 3 * (Z ∩ Q).card ≤ 2 * (Q \ X).card := by omega
    simpa only [hinter, hrightEx, ← Finset.coe_inter, ← Finset.coe_sdiff, Set.ncard_coe_finset] using hb

end GraphMinor.Compute
