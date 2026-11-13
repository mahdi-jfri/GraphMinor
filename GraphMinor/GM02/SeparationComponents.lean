module

public import GraphMinor.GM02.ComponentTestSeparation

/-!
# Components of the complement of a separation

An edge outside the common vertex set cannot change sides: whichever
subgraph contains the edge also contains both ends. Induction along a
walk then places a whole remaining component on its starting side.
Thus every balanced separation passes the component test in II (3.1).
-/

public section
namespace GraphMinor.GM02
open Graph Set Relation Classical
universe u v
variable {α : Type u} {β : Type v} {G H H' : Graph α β}

private theorem adj_stays_left (hsep : IsSeparation G H H') {a b : α}
    (ha : a ∈ V(H) \ V(H'))
    (hab : (G.induce (V(G) \ (V(H) ∩ V(H')))).Adj a b) : b ∈ V(H) \ V(H') := by
  obtain ⟨e, he⟩ := hab
  have heG : G.IsLink e a b ∧ a ∈ V(G) \ (V(H) ∩ V(H')) ∧
      b ∈ V(G) \ (V(H) ∩ V(H')) := by
    simpa only [Graph.induce_isLink] using he
  have heE : e ∈ E(H) ∪ E(H') := hsep.2.2.2.1.symm ▸ heG.1.edge_mem
  have hbH : b ∈ V(H) := by
    rcases heE with heH | heH'
    · exact ((hsep.1.isLink_iff heH).2 heG.1).right_mem
    · exact (ha.2 (((hsep.2.1.isLink_iff heH').2 heG.1).left_mem)).elim
  exact ⟨hbH, fun hbH' => heG.2.2.2 ⟨hbH, hbH'⟩⟩

/-- A component of the graph outside a separation's common vertices stays
on the first side if its initial vertex lies there. -/
theorem deletedComponent_subset_left (hsep : IsSeparation G H H') {a : α}
    (ha : a ∈ V(H) \ V(H')) :
    deletedComponent G (V(H) ∩ V(H')) a ⊆ V(H) \ V(H') := by
  intro b hb
  have hp := hb.2
  clear hb
  induction hp with
  | refl => exact ha
  | tail hp hab ih => exact adj_stays_left hsep ih hab

/-- Each component of the complement lies wholly on one of the exclusive sides. -/
theorem deletedComponent_subset_side (hsep : IsSeparation G H H') {a : α}
    (ha : a ∈ V(G) \ (V(H) ∩ V(H'))) :
    deletedComponent G (V(H) ∩ V(H')) a ⊆ V(H) \ V(H') ∨
      deletedComponent G (V(H) ∩ V(H')) a ⊆ V(H') \ V(H) := by
  have haU : a ∈ V(H) ∪ V(H') := hsep.2.2.1.symm ▸ ha.1
  rcases haU with haH | haH'
  · exact Or.inl (deletedComponent_subset_left hsep ⟨haH, fun h => ha.2 ⟨haH, h⟩⟩)
  · have hswap : IsSeparation G H' H :=
      ⟨hsep.2.1, hsep.1, (Set.union_comm _ _).trans hsep.2.2.1,
        (Set.union_comm _ _).trans hsep.2.2.2.1, hsep.2.2.2.2.symm⟩
    apply Or.inr
    rw [Set.inter_comm]
    exact deletedComponent_subset_left hswap ⟨haH', fun h => ha.2 ⟨h, haH'⟩⟩

/-- A balanced separation passes the component test of II (3.1), page 316. -/
theorem balanced_separation_component_bound (hV : (V(G)).Finite)
    (hsep : IsSeparation G H H') {Q : Set α}
    (hL : 3 * ((V(H) \ V(H')) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard)
    (hR : 3 * ((V(H') \ V(H)) ∩ Q).ncard ≤ 2 * (Q \ (V(H) ∩ V(H'))).ncard)
    {a : α} (ha : a ∈ V(G) \ (V(H) ∩ V(H'))) :
    3 * (deletedComponent G (V(H) ∩ V(H')) a ∩ Q).ncard ≤
      2 * (Q \ (V(H) ∩ V(H'))).ncard := by
  rcases deletedComponent_subset_side hsep ha with h | h
  · exact (Nat.mul_le_mul_left 3 (Set.ncard_le_ncard (Set.inter_subset_inter_left Q h)
      ((hV.subset hsep.1.vertexSet_mono).sdiff.inter_of_left Q))).trans hL
  · exact (Nat.mul_le_mul_left 3 (Set.ncard_le_ncard (Set.inter_subset_inter_left Q h)
      ((hV.subset hsep.2.1.vertexSet_mono).sdiff.inter_of_left Q))).trans hR

end GraphMinor.GM02
