module

public import GraphMinor.LRPlanarity.TreeNeighborhoodUnion
import GraphMinor.LRPlanarity.TreeNeighborhoodForest

/-!
# The local geometry of the next attached leaf

Part IV, Section 7b of the planarity note attaches one tube and new vertex
polygon to the previous neighborhood. Parent closure ensures that no old
tube is incident with the new vertex. Pairwise separation therefore makes
the old union disjoint from the new polygon, and its intersection with the
new tube is precisely the parent-side interval. That interval remains on
the old boundary by the proved unused-boundary invariant.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Inserting a vertex adds exactly its parent tube and vertex polygon to
the finite cell union. -/
theorem forestCellUnion_insert {N : ℕ} (P R : Fin N → Set ℂ)
    (S : Finset (Fin N)) (leaf : Fin N) :
    forestCellUnion P R (insert leaf S) = forestCellUnion P R S ∪ R leaf ∪ P leaf := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨v,hv'⟩ := mem_iUnion.mp hx
    obtain ⟨hv,hxv⟩ := mem_iUnion.mp hv'
    rcases Finset.mem_insert.mp hv with he | hv
    · subst v
      exact hxv.elim Or.inr (fun h => Or.inl (Or.inr h))
    · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨hv,hxv⟩⟩))
  · intro hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨v,hv'⟩ := mem_iUnion.mp hx
      obtain ⟨hv,hxv⟩ := mem_iUnion.mp hv'
      exact mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hv,hxv⟩⟩
    · exact mem_iUnion.mpr ⟨leaf,mem_iUnion.mpr ⟨Finset.mem_insert_self _ _,Or.inr hx⟩⟩
    · exact mem_iUnion.mpr ⟨leaf,mem_iUnion.mpr ⟨Finset.mem_insert_self _ _,Or.inl hx⟩⟩

/-- Part IV, Section 7b: the next leaf's gluing configuration follows from
the constructed local cell intersections and parent closure. -/
theorem cell_union_next_leaf_geometry {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
    (hT : T.IsDFS G) (root : Fin N) (hroot : T.parent root = none)
    (P R L K : Fin N → Set ℂ) (a b c d : Fin N → ℂ)
    (hP : ∀ v, IsClosedDisc (P v)) (hPsep : Pairwise (fun u v => Disjoint (P u) (P v)))
    (hRnone : ∀ v, T.parent v = none → R v = ∅)
    (hRsep : Pairwise (fun u v => Disjoint (R u) (R v)))
    (hlocal : ∀ v p, T.parent v = some p →
      IsClosedDisc (R v) ∧ IsLineWithEnds (L v) (a v) (b v) ∧
      IsLineWithEnds (K v) (c v) (d v) ∧ P p ∩ R v = L v ∧ R v ∩ P v = K v ∧
      L v ⊆ discBd (P p) ∧ L v ⊆ discBd (R v) ∧ K v ⊆ discBd (R v) ∧ K v ⊆ discBd (P v))
    (haway : ∀ v p, T.parent v = some p → ∀ w, w ≠ v → w ≠ p → Disjoint (R v) (P w))
    (S : Finset (Fin N)) (hrootS : root ∈ S) (hancestor : ∀ v ∈ S, T.Ancestor root v)
    (hclosed : ∀ v ∈ S, ∀ p, T.parent v = some p → p ∈ S)
    (leaf p : Fin N) (hleaf : leaf ∉ S) (hp : p ∈ S) (hparent : T.parent leaf = some p) :
    IsClosedDisc (forestCellUnion P R S) ∧
      forestCellUnion P R S ∩ R leaf = L leaf ∧
      Disjoint (forestCellUnion P R S) (P leaf) ∧ L leaf ⊆ discBd (forestCellUnion P R S) := by
  classical
  have hparents : ∀ v ∈ S, v ≠ root → ∃ p ∈ S, T.parent v = some p := by
    intro v hv hvr
    cases hpv : T.parent v with
    | none =>
      have hdepthv := hT.1 v hpv
      have hdepthroot := hT.1 root hroot
      have hlt := strict_ancestor_depth_lt hT (hancestor v hv) (Ne.symm hvr)
      rw [hdepthv,hdepthroot] at hlt
      exact (Nat.lt_irrefl 0 hlt).elim
    | some p => exact ⟨p,hclosed v hv p hpv,rfl⟩
  obtain ⟨hN,hboundary⟩ := forestCellUnion_isClosedDisc hT root P R L K a b c d hP hPsep
    (hRnone root hroot) hRsep hlocal haway S hrootS hancestor hparents
  have hleafne : ∀ v ∈ S, v ≠ leaf := fun v hv he => hleaf (he ▸ hv)
  obtain ⟨_,_,_,hPL,_,hLP,_,_,_⟩ := hlocal leaf p hparent
  have hNP : Disjoint (forestCellUnion P R S) (P leaf) := by
    rw [disjoint_left]
    intro x hx hxleaf
    obtain ⟨v,hv'⟩ := mem_iUnion.mp hx
    obtain ⟨hv,hxP | hxR⟩ := mem_iUnion.mp hv'
    · exact disjoint_left.mp (hPsep (hleafne v hv)) hxP hxleaf
    · cases hpv : T.parent v with
      | none => simp only [hRnone v hpv,mem_empty_iff_false] at hxR
      | some q =>
        have hq := hclosed v hv q hpv
        exact disjoint_left.mp (haway v q hpv leaf (hleafne v hv).symm (hleafne q hq).symm) hxR hxleaf
  have hNR : forestCellUnion P R S ∩ R leaf = L leaf := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨v,hv'⟩ := mem_iUnion.mp hx.1
      obtain ⟨hv,hxP | hxR⟩ := mem_iUnion.mp hv'
      · by_cases hvp : v = p
        · subst v
          exact hPL ▸ (⟨hxP,hx.2⟩ : x ∈ P p ∩ R leaf)
        · exact (disjoint_left.mp (haway leaf p hparent v (hleafne v hv) hvp) hx.2 hxP).elim
      · exact (disjoint_left.mp (hRsep (hleafne v hv)) hxR hx.2).elim
    · intro x hx
      have hm : x ∈ P p ∩ R leaf := hPL.symm ▸ hx
      exact ⟨mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,Or.inl hm.1⟩⟩,hm.2⟩
  refine ⟨hN,hNR,hNP,?_⟩
  apply hboundary p hp (L leaf) hLP
  intro v hv
  exact (hRsep (hleafne v hv).symm).mono_left (fun x hx => (hPL.symm ▸ hx).2)

end GraphMinor.LRPlanarity
