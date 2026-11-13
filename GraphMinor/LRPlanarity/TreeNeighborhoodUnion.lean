module

public import GraphMinor.LRPlanarity.Defs
public import GraphMinor.Surface.Defs
import GraphMinor.LRPlanarity.TreeNeighborhoodLeafOrder
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundary
import GraphMinor.LRPlanarity.TreeNeighborhoodGluing

/-!
# The disc obtained from a finite tree of polygons and strips

Part IV, Section 7b of the planarity note builds the neighborhood by
attaching a strip and a leaf polygon. This file performs that induction
for polygons and strips with the stated exact intersections. Along with
the disc conclusion it retains every polygon boundary subset that avoids
the strips already attached. Thus each unused strip interval is available
for the next gluing.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- The union of vertex polygons and their parent strips in Part IV,
Section 7b. The root's parent strip is empty. -/
@[expose] def forestCellUnion {N : ℕ} (P R : Fin N → Set ℂ)
    (S : Finset (Fin N)) : Set ℂ := ⋃ v ∈ S, P v ∪ R v

private theorem mem_forestCellUnion {N : ℕ} {P R : Fin N → Set ℂ}
    {S : Finset (Fin N)} {x : ℂ} :
    x ∈ forestCellUnion P R S ↔ ∃ v ∈ S, x ∈ P v ∨ x ∈ R v := by
  simp only [forestCellUnion, mem_iUnion, mem_union, exists_prop]

/-- Part IV, Section 7b: polygons joined by separated parent strips form a
disc. Boundary subsets avoiding all attached strips remain on its boundary.
The assumptions describe the local polygon and strip configuration, rather
than assuming any conclusion about their union. -/
theorem forestCellUnion_isClosedDisc {N : ℕ} {G : SimpleGraph (Fin N)}
    {T : Forest N} (hT : T.IsDFS G) (root : Fin N)
    (P R L K : Fin N → Set ℂ) (a b c d : Fin N → ℂ)
    (hP : ∀ v, IsClosedDisc (P v)) (hPsep : Pairwise (fun u v => Disjoint (P u) (P v)))
    (hRroot : R root = ∅) (hRsep : Pairwise (fun u v => Disjoint (R u) (R v)))
    (hlocal : ∀ v p, T.parent v = some p →
      IsClosedDisc (R v) ∧ IsLineWithEnds (L v) (a v) (b v) ∧
      IsLineWithEnds (K v) (c v) (d v) ∧
      P p ∩ R v = L v ∧ R v ∩ P v = K v ∧
      L v ⊆ discBd (P p) ∧ L v ⊆ discBd (R v) ∧
      K v ⊆ discBd (R v) ∧ K v ⊆ discBd (P v))
    (haway : ∀ v p, T.parent v = some p →
      ∀ w, w ≠ v → w ≠ p → Disjoint (R v) (P w))
    (S : Finset (Fin N)) (hroot : root ∈ S)
    (hancestor : ∀ v ∈ S, T.Ancestor root v)
    (hparent : ∀ v ∈ S, v ≠ root → ∃ p ∈ S, T.parent v = some p) :
    IsClosedDisc (forestCellUnion P R S) ∧
      ∀ u ∈ S, ∀ A : Set ℂ, A ⊆ discBd (P u) →
        (∀ v ∈ S, Disjoint A (R v)) → A ⊆ discBd (forestCellUnion P R S) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hother : ∃ w ∈ S, w ≠ root
    · obtain ⟨leaf, hleaf, hlr, hchild, hroot', hanc', hpar'⟩ :=
        exists_leaf_erase_subtree hT root S hroot hancestor hparent hother
      obtain ⟨p, hp, hleafp⟩ := hparent leaf hleaf hlr
      have hpl : p ≠ leaf := by
        intro he
        exact hchild leaf hleaf (he ▸ hleafp)
      have hp' : p ∈ S.erase leaf := Finset.mem_erase.mpr ⟨hpl, hp⟩
      obtain ⟨hold, hboundary⟩ := ih (S.erase leaf)
        (Finset.erase_ssubset hleaf) hroot' hanc' hpar'
      obtain ⟨hRl, hLl, hKl, hPL, hRK, hLP, hLR, hKR, hKP⟩ := hlocal leaf p hleafp
      have hdisjoint : Disjoint (forestCellUnion P R (S.erase leaf)) (P leaf) := by
        rw [disjoint_left]
        intro x hx hxleaf
        obtain ⟨v, hv, hxv | hxv⟩ := mem_forestCellUnion.mp hx
        · exact disjoint_left.mp (hPsep (Finset.ne_of_mem_erase hv)) hxv hxleaf
        · by_cases hvr : v = root
          · subst v
            simp only [hRroot, mem_empty_iff_false] at hxv
          · obtain ⟨q, hq, hvq⟩ := hpar' v hv hvr
            exact disjoint_left.mp (haway v q hvq leaf
              (Finset.ne_of_mem_erase hv).symm (Finset.ne_of_mem_erase hq).symm) hxv hxleaf
      have hinter : forestCellUnion P R (S.erase leaf) ∩ R leaf = L leaf := by
        apply Subset.antisymm
        · intro x hx
          obtain ⟨v, hv, hxv | hxv⟩ := mem_forestCellUnion.mp hx.1
          · by_cases hvp : v = p
            · subst v
              exact hPL ▸ ⟨hxv, hx.2⟩
            · exact (disjoint_left.mp (haway leaf p hleafp v
                (Finset.ne_of_mem_erase hv) hvp) hx.2 hxv).elim
          · exact (disjoint_left.mp (hRsep (Finset.ne_of_mem_erase hv)) hxv hx.2).elim
        · intro x hx
          have hxPR : x ∈ P p ∩ R leaf := hPL.symm ▸ hx
          exact ⟨mem_forestCellUnion.mpr ⟨p, hp', Or.inl hxPR.1⟩, hxPR.2⟩
      have hLold : L leaf ⊆ discBd (forestCellUnion P R (S.erase leaf)) := by
        apply hboundary p hp' (L leaf) hLP
        intro v hv
        exact (hRsep (Finset.ne_of_mem_erase hv).symm).mono_left
          (fun x hx => (hPL.symm ▸ hx).2)
      obtain ⟨hdisc, _⟩ := attach_tree_leaf_discs hold hRl (hP leaf) hLl hKl
        hinter hRK hdisjoint hLold hLR hKR hKP
      have hunion : forestCellUnion P R S =
          forestCellUnion P R (S.erase leaf) ∪ R leaf ∪ P leaf := by
        ext x
        constructor
        · intro hx
          obtain ⟨v, hv, hxv⟩ := mem_forestCellUnion.mp hx
          by_cases hvl : v = leaf
          · subst v
            exact hxv.elim Or.inr (fun h => Or.inl (Or.inr h))
          · exact Or.inl (Or.inl (mem_forestCellUnion.mpr
              ⟨v, Finset.mem_erase.mpr ⟨hvl, hv⟩, hxv⟩))
        · intro hx
          rcases hx with (hx | hx) | hx
          · obtain ⟨v, hv, hxv⟩ := mem_forestCellUnion.mp hx
            exact mem_forestCellUnion.mpr ⟨v, Finset.mem_of_mem_erase hv, hxv⟩
          · exact mem_forestCellUnion.mpr ⟨leaf, hleaf, Or.inr hx⟩
          · exact mem_forestCellUnion.mpr ⟨leaf, hleaf, Or.inl hx⟩
      rw [hunion]
      refine ⟨hdisc, ?_⟩
      intro u hu A hA havoid
      have hAL : Disjoint A (L leaf) := (havoid leaf hleaf).mono_right
        (fun x hx => (hPL.symm ▸ hx).2)
      have hAK : Disjoint A (K leaf) := (havoid leaf hleaf).mono_right
        (fun x hx => (hRK.symm ▸ hx).1)
      by_cases hul : u = leaf
      · subst u
        exact new_boundary_survives_leaf_attachment hold hRl (hP leaf) hLl hKl
          hinter hRK hdisjoint hLold hLR hKR hKP hA hAK
      · have hAold := hboundary u (Finset.mem_erase.mpr ⟨hul, hu⟩) A hA
          (fun v hv => havoid v (Finset.mem_of_mem_erase hv))
        exact old_boundary_survives_leaf_attachment hold hRl (hP leaf) hLl hKl
          hinter hRK hdisjoint hLold hLR hKR hKP hAold hAL hAK
    · have hS : S = {root} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hroot, ?_⟩
        intro v hv
        by_contra hvr
        exact hother ⟨v, hv, hvr⟩
      subst S
      have heq : forestCellUnion P R {root} = P root := by
        simp only [forestCellUnion, Finset.mem_singleton, iUnion_iUnion_eq_left,
          hRroot, union_empty]
      rw [heq]
      refine ⟨hP root, ?_⟩
      intro u hu A hA _
      simpa only [Finset.mem_singleton.mp hu] using hA

end GraphMinor.LRPlanarity
