module

public import GraphMinor.LRPlanarity.TreeNeighborhoodMarkedLeaf
import GraphMinor.LRPlanarity.TreeNeighborhoodRootMarkers
import GraphMinor.LRPlanarity.TreeNeighborhoodContourSplice
import GraphMinor.LRPlanarity.TreeNeighborhoodLeafOrder
import GraphMinor.Surface.PlaneOrientation

/-!
# Ordered boundary markers on a finite rooted subtree

Part IV, Section 7b of the planarity note reads the boundary while adding
one leaf at a time. Start with the root's boundary order. Remove a deepest
leaf for the induction, then insert its local rotation by the marked leaf
step. Local orders outside the subtree retain their original values.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: every finite parent-closed rooted subtree admits
valid local orders whose partial contour reads its boundary markers in
order. The hypotheses describe the individual polygons, tubes, and ports. -/
theorem exists_marked_subtree_order {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
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
    (child : Fin N → ℂ) (port : Port N → ℂ)
    (hchild : ∀ w v, T.parent w = some v → child w ∈ L w)
    (hport : ∀ p, T.BackEdge G p.edge → port p ∈ frontier (P p.vertex))
    (hportinj : InjOn port {p | T.BackEdge G p.edge})
    (hportavoid : ∀ p, T.BackEdge G p.edge → ∀ v, port p ∉ R v)
    (S : Finset (Fin N)) (hrootS : root ∈ S) (hancestor : ∀ v ∈ S, T.Ancestor root v)
    (hclosed : ∀ v ∈ S, ∀ p, T.parent v = some p → p ∈ S)
    (initial : ContourOrder N) (hinitial : ValidContourOrder T G initial) :
    ∃ (order : ContourOrder N) (base : ℂ) (f : ℝ → ℂ) (parameter : ContourEvent N → ℝ),
      ValidContourOrder T G order ∧ (∀ v, v ∉ S → order v = initial v) ∧
      (∀ v, base ∉ R v) ∧ Continuous f ∧
      InjOn f (Ico (0 : ℝ) 1) ∧ InjOn f (Ioc (0 : ℝ) 1) ∧
      f '' Icc (0 : ℝ) 1 = discBd (forestCellUnion P R S) ∧ f 0 = base ∧ f 1 = base ∧
      (∀ e, e ∈ partialVertexContour order S (N+1) root ↔ e ∈ partialContourEvents T G S) ∧
      (∀ e ∈ partialVertexContour order S (N+1) root,
        parameter e ∈ Ioo (0 : ℝ) 1 ∧ f (parameter e) = contourMarker child port e) ∧
      (partialVertexContour order S (N+1) root).Pairwise (fun e e' => parameter e < parameter e') := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    have hparent : ∀ v ∈ S, v ≠ root → ∃ p ∈ S, T.parent v = some p := by
      intro v hv hne
      obtain ⟨p,_,hp⟩ := ancestor_parent_of_ne (hancestor v hv) hne
      exact ⟨p,hclosed v hv p hp,hp⟩
    by_cases hother : ∃ w ∈ S, w ≠ root
    · obtain ⟨leaf,hleaf,hlr,hchildless,hroot',hanc',hpar'⟩ :=
        exists_leaf_erase_subtree hT root S hrootS hancestor hparent hother
      have hclosed' : ∀ v ∈ S.erase leaf, ∀ p, T.parent v = some p → p ∈ S.erase leaf := by
        intro v hv p hp
        have hpS := hclosed v (Finset.mem_of_mem_erase hv) p hp
        have hpl : p ≠ leaf := fun he => hchildless v (Finset.mem_of_mem_erase hv) (he ▸ hp)
        exact Finset.mem_erase.mpr ⟨hpl,hpS⟩
      obtain ⟨order,base,f,θ,hvalid,houtside,hbase,hf,hIco,hIoc,himage,hzero,hone,hword,hcoords,hsort⟩ :=
        ih (S.erase leaf) (Finset.erase_ssubset hleaf) hroot' hanc' hclosed'
      obtain ⟨p,hp,hparentleaf⟩ := hparent leaf hleaf hlr
      have hpl : p ≠ leaf := fun he => hchildless leaf hleaf (he ▸ hparentleaf)
      have hp' : p ∈ S.erase leaf := Finset.mem_erase.mpr ⟨hpl,hp⟩
      obtain ⟨rotation,g,after,hperm,hg,hgIco,hgIoc,hgimage,hgzero,hgone,hgword,hgcoords,hgsort⟩ :=
        exists_marked_leaf_rotation hT root hroot P R L K a b c d hP hPsep hRnone hRsep hlocal haway
          child port hchild hport hportinj hportavoid (S.erase leaf) hroot' hanc' hclosed'
          leaf p (Finset.notMem_erase leaf S) hp' hparentleaf order hvalid base hbase f θ
          hf hIco hIoc himage hzero hone hword hcoords hsort
      have hset : insert leaf (S.erase leaf) = S := Finset.insert_erase hleaf
      rw [hset] at hgimage hgword hgcoords hgsort
      refine ⟨Function.update order leaf rotation,base,g,after,
        validContourOrder_update_of_perm hvalid leaf hperm,?_,hbase,hg,hgIco,hgIoc,
        hgimage,hgzero,hgone,hgword,hgcoords,hgsort⟩
      intro v hv
      have hvl : v ≠ leaf := fun he => hv (he ▸ hleaf)
      rw [Function.update_of_ne hvl]
      exact houtside v (fun hm => hv (Finset.mem_of_mem_erase hm))
    · have hS : S = {root} := by
        ext v
        simp only [Finset.mem_singleton]
        constructor
        · intro hv
          by_contra hne
          exact hother ⟨v,hv,hne⟩
        · intro he
          exact he ▸ hrootS
      subst S
      have hbd : discBd (P root) = frontier (P root) :=
        (subBd_eq_discBd_complex (hP root)).symm.trans (Surface.subBd_eq_frontier _)
      obtain ⟨base,rotation,f,θ,_,hbase,hperm,hf,hIco,hIoc,himage,hzero,hone,hcoords,hsort⟩ :=
        exists_root_marker_order hinitial P R L child port hP hRsep hRnone haway
          (fun w v hv => ⟨a w,b w,(hlocal w v hv).2.1⟩)
          (fun w v hv => (hlocal w v hv).2.2.2.1)
          (fun w v hv => by
            have hbdv : discBd (P v) = frontier (P v) :=
              (subBd_eq_discBd_complex (hP v)).symm.trans (Surface.subBd_eq_frontier _)
            exact hbdv ▸ (hlocal w v hv).2.2.2.2.2.1)
          hchild hport hportinj hportavoid root hroot
      let order := Function.update initial root rotation
      have hvalid : ValidContourOrder T G order := validContourOrder_update_of_perm hinitial root hperm
      have hpartial : partialVertexContour order {root} (N+1) root = rotation := by
        rw [partialVertexContour_singleton_root hvalid root hroot N]
        exact Function.update_self root rotation initial
      have hcell : forestCellUnion P R {root} = P root := by
        simp [forestCellUnion,hRnone root hroot]
      refine ⟨order,base,f,θ,hvalid,?_,hbase,hf,hIco,hIoc,?_,hzero,hone,?_,?_,?_⟩
      · intro v hv
        exact Function.update_of_ne (fun he => hv (Finset.mem_singleton.mpr he)) rotation initial
      · rw [hcell,hbd]
        exact himage
      · intro e
        rw [partialVertexContour_singleton_root hvalid root hroot N]
        exact (mem_partialContourEvents_singleton_iff hvalid root hroot e).symm
      · rw [hpartial]
        exact hcoords
      · rw [hpartial]
        exact hsort

end GraphMinor.LRPlanarity
