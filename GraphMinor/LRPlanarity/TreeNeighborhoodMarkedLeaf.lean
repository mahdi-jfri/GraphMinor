module

public import GraphMinor.LRPlanarity.TreeNeighborhoodMarkerGeometry
public import GraphMinor.LRPlanarity.TreeNeighborhoodPartialContour
import GraphMinor.LRPlanarity.TreeNeighborhoodLeafGeometry
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryReplacement
import GraphMinor.LRPlanarity.TreeNeighborhoodMarkedSplice
import GraphMinor.LRPlanarity.TreeNeighborhoodContourSplice
import GraphMinor.LRPlanarity.TreeNeighborhoodOrderedSplice
import GraphMinor.Surface.PlaneOrientation
import GraphMinor.Surface.DiscUnion

/-!
# The marked leaf step for the geometric contour

Part IV, Section 7b of the planarity note attaches a tube and a new vertex
polygon. Derive the local gluing configuration from the old parent-closed
union. Every old marker except the child label lies on the unchanged
boundary arc. The new vertex's legal markers lie on the detour. The marked
boundary substitution and the partial-contour list identity then give the
same new word, with a valid local rotation and the fixed root cut.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: one actual leaf attachment preserves the ordered
marked-boundary interpretation of the partial rooted contour. -/
theorem exists_marked_leaf_rotation {N : ℕ} {G : SimpleGraph (Fin N)} {T : Forest N}
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
    (leaf p : Fin N) (hleaf : leaf ∉ S) (hp : p ∈ S) (hparent : T.parent leaf = some p)
    (order : ContourOrder N) (hvalid : ValidContourOrder T G order)
    (base : ℂ) (hbase : ∀ v, base ∉ R v) (f : ℝ → ℂ) (before : ContourEvent N → ℝ)
    (hf : Continuous f) (hIco : InjOn f (Ico (0 : ℝ) 1)) (hIoc : InjOn f (Ioc (0 : ℝ) 1))
    (himage : f '' Icc (0 : ℝ) 1 = discBd (forestCellUnion P R S))
    (hzero : f 0 = base) (hone : f 1 = base)
    (hword : ∀ e, e ∈ partialVertexContour order S (N+1) root ↔ e ∈ partialContourEvents T G S)
    (hbefore : ∀ e ∈ partialVertexContour order S (N+1) root,
      before e ∈ Ioo (0 : ℝ) 1 ∧ f (before e) = contourMarker child port e)
    (hsorted : (partialVertexContour order S (N+1) root).Pairwise (fun e e' => before e < before e')) :
    ∃ (rotation : List (ContourEvent N)) (g : ℝ → ℂ) (after : ContourEvent N → ℝ),
      rotation.Perm (order leaf) ∧ Continuous g ∧
      InjOn g (Ico (0 : ℝ) 1) ∧ InjOn g (Ioc (0 : ℝ) 1) ∧
      g '' Icc (0 : ℝ) 1 = discBd (forestCellUnion P R (insert leaf S)) ∧ g 0 = base ∧ g 1 = base ∧
      (∀ e, e ∈ partialVertexContour (Function.update order leaf rotation) (insert leaf S) (N+1) root ↔
        e ∈ partialContourEvents T G (insert leaf S)) ∧
      (∀ e ∈ partialVertexContour (Function.update order leaf rotation) (insert leaf S) (N+1) root,
        after e ∈ Ioo (0 : ℝ) 1 ∧ g (after e) = contourMarker child port e) ∧
      (partialVertexContour (Function.update order leaf rotation) (insert leaf S) (N+1) root).Pairwise
        (fun e e' => after e < after e') := by
  classical
  let old := partialVertexContour order S (N+1) root
  let marker := contourMarker child port
  obtain ⟨hOld,hNR,hNP,hLN⟩ := cell_union_next_leaf_geometry hT root hroot P R L K a b c d
    hP hPsep hRnone hRsep hlocal haway S hrootS hancestor hclosed leaf p hleaf hp hparent
  obtain ⟨hRl,hLl,hKl,hPL,hRP,hLP,hLR,hKR,hKP⟩ := hlocal leaf p hparent
  obtain ⟨hNew,J,M,hJ,hM,hcover,hinter,hcover',hinter',h,k,hmatch,hfix,hdetour⟩ :=
    leaf_attachment_boundary_replacement hOld hRl (hP leaf) hLl hKl hNR hRP hNP hLN hLR hKR hKP
  have hnewset := forestCellUnion_insert P R S leaf
  rw [← hnewset] at hNew hcover' hmatch
  have hLsub : ∀ w v, T.parent w = some v → L w ⊆ R w := by
    intro w v hv x hx
    exact ((hlocal w v hv).2.2.2.1.symm ▸ hx).2
  have hchildR : ∀ w v, T.parent w = some v → child w ∈ R w :=
    fun w v hv => hLsub w v hv (hchild w v hv)
  have hchildFront : ∀ w v, T.parent w = some v → child w ∈ frontier (P v) := by
    intro w v hv
    have hbd : discBd (P v) = frontier (P v) :=
      (subBd_eq_discBd_complex (hP v)).symm.trans (Surface.subBd_eq_frontier _)
    exact hbd ▸ (hlocal w v hv).2.2.2.2.2.1 (hchild w v hv)
  have hRclosed : ∀ v, IsClosed (R v) := by
    intro v
    cases hv : T.parent v with
    | none => rw [hRnone v hv]; exact isClosed_empty
    | some u => exact (hlocal v u hv).1.isCompact.isClosed
  have hmarker : ContourEvent.child leaf ∈ old := (hword _).mpr
    ((child_mem_partialContourEvents_iff T G S leaf).mpr ⟨hleaf,p,hp,hparent⟩)
  have hold : ∀ e ∈ old, e ≠ ContourEvent.child leaf → marker e ∈ J ∧ marker e ∉ L leaf := by
    intro e he hne
    have hnotR := contourMarker_not_mem_other_tube T G R child port hRsep hchildR hportavoid
      S leaf ((hword e).mp he) hne
    have hnotL : marker e ∉ L leaf := fun hx => hnotR (hLsub leaf p hparent hx)
    have hcoord := hbefore e he
    have hm : marker e ∈ discBd (forestCellUnion P R S) := by
      have ht : before e ∈ Icc (0 : ℝ) 1 := ⟨hcoord.1.1.le, hcoord.1.2.le⟩
      have hx : f (before e) ∈ discBd (forestCellUnion P R S) :=
        himage ▸ mem_image_of_mem f ht
      rw [hcoord.2] at hx
      exact hx
    have hm' : marker e ∈ L leaf ∪ J := hcover.symm ▸ hm
    exact ⟨hm'.resolve_left hnotL,hnotL⟩
  let newLabels := (order leaf).toFinset
  have hlocalActive : ∀ e ∈ order leaf, e ∈ partialContourEvents T G (insert leaf S) := by
    intro e he
    exact (mem_partialContourEvents_insert_iff hT hvalid S hclosed leaf hleaf e).mpr (Or.inr he)
  have hnew : ∀ e ∈ newLabels, marker e ∈ M := by
    intro e he
    have heOrder : e ∈ order leaf := List.mem_toFinset.mp he
    have hmfront := contourMarker_mem_partial_frontier T G P R child port
      (fun v => (hP v).isCompact.isClosed) hRclosed hPsep hRsep
      (fun w v hv => ⟨hchildFront w v hv,hchildR w v hv⟩) hport hportavoid
      (insert leaf S) (hlocalActive e heOrder)
    have hnewbd : discBd (forestCellUnion P R (insert leaf S)) =
        frontier (forestCellUnion P R (insert leaf S)) :=
      (subBd_eq_discBd_complex hNew).symm.trans (Surface.subBd_eq_frontier _)
    have hmBd : marker e ∈ discBd (forestCellUnion P R (insert leaf S)) := hnewbd.symm ▸ hmfront
    have hmUnion : marker e ∈ J ∪ M := hcover'.symm ▸ hmBd
    have hmP : marker e ∈ P leaf := (hP leaf).isCompact.isClosed.closure_eq ▸
      frontier_subset_closure (contourMarker_mem_local_frontier hvalid P child port hchildFront hport leaf heOrder)
    have hmJ : marker e ∉ J := by
      intro hj
      have hmOld : marker e ∈ forestCellUnion P R S := discBd_subset _ (hcover ▸ Or.inr hj)
      exact disjoint_left.mp hNP hmOld hmP
    exact hmUnion.resolve_left hmJ
  have hnewinj : InjOn marker (newLabels : Set (ContourEvent N)) := by
    intro e he f hf heq
    exact contourMarker_injOn_partial_events T G R child port hRsep hchildR hportinj hportavoid
      (insert leaf S) (hlocalActive e (List.mem_toFinset.mp he))
      (hlocalActive f (List.mem_toFinset.mp hf)) heq
  have hzeroL : f 0 ∉ L leaf := by rw [hzero]; exact fun hm => hbase leaf (hLsub leaf p hparent hm)
  have honeL : f 1 ∉ L leaf := by rw [hone]; exact fun hm => hbase leaf (hLsub leaf p hparent hm)
  obtain ⟨rotation,g,after,hnd,hmem,hg,hgIco,hgIoc,hgimage,hcoords,hsort,_,hg0,hg1⟩ :=
    marked_boundary_interval_splice hLl hcover hmatch hfix hdetour old (ContourEvent.child leaf)
      marker before f hmarker (hchild leaf p hparent) hf hIco hIoc himage hzeroL honeL
      hbefore hsorted hold newLabels hnew hnewinj
  have hrotationMem : ∀ e, e ∈ rotation ↔ e ∈ order leaf :=
    fun e => (hmem e).trans List.mem_toFinset
  have hperm : rotation.Perm (order leaf) :=
    (List.perm_ext_iff_of_nodup hnd (hvalid leaf).1).mpr hrotationMem
  have hbudget : N ≤ T.depth root + (N+1) := Nat.le_succ_of_le (Nat.le_add_left N (T.depth root))
  have hsplice := partialVertexContour_insert_leaf hT hvalid S hclosed leaf hleaf rotation hperm
    (N+1) root hrootS hbudget
  refine ⟨rotation,g,after,hperm,hg,hgIco,hgIoc,hgimage,hg0.trans hzero,hg1.trans hone,?_,?_,?_⟩
  · intro e
    rw [hsplice,mem_marker_splice_iff old rotation (ContourEvent.child leaf) hmarker e,hword e,hrotationMem e]
    exact (mem_partialContourEvents_insert_iff hT hvalid S hclosed leaf hleaf e).symm
  · rw [hsplice]
    exact hcoords
  · rw [hsplice]
    exact hsort

end GraphMinor.LRPlanarity
