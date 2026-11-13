module

public import GraphMinor.LRPlanarity.TreeNeighborhoodMarkerGeometry
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryGap
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryPorts
import GraphMinor.Surface.DiscMerge
import GraphMinor.Surface.Triangulate
import GraphMinor.Surface.PlaneOrientation
import GraphMinor.Surface.SurfaceGraph

/-!
# Initial root boundary markers and a fixed cut corner

Part IV, opening and Section 7b of the planarity note chooses a root cut
corner and reads its local incidences around the vertex polygon. Choose
the cut outside the disjoint child intervals and port points, then sort
the markers along the boundary traversal. Every other tree tube avoids
the root polygon. Thus this cut misses all tree tubes, and later leaf
attachments keep it fixed.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: initialize the root's local boundary order at a
cut point avoiding all tree tubes. The hypotheses concern individual
vertex discs, parent tubes, their exact intervals, and the port points. -/
theorem exists_root_marker_order {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {order : ContourOrder N} (hvalid : ValidContourOrder T G order)
    (P R L : Fin N → Set ℂ) (child : Fin N → ℂ) (port : Port N → ℂ)
    (hP : ∀ v, IsClosedDisc (P v))
    (hRsep : Pairwise (fun u v => Disjoint (R u) (R v)))
    (hRnone : ∀ v, T.parent v = none → R v = ∅)
    (hRaway : ∀ v p, T.parent v = some p → ∀ w, w ≠ v → w ≠ p → Disjoint (R v) (P w))
    (hline : ∀ w v, T.parent w = some v → ∃ a b, IsLineWithEnds (L w) a b)
    (hinter : ∀ w v, T.parent w = some v → P v ∩ R w = L w)
    (hLbd : ∀ w v, T.parent w = some v → L w ⊆ frontier (P v))
    (hchild : ∀ w v, T.parent w = some v → child w ∈ L w)
    (hport : ∀ p, T.BackEdge G p.edge → port p ∈ frontier (P p.vertex))
    (hportinj : InjOn port {p | T.BackEdge G p.edge})
    (hportavoid : ∀ p, T.BackEdge G p.edge → ∀ v, port p ∉ R v)
    (root : Fin N) (hroot : T.parent root = none) :
    ∃ (base : ℂ) (rotation : List (ContourEvent N)) (f : ℝ → ℂ) (parameter : ContourEvent N → ℝ),
      base ∈ frontier (P root) ∧ (∀ v, base ∉ R v) ∧ rotation.Perm (order root) ∧
      Continuous f ∧ InjOn f (Ico (0 : ℝ) 1) ∧ InjOn f (Ioc (0 : ℝ) 1) ∧
      f '' Icc (0 : ℝ) 1 = frontier (P root) ∧ f 0 = base ∧ f 1 = base ∧
      (∀ e ∈ rotation, parameter e ∈ Ioo (0 : ℝ) 1 ∧ f (parameter e) = contourMarker child port e) ∧
      rotation.Pairwise (fun e e' => parameter e < parameter e') := by
  classical
  let marker := contourMarker child port
  let piece : ContourEvent N → Set ℂ := fun e => match e with
    | .child w => L w
    | .port p => {port p}
  have hLsub : ∀ w v, T.parent w = some v → L w ⊆ R w := by
    intro w v hp x hx
    exact (hinter w v hp).symm ▸ hx |>.2
  have hchildR : ∀ w v, T.parent w = some v → child w ∈ R w :=
    fun w v hp => hLsub w v hp (hchild w v hp)
  have hbd : discBd (P root) = frontier (P root) :=
    (subBd_eq_discBd_complex (hP root)).symm.trans (Surface.subBd_eq_frontier _)
  have hcircle : IsOArc (frontier (P root)) := hbd ▸ (hP root).isOArc_discBd
  have hpieceClosed : ∀ e ∈ order root, IsClosed (piece e) := by
    intro e he
    cases e with
    | child w =>
      obtain ⟨a,b,hl⟩ := hline w root ((child_mem_valid_contour_iff hvalid root w).mp he)
      exact hl.isCompact.isClosed
    | port p => exact isClosed_singleton
  have hpieceSub : ∀ e ∈ order root, piece e ⊆ frontier (P root) := by
    intro e he
    cases e with
    | child w => exact hLbd w root ((child_mem_valid_contour_iff hvalid root w).mp he)
    | port p =>
      have hp := (port_mem_valid_contour_iff hvalid root p).mp he
      intro x hx
      have heq : x = port p := hx
      subst x
      have hm := hport p hp.1
      rw [hp.2] at hm
      exact hm
  have hpieceMarker : ∀ e ∈ order root, marker e ∈ piece e := by
    intro e he
    cases e with
    | child w => exact hchild w root ((child_mem_valid_contour_iff hvalid root w).mp he)
    | port p => exact mem_singleton _
  have hpieceSep : ∀ e ∈ order root, ∀ f ∈ order root, e ≠ f → Disjoint (piece e) (piece f) := by
    intro e he f hf hne
    cases e with
    | child w =>
      have hw := (child_mem_valid_contour_iff hvalid root w).mp he
      cases f with
      | child z =>
        have hz := (child_mem_valid_contour_iff hvalid root z).mp hf
        have hwz : w ≠ z := fun h => hne (congrArg ContourEvent.child h)
        exact (hRsep hwz).mono (hLsub w root hw) (hLsub z root hz)
      | port p =>
        have hp := (port_mem_valid_contour_iff hvalid root p).mp hf
        change Disjoint (L w) {port p}
        rw [disjoint_singleton_right]
        exact fun hm => hportavoid p hp.1 w (hLsub w root hw hm)
    | port p =>
      have hp := (port_mem_valid_contour_iff hvalid root p).mp he
      cases f with
      | child w =>
        have hw := (child_mem_valid_contour_iff hvalid root w).mp hf
        change Disjoint {port p} (L w)
        rw [disjoint_singleton_left]
        exact fun hm => hportavoid p hp.1 w (hLsub w root hw hm)
      | port q =>
        have hq := (port_mem_valid_contour_iff hvalid root q).mp hf
        change Disjoint {port p} {port q}
        rw [disjoint_singleton_left]
        intro hm
        have heq : port p = port q := hm
        exact hne (congrArg ContourEvent.port (hportinj hp.1 hq.1 heq))
  have hproper : ∀ e ∈ order root, ¬frontier (P root) ⊆ piece e := by
    intro e he
    cases e with
    | child w =>
      obtain ⟨a,b,hl⟩ := hline w root ((child_mem_valid_contour_iff hvalid root w).mp he)
      exact circle_not_subset_boundary_line hcircle hl (hpieceSub _ he)
    | port p =>
      intro hcover
      exact isOArc_infinite hcircle ((Set.finite_singleton (port p)).subset hcover)
  let E := {e : ContourEvent N // e ∈ order root}
  have hcircleNe : (frontier (P root)).Nonempty := by
    obtain ⟨φ⟩ := hcircle
    exact ⟨φ 1,(φ 1).property⟩
  obtain ⟨base,hbase,hbaseOutside⟩ := exists_point_outside_disjoint_closed_pieces
    (frontier (P root)) hcircle.isPreconnected hcircleNe (fun e : E => piece e.val)
    (fun e => hpieceClosed e.val e.property)
    (fun e f hne => hpieceSep e.val e.property f.val f.property (fun h => hne (Subtype.ext h)))
    (fun e => hproper e.val e.property)
  have hbaseP : base ∈ P root := (hP root).isCompact.isClosed.closure_eq ▸ frontier_subset_closure hbase
  have hbaseR : ∀ v, base ∉ R v := by
    intro v hvR
    cases hp : T.parent v with
    | none => simp only [hRnone v hp,mem_empty_iff_false] at hvR
    | some p =>
      by_cases hpr : p = root
      · subst p
        have he : ContourEvent.child v ∈ order root := (child_mem_valid_contour_iff hvalid root v).mpr hp
        have hm : base ∈ P root ∩ R v := ⟨hbaseP,hvR⟩
        have hL : base ∈ L v := hinter v root hp ▸ hm
        exact hbaseOutside ⟨ContourEvent.child v,he⟩ hL
      · have hvr : v ≠ root := by
          intro he
          rw [he,hroot] at hp
          cases hp
        exact disjoint_left.mp (hRaway v p hp root hvr.symm (Ne.symm hpr)) hvR hbaseP
  have hmarkerInj : Function.Injective (fun e : E => marker e.val) := by
    intro e f he
    apply Subtype.ext
    apply contourMarker_injOn_partial_events T G R child port hRsep hchildR hportinj hportavoid {root}
    · exact (mem_partialContourEvents_singleton_iff hvalid root hroot e.val).mpr e.property
    · exact (mem_partialContourEvents_singleton_iff hvalid root hroot f.val).mpr f.property
    · exact he
  have hmarkerC : ∀ e : E, marker e.val ∈ frontier (P root) :=
    fun e => hpieceSub e.val e.property (hpieceMarker e.val e.property)
  have hbaseNotMarker : base ∉ range (fun e : E => marker e.val) := by
    rintro ⟨e,he⟩
    exact hbaseOutside e (he ▸ hpieceMarker e.val e.property)
  obtain ⟨word,f,θ,hnd,hall,hf,hIco,hIoc,himage,hzero,hone,hθ,hsorted⟩ :=
    exists_ordered_boundary_ports_at hcircle (fun e : E => marker e.val) hmarkerInj hmarkerC
      base hbase hbaseNotMarker
  let rotation := word.map Subtype.val
  let parameter := fun e => if he : e ∈ order root then θ ⟨e,he⟩ else 0
  have hparam : ∀ e : E, parameter e.val = θ e := fun e => dite_eq_left e.property
  have hmem : ∀ e, e ∈ rotation ↔ e ∈ order root := by
    intro e
    constructor
    · intro he
      obtain ⟨q,_,hqe⟩ := List.mem_map.mp he
      exact hqe ▸ q.property
    · intro he
      exact List.mem_map.mpr ⟨⟨e,he⟩,hall ⟨e,he⟩,rfl⟩
  have hperm : rotation.Perm (order root) :=
    (List.perm_ext_iff_of_nodup (hnd.map Subtype.val_injective) (hvalid root).1).mpr hmem
  refine ⟨base,rotation,f,parameter,hbase,hbaseR,hperm,hf,hIco,hIoc,himage,hzero,hone,?_,?_⟩
  · intro e he
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp he
    rw [hparam q]
    exact hθ q
  · apply List.pairwise_map.mpr
    apply hsorted.imp
    intro e e' he
    simpa only [hparam e,hparam e'] using he

end GraphMinor.LRPlanarity
