module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPartialEvents
public import GraphMinor.LRPlanarity.TreeNeighborhoodUnion
import GraphMinor.Surface.SurfaceGraph

/-!
# Markers on the boundary of a partial tree neighborhood

Part IV, Section 7b of the planarity note keeps each unattached child
interval on the current boundary and each back-edge port at its vertex
polygon. Child markers lie in distinct future tubes, and ports avoid all
tree tubes, so the markers are distinct. A point on a vertex-polygon
frontier that misses all included tubes stays on the union frontier,
because all other closed pieces miss a neighborhood of that point.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface Topology

/-- Boundary labels use a chosen point of the child attachment interval
and the source or target point of each back-edge port. -/
@[expose] def contourMarker {N : ℕ} (child : Fin N → ℂ) (port : Port N → ℂ) :
    ContourEvent N → ℂ
  | .child w => child w
  | .port p => port p

/-- A vertex-polygon boundary point outside every included tube remains on
the frontier of the partial union. -/
theorem vertex_frontier_mem_cell_union_frontier {N : ℕ} (P R : Fin N → Set ℂ)
    (hP : ∀ v, IsClosed (P v)) (hR : ∀ v, IsClosed (R v))
    (hsep : Pairwise (fun u v => Disjoint (P u) (P v)))
    (S : Finset (Fin N)) {u : Fin N} (hu : u ∈ S) {x : ℂ}
    (hx : x ∈ frontier (P u)) (havoid : ∀ v ∈ S, x ∉ R v) :
    x ∈ frontier (forestCellUnion P R S) := by
  classical
  let Rest := (⋃ v ∈ S.erase u, P v) ∪ ⋃ v ∈ S, R v
  have hRest : IsClosed Rest :=
    (isClosed_biUnion_finset fun v _ => hP v).union (isClosed_biUnion_finset fun v _ => hR v)
  have hxP : x ∈ P u := (hP u).closure_eq ▸ frontier_subset_closure hx
  have hxRest : x ∉ Rest := by
    intro hm
    rcases hm with hm | hm
    · obtain ⟨v,hv'⟩ := mem_iUnion.mp hm
      obtain ⟨hv,hxv⟩ := mem_iUnion.mp hv'
      exact disjoint_left.mp (hsep (Finset.ne_of_mem_erase hv).symm) hxP hxv
    · obtain ⟨v,hv'⟩ := mem_iUnion.mp hm
      obtain ⟨hv,hxv⟩ := mem_iUnion.mp hv'
      exact havoid v hv hxv
  have hcover : forestCellUnion P R S = P u ∪ Rest := by
    ext y
    constructor
    · intro hy
      obtain ⟨v,hv'⟩ := mem_iUnion.mp hy
      obtain ⟨hv,hyv⟩ := mem_iUnion.mp hv'
      rcases hyv with hyP | hyR
      · by_cases he : v = u
        · exact Or.inl (he ▸ hyP)
        · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨he,hv⟩,hyP⟩⟩))
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨hv,hyR⟩⟩))
    · intro hy
      rcases hy with hyP | (hyP | hyR)
      · exact mem_iUnion.mpr ⟨u,mem_iUnion.mpr ⟨hu,Or.inl hyP⟩⟩
      · obtain ⟨v,hv'⟩ := mem_iUnion.mp hyP
        obtain ⟨hv,hyv⟩ := mem_iUnion.mp hv'
        exact mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨Finset.mem_of_mem_erase hv,Or.inl hyv⟩⟩
      · obtain ⟨v,hv'⟩ := mem_iUnion.mp hyR
        obtain ⟨hv,hyv⟩ := mem_iUnion.mp hv'
        exact mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨hv,Or.inr hyv⟩⟩
  rw [frontier]
  refine ⟨subset_closure (hcover.symm ▸ Or.inl hxP),?_⟩
  intro hi
  have hnbhd := Filter.inter_mem (mem_interior_iff_mem_nhds.mp hi) (hRest.isOpen_compl.mem_nhds hxRest)
  have hsmall : forestCellUnion P R S ∩ Restᶜ ⊆ P u := by
    rw [hcover]
    intro y hy
    exact hy.1.elim id (fun h => (hy.2 h).elim)
  have hPnhds : P u ∈ 𝓝 x := Filter.mem_of_superset hnbhd hsmall
  exact disjoint_left.mp disjoint_interior_frontier (mem_interior_iff_mem_nhds.mpr hPnhds) hx

/-- Retained child markers and back-edge ports are injective on the partial
boundary label set, by tube separation and port avoidance. -/
theorem contourMarker_injOn_partial_events {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (R : Fin N → Set ℂ) (child : Fin N → ℂ) (port : Port N → ℂ)
    (hRsep : Pairwise (fun u v => Disjoint (R u) (R v)))
    (hchild : ∀ w v, T.parent w = some v → child w ∈ R w)
    (hportinj : InjOn port {p | T.BackEdge G p.edge})
    (hportavoid : ∀ p, T.BackEdge G p.edge → ∀ v, port p ∉ R v)
    (S : Finset (Fin N)) : InjOn (contourMarker child port) (partialContourEvents T G S : Set (ContourEvent N)) := by
  intro e he f hf heq
  cases e with
  | child w =>
    obtain ⟨_,v,_,hp⟩ := (child_mem_partialContourEvents_iff T G S w).mp he
    cases f with
    | child z =>
      dsimp only [contourMarker] at heq
      obtain ⟨_,u,_,hq⟩ := (child_mem_partialContourEvents_iff T G S z).mp hf
      have hwz : w = z := by
        by_contra hne
        exact disjoint_left.mp (hRsep hne) (hchild w v hp) (heq.symm ▸ hchild z u hq)
      exact congrArg ContourEvent.child hwz
    | port p =>
      dsimp only [contourMarker] at heq
      have hb := ((port_mem_partialContourEvents_iff T G S p).mp hf).1
      exact (hportavoid p hb w (heq ▸ hchild w v hp)).elim
  | port p =>
    have hb := ((port_mem_partialContourEvents_iff T G S p).mp he).1
    cases f with
    | child w =>
      dsimp only [contourMarker] at heq
      obtain ⟨_,v,_,hp⟩ := (child_mem_partialContourEvents_iff T G S w).mp hf
      exact (hportavoid p hb w (heq.symm ▸ hchild w v hp)).elim
    | port q =>
      dsimp only [contourMarker] at heq
      have hc := ((port_mem_partialContourEvents_iff T G S q).mp hf).1
      exact congrArg ContourEvent.port (hportinj hb hc heq)

/-- Every active marker lies on the actual partial neighborhood frontier. -/
theorem contourMarker_mem_partial_frontier {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (P R : Fin N → Set ℂ) (child : Fin N → ℂ) (port : Port N → ℂ)
    (hP : ∀ v, IsClosed (P v)) (hR : ∀ v, IsClosed (R v))
    (hPsep : Pairwise (fun u v => Disjoint (P u) (P v)))
    (hRsep : Pairwise (fun u v => Disjoint (R u) (R v)))
    (hchild : ∀ w v, T.parent w = some v → child w ∈ frontier (P v) ∧ child w ∈ R w)
    (hport : ∀ p, T.BackEdge G p.edge → port p ∈ frontier (P p.vertex))
    (hportavoid : ∀ p, T.BackEdge G p.edge → ∀ v, port p ∉ R v)
    (S : Finset (Fin N)) {event : ContourEvent N} (he : event ∈ partialContourEvents T G S) :
    contourMarker child port event ∈ frontier (forestCellUnion P R S) := by
  cases event with
  | child w =>
    obtain ⟨hw,v,hv,hp⟩ := (child_mem_partialContourEvents_iff T G S w).mp he
    apply vertex_frontier_mem_cell_union_frontier P R hP hR hPsep S hv (hchild w v hp).1
    intro u hu hmem
    have hwu : w ≠ u := fun h => hw (h.symm ▸ hu)
    exact disjoint_left.mp (hRsep hwu) (hchild w v hp).2 hmem
  | port p =>
    obtain ⟨hb,hv⟩ := (port_mem_partialContourEvents_iff T G S p).mp he
    exact vertex_frontier_mem_cell_union_frontier P R hP hR hPsep S hv (hport p hb)
      (fun v _ => hportavoid p hb v)

/-- Every legal local event is marked on its own vertex-polygon frontier. -/
theorem contourMarker_mem_local_frontier {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {order : ContourOrder N} (hvalid : ValidContourOrder T G order)
    (P : Fin N → Set ℂ) (child : Fin N → ℂ) (port : Port N → ℂ)
    (hchild : ∀ w v, T.parent w = some v → child w ∈ frontier (P v))
    (hport : ∀ p, T.BackEdge G p.edge → port p ∈ frontier (P p.vertex))
    (v : Fin N) {event : ContourEvent N} (he : event ∈ order v) :
    contourMarker child port event ∈ frontier (P v) := by
  cases event with
  | child w => exact hchild w v ((child_mem_valid_contour_iff hvalid v w).mp he)
  | port p =>
    have hp := (port_mem_valid_contour_iff hvalid v p).mp he
    have hm := hport p hp.1
    rw [hp.2] at hm
    exact hm

/-- Every old marker other than an unattached child's own label misses
that child's tube. -/
theorem contourMarker_not_mem_other_tube {N : ℕ} (T : Forest N) (G : SimpleGraph (Fin N))
    (R : Fin N → Set ℂ) (child : Fin N → ℂ) (port : Port N → ℂ)
    (hRsep : Pairwise (fun u v => Disjoint (R u) (R v)))
    (hchild : ∀ w v, T.parent w = some v → child w ∈ R w)
    (hportavoid : ∀ p, T.BackEdge G p.edge → ∀ v, port p ∉ R v)
    (S : Finset (Fin N)) (leaf : Fin N) {event : ContourEvent N}
    (he : event ∈ partialContourEvents T G S) (hne : event ≠ ContourEvent.child leaf) :
    contourMarker child port event ∉ R leaf := by
  cases event with
  | child w =>
    obtain ⟨_,v,_,hp⟩ := (child_mem_partialContourEvents_iff T G S w).mp he
    have hwl : w ≠ leaf := fun h => hne (congrArg ContourEvent.child h)
    exact fun hm => disjoint_left.mp (hRsep hwl) (hchild w v hp) hm
  | port p => exact hportavoid p ((port_mem_partialContourEvents_iff T G S p).mp he).1 leaf

end GraphMinor.LRPlanarity
