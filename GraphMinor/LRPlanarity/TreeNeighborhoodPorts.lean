module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPlacement
public import GraphMinor.LRPlanarity.DefsContour
import GraphMinor.Surface.PlaneOrientation
import GraphMinor.Surface.DiscUnion
import GraphMinor.LRPlanarity.TreeNeighborhoodCenterlines
import GraphMinor.LRPlanarity.TreeNeighborhoodInteriors

/-!
# Where straight cotree edges leave vertex polygons

Part IV, Section 7b of the planarity note cuts cotree edges at the vertex
facets. Along a prescribed outward normal, the polygon contains precisely
the part of the ray up to its radius. The endpoint of that part lies on
the polygon boundary. Distinct incidences have distinct facet points,
using the disjoint polygons and the distinct incident normals.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Along a prescribed unit normal, membership in a vertex polygon ends
exactly at the radius of its tangent circle. -/
theorem ray_point_mem_vertexPolygonAt_iff (center : ℂ) (directions : Finset ℝ)
    {r t μ : ℝ} (ht : 0 ≤ t) (hμ : μ ∈ directions) :
    center + t • eC μ ∈ vertexPolygonAt center directions r ↔ t ≤ r := by
  constructor
  · rintro ⟨z, hz, he⟩
    have hez : z = t • eC μ := add_left_cancel he
    rw [hez] at hz
    have hb : gf μ (t • eC μ) ≤ r := mem_iInter.mp (mem_iInter.mp hz.2 μ) hμ
    simpa only [gf_smul, gf_eC, sub_self, Real.cos_zero, mul_one] using hb
  · intro htr
    refine ⟨t • eC μ, ?_, rfl⟩
    apply closedBall_subset_vertexPolygon directions r
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht, norm_eC, mul_one]
    exact htr

/-- The crossing point on a prescribed facet is on the translated polygon
boundary. -/
theorem vertexPolygonAt_direction_mem_discBd (center : ℂ) (directions : Finset ℝ)
    {r μ : ℝ} (hr : 0 < r) (hμ : μ ∈ directions) :
    center + r • eC μ ∈ discBd (vertexPolygonAt center directions r) := by
  have hdisc := vertexPolygonAt_isClosedDisc center directions hr
  have hbd : discBd (vertexPolygonAt center directions r) =
      frontier (vertexPolygonAt center directions r) :=
    (subBd_eq_discBd_complex hdisc).symm.trans (Surface.subBd_eq_frontier _)
  rw [hbd]
  have hm := mem_image_of_mem (Homeomorph.addLeft center)
    (vertexPolygon_direction_mem_frontier directions hr hμ)
  rw [(Homeomorph.addLeft center).image_frontier] at hm
  exact hm

/-- The polygon cuts a straight incident edge in its initial radial segment,
and its frontier meets that edge at exactly the facet point. -/
theorem vertexPolygonAt_straight_edge_tail (center : ℂ) (directions : Finset ℝ)
    {μ r d : ℝ} (hr : 0 < r) (hrd : r < d) (hμ : μ ∈ directions) :
    vertexPolygonAt center directions r ∩ segment ℝ center (center + eC μ * (d : ℂ)) =
      segment ℝ center (center + r • eC μ) ∧
    frontier (vertexPolygonAt center directions r) ∩
      segment ℝ center (center + eC μ * (d : ℂ)) = {center + r • eC μ} := by
  have hd : 0 < d := hr.trans hrd
  have hsmul : ∀ t : ℝ, center + eC μ * (t : ℂ) = center + t • eC μ := by
    intro t
    rw [Complex.real_smul, mul_comm]
  have htail : vertexPolygonAt center directions r ∩
      segment ℝ center (center + eC μ * (d : ℂ)) = stripCenterline center μ 0 r := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, he⟩ := segment_subset_stripCenterline center μ hd.le hx.2
      dsimp only at he
      have hxP : center + t • eC μ ∈ vertexPolygonAt center directions r := by
        rw [← hsmul t, he]
        exact hx.1
      have htr := (ray_point_mem_vertexPolygonAt_iff center directions ht.1 hμ).mp hxP
      exact ⟨t, ⟨ht.1,htr⟩, he⟩
    · rintro x ⟨t, ht, rfl⟩
      refine ⟨?_, stripCenterline_subset_segment center μ hd le_rfl hrd.le ⟨t,ht,rfl⟩⟩
      change center + eC μ * (t : ℂ) ∈ vertexPolygonAt center directions r
      rw [hsmul]
      exact (ray_point_mem_vertexPolygonAt_iff center directions ht.1 hμ).mpr ht.2
  refine ⟨?_, ?_⟩
  · rw [htail, stripCenterline_eq_segment center μ hr.le]
    simp only [Complex.ofReal_zero, mul_zero, add_zero, hsmul]
  · apply Subset.antisymm
    · intro x hx
      have hxP : x ∈ vertexPolygonAt center directions r :=
        (vertexPolygonAt_isClosedDisc center directions hr).isCompact.isClosed.closure_eq ▸
          frontier_subset_closure hx.1
      have hxtail : x ∈ vertexPolygonAt center directions r ∩
          segment ℝ center (center + eC μ * (d : ℂ)) := ⟨hxP,hx.2⟩
      rw [htail] at hxtail
      obtain ⟨t, ht, he⟩ := hxtail
      dsimp only at he
      have htr : t = r := by
        apply le_antisymm ht.2
        apply le_of_not_gt
        intro hlt
        have hi := ray_point_mem_polygon_interior center directions μ ht.1 hlt
        exact disjoint_left.mp disjoint_interior_frontier (he ▸ hi) hx.1
      exact he.symm.trans ((congrArg (fun t : ℝ => center + eC μ * (t : ℂ)) htr).trans (hsmul r))
    · intro x hx
      subst x
      have hdisc := vertexPolygonAt_isClosedDisc center directions hr
      have hbd : discBd (vertexPolygonAt center directions r) =
          frontier (vertexPolygonAt center directions r) :=
        (subBd_eq_discBd_complex hdisc).symm.trans (Surface.subBd_eq_frontier _)
      refine ⟨hbd ▸ vertexPolygonAt_direction_mem_discBd center directions hr hμ, ?_⟩
      rw [← hsmul r]
      exact stripCenterline_subset_segment center μ hd le_rfl le_rfl
        ⟨r, ⟨hr.le,hrd.le⟩, rfl⟩

/-- Part IV, Section 7b: positive-radius facet points are distinct for all
incidences when polygons are disjoint and the normals at a vertex distinct. -/
theorem vertex_facet_points_injective {V : Type*} {G : SimpleGraph V}
    (point : V → ℂ) (angle : ∀ u, {v // G.Adj u v} → ℝ)
    (directions : V → Finset ℝ) (r : V → ℝ)
    (hr : ∀ u, 0 < r u) (hmem : ∀ u v, angle u v ∈ directions u)
    (hnormal : ∀ u, Function.Injective (fun v => eC (angle u v)))
    (hsep : Pairwise (fun u v => Disjoint
      (vertexPolygonAt (point u) (directions u) (r u))
      (vertexPolygonAt (point v) (directions v) (r v)))) :
    Function.Injective (fun e : {e : V × V // G.Adj e.1 e.2} =>
      point e.val.1 + r e.val.1 • eC (angle e.val.1 ⟨e.val.2, e.property⟩)) := by
  intro e f he
  dsimp only at he
  have hm : ∀ e : {e : V × V // G.Adj e.1 e.2},
      point e.val.1 + r e.val.1 • eC (angle e.val.1 ⟨e.val.2, e.property⟩) ∈
        vertexPolygonAt (point e.val.1) (directions e.val.1) (r e.val.1) := by
    intro e
    exact discBd_subset _ (vertexPolygonAt_direction_mem_discBd _ _ (hr _) (hmem _ _))
  have hsource : e.val.1 = f.val.1 := by
    by_contra hne
    exact disjoint_left.mp (hsep hne) (hm e) (he.symm ▸ hm f)
  obtain ⟨⟨u, v⟩, huv⟩ := e
  obtain ⟨⟨u', w⟩, huw⟩ := f
  dsimp only at hsource
  subst u'
  have hsmul := add_left_cancel he
  have hdir := (smul_right_injective ℂ (hr u).ne') hsmul
  have hneighbor := hnormal u hdir
  exact Subtype.ext (Prod.ext rfl (congrArg Subtype.val hneighbor))

/-- Back-edge ports represent distinct directed incidences. Opposite
orientations of a single edge cannot both be back edges, by strict depth. -/
theorem backEdge_port_incidence_injOn {N : ℕ} {T : Forest N}
    {G : SimpleGraph (Fin N)} :
    InjOn (fun p : Port N => if p.source then p.edge else (p.edge.2, p.edge.1))
      {p | T.BackEdge G p.edge} := by
  intro p hp q hq he
  obtain ⟨e, side⟩ := p
  obtain ⟨f, side'⟩ := q
  cases side <;> cases side'
  · have hs := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    simp only [Bool.false_eq_true, ite_false] at hs ht
    have hef : e = f := Prod.ext ht hs
    cases hef
    rfl
  · have hs := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    simp only [Bool.false_eq_true, ite_false, ite_true] at hs ht
    have hpe := hp.2.2.1
    change T.depth e.2 < T.depth e.1 at hpe
    rw [hs, ht] at hpe
    exact (Nat.lt_asymm hpe hq.2.2.1).elim
  · have hs := congrArg Prod.fst he
    have ht := congrArg Prod.snd he
    simp only [Bool.false_eq_true, ite_false, ite_true] at hs ht
    have hpe := hp.2.2.1
    change T.depth e.2 < T.depth e.1 at hpe
    rw [ht, hs] at hpe
    exact (Nat.lt_asymm hpe hq.2.2.1).elim
  · have hef : e = f := he
    cases hef
    rfl

end GraphMinor.LRPlanarity
