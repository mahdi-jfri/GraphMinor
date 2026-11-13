module

public import GraphMinor.LRPlanarity.DefsContour
import GraphMinor.LRPlanarity.TreeNeighborhoodContourForest

/-!
# Ports emitted by the rooted contour recursion

Part IV, opening and Section 7b of the planarity note places each source
or target token at its incident vertex, then substitutes child contours.
A valid local order therefore emits exactly the ports incident with the
rooted subtree. The search-depth bound ensures that the finite fuel in
the specified contour definition suffices for every child substitution.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Part IV, opening: the source token is at the source of its edge, and
the target token is at its target. -/
@[expose] def Port.vertex {N : ℕ} (p : Port N) : Fin N :=
  if p.source then p.edge.1 else p.edge.2

/-- Membership of a child incidence in a valid local contour order. -/
theorem child_mem_valid_contour_iff {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {order : ContourOrder N} (hvalid : ValidContourOrder T G order) (v w : Fin N) :
    ContourEvent.child w ∈ order v ↔ T.parent w = some v := (hvalid v).2 _

/-- Membership of a source or target token in a valid local contour order. -/
theorem port_mem_valid_contour_iff {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {order : ContourOrder N} (hvalid : ValidContourOrder T G order) (v : Fin N) (p : Port N) :
    ContourEvent.port p ∈ order v ↔ T.BackEdge G p.edge ∧ p.vertex = v := by
  have h := (hvalid v).2 (ContourEvent.port p)
  cases hs : p.source <;> simpa only [Port.vertex,hs,Bool.false_eq_true,ite_false,ite_true] using h

/-- Part IV, Section 7b: with sufficient fuel, the rooted contour contains
exactly the back-edge ports attached to descendants of its root. -/
theorem mem_vertexContour_iff {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    (hT : T.IsDFS G) {order : ContourOrder N} (hvalid : ValidContourOrder T G order)
    (fuel : ℕ) (v : Fin N) (hfuel : N ≤ T.depth v + fuel) (p : Port N) :
    p ∈ vertexContour order fuel v ↔ T.BackEdge G p.edge ∧ T.Ancestor v p.vertex := by
  induction fuel generalizing v with
  | zero =>
    have hbad : N ≤ T.depth v := by simpa only [Nat.add_zero] using hfuel
    exact ((not_le_of_gt (dfs_depth_lt_card hT v)) hbad).elim
  | succ fuel ih =>
    have hbudget : ∀ w, T.parent w = some v → N ≤ T.depth w + fuel := by
      intro w hp
      rw [(hT.2.1 v w hp).2,Nat.add_assoc,Nat.add_comm 1 fuel]
      exact hfuel
    rw [vertexContour,List.mem_flatMap]
    constructor
    · rintro ⟨event,he,hp⟩
      cases event with
      | child w =>
        have hw := (child_mem_valid_contour_iff hvalid v w).mp he
        obtain ⟨hb,hanc⟩ := (ih w (hbudget w hw)).mp hp
        exact ⟨hb,Relation.ReflTransGen.head hw hanc⟩
      | port q =>
        have heq : p = q := List.mem_singleton.mp hp
        subst p
        have hq := (port_mem_valid_contour_iff hvalid v q).mp he
        refine ⟨hq.1,?_⟩
        rw [hq.2]
        exact Relation.ReflTransGen.refl
    · rintro ⟨hb,hanc⟩
      rcases hanc.cases_head with heq | ⟨w,hparent,hdesc⟩
      · refine ⟨ContourEvent.port p,?_,List.mem_singleton_self p⟩
        exact (port_mem_valid_contour_iff hvalid v p).mpr ⟨hb,heq.symm⟩
      · refine ⟨ContourEvent.child w,(child_mem_valid_contour_iff hvalid v w).mpr hparent,?_⟩
        exact (ih w (hbudget w hparent)).mpr ⟨hb,hdesc⟩

end GraphMinor.LRPlanarity
