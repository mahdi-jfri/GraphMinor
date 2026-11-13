module

public import GraphMinor.LRPlanarity.DefsContour
public import GraphMinor.LRPlanarity.TreeNeighborhoodContourRecursion

/-!
# Contours before all tree leaves are attached

Part IV, Section 7b of the planarity note adds one vertex polygon and
strip at a time. Before a child is attached, its incidence remains one
boundary marker. Once attached, that marker expands to the child's local
contour. This partial recursion records precisely those substitutions.
When the included set contains the whole rooted subtree, only ports
remain and the recursion is the specified vertex contour.
-/

public section
namespace GraphMinor.LRPlanarity

/-- The descendant vertex used to locate an emitted child or port marker. -/
@[expose] def ContourEvent.vertex {N : ℕ} : ContourEvent N → Fin N
  | .child w => w
  | .port p => p.vertex

/-- Part IV, Section 7b: expand included children and retain one marker for
each child whose polygon has not been attached. -/
@[expose] def partialVertexContour {N : ℕ} (order : ContourOrder N) (S : Finset (Fin N)) :
    ℕ → Fin N → List (ContourEvent N)
  | 0, _ => []
  | fuel + 1, v => (order v).flatMap fun event => match event with
    | .child w => if w ∈ S then partialVertexContour order S fuel w else [.child w]
    | .port p => [.port p]

/-- Every emitted partial-contour marker belongs below the recursion root. -/
theorem partialVertexContour_ancestor {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {order : ContourOrder N} (hvalid : ValidContourOrder T G order) (S : Finset (Fin N))
    (fuel : ℕ) (v : Fin N) {event : ContourEvent N}
    (hevent : event ∈ partialVertexContour order S fuel v) : T.Ancestor v event.vertex := by
  induction fuel generalizing v with
  | zero => simp only [partialVertexContour,List.not_mem_nil] at hevent
  | succ fuel ih =>
    obtain ⟨e,he,hblock⟩ := List.mem_flatMap.mp hevent
    cases e with
    | child w =>
      have hp := (child_mem_valid_contour_iff hvalid v w).mp he
      by_cases hw : w ∈ S
      · simp only [hw,ite_true] at hblock
        exact Relation.ReflTransGen.head hp (ih w hblock)
      · simp only [hw,ite_false] at hblock
        have heq : event = ContourEvent.child w := List.mem_singleton.mp hblock
        subst event
        exact Relation.ReflTransGen.single hp
    | port p =>
      have heq : event = ContourEvent.port p := List.mem_singleton.mp hblock
      subst event
      have hp := (port_mem_valid_contour_iff hvalid v p).mp he
      change T.Ancestor v p.vertex
      rw [hp.2]
      exact Relation.ReflTransGen.refl

/-- A parent-closed finite set contains every ancestor of each of its vertices. -/
theorem ancestor_mem_parent_closed {N : ℕ} {T : Forest N} {S : Finset (Fin N)}
    (hclosed : ∀ v ∈ S, ∀ u, T.parent v = some u → u ∈ S)
    {u v : Fin N} (h : T.Ancestor u v) (hv : v ∈ S) : u ∈ S := by
  induction h with
  | refl => exact hv
  | @tail p v hprefix hp ih => exact ih (hclosed v hv p hp)

/-- Once all descendants are included, the partial contour consists
exactly of the port events in the specified vertex contour. -/
theorem partialVertexContour_eq_port_map {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {order : ContourOrder N} (hvalid : ValidContourOrder T G order) (S : Finset (Fin N))
    (fuel : ℕ) (v : Fin N) (hinclude : ∀ w, T.Ancestor v w → w ∈ S) :
    partialVertexContour order S fuel v = (vertexContour order fuel v).map ContourEvent.port := by
  induction fuel generalizing v with
  | zero => rfl
  | succ fuel ih =>
    rw [partialVertexContour,vertexContour,List.map_flatMap]
    apply List.flatMap_congr
    intro event he
    cases event with
    | child w =>
      have hp := (child_mem_valid_contour_iff hvalid v w).mp he
      dsimp only
      rw [ite_eq_left (hinclude w (Relation.ReflTransGen.single hp))]
      exact ih w (fun x hx => hinclude x (Relation.ReflTransGen.head hp hx))
    | port p => rfl

/-- Before attaching any child, the root polygon's partial word is its
local incidence list, for every positive fuel. -/
theorem partialVertexContour_singleton_root {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {order : ContourOrder N} (hvalid : ValidContourOrder T G order)
    (root : Fin N) (hroot : T.parent root = none) (fuel : ℕ) :
    partialVertexContour order {root} (fuel+1) root = order root := by
  rw [partialVertexContour]
  calc
    (order root).flatMap _ = (order root).flatMap (fun event => [event]) := by
      apply List.flatMap_congr
      intro event he
      cases event with
      | child w =>
        have hp := (child_mem_valid_contour_iff hvalid root w).mp he
        have hwr : w ≠ root := by
          intro hw
          rw [hw,hroot] at hp
          cases hp
        have hwS : w ∉ ({root} : Finset (Fin N)) := by simpa only [Finset.mem_singleton] using hwr
        dsimp only
        rw [ite_eq_right hwS]
      | port p => rfl
    _ = order root := by simp

end GraphMinor.LRPlanarity
