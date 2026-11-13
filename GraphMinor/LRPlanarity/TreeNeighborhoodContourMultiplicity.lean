module

public import GraphMinor.LRPlanarity.DefsContour
import GraphMinor.LRPlanarity.TreeNeighborhoodContourRecursion
import GraphMinor.LRPlanarity.TreeNeighborhoodContourForest
import GraphMinor.LRPlanarity.TreeNeighborhoodForest
import Mathlib.Data.List.Nodup

/-!
# Every contour port occurs exactly once

Part IV, Section 7b of the planarity note substitutes each child contour
once into a valid local order. Distinct children have disjoint descendant
sets, and a vertex port belongs to none of those child subtrees. Thus the
substituted lists are disjoint and contain no repetitions. Distinct roots
also have disjoint descendant sets. Concatenating the root contours gives
exactly one source and one target token for every back edge.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Part IV, Section 7b: a valid local-order recursion emits no port twice. -/
theorem vertexContour_nodup {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    (hT : T.IsDFS G) {order : ContourOrder N} (hvalid : ValidContourOrder T G order)
    (fuel : ℕ) (v : Fin N) (hfuel : N ≤ T.depth v + fuel) :
    (vertexContour order fuel v).Nodup := by
  induction fuel generalizing v with
  | zero => simp [vertexContour]
  | succ fuel ih =>
    have hbudget : ∀ w, T.parent w = some v → N ≤ T.depth w + fuel := by
      intro w hp
      rw [(hT.2.1 v w hp).2,Nat.add_assoc,Nat.add_comm 1 fuel]
      exact hfuel
    let block := fun event : ContourEvent N => match event with
      | .child w => vertexContour order fuel w
      | .port p => [p]
    change ((order v).flatMap block).Nodup
    apply List.nodup_flatMap.mpr
    constructor
    · intro event he
      cases event with
      | child w => exact ih w (hbudget w ((child_mem_valid_contour_iff hvalid v w).mp he))
      | port p => exact List.nodup_singleton p
    · apply (hvalid v).1.pairwise_of_forall_ne
      intro e he f hf hne
      change (block e).Disjoint (block f)
      rw [List.disjoint_left]
      intro p hpe hpf
      cases e with
      | child w =>
        have hw := (child_mem_valid_contour_iff hvalid v w).mp he
        have hdesc := ((mem_vertexContour_iff hT hvalid fuel w (hbudget w hw) p).mp hpe).2
        cases f with
        | child z =>
          have hz := (child_mem_valid_contour_iff hvalid v z).mp hf
          have hdesc' := ((mem_vertexContour_iff hT hvalid fuel z (hbudget z hz) p).mp hpf).2
          have heq : w = z := equal_depth_ancestors_eq hT hdesc hdesc'
            ((hT.2.1 v w hw).2.trans (hT.2.1 v z hz).2.symm)
          exact hne (congrArg ContourEvent.child heq)
        | port q =>
          have hpq : p = q := List.mem_singleton.mp hpf
          have hq := (port_mem_valid_contour_iff hvalid v q).mp hf
          have hle := ancestor_depth_le hT hdesc
          rw [hpq,hq.2,(hT.2.1 v w hw).2] at hle
          exact Nat.not_succ_le_self _ hle
      | port q =>
        have hpq : p = q := List.mem_singleton.mp hpe
        have hq := (port_mem_valid_contour_iff hvalid v q).mp he
        cases f with
        | child w =>
          have hw := (child_mem_valid_contour_iff hvalid v w).mp hf
          have hdesc := ((mem_vertexContour_iff hT hvalid fuel w (hbudget w hw) p).mp hpf).2
          have hle := ancestor_depth_le hT hdesc
          rw [hpq,hq.2,(hT.2.1 v w hw).2] at hle
          exact Nat.not_succ_le_self _ hle
        | port r =>
          have hpr : p = r := List.mem_singleton.mp hpf
          exact hne (congrArg ContourEvent.port (hpq.symm.trans hpr))

/-- Part IV, Section 7b: the specified whole-forest contour is a port word
for every valid local order. Its finite fuel suffices, and roots have
disjoint port sets. -/
theorem isPortWord_of_validContourOrder {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    (hT : T.IsDFS G) {order : ContourOrder N} (hvalid : ValidContourOrder T G order) :
    IsPortWord T G (contourWord T order) := by
  classical
  let roots := (Finset.univ.filter (fun v => T.parent v = none)).sort (· ≤ ·)
  have hrootmem : ∀ v, v ∈ roots ↔ T.parent v = none := by
    intro v
    simp only [roots,Finset.mem_sort,Finset.mem_filter,Finset.mem_univ,true_and]
  have hrootsnd : roots.Nodup := Finset.sort_nodup _ _
  have hbudget : ∀ v, N ≤ T.depth v + (N + 1) :=
    fun v => Nat.le_succ_of_le (Nat.le_add_left N (T.depth v))
  change (roots.flatMap (vertexContour order (N + 1))).Nodup ∧ _
  constructor
  · apply List.nodup_flatMap.mpr
    refine ⟨fun v _ => vertexContour_nodup hT hvalid (N+1) v (hbudget v),?_⟩
    apply hrootsnd.pairwise_of_forall_ne
    intro u hu v hv huv
    change (vertexContour order (N+1) u).Disjoint (vertexContour order (N+1) v)
    rw [List.disjoint_left]
    intro p hpu hpv
    have hancu := ((mem_vertexContour_iff hT hvalid (N+1) u (hbudget u) p).mp hpu).2
    have hancv := ((mem_vertexContour_iff hT hvalid (N+1) v (hbudget v) p).mp hpv).2
    exact huv (equal_depth_ancestors_eq hT hancu hancv
      ((hT.1 u ((hrootmem u).mp hu)).trans (hT.1 v ((hrootmem v).mp hv)).symm))
  · intro p
    change p ∈ roots.flatMap (vertexContour order (N+1)) ↔ T.BackEdge G p.edge
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨root,_,hp⟩
      exact ((mem_vertexContour_iff hT hvalid (N+1) root (hbudget root) p).mp hp).1
    · intro hb
      obtain ⟨root,hroot,hanc⟩ := exists_root_ancestor hT p.vertex
      exact ⟨root,(hrootmem root).mpr hroot,
        (mem_vertexContour_iff hT hvalid (N+1) root (hbudget root) p).mpr ⟨hb,hanc⟩⟩

end GraphMinor.LRPlanarity
