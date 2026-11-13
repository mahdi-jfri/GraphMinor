module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPartialContour
import GraphMinor.LRPlanarity.TreeNeighborhoodContourForest
import Mathlib.Data.List.Perm.Basic

/-!
# Substituting a newly attached leaf contour

Part IV, Section 7b of the planarity note replaces the child incidence
at an attachment by that child's boundary contour. A partial contour
retains child markers outside the included tree. Adding one vertex and
choosing its new local rotation substitutes that rotation at its marker.
The other local orders are unchanged. This file proves that list identity
with the exact finite fuel used by the contour specification.
-/

public section
namespace GraphMinor.LRPlanarity

/-- Reordering one local incidence list preserves the validity conditions. -/
theorem validContourOrder_update_of_perm {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    {order : ContourOrder N} (hvalid : ValidContourOrder T G order) (v : Fin N)
    {rotation : List (ContourEvent N)} (hperm : rotation.Perm (order v)) :
    ValidContourOrder T G (Function.update order v rotation) := by
  classical
  intro w
  by_cases hw : w = v
  · subst w
    rw [Function.update_self]
    exact ⟨hperm.nodup_iff.mpr (hvalid v).1,fun e => hperm.mem_iff.trans ((hvalid v).2 e)⟩
  · rw [Function.update_of_ne hw]
    exact hvalid w

/-- Part IV, Section 7b: adding one vertex to a parent-closed partial tree
substitutes its new local rotation for the retained child marker. -/
theorem partialVertexContour_insert_leaf {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)}
    (hT : T.IsDFS G) {order : ContourOrder N} (hvalid : ValidContourOrder T G order)
    (S : Finset (Fin N)) (hclosed : ∀ v ∈ S, ∀ u, T.parent v = some u → u ∈ S)
    (leaf : Fin N) (hleaf : leaf ∉ S) (rotation : List (ContourEvent N))
    (hperm : rotation.Perm (order leaf)) (fuel : ℕ) (v : Fin N) (hv : v ∈ S)
    (hfuel : N ≤ T.depth v + fuel) :
    partialVertexContour (Function.update order leaf rotation) (insert leaf S) fuel v =
      (partialVertexContour order S fuel v).flatMap
        (fun event => if event = ContourEvent.child leaf then rotation else [event]) := by
  classical
  let updated := Function.update order leaf rotation
  let replace := fun event => if event = ContourEvent.child leaf then rotation else [event]
  have hvalid' : ValidContourOrder T G updated := validContourOrder_update_of_perm hvalid leaf hperm
  have hchildren : ∀ w, T.parent w = some leaf → w ∉ insert leaf S := by
    intro w hp hw
    rcases Finset.mem_insert.mp hw with he | hwS
    · subst w
      have hdepth := (hT.2.1 leaf leaf hp).2
      exact Nat.ne_of_lt (Nat.lt_succ_self (T.depth leaf)) hdepth
    · exact hleaf (hclosed w hwS leaf hp)
  have hleafword : ∀ n, 0 < n → partialVertexContour updated (insert leaf S) n leaf = rotation := by
    intro n hn
    cases n with
    | zero => exact (Nat.not_lt_zero _ hn).elim
    | succ n =>
      rw [partialVertexContour,show updated leaf = rotation from Function.update_self leaf rotation order]
      calc
        rotation.flatMap _ = rotation.flatMap (fun event => [event]) := by
          apply List.flatMap_congr
          intro event he
          have he' : event ∈ updated leaf := by simpa only [updated,Function.update_self] using he
          cases event with
          | child w =>
            have hp := (child_mem_valid_contour_iff hvalid' leaf w).mp he'
            dsimp only
            rw [ite_eq_right (hchildren w hp)]
          | port p => rfl
        _ = rotation := by simp
  change partialVertexContour updated (insert leaf S) fuel v =
    (partialVertexContour order S fuel v).flatMap replace
  induction fuel generalizing v with
  | zero => rfl
  | succ fuel ih =>
    have hvleaf : v ≠ leaf := fun he => hleaf (he ▸ hv)
    have horder : updated v = order v := Function.update_of_ne hvleaf _ _
    have hbudget : ∀ w, T.parent w = some v → N ≤ T.depth w + fuel := by
      intro w hp
      rw [(hT.2.1 v w hp).2,Nat.add_assoc,Nat.add_comm 1 fuel]
      exact hfuel
    rw [partialVertexContour,partialVertexContour,horder,List.flatMap_assoc]
    apply List.flatMap_congr
    intro event he
    cases event with
    | child w =>
      have hp := (child_mem_valid_contour_iff hvalid v w).mp he
      dsimp only
      by_cases hwl : w = leaf
      · subst w
        rw [ite_eq_left (Finset.mem_insert_self _ _),ite_eq_right hleaf]
        have hpositive : 0 < fuel := by
          by_contra hn
          have hf0 : fuel = 0 := Nat.eq_zero_of_not_pos hn
          have hbound := hbudget leaf hp
          rw [hf0,Nat.add_zero] at hbound
          exact (not_le_of_gt (dfs_depth_lt_card hT leaf)) hbound
        rw [hleafword fuel hpositive]
        simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,replace,ite_true]
      · by_cases hw : w ∈ S
        · rw [ite_eq_left (Finset.mem_insert_of_mem hw),ite_eq_left hw]
          exact ih w hw (hbudget w hp)
        · have hw' : w ∉ insert leaf S := by simpa only [Finset.mem_insert,not_or] using And.intro hwl hw
          rw [ite_eq_right hw',ite_eq_right hw]
          simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,replace,
            ContourEvent.child.injEq,hwl,ite_false]
    | port p =>
      dsimp only
      simp [replace]

end GraphMinor.LRPlanarity
