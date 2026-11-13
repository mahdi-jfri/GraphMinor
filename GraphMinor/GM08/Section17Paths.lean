module

public import GraphMinor.GM08.Section15Menger
public import GraphMinor.GM07.Defs
import GraphMinor.GM11.Walks
import GraphMinor.GM08.Section9NestLinkage

/-!
# Comparing the two cylinder linkage counts

The boundary-linking condition in VIII uses skeleton paths. Lift each
walk to the drawing and take its path drawing. Its vertices are exactly
the walk support, so disjointness is preserved. These paths give the
maximum-path bounds required by VII (9.3).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Skeleton linkage gives the path-drawing count used in VII (9.3),
as needed in the proof of VIII (17.2), page 284. -/
theorem hasDisjointPathsBetween_of_skeleton_paths {S : Type w} [TopologicalSpace S] [T1Space S]
    (Γ : Drawing S) {A B : Set S} {n : ℕ}
    (h : HasDisjointPaths Γ.toHypergraph.skeleton (Γ.V ∩ A) (Γ.V ∩ B) n) :
    GM07.HasDisjointPathsBetween Γ A B n := by
  classical
  obtain ⟨Q, hQ⟩ := h
  have hw : ∀ i : Fin n, ∃ W : GraphWalk Γ.toGraph (Q i).first (Q i).last,
      W.support = (Q i).walk.support := fun i =>
    exists_graphWalk_of_skeleton_walk Γ (Q i).first_mem.1 (Q i).walk
  choose W hW using hw
  refine ⟨fun i => GM11.walkDrawing Γ (W i), fun i => (Q i).first,
    fun i => (Q i).last, ?_, ?_⟩
  · intro i
    refine ⟨GM11.walkDrawing_isSubdrawing Γ (W i), (Q i).first_mem.2,
      (Q i).last_mem.2, GM11.walkDrawing_isPathBetween Γ ?_⟩
    change (W i).support.Nodup
    rw [hW]
    exact (Q i).isPath.support_nodup
  · intro i j hij
    rw [GM11.walkDrawing_V, GM11.walkDrawing_V, hW, hW]
    exact hQ hij

/-- Skeleton linkage gives the lower bound on VII's maximum path count. -/
theorem le_maxDisjointPaths_of_skeleton_paths {S : Type w} [TopologicalSpace S] [T1Space S]
    (Γ : Drawing S) {A B : Set S} {n : ℕ}
    (h : HasDisjointPaths Γ.toHypergraph.skeleton (Γ.V ∩ A) (Γ.V ∩ B) n) :
    n ≤ GM07.maxDisjointPaths Γ A B :=
  le_maxDisjointPaths_of_paths (hasDisjointPathsBetween_of_skeleton_paths Γ h)

/-- Paths of a subdrawing remain paths of the full drawing, with the
same vertex disjointness and endpoint sets. -/
theorem hasDisjointPathsBetween_of_isSubdrawing {S : Type w} [TopologicalSpace S]
    {Γ Δ : Drawing S} (hsub : Δ.IsSubdrawing Γ) {A B : Set S} {n : ℕ}
    (h : GM07.HasDisjointPathsBetween Δ A B n) :
    GM07.HasDisjointPathsBetween Γ A B n := by
  obtain ⟨P, a, b, hP, hdis⟩ := h
  exact ⟨P, a, b, fun i => ⟨(hP i).1.trans hsub,
    (hP i).2.1, (hP i).2.2.1, (hP i).2.2.2⟩, hdis⟩

end GraphMinor.GM08
