module

public import GraphMinor.GM06.Defs

/-!
# Counting the endpoint contacts of an approach curve

The approach curves in VI (5.5), page 131, miss the drawing at all
interior parameters. Their only vertex times are therefore their
endpoints that are vertices. Starting at an initial vertex gives
one contact, and a vertex join gives one more. The count uses
parameter times, so it also counts both ends of a returning curve.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

open Classical in
/-- An approach starting at a drawing vertex and missing all vertices
in its interior has one vertex time, plus its terminal vertex time.
This counts the approach pieces in VI (5.5), page 131. -/
theorem curveL_of_interior_disjoint_vertices
    {S : Type*} [TopologicalSpace S] {G : Drawing S} (f : Curve S)
    (hstart : f 0 ∈ G.V)
    (hinterior : ∀ t : unitInterval, 0 < t → t < 1 → f t ∉ G.V) :
    (curveVertexHits G f).Finite ∧
      curveL G f = 1 + (if f 1 ∈ G.V then 1 else 0) := by
  classical
  have hsub : curveVertexHits G f ⊆ ({0, 1} : Set unitInterval) := by
    intro t ht
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    · by_cases ht1 : t = 1
      · exact Or.inr ht1
      · exact (hinterior t (lt_of_le_of_ne bot_le (Ne.symm ht0))
          (lt_of_le_of_ne le_top ht1) ht).elim
  have hfin : (curveVertexHits G f).Finite :=
    ((finite_singleton (1 : unitInterval)).insert 0).subset hsub
  refine ⟨hfin, ?_⟩
  by_cases hend : f 1 ∈ G.V
  · have hset : curveVertexHits G f = {0, 1} := by
      apply subset_antisymm hsub
      rintro t (rfl | ht)
      · exact hstart
      · exact ht ▸ hend
    rw [curveL, hset, ncard_pair (by norm_num : (0 : unitInterval) ≠ 1), ite_eq_left hend]
  · have hset : curveVertexHits G f = {0} := by
      apply subset_antisymm
      · intro t ht
        rcases hsub ht with ht0 | ht1
        · exact ht0
        · exact (hend (ht1 ▸ ht)).elim
      · rintro t rfl
        exact hstart
    rw [curveL, hset, ncard_singleton, ite_eq_right hend]

open Classical in
/-- The endpoint count also applies when the interior misses the
whole drawing, as for the replacement approach in VI (5.5). -/
theorem curveL_of_interior_disjoint_drawing
    {S : Type*} [TopologicalSpace S] {G : Drawing S} (f : Curve S)
    (hstart : f 0 ∈ G.V)
    (hinterior : ∀ t : unitInterval, 0 < t → t < 1 → f t ∉ G.U) :
    (curveVertexHits G f).Finite ∧
      curveL G f = 1 + (if f 1 ∈ G.V then 1 else 0) := by
  exact curveL_of_interior_disjoint_vertices f hstart
    (fun t ht0 ht1 htV => hinterior t ht0 ht1 (G.V_subset_U htV))

/-- If its terminal point is a vertex or misses the drawing, the
approach curve is normal as required in VI (5.5), page 131. -/
theorem isNormalCurve_of_interior_disjoint_drawing
    {S : Type*} [TopologicalSpace S] {G : Drawing S} (f : Curve S)
    (hstart : f 0 ∈ G.V) (hend : f 1 ∈ G.V ∨ f 1 ∉ G.U)
    (hinterior : ∀ t : unitInterval, 0 < t → t < 1 → f t ∉ G.U) :
    IsNormalCurve G f := by
  rintro x ⟨⟨t, rfl⟩, htG⟩
  by_cases ht0 : t = 0
  · exact ht0 ▸ hstart
  · by_cases ht1 : t = 1
    · rcases hend with hv | hno
      · exact ht1 ▸ hv
      · exact (hno (ht1 ▸ htG)).elim
    · exact (hinterior t (lt_of_le_of_ne bot_le (Ne.symm ht0))
        (lt_of_le_of_ne le_top ht1) htG).elim

end GraphMinor.GM06
