module

public import GraphMinor.GM06.Defs
public import Mathlib.Topology.Subpath

/-!
# Vertex counts on subpaths

The helix surgery in VI (5.5), pages 131–132, divides a curve at its
last region and vertex times. A nonconstant affine change of parameter
is injective. Its image on the vertex-hit set is exactly the set of
old vertex times in the chosen interval. This gives finite counts
and their exact values without counting repeated endpoint pauses.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The affine parameter map of a nondegenerate subpath is injective. -/
theorem convexComb_injective_of_ne {a b : unitInterval} (hab : a ≠ b) :
    Function.Injective (Icc.convexComb a b) := by
  intro s t h
  have he := congrArg Subtype.val h
  apply Subtype.ext
  apply mul_right_cancel₀ (show (b : ℝ) - a ≠ 0 from sub_ne_zero.mpr
    (fun h => hab (Subtype.ext h.symm)))
  change (1 - (s : ℝ)) * a + s * b = (1 - (t : ℝ)) * a + t * b at he
  nlinarith only [he]

/-- Vertex times of a subpath correspond exactly to the old vertex
times in its parameter interval. This is used in VI (5.5), page 132. -/
theorem image_vertex_hits_subpath
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y : S}
    (p : Path x y) (a b : unitInterval) :
    Icc.convexComb a b '' curveVertexHits G (p.subpath a b).toContinuousMap =
      curveVertexHits G p.toContinuousMap ∩ uIcc a b := by
  change Icc.convexComb a b '' ((Icc.convexComb a b) ⁻¹' curveVertexHits G p.toContinuousMap) = _
  rw [image_preimage_eq_inter_range, Path.range_subpathAux]

/-- A nondegenerate subpath has as many vertex hits as the original
curve has in the chosen closed interval, in VI (5.5), page 132. -/
theorem curveL_subpath
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y : S}
    (p : Path x y) {a b : unitInterval} (hab : a ≠ b)
    (hf : (curveVertexHits G p.toContinuousMap).Finite) :
    (curveVertexHits G (p.subpath a b).toContinuousMap).Finite ∧
      curveL G (p.subpath a b).toContinuousMap =
        (curveVertexHits G p.toContinuousMap ∩ uIcc a b).ncard := by
  have hi := convexComb_injective_of_ne hab
  have hfin : (curveVertexHits G (p.subpath a b).toContinuousMap).Finite := by
    change ((Icc.convexComb a b) ⁻¹' curveVertexHits G p.toContinuousMap).Finite
    exact Set.Finite.preimage hi.injOn hf
  refine ⟨hfin, ?_⟩
  rw [curveL, ← image_vertex_hits_subpath p a b]
  exact (ncard_image_of_injective _ hi).symm

/-- A suffix ending away from the vertices has the same interval
count even when its two parameters coincide. This includes the
terminal last-visit case of VI (5.5), page 131. -/
theorem curveL_subpath_of_end_not_vertex
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y : S}
    (p : Path x y) (a b : unitInterval) (hb : p b ∉ G.V)
    (hf : (curveVertexHits G p.toContinuousMap).Finite) :
    (curveVertexHits G (p.subpath a b).toContinuousMap).Finite ∧
      curveL G (p.subpath a b).toContinuousMap =
        (curveVertexHits G p.toContinuousMap ∩ uIcc a b).ncard := by
  by_cases hab : a = b
  · subst b
    have hset : curveVertexHits G (p.subpath a a).toContinuousMap = ∅ := by
      ext t
      change p (Icc.convexComb a a t) ∈ G.V ↔ False
      rw [Icc.convexComb_eq]
      exact iff_false_intro hb
    have hinterval : curveVertexHits G p.toContinuousMap ∩ uIcc a a = ∅ := by
      ext t
      simp only [uIcc_self, mem_inter_iff, mem_singleton_iff, mem_empty_iff_false]
      apply iff_false_intro
      rintro ⟨htV, rfl⟩
      exact hb htV
    refine ⟨hset ▸ finite_empty, ?_⟩
    rw [curveL, hset, hinterval]
  · exact curveL_subpath p hab hf

/-- Strict interior subpath parameters lie strictly between the
two cut times, as used for the last-vertex condition in VI (5.5). -/
theorem convexComb_mem_Ioo_of_lt {a b : unitInterval} (hab : a < b)
    {t : unitInterval} (ht : t ∈ Ioo (0 : unitInterval) 1) :
    Icc.convexComb a b t ∈ Ioo a b := by
  have hdiff : (0 : ℝ) < (b : ℝ) - a := sub_pos.mpr hab
  have ht0 : (0 : ℝ) < t := ht.1
  have ht1 : (t : ℝ) < 1 := ht.2
  have hp := mul_pos ht0 hdiff
  have hq := mul_pos (sub_pos.mpr ht1) hdiff
  constructor
  · change (a : ℝ) < (1 - (t : ℝ)) * a + t * b
    nlinarith only [hp]
  · change (1 - (t : ℝ)) * a + t * b < (b : ℝ)
    nlinarith only [hq]

/-- Restricting a normal curve to a linearly parametrized subpath
preserves normality, as for the two old helix pieces in VI (5.5). -/
theorem isNormalCurve_path_subpath
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y : S}
    (p : Path x y) (hp : IsNormalCurve G p.toContinuousMap) (a b : unitInterval) :
    IsNormalCurve G (p.subpath a b).toContinuousMap := by
  rintro z ⟨⟨t, rfl⟩, htU⟩
  exact hp ⟨mem_range_self (Icc.convexComb a b t), htU⟩

end GraphMinor.GM06
