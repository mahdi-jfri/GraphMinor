module

public import GraphMinor.GM06.Section5CurveCount

/-!
# Counting before the auxiliary curve enters its return

In VI (5.5), page 132, the auxiliary curve first follows the old
prefix and then its return. Vertex times strictly before the join
are the first-half images of the old prefix's vertex times with its
terminal parameter removed. The join is a vertex, so its removal
reduces the finite count by exactly one.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The vertex times before the middle of a concatenation are the
first-half images of the first path's vertex times before its end. -/
theorem earlier_vertex_hits_path_trans
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x v y : S}
    (p : Path x v) (q : Path v y) :
    curveVertexHits G (p.trans q).toContinuousMap ∩ Iio (leftHalfTime 1) =
      leftHalfTime '' (curveVertexHits G p.toContinuousMap \ {1}) := by
  ext t
  constructor
  · rintro ⟨ht, htlt⟩
    rw [curveVertexHits_path_trans] at ht
    rcases ht with ⟨s, hs, hst⟩ | ⟨s, hs, hst⟩
    · refine ⟨s, ⟨hs, ?_⟩, hst⟩
      intro hs1
      have he : leftHalfTime 1 = t := mem_singleton_iff.mp hs1 ▸ hst
      have htne : t ≠ leftHalfTime 1 := ne_of_lt htlt
      exact htne he.symm
    · rw [← hst] at htlt
      change ((s : ℝ) + 1) / 2 < (1 : ℝ) / 2 at htlt
      linarith only [htlt, s.2.1]
  · rintro ⟨s, ⟨hs, hs1⟩, hst⟩
    refine ⟨?_, ?_⟩
    · rw [curveVertexHits_path_trans]
      exact Or.inl ⟨s, hs, hst⟩
    · rw [← hst]
      have hslt : s < 1 := lt_of_le_of_ne le_top (fun h => hs1 (mem_singleton_iff.mpr h))
      have hslt' : (s : ℝ) < 1 := hslt
      change (s : ℝ) / 2 < (1 : ℝ) / 2
      linarith only [hslt']

/-- The count before the auxiliary return, plus its joining vertex,
is exactly the old-prefix count in VI (5.5), page 132. -/
theorem earlier_vertex_hits_path_trans_ncard
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x v y : S}
    (p : Path x v) (q : Path v y) (hv : v ∈ G.V)
    (hp : (curveVertexHits G p.toContinuousMap).Finite) :
    (curveVertexHits G (p.trans q).toContinuousMap ∩ Iio (leftHalfTime 1)).ncard + 1 =
      curveL G p.toContinuousMap := by
  have hEnd : (1 : unitInterval) ∈ curveVertexHits G p.toContinuousMap := by
    change p 1 ∈ G.V
    rw [Path.target]
    exact hv
  rw [earlier_vertex_hits_path_trans, ncard_image_of_injective _ leftHalfTime_injective]
  exact ncard_sdiff_singleton_add_one hEnd hp

end GraphMinor.GM06
