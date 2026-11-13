module

public import GraphMinor.GM06.Defs

/-!
# Vertex contacts under concatenation

The curve replacements in VI (5.5), pages 131–132, reparametrize
two curves into the two halves of the interval. Their vertex-hit
sets become injective images. Those images meet only at the join,
and contain the join exactly when its point is a vertex. Taking
finite cardinalities gives the vertex-count addition formula.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface unitInterval
/-- Embed a parameter interval in the first half of a concatenation
as used in VI (5.5), page 131. -/
@[expose] noncomputable def leftHalfTime (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2, by constructor <;> linarith only [t.2.1, t.2.2]⟩
/-- Embed a parameter interval in the second half of a concatenation
as used in VI (5.5), page 131. -/
@[expose] noncomputable def rightHalfTime (t : unitInterval) : unitInterval :=
  ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith only [t.2.1, t.2.2]⟩
/-- The first-half reparametrization is injective. -/
theorem leftHalfTime_injective : Function.Injective leftHalfTime := by
  intro s t he
  have hh := congrArg Subtype.val he
  apply Subtype.ext
  change (s : ℝ) / 2 = (t : ℝ) / 2 at hh
  linarith only [hh]
/-- The second-half reparametrization is injective. -/
theorem rightHalfTime_injective : Function.Injective rightHalfTime := by
  intro s t he
  have hh := congrArg Subtype.val he
  apply Subtype.ext
  change ((s : ℝ) + 1) / 2 = ((t : ℝ) + 1) / 2 at hh
  linarith only [hh]
/-- The two half-interval maps meet at the join. -/
theorem rightHalfTime_zero : rightHalfTime 0 = leftHalfTime 1 := by
  apply Subtype.ext
  change ((0 : ℝ) + 1) / 2 = 1 / 2
  norm_num
/-- Concatenation at a first-half parameter evaluates the first path. -/
theorem path_trans_leftHalfTime {S : Type*} [TopologicalSpace S] {x v y : S}
    (p : Path x v) (q : Path v y) (s : unitInterval) :
    (p.trans q) (leftHalfTime s) = p s := by
  rw [Path.trans_apply, dite_eq_left (by
    change (s : ℝ) / 2 ≤ 1 / 2
    linarith only [s.2.2])]
  congr 1
  apply Subtype.ext
  change 2 * ((s : ℝ) / 2) = s
  ring
/-- Concatenation at a second-half parameter evaluates the second path. -/
theorem path_trans_rightHalfTime {S : Type*} [TopologicalSpace S] {x v y : S}
    (p : Path x v) (q : Path v y) (s : unitInterval) :
    (p.trans q) (rightHalfTime s) = q s := by
  by_cases hs : s = 0
  · rw [hs, rightHalfTime_zero, path_trans_leftHalfTime, Path.target, Path.source]
  · rw [Path.trans_apply, dite_eq_right (by
      change ¬ ((s : ℝ) + 1) / 2 ≤ 1 / 2
      have hp : (0 : ℝ) < s := unitInterval.pos_iff_ne_zero.mpr hs
      linarith only [hp])]
    congr 1
    apply Subtype.ext
    change 2 * (((s : ℝ) + 1) / 2) - 1 = s
    ring
/-- The vertex-hit set of a concatenation is the union of the two reparametrized hit sets. -/
theorem curveVertexHits_path_trans {S : Type*} [TopologicalSpace S] {G : Drawing S} {x v y : S}
    (p : Path x v) (q : Path v y) :
    curveVertexHits G (p.trans q).toContinuousMap =
      leftHalfTime '' curveVertexHits G p.toContinuousMap ∪
        rightHalfTime '' curveVertexHits G q.toContinuousMap := by
  ext t
  constructor
  · intro ht
    change (p.trans q) t ∈ G.V at ht
    rw [Path.trans_apply] at ht
    split_ifs at ht with hthalf
    · apply Or.inl
      refine ⟨⟨2 * (t : ℝ), (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, hthalf⟩⟩, ht, ?_⟩
      apply Subtype.ext
      change (2 * (t : ℝ)) / 2 = t
      ring
    · apply Or.inr
      refine ⟨⟨2 * (t : ℝ) - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hthalf).le, t.2.2⟩⟩, ht, ?_⟩
      apply Subtype.ext
      change (2 * (t : ℝ) - 1 + 1) / 2 = t
      ring
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · change (p.trans q) (leftHalfTime s) ∈ G.V
      rw [path_trans_leftHalfTime]
      exact hs
    · change (p.trans q) (rightHalfTime s) ∈ G.V
      rw [path_trans_rightHalfTime]
      exact hs
end GraphMinor.GM06

namespace GraphMinor.GM06
open Set GraphMinor.Surface unitInterval
open Classical in
/-- The finite vertex counts of a concatenation add, with one correction
when the joining point is a vertex. This is the counting step used in VI (5.5), pages 131–132. -/
theorem curveL_path_trans_add {S : Type*} [TopologicalSpace S] {G : Drawing S} {x v y : S}
    (p : Path x v) (q : Path v y)
    (hp : (curveVertexHits G p.toContinuousMap).Finite)
    (hq : (curveVertexHits G q.toContinuousMap).Finite) :
    (curveVertexHits G (p.trans q).toContinuousMap).Finite ∧
      curveL G (p.trans q).toContinuousMap + (if v ∈ G.V then 1 else 0) =
        curveL G p.toContinuousMap + curveL G q.toContinuousMap := by
  classical
  let A := leftHalfTime '' curveVertexHits G p.toContinuousMap
  let B := rightHalfTime '' curveVertexHits G q.toContinuousMap
  have hAf : A.Finite := hp.image leftHalfTime
  have hBf : B.Finite := hq.image rightHalfTime
  have hinter : A ∩ B = if v ∈ G.V then {leftHalfTime 1} else ∅ := by
    have hsub : A ∩ B ⊆ {leftHalfTime 1} := by
      rintro t ⟨⟨s, hs, hst⟩, ⟨u, hu, hut⟩⟩
      have hh := congrArg Subtype.val (hst.trans hut.symm)
      change (s : ℝ) / 2 = ((u : ℝ) + 1) / 2 at hh
      have hs1 : s = 1 := by
        apply Subtype.ext
        change (s : ℝ) = 1
        linarith only [hh, s.2.2, u.2.1]
      rw [← hst, hs1]
      rfl
    by_cases hv : v ∈ G.V
    · rw [ite_eq_left hv]
      apply hsub.antisymm
      rintro t rfl
      refine ⟨⟨1, ?_, rfl⟩, ⟨0, ?_, rightHalfTime_zero⟩⟩
      · change p 1 ∈ G.V
        rw [Path.target]
        exact hv
      · change q 0 ∈ G.V
        rw [Path.source]
        exact hv
    · rw [ite_eq_right hv]
      apply subset_empty_iff.mp
      rintro t ht
      have htmid := hsub ht
      have htmid' : t = leftHalfTime 1 := htmid
      obtain ⟨s, hs, hst⟩ := ht.1
      have hs1 : s = 1 := leftHalfTime_injective (hst.trans htmid')
      change p s ∈ G.V at hs
      rw [hs1, Path.target] at hs
      exact hv hs
  have hcard := ncard_union_add_ncard_inter A B hAf hBf
  have hAcard : A.ncard = curveL G p.toContinuousMap := ncard_image_of_injective _ leftHalfTime_injective
  have hBcard : B.ncard = curveL G q.toContinuousMap := ncard_image_of_injective _ rightHalfTime_injective
  have hintercard : (A ∩ B).ncard = if v ∈ G.V then 1 else 0 := by
    rw [hinter]
    split_ifs <;> simp only [ncard_singleton, ncard_empty]
  have heq : curveVertexHits G (p.trans q).toContinuousMap = A ∪ B := curveVertexHits_path_trans p q
  refine ⟨heq.symm ▸ hAf.union hBf, ?_⟩
  change (curveVertexHits G (p.trans q).toContinuousMap).ncard + _ = _
  rw [heq, ← hAcard, ← hBcard, ← hintercard]
  exact hcard
end GraphMinor.GM06

namespace GraphMinor.GM06
open Set GraphMinor.Surface
/-- The first-half parameter embedding is continuous. -/
theorem continuous_leftHalfTime : Continuous leftHalfTime := by
  have h : Continuous (fun t : unitInterval => (t : ℝ) / 2) := by fun_prop
  exact h.subtype_mk _
/-- The second-half parameter embedding is continuous. -/
theorem continuous_rightHalfTime : Continuous rightHalfTime := by
  have h : Continuous (fun t : unitInterval => ((t : ℝ) + 1) / 2) := by fun_prop
  exact h.subtype_mk _
/-- The second-half parameter embedding preserves strict order. -/
theorem strictMono_rightHalfTime : StrictMono rightHalfTime := by
  intro s t hst
  change ((s : ℝ) + 1) / 2 < ((t : ℝ) + 1) / 2
  have hh : (s : ℝ) < t := hst
  linarith only [hh]
/-- The concatenation of two normal curves is normal. -/
theorem isNormalCurve_path_trans {S : Type*} [TopologicalSpace S] {G : Drawing S} {x v y : S}
    (p : Path x v) (q : Path v y)
    (hp : IsNormalCurve G p.toContinuousMap) (hq : IsNormalCurve G q.toContinuousMap) :
    IsNormalCurve G (p.trans q).toContinuousMap := by
  intro z hz
  have hzr : z ∈ range (p.trans q) := hz.1
  rw [Path.trans_range] at hzr
  rcases hzr with hzp | hzq
  · exact hp ⟨hzp, hz.2⟩
  · exact hq ⟨hzq, hz.2⟩
end GraphMinor.GM06
