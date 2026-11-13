module

public import GraphMinor.GM06.Section5CurveCount
import GraphMinor.GM11.Regions

/-!
# The last visit to the deleted-edge region

For claim (1) of VI (5.5), the closed set of region-visit times has
a maximum. Prepending a curve transports this maximum into the
second half of the interval. If there is no earlier vertex hit,
normality puts the initial curve segment in one region, so its
initial point is in the region reached before the maximum.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface unitInterval
/-- The closed set of visit times to a nonempty region preimage has a
last point, as used in VI (5.5), page 130. -/
theorem exists_last_region_visit {S : Type*} [TopologicalSpace S] (f : Curve S) (R : Set S)
    (h : (f ⁻¹' R).Nonempty) : ∃ z : unitInterval, IsGreatest (closure (f ⁻¹' R)) z := by
  exact isClosed_closure.isCompact.exists_isGreatest (closure_nonempty_iff.mpr h)
/-- Prepending a path moves the last region visit to its corresponding
second-half parameter, as used in claim (1) of VI (5.5), page 131. -/
theorem last_region_visit_path_trans {S : Type*} [TopologicalSpace S] {x v y : S}
    (p : Path x v) (q : Path v y) {R : Set S} {z : unitInterval}
    (hz : IsGreatest (closure (q ⁻¹' R)) z) :
    IsGreatest (closure ((p.trans q) ⁻¹' R)) (rightHalfTime z) := by
  have htime : rightHalfTime '' (q ⁻¹' R) ⊆ (p.trans q) ⁻¹' R := by
    rintro _ ⟨t, ht, rfl⟩
    change (p.trans q) (rightHalfTime t) ∈ R
    rw [path_trans_rightHalfTime]
    exact ht
  have hmem : rightHalfTime z ∈ closure ((p.trans q) ⁻¹' R) := by
    apply closure_mono htime
    exact (image_closure_subset_closure_image continuous_rightHalfTime) ⟨z, hz.1, rfl⟩
  have hbound : (p.trans q) ⁻¹' R ⊆ Iic (rightHalfTime z) := by
    intro t ht
    by_cases hhalf : (t : ℝ) ≤ 1 / 2
    · change (t : ℝ) ≤ ((z : ℝ) + 1) / 2
      linarith only [hhalf, z.2.1]
    · change (p.trans q) t ∈ R at ht
      rw [Path.trans_apply, dite_eq_right hhalf] at ht
      have huz : (⟨2 * (t : ℝ) - 1,
          two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hhalf).le, t.2.2⟩⟩ : unitInterval) ≤ z :=
        hz.2 (subset_closure ht)
      change 2 * (t : ℝ) - 1 ≤ z at huz
      change (t : ℝ) ≤ ((z : ℝ) + 1) / 2
      linarith only [huz]
  exact ⟨hmem, closure_minimal hbound isClosed_Iic⟩
/-- If a normal curve reaches a region by a given time and has no
earlier vertex contact, it starts in that region. This is the first
observation in the proof of claim (1) of VI (5.5), page 131. -/
theorem initial_point_mem_region_of_no_prior_vertex {S : Type*} [TopologicalSpace S] {G : Drawing S} (f : Curve S)
    (hf : IsNormalCurve G f) {R : Set S} (hR : R ∈ G.R)
    {u z : unitInterval} (hu : f u ∈ R) (huz : u ≤ z)
    (hn : ¬ ∃ t : unitInterval, t < z ∧ f t ∈ G.V) : f 0 ∈ R := by
  have hpre : IsPreconnected (f '' Icc (0 : unitInterval) u) :=
    isPreconnected_Icc.image f f.continuous.continuousOn
  have hdis : Disjoint (f '' Icc (0 : unitInterval) u) G.U := by
    refine disjoint_left.mpr ?_
    rintro a ⟨t, ht, rfl⟩ htG
    by_cases htz : t < z
    · exact hn ⟨t, htz, hf ⟨mem_range_self t, htG⟩⟩
    · have htu : t = u := le_antisymm ht.2 (huz.trans (le_of_not_gt htz))
      exact GM11.region_subset hR (htu ▸ hu) htG
  have hsub := GM11.subset_region hR hpre hdis ⟨u, ⟨bot_le, le_rfl⟩, rfl⟩ hu
  exact hsub ⟨0, ⟨le_rfl, bot_le⟩, rfl⟩
/-- The last point of a region visit lies in its closure. Unless it is
the terminal parameter, normality forces it to be a drawing vertex.
This is the choice of z₂ in VI (5.5), page 130. -/
theorem last_region_visit_mem_vertex_or_terminal
    {S : Type*} [TopologicalSpace S] [LocallyConnectedSpace S]
    {G : Drawing S} (f : Curve S) (hf : IsNormalCurve G f)
    {R : Set S} (hR : R ∈ G.R) {z : unitInterval}
    (hz : IsGreatest (closure (f ⁻¹' R)) z) :
    f z ∈ closure R ∧ (f z ∈ G.V ∨ z = 1) := by
  have hcl : f z ∈ closure R := f.continuous.closure_preimage_subset R hz.1
  refine ⟨hcl, ?_⟩
  by_cases hz1 : z = 1
  · exact Or.inr hz1
  · have hzr : f z ∉ R := by
      intro hzr
      have hzlt : z < 1 := lt_of_le_of_ne (le_top) hz1
      have hzI : z ∈ closure (Ioi z) := by
        rw [closure_Ioi' (show (Ioi z).Nonempty from ⟨1, hzlt⟩)]
        exact le_rfl
      obtain ⟨t, htf, hzt⟩ := mem_closure_iff.mp hzI (f ⁻¹' R)
        ((GM11.region_isOpen hR).preimage f.continuous) hzr
      exact (not_lt_of_ge (hz.2 (subset_closure htf))) hzt
    have hzU : f z ∈ G.U := (GM11.closure_region_subset hR hcl).resolve_left hzr
    exact Or.inl (hf ⟨mem_range_self z, hzU⟩)

/-- Finitely many vertex hits and an earlier hit give a last vertex
hit strictly before z₂, as chosen after claim (1) of VI (5.5), page 131. -/
theorem exists_last_vertex_hit_before
    {S : Type*} [TopologicalSpace S] {G : Drawing S} (f : Curve S)
    (hf : (curveVertexHits G f).Finite) {z₂ : unitInterval}
    (hprior : ∃ t : unitInterval, t < z₂ ∧ f t ∈ G.V) :
    ∃ z₁ : unitInterval, z₁ < z₂ ∧ f z₁ ∈ G.V ∧
      ∀ t : unitInterval, z₁ < t → t < z₂ → f t ∉ G.V := by
  let T := curveVertexHits G f ∩ Iio z₂
  have hT : T.Finite := hf.inter_of_left _
  have hTne : T.Nonempty := by
    obtain ⟨t, htz, htV⟩ := hprior
    exact ⟨t, htV, htz⟩
  obtain ⟨z₁, hz₁, hmax⟩ := hT.isCompact.exists_isGreatest hTne
  refine ⟨z₁, hz₁.2, hz₁.1, ?_⟩
  intro t ht₁ ht₂ htV
  exact (not_lt_of_ge (hmax ⟨htV, ht₂⟩)) ht₁

/-- Between the last earlier vertex hit and the last region visit,
the normal curve stays in that region. Both endpoint values are
incident with it. This supplies the incidence at z₁ used in VI (5.5),
page 132, rather than assuming that incidence. -/
theorem curve_between_last_vertex_and_region_visit
    {S : Type*} [TopologicalSpace S] [LocallyConnectedSpace S]
    {G : Drawing S} (f : Curve S) (hf : IsNormalCurve G f)
    {R : Set S} (hR : R ∈ G.R) {z₁ z₂ : unitInterval}
    (hz : IsGreatest (closure (f ⁻¹' R)) z₂) (hzlt : z₁ < z₂)
    (hno : ∀ t : unitInterval, z₁ < t → t < z₂ → f t ∉ G.V) :
    (∀ t : unitInterval, z₁ < t → t < z₂ → f t ∈ R) ∧
      (∀ t : unitInterval, z₁ ≤ t → t ≤ z₂ → f t ∈ closure R) := by
  obtain ⟨u, hzu, huR⟩ := mem_closure_iff.mp hz.1 (Ioi z₁) isOpen_Ioi hzlt
  have huz : u ≤ z₂ := hz.2 (subset_closure huR)
  have hvisit : ∃ v : unitInterval, z₁ < v ∧ v < z₂ ∧ f v ∈ R := by
    by_cases huz' : u < z₂
    · exact ⟨u, hzu, huz', huR⟩
    · have hueq : u = z₂ := le_antisymm huz (le_of_not_gt huz')
      have hzR : f z₂ ∈ R := hueq ▸ huR
      have hzcl : z₂ ∈ closure (Iio z₂) := by
        rw [closure_Iio' (show (Iio z₂).Nonempty from ⟨z₁, hzlt⟩)]
        exact le_rfl
      obtain ⟨v, ⟨hvR, hvz₁⟩, hvz₂⟩ := mem_closure_iff.mp hzcl
        ((f ⁻¹' R) ∩ Ioi z₁) (((GM11.region_isOpen hR).preimage f.continuous).inter isOpen_Ioi)
        ⟨hzR, hzlt⟩
      exact ⟨v, hvz₁, hvz₂, hvR⟩
  have hpre : IsPreconnected (f '' Ioo z₁ z₂) :=
    isPreconnected_Ioo.image f f.continuous.continuousOn
  have hdis : Disjoint (f '' Ioo z₁ z₂) G.U := by
    refine disjoint_left.mpr ?_
    rintro x ⟨t, ht, rfl⟩ htG
    exact hno t ht.1 ht.2 (hf ⟨mem_range_self t, htG⟩)
  obtain ⟨v, hv₁, hv₂, hvR⟩ := hvisit
  have hsub : Ioo z₁ z₂ ⊆ f ⁻¹' R := by
    intro t ht
    exact GM11.subset_region hR hpre hdis ⟨v, ⟨hv₁, hv₂⟩, rfl⟩ hvR ⟨t, ht, rfl⟩
  refine ⟨fun t ht₁ ht₂ => hsub ⟨ht₁, ht₂⟩, ?_⟩
  intro t ht₁ ht₂
  have htcl : t ∈ closure (Ioo z₁ z₂) := by
    rw [closure_Ioo hzlt.ne]
    exact ⟨ht₁, ht₂⟩
  exact f.continuous.closure_preimage_subset R (closure_mono hsub htcl)

end GraphMinor.GM06
