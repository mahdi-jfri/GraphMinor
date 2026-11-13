module

public import GraphMinor.GM06.Section5LiftCover
import GraphMinor.GM06.Section5RegionPoint

/-!
# The lifted disc projects into the prescribed strip

In VI (5.1), page 129, paths must stay in the component Σᵢ between
two consecutive linkage paths. The lifted disc interior projects to
a connected set missing the linkage. The dual point on the initial
cuff is in its closure. Adding that point preserves connectedness,
so the projected interior lies in the component defining Σᵢ.
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface

/-- The interior of the disc between the lifts starting at i and
i + 1 projects into the linkage strip Σᵢ. -/
theorem stripDiscInterior_projection_mem_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L ((i.val : ℤ) + 1))
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {p : ℝ × ℝ} (hp : p ∈ discInt D) {x : ClosedCylinder}
    (hr : x.1.1 = p.1) (ha : x.1.2 = Circle.exp p.2) :
    x ∈ cylinderStrip L i := by
  let m : ℤ := (i.val : ℤ) + 1
  let b : ℝ × ℝ := (1, (2 * ((i.val + 1 : ℕ) : ℝ) + 1) * π / k)
  let f : (ℝ × ℝ) → ClosedCylinder := fun q =>
    ⟨(max 1 (min 2 q.1), Circle.exp q.2),
      ⟨⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩, mem_univ _⟩⟩
  have hf : Continuous f :=
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk
      (Circle.exp.continuous.comp continuous_snd)).subtype_mk _
  have hfr (q : ℝ × ℝ) (hq : q ∈ D) : (f q).1.1 = q.1 := by
    have hb := hstrip hq
    change max 1 (min 2 q.1) = q.1
    rw [min_eq_right hb.2, max_eq_right hb.1]
  have hfb : f b = cylinderN1Point k i := by
    apply Subtype.ext
    apply Prod.ext
    · change max 1 (min 2 1) = 1
      norm_num
    · rfl
  have hbB : b ∈ discBd D := by
    rw [hBd]
    apply Or.inl
    apply Or.inr
    refine ⟨mem_singleton 1, ?_⟩
    have hm := (liftedLinkageCurve_props_raw hG.1 L m).2.2.2.1
    have hn := (liftedLinkageCurve_props_raw hG.1 L (m + 1)).2.2.2.1
    change (liftedLinkageCurve hG.1 L m 0).2 ≤ b.2 ∧
      b.2 ≤ (liftedLinkageCurve hG.1 L (m + 1) 0).2
    rw [hm, hn]
    dsimp [b, m]
    constructor <;> apply (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hG.1)).mpr
    all_goals push_cast; nlinarith only [pi_pos]
  have hbcl : cylinderN1Point k i ∈ closure (f '' discInt D) := by
    rw [← hfb]
    exact mem_closure_image hf.continuousAt
      (hD.subset_closure_discInt (discBd_subset D hbB))
  have hconn : IsPreconnected (insert (cylinderN1Point k i) (f '' discInt D)) :=
    (hD.isPreconnected_discInt.image f hf.continuousOn).subset_closure
      (subset_insert _ _) (by
        intro y hy
        rcases hy with rfl | hy
        · exact hbcl
        · exact subset_closure hy)
  have hmiss : insert (cylinderN1Point k i) (f '' discInt D) ⊆
      univ \ ⋃ j, (L.pathDrawing j).U := by
    intro y hy
    refine ⟨mem_univ _, ?_⟩
    rcases hy with rfl | ⟨q, hq, rfl⟩
    · intro hy
      obtain ⟨j, hj⟩ := mem_iUnion.mp hy
      exact cylinderN1Point_not_mem_U hG i ((L.isSubdrawing j).2 hj)
    · exact stripDiscInterior_projection_not_mem_linkage L hG hθ m hD hBd hstrip hq
        (hfr q hq.1) rfl
  have hsub := hconn.subset_connectedComponentIn (mem_insert _ _) hmiss
  have hxf : x = f p := by
    apply Subtype.ext
    apply Prod.ext
    · exact hr.trans (hfr p hp.1).symm
    · exact ha
  rw [hxf]
  exact hsub (mem_insert_of_mem _ ⟨p, hp, rfl⟩)

/-- The whole lifted disc projects into the closure of its cylinder
strip, since a closed disc is contained in the closure of its interior. -/
theorem stripDisc_projection_mem_closure_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L ((i.val : ℤ) + 1))
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {p : ℝ × ℝ} (hp : p ∈ D) {x : ClosedCylinder}
    (hr : x.1.1 = p.1) (ha : x.1.2 = Circle.exp p.2) :
    x ∈ closure (cylinderStrip L i) := by
  let f : (ℝ × ℝ) → ClosedCylinder := fun q =>
    ⟨(max 1 (min 2 q.1), Circle.exp q.2),
      ⟨⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩, mem_univ _⟩⟩
  have hf : Continuous f :=
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk
      (Circle.exp.continuous.comp continuous_snd)).subtype_mk _
  have hfr (q : ℝ × ℝ) (hq : q ∈ D) : (f q).1.1 = q.1 := by
    have hb := hstrip hq
    change max 1 (min 2 q.1) = q.1
    rw [min_eq_right hb.2, max_eq_right hb.1]
  have hsub : f '' discInt D ⊆ cylinderStrip L i := by
    rintro y ⟨q, hq, rfl⟩
    exact stripDiscInterior_projection_mem_strip L hG hθ i hD hBd hstrip hq
      (hfr q hq.1) rfl
  have hx : x = f p := by
    apply Subtype.ext
    apply Prod.ext
    · exact hr.trans (hfr p hp).symm
    · exact ha
  rw [hx]
  exact closure_mono hsub (mem_closure_image hf.continuousAt (hD.subset_closure_discInt hp))

/-- Each linkage path is incident with the strip immediately after
its initial vertex. This includes every vertex and edge of the path. -/
theorem CylinderLinkage.U_subset_closure_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k) :
    (L.pathDrawing i).U ⊆ closure (cylinderStrip L i) := by
  obtain ⟨D, hD, hBd, hstrip⟩ :=
    exists_closedDisc_of_liftedStripBoundary L hG hθ ((i.val : ℤ) + 1)
  intro x hx
  obtain ⟨t, rfl⟩ := (L.curve_parametrizes i).2.1.symm ▸ hx
  let m : ℤ := (i.val : ℤ) + 1
  have hi : modIdx k hG.1 m = i := modIdx_natCast_succ hG.1 i
  have hp : liftedLinkageCurve hG.1 L m t ∈ D := by
    apply discBd_subset D
    rw [hBd]
    exact Or.inl (Or.inl (Or.inl (mem_range_self t)))
  apply stripDisc_projection_mem_closure_strip L hG hθ i hD hBd hstrip hp
  · rw [liftedLinkageCurve_fst, hi]
  · have he := (liftedLinkageCurve_props_raw hG.1 L m).2.2.2.2.2 t
    rw [hi] at he
    exact he.symm

end GraphMinor.GM06
