module

public import GraphMinor.GM06.Section5StripAvoidance

/-!
# Projecting the disc between lifted paths

The indexed lifts used in VI (5.1), page 129, account for every lift
of every linkage point. Equal angular projections differ by a whole
period, and adding that period to a lifted path changes its index by
k. Consequently, the interior of the disc between consecutive lifts
projects into the complement of the linkage on the cylinder.
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface

/-- Every planar point projecting to a point on a linkage curve
lies on one of the indexed lifts of that curve. -/
theorem exists_index_of_linkage_projection
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k)
    (L : CylinderLinkage k G) (i : Fin k) (t : unitInterval) (p : ℝ × ℝ)
    (hr : p.1 = (L.curve i t).1.1)
    (ha : Circle.exp p.2 = (L.curve i t).1.2) :
    ∃ n : ℤ, liftedLinkageCurve hk L n t = p := by
  let m : ℤ := (i.val : ℤ) + 1
  have hi : modIdx k hk m = i := modIdx_natCast_succ hk i
  have he := (liftedLinkageCurve_props_raw hk L m).2.2.2.2.2 t
  rw [hi] at he
  obtain ⟨q, hq⟩ := Circle.exp_eq_exp.mp (ha.trans he.symm)
  refine ⟨m + (k : ℤ) * q, ?_⟩
  rw [liftedLinkageCurve_add_mul]
  apply Prod.ext
  · rw [liftedLinkageCurve_fst, hi]
    exact hr.symm
  · exact hq.symm

/-- The strip disc interior misses every indexed linkage lift. -/
theorem disjoint_stripDiscInterior_linkage_lift
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m n : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    Disjoint (discInt D) (range (liftedLinkageCurve hG.1 L n)) := by
  by_cases hnm : n = m
  · subst n
    apply disjoint_left.mpr
    intro p hp hpr
    apply hp.2
    rw [hBd]
    exact Or.inl (Or.inl (Or.inl hpr))
  by_cases hnm1 : n = m + 1
  · subst n
    apply disjoint_left.mpr
    intro p hp hpr
    apply hp.2
    rw [hBd]
    exact Or.inl (Or.inl (Or.inr hpr))
  have hd := disjoint_stripDisc_of_other_index L hG hθ hnm hnm1 hD hBd hstrip
  exact disjoint_left.mpr (fun _ hp hpr => disjoint_left.mp hd hpr hp.1)

/-- Projecting a point of the strip disc interior to the cylinder
cannot land on any linkage path. -/
theorem stripDiscInterior_projection_not_mem_linkage
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {p : ℝ × ℝ} (hp : p ∈ discInt D) {x : ClosedCylinder}
    (hr : x.1.1 = p.1) (ha : x.1.2 = Circle.exp p.2) :
    x ∉ ⋃ i, (L.pathDrawing i).U := by
  intro hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨t, ht⟩ := (L.curve_parametrizes i).2.1.symm ▸ hi
  have hrt : p.1 = (L.curve i t).1.1 := hr.symm.trans (congrArg (fun z : ClosedCylinder => z.1.1) ht.symm)
  have hat : Circle.exp p.2 = (L.curve i t).1.2 := ha.symm.trans (congrArg (fun z : ClosedCylinder => z.1.2) ht.symm)
  obtain ⟨n, hn⟩ := exists_index_of_linkage_projection hG.1 L i t p hrt hat
  exact disjoint_left.mp (disjoint_stripDiscInterior_linkage_lift L hG hθ m n hD hBd hstrip)
    hp ⟨t, hn⟩

end GraphMinor.GM06
