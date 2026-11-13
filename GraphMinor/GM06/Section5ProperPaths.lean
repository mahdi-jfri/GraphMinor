module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5LinkageEnds

/-!
# Linkage paths meet the cuffs only at their ends

In the strip argument for VI (5.1), page 129, each linkage path is a
crosscut from one cuff to the other. Properness puts every cuff point
of a path among the prescribed vertices. Each prescribed vertex is
already an end of one linkage path. Disjointness therefore forces any
cuff point of a given path to be one of its own ends. Injectivity then
puts all interior curve parameters strictly between the cuffs.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- A linkage path meets the boundary of a Section 5 drawing exactly
at its own two ends. -/
theorem CylinderLinkage.U_inter_boundary
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    (L.pathDrawing i).U ∩ bd ClosedCylinder = {cylinderM1Point k i, L.curve i 1} := by
  have hstart (j : Fin k) : cylinderM1Point k j ∈ (L.pathDrawing j).U := by
    rw [← (L.curve_parametrizes j).2.1]
    exact ⟨0, (L.curve_parametrizes j).2.2.1⟩
  have hend (j : Fin k) : L.curve j 1 ∈ (L.pathDrawing j).U := by
    rw [← (L.curve_parametrizes j).2.1]
    exact mem_range_self 1
  ext x
  constructor
  · intro hx
    have hxG : x ∈ G.V ∩ bd ClosedCylinder := ⟨hG.2.1 ⟨hx.2, (L.isSubdrawing i).2 hx.1⟩, hx.2⟩
    rw [hG.2.2] at hxG
    rcases hxG with hxM1 | hxM2
    · obtain ⟨j, hj⟩ := hxM1
      have hji : j = i := by
        by_contra hne
        exact disjoint_left.mp (L.pairwise_disjoint hne) (hj ▸ hstart j) hx.1
      subst j
      exact Or.inl hj.symm
    · obtain ⟨j, hj⟩ := L.curve_one_surjective hxM2
      have hji : j = i := by
        by_contra hne
        exact disjoint_left.mp (L.pairwise_disjoint hne) (hj ▸ hend j) hx.1
      subst j
      exact Or.inr hj.symm
  · rintro (rfl | hx)
    · refine ⟨hstart i, ?_⟩
      rw [bd_closedCylinder]
      exact Or.inl rfl
    · rw [mem_singleton_iff] at hx
      subst x
      refine ⟨hend i, ?_⟩
      obtain ⟨j, hj⟩ := L.curve_one_mem i
      rw [← hj, bd_closedCylinder]
      exact Or.inr rfl

/-- Interior parameters of a linkage curve lie off both cuffs. -/
theorem CylinderLinkage.curve_interior_not_mem_boundary
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) {t : unitInterval} (ht : t ∈ Ioo 0 1) :
    L.curve i t ∉ bd ClosedCylinder := by
  intro hbd
  have htU : L.curve i t ∈ (L.pathDrawing i).U := by
    rw [← (L.curve_parametrizes i).2.1]
    exact mem_range_self t
  have hends : L.curve i t ∈ ({cylinderM1Point k i, L.curve i 1} : Set ClosedCylinder) :=
    L.U_inter_boundary hG i ▸ ⟨htU, hbd⟩
  rcases hends with hs | he
  · have heq : L.curve i t = L.curve i 0 := hs.trans (L.curve_parametrizes i).2.2.1.symm
    exact ht.1.ne' ((L.curve_parametrizes i).1 heq)
  · have heq : t = 1 := (L.curve_parametrizes i).1 (mem_singleton_iff.mp he)
    exact ht.2.ne heq

/-- Interior points of a linkage curve have radial coordinate strictly
between the two cuff radii. -/
theorem CylinderLinkage.radius_curve_interior
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) {t : unitInterval} (ht : t ∈ Ioo 0 1) :
    1 < (L.curve i t).1.1 ∧ (L.curve i t).1.1 < 2 := by
  have hnot := L.curve_interior_not_mem_boundary hG i ht
  rw [bd_closedCylinder] at hnot
  have h1 : (L.curve i t).1.1 ≠ 1 := fun h => hnot (Or.inl h)
  have h2 : (L.curve i t).1.1 ≠ 2 := fun h => hnot (Or.inr h)
  exact ⟨(lt_or_eq_of_le (L.curve i t).2.1.1).resolve_right h1.symm,
    (lt_or_eq_of_le (L.curve i t).2.1.2).resolve_right h2⟩

end GraphMinor.GM06
