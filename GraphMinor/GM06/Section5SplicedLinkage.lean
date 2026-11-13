module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5NextContact
import GraphMinor.GM06.Section5Splice
import GraphMinor.GM06.Section5StripDisjoint
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# The linkage obtained by cyclic splicing

For VI (5.1), page 129, join each region path to the tail of the
next old linkage path. Each new path stays in its strip or on that
old path, and it avoids the old path's initial vertex. Two different
strips are disjoint. At an old linkage path, one new path can use its
tail and the next can meet it only at its initial vertex. Thus the
new paths are pairwise disjoint and form a linkage.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

private theorem strip_point_not_mem_path
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (i j : Fin k) {x : ClosedCylinder} (hx : x ∈ cylinderStrip L i) :
    x ∉ (L.pathDrawing j).U := by
  intro hxj
  exact (connectedComponentIn_subset _ _ hx).2 (mem_iUnion.mpr ⟨j, hxj⟩)

private theorem pairwise_disjoint_of_strip_confinement
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (R : Fin k → Drawing ClosedCylinder)
    (hconf : ∀ i, (R i).U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i} ∪
      (L.pathDrawing (finSuccCycle i)).U)
    (havoid : ∀ i, cylinderM1Point k (finSuccCycle i) ∉ (R i).U) :
    Pairwise fun i j => Disjoint (R i).U (R j).U := by
  intro i j hij
  have hs (a : Fin k) : cylinderM1Point k a ∈ (L.pathDrawing a).U :=
    (L.pathDrawing a).V_subset_U (isPathDrawing_end_vertices (L.isPath a)).1
  have hsucc : finSuccCycle i ≠ finSuccCycle j := by
    intro he
    apply hij
    have hp := congrArg finPredCycle he
    simpa only [finPredCycle_finSuccCycle] using hp
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases hconf i hxi with (hxiS | hxiS) | hxiP
  · rcases hconf j hxj with (hxjS | hxjS) | hxjP
    · exact disjoint_left.mp (disjoint_cylinderStrip L hG hθ hij) hxiS hxjS
    · exact strip_point_not_mem_path L i j hxiS
        ((mem_singleton_iff.mp hxjS).symm ▸ hs j)
    · exact strip_point_not_mem_path L i (finSuccCycle j) hxiS hxjP
  · have he : x = cylinderM1Point k i := mem_singleton_iff.mp hxiS
    subst x
    rcases hconf j hxj with (hxjS | hxjS) | hxjP
    · exact strip_point_not_mem_path L j i hxjS (hs i)
    · exact hij (cylinderM1Point_injective hG.1 (mem_singleton_iff.mp hxjS))
    · by_cases he : i = finSuccCycle j
      · apply havoid j
        rw [← he]
        exact hxj
      · exact disjoint_left.mp (L.pairwise_disjoint he) (hs i) hxjP
  · rcases hconf j hxj with (hxjS | hxjS) | hxjP
    · exact strip_point_not_mem_path L j (finSuccCycle i) hxjS hxiP
    · have he : x = cylinderM1Point k j := mem_singleton_iff.mp hxjS
      subst x
      by_cases he : j = finSuccCycle i
      · apply havoid i
        rw [← he]
        exact hxi
      · exact disjoint_left.mp (L.pairwise_disjoint he) (hs j) hxiP
    · exact disjoint_left.mp (L.pairwise_disjoint hsucc) hxiP hxjP

/-- Paths through consecutive strips, meeting the next old path
only at their terminal contacts, give the cyclically spliced linkage
of VI (5.1), page 129. -/
theorem exists_spliced_linkage_of_strip_paths
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hpaths : ∀ i, ∃ t ∈ (L.pathDrawing (finSuccCycle i)).V,
      t ≠ cylinderM1Point k (finSuccCycle i) ∧ ∃ Q : Drawing ClosedCylinder,
        IsSubpathOf G Q (cylinderM1Point k i) t ∧
        Q.U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i, t} ∧
        Q.U ∩ (L.pathDrawing (finSuccCycle i)).U ⊆ {t}) :
    ∃ L' : CylinderLinkage k G,
      (∀ i, L'.curve i 1 = L.curve (finSuccCycle i) 1) ∧
      (∀ i, (L'.pathDrawing i).U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i} ∪
        (L.pathDrawing (finSuccCycle i)).U) ∧
      (∀ i, cylinderM1Point k (finSuccCycle i) ∉ (L'.pathDrawing i).U) := by
  classical
  choose t ht htne Q hQ hQstrip hQmeet using hpaths
  choose T R hTail hTP hR hRU hRnot using fun i => exists_path_after_linkage_tail
    (L.isSubdrawing (finSuccCycle i)).1 (hQ i).1
    (L.isPath (finSuccCycle i)) (hQ i).2.2 (ht i) (htne i) (hQmeet i)
  have hconf : ∀ i, (R i).U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i} ∪
      (L.pathDrawing (finSuccCycle i)).U := by
    intro i x hx
    rw [hRU i] at hx
    rcases hx with hxQ | hxT
    · rcases hQstrip i hxQ with hxS | hxEnds
      · exact Or.inl (Or.inl hxS)
      · rcases hxEnds with he | he
        · exact Or.inl (Or.inr (mem_singleton_iff.mpr he))
        · apply Or.inr
          rw [mem_singleton_iff.mp he]
          exact (L.pathDrawing (finSuccCycle i)).V_subset_U (ht i)
    · exact Or.inr ((hTP i).U_subset hxT)
  have hdisj := pairwise_disjoint_of_strip_confinement L hG hθ R hconf hRnot
  choose f hf using fun i => (hR i).2.2.2
  let L' : CylinderLinkage k G := {
    pathDrawing := R
    curve := f
    isSubdrawing i := ⟨(hR i).1, (hR i).2.1⟩
    isPath i := by
      rw [(hf i).2.2.2]
      exact (hR i).2.2
    curve_parametrizes i := ⟨(hf i).1, (hf i).2.1, (hf i).2.2.1, rfl⟩
    curve_one_mem i := by
      rw [(hf i).2.2.2]
      exact L.curve_one_mem (finSuccCycle i)
    pairwise_disjoint := hdisj }
  exact ⟨L', fun i => (hf i).2.2.2, hconf, hRnot⟩

/-- The cyclic splicing in VI (5.1), page 129, produces a linkage
once each region meets its preceding linkage path only at its initial
vertex. The terminal vertices move to the next old path, and the new
paths obey the strip confinement needed to compute their winding. -/
theorem exists_spliced_linkage_of_region_contacts
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (hcontact : ∀ i, closure (cylinderRegion k G i) ∩ (L.pathDrawing i).U ⊆
      {cylinderM1Point k i}) :
    ∃ L' : CylinderLinkage k G,
      (∀ i, L'.curve i 1 = L.curve (finSuccCycle i) 1) ∧
      (∀ i, (L'.pathDrawing i).U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i} ∪
        (L.pathDrawing (finSuccCycle i)).U) ∧
      (∀ i, cylinderM1Point k (finSuccCycle i) ∉ (L'.pathDrawing i).U) := by
  exact exists_spliced_linkage_of_strip_paths L hG hθ
    (fun i => exists_path_to_next_linkage_in_strip L hG hk hθ hno i (hcontact i))

end GraphMinor.GM06
