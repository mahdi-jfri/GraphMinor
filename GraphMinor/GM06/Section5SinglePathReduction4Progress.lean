module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5IncidentPrefixValency
import GraphMinor.GM06.Section5PrefixLiftSeam
import GraphMinor.GM06.Section5SidedReduction4
import GraphMinor.GM06.Section5SingleEdgePath
import GraphMinor.GM06.Section5ValencyOneCase
import GraphMinor.GM06.Section5Reduction3Apply
import GraphMinor.GM06.Section5
import GraphMinor.GM11.Walks

/-!
# Reduction 4 enables a smaller reduction for one path

This proves the observation after Reduction 4 in VI, page 129,
with incidence on the chosen lifted side. Absence of Reductions 1
and 2 forces the new incident prefix to start at a vertex of valency
one. Absence of Reduction 3 then makes both linkage paths the same
single edge. Their aligned lifts agree, contradicting the old prefix
condition of Reduction 4.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The valency-one case of the reduction loop on page 133 of VI.
If Reduction 3 fails, the unique edge at the initial point ends on
the outer cuff. Both the old path and any proposed rerouted path
are that closed edge. Their aligned lifts agree, contradicting the
old-prefix condition of the side-sensitive Reduction 4. -/
theorem not_reduction4_of_one_valency_one_no_reduction3
    {G G' : Drawing ClosedCylinder}
    (L : CylinderLinkage 1 G) (L' : CylinderLinkage 1 G')
    (hG : IsCylinderSection5Drawing 1 G)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) = 1)
    (hno3 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction3Step 1 G L H M) :
    ¬ Section5Reduction4Step 1 G L G' L' := by
  classical
  intro hRed
  obtain ⟨hGG, hside⟩ := section5Reduction4Step_iff_of_one.mp hRed
  subst G'
  obtain ⟨i, u, T, Q, q, _, _, hbad, _, hQG, hQU, hQpath,
    hq, hqR, _, hNew, _⟩ := hside
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hQL : Q.U ⊆ (L'.pathDrawing 0).U := by
    rw [hNew]
    exact subset_union_left
  obtain ⟨e, heQ, w, hws, hlQ⟩ := exists_nonloop_first_link hQpath
  have hlG := (hQG.isLink_iff heQ).mp hlQ
  have hwC : w ∈ cylinderCuff2 := by
    by_contra hwC
    obtain ⟨H, M, hH, h3⟩ := exists_section5_reduction3_of_interior_neighbour
      L hG 0 hval hlG hws hwC
    exact hno3 H M hH h3
  have hOld := (linkage_path_eq_closed_edge_of_valency_one L hG 0 hval hlG hwC).2
  have hNewClosed := (linkage_path_eq_closed_edge_of_valency_one L' hG 0 hval hlG hwC).2
  have hQUold : Q.U = (L.pathDrawing 0).U := by
    apply subset_antisymm
    · rw [hOld]
      exact hQL.trans hNewClosed.subset
    · rw [hOld]
      exact Q.closure_subset_U heQ
  have hRange : range q = (L.pathDrawing 0).U := hq.2.1.trans hQUold
  have hLiftRange := range_aligned_lift_eq_of_range_eq_path (L.isPath 0)
    (L.curve 0) (L.curve_parametrizes 0) q hRange hq.2.2.1
    (cylinderInitialLift 1 0).2 rfl
  apply hbad
  intro p hp
  apply hqR
  rw [hLiftRange]
  exact image_subset_range _ _ hp

/-- Graph Minors VI, page 129, the observation after Reduction 4
for one path, with the corrected lifted incidence condition. -/
theorem reduction123_applies_after_reduction4_of_one
    {G G' : Drawing ClosedCylinder}
    (L : CylinderLinkage 1 G) (L' : CylinderLinkage 1 G')
    (hG : IsCylinderSection5Drawing 1 G)
    (hRed : Section5Reduction4Step 1 G L G' L') :
    ∃ (G'' : Drawing ClosedCylinder) (L'' : CylinderLinkage 1 G''),
      IsCylinderSection5Drawing 1 G'' ∧
        (Section5Reduction1Step 1 G' L' G'' L'' ∨
          Section5Reduction2Step 1 G' L' G'' L'' ∨
            Section5Reduction3Step 1 G' L' G'' L'') := by
  classical
  obtain ⟨hGG, hside⟩ := section5Reduction4Step_iff_of_one.mp hRed
  subst G'
  obtain ⟨i, u, T, Q, q, _, _, hbad, _, hQG, hQU, hQpath,
    hq, hqR, _, hNew, _⟩ := hside
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  by_contra hnone
  have hno1 (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H)
      (hH : IsCylinderSection5Drawing 1 H) : ¬ Section5Reduction1Step 1 G L' H M :=
    fun h => hnone ⟨H, M, hH, Or.inl h⟩
  have hno2 (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H)
      (hH : IsCylinderSection5Drawing 1 H) : ¬ Section5Reduction2Step 1 G L' H M :=
    fun h => hnone ⟨H, M, hH, Or.inr (Or.inl h)⟩
  have hno3 (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H)
      (hH : IsCylinderSection5Drawing 1 H) : ¬ Section5Reduction3Step 1 G L' H M :=
    fun h => hnone ⟨H, M, hH, Or.inr (Or.inr h)⟩
  obtain ⟨θ', hθ'⟩ := CylinderLinkage.exists_hasTheta hG.1 L'
  have hQL : Q.U ⊆ (L'.pathDrawing 0).U := by
    rw [hNew]
    exact subset_union_left
  have hval := valency_initial_eq_one_of_incident_prefix_of_no_reductions12
    L' hG hθ' hno1 hno2 ⟨hQG, hQU, hQpath⟩ hQL q hq hqR
  obtain ⟨e, heQ, w, hws, hlQ⟩ := exists_nonloop_first_link hQpath
  have hlG := (hQG.isLink_iff heQ).mp hlQ
  have hwC : w ∈ cylinderCuff2 := by
    by_contra hwC
    obtain ⟨H, M, hH, h3⟩ := exists_section5_reduction3_of_interior_neighbour
      L' hG 0 hval hlG hws hwC
    exact hno3 H M hH h3
  have hOld := (linkage_path_eq_closed_edge_of_valency_one L hG 0 hval hlG hwC).2
  have hNewClosed := (linkage_path_eq_closed_edge_of_valency_one L' hG 0 hval hlG hwC).2
  have hQUold : Q.U = (L.pathDrawing 0).U := by
    apply subset_antisymm
    · rw [hOld]
      exact hQL.trans hNewClosed.subset
    · rw [hOld]
      exact Q.closure_subset_U heQ
  have hRange : range q = (L.pathDrawing 0).U := hq.2.1.trans hQUold
  have hLiftRange := range_aligned_lift_eq_of_range_eq_path (L.isPath 0)
    (L.curve 0) (L.curve_parametrizes 0) q hRange hq.2.2.1
    (cylinderInitialLift 1 0).2 rfl
  apply hbad
  intro p hp
  apply hqR
  rw [hLiftRange]
  exact image_subset_range _ _ hp

end GraphMinor.GM06
