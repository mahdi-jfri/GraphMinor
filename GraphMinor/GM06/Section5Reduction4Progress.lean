module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5SinglePathReduction4Progress
import GraphMinor.GM06.Section5SidedReduction4
import GraphMinor.GM06.Section5InitialPathEdgeNotIncident
import GraphMinor.GM06.Section5SingleEdgePath
import GraphMinor.GM06.Section5ValencyOneCase
import GraphMinor.GM06.Section5Reduction3Apply
import GraphMinor.GM06.Section5
import GraphMinor.GM11.CircuitRegions
import GraphMinor.GM11.Walks

/-!
# Reduction 4 enables a smaller reduction

For at least two paths, this proves the observation following
Reduction 4 in VI, page 129. If none of Reductions 1–3 applies to the new linkage, its initial
edge in Qᵢ lies in the region closure. The initial-edge lemma forces
valency one. Excluding Reduction 3 puts the neighbour on the outer
cuff, so the old linkage path is that single edge. Its whole prefix
is then in the region closure, contradicting Reduction 4's condition.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface
/-- Graph Minors VI, page 129, the observation after Reduction 4,
for at least two paths: an application enables one of Reductions 1–3.
The proof checks the new initial edge in the unchanged region Rᵢ. -/
theorem reduction123_applies_after_reduction4_of_two_le {k : ℕ} {G G' : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hRed : Section5Reduction4Step k G L G' L') :
    ∃ (G'' : Drawing ClosedCylinder) (L'' : CylinderLinkage k G''),
      IsCylinderSection5Drawing k G'' ∧
        (Section5Reduction1Step k G' L' G'' L'' ∨
          Section5Reduction2Step k G' L' G'' L'' ∨
            Section5Reduction3Step k G' L' G'' L'') := by
  classical
  obtain ⟨hGG, i, v, A, B, Q, _, _, hA, _, hbad, hQG, _, hQpath, hQR, hNew, _⟩ :=
    section5Reduction4Step_iff_of_two_le hk |>.mp hRed
  subst G'
  by_contra hnone
  have hno1 (H : Drawing ClosedCylinder) (M : CylinderLinkage k H)
      (hH : IsCylinderSection5Drawing k H) : ¬ Section5Reduction1Step k G L' H M :=
    fun h => hnone ⟨H, M, hH, Or.inl h⟩
  have hno2 (H : Drawing ClosedCylinder) (M : CylinderLinkage k H)
      (hH : IsCylinderSection5Drawing k H) : ¬ Section5Reduction2Step k G L' H M :=
    fun h => hnone ⟨H, M, hH, Or.inr (Or.inl h)⟩
  have hno3 (H : Drawing ClosedCylinder) (M : CylinderLinkage k H)
      (hH : IsCylinderSection5Drawing k H) : ¬ Section5Reduction3Step k G L' H M :=
    fun h => hnone ⟨H, M, hH, Or.inr (Or.inr h)⟩
  obtain ⟨θ', hθ'⟩ := CylinderLinkage.exists_hasTheta hG.1 L'
  obtain ⟨e, heQ, w, hws, hlQ⟩ := exists_nonloop_first_link hQpath
  have hlG := (hQG.isLink_iff heQ).mp hlQ
  have hse : cylinderM1Point k i ∈ closure e :=
    (show cylinderM1Point k i ∈ closure e ∩ G.V from hlG.2.2.2.symm ▸ mem_insert _ {w}).1
  have heR : e ⊆ closure (cylinderRegion k G i) :=
    fun x hx => hQR ((heQ.2.1 hx).1)
  have heNew : e ∈ (L'.pathDrawing i).E := by
    by_contra heNot
    obtain ⟨x, hxe⟩ := hlG.1.1
    have hxQ : x ∈ Q.U := (heQ.2.1 hxe).1
    have hxNew : x ∈ (L'.pathDrawing i).U := hNew.symm ▸ Or.inl hxQ
    exact disjoint_left.mp (GM11.edge_disjoint_U (L'.isSubdrawing i).1 hlG.1 heNot) hxe hxNew
  have hval : vertexValency G.toGraph (cylinderM1Point k i) = 1 := by
    by_contra hval
    exact initial_path_edge_not_subset_region_closure_of_no_reductions12 L' hk hG hθ'
      hno1 hno2 i hval heNew hse heR
  have hwC : w ∈ cylinderCuff2 := by
    by_contra hwC
    obtain ⟨H, M, hH, h3⟩ :=
      exists_section5_reduction3_of_interior_neighbour L' hG i hval hlG hws hwC
    exact hno3 H M hH h3
  have hOld := (linkage_path_eq_closed_edge_of_valency_one L hG i hval hlG hwC).2
  apply hbad
  apply hA.2.1.trans
  rw [hOld]
  exact closure_minimal heR isClosed_closure
/-- Graph Minors VI, page 129: every application of Reduction 4
with the corrected side condition enables one of Reductions 1–3. -/
theorem reduction123_applies_after_reduction4 {k : ℕ} {G G' : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hG : IsCylinderSection5Drawing k G)
    (hRed : Section5Reduction4Step k G L G' L') :
    ∃ (G'' : Drawing ClosedCylinder) (L'' : CylinderLinkage k G''),
      IsCylinderSection5Drawing k G'' ∧
        (Section5Reduction1Step k G' L' G'' L'' ∨
          Section5Reduction2Step k G' L' G'' L'' ∨
            Section5Reduction3Step k G' L' G'' L'') := by
  by_cases hk1 : k = 1
  · subst k
    exact reduction123_applies_after_reduction4_of_one L L' hG hRed
  · have hk : 1 < k := by have := hG.1; omega
    exact reduction123_applies_after_reduction4_of_two_le L L' hk hG hRed

end GraphMinor.GM06
