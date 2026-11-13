module

public import GraphMinor.GM06.Section5ComputedReduction2Complete

/-!
# Failed finite tests exclude Reduction 2

For VI (5.7), page 133, run the component and initial-loop tests
at each initial vertex. If every test fails, no separation in
Reduction 2 exists. Its retained side contains each given path,
and hence the exact protected mask, so the completeness theorem
would otherwise supply a successful test.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.Compute

/-- Exhausting the finite component and loop tests at every initial
vertex excludes every Reduction 2 retaining the given linkage. -/
theorem not_reduction2_of_finite_tests
    {k n : ℕ} {G G₁ : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L₁ : CylinderLinkage k G₁)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (A : Finset (Fin n)) (hV : G.V = vertex '' (A : Set (Fin n)))
    (cuts : Fin k → Fin n) (hcuts : ∀ i, vertex (cuts i) = cylinderM1Point k i)
    (Q : Finset (Fin n))
    (hQ : vertex '' (Q : Set (Fin n)) ⊆ ⋃ j : Fin k, (L.pathDrawing j).V)
    (hcomponents : ∀ i : Fin k, ∀ source ∈ A,
      (Q ∩ GraphMinor.Compute.reachSet (gm06PuncturedGraphData tagged (cuts i)).vertexGraph source).card ≠ 0)
    (hloops : ∀ i : Fin k, ∀ j : Fin tagged.length,
      ¬ (tagged[j].2 = 1 ∧ tagged[j].1.1 = cuts i ∧ tagged[j].1.2 = cuts i)) :
    ¬ Section5Reduction2Step k G L G₁ L₁ := by
  rintro ⟨i, G₂, hsep, _, _, hover, hne, hpaths, _⟩
  have hover' : G₁.toGraph.vertexSet ∩ G₂.toGraph.vertexSet ⊆ {vertex (cuts i)} := by
    rw [hcuts i]
    exact hover
  have hQ₁ : vertex '' (Q : Set (Fin n)) ⊆ G₁.toGraph.vertexSet := by
    intro a ha
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hQ ha)
    have hsub : (L.pathDrawing j).IsSubdrawing G₁ := by
      simpa only [hpaths] using (L₁.isSubdrawing j).1
    exact hsub.1 hj
  rcases computed_reduction2_search_complete hsep vertex tagged edge hlinks hcover A hV
      (cuts i) hover' hne Q hQ₁ with ⟨source, hsource, hzero⟩ | ⟨j, hj⟩
  · exact hcomponents i source hsource hzero
  · exact hloops i j hj

end GraphMinor.GM06
