module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5NoReduction1
import GraphMinor.GM06.Section5SeparationDeletion
import GraphMinor.GM06.Section5HelixReduction1
import GraphMinor.GM11.Forest
import GraphMinor.GM11.Section5

/-!
# Removing clockwise edges on the discarded side

For Reduction 2 in VI (5.5), page 130, first delete clockwise
edges of its discarded side. Each deletion is a proved Reduction 1,
and the separation calculation keeps the retained side unchanged.
Induction on the discarded edge count terminates with no such edge.
The proved Reduction 1 comparison pulls every resulting helix back
through the finite sequence without increasing potential.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Exhaust clockwise deletions on the discarded side of a
separation, retaining an actual potential-nonincreasing helix pullback. -/
theorem exists_clockwise_reduced_separation_with_linkage_eq
    {k : ℕ} {G G₁ G₂ : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hoverlap : G₁.V ∩ G₂.V ⊆ {cylinderM1Point k i}) :
    ∃ H : Drawing ClosedCylinder, ∃ M : CylinderLinkage k H, ∃ T : Drawing ClosedCylinder,
      IsCylinderSection5Drawing k H ∧ IsGraphSeparation H.toGraph G₁.toGraph T.toGraph ∧
      G₁.V ∩ T.V ⊆ {cylinderM1Point k i} ∧
      (∀ e ∈ T.E, ¬ IsClockwiseInitialEdge M i e) ∧
      M.pathDrawing = L.pathDrawing ∧ M.curve = L.curve ∧
      ∀ f : Curve ClosedCylinder, IsHelix k H f →
        ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g ≤ curvePhi k H f := by
  classical
  generalize hn : G₂.E.ncard = n
  induction n using Nat.strong_induction_on generalizing G G₂ with
  | h n ih =>
    by_cases hclock : ∃ e ∈ G₂.E, IsClockwiseInitialEdge L i e
    · obtain ⟨e, he, hside⟩ := hclock
      obtain ⟨H, M, hH, hRed, hV, hE, _⟩ := exists_reduction1_deleting_clockwise_edge L hG
        (hsep.2.1.edgeSet_mono he) hside
      have hEq : M.pathDrawing = L.pathDrawing ∧ M.curve = L.curve := by
        obtain ⟨_, _, _, _, _, _, _, hp, hc⟩ := hRed
        exact ⟨hp, hc⟩
      have hnext := graph_separation_after_discarded_edge_deletion hsep he hV hE
      have hover : G₁.V ∩ (G₂.deleteEdge e).V ⊆ {cylinderM1Point k i} := by
        rw [GraphMinor.GM11.deleteEdge_V]
        exact hoverlap
      have hless : (G₂.deleteEdge e).E.ncard < n := by
        rw [GraphMinor.GM11.deleteEdge_E, ← hn]
        exact ncard_sdiff_singleton_lt_of_mem he G₂.finite_edges
      obtain ⟨K, N, T, hK, hsepK, hoverK, hnoK, hNP, hNC, hback⟩ := ih _ hless
        (L := M) hH hnext hover rfl
      refine ⟨K, N, T, hK, hsepK, hoverK, hnoK, hNP.trans hEq.1, hNC.trans hEq.2, ?_⟩
      intro f hf
      obtain ⟨g, hg, hφg⟩ := hback f hf
      obtain ⟨g₀, hg₀, hφ₀⟩ := theorem_5_5_red1 L M hG hH hRed g hg
      exact ⟨g₀, hg₀, hφ₀.trans hφg⟩
    · refine ⟨G, L, G₂, hG, hsep, hoverlap, ?_, rfl, rfl, ?_⟩
      · intro e he hside
        exact hclock ⟨e, he, hside⟩
      · intro f hf
        exact ⟨f, hf, le_rfl⟩

/-- Forget the explicit linkage equalities after exhausting the
clockwise discarded edges and retaining the helix pullback. -/
theorem exists_clockwise_reduced_separation
    {k : ℕ} {G G₁ G₂ : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hoverlap : G₁.V ∩ G₂.V ⊆ {cylinderM1Point k i}) :
    ∃ H : Drawing ClosedCylinder, ∃ M : CylinderLinkage k H, ∃ T : Drawing ClosedCylinder,
      IsCylinderSection5Drawing k H ∧ IsGraphSeparation H.toGraph G₁.toGraph T.toGraph ∧
      G₁.V ∩ T.V ⊆ {cylinderM1Point k i} ∧
      (∀ e ∈ T.E, ¬ IsClockwiseInitialEdge M i e) ∧
      ∀ f : Curve ClosedCylinder, IsHelix k H f →
        ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g ≤ curvePhi k H f := by
  obtain ⟨H, M, T, hH, hsepH, hover, hno, _, _, hback⟩ :=
    exists_clockwise_reduced_separation_with_linkage_eq L hG i hsep hoverlap
  exact ⟨H, M, T, hH, hsepH, hover, hno, hback⟩

end GraphMinor.GM06
