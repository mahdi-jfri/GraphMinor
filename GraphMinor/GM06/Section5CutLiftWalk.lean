module

public import GraphMinor.GM06.Section5CutLiftLink
import GraphMinor.GM11.Walks

/-!
# Lifting a walk until it reaches the seam

Lift successive links while the current vertex is off the linkage.
Stop at the first vertex on it. If the original walk avoids the
initial vertex, every vertex of the lifted prefix also projects
away from that vertex. This is the path-lifting step for connecting
the punctured cut drawing to its boundary core in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- An original walk to the linkage which avoids its initial vertex
has a lifted prefix reaching a seam vertex and avoiding both initial copies. -/
theorem exists_cut_walk_to_linkage_avoiding_initial
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    {x : D} (hxF : x ∈ F.V) {v : ClosedCylinder}
    (W : GraphWalk G.toGraph (radialCylinderProjection x.1) v)
    (hv : v ∈ (L.pathDrawing 0).V)
    (havoid : ∀ z ∈ W.support, z ≠ cylinderM1Point 1 0) :
    ∃ y : D, ∃ R : GraphWalk F.toGraph x y,
      radialCylinderProjection y.1 ∈ (L.pathDrawing 0).V ∧
      ∀ z ∈ R.support, radialCylinderProjection z.1 ≠ cylinderM1Point 1 0 := by
  have hlift : ∀ {s t : ClosedCylinder} (W : GraphWalk G.toGraph s t),
      t ∈ (L.pathDrawing 0).V →
      (∀ z ∈ W.support, z ≠ cylinderM1Point 1 0) →
      ∀ x : D, x ∈ F.V → radialCylinderProjection x.1 = s →
      ∃ y : D, ∃ R : GraphWalk F.toGraph x y,
        radialCylinderProjection y.1 ∈ (L.pathDrawing 0).V ∧
        ∀ z ∈ R.support, radialCylinderProjection z.1 ≠ cylinderM1Point 1 0 := by
    intro s t W
    induction W with
    | nil hs =>
      intro ht hn x hx hp
      refine ⟨x, GraphWalk.nil hx, hp.symm ▸ ht, ?_⟩
      intro z hz
      have hzx : z = x := List.mem_singleton.mp hz
      rw [hzx, hp]
      exact hn _ (List.mem_singleton_self _)
    | @cons s a t e hl W ih =>
      intro ht hn x hx hp
      by_cases hsP : s ∈ (L.pathDrawing 0).V
      · refine ⟨x, GraphWalk.nil hx, hp.symm ▸ hsP, ?_⟩
        intro z hz
        have hzx : z = x := List.mem_singleton.mp hz
        rw [hzx, hp]
        exact hn s List.mem_cons_self
      · have hxP : radialCylinderProjection x.1 ∉ (L.pathDrawing 0).V := hp.symm ▸ hsP
        have hl' : G.toGraph.IsLink e (radialCylinderProjection x.1) a := hp.symm ▸ hl
        obtain ⟨x', hxx', hp'⟩ := exists_cut_link_at_non_seam_vertex L hG hθ hD hBd hstrip
          F hFU hFV hEdges hx hxP hl'
        obtain ⟨y, R, hy, hR⟩ := ih ht
          (fun z hz => hn z (List.mem_cons_of_mem s hz)) x' hxx'.right_mem hp'
        refine ⟨y, GraphWalk.cons hxx' R, hy, ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with hzx | hz
        · rw [hzx, hp]
          exact hn s List.mem_cons_self
        · exact hR z hz
  exact hlift W hv havoid x hxF rfl

end GraphMinor.GM06
