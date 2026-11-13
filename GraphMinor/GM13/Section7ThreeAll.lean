module

public import GraphMinor.GM13.Section7HexHoleFar
public import GraphMinor.GM13.Section7ThreeWall
public import GraphMinor.GM13.Parallel

/-!
# Graph Minors XIII, (7.3) for every `r`

This file proves (7.3) of *Graph Minors XIII* (page 90) for every `r ≥ 0` with `h ≥ 2r + 4`, in
the form of `theorem_7_3_one`: the new wall `H'` is drawn as in Fig. 1, and it carries the drawing
induced by `H` (`theorem_7_3_induced`). Dropping the second fact gives `theorem_7_3`, the form
`GM13Theorem73Statement` that Section 9 uses.

For `r = 0` this is `theorem_7_3_zero`. For `r ≥ 1` write `k = r + 1`. By
`exists_induced_of_far_chains` it is enough to give, for every element `mv` of the wall, a chain
from height `h` to height `h - 2k` with constant at most `4k` that is far from `mv`. If `mv` is
at distance at most `k` from a side of the wall, the moved subwall of `exists_far_chain_near`
does it. Otherwise the hexagonal hole of `exists_far_chain_deep` does it.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

/-- **A far chain for every element**, for `k ≥ 2`. -/
theorem exists_far_chain {h k : ℕ} (hk : 2 ≤ k) (hh : 2 * k + 2 ≤ h) (he : Even h)
    {mv : ℤ × ℤ} (hmv : mv ∈ fig1WallCells h) :
    ∃ c : Chain h (h - 2 * k) (2 * (2 * k)), c.Far mv k := by
  by_cases hnear : sideB mv ≤ k ∨ sideT h mv ≤ k ∨ sideL mv ≤ k ∨ sideR h mv ≤ k
  · exact exists_far_chain_near hk (by omega) he hmv hnear
  · push Not at hnear
    exact exists_far_chain_deep hk (by omega) he hmv hnear

variable {α : Type u} {β : Type v}

/-- **Graph Minors XIII, (7.3)** (page 90), with `H'` drawn as its drawing induced by `H`. The
paper's statement: "(7.3) *Let $H$ be a wall of height $h$ with distance function $d$ and let
$v \in V(H)$. Let $r \ge 0$ be an integer with $h \ge 2r + 4$. Then there is a subgraph $H'$ of
$H$, which is a wall of height $h - 2r - 2$, such that* *(i) $d' \ge d - 4r - 4$, where $d'$ is
the distance function in $H'$* *(ii) there is no vertex $u$ of $H'$ with $d(u, v) \le r$.*" Here
the wall `H` is drawn as in Fig. 1, and the conclusion also says how `H'` is drawn. -/
theorem theorem_7_3_induced (H : DrawnWall α β) (v : α) (r : ℕ) (hF : H.IsFigure1)
    (hv : v ∈ V(H.graph)) (hh : 2 * r + 4 ≤ H.height) :
    ∃ H' : DrawnWall α β,
      H'.IsFigure1 ∧
      H'.graph ≤ H.graph ∧ H'.drawingU ⊆ H.drawingU ∧ H'.vertexPoint = H.vertexPoint ∧
      H'.height = H.height - 2 * r - 2 ∧ DistGeSub H'.planeDist H.planeDist (4 * r + 4) ∧
      (∀ u ∈ V(H'.graph), ¬ H.dist u v ≤ r) ∧
      ∃ (φ : EuclideanPlane ≃ₜ EuclideanPlane) (Γ : GraphDrawing H.graph EuclideanPlane),
        IsFigure1CoordDrawing H.toWall Γ ∧ H.drawingU = φ '' Γ.drawing.U ∧
        (∀ (u : α) (hu : u ∈ V(H.graph)), H.vertexPoint u = φ (Γ.iso.vertexEquiv ⟨u, hu⟩).1) ∧
        H'.drawingU = φ '' indU Γ H'.toWall := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simpa using theorem_7_3_zero H v hF hv (by omega)
  refine exists_induced_of_far_chains H v r hF hv ?_
  intro mv hmv
  obtain ⟨c, hc⟩ := exists_far_chain (k := r + 1) (by omega) (by omega) H.even_height hmv
  rw [show H.height - 2 * r - 2 = H.height - 2 * (r + 1) by omega]
  exact ⟨_, by omega, c, hc⟩

/-- **Graph Minors XIII, (7.3)** (Section 7, page 90), in the form `GM13Theorem73Statement`:
`theorem_7_3_induced` without the description of the drawing of `H'`. -/
theorem theorem_7_3_proof : GM13Theorem73Statement.{u, v} := by
  intro α β H v r hF hv hh
  obtain ⟨H', hF', hle, hU, hP, hht, hd, hfar, -⟩ := theorem_7_3_induced H v r hF hv hh
  exact ⟨H', hF', hle, hU, hP, hht, hd, hfar⟩

end GraphMinor.GM13
