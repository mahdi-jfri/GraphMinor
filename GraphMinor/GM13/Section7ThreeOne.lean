module

public import GraphMinor.GM13.Section7TransKFar
public import GraphMinor.GM13.Section7ThreeWall

/-!
# Graph Minors XIII, (7.3) with `r = 1`

This file proves (7.3) of Graph Minors XIII (page 90) for `r = 1`, in the form of
`theorem_7_3_zero`: the new wall `H'` carries the drawing induced by `H`.

For `r = 1` the new wall must have height `h - 4`, its distance may drop by `8`, and no vertex
of it may be at distance `≤ 1` from `v`. Two distinct points of the drawing are at distance at
least `2`, so the last condition only asks that `v` is not in `H'`. So two steps of height `2`
suffice: a step of the case `r = 0` that deletes the element `mv` of `v`
(`exists_deleting_shape_of_eq`), then the subwall moved by `(1, 1)`. Each step has constant
`4`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

/-- **A far chain for `k = 2`**, for every element `mv` of the wall. -/
theorem exists_far_chain_two {h : ℕ} (hh : 6 ≤ h) (he : Even h) {mv : ℤ × ℤ}
    (hmv : mv ∈ fig1WallCells h) :
    ∃ K ≤ 8, ∃ c : Chain h (h - 4) K, c.Far mv 2 := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 4 := ⟨h - 4, by omega⟩
  rw [show h' + 4 - 4 = h' by omega]
  have hh' : 1 ≤ h' := by omega
  have he' : Even h' := by
    obtain ⟨a, ha⟩ := he
    exact ⟨a - 2, by omega⟩
  have he2 : Even (h' + 2) := by
    obtain ⟨a, ha⟩ := he'
    exact ⟨a + 1, by omega⟩
  obtain ⟨τ, hKI, hown, R, hray, hmono⟩ :=
    exists_deleting_shape_of_eq (h' := h' + 2) rfl (by omega) he2 hmv
  let s : Step (h' + 4) (h' + 2) 4 :=
    { τ := τ, R := R, ki := hKI, two_le := by omega, pos := by omega, even := he2, rayOK := hray,
      rowMono := hmono }
  let t : Step (h' + 2 * 1) h' (2 * (2 * 1)) :=
    transStepK h' 1 hh' he' (i := 1) (j := 1) ⟨by omega, by omega, by omega, by omega, by omega⟩
      (by omega) (by omega) (by omega) (by omega)
  refine ⟨4 + (2 * (2 * 1) + 0), by omega, Chain.cons s (Chain.cons t (Chain.nil h')), ?_⟩
  intro m _ hm
  refine ⟨?_, fun F hF G hG => ?_⟩
  · intro e
    apply hm
    rw [e]
    change (τ.own mv).bind _ = none
    rw [hown]
    rfl
  · have := faceDist_nonneg (isWallFace_of_mem_cellFaces hF) (isWallFace_of_mem_cellFaces hG)
    push_cast
    omega

variable {α : Type u} {β : Type v}

/-- **Graph Minors XIII, (7.3) with `r = 1`** (page 90), with `H'` drawn as its drawing induced
by `H`. -/
theorem theorem_7_3_one (H : DrawnWall α β) (v : α) (hF : H.IsFigure1) (hv : v ∈ V(H.graph))
    (hh : 6 ≤ H.height) :
    ∃ H' : DrawnWall α β,
      H'.IsFigure1 ∧
      H'.graph ≤ H.graph ∧ H'.drawingU ⊆ H.drawingU ∧ H'.vertexPoint = H.vertexPoint ∧
      H'.height = H.height - 2 * 1 - 2 ∧ DistGeSub H'.planeDist H.planeDist (4 * 1 + 4) ∧
      (∀ u ∈ V(H'.graph), ¬ H.dist u v ≤ 1) ∧
      ∃ (φ : EuclideanPlane ≃ₜ EuclideanPlane) (Γ : GraphDrawing H.graph EuclideanPlane),
        IsFigure1CoordDrawing H.toWall Γ ∧ H.drawingU = φ '' Γ.drawing.U ∧
        (∀ (u : α) (hu : u ∈ V(H.graph)), H.vertexPoint u = φ (Γ.iso.vertexEquiv ⟨u, hu⟩).1) ∧
        H'.drawingU = φ '' indU Γ H'.toWall := by
  refine exists_induced_of_far_chains H v 1 hF hv ?_
  intro mv hmv
  rw [show H.height - 2 * 1 - 2 = H.height - 4 by omega]
  exact exists_far_chain_two hh H.even_height hmv

end GraphMinor.GM13
