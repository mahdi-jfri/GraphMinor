module

public import GraphMinor.GM13.Section7WallWalks

/-!
# Graph Minors XIII, Section 7: the distance of a wall whose faces are named

The file `Section7WallWalks.lean` gives the exact formula `d(s, t) = [s] + [t] + D(F, G)` for the
wall of Fig. 1, where `D` is the distance between faces of the wall. In (7.3) we pass to a wall
`H'` inside the wall `H` of Fig. 1, drawn with the drawing it gets from `H`. Each face of `H'` is
a union of faces of `H`, so the same formula should hold with each square of the grid named by
the face of `H'` that contains it.

This file proves the formula for any drawing `𝒰` made of cells and any naming `name` of the
squares by the faces of the elementary wall of height `h`, under local conditions
(`FaceNaming`):

* the squares around a cell off the drawing have the same name, and the names of the squares
  around a cell of the drawing are equal or touch (this gives the lower bound
  `FaceNaming.le_planeWallDist`, as in `le_planeWallDist_fig1`);
* squares with the same name are joined by a cell walk of cost zero, faces that touch have
  squares joined by a walk of cost at most one, and every face names some square (this gives the
  upper bound `FaceNaming.planeWallDist_le`, as in `planeWallDist_fig1_le`).

The wall of Fig. 1 itself has such a naming (`fig1FaceNaming`). The comparison of two drawings
with namings (`FaceNaming.distGeSub`) reduces `d' ≥ d - K` to an inequality on faces.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-! ## Cell walks and a smaller drawing -/

namespace CellWalk

theorem cost_mono {𝒰 𝒱 : Set (ℤ × ℤ)} (h𝒰 : 𝒰 ⊆ 𝒱) :
    ∀ {c d : ℤ × ℤ} (w : CellWalk c d), w.cost 𝒰 ≤ w.cost 𝒱
  | c, _, nil _ => by
    simp only [cost]
    by_cases hc : c ∈ 𝒰
    · rw [cellInd_of_mem hc, cellInd_of_mem (h𝒰 hc)]
    · rw [cellInd_of_not_mem hc]; omega
  | c, _, cons _ w => by
    simp only [cost]
    have := cost_mono h𝒰 w
    by_cases hc : c ∈ 𝒰
    · rw [cellInd_of_mem hc, cellInd_of_mem (h𝒰 hc)]; omega
    · rw [cellInd_of_not_mem hc]; omega

theorem costTail_mono {𝒰 𝒱 : Set (ℤ × ℤ)} (h𝒰 : 𝒰 ⊆ 𝒱) {c d : ℤ × ℤ} (w : CellWalk c d) :
    w.costTail 𝒰 ≤ w.costTail 𝒱 := by
  cases w with
  | nil => simp [costTail]
  | cons _ w => exact cost_mono h𝒰 w

end CellWalk

/-- A smaller drawing gives a smaller cell distance. -/
theorem cellDist_mono {𝒰 𝒱 : Set (ℤ × ℤ)} (h𝒰 : 𝒰 ⊆ 𝒱) (c d : ℤ × ℤ) :
    cellDist 𝒰 c d ≤ cellDist 𝒱 c d := by
  obtain ⟨w, hw⟩ := exists_cellDist_eq 𝒱 c d
  have := cellDist_le 𝒰 w
  have := CellWalk.costTail_mono h𝒰 w
  omega

/-- Between two squares off the drawing the cell distance is symmetric. -/
theorem cellDist_comm_of_not_mem {𝒰 : Set (ℤ × ℤ)} {c d : ℤ × ℤ} (hc : c ∉ 𝒰) (hd : d ∉ 𝒰) :
    cellDist 𝒰 c d = cellDist 𝒰 d c := by
  have h1 := cellDist_symm_le 𝒰 c d
  have h2 := cellDist_symm_le 𝒰 d c
  rw [cellInd_of_not_mem hc, cellInd_of_not_mem hd] at h1 h2
  omega

/-! ## Namings of the squares by faces -/

/-- A naming of the squares of the grid by the faces of the elementary wall of height `h`, fitting
the drawing `𝒰`. -/
structure FaceNaming (𝒰 : Set (ℤ × ℤ)) (h : ℕ) (name : ℤ × ℤ → ℤ × ℤ) : Prop where
  /-- The drawing has no square. -/
  not_square : ∀ c ∈ 𝒰, ¬ IsSquareCell c
  /-- Every name is a face. -/
  face : ∀ q, IsBrick h (name q) ∨ name q = outFace
  /-- The squares around a cell off the drawing have the same name. -/
  free : ∀ c ∉ 𝒰, ∀ q ∈ squaresAbove c, ∀ q' ∈ squaresAbove c, name q = name q'
  /-- The names of the squares around a cell of the drawing are equal or touch. -/
  drawn : ∀ c ∈ 𝒰, ∀ q ∈ squaresAbove c, ∀ q' ∈ squaresAbove c,
    name q = name q' ∨ FaceAdj h (name q) (name q')
  /-- Squares with the same name are at cell distance zero. -/
  same : ∀ q q', IsSquareCell q → IsSquareCell q' → name q = name q' → cellDist 𝒰 q q' = 0
  /-- Touching faces name two squares at cell distance at most one. -/
  adj : ∀ F G, FaceAdj h F G → ∃ q q', IsSquareCell q ∧ IsSquareCell q' ∧ name q = F ∧
    name q' = G ∧ cellDist 𝒰 q q' ≤ 1
  /-- Every face names a square. -/
  surj : ∀ F, IsBrick h F ∨ F = outFace → ∃ q, IsSquareCell q ∧ name q = F

namespace FaceNaming

variable {𝒰 : Set (ℤ × ℤ)} {h : ℕ} {name : ℤ × ℤ → ℤ × ℤ} (N : FaceNaming 𝒰 h name)
include N

/-! ### The lower bound -/

/-- The least distance from a face named at the cell `c` to the face `G`. -/
noncomputable def distFrom (name : ℤ × ℤ → ℤ × ℤ) (h : ℕ) (c : ℤ × ℤ) (G : ℤ × ℤ) : ℕ :=
  sInf ((fun q => (faceDist h (name q) G).toNat) '' squaresAbove c)

omit N in
theorem exists_distFrom_eq (c G : ℤ × ℤ) :
    ∃ q ∈ squaresAbove c, (faceDist h (name q) G).toNat = distFrom name h c G := by
  have hne : ((fun q => (faceDist h (name q) G).toNat) '' squaresAbove c).Nonempty :=
    (squaresAbove_nonempty c).image _
  obtain ⟨q, hq, hq'⟩ := Nat.sInf_mem hne
  exact ⟨q, hq, hq'⟩

omit N in
theorem distFrom_le {c q : ℤ × ℤ} (hq : q ∈ squaresAbove c) (G : ℤ × ℤ) :
    distFrom name h c G ≤ (faceDist h (name q) G).toNat :=
  Nat.sInf_le ⟨q, hq, rfl⟩

/-- **Lower bound.** For points in different cells there are faces `F` at `s` and `G` at `t` with
`[s] + [t] + D(F, G) ≤ d(s, t)`. -/
theorem le_planeWallDist {s t : ℝ × ℝ} (hst : cellCode s ≠ cellCode t) :
    ∃ q ∈ squaresAbove (cellCode s), ∃ q' ∈ squaresAbove (cellCode t),
      cellInd 𝒰 (cellCode s) + cellInd 𝒰 (cellCode t) + (faceDist h (name q) (name q')).toNat ≤
        planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) := by
  have hψ : ∀ F G, FaceAdj h F G →
      distFrom name h (cellCode s) G ≤ distFrom name h (cellCode s) F + 1 := by
    intro F G hFG
    obtain ⟨q, hq, hqe⟩ := exists_distFrom_eq (name := name) (h := h) (cellCode s) F
    have h1 := distFrom_le (name := name) (h := h) hq G
    have h2 := faceDist_le_of_faceAdj (N.face q) hFG
    omega
  have hs : ∀ q ∈ squaresAbove (cellCode s), distFrom name h (cellCode s) (name q) = 0 := by
    intro q hq
    have h1 := distFrom_le (name := name) (h := h) hq (name q)
    rw [faceDist_self (N.face q)] at h1
    omega
  obtain ⟨q', hq', hle⟩ := le_planeWallDist_of_faces N.not_square name (FaceAdj h) N.free N.drawn
    (distFrom name h (cellCode s)) hψ hst hs
  obtain ⟨q, hq, hqe⟩ := exists_distFrom_eq (name := name) (h := h) (cellCode s) (name q')
  exact ⟨q, hq, q', hq', by rw [hqe]; exact hle⟩

/-! ### The upper bound -/

theorem square_not_mem {q : ℤ × ℤ} (hq : IsSquareCell q) : q ∉ 𝒰 :=
  fun h => N.not_square q h hq

/-- Squares of touching faces are at cell distance at most one. -/
theorem cellDist_le_one {q q' : ℤ × ℤ} (hq : IsSquareCell q) (hq' : IsSquareCell q')
    (hadj : FaceAdj h (name q) (name q')) : cellDist 𝒰 q q' ≤ 1 := by
  obtain ⟨r, r', hr, hr', e, e', hrr⟩ := N.adj _ _ hadj
  have h1 := N.same q r hq hr e.symm
  have h2 := N.same r' q' hr' hq' e'
  have t1 := cellDist_triangle 𝒰 q r r'
  have t2 := cellDist_triangle 𝒰 q r' q'
  omega

/-- A square named by each face. -/
noncomputable def rep (F : ℤ × ℤ) : ℤ × ℤ :=
  open Classical in
  if hF : IsBrick h F ∨ F = outFace then (N.surj F hF).choose else (0, 0)

theorem rep_spec {F : ℤ × ℤ} (hF : IsBrick h F ∨ F = outFace) :
    IsSquareCell (N.rep F) ∧ name (N.rep F) = F := by
  unfold rep
  rw [dite_eq_left hF]
  exact (N.surj F hF).choose_spec

/-- Along the bricks, the cell distance between named squares is at most the step count. -/
theorem cellDist_rep_le_hexDist :
    ∀ n : ℕ, ∀ F G : ℤ × ℤ, IsBrick h F → IsBrick h G → hexDist F G ≤ n →
      cellDist 𝒰 (N.rep F) (N.rep G) ≤ n
  | 0, F, G, hF, hG, hd => by
    have hFG : F = G := by
      unfold IsBrick at hF hG
      unfold hexDist at hd
      exact Prod.ext (by omega) (by omega)
    subst hFG
    simp [cellDist_self]
  | n + 1, F, G, hF, hG, hd => by
    by_cases hFG : F = G
    · subst hFG
      simp [cellDist_self]
    obtain ⟨F', hF', h1, h2⟩ := exists_hex_step hF hG hFG
    obtain ⟨s1, e1⟩ := N.rep_spec (Or.inl hF)
    obtain ⟨s2, e2⟩ := N.rep_spec (Or.inl hF')
    have a1 := N.cellDist_le_one s1 s2 (by rw [e1, e2]; exact Or.inl ⟨hF, hF', h1⟩)
    have a2 := cellDist_rep_le_hexDist n F' G hF' hG (by push_cast at hd; omega)
    have := cellDist_triangle 𝒰 (N.rep F) (N.rep F') (N.rep G)
    omega

/-- The cell distance from the square named by a brick to the square named by the outer face is
at most the step count to the outer face. -/
theorem cellDist_rep_out_le :
    ∀ n : ℕ, ∀ F : ℤ × ℤ, IsBrick h F → outDepth h F ≤ n →
      cellDist 𝒰 (N.rep F) (N.rep outFace) ≤ n
  | 0, F, hF, hd => by
    have := one_le_outDepth hF
    omega
  | n + 1, F, hF, hd => by
    obtain ⟨s1, e1⟩ := N.rep_spec (Or.inl hF)
    obtain ⟨so, eo⟩ := N.rep_spec (h := h) (Or.inr rfl)
    by_cases h1 : outDepth h F = 1
    · have := N.cellDist_le_one s1 so (by rw [e1, eo]; exact Or.inr (Or.inr ⟨rfl, hF, h1⟩))
      omega
    · have h2 := one_le_outDepth hF
      obtain ⟨F', hF', e3, e4⟩ := exists_out_step hF (by omega)
      obtain ⟨s2, e2⟩ := N.rep_spec (Or.inl hF')
      have a1 := N.cellDist_le_one s1 s2 (by rw [e1, e2]; exact Or.inl ⟨hF, hF', e3⟩)
      have a2 := cellDist_rep_out_le n F' hF' (by push_cast at hd; omega)
      have := cellDist_triangle 𝒰 (N.rep F) (N.rep F') (N.rep outFace)
      omega

/-- The cell distance between named squares is symmetric. -/
theorem cellDist_rep_comm (F G : ℤ × ℤ) (hF : IsBrick h F ∨ F = outFace)
    (hG : IsBrick h G ∨ G = outFace) :
    cellDist 𝒰 (N.rep F) (N.rep G) = cellDist 𝒰 (N.rep G) (N.rep F) :=
  cellDist_comm_of_not_mem (N.square_not_mem (N.rep_spec hF).1)
    (N.square_not_mem (N.rep_spec hG).1)

/-- **Cell distance against face distance.** Two squares are at cell distance at most the
distance between their names. -/
theorem cellDist_le_faceDist {q q' : ℤ × ℤ} (hq : IsSquareCell q) (hq' : IsSquareCell q') :
    (cellDist 𝒰 q q' : ℤ) ≤ faceDist h (name q) (name q') := by
  have hne : ∀ {K : ℤ × ℤ}, IsBrick h K → K ≠ outFace :=
    fun hb hk => not_isBrick_outFace h (hk ▸ hb)
  obtain ⟨s1, e1⟩ := N.rep_spec (N.face q)
  obtain ⟨s2, e2⟩ := N.rep_spec (N.face q')
  have a1 := N.same q (N.rep (name q)) hq s1 e1.symm
  have a2 := N.same (N.rep (name q')) q' s2 hq' e2
  have t1 := cellDist_triangle 𝒰 q (N.rep (name q)) q'
  have t2 := cellDist_triangle 𝒰 (N.rep (name q)) (N.rep (name q')) q'
  -- it remains to bound the distance between the two named squares
  suffices key : (cellDist 𝒰 (N.rep (name q)) (N.rep (name q')) : ℤ) ≤
      faceDist h (name q) (name q') by omega
  have tri := fun a b c => cellDist_triangle 𝒰 a b c
  rcases N.face q with hb | ho <;> rcases N.face q' with hb' | ho'
  · rw [faceDist_of_ne (hne hb) (hne hb')]
    have b1 := N.cellDist_rep_le_hexDist (hexDist (name q) (name q')).toNat _ _ hb hb'
      (by have := hexDist_nonneg (name q) (name q'); omega)
    have b2 := N.cellDist_rep_out_le (outDepth h (name q)).toNat _ hb
      (by have := one_le_outDepth hb; omega)
    have b3 := N.cellDist_rep_out_le (outDepth h (name q')).toNat _ hb'
      (by have := one_le_outDepth hb'; omega)
    rw [N.cellDist_rep_comm _ _ (Or.inl hb') (Or.inr rfl)] at b3
    have := tri (N.rep (name q)) (N.rep outFace) (N.rep (name q'))
    have := hexDist_nonneg (name q) (name q')
    have := one_le_outDepth hb
    have := one_le_outDepth hb'
    rw [le_min_iff]
    constructor <;> omega
  · rw [ho', faceDist_out_right (hne hb)]
    have b2 := N.cellDist_rep_out_le (outDepth h (name q)).toNat _ hb
      (by have := one_le_outDepth hb; omega)
    have := one_le_outDepth hb
    omega
  · rw [ho, faceDist_out_left (hne hb')]
    have b3 := N.cellDist_rep_out_le (outDepth h (name q')).toNat _ hb'
      (by have := one_le_outDepth hb'; omega)
    rw [N.cellDist_rep_comm _ _ (Or.inl hb') (Or.inr rfl)] at b3
    have := one_le_outDepth hb'
    omega
  · rw [ho, ho', faceDist_out_out, cellDist_self]
    simp

/-- **Upper bound.** For points `s, t` in different cells, and any faces `F` at `s` and `G` at
`t`, `d(s, t) ≤ [s] + [t] + D(F, G)`. -/
theorem planeWallDist_le {s t : ℝ × ℝ} (hst : cellCode s ≠ cellCode t) {q q' : ℤ × ℤ}
    (hq : q ∈ squaresAbove (cellCode s)) (hq' : q' ∈ squaresAbove (cellCode t)) :
    (planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) : ℤ) ≤
      cellInd 𝒰 (cellCode s) + cellInd 𝒰 (cellCode t) + faceDist h (name q) (name q') := by
  have h1 := planeWallDist_cellSet_le_cellDist N.not_square hst
  have h2 := cellDist_le_of_cellRel 𝒰 (Or.inl hq.2 : CellRel (cellCode s) q)
  have h3 := cellDist_le_of_cellRel 𝒰 (Or.inr hq'.2 : CellRel q' (cellCode t))
  rw [cellInd_of_not_mem (N.square_not_mem hq.1)] at h2
  have h4 := N.cellDist_le_faceDist hq.1 hq'.1
  have t1 := cellDist_triangle 𝒰 (cellCode s) q q'
  have t2 := cellDist_triangle 𝒰 (cellCode s) q' (cellCode t)
  omega

/-- Two points of one cell are at distance at most two. -/
theorem planeWallDist_le_two_of_cellCode_eq {s t : ℝ × ℝ} (hst : cellCode s = cellCode t) :
    planeWallDist (fig1PlaneEquiv '' cellSet 𝒰) (fig1PlaneEquiv s) (fig1PlaneEquiv t) ≤ 2 := by
  by_cases he : s = t
  · subst he
    simp [planeWallDist]
  set c := cellCode s
  have hsq := cellUp_mem_squaresAbove c
  let w : CellWalk (cellCode s) (cellCode t) :=
    CellWalk.cons (Or.inl hsq.2 : CellRel c (cellUp c))
      (CellWalk.cons (Or.inr (hst ▸ hsq.2) : CellRel (cellUp c) (cellCode t))
        (CellWalk.nil _))
  have h1 := planeWallDist_cellSet_le N.not_square he w (by simp [w, CellWalk.isNil])
  have h2 : w.cost 𝒰 ≤ 2 := by
    simp only [w, CellWalk.cost]
    rw [cellInd_of_not_mem (N.square_not_mem hsq.1)]
    have := cellInd_le_one 𝒰 c
    have := cellInd_le_one 𝒰 (cellCode s)
    have := cellInd_le_one 𝒰 (cellCode t)
    omega
  omega

end FaceNaming

/-! ## Comparing two drawings -/

/-- **Comparison of distances.** Let `𝒰` and `𝒰'` be drawings with namings by the faces of the
walls of heights `h` and `h'`. Suppose that for any two distinct cells and any faces `F'`, `G'`
of `H'` named at them, there are faces `F`, `G` of `H` named at them with
`[c] + [d] + D(F, G) ≤ [c]' + [d]' + D'(F', G') + K`. Then `d ≤ d' + K`, if `K ≥ 2`. -/
theorem FaceNaming.distGeSub {𝒰 𝒰' : Set (ℤ × ℤ)} {h h' : ℕ} {name name' : ℤ × ℤ → ℤ × ℤ}
    (N : FaceNaming 𝒰 h name) (N' : FaceNaming 𝒰' h' name') (K : ℕ) (hK : 2 ≤ K)
    (hKI : ∀ c d : ℤ × ℤ, c ≠ d → ∀ q₀ ∈ squaresAbove c, ∀ q₀' ∈ squaresAbove d,
      ∃ q ∈ squaresAbove c, ∃ q' ∈ squaresAbove d,
        (cellInd 𝒰 c + cellInd 𝒰 d : ℤ) + faceDist h (name q) (name q') ≤
          cellInd 𝒰' c + cellInd 𝒰' d + faceDist h' (name' q₀) (name' q₀') + K) :
    DistGeSub (planeWallDist (fig1PlaneEquiv '' cellSet 𝒰'))
      (planeWallDist (fig1PlaneEquiv '' cellSet 𝒰)) K := by
  intro s t
  obtain ⟨s, rfl⟩ := fig1PlaneEquiv.surjective s
  obtain ⟨t, rfl⟩ := fig1PlaneEquiv.surjective t
  by_cases hst : cellCode s = cellCode t
  · have := N.planeWallDist_le_two_of_cellCode_eq hst
    omega
  obtain ⟨q₀, hq₀, q₀', hq₀', hlow⟩ := N'.le_planeWallDist hst
  obtain ⟨q, hq, q', hq', hki⟩ := hKI _ _ hst q₀ hq₀ q₀' hq₀'
  have hup := N.planeWallDist_le hst hq hq'
  have hnn : 0 ≤ faceDist h' (name' q₀) (name' q₀') := by
    rcases N'.face q₀ with hb | ho <;> rcases N'.face q₀' with hb' | ho'
    · have h1 := hexDist_nonneg (name' q₀) (name' q₀')
      have h2 := one_le_outDepth hb
      have h3 := one_le_outDepth hb'
      rw [faceDist_of_ne (fun e => not_isBrick_outFace h' (e ▸ hb))
        (fun e => not_isBrick_outFace h' (e ▸ hb'))]
      exact le_min h1 (by omega)
    · rw [ho', faceDist_out_right (fun e => not_isBrick_outFace h' (e ▸ hb))]
      have := one_le_outDepth hb
      omega
    · rw [ho, faceDist_out_left (fun e => not_isBrick_outFace h' (e ▸ hb'))]
      have := one_le_outDepth hb'
      omega
    · rw [ho, ho', faceDist_out_out]
  have : ((faceDist h' (name' q₀) (name' q₀')).toNat : ℤ) = faceDist h' (name' q₀) (name' q₀') :=
    Int.toNat_of_nonneg hnn
  omega

/-! ## The naming of the wall of Fig. 1 -/

theorem exists_eq_of_isSquareCell {q : ℤ × ℤ} (hq : IsSquareCell q) :
    ∃ x y : ℤ, q = (2 * x + 1, 2 * y + 1) := by
  obtain ⟨a, b⟩ := q
  unfold IsSquareCell at hq
  exact ⟨a / 2, b / 2, Prod.ext (by simp only; omega) (by simp only; omega)⟩

/-- The faces of the wall of Fig. 1 name the squares. -/
theorem fig1FaceNaming {h : ℕ} (hh : 1 ≤ h) (he : Even h) :
    FaceNaming (fig1WallCells h) h (wallFace h) where
  not_square := fun c hc => fig1WallCells_not_square h c hc
  face := isBrick_or_eq_outFace_wallFace h
  free := fun c hc q hq q' hq' => wallFace_eq_of_not_mem hh he hc hq hq'
  drawn := fun c _ q hq q' hq' => wallFace_eq_or_adj h hq hq'
  same := by
    intro q q' hq hq' e
    obtain ⟨x, y, rfl⟩ := exists_eq_of_isSquareCell hq
    obtain ⟨x', y', rfl⟩ := exists_eq_of_isSquareCell hq'
    exact cellDist_eq_zero_of_wallFace_eq hh he e
  adj := by
    intro F G hFG
    obtain ⟨x0, y0, x1, y1, m, h1, h2, h3, h4⟩ := exists_common_of_faceAdj hFG
    exact ⟨_, _, h3.1, h4.1, h1, h2,
      cellDist_le_one_of_common h3 h4 (square_not_mem_fig1WallCells x1 y1)⟩
  surj := by
    intro F hF
    rcases hF with hF | rfl
    · exact ⟨brickSq F, ⟨by unfold brickSq; simp only; omega, by unfold brickSq; simp only; omega⟩,
        wallFace_brickSq hF⟩
    · exact ⟨outBase, ⟨by decide, by decide⟩, wallFace_outBase⟩

end GraphMinor.GM13
