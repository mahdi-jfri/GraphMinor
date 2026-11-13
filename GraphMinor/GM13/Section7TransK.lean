module

public import GraphMinor.GM13.Section7Chain
public import GraphMinor.GM13.Section7RealizeMove

/-!
# Graph Minors XIII, (7.3): subwalls moved by a long vector

This file is the first half of the proof of (7.3) for an element near the border of the wall
(Graph Minors XIII, page 90). For `k ≥ 1`, a wall of height `h'` sits inside a wall of height
`h' + 2k` as a copy moved by a vector `(i, j)`: the vertex `(x, y)` of the small wall is the
vertex `(x + i, y + j)` of the large one. We take `0 ≤ i ≤ 4k`, `0 ≤ j ≤ 2k` and `i + j` even
(`TransVecK`). This generalizes `transShape` of `Section7Translate.lean`, where `k = 1`.

* `transShapeK`: the shape of the moved subwall. The faces outside the small wall reach the
  outer face by steps across deleted elements (`transK_conn`): go down from a face below the
  small wall, up from a face above it, left or right from a face beside it.
* `transShapeK_depthTestK`: for `1 ≤ i ≤ 4k - 1` and `1 ≤ j ≤ 2k - 1` the shape passes the depth
  test with constant `2k`, so it has `KI (4k)`.
* `transRealizationK`: the realization of the moved subwall.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-! ## The moved subwall -/

/-- The vector `(i, j)` keeps the small wall of height `h'` inside the large one of height
`h' + 2k`. -/
structure TransVecK (k : ℕ) (i j : ℤ) : Prop where
  i0 : 0 ≤ i
  i4 : i ≤ 4 * k
  j0 : 0 ≤ j
  j2 : j ≤ 2 * k
  par : (i + j) % 2 = 0

theorem TransVecK.isBrick {k : ℕ} {i j : ℤ} (hv : TransVecK k i j) {h' : ℕ} {F : ℤ × ℤ}
    (hF : IsBrick h' (F.1 - i, F.2 - j)) : IsBrick (h' + 2 * k) F := by
  obtain ⟨_, _, _, _, _⟩ := hv
  unfold IsBrick at *
  push_cast
  omega

theorem TransVecK.transPi_outFace {k : ℕ} {i j : ℤ} (hv : TransVecK k i j) (h' : ℕ) :
    transPi h' i j outFace = outFace := by
  have := hv.j0
  unfold transPi
  rw [ite_eq_right_iff.mpr (fun h => absurd h ?_)]
  unfold IsBrick outFace
  omega

/-- Moving a square moves its face. -/
theorem TransVecK.transPi_wallFace {k : ℕ} {i j : ℤ} (hv : TransVecK k i j) (h' : ℕ)
    (q : ℤ × ℤ) :
    transPi h' i j (wallFace (h' + 2 * k) q) = wallFace h' (q.1 - 2 * i, q.2 - 2 * j) := by
  unfold wallFace
  rw [brickOf_sub hv.par]
  split_ifs with h1 h2 h2
  · unfold transPi; rw [if_pos h2]
  · unfold transPi; rw [if_neg h2]
  · exact absurd (hv.isBrick h2) h1
  · exact hv.transPi_outFace h'

theorem TransVecK.image_cellFaces {k : ℕ} {i j : ℤ} (hv : TransVecK k i j) (h' : ℕ)
    (m : ℤ × ℤ) :
    transPi h' i j '' cellFaces (h' + 2 * k) m = cellFaces h' (m.1 - 2 * i, m.2 - 2 * j) := by
  ext F
  simp only [cellFaces, mem_image]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨_, (mem_squaresAbove_sub i j).mpr hq, (hv.transPi_wallFace h' q).symm⟩
  · rintro ⟨q', hq', rfl⟩
    refine ⟨_, ⟨(q'.1 + 2 * i, q'.2 + 2 * j), ?_, rfl⟩, ?_⟩
    · rw [← mem_squaresAbove_sub i j]
      simpa using hq'
    · rw [hv.transPi_wallFace]
      simp

theorem even_add_two_mul {h' : ℕ} (he' : Even h') (k : ℕ) : Even (h' + 2 * k) := by
  obtain ⟨a, ha⟩ := he'
  exact ⟨a + k, by omega⟩

/-- **The moved subwall as a shape.** The steps from the faces outside the small wall to the
outer face are an argument here; `transK_conn` gives them. -/
def transShapeK (h' k : ℕ) (hh' : 1 ≤ h') (he' : Even h') {i j : ℤ} (hv : TransVecK k i j)
    (hconn : ∀ F, IsWallFace (h' + 2 * k) F → transPi h' i j F = outFace →
      Relation.ReflTransGen (DelStep (h := h' + 2 * k) (transOwn h' i j)) F outFace) :
    Shape (h' + 2 * k) h' where
  own := transOwn h' i j
  π := transPi h' i j
  own_mem := by
    intro m _ m' hm'
    unfold transOwn at hm'
    split_ifs at hm' with h1
    · cases hm'
      exact (mem_fig1WallCells_iff hh' he' _).mpr h1
  own_surj := by
    intro m' hm'
    have h1 := (mem_fig1WallCells_iff hh' he' _).mp hm'
    have hv' := hv
    obtain ⟨_, _, _, _, _⟩ := hv'
    refine ⟨(m'.1 + 2 * i, m'.2 + 2 * j), ?_, ?_⟩
    · rw [mem_fig1WallCells_iff (by omega) (even_add_two_mul he' k)]
      unfold IsWallCell at *
      push_cast
      omega
    · unfold transOwn
      simp only [add_sub_cancel_right, Prod.mk.eta]
      rw [if_pos h1]
  π_face := by
    intro F _
    unfold transPi
    split_ifs with h1
    · exact Or.inl h1
    · exact Or.inr rfl
  π_surj := by
    intro F' hF'
    rcases hF' with hb | rfl
    · refine ⟨(F'.1 + i, F'.2 + j), Or.inl (hv.isBrick (by simpa using hb)), ?_⟩
      unfold transPi
      simp only [add_sub_cancel_right, Prod.mk.eta]
      rw [if_pos hb]
    · exact ⟨outFace, Or.inr rfl, hv.transPi_outFace h'⟩
  del := by
    intro m _ hown F hF G hG
    have hnot : (m.1 - 2 * i, m.2 - 2 * j) ∉ fig1WallCells h' := by
      rw [mem_fig1WallCells_iff hh' he']
      intro h1
      unfold transOwn at hown
      rw [if_pos h1] at hown
      exact absurd hown (by simp)
    have h1 : transPi h' i j F ∈ cellFaces h' (m.1 - 2 * i, m.2 - 2 * j) := by
      rw [← hv.image_cellFaces]; exact mem_image_of_mem _ hF
    have h2 : transPi h' i j G ∈ cellFaces h' (m.1 - 2 * i, m.2 - 2 * j) := by
      rw [← hv.image_cellFaces]; exact mem_image_of_mem _ hG
    obtain ⟨q, hq, e⟩ := h1
    obtain ⟨q', hq', e'⟩ := h2
    rw [← e, ← e']
    exact wallFace_eq_of_not_mem hh' he' hnot hq hq'
  keep := by
    intro m _ m' hm'
    unfold transOwn at hm'
    split_ifs at hm' with h1
    cases hm'
    exact hv.image_cellFaces h' m
  conn := by
    intro F G hF hG he
    by_cases ho : transPi h' i j F = outFace
    · exact (hconn F hF ho).trans (reflTransGen_delStep_symm (hconn G hG (he ▸ ho)))
    · obtain ⟨-, e1⟩ := transPi_eq_of_ne ho
      obtain ⟨-, e2⟩ := transPi_eq_of_ne (he ▸ ho)
      rw [e1, e2] at he
      simp only [Prod.mk.injEq] at he
      have : F = G := Prod.ext (by omega) (by omega)
      rw [this]

/-- The left square of a brick lies in that brick. -/
theorem wallFace_left_sq {h : ℕ} {X Y : ℤ} (hb : IsBrick h (X, Y)) :
    wallFace h (2 * X - 1, 2 * Y + 1) = (X, Y) := by
  have e : brickOf (2 * X - 1, 2 * Y + 1) = (X, Y) := by
    unfold IsBrick at hb
    simp only [brickOf, Prod.mk.injEq] at hb ⊢
    omega
  unfold wallFace
  rw [e, if_pos hb]

/-- The right square of a brick lies in that brick. -/
theorem wallFace_right_sq {h : ℕ} {X Y : ℤ} (hb : IsBrick h (X, Y)) :
    wallFace h (2 * X + 1, 2 * Y + 1) = (X, Y) := by
  have e : brickOf (2 * X + 1, 2 * Y + 1) = (X, Y) := by
    unfold IsBrick at hb
    simp only [brickOf, Prod.mk.injEq] at hb ⊢
    omega
  unfold wallFace
  rw [e, if_pos hb]

/-! ## Steps to the outer face -/

section Conn

variable {h' k : ℕ} (hh' : 1 ≤ h') (he' : Even h') {i j : ℤ}
include hh' he'

/-- A step across a deleted cell `(a, b)` between the faces of two squares around it. -/
theorem transK_step (G H : ℤ × ℤ) (a b c d c' d' : ℤ) (h1 : IsWallCell (h' + 2 * k) (a, b))
    (h2 : ¬ IsWallCell h' (a - 2 * i, b - 2 * j))
    (h3 : (c, d) ∈ squaresAbove (a, b)) (h4 : (c', d') ∈ squaresAbove (a, b))
    (h5 : wallFace (h' + 2 * k) (c, d) = G) (h6 : wallFace (h' + 2 * k) (c', d') = H) :
    Relation.ReflTransGen (DelStep (h := h' + 2 * k) (transOwn h' i j)) G H := by
  refine .single (delStep_of ((mem_fig1WallCells_iff (by omega) (even_add_two_mul he' k) _).mpr h1)
    ?_ h3 h4 h5 h6)
  unfold transOwn
  rw [if_neg h2]

omit hh' he' in
/-- To reach the outer face from the face of a square `q`, it is enough to reach it from the
brick of `q` when that brick is in the wall. -/
theorem reflTransGen_out_of_brick {h : ℕ} {own : ℤ × ℤ → Option (ℤ × ℤ)} {F : ℤ × ℤ}
    {q : ℤ × ℤ} (h1 : Relation.ReflTransGen (DelStep (h := h) own) F (wallFace h q))
    (h2 : IsBrick h (brickOf q) →
      Relation.ReflTransGen (DelStep (h := h) own) (brickOf q) outFace) :
    Relation.ReflTransGen (DelStep (h := h) own) F outFace := by
  unfold wallFace at h1
  split_ifs at h1 with hb
  · exact h1.trans (h2 hb)
  · exact h1

/-- Down from a brick below the small wall. -/
theorem transK_down : ∀ (n : ℕ) (X Y : ℤ), Y = n → Y < j → IsBrick (h' + 2 * k) (X, Y) →
    Relation.ReflTransGen (DelStep (h := h' + 2 * k) (transOwn h' i j)) (X, Y) outFace := by
  intro n
  induction n with
  | zero =>
    intro X Y hY hj hb
    have hb0 := hb
    unfold IsBrick at hb0
    simp only at hb0
    refine reflTransGen_out_of_brick (q := (2 * X - 1, 2 * Y - 1))
      (transK_step hh' he' (k := k) (i := i) (j := j) _ _ (2 * X - 1) (2 * Y) (2 * X - 1) (2 * Y + 1) (2 * X - 1) (2 * Y - 1)
        (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (wallFace_left_sq hb) rfl) ?_
    intro hb'
    simp only [brickOf, IsBrick] at hb'
    omega
  | succ n ih =>
    intro X Y hY hj hb
    have hb0 := hb
    unfold IsBrick at hb0
    simp only at hb0
    refine reflTransGen_out_of_brick (q := (2 * X - 1, 2 * Y - 1))
      (transK_step hh' he' (k := k) (i := i) (j := j) _ _ (2 * X - 1) (2 * Y) (2 * X - 1) (2 * Y + 1) (2 * X - 1) (2 * Y - 1)
        (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (wallFace_left_sq hb) rfl) ?_
    intro hb'
    have e : brickOf (2 * X - 1, 2 * Y - 1) = (X - 1, Y - 1) := by
      simp only [brickOf, Prod.mk.injEq]; omega
    rw [e] at hb' ⊢
    exact ih _ _ (by push_cast at hY; omega) (by omega) hb'

/-- Up from a brick above the small wall. -/
theorem transK_up : ∀ (n : ℕ) (X Y : ℤ), (h' : ℤ) + 2 * k - 1 - Y = n → j + h' ≤ Y →
    IsBrick (h' + 2 * k) (X, Y) →
    Relation.ReflTransGen (DelStep (h := h' + 2 * k) (transOwn h' i j)) (X, Y) outFace := by
  intro n
  induction n with
  | zero =>
    intro X Y hY hj hb
    have hb0 := hb
    unfold IsBrick at hb0
    simp only at hb0
    push_cast at hb0
    refine reflTransGen_out_of_brick (q := (2 * X - 1, 2 * Y + 3))
      (transK_step hh' he' (k := k) (i := i) (j := j) _ _ (2 * X - 1) (2 * Y + 2) (2 * X - 1) (2 * Y + 1) (2 * X - 1) (2 * Y + 3)
        (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (wallFace_left_sq hb) rfl) ?_
    intro hb'
    simp only [brickOf, IsBrick] at hb'
    push_cast at hb'
    omega
  | succ n ih =>
    intro X Y hY hj hb
    have hb0 := hb
    unfold IsBrick at hb0
    simp only at hb0
    push_cast at hb0
    refine reflTransGen_out_of_brick (q := (2 * X - 1, 2 * Y + 3))
      (transK_step hh' he' (k := k) (i := i) (j := j) _ _ (2 * X - 1) (2 * Y + 2) (2 * X - 1) (2 * Y + 1) (2 * X - 1) (2 * Y + 3)
        (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (wallFace_left_sq hb) rfl) ?_
    intro hb'
    have e : brickOf (2 * X - 1, 2 * Y + 3) = (X - 1, Y + 1) := by
      simp only [brickOf, Prod.mk.injEq]; omega
    rw [e] at hb' ⊢
    exact ih _ _ (by push_cast at hY; omega) (by omega) hb'

/-- Left from a brick left of the small wall. -/
theorem transK_left : ∀ (n : ℕ) (X Y : ℤ), X = n → X ≤ i → IsBrick (h' + 2 * k) (X, Y) →
    Relation.ReflTransGen (DelStep (h := h' + 2 * k) (transOwn h' i j)) (X, Y) outFace := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X Y hX hi hb
    have hb0 := hb
    unfold IsBrick at hb0
    simp only at hb0
    refine reflTransGen_out_of_brick (q := (2 * X - 3, 2 * Y + 1))
      (transK_step hh' he' (k := k) (i := i) (j := j) _ _ (2 * X - 2) (2 * Y + 1) (2 * X - 1) (2 * Y + 1) (2 * X - 3) (2 * Y + 1)
        (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (wallFace_left_sq hb) rfl) ?_
    intro hb'
    have e : brickOf (2 * X - 3, 2 * Y + 1) = (X - 2, Y) := by
      simp only [brickOf, Prod.mk.injEq]; omega
    rw [e] at hb' ⊢
    have h0 : 1 ≤ X - 2 := by unfold IsBrick at hb'; simp only at hb'; omega
    exact ih (n - 2) (by omega) _ _ (by omega) (by omega) hb'

/-- Right from a brick right of the small wall. -/
theorem transK_right : ∀ (n : ℕ) (X Y : ℤ), 2 * ((h' : ℤ) + 2 * k) - X = n →
    2 * (h' : ℤ) + i + 1 ≤ X → IsBrick (h' + 2 * k) (X, Y) →
    Relation.ReflTransGen (DelStep (h := h' + 2 * k) (transOwn h' i j)) (X, Y) outFace := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X Y hX hi hb
    have hb0 := hb
    unfold IsBrick at hb0
    simp only at hb0
    push_cast at hb0
    refine reflTransGen_out_of_brick (q := (2 * X + 3, 2 * Y + 1))
      (transK_step hh' he' (k := k) (i := i) (j := j) _ _ (2 * X + 2) (2 * Y + 1) (2 * X + 1) (2 * Y + 1) (2 * X + 3) (2 * Y + 1)
        (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (wallFace_right_sq hb) rfl) ?_
    intro hb'
    have e : brickOf (2 * X + 3, 2 * Y + 1) = (X + 2, Y) := by
      simp only [brickOf, Prod.mk.injEq]; omega
    rw [e] at hb' ⊢
    have h0 : X + 2 ≤ 2 * ((h' : ℤ) + 2 * k) := by
      unfold IsBrick at hb'; simp only at hb'; push_cast at hb'; omega
    exact ih (n - 2) (by omega) _ _ (by omega) (by omega) hb'

/-- **The steps out for the moved subwall.** -/
theorem transK_conn (hv : TransVecK k i j) (F : ℤ × ℤ) (hF : IsWallFace (h' + 2 * k) F)
    (hπ : transPi h' i j F = outFace) :
    Relation.ReflTransGen (DelStep (h := h' + 2 * k) (transOwn h' i j)) F outFace := by
  rcases hF with hF | rfl
  swap
  · exact .refl
  obtain ⟨X, Y⟩ := F
  have hnb : ¬ IsBrick h' (X - i, Y - j) := by
    intro hb
    unfold transPi at hπ
    rw [if_pos hb] at hπ
    unfold IsBrick at hb
    simp only [outFace, Prod.mk.injEq] at hπ
    omega
  have hF' := hF
  unfold IsBrick at hF' hnb
  simp only at hF' hnb
  obtain ⟨_, _, _, _, hpar⟩ := hv
  have hcase : Y < j ∨ j + h' ≤ Y ∨ X ≤ i ∨ 2 * (h' : ℤ) + i + 1 ≤ X := by omega
  rcases hcase with hc | hc | hc | hc
  · exact transK_down hh' he' Y.toNat X Y (by omega) hc hF
  · exact transK_up hh' he' ((h' : ℤ) + 2 * k - 1 - Y).toNat X Y
      (by push_cast at hF'; omega) hc hF
  · exact transK_left hh' he' X.toNat X Y (by omega) hc hF
  · exact transK_right hh' he' (2 * ((h' : ℤ) + 2 * k) - X).toNat X Y
      (by push_cast at hF'; omega) hc hF

end Conn

/-- **The moved subwall of height drop `2k`.** -/
def transShapeK' (h' k : ℕ) (hh' : 1 ≤ h') (he' : Even h') {i j : ℤ} (hv : TransVecK k i j) :
    Shape (h' + 2 * k) h' :=
  transShapeK h' k hh' he' hv (transK_conn hh' he' hv)

/-! ## The depth test -/

/-- A bound on the depth of the face of a square from one side of its brick. -/
theorem faceDepth_wallFace_le {h : ℕ} {q : ℤ × ℤ} {D : ℤ} (hD : 0 ≤ D)
    (H : (brickOf q).2 + 1 ≤ D ∨ (h : ℤ) - (brickOf q).2 ≤ D ∨ ((brickOf q).1 + 1) / 2 ≤ D ∨
      (2 * (h : ℤ) + 2 - (brickOf q).1) / 2 ≤ D) :
    faceDepth h (wallFace h q) ≤ D := by
  unfold wallFace
  split_ifs with hb
  · rw [faceDepth_of_isBrick hb]
    unfold outDepth
    omega
  · simp [faceDepth, hD]

/-- Comparing two minima of four numbers term by term. -/
theorem min4_le_min4_add {a b c d a' b' c' d' K : ℤ} (h1 : a ≤ a' + K) (h2 : b ≤ b' + K)
    (h3 : c ≤ c' + K) (h4 : d ≤ d' + K) :
    min (min a b) (min c d) ≤ min (min a' b') (min c' d') + K := by
  omega

/-- **The depth test for the moved subwall** with `1 ≤ i ≤ 4k - 1` and `1 ≤ j ≤ 2k - 1`. -/
theorem transShapeK_depthTestK (h' k : ℕ) (hh' : 1 ≤ h') (he' : Even h') {i j : ℤ}
    (hv : TransVecK k i j) (hi1 : 1 ≤ i) (hi2 : i + 1 ≤ 4 * k) (hj1 : 1 ≤ j)
    (hj2 : j + 1 ≤ 2 * k) :
    (transShapeK' h' k hh' he' hv).DepthTestK (2 * k) where
  one_le := by omega
  out := hv.transPi_outFace h'
  hex := by
    intro F G _ _ hF' hG'
    change IsBrick h' (transPi h' i j F) at hF'
    change IsBrick h' (transPi h' i j G) at hG'
    change hexDist F G ≤ hexDist (transPi h' i j F) (transPi h' i j G) + ((2 * (2 * k) - 2 : ℕ) : ℤ)
    have nF : transPi h' i j F ≠ outFace := by
      intro e; rw [e] at hF'; exact not_isBrick_outFace h' hF'
    have nG : transPi h' i j G ≠ outFace := by
      intro e; rw [e] at hG'; exact not_isBrick_outFace h' hG'
    rw [(transPi_eq_of_ne nF).2, (transPi_eq_of_ne nG).2, hexDist_sub]
    omega
  brick := by
    intro F hF
    change faceDepth (h' + 2 * k) F ≤ faceDepth h' (transPi h' i j F) + ((2 * k : ℕ) : ℤ)
    obtain ⟨hi0, hi4, hj0, hj2', _⟩ := hv
    rw [faceDepth_of_isBrick hF]
    obtain ⟨X, Y⟩ := F
    unfold IsBrick at hF
    simp only at hF
    push_cast at hF ⊢
    unfold transPi
    split_ifs with hb
    · rw [faceDepth_of_isBrick hb]
      unfold outDepth
      simp only
      apply min4_le_min4_add <;> omega
    · simp only [faceDepth, if_true, zero_add]
      unfold outDepth
      unfold IsBrick at hb
      simp only at hb ⊢
      have hc : Y < j ∨ j + h' ≤ Y ∨ X ≤ i ∨ 2 * (h' : ℤ) + i + 1 ≤ X := by omega
      rcases hc with hc | hc | hc | hc
      · exact (min_le_left _ _).trans ((min_le_left _ _).trans (by omega))
      · exact (min_le_left _ _).trans ((min_le_right _ _).trans (by omega))
      · exact (min_le_right _ _).trans ((min_le_left _ _).trans (by omega))
      · exact (min_le_right _ _).trans ((min_le_right _ _).trans (by omega))
  del := by
    intro m hm hown
    change transOwn h' i j m = none at hown
    rw [mem_fig1WallCells_iff (by omega) (even_add_two_mul he' k)] at hm
    have hnc : ¬ IsWallCell h' (m.1 - 2 * i, m.2 - 2 * j) := by
      intro h1; unfold transOwn at hown; rw [if_pos h1] at hown; simp at hown
    suffices H : ∃ q ∈ squaresAbove m, faceDepth (h' + 2 * k) (wallFace (h' + 2 * k) q) ≤
        2 * (k : ℤ) - 1 by
      obtain ⟨q, hq, hle⟩ := H
      refine ⟨q, hq, ?_⟩
      have := faceDepth_nonneg ((transShapeK' h' k hh' he' hv).π_face _
        (isBrick_or_eq_outFace_wallFace (h' + 2 * k) q))
      push_cast
      omega
    obtain ⟨a, b⟩ := m
    obtain ⟨_, _, _, _, hpar⟩ := hv
    unfold IsWallCell at hm hnc
    simp only at hm hnc
    push_cast at hm hnc
    have hcase : b ≤ 2 * j ∨ 2 * j + 2 * (h' : ℤ) ≤ b ∨ a ≤ 2 * i - 1 ∨
        4 * (h' : ℤ) + 3 + 2 * i ≤ a := by
      omega
    have hodd : b % 2 = 1 → a % 2 = 0 ∧ (a / 2 + (b - 1) / 2) % 2 = 1 := by omega
    clear hm hnc hown
    rcases hcase with hc | hc | hc | hc
    · refine ⟨(a + 1 - a % 2, b - 1 + b % 2), by sq_tac, faceDepth_wallFace_le (by omega) ?_⟩
      simp only [brickOf]; omega
    · refine ⟨(a + 1 - a % 2, b + 1 - b % 2), by sq_tac, faceDepth_wallFace_le (by omega) ?_⟩
      simp only [brickOf]; push_cast; omega
    · rcases Int.emod_two_eq_zero_or_one b with hb | hb
      · rcases Int.emod_two_eq_zero_or_one ((a - 2 + a % 2) / 2 + b / 2) with hp | hp
        · refine ⟨(a - 1 + a % 2, b + 1), by sq_tac, faceDepth_wallFace_le (by omega) ?_⟩
          simp only [brickOf]; omega
        · refine ⟨(a - 1 + a % 2, b - 1), by sq_tac, faceDepth_wallFace_le (by omega) ?_⟩
          simp only [brickOf]; omega
      · refine ⟨(a - 1 + a % 2, b), by sq_tac, faceDepth_wallFace_le (by omega) ?_⟩
        simp only [brickOf]; omega
    · rcases Int.emod_two_eq_zero_or_one b with hb | hb
      · rcases Int.emod_two_eq_zero_or_one ((a - a % 2) / 2 + b / 2) with hp | hp
        · refine ⟨(a + 1 - a % 2, b - 1), by sq_tac, faceDepth_wallFace_le (by omega) ?_⟩
          simp only [brickOf]; push_cast; omega
        · refine ⟨(a + 1 - a % 2, b + 1), by sq_tac, faceDepth_wallFace_le (by omega) ?_⟩
          simp only [brickOf]; push_cast; omega
      · refine ⟨(a + 1 - a % 2, b), by sq_tac, faceDepth_wallFace_le (by omega) ?_⟩
        simp only [brickOf]; push_cast; omega

/-! ## The realization -/

/-- **The moved subwall as a realization.** The vertex `p` goes to `p + (i, j)`, and each edge
to the edge between the moved ends. -/
def transRealizationK (h' k : ℕ) (hh' : 1 ≤ h') (he' : Even h') {i j : ℕ}
    (hv : TransVecK k i j) : (transShapeK' h' k hh' he' hv).Realization where
  vmap p := (p.1 + i, p.2 + j)
  inner _ _ := []
  vmap_mem p hp := by
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have h3' : ¬ (p.1 = 0 ∧ p.2 = 0) := fun e => h3 (Prod.ext e.1 e.2)
    have h4' : ¬ (p.1 = 2 * h' + 1 ∧ p.2 = h') := fun e => h4 (Prod.ext e.1 e.2)
    obtain ⟨_, _, _, _, _⟩ := hv
    refine ⟨by simp only; omega, by simp only; omega, ?_, ?_⟩ <;>
      intro e <;> simp only [Prod.mk.injEq] at e <;> omega
  inner_symm _ _ _ := rfl
  chain p q hpq := by
    obtain ⟨⟨hp1, hp2, hp3, hp4⟩, ⟨hq1, hq2, hq3, hq4⟩, hadj⟩ := hpq
    have hp3' : ¬ (p.1 = 0 ∧ p.2 = 0) := fun e => hp3 (Prod.ext e.1 e.2)
    have hp4' : ¬ (p.1 = 2 * h' + 1 ∧ p.2 = h') := fun e => hp4 (Prod.ext e.1 e.2)
    have hq3' : ¬ (q.1 = 0 ∧ q.2 = 0) := fun e => hq3 (Prod.ext e.1 e.2)
    have hq4' : ¬ (q.1 = 2 * h' + 1 ∧ q.2 = h') := fun e => hq4 (Prod.ext e.1 e.2)
    obtain ⟨_, _, _, _, _⟩ := hv
    simp only [List.nil_append, List.isChain_cons_cons, List.isChain_singleton, and_true]
    refine ⟨⟨by simp only; omega, by simp only; omega, ?_, ?_⟩,
      ⟨by simp only; omega, by simp only; omega, ?_, ?_⟩, ?_⟩
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · intro e; simp only [Prod.mk.injEq] at e; omega
    · simp only [Nat.odd_iff] at hadj ⊢
      omega
  nodup p q hpq := by
    obtain ⟨-, -, hadj⟩ := hpq
    simp only [List.nil_append, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true, Prod.mk.injEq]
    omega
  own_vmap p hp := by
    change transOwn h' i j _ = _
    unfold transOwn
    have e : ((vCell (p.1 + i, p.2 + j)).1 - 2 * (i : ℤ), (vCell (p.1 + i, p.2 + j)).2 - 2 * j) =
        vCell p := by
      simp only [vCell, Prod.mk.injEq]; push_cast; constructor <;> ring
    rw [e]
    simp only [isWallCell_vCell hp, ↓reduceIte]
  own_inner _ _ _ u hu := absurd hu (List.not_mem_nil)
  own_step p q hpq uw huw := by
    simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at huw
    subst huw
    change transOwn h' i j _ = _
    unfold transOwn
    have e : ((eCell (p.1 + i, p.2 + j) (q.1 + i, q.2 + j)).1 - 2 * (i : ℤ),
        (eCell (p.1 + i, p.2 + j) (q.1 + i, q.2 + j)).2 - 2 * j) = eCell p q := by
      simp only [eCell, Prod.mk.injEq]; push_cast; constructor <;> ring
    rw [e]
    simp only [isWallCell_eCell he' hpq, ↓reduceIte]
  own_cover m hm hown := by
    obtain ⟨a, b⟩ := m
    change transOwn h' i j (a, b) ≠ none at hown
    unfold transOwn at hown
    split_ifs at hown with hc
    · rcases isWallCell_cases he' hc with ⟨p, hp, e⟩ | ⟨p, q, hpq, e⟩
      · left
        refine ⟨p, hp, ?_⟩
        simp only [vCell, Prod.mk.injEq] at e ⊢
        push_cast
        omega
      · right
        refine ⟨p, q, hpq, Or.inr ⟨((p.1 + i, p.2 + j), (q.1 + i, q.2 + j)), by simp, ?_⟩⟩
        simp only [eCell, Prod.mk.injEq] at e ⊢
        push_cast
        omega
    · exact absurd rfl hown

/-! ## The step -/

/-- **The moved subwall as a step of a chain**, for `1 ≤ i ≤ 4k - 1` and `1 ≤ j ≤ 2k - 1`. -/
def transStepK (h' k : ℕ) (hh' : 1 ≤ h') (he' : Even h') {i j : ℕ} (hv : TransVecK k i j)
    (hi1 : 1 ≤ i) (hi2 : i + 1 ≤ 4 * k) (hj1 : 1 ≤ j) (hj2 : j + 1 ≤ 2 * k) :
    Step (h' + 2 * k) h' (2 * (2 * k)) where
  τ := transShapeK' h' k hh' he' hv
  R := transRealizationK h' k hh' he' hv
  ki := (transShapeK_depthTestK h' k hh' he' hv (by exact_mod_cast hi1) (by exact_mod_cast hi2)
    (by exact_mod_cast hj1) (by exact_mod_cast hj2)).ki
  two_le := by omega
  pos := hh'
  even := he'
  rayOK := Shape.Realization.rayOK_of_trans _ (by omega) (even_add_two_mul he' k) hh' he'
    (fun _ => rfl) (fun _ => rfl)
  rowMono := Shape.Realization.rowMono_of_trans _ (fun _ => rfl)

end GraphMinor.GM13
