module

public import GraphMinor.GM13.Section7KI

/-!
# Graph Minors XIII, (7.3): subwalls moved inside the wall

The simplest wall of height `h` inside a wall of height `h + 2` is a copy of it moved by a vector
`(i, j)`: the vertex `(x, y)` of the small wall is the vertex `(x + i, y + j)` of the large one.
This file builds the shape of that subwall (`transShape`) for `0 ≤ i ≤ 4`, `0 ≤ j ≤ 2` and
`i + j` even. It shows that for the vectors `(1, 1)` and `(3, 1)` the shape passes the depth test
of `Section7KI.lean`, so it has the property `KI 4`.

The key fact is that moving a square moves its face: `transPi (wallFace q)` is the face of the
small wall at the moved square (`transPi_wallFace`). So a kept element keeps its faces, and a
deleted element lies outside the small wall, where all squares around it have one face.

The file also has tools used for all shapes: a test for the existence of a square around a cell
by its four corners (`exists_mem_squaresAbove_of_or`) and steps across deleted elements.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-! ## Tools -/

/-- The four squares around a cell `(a, b)`, by their coordinates. -/
theorem corner_mem_squaresAbove {a b : ℤ} {e f : ℤ} (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1) :
    (a + (1 - a % 2) * e, b + (1 - b % 2) * f) ∈ squaresAbove (a, b) := by
  rw [mem_squaresAbove_iff]
  simp only
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
  rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
  rcases Int.emod_two_eq_zero_or_one b with hb | hb <;> simp only [ha, hb] <;> omega

/-- To find a square around `(a, b)` with a property, it is enough to test the four corners. -/
theorem exists_mem_squaresAbove_of_or {a b : ℤ} {P : ℤ × ℤ → Prop}
    (h : P (a + (1 - a % 2), b + (1 - b % 2)) ∨ P (a + (1 - a % 2), b - (1 - b % 2)) ∨
      P (a - (1 - a % 2), b + (1 - b % 2)) ∨ P (a - (1 - a % 2), b - (1 - b % 2))) :
    ∃ q ∈ squaresAbove (a, b), P q := by
  rcases h with h | h | h | h
  · exact ⟨_, by simpa using corner_mem_squaresAbove (a := a) (b := b) (Or.inl rfl) (Or.inl rfl), h⟩
  · exact ⟨_, by simpa [sub_eq_add_neg] using
      corner_mem_squaresAbove (a := a) (b := b) (Or.inl rfl) (Or.inr rfl), h⟩
  · exact ⟨_, by simpa [sub_eq_add_neg] using
      corner_mem_squaresAbove (a := a) (b := b) (Or.inr rfl) (Or.inl rfl), h⟩
  · exact ⟨_, by simpa [sub_eq_add_neg] using
      corner_mem_squaresAbove (a := a) (b := b) (Or.inr rfl) (Or.inr rfl), h⟩

/-- A step across a deleted element, from explicit squares. -/
theorem delStep_of {h : ℕ} {own : ℤ × ℤ → Option (ℤ × ℤ)} {m q q' F G : ℤ × ℤ}
    (hm : m ∈ fig1WallCells h) (hown : own m = none) (hq : q ∈ squaresAbove m)
    (hq' : q' ∈ squaresAbove m) (hF : wallFace h q = F) (hG : wallFace h q' = G) :
    DelStep (h := h) own F G :=
  ⟨m, hm, hown, ⟨q, hq, hF⟩, ⟨q', hq', hG⟩⟩

theorem delStep_symm {h : ℕ} {own : ℤ × ℤ → Option (ℤ × ℤ)} {F G : ℤ × ℤ}
    (hs : DelStep (h := h) own F G) : DelStep (h := h) own G F := by
  obtain ⟨m, hm, ho, hF, hG⟩ := hs
  exact ⟨m, hm, ho, hG, hF⟩

theorem reflTransGen_delStep_symm {h : ℕ} {own : ℤ × ℤ → Option (ℤ × ℤ)} {F G : ℤ × ℤ}
    (hs : Relation.ReflTransGen (DelStep (h := h) own) F G) :
    Relation.ReflTransGen (DelStep (h := h) own) G F := by
  induction hs with
  | refl => exact .refl
  | tail _ hst ih => exact Relation.ReflTransGen.head (delStep_symm hst) ih

/-! ## The moved subwall -/

/-- The face of the small wall (height `h'`, moved by `(i, j)`) that contains the face `F` of the
large wall. -/
def transPi (h' : ℕ) (i j : ℤ) (F : ℤ × ℤ) : ℤ × ℤ :=
  if IsBrick h' (F.1 - i, F.2 - j) then (F.1 - i, F.2 - j) else outFace

/-- The element of the small wall that contains the element `m` of the large wall. -/
def transOwn (h' : ℕ) (i j : ℤ) (m : ℤ × ℤ) : Option (ℤ × ℤ) :=
  if IsWallCell h' (m.1 - 2 * i, m.2 - 2 * j) then some (m.1 - 2 * i, m.2 - 2 * j) else none

theorem brickOf_sub {i j : ℤ} (hij : (i + j) % 2 = 0) (q : ℤ × ℤ) :
    brickOf (q.1 - 2 * i, q.2 - 2 * j) = ((brickOf q).1 - i, (brickOf q).2 - j) := by
  unfold brickOf
  ext <;> simp only <;> omega

/-- The vector `(i, j)` keeps the small wall inside the large one. -/
structure TransVec (i j : ℤ) : Prop where
  i0 : 0 ≤ i
  i4 : i ≤ 4
  j0 : 0 ≤ j
  j2 : j ≤ 2
  par : (i + j) % 2 = 0

theorem TransVec.isBrick {i j : ℤ} (hv : TransVec i j) {h' : ℕ} {F : ℤ × ℤ}
    (hF : IsBrick h' (F.1 - i, F.2 - j)) : IsBrick (h' + 2) F := by
  obtain ⟨_, _, _, _, _⟩ := hv
  unfold IsBrick at *
  push_cast
  omega

theorem TransVec.transPi_outFace {i j : ℤ} (hv : TransVec i j) (h' : ℕ) :
    transPi h' i j outFace = outFace := by
  have := hv.j0
  unfold transPi
  rw [ite_eq_right_iff.mpr (fun h => absurd h ?_)]
  unfold IsBrick outFace
  omega

/-- **Moving a square moves its face.** -/
theorem TransVec.transPi_wallFace {i j : ℤ} (hv : TransVec i j) (h' : ℕ) (q : ℤ × ℤ) :
    transPi h' i j (wallFace (h' + 2) q) = wallFace h' (q.1 - 2 * i, q.2 - 2 * j) := by
  unfold wallFace
  rw [brickOf_sub hv.par]
  split_ifs with h1 h2 h2
  · unfold transPi; rw [if_pos h2]
  · unfold transPi; rw [if_neg h2]
  · exact absurd (hv.isBrick h2) h1
  · exact hv.transPi_outFace h'

theorem mem_squaresAbove_sub {c q : ℤ × ℤ} (i j : ℤ) :
    (q.1 - 2 * i, q.2 - 2 * j) ∈ squaresAbove (c.1 - 2 * i, c.2 - 2 * j) ↔ q ∈ squaresAbove c := by
  simp only [mem_squaresAbove_iff]
  omega

theorem TransVec.image_cellFaces {i j : ℤ} (hv : TransVec i j) (h' : ℕ) (m : ℤ × ℤ) :
    transPi h' i j '' cellFaces (h' + 2) m = cellFaces h' (m.1 - 2 * i, m.2 - 2 * j) := by
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

theorem transPi_eq_of_ne {h' : ℕ} {i j : ℤ} {F : ℤ × ℤ} (hF : transPi h' i j F ≠ outFace) :
    IsBrick h' (F.1 - i, F.2 - j) ∧ transPi h' i j F = (F.1 - i, F.2 - j) := by
  unfold transPi at *
  split_ifs at * with h1
  · exact ⟨h1, rfl⟩
  · exact absurd rfl hF

/-- **The moved subwall as a shape.** The steps from the faces outside the small wall to the
outer face are an argument, given for each vector. -/
def transShape (h' : ℕ) (hh' : 1 ≤ h') (he' : Even h') {i j : ℤ} (hv : TransVec i j)
    (hconn : ∀ F, IsWallFace (h' + 2) F → transPi h' i j F = outFace →
      Relation.ReflTransGen (DelStep (h := h' + 2) (transOwn h' i j)) F outFace) :
    Shape (h' + 2) h' where
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
    · rw [mem_fig1WallCells_iff (by omega) (by obtain ⟨k, hk⟩ := he'; exact ⟨k + 1, by omega⟩)]
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

/-! ## The vectors `(1, 1)` and `(3, 1)` -/

/-- One step to a face from the cell `(a, b)`, for the moved subwall. -/
theorem trans_delStep {h' : ℕ} (hh' : 1 ≤ h') (he' : Even h') {i j a b : ℤ} {q q' F G : ℤ × ℤ}
    (hcell : IsWallCell (h' + 2) (a, b)) (hdel : ¬ IsWallCell h' (a - 2 * i, b - 2 * j))
    (hq : q ∈ squaresAbove (a, b)) (hq' : q' ∈ squaresAbove (a, b))
    (hF : wallFace (h' + 2) q = F) (hG : wallFace (h' + 2) q' = G) :
    DelStep (h := h' + 2) (transOwn h' i j) F G := by
  refine delStep_of ((mem_fig1WallCells_iff (by omega)
    (by obtain ⟨k, hk⟩ := he'; exact ⟨k + 1, by omega⟩) _).mpr hcell) ?_ hq hq' hF hG
  unfold transOwn
  rw [if_neg hdel]

theorem wallFace_eq_brick {h : ℕ} {q F : ℤ × ℤ} (hq : brickOf q = F) (hF : IsBrick h F) :
    wallFace h q = F := by
  subst hq
  unfold wallFace
  rw [if_pos hF]

theorem wallFace_eq_out {h : ℕ} {q : ℤ × ℤ} (hq : ¬ IsBrick h (brickOf q)) :
    wallFace h q = outFace := by
  unfold wallFace
  rw [if_neg hq]

/-- Remove `True` and `False` from a goal and its hypotheses, then call `omega`. -/
macro "lin_tac" : tactic => `(tactic| ((try simp only [true_and, and_true, not_true_eq_false, false_and, and_false, or_false, false_or, not_false_eq_true, true_or, or_true, not_and, true_iff, iff_true, imp_false, true_implies, implies_true] at *) <;> first | done | trivial | omega))

/-- A tactic for squares above a cell. -/
macro "sq_tac" : tactic => `(tactic| (rw [mem_squaresAbove_iff]; (try simp only); lin_tac))

/-- A tactic for the faces of squares. -/
macro "wf_tac" : tactic => `(tactic| first | exact wallFace_eq_out (by simp only [brickOf, IsBrick]; (try push_cast); lin_tac) | exact wallFace_eq_brick (by simp only [brickOf, Prod.mk.injEq]; lin_tac) (by simp only [IsBrick]; (try push_cast); lin_tac))

/-- A tactic for the cells of a wall. -/
macro "wc_tac" : tactic => `(tactic| (simp only [IsWallCell]; (try push_cast); lin_tac))

/-- A single step across the cell `(a, b)`, with the squares named by coordinates. -/
theorem trans_step {h' : ℕ} (hh' : 1 ≤ h') (he' : Even h') {i j : ℤ} (G H : ℤ × ℤ)
    (a b c d c' d' : ℤ) (h1 : IsWallCell (h' + 2) (a, b)) (h2 : ¬ IsWallCell h' (a - 2 * i, b - 2 * j))
    (h3 : (c, d) ∈ squaresAbove (a, b)) (h4 : (c', d') ∈ squaresAbove (a, b))
    (h5 : wallFace (h' + 2) (c, d) = G) (h6 : wallFace (h' + 2) (c', d') = H) :
    Relation.ReflTransGen (DelStep (h := h' + 2) (transOwn h' i j)) G H :=
  .single (trans_delStep hh' he' h1 h2 h3 h4 h5 h6)

/-- The steps out for the vector `(i, j)` with `j = 1` and `i ∈ {1, 3}`. -/
theorem trans_conn {h' : ℕ} (hh' : 1 ≤ h') (he' : Even h') {i : ℤ} (hi : i = 1 ∨ i = 3)
    (F : ℤ × ℤ) (hF : IsWallFace (h' + 2) F) (hπ : transPi h' i 1 F = outFace) :
    Relation.ReflTransGen (DelStep (h := h' + 2) (transOwn h' i 1)) F outFace := by
  obtain ⟨k, hk⟩ := he'
  rcases hF with hF | rfl
  swap
  · exact .refl
  obtain ⟨X, Y⟩ := F
  have hnb : ¬ IsBrick h' (X - i, Y - 1) := by
    intro hb
    unfold transPi at hπ
    rw [if_pos hb] at hπ
    unfold IsBrick at hb
    simp only [outFace, Prod.mk.injEq] at hπ
    omega
  unfold IsBrick at hF hnb
  simp only at hF hnb
  have sq : ∀ {a b c d : ℤ}, c % 2 = 1 → d % 2 = 1 → (a = c ∨ a = c - 1 ∨ a = c + 1) →
      (b = d ∨ b = d - 1 ∨ b = d + 1) → (c, d) ∈ squaresAbove (a, b) := by
    intro a b c d h1 h2 h3 h4
    rw [mem_squaresAbove_iff]
    exact ⟨h1, h2, h3, h4⟩
  have hY : Y = 0 ∨ Y = h' + 1 ∨ X ≤ i ∨ 2 * (h' : ℤ) + i + 1 ≤ X := by omega
  obtain ⟨t, ht⟩ : ∃ t, X = Y + 2 * t := ⟨(X - Y) / 2, by omega⟩
  have hF' : 0 ≤ Y ∧ Y < h' + 2 ∧ 1 ≤ X ∧ X ≤ 2 * h' + 4 := by push_cast at hF; omega
  have he' : Even h' := ⟨k, hk⟩
  clear hnb hπ sq hF
  rcases hY with hY | hY | hX | hX
  · exact trans_step hh' he' _ _ (2 * X - 1) 0 (2 * X - 1) 1 (2 * X - 1) (-1) (by wc_tac) (by wc_tac)
      (by sq_tac) (by sq_tac) (by wf_tac) (by wf_tac)
  · exact trans_step hh' he' _ _ (2 * X - 1) (2 * h' + 4) (2 * X - 1) (2 * h' + 3) (2 * X - 1) (2 * h' + 5)
      (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (by wf_tac) (by wf_tac)
  · have hX' : X = 1 ∨ X = 2 ∨ X = 3 := by omega
    rcases hX' with hX' | hX' | hX'
    · exact trans_step hh' he' _ _ 0 (2 * Y + 1) 1 (2 * Y + 1) (-1) (2 * Y + 1) (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (by wf_tac) (by wf_tac)
    · exact trans_step hh' he' _ _ 2 (2 * Y + 1) 3 (2 * Y + 1) 1 (2 * Y + 1) (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (by wf_tac) (by wf_tac)
    · refine (trans_step hh' he' _ (1, Y) 4 (2 * Y + 1) 5 (2 * Y + 1) 3 (2 * Y + 1) (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (by wf_tac) (by wf_tac)).trans ?_
      exact trans_step hh' he' _ _ 0 (2 * Y + 1) 1 (2 * Y + 1) (-1) (2 * Y + 1) (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (by wf_tac) (by wf_tac)
  · have hX' : X = 2 * h' + 4 ∨ X = 2 * h' + 3 ∨ X = 2 * h' + 2 := by omega
    rcases hX' with hX' | hX' | hX'
    · exact trans_step hh' he' _ _ (4 * h' + 10) (2 * Y + 1) (4 * h' + 9) (2 * Y + 1) (4 * h' + 11) (2 * Y + 1)
        (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (by wf_tac) (by wf_tac)
    · exact trans_step hh' he' _ _ (4 * h' + 8) (2 * Y + 1) (4 * h' + 7) (2 * Y + 1) (4 * h' + 9) (2 * Y + 1)
        (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (by wf_tac) (by wf_tac)
    · refine (trans_step hh' he' _ (2 * h' + 4, Y) (4 * h' + 6) (2 * Y + 1) (4 * h' + 5) (2 * Y + 1)
        (4 * h' + 7) (2 * Y + 1) (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (by wf_tac) (by wf_tac)).trans ?_
      exact trans_step hh' he' _ _ (4 * h' + 10) (2 * Y + 1) (4 * h' + 9) (2 * Y + 1) (4 * h' + 11) (2 * Y + 1)
        (by wc_tac) (by wc_tac) (by sq_tac) (by sq_tac) (by wf_tac) (by wf_tac)

/-- The subwall moved by `(i, 1)`, for `i = 1` or `i = 3`. -/
def transShape1 (h' : ℕ) (hh' : 1 ≤ h') (he' : Even h') {i : ℤ} (hi : i = 1 ∨ i = 3) :
    Shape (h' + 2) h' :=
  transShape h' hh' he' (i := i) (j := 1) ⟨by omega, by omega, by omega, by omega, by omega⟩
    (trans_conn hh' he' hi)

/-! ## The depth test for the vectors `(1, 1)` and `(3, 1)` -/

theorem faceDepth_of_isBrick {h : ℕ} {F : ℤ × ℤ} (hF : IsBrick h F) :
    faceDepth h F = outDepth h F := by
  unfold faceDepth
  rw [if_neg]
  intro e
  rw [e] at hF
  unfold IsBrick outFace at hF
  simp only at hF
  omega

/-- A square next to the border of the wall has a face of depth at most 1. -/
theorem faceDepth_wallFace_le_one {h : ℕ} {q : ℤ × ℤ}
    (H : (brickOf q).1 ≤ 2 ∨ 2 * (h : ℤ) - 1 ≤ (brickOf q).1 ∨ (brickOf q).2 ≤ 0 ∨
      (h : ℤ) - 1 ≤ (brickOf q).2) :
    faceDepth h (wallFace h q) ≤ 1 := by
  unfold wallFace
  split_ifs with hb
  · rw [faceDepth_of_isBrick hb]
    unfold outDepth
    omega
  · simp [faceDepth]

theorem hexDist_sub (F G : ℤ × ℤ) (i j : ℤ) :
    hexDist (F.1 - i, F.2 - j) (G.1 - i, G.2 - j) = hexDist F G := by
  unfold hexDist
  simp only [sub_sub_sub_cancel_right]

theorem transShape1_depthTest (h' : ℕ) (hh' : 1 ≤ h') (he' : Even h') {i : ℤ}
    (hi : i = 1 ∨ i = 3) : (transShape1 h' hh' he' hi).DepthTest where
  out := TransVec.transPi_outFace (i := i) (j := 1) ⟨by omega, by omega, by omega, by omega, by omega⟩ h'
  hex := by
    intro F G _ _ hF' hG'
    change IsBrick h' (transPi h' i 1 F) at hF'
    change IsBrick h' (transPi h' i 1 G) at hG'
    change hexDist F G ≤ hexDist (transPi h' i 1 F) (transPi h' i 1 G) + 2
    have nF : transPi h' i 1 F ≠ outFace := by
      intro e; rw [e] at hF'; unfold IsBrick outFace at hF'; simp at hF'
    have nG : transPi h' i 1 G ≠ outFace := by
      intro e; rw [e] at hG'; unfold IsBrick outFace at hG'; simp at hG'
    rw [(transPi_eq_of_ne nF).2, (transPi_eq_of_ne nG).2, hexDist_sub]
    omega
  brick := by
    intro F hF
    change faceDepth (h' + 2) F ≤ faceDepth h' (transPi h' i 1 F) + 2
    rw [faceDepth_of_isBrick hF]
    unfold transPi
    split_ifs with hb
    · rw [faceDepth_of_isBrick hb]
      unfold outDepth
      unfold IsBrick at hb hF
      push_cast at hb hF ⊢
      omega
    · simp only [faceDepth, if_true]
      unfold outDepth
      unfold IsBrick at hb hF
      push_cast at hb hF ⊢
      omega
  del := by
    intro m hm hown
    change transOwn h' i 1 m = none at hown
    rw [mem_fig1WallCells_iff (by omega) (by obtain ⟨k, hk⟩ := he'; exact ⟨k + 1, by omega⟩)]
      at hm
    have hnc : ¬ IsWallCell h' (m.1 - 2 * i, m.2 - 2 * 1) := by
      intro h1; unfold transOwn at hown; rw [if_pos h1] at hown; simp at hown
    suffices H : ∃ q ∈ squaresAbove m, faceDepth (h' + 2) (wallFace (h' + 2) q) ≤ 1 by
      obtain ⟨q, hq, hle⟩ := H
      refine ⟨q, hq, ?_⟩
      have := faceDepth_nonneg ((transShape1 h' hh' he' hi).π_face _
        (isBrick_or_eq_outFace_wallFace (h' + 2) q))
      omega
    obtain ⟨a, b⟩ := m
    obtain ⟨k, hk⟩ := he'
    unfold IsWallCell at hm hnc
    simp only at hm hnc
    push_cast at hm hnc
    have hcase : b ≤ 2 ∨ 2 * (h' : ℤ) + 2 ≤ b ∨ a ≤ 2 * i - 1 ∨ 4 * (h' : ℤ) + 3 + 2 * i ≤ a := by
      omega
    rcases hcase with hc | hc | hc | hc
    · refine ⟨(a + 1 - a % 2, 1), by sq_tac, faceDepth_wallFace_le_one ?_⟩
      simp only [brickOf]; omega
    · refine ⟨(a + 1 - a % 2, 2 * h' + 3), by sq_tac, faceDepth_wallFace_le_one ?_⟩
      simp only [brickOf]; push_cast; omega
    · refine ⟨(a - 1 + a % 2, b + (1 - b % 2) * (1 - 2 * ((b / 2) % 2))), ?_,
        faceDepth_wallFace_le_one ?_⟩
      · rw [mem_squaresAbove_iff]
        rcases Int.emod_two_eq_zero_or_one b with hb | hb <;>
        rcases Int.emod_two_eq_zero_or_one (b / 2) with hb' | hb' <;> simp only [hb, hb'] <;> omega
      · simp only [brickOf]
        rcases Int.emod_two_eq_zero_or_one b with hb | hb <;>
        rcases Int.emod_two_eq_zero_or_one (b / 2) with hb' | hb' <;> simp only [hb, hb'] <;> omega
    · refine ⟨(a + 1 - a % 2, b - (1 - b % 2) * (1 - 2 * ((b / 2) % 2))), ?_,
        faceDepth_wallFace_le_one ?_⟩
      · rw [mem_squaresAbove_iff]
        rcases Int.emod_two_eq_zero_or_one b with hb | hb <;>
        rcases Int.emod_two_eq_zero_or_one (b / 2) with hb' | hb' <;> simp only [hb, hb'] <;> omega
      · simp only [brickOf]
        push_cast
        rcases Int.emod_two_eq_zero_or_one b with hb | hb <;>
        rcases Int.emod_two_eq_zero_or_one (b / 2) with hb' | hb' <;> simp only [hb, hb'] <;> omega
end GraphMinor.GM13
