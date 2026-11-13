module

public import GraphMinor.GM13.Section7KI

/-!
# Graph Minors XIII, (7.3): turning a shape by 180 degrees

A shape that deletes elements near the bottom of the wall can be used near the top after a turn
by 180 degrees. This file defines the turn of a shape (`Shape.rotate`) and shows that it keeps
the depth test (`Shape.DepthTest.rotate`).

The turn of the wall of Fig. 1 of height `h` (with `h` even) sends the cell `(a, b)` to
`(4h + 2 - a, 2h - b)` (`rotC`), the brick `(X, Y)` to `(2h + 1 - X, h - 1 - Y)`, and the outer
face to itself (`rotF`). It maps the wall onto itself (`isWallCell_rotC`), and the face of a
turned square is the turned face (`wallFace_rotC`). Depths and hex distances do not change. The
turned shape keeps the element `m` exactly when the shape keeps the turned element, and then it
goes to the turned new element.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-- The turn by 180 degrees of the cells of the wall of Fig. 1 of height `h`. -/
def rotC (h : ℕ) (c : ℤ × ℤ) : ℤ × ℤ := (4 * h + 2 - c.1, 2 * h - c.2)

/-- The turn by 180 degrees of the faces of the wall of Fig. 1 of height `h`. -/
def rotF (h : ℕ) (F : ℤ × ℤ) : ℤ × ℤ :=
  if F = outFace then outFace else (2 * h + 1 - F.1, h - 1 - F.2)

theorem rotC_rotC (h : ℕ) (c : ℤ × ℤ) : rotC h (rotC h c) = c := by
  unfold rotC
  ext <;> simp

theorem rotC_injective (h : ℕ) : Function.Injective (rotC h) := fun c d e => by
  rw [← rotC_rotC h c, e, rotC_rotC]

theorem isWallCell_rotC {h : ℕ} (he : Even h) {c : ℤ × ℤ} :
    IsWallCell h (rotC h c) ↔ IsWallCell h c := by
  obtain ⟨k, hk⟩ := he
  obtain ⟨a, b⟩ := c
  unfold IsWallCell rotC
  simp only
  subst hk
  push_cast
  omega

theorem mem_fig1WallCells_rotC {h : ℕ} (hh : 1 ≤ h) (he : Even h) {c : ℤ × ℤ} :
    rotC h c ∈ fig1WallCells h ↔ c ∈ fig1WallCells h := by
  rw [mem_fig1WallCells_iff hh he, mem_fig1WallCells_iff hh he, isWallCell_rotC he]

theorem mem_squaresAbove_rotC {h : ℕ} {c q : ℤ × ℤ} :
    rotC h q ∈ squaresAbove (rotC h c) ↔ q ∈ squaresAbove c := by
  rw [mem_squaresAbove_iff, mem_squaresAbove_iff]
  unfold rotC
  simp only
  omega

theorem squaresAbove_rotC {h : ℕ} (c : ℤ × ℤ) :
    squaresAbove (rotC h c) = rotC h '' squaresAbove c := by
  ext q
  constructor
  · intro hq
    refine ⟨rotC h q, ?_, rotC_rotC h q⟩
    rw [← mem_squaresAbove_rotC (h := h), rotC_rotC]
    exact hq
  · rintro ⟨q, hq, rfl⟩
    exact mem_squaresAbove_rotC.mpr hq

theorem rotF_outFace (h : ℕ) : rotF h outFace = outFace := by
  simp [rotF]

theorem isBrick_rotF {h : ℕ} (he : Even h) {F : ℤ × ℤ} (hF : IsBrick h F) :
    IsBrick h (rotF h F) := by
  have hne : F ≠ outFace := fun e => not_isBrick_outFace h (e ▸ hF)
  obtain ⟨k, hk⟩ := he
  unfold rotF
  rw [if_neg hne]
  unfold IsBrick at hF ⊢
  simp only
  subst hk
  push_cast at hF ⊢
  omega

theorem rotF_brick {h : ℕ} {F : ℤ × ℤ} (hF : IsBrick h F) :
    rotF h F = (2 * h + 1 - F.1, h - 1 - F.2) := by
  have hne : F ≠ outFace := fun e => not_isBrick_outFace h (e ▸ hF)
  unfold rotF
  rw [if_neg hne]

theorem rotF_rotF {h : ℕ} (he : Even h) {F : ℤ × ℤ} (hF : IsWallFace h F) :
    rotF h (rotF h F) = F := by
  rcases hF with hb | rfl
  · rw [rotF_brick (isBrick_rotF he hb), rotF_brick hb]
    ext <;> simp
  · rw [rotF_outFace, rotF_outFace]

theorem isWallFace_rotF {h : ℕ} (he : Even h) {F : ℤ × ℤ} (hF : IsWallFace h F) :
    IsWallFace h (rotF h F) := by
  rcases hF with hb | rfl
  · exact Or.inl (isBrick_rotF he hb)
  · exact Or.inr (rotF_outFace h)

theorem rotF_injOn {h : ℕ} (he : Even h) {F G : ℤ × ℤ} (hF : IsWallFace h F)
    (hG : IsWallFace h G) (e : rotF h F = rotF h G) : F = G := by
  rw [← rotF_rotF he hF, e, rotF_rotF he hG]

/-- **The face of a turned square is the turned face.** -/
theorem wallFace_rotC {h : ℕ} (he : Even h) {q : ℤ × ℤ} (hq : q.1 % 2 = 1 ∧ q.2 % 2 = 1) :
    wallFace h (rotC h q) = rotF h (wallFace h q) := by
  obtain ⟨k, hk⟩ := he
  obtain ⟨a, b⟩ := q
  obtain ⟨x, rfl⟩ : ∃ x, a = 2 * x + 1 := ⟨a / 2, by simp only at hq; omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = 2 * y + 1 := ⟨b / 2, by simp only at hq; omega⟩
  have e : rotC h (2 * x + 1, 2 * y + 1) = (2 * (2 * h - x) + 1, 2 * (h - 1 - y) + 1) := by
    unfold rotC; ext <;> simp only <;> ring
  rw [e, wallFace_square, wallFace_square]
  clear e hq
  subst hk
  unfold rotF outFace
  push_cast
  split_ifs <;> simp only [Prod.mk.injEq, and_true, not_true_eq_false] at * <;> omega

theorem cellFaces_rotC {h : ℕ} (he : Even h) (m : ℤ × ℤ) :
    cellFaces h (rotC h m) = rotF h '' cellFaces h m := by
  unfold cellFaces
  rw [squaresAbove_rotC, image_image, image_image]
  apply image_congr
  intro q hq
  have hsq := (mem_squaresAbove_iff.mp hq)
  exact wallFace_rotC he ⟨hsq.1, hsq.2.1⟩

theorem faceDepth_eq_outDepth {h : ℕ} {F : ℤ × ℤ} (hF : IsBrick h F) :
    faceDepth h F = outDepth h F := by
  have hne : F ≠ outFace := fun e => not_isBrick_outFace h (e ▸ hF)
  unfold faceDepth
  rw [if_neg hne]

theorem outDepth_rotF {h : ℕ} {F : ℤ × ℤ} (hF : IsBrick h F) :
    outDepth h (rotF h F) = outDepth h F := by
  rw [rotF_brick hF]
  unfold outDepth
  simp only
  omega

theorem faceDepth_rotF {h : ℕ} (he : Even h) {F : ℤ × ℤ} (hF : IsWallFace h F) :
    faceDepth h (rotF h F) = faceDepth h F := by
  rcases hF with hb | rfl
  · have hb' := isBrick_rotF he hb
    rw [faceDepth_eq_outDepth hb', faceDepth_eq_outDepth hb, outDepth_rotF hb]
  · rw [rotF_outFace]

theorem hexDist_rotF {h : ℕ} {F G : ℤ × ℤ} (hF : IsBrick h F) (hG : IsBrick h G) :
    hexDist (rotF h F) (rotF h G) = hexDist F G := by
  rw [rotF_brick hF, rotF_brick hG]
  unfold hexDist
  simp only
  omega

namespace Shape

variable {h h' : ℕ} (τ : Shape h h')

/-- **The turn of a shape by 180 degrees.** It keeps `m` when `τ` keeps the turned element, and
sends each face through the turned shape. -/
def rotate (hh : 1 ≤ h) (he : Even h) (hh' : 1 ≤ h') (he' : Even h') : Shape h h' where
  own m := (τ.own (rotC h m)).map (rotC h')
  π F := rotF h' (τ.π (rotF h F))
  own_mem m hm m' hown := by
    obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp hown
    exact (mem_fig1WallCells_rotC hh' he').mpr
      (τ.own_mem _ ((mem_fig1WallCells_rotC hh he).mpr hm) n hn)
  own_surj m' hm' := by
    obtain ⟨m, hm, hown⟩ := τ.own_surj (rotC h' m') ((mem_fig1WallCells_rotC hh' he').mpr hm')
    refine ⟨rotC h m, (mem_fig1WallCells_rotC hh he).mpr hm, ?_⟩
    rw [rotC_rotC, hown, Option.map_some, rotC_rotC]
  π_face F hF := isWallFace_rotF he' (τ.π_face _ (isWallFace_rotF he hF))
  π_surj F' hF' := by
    obtain ⟨F, hF, e⟩ := τ.π_surj (rotF h' F') (isWallFace_rotF he' hF')
    refine ⟨rotF h F, isWallFace_rotF he hF, ?_⟩
    show rotF h' (τ.π (rotF h (rotF h F))) = F'
    rw [rotF_rotF he hF, e, rotF_rotF he' hF']
  del m hm hown F hF G hG := by
    simp only [Option.map_eq_none_iff] at hown
    have hm' := (mem_fig1WallCells_rotC hh he).mpr hm
    have hF' : rotF h F ∈ cellFaces h (rotC h m) := by
      rw [cellFaces_rotC he]; exact mem_image_of_mem _ hF
    have hG' : rotF h G ∈ cellFaces h (rotC h m) := by
      rw [cellFaces_rotC he]; exact mem_image_of_mem _ hG
    show rotF h' (τ.π (rotF h F)) = rotF h' (τ.π (rotF h G))
    rw [τ.del _ hm' hown _ hF' _ hG']
  keep m hm m'' hown := by
    obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.mp hown
    have hk := τ.keep _ ((mem_fig1WallCells_rotC hh he).mpr hm) m' hm'
    rw [cellFaces_rotC he] at hk
    rw [cellFaces_rotC he', ← hk, image_image, image_image]
  conn F G hF hG e := by
    change rotF h' (τ.π (rotF h F)) = rotF h' (τ.π (rotF h G)) at e
    have e' := rotF_injOn he' (τ.π_face _ (isWallFace_rotF he hF))
      (τ.π_face _ (isWallFace_rotF he hG)) e
    have hr := τ.conn _ _ (isWallFace_rotF he hF) (isWallFace_rotF he hG) e'
    rw [← rotF_rotF he hF, ← rotF_rotF he hG]
    refine Relation.ReflTransGen.lift (rotF h) ?_ _ _ hr
    rintro A B ⟨m, hm, hown, hA, hB⟩
    refine ⟨rotC h m, (mem_fig1WallCells_rotC hh he).mpr hm, ?_, ?_, ?_⟩
    · simp only [rotC_rotC, hown, Option.map_none]
    · rw [cellFaces_rotC he]; exact mem_image_of_mem _ hA
    · rw [cellFaces_rotC he]; exact mem_image_of_mem _ hB

variable {τ}

/-- **The turn keeps the depth test.** -/
theorem DepthTest.rotate (hT : τ.DepthTest) (hh : 1 ≤ h) (he : Even h) (hh' : 1 ≤ h')
    (he' : Even h') : (τ.rotate hh he hh' he').DepthTest where
  out := by
    change rotF h' (τ.π (rotF h outFace)) = outFace
    rw [rotF_outFace, hT.out, rotF_outFace]
  hex F G hF hG hF' hG' := by
    change IsBrick h' (rotF h' (τ.π (rotF h F))) at hF'
    change IsBrick h' (rotF h' (τ.π (rotF h G))) at hG'
    change hexDist F G ≤ hexDist (rotF h' (τ.π (rotF h F))) (rotF h' (τ.π (rotF h G))) + 2
    have b1 : IsBrick h' (τ.π (rotF h F)) := by
      rcases τ.π_face _ (isWallFace_rotF he (Or.inl hF)) with hb | ho
      · exact hb
      · rw [ho, rotF_outFace] at hF'; exact absurd hF' (not_isBrick_outFace h')
    have b2 : IsBrick h' (τ.π (rotF h G)) := by
      rcases τ.π_face _ (isWallFace_rotF he (Or.inl hG)) with hb | ho
      · exact hb
      · rw [ho, rotF_outFace] at hG'; exact absurd hG' (not_isBrick_outFace h')
    rw [hexDist_rotF b1 b2, ← hexDist_rotF hF hG]
    exact hT.hex _ _ (isBrick_rotF he hF) (isBrick_rotF he hG) b1 b2
  brick F hF := by
    change faceDepth h F ≤ faceDepth h' (rotF h' (τ.π (rotF h F))) + 2
    rw [faceDepth_rotF he' (τ.π_face _ (isWallFace_rotF he (Or.inl hF))),
      ← faceDepth_rotF he (Or.inl hF)]
    exact hT.brick _ (isBrick_rotF he hF)
  del m hm hown := by
    change (τ.own (rotC h m)).map (rotC h') = none at hown
    simp only [Option.map_eq_none_iff] at hown
    obtain ⟨q, hq, hle⟩ := hT.del _ ((mem_fig1WallCells_rotC hh he).mpr hm) hown
    have hsq := mem_squaresAbove_iff.mp hq
    refine ⟨rotC h q, ?_, ?_⟩
    · rw [← mem_squaresAbove_rotC (h := h), rotC_rotC]; exact hq
    · have hsq' : (rotC h q).1 % 2 = 1 ∧ (rotC h q).2 % 2 = 1 := by
        unfold rotC; simp only; omega
      change faceDepth h (wallFace h (rotC h q)) ≤
        faceDepth h' (rotF h' (τ.π (rotF h (wallFace h (rotC h q))))) + 1
      have hw := isBrick_or_eq_outFace_wallFace h q
      have hw' : IsWallFace h (wallFace h q) := hw
      rw [wallFace_rotC he ⟨hsq.1, hsq.2.1⟩, rotF_rotF he hw', faceDepth_rotF he hw',
        faceDepth_rotF he' (τ.π_face _ hw')]
      exact hle

end Shape

end GraphMinor.GM13
