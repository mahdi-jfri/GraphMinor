module

public import GraphMinor.GM13.Section7RayHexHole
public import GraphMinor.GM13.Section7TransKFar

/-!
# Graph Minors XIII, (7.3): the hexagonal hole is far from the element of `v`

This file proves (7.3) of *Graph Minors XIII* (page 90) for an element `mv` deep inside the
wall: it gives a chain of one step that is far from `mv` in the sense of `Chain.Far`
(`exists_far_chain_deep`).

The idea is simple. A kept element is sent to an element of the new wall, and every element of
a wall has two different faces (`exists_ne_mem_cellFaces`). So a kept element has a face that is
not sent to the face of the hole. If a whole ball of radius `k - 1` of bricks around a brick
`B0` goes to one face, a kept element thus has a face outside that ball, and all its faces are at
face distance at least `k - 1` from `B0`. If every face at `mv` is at hex distance at most one
from `B0`, this gives `Chain.Far mv k` (`Shape.far_of_merge`).

For the hexagonal hole the ball of radius `b = k - 1` around its centre (`HexHole.centre`) goes
to one face (`HexHole.pi_ball`): every square of the ball goes to a square of one new brick
(`HexHole.bk_newSq_ball`). We take as centre the brick of the square at `mv` that lies lowest and
furthest left (`HexHole.exists_good`). The depth test of the hole needs the band in the lower half
of the wall; for `mv` in the upper half we turn the hole by 180 degrees (`Shape.rotate`), which
keeps the depth test (`Shape.DepthTestK.rotate`) and the merged ball (`Shape.merge_rotate`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

namespace HexHole

variable {h' b : ℕ} {Y0 c0 sL : ℤ}

/-- The centre of the hole: a brick of the band row `Y0 + b - 1`. -/
def centre (b : ℕ) (Y0 c0 sL : ℤ) : ℤ × ℤ :=
  (c0 + sL + b - ((c0 + sL + b + Y0 + b - 1) % 2), Y0 + b - 1)

/-- The centre goes to the new square `(c0 - 1, Y0 - 1)`. -/
theorem newSq_centre (hb : 1 ≤ b) :
    newSq b Y0 c0 sL (centre b Y0 c0 sL) = (c0 - 1, Y0 - 1) := by
  have h1 : ¬ (Y0 + b - 1 ≤ Y0 - 1) := by omega
  have h2 : ¬ (Y0 + 2 * (b : ℤ) ≤ Y0 + b - 1) := by omega
  have h3 : Y0 + b - 1 - Y0 + 1 ≤ (b : ℤ) := by omega
  simp only [centre, newSq, side, off]
  simp only [h1, h2, h3, ↓reduceIte]
  have h4 : ¬ (c0 + sL + b - (c0 + sL + b + Y0 + b - 1) % 2 - sL - -(Y0 + b - 1 - Y0 + 1) ≤
      c0 - 1) := by omega
  have h5 : ¬ (c0 ≤ c0 + sL + b - (c0 + sL + b + Y0 + b - 1) % 2 - sL - 2 * b +
      -(Y0 + b - 1 - Y0 + 1)) := by omega
  simp only [h4, h5, ↓reduceIte]

/-- A hex distance at most `R`, as linear bounds. -/
theorem hexDist_le_bounds {F G : ℤ × ℤ} {R : ℤ} (hd : hexDist F G ≤ R) :
    F.2 - G.2 ≤ R ∧ G.2 - F.2 ≤ R ∧ (F.1 - G.1) + (F.2 - G.2) ≤ 2 * R + 1 ∧
      (F.1 - G.1) + (G.2 - F.2) ≤ 2 * R + 1 ∧ (G.1 - F.1) + (F.2 - G.2) ≤ 2 * R + 1 ∧
      (G.1 - F.1) + (G.2 - F.2) ≤ 2 * R + 1 := by
  unfold hexDist at hd
  have e1 := le_max_left (F.2 - G.2) (G.2 - F.2)
  have e2 := le_max_right (F.2 - G.2) (G.2 - F.2)
  have e3 := le_max_left (F.1 - G.1) (G.1 - F.1)
  have e4 := le_max_right (F.1 - G.1) (G.1 - F.1)
  have e5 := le_max_left (max (F.2 - G.2) (G.2 - F.2))
    ((max (F.1 - G.1) (G.1 - F.1) + max (F.2 - G.2) (G.2 - F.2)) / 2)
  have e6 := le_max_right (max (F.2 - G.2) (G.2 - F.2))
    ((max (F.1 - G.1) (G.1 - F.1) + max (F.2 - G.2) (G.2 - F.2)) / 2)
  omega

/-- **Every square of the ball of radius `b` around the centre goes to a square of the brick of
the new square `(c0 - 1, Y0 - 1)`.** -/
theorem bk_newSq_ball (_hb : 1 ≤ b) (hse : sL % 2 = 0) {X Y : ℤ} (hF : (X - Y) % 2 = 0)
    (hd : hexDist (X, Y) (centre b Y0 c0 sL) ≤ b) :
    bk (newSq b Y0 c0 sL (X, Y)) = bk (c0 - 1, Y0 - 1) := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hexDist_le_bounds hd
  clear hd
  simp only [centre] at d1 d2 d3 d4 d5 d6
  unfold newSq
  by_cases h1 : Y ≤ Y0 - 1
  · simp only [if_pos h1, side, bk, Prod.mk.injEq]
    split_ifs <;> omega
  · have h2 : ¬ Y0 + 2 * (b : ℤ) ≤ Y := by omega
    simp only [if_neg h1, if_neg h2, side, off, bk, Prod.mk.injEq, and_true]
    split_ifs <;> omega

end HexHole

/-- The face distance does not depend on the order of the two faces. -/
theorem faceDist_comm (h : ℕ) (F G : ℤ × ℤ) : faceDist h F G = faceDist h G F := by
  unfold faceDist
  split_ifs with h1 h2 h2 <;> first | rfl | (subst_vars; rfl) | skip
  rw [hexDist_comm, add_comm]

/-- Two bricks at hex distance zero are equal. -/
theorem eq_of_hexDist_eq_zero {h : ℕ} {F G : ℤ × ℤ} (hF : IsBrick h F) (hG : IsBrick h G)
    (e : hexDist F G = 0) : F = G := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := HexHole.hexDist_le_bounds e.le
  unfold IsBrick at hF hG
  ext <;> omega

/-- **Every element of a wall has two different faces.** -/
theorem exists_ne_mem_cellFaces {h : ℕ} (he : Even h) {m : ℤ × ℤ} (hm : IsWallCell h m) :
    ∃ F ∈ cellFaces h m, ∃ G ∈ cellFaces h m, F ≠ G := by
  -- an edge `e` of the wall whose squares are squares of `m`
  obtain ⟨e, he1, he2, he3⟩ : ∃ e : ℤ × ℤ, IsWallCell h e ∧ (e.1 % 2 = 1 ∨ e.2 % 2 = 1) ∧
      squaresAbove e ⊆ squaresAbove m := by
    by_cases hv : m.1 % 2 = 0 ∧ m.2 % 2 = 0
    · have hm' := hm
      unfold IsWallCell at hm'
      by_cases hl : 1 ≤ m.1 ∧ ¬ (m.1 ≤ 2 ∧ m.2 = 0)
      · refine ⟨(m.1 - 1, m.2), ?_, by simp only; omega, fun q hq => ?_⟩
        · unfold IsWallCell; simp only; omega
        · rw [mem_squaresAbove_iff] at hq ⊢; simp only at hq; omega
      · refine ⟨(m.1 + 1, m.2), ?_, by simp only; omega, fun q hq => ?_⟩
        · unfold IsWallCell; simp only; omega
        · rw [mem_squaresAbove_iff] at hq ⊢; simp only at hq; omega
    · exact ⟨m, hm, by omega, subset_rfl⟩
  have hsub : cellFaces h e ⊆ cellFaces h m := Set.image_mono he3
  obtain ⟨q, hq⟩ := squaresAbove_nonempty e
  have hF : wallFace h q ∈ cellFaces h e := ⟨q, hq, rfl⟩
  by_contra hc
  push Not at hc
  apply HexHole.not_cellFaces_eq_singleton he he1 he2 (wallFace h q)
  ext G
  constructor
  · intro hG
    exact hc G (hsub hG) _ (hsub hF)
  · rintro rfl
    exact hF

namespace Shape

variable {h h' : ℕ} (τ : Shape h h')

/-- **A shape that sends a ball to one face is far from the centre.** Let `B0` be a brick at
depth at least `k`, every face at `mv` a brick at hex distance at most one from `B0`, and let
`τ` send every brick at hex distance at most `k - 1` from `B0` to the face of `B0`. Then every
element that `τ` keeps differs from `mv`, and its faces are at face distance at least `k - 2`
from the faces at `mv`. -/
theorem far_of_merge (hh' : 1 ≤ h') (he' : Even h') {B0 mv : ℤ × ℤ} {k : ℕ} (hk : 2 ≤ k)
    (hB0 : IsBrick h B0) (hdep : (k : ℤ) ≤ outDepth h B0)
    (merge : ∀ F, IsBrick h F → hexDist F B0 ≤ k - 1 → τ.π F = τ.π B0)
    (hmv : ∀ G ∈ cellFaces h mv, IsBrick h G ∧ hexDist G B0 ≤ 1) :
    ∀ m ∈ fig1WallCells h, τ.own m ≠ none → m ≠ mv ∧
      ∀ F ∈ cellFaces h m, ∀ G ∈ cellFaces h mv, (k : ℤ) ≤ faceDist h F G + 2 := by
  intro m hm hown
  obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.mp hown
  have hkeep := τ.keep m hm m' hm'
  have hw : IsWallCell h' m' := (mem_fig1WallCells_iff hh' he' m').mp (τ.own_mem m hm m' hm')
  -- a face `E` of `m` outside the ball, since the faces of `m` go to two different faces
  obtain ⟨F1, hF1, F2, hF2, hne⟩ := exists_ne_mem_cellFaces he' hw
  rw [← hkeep] at hF1 hF2
  obtain ⟨E1, hE1, rfl⟩ := hF1
  obtain ⟨E2, hE2, rfl⟩ := hF2
  obtain ⟨E, hE, hEf⟩ : ∃ E ∈ cellFaces h m, ¬ (IsBrick h E ∧ hexDist E B0 ≤ k - 1) := by
    by_contra hc
    push Not at hc
    obtain ⟨b1, d1⟩ := hc E1 hE1
    obtain ⟨b2, d2⟩ := hc E2 hE2
    exact hne (by rw [merge E1 b1 d1, merge E2 b2 d2])
  have hB0o : B0 ≠ outFace := fun e => not_isBrick_outFace h (e ▸ hB0)
  have hEB : (k : ℤ) ≤ faceDist h B0 E := by
    rcases isWallFace_of_mem_cellFaces hE with hb | rfl
    · have hEo : E ≠ outFace := fun e => not_isBrick_outFace h (e ▸ hb)
      have h1 : (k : ℤ) ≤ hexDist E B0 := by
        by_contra h2
        exact hEf ⟨hb, by omega⟩
      have h2 := one_le_outDepth hb
      rw [faceDist_of_ne hB0o hEo, hexDist_comm]
      exact le_min h1 (by omega)
    · rw [faceDist_out_right hB0o]
      exact hdep
  -- every face of `m` is at face distance at least `k - 1` from `B0`
  have hF : ∀ F ∈ cellFaces h m, (k : ℤ) - 1 ≤ faceDist h B0 F := by
    rintro F ⟨q, hq, rfl⟩
    obtain ⟨q', hq', rfl⟩ := hE
    rcases wallFace_eq_or_adj h hq hq' with e | e
    · rw [e]; omega
    · have := faceDist_le_of_faceAdj (Or.inl hB0) e
      omega
  refine ⟨?_, ?_⟩
  · rintro rfl
    obtain ⟨b1, d1⟩ := hmv E hE
    exact hEf ⟨b1, by omega⟩
  · intro F hFm G hG
    obtain ⟨hGb, hGd⟩ := hmv G hG
    have h1 := hF F hFm
    rw [faceDist_comm] at h1
    have hFw := isWallFace_of_mem_cellFaces hFm
    by_cases h0 : hexDist G B0 = 0
    · rw [eq_of_hexDist_eq_zero hGb hB0 h0]
      omega
    · have hadj : FaceAdj h G B0 := Or.inl ⟨hGb, hB0, by have := hexDist_nonneg G B0; omega⟩
      have := faceDist_le_of_faceAdj hFw hadj
      omega

end Shape

namespace Shape

variable {h h' : ℕ} {τ : Shape h h'}

/-- **The turn keeps the depth test with a parameter.** -/
theorem DepthTestK.rotate {K : ℕ} (hT : τ.DepthTestK K) (hh : 1 ≤ h) (he : Even h) (hh' : 1 ≤ h')
    (he' : Even h') : (τ.rotate hh he hh' he').DepthTestK K where
  one_le := hT.one_le
  out := by
    change rotF h' (τ.π (rotF h outFace)) = outFace
    rw [rotF_outFace, hT.out, rotF_outFace]
  hex F G hF hG hF' hG' := by
    change IsBrick h' (rotF h' (τ.π (rotF h F))) at hF'
    change IsBrick h' (rotF h' (τ.π (rotF h G))) at hG'
    change hexDist F G ≤ hexDist (rotF h' (τ.π (rotF h F))) (rotF h' (τ.π (rotF h G))) + _
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
    change faceDepth h F ≤ faceDepth h' (rotF h' (τ.π (rotF h F))) + K
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
    · change faceDepth h (wallFace h (rotC h q)) ≤
        faceDepth h' (rotF h' (τ.π (rotF h (wallFace h (rotC h q))))) + _
      have hw : IsWallFace h (wallFace h q) := isBrick_or_eq_outFace_wallFace h q
      rw [wallFace_rotC he ⟨hsq.1, hsq.2.1⟩, rotF_rotF he hw, faceDepth_rotF he hw,
        faceDepth_rotF he' (τ.π_face _ hw)]
      exact hle

/-- **The turn keeps a merged ball**, around the turned centre. -/
theorem merge_rotate (hh : 1 ≤ h) (he : Even h) (hh' : 1 ≤ h') (he' : Even h') {B0 : ℤ × ℤ}
    (hB0 : IsBrick h B0) {R : ℤ}
    (merge : ∀ F, IsBrick h F → hexDist F B0 ≤ R → τ.π F = τ.π B0) :
    ∀ F, IsBrick h F → hexDist F (rotF h B0) ≤ R →
      (τ.rotate hh he hh' he').π F = (τ.rotate hh he hh' he').π (rotF h B0) := by
  intro F hF hd
  change rotF h' (τ.π (rotF h F)) = rotF h' (τ.π (rotF h (rotF h B0)))
  rw [rotF_rotF he (Or.inl hB0)]
  have hd' : hexDist (rotF h F) B0 ≤ R := by
    rw [← rotF_rotF he (Or.inl hB0), hexDist_rotF hF (isBrick_rotF he hB0)]
    exact hd
  rw [merge _ (isBrick_rotF he hF) hd']

end Shape

namespace HexHole

variable {h' b : ℕ} {Y0 c0 sL : ℤ}

/-- **The ball of radius `b` around the centre goes to one face.** -/
theorem pi_ball (hp : Params h' b Y0 c0 sL) {F : ℤ × ℤ} (hF : IsBrick (h' + 2 * b + 2) F)
    (hc : IsBrick (h' + 2 * b + 2) (centre b Y0 c0 sL)) (hd : hexDist F (centre b Y0 c0 sL) ≤ b) :
    pi h' b Y0 c0 sL F = pi h' b Y0 c0 sL (centre b Y0 c0 sL) := by
  unfold pi
  rw [if_pos hF, if_pos hc, newSq_centre hp.b1]
  obtain ⟨X, Y⟩ := F
  have hF' : (X - Y) % 2 = 0 := hF.2.2.2.2
  exact sqFace_eq_of_bk (bk_newSq_ball hp.b1 hp.sLe hF' hd)

/-- The hexagonal hole as a step of a chain. -/
def step (hg : Good h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {s : ℕ} (hs : (s : ℤ) = sL) :
    Step (h' + 2 * b + 2) h' (2 * (2 * (b + 1))) :=
  ⟨shape hg.toParams hh' he', realization hg.toParams hh' he' hs, ki hg hh' he', by omega, hh',
    he', rayOK hg.toParams hh' he' hs, rowMono hg.toParams hh' he' hs⟩

/-- The hexagonal hole turned by 180 degrees, as a step of a chain. -/
def stepRot (hg : Good h' b Y0 c0 sL) (hh' : 1 ≤ h') (he' : Even h') {s : ℕ}
    (hs : (s : ℤ) = sL) : Step (h' + 2 * b + 2) h' (2 * (2 * (b + 1))) :=
  ⟨(shape hg.toParams hh' he').rotate (by omega) (even_add_two_mul_add_two he' b) hh' he',
    (realization hg.toParams hh' he' hs).rotate (by omega) (even_add_two_mul_add_two he' b) hh'
      he',
    ((depthTestK hg hh' he').rotate (by omega) (even_add_two_mul_add_two he' b) hh' he').ki,
    by omega, hh', he',
    Shape.Realization.rayOK_rotate _ _ _ _ _ (rayOK hg.toParams hh' he' hs),
    Shape.Realization.rowMono_rotate _ _ _ _ _ (rowMono hg.toParams hh' he' hs)⟩

/-- **The choice of the hole for a deep element low in the wall.** Let `mv = (a, d)` be at
distance more than `b + 1` from every side of the wall of height `h' + 2b + 2`. The square
`((a - 1) / 2, (d - 1) / 2)` is a square at `mv`, and we take its brick as the centre. Then
every face at `mv` is a brick at hex distance at most one from the centre. If the centre is in
the lower half, the parameters of the hole are good. -/
theorem exists_good (hb : 1 ≤ b) (hh' : 1 ≤ h') {mv : ℤ × ℤ}
    (hmv : IsWallCell (h' + 2 * b + 2) mv)
    (hdeep : (b : ℤ) + 1 < sideB mv ∧ (b : ℤ) + 1 < sideT (h' + 2 * b + 2) mv ∧
      (b : ℤ) + 1 < sideL mv ∧ (b : ℤ) + 1 < sideR (h' + 2 * b + 2) mv)
    (hlow : 2 * ((mv.2 - 1) / 2 - b + 1) ≤ (h' : ℤ) + 2 * b + 2) :
    ∃ Y0 c0 : ℤ, Good h' b Y0 c0 ((b + 1 + (b + 1) % 2 : ℕ) : ℤ) ∧
      IsBrick (h' + 2 * b + 2) (centre b Y0 c0 ((b + 1 + (b + 1) % 2 : ℕ) : ℤ)) ∧
      (b : ℤ) + 1 ≤ outDepth (h' + 2 * b + 2) (centre b Y0 c0 ((b + 1 + (b + 1) % 2 : ℕ) : ℤ)) ∧
      ∀ G ∈ cellFaces (h' + 2 * b + 2) mv, IsBrick (h' + 2 * b + 2) G ∧
        hexDist G (centre b Y0 c0 ((b + 1 + (b + 1) % 2 : ℕ) : ℤ)) ≤ 1 := by
  obtain ⟨a, d⟩ := mv
  simp only [sideB, sideT, sideL, sideR] at hdeep hlow
  have hmv' := hmv
  unfold IsWallCell at hmv'
  simp only at hmv'
  push_cast at hdeep hmv' ⊢
  have hsL : (((b + 1 + (b + 1) % 2 : ℕ)) : ℤ) = b + 1 + (b + 1) % 2 := by push_cast; rfl
  have e : centre b ((d - 1) / 2 - b + 1)
      ((a - 1) / 2 + ((a - 1) / 2 + (d - 1) / 2) % 2 - (b + 1 + (b + 1) % 2) - b)
      (b + 1 + (b + 1) % 2) =
      ((a - 1) / 2 + ((a - 1) / 2 + (d - 1) / 2) % 2, (d - 1) / 2) := by
    unfold centre; ext <;> simp only <;> omega
  refine ⟨(d - 1) / 2 - b + 1,
    (a - 1) / 2 + ((a - 1) / 2 + (d - 1) / 2) % 2 - (b + 1 + (b + 1) % 2) - b,
    ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
      by omega, by omega, by omega⟩, ?_, ?_, ?_⟩
  · rw [e]; unfold IsBrick; simp only; omega
  · rw [e]; unfold outDepth; simp only; omega
  · rintro G ⟨q, hq, rfl⟩
    obtain ⟨x, y, rfl, h1, h2, h3, h4, -, -⟩ := exists_of_mem_squaresAbove hq
    simp only at h1 h2 h3 h4
    rw [e, wallFace_square, if_pos (by omega)]
    refine ⟨by unfold IsBrick; simp only; omega, ?_⟩
    unfold hexDist
    simp only
    omega

end HexHole

/-- A chain of one step keeps what its step keeps. -/
theorem Chain.own_single {h h' K : ℕ} (s : Step h h' K) (m : ℤ × ℤ) :
    (Chain.cons s (Chain.nil h')).own m = s.τ.own m := by
  simp [Chain.own]

/-- **A far chain for a deep element.** If the cell `mv` is at distance more than `k` from
every side of the wall, a hexagonal hole around it (turned by 180 degrees if `mv` is high in
the wall) is a chain of one step that is far from `mv`. -/
theorem exists_far_chain_deep {h k : ℕ} (hk : 2 ≤ k) (hh : 2 * k + 1 ≤ h) (he : Even h)
    {mv : ℤ × ℤ} (hmv : mv ∈ fig1WallCells h)
    (hdeep : (k : ℤ) < sideB mv ∧ (k : ℤ) < sideT h mv ∧ (k : ℤ) < sideL mv ∧
      (k : ℤ) < sideR h mv) :
    ∃ c : Chain h (h - 2 * k) (2 * (2 * k)), c.Far mv k := by
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 2 * b + 2 := ⟨h - 2 * b - 2, by omega⟩
  rw [show h' + 2 * b + 2 - 2 * (b + 1) = h' by omega]
  have hb : 1 ≤ b := by omega
  have hh' : 1 ≤ h' := by omega
  have he' : Even h' := by
    obtain ⟨a, ha⟩ := he
    exact ⟨a - b - 1, by omega⟩
  have hmv' := (mem_fig1WallCells_iff (by omega) he mv).mp hmv
  push_cast at hdeep
  by_cases hlow : 2 * ((mv.2 - 1) / 2 - b + 1) ≤ (h' : ℤ) + 2 * b + 2
  · -- the hole itself
    obtain ⟨Y0, c0, hg, hc, hdep, hG⟩ := HexHole.exists_good hb hh' hmv'
      (by push_cast; omega) hlow
    let c : Chain (h' + 2 * b + 2) h' (2 * (2 * (b + 1)) + 0) :=
      Chain.cons (HexHole.step hg hh' he' rfl) (Chain.nil h')
    refine ⟨c, ?_⟩
    intro m hm hown
    rw [Chain.own_single] at hown
    refine Shape.far_of_merge _ hh' he' (by omega) hc (by push_cast at hdep ⊢; omega) ?_ hG m hm
      hown
    intro F hF hd
    change HexHole.pi h' b Y0 c0 _ F = HexHole.pi h' b Y0 c0 _ _
    exact HexHole.pi_ball hg.toParams hF hc (hd.trans_eq (by push_cast; ring))
  · -- the hole turned by 180 degrees, around the turned element
    have hrot : IsWallCell (h' + 2 * b + 2) (rotC (h' + 2 * b + 2) mv) :=
      (isWallCell_rotC he).mpr hmv'
    obtain ⟨a, d⟩ := mv
    have hw := hmv'
    unfold IsWallCell at hw
    simp only [sideB, sideT, sideL, sideR] at hdeep hlow hw
    push_cast at hw
    obtain ⟨Y0, c0, hg, hc, hdep, hG⟩ := HexHole.exists_good hb hh' hrot
      (by simp only [sideB, sideT, sideL, sideR, rotC]; push_cast; omega)
      (by simp only [rotC]; push_cast; omega)
    let c : Chain (h' + 2 * b + 2) h' (2 * (2 * (b + 1)) + 0) :=
      Chain.cons (HexHole.stepRot hg hh' he' rfl) (Chain.nil h')
    refine ⟨c, ?_⟩
    intro m hm hown
    rw [Chain.own_single] at hown
    refine Shape.far_of_merge _ hh' he' (by omega) (isBrick_rotF he hc)
      (by rw [outDepth_rotF hc]; push_cast at hdep ⊢; omega) ?_ ?_ m hm hown
    · refine Shape.merge_rotate (by omega) he hh' he' hc ?_
      intro F hF hd
      change HexHole.pi h' b Y0 c0 _ F = HexHole.pi h' b Y0 c0 _ _
      exact HexHole.pi_ball hg.toParams hF hc (hd.trans_eq (by push_cast; ring))
    · intro G hGm
      have hGw := isWallFace_of_mem_cellFaces hGm
      have hG' : rotF (h' + 2 * b + 2) G ∈
          cellFaces (h' + 2 * b + 2) (rotC (h' + 2 * b + 2) (a, d)) := by
        rw [cellFaces_rotC he]
        exact Set.mem_image_of_mem _ hGm
      obtain ⟨b1, d1⟩ := hG _ hG'
      rw [← rotF_rotF he hGw]
      exact ⟨isBrick_rotF he b1, by rw [hexDist_rotF b1 hc]; exact d1⟩
