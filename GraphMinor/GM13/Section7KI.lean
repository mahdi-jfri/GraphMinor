module

public import GraphMinor.GM13.Section7Shape

/-!
# Graph Minors XIII, (7.3): a test for the distance comparison of a shape

`CellWall.transform_distGeSub` reduces (i) of (7.3) to the condition `Shape.KI` on the cells of
the wall of Fig. 1. This file gives three simple conditions on a shape that imply `KI 4`.
Write `D` and `D'` for the face distances of the old and the new wall.

- (S1) For bricks `F`, `G` that `π` sends to bricks, `hexDist F G ≤ hexDist (π F) (π G) + 2`.
- (S2) Every brick `F` is at most 2 steps deeper than `π F` (the outer face has depth 0).
- (S3) Every deleted element has a face `F` at most 1 step deeper than `π F`.

The idea: a distance `D (F, G)` goes either through the bricks, where (S1) loses at most 2, or
out to the outer face and back, where the two depths lose at most what (S2) and (S3) allow. A
deleted cell counts once in the old distance and not in the new one, and (S3) pays for it.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set

/-- The depth of a face: the number of steps from it to the outer face. -/
def faceDepth (h : ℕ) (F : ℤ × ℤ) : ℤ := if F = outFace then 0 else outDepth h F

theorem faceDepth_nonneg {h : ℕ} {F : ℤ × ℤ} (hF : IsWallFace h F) : 0 ≤ faceDepth h F := by
  unfold faceDepth
  split_ifs with h1
  · exact le_rfl
  · rcases hF with hb | ho
    · have := one_le_outDepth hb; omega
    · exact absurd ho h1

/-- The face distance is at most the sum of the depths. -/
theorem faceDist_le_faceDepth (h : ℕ) (F G : ℤ × ℤ) :
    faceDist h F G ≤ faceDepth h F + faceDepth h G := by
  unfold faceDist faceDepth
  split_ifs <;> omega

/-- When one of the faces is the outer face, the face distance is the sum of the depths. -/
theorem faceDist_eq_faceDepth {h : ℕ} {F G : ℤ × ℤ} (hFG : F = outFace ∨ G = outFace) :
    faceDist h F G = faceDepth h F + faceDepth h G := by
  unfold faceDist faceDepth
  split_ifs <;> simp_all

/-- The core comparison of two faces. -/
theorem faceDist_le_of_depths {h h' : ℕ} (π : ℤ × ℤ → ℤ × ℤ) (hπ : π outFace = outFace)
    (hS1 : ∀ F G, IsBrick h F → IsBrick h G → IsBrick h' (π F) → IsBrick h' (π G) →
      hexDist F G ≤ hexDist (π F) (π G) + 2)
    {F G : ℤ × ℤ} (hF : IsWallFace h F) (hG : IsWallFace h G) (hF' : IsWallFace h' (π F))
    (hG' : IsWallFace h' (π G)) {a b : ℤ} (hab : 2 ≤ a + b)
    (ha : faceDepth h F ≤ faceDepth h' (π F) + a) (hb : faceDepth h G ≤ faceDepth h' (π G) + b) :
    faceDist h F G ≤ faceDist h' (π F) (π G) + (a + b) := by
  have hle := faceDist_le_faceDepth h F G
  by_cases hout : π F = outFace ∨ π G = outFace
  · rw [faceDist_eq_faceDepth hout]
    omega
  · push Not at hout
    have hFo : F ≠ outFace := fun e => hout.1 (e ▸ hπ)
    have hGo : G ≠ outFace := fun e => hout.2 (e ▸ hπ)
    have hFb : IsBrick h F := hF.resolve_right hFo
    have hGb : IsBrick h G := hG.resolve_right hGo
    have hFb' : IsBrick h' (π F) := hF'.resolve_right hout.1
    have hGb' : IsBrick h' (π G) := hG'.resolve_right hout.2
    have h1 := hS1 F G hFb hGb hFb' hGb'
    rw [faceDist_of_ne hFo hGo, faceDist_of_ne hout.1 hout.2]
    simp only [faceDepth, hFo, hGo, hout.1, hout.2, ite_false] at ha hb
    omega

namespace Shape

variable {h h' : ℕ} (τ : Shape h h')

/-- The three conditions on a shape. -/
structure DepthTest : Prop where
  out : τ.π outFace = outFace
  hex : ∀ F G, IsBrick h F → IsBrick h G → IsBrick h' (τ.π F) → IsBrick h' (τ.π G) →
    hexDist F G ≤ hexDist (τ.π F) (τ.π G) + 2
  brick : ∀ F, IsBrick h F → faceDepth h F ≤ faceDepth h' (τ.π F) + 2
  del : ∀ m ∈ fig1WallCells h, τ.own m = none →
    ∃ q ∈ squaresAbove m, faceDepth h (wallFace h q) ≤ faceDepth h' (τ.π (wallFace h q)) + 1

variable {τ}

/-- At each cell, a face whose depth pays for the cell. -/
theorem DepthTest.exists_face (hT : τ.DepthTest) (c : ℤ × ℤ) {q₀ : ℤ × ℤ}
    (hq₀ : q₀ ∈ squaresAbove c) :
    ∃ q ∈ squaresAbove c, τ.π (wallFace h q) = τ.π (wallFace h q₀) ∧
      (cellInd (fig1WallCells h) c : ℤ) - cellInd τ.keptCells c ≤ 1 ∧
      (cellInd (fig1WallCells h) c : ℤ) - cellInd τ.keptCells c + faceDepth h (wallFace h q) ≤
        faceDepth h' (τ.π (wallFace h q)) + 2 := by
  have hface := isBrick_or_eq_outFace_wallFace h q₀
  have hgen : faceDepth h (wallFace h q₀) ≤ faceDepth h' (τ.π (wallFace h q₀)) + 2 := by
    rcases hface with hb | ho
    · exact hT.brick _ hb
    · have := faceDepth_nonneg (τ.π_face _ (Or.inr ho))
      have h0 : faceDepth h (wallFace h q₀) = 0 := by rw [ho]; simp [faceDepth]
      omega
  by_cases hc : c ∈ fig1WallCells h
  · by_cases hown : τ.own c = none
    · obtain ⟨q, hq, hle⟩ := hT.del c hc hown
      have he := τ.del c hc hown _ ⟨q, hq, rfl⟩ _ ⟨q₀, hq₀, rfl⟩
      refine ⟨q, hq, he, ?_, ?_⟩ <;>
      rw [cellInd_of_mem hc, cellInd_of_not_mem (fun h' : c ∈ τ.keptCells => h'.2 hown)] <;>
      push_cast <;> omega
    · refine ⟨q₀, hq₀, rfl, ?_, ?_⟩ <;>
      rw [cellInd_of_mem hc, cellInd_of_mem (show c ∈ τ.keptCells from ⟨hc, hown⟩)] <;>
      push_cast <;> omega
  · refine ⟨q₀, hq₀, rfl, ?_, ?_⟩ <;>
    rw [cellInd_of_not_mem hc, cellInd_of_not_mem (fun h' : c ∈ τ.keptCells => hc h'.1)] <;>
    push_cast <;> omega

/-- **The test gives `KI 4`.** -/
theorem DepthTest.ki (hT : τ.DepthTest) : τ.KI 4 := by
  intro c d _ q₀ hq₀ q₀' hq₀'
  obtain ⟨q, hq, e, h1, h2⟩ := hT.exists_face c hq₀
  obtain ⟨q', hq', e', h1', h2'⟩ := hT.exists_face d hq₀'
  refine ⟨q, hq, q', hq', ?_⟩
  have hF := isBrick_or_eq_outFace_wallFace h q
  have hG := isBrick_or_eq_outFace_wallFace h q'
  have key := faceDist_le_of_depths τ.π hT.out hT.hex hF hG (τ.π_face _ hF) (τ.π_face _ hG)
    (a := 2 - ((cellInd (fig1WallCells h) c : ℤ) - cellInd τ.keptCells c))
    (b := 2 - ((cellInd (fig1WallCells h) d : ℤ) - cellInd τ.keptCells d)) (by omega)
    (by omega) (by omega)
  rw [← e, ← e']
  omega

end Shape

end GraphMinor.GM13
