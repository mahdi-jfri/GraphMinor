module

public import GraphMinor.GM06.Alg57OnePathLemma12
import GraphMinor.GM06.Alg57Reduction4Complete
import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# One-path Reduction 4 in the cut disc

For `k = 1` we put Lemmas 12 and 13 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`)
together. `OnePathReduction4At` says, in the cut disc `D`, what `FIND_4` looks for: a vertex `Γ₁ u`
of the lift of `P₁` with `u > 0` whose lifted prefix is not in the closure of the lifted region, and
a path of the cut drawing `F` from the start of `Γ₁` to `Γ₁ u` that misses `Γ₂`, has edges over
edges of `G`, lies over the closure of the lifted region, and whose projection meets the tail of
`P₁` from `P₁(u)` only at `P₁(u)`.

`exists_reduction4Step_one_iff` says that, when Reductions 1 and 2 do not apply and `s₁` does not
have valency one, a one-path Reduction 4 step exists exactly when `OnePathReduction4At` holds.
Soundness is `exists_reduction4Step_one_of_cut_path`. Completeness is
`exists_cut_path_of_reduction4Step_one`, whose path meets `Γ₁` only at its ends, and
`cutProj_inter_tail_subset` turns this into the tail condition.
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- A path of the cut disc that misses `Γ₂` and meets `Γ₁` only at its ends `Γ₁ 0` and `Γ₁ u`,
with `u > 0`, projects to a set that meets the tail of `P₁` from `P₁(u)` only at `P₁(u)`. The tail
is `P₁` on `[u, 1]` (`range_eq_image_uIcc_of_subarc`), so it does not contain `s₁ = P₁(0)`. -/
theorem cutProj_inter_tail_subset (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) {Q : Drawing D} {s w : D}
    (hs : s.1 = (1, 2 * π)) {u : 𝕀} (hu : 0 < u) (hw : w.1 = liftedLinkageCurve hG.1 L 1 u)
    (hright : ∀ p ∈ Q.U, p.1 ∉ range (liftedLinkageCurve hG.1 L 2))
    (hΓ : ∀ p ∈ Q.U, p.1 ∈ range (liftedLinkageCurve hG.1 L 1) → p = s ∨ p = w)
    {T : Drawing ClosedCylinder}
    (hT : IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1)) :
    cutProj D '' Q.U ∩ T.U ⊆ {L.curve 0 u} := by
  rintro _ ⟨⟨p, hp, rfl⟩, hxT⟩
  rcases hT with ⟨-, hU, -⟩ | ⟨-, hTP, hTpath⟩
  · rw [hU] at hxT
    exact hxT
  obtain ⟨hfi, hfr, hf0, hf1⟩ := L.curve_parametrizes 0
  rcases mem_lifts_of_cutProj_mem_path L hG hθ hD hBd hstrip (hTP hxT) with hΓ1 | hΓ2
  · rcases hΓ p hp hΓ1 with rfl | rfl
    · exfalso
      have hps : cutProj D p = cylinderM1Point 1 0 := by
        change radialCylinderProjection p.1 = _
        rw [hs, radialCylinderProjection_one_two_pi]
      obtain ⟨g', hg'i, hg'r, hg'0, hg'1⟩ := hTpath.2
      have hrange : range g' = L.curve 0 '' uIcc u 1 :=
        range_eq_image_uIcc_of_subarc hfi hg'i (by rw [hg'r, hfr]; exact hTP) hg'0 hg'1
      rw [← hg'r, hrange, hps, ← hf0] at hxT
      obtain ⟨r, hr, hr0⟩ := hxT
      have hr0' : r = 0 := hfi hr0
      rw [hr0', uIcc_of_le unitInterval.le_one'] at hr
      exact absurd hr.1 (not_le.mpr hu)
    · change radialCylinderProjection p.1 ∈ _
      rw [hw, radialCylinderProjection_lift_one]
      exact mem_singleton _
  · exact absurd hΓ2 (hright p hp)

/-- **One-path Reduction 4 in the cut disc**: what `FIND_4` looks for when `k = 1`. -/
@[expose] def OnePathReduction4At (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (D : Set (ℝ × ℝ)) (F : Drawing D) : Prop :=
  ∃ u : 𝕀, 0 < u ∧ L.curve 0 u ∈ (L.pathDrawing 0).V ∧
    ¬ (cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 '' Icc 0 u ⊆
      closure (cylinderCoverRegion 1 G 0)) ∧
    ∃ (s w : D) (Q : Drawing D), IsSubpathOf F Q s w ∧ s.1 = (1, 2 * π) ∧
      w.1 = liftedLinkageCurve hG.1 L 1 u ∧
      (∀ p ∈ Q.U, p.1 ∉ range (liftedLinkageCurve hG.1 L 2)) ∧
      (∀ ec ∈ Q.E, cutProj D '' ec ∈ G.E) ∧
      cutCov D '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0) ∧
      ∃ T : Drawing ClosedCylinder,
        IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1) ∧
        cutProj D '' Q.U ∩ T.U ⊆ {L.curve 0 u}

/-- **Lemmas 12 and 13 for `k = 1`.** When Reductions 1 and 2 do not apply and `s₁` does not have
valency one, a one-path Reduction 4 step exists exactly when `OnePathReduction4At` holds in the cut
disc. -/
theorem exists_reduction4Step_one_iff (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction1Step 1 G L H M)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e) :
    (∃ L' : CylinderLinkage 1 G, Section5Reduction4Step 1 G L G L') ↔
      OnePathReduction4At L hG D F := by
  constructor
  · rintro ⟨L', h⟩
    obtain ⟨u, hu, huV, hpre, s, w, Q, hQ, hs, hw, hright, hΓ, hE, hR⟩ :=
      exists_cut_path_of_reduction4Step_one L hG hθ hno1 hno2 hval hD hBd hstrip F hFU hFV
        hEdges h
    have hPG : (L.pathDrawing 0).IsSubdrawing G := (L.isSubdrawing 0).1
    have htP : L.curve 0 1 ∈ (L.pathDrawing 0).V := by
      rw [← (L.curve_parametrizes 0).2.2.2]
      exact (isPathDrawing_end_vertices (L.isPath 0)).2
    obtain ⟨T, hT⟩ : ∃ T : Drawing ClosedCylinder,
        IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1) := by
      by_cases hu1 : L.curve 0 u = L.curve 0 1
      · let T := walkDrawing (L.pathDrawing 0) (GraphWalk.nil htP)
        have hTV : T.V = {L.curve 0 1} := by
          rw [walkDrawing_V]
          ext x
          simp [GraphWalk.support]
        have hTU : T.U = {L.curve 0 1} := by
          ext x
          rw [mem_walkDrawing_U]
          simp [GraphWalk.support, GraphWalk.edges]
        exact ⟨T, Or.inl ⟨hu1, by rw [hTU, hu1], by rw [hTV, hu1]⟩⟩
      · obtain ⟨T, hT⟩ := exists_subpath_of_isPathDrawing (L.isPath 0) huV htP hu1
        exact ⟨T, Or.inr hT⟩
    exact ⟨u, hu, huV, hpre, s, w, Q, hQ, hs, hw, hright, hE, hR, T, hT,
      cutProj_inter_tail_subset L hG hθ hD hBd hstrip hs hu hw hright hΓ hT⟩
  · rintro ⟨u, hu, huV, hpre, s, w, Q, hQ, hs, hw, hright, hE, hR, T, hT, hQT⟩
    exact exists_reduction4Step_one_of_cut_path L hG hθ hD hBd hstrip hFV hQ hs hu huV hw hright
      hE hR hpre hT hQT

end GraphMinor.GM06
