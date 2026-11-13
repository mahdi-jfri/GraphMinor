module

public import GraphMinor.GM06.Section5CutPathParameter
public import GraphMinor.GM07.Matched
import GraphMinor.GM06.Section5SingleStripFibers
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5CoverLinkageLift
import GraphMinor.GM06.Section5CarriedPath
public import GraphMinor.GM06.Alg57Reduction4Witness
import GraphMinor.GM06.Section5ReplaceLinkagePath
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# A path in the cut disc gives Reduction 4, for one path

This is the soundness half of Lemma 13 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`)
for `k = 1`. Cut the cylinder along the sole linkage path `P₁`. The result is the closed disc `D`
between the chosen lift `L₁ = Γ₁` of `P₁` and its one-turn translate `U₁ = Γ₂`, with the drawing `F`
of the lifted graph and the boundary of `D`. `FIND_4` returns a path `Q̃` of `F` from the left copy
`s̃` of `s₁` to the left copy `Γ₁ u` of a vertex `v = P₁(u)`. It is found in the graph `A_{1,j}`, so
it misses `U₁`, lies in the closure of the lifted region, and meets the tail of `P₁` after `v` only
at `v`.

Our proof of (5.7) says that projection is injective on `D` minus `U₁`, so the projected list is a
path. Here:

* `injOn_cutProj_of_not_mem_right`: the projection is injective on points off `Γ₂`
  (`radialCylinderProjection_single_strip_fibers`);
* `exists_projected_path_of_injOn`: a path of `F` on which the projection is injective, whose
  edges project to edges of `G`, projects to a path of `G` with the projected point set
  (`exists_path_image_of_isCarry`);
* `exists_parameterized_projection_of_injOn`: its parametrization has, as its lift in the
  cover, the cut path itself;
* `exists_reduction4Step_one_of_cut_path`: these give the one-path Reduction 4 step
  (`Section5Reduction4SideCondition`).
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface GraphMinor.GM11

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- The projection of the cut disc to the cylinder. -/
@[expose] noncomputable def cutProj (D : Set (ℝ × ℝ)) : D → ClosedCylinder :=
  fun p => radialCylinderProjection p.1

/-- The cut disc in the angular cover. -/
@[expose] noncomputable def cutCov (D : Set (ℝ × ℝ)) : D → CylinderCover :=
  fun p => planeToCylinderCover p.1

theorem continuous_cutProj : Continuous (cutProj D) :=
  continuous_radialCylinderProjection.comp continuous_subtype_val

theorem continuous_cutCov : Continuous (cutCov D) :=
  continuous_planeToCylinderCover.comp continuous_subtype_val

theorem isClosedMap_cutProj (hD : IsClosedDisc D) : IsClosedMap (cutProj D) := by
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  exact continuous_cutProj.isClosedMap

/-- The left copy of `s₁` is `(1, 2π)`; it projects to `s₁`. -/
theorem radialCylinderProjection_one_two_pi :
    radialCylinderProjection ((1 : ℝ), 2 * π) = cylinderM1Point 1 0 := by
  apply Subtype.ext
  apply Prod.ext
  · change max 1 (min 2 (1 : ℝ)) = 1
    norm_num
  · change Circle.exp (2 * π) = Circle.exp (2 * (((0 + 1 : ℕ) : ℝ)) * π / (1 : ℕ))
    norm_num

/-- The left lift `Γ₁` projects to the linkage curve. -/
theorem radialCylinderProjection_lift_one (L : CylinderLinkage 1 G) (hk : 0 < 1) (n : ℤ)
    (t : unitInterval) : radialCylinderProjection (liftedLinkageCurve hk L n t) = L.curve 0 t := by
  rw [radialCylinderProjection_liftedLinkageCurve]
  have hi : modIdx 1 hk n = 0 := Subsingleton.elim _ _
  rw [hi]

/-- The lift of the linkage curve from the chosen lift of `s₁` is `Γ₁` in the cover. -/
theorem cylinderCurveLiftAt_linkage_one (L : CylinderLinkage 1 G) (hk : 0 < 1) (t : unitInterval) :
    cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 t =
      planeToCylinderCover (liftedLinkageCurve hk L 1 t) := by
  have h := cylinderCurveLiftAt_eq_indexed_linkage_lift hk L 1 t
  have hi : modIdx 1 hk 1 = 0 := Subsingleton.elim _ _
  rw [hi] at h
  simpa [cylinderInitialLift] using h

/-- **The projection is injective off `U₁`.** Two points of the cut disc with the same projection,
neither on the right lift `Γ₂`, are equal. -/
theorem injOn_cutProj_of_not_mem_right (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) {S : Set D}
    (hS : ∀ p ∈ S, p.1 ∉ range (liftedLinkageCurve hG.1 L 2)) : InjOn (cutProj D) S := by
  intro p hp q hq heq
  rcases radialCylinderProjection_single_strip_fibers L hG hθ 1 hD hBd hstrip p.2 q.2 heq with
    he | ⟨t, ⟨hp2, -⟩ | ⟨hq2, -⟩⟩
  · exact Subtype.ext he
  · exact absurd ⟨t, hp2.symm⟩ (hS p hp)
  · exact absurd ⟨t, hq2.symm⟩ (hS q hq)

/-- A path of the cut drawing on which the projection is injective, whose edges project to edges
of `G`, projects to a path of `G` with the projected point set. -/
theorem exists_projected_path_of_injOn (hD : IsClosedDisc D) {F : Drawing D}
    (hFV : F.V = cutProj D ⁻¹' G.V) {Q : Drawing D} {s t : D} (hQ : IsSubpathOf F Q s t)
    (hinj : InjOn (cutProj D) Q.U) (hE : ∀ ec ∈ Q.E, cutProj D '' ec ∈ G.E)
    (hends : cutProj D s ≠ cutProj D t) :
    ∃ P : Drawing ClosedCylinder, IsSubpathOf G P (cutProj D s) (cutProj D t) ∧
      P.U = cutProj D '' Q.U := by
  have hclosed := isClosedMap_cutProj hD
  have hc : Continuous (cutProj D) := continuous_cutProj
  have hcarry : GM07.IsCarry Q G (cutProj D) Q.V := by
    refine ⟨hc.continuousOn, hinj, fun x hx => ⟨hx, ?_⟩, ?_⟩
    · have hxF := hQ.1.1 hx
      rw [hFV] at hxF
      exact hxF
    · intro ec hec x y hcap hx
      have hy : y ∈ Q.V :=
        (show y ∈ closure ec ∩ Q.V from hcap.symm ▸ mem_insert_of_mem x rfl).2
      refine ⟨hy, hE ec hec, ?_, image_closure_subset_closure_image hc⟩
      rw [hclosed.closure_image_eq_of_continuous hc]
      ext z
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hpV⟩
        have hpF : p ∈ F.V := by rw [hFV]; exact hpV
        have hpQ : p ∈ closure ec ∩ Q.V := by
          rw [hQ.1.closure_inter_V hec]
          exact ⟨hp, hpF⟩
        rw [hcap] at hpQ
        rcases hpQ with rfl | hpQ
        · exact Or.inl rfl
        · exact Or.inr (by rw [mem_singleton_iff.mp hpQ]; rfl)
      · have hxy : x ∈ closure ec ∩ Q.V ∧ y ∈ closure ec ∩ Q.V := by
          rw [hcap]; exact ⟨Or.inl rfl, Or.inr rfl⟩
        have hV : ∀ w ∈ closure ec ∩ Q.V, cutProj D w ∈ cutProj D '' closure ec ∩ G.V := by
          intro w hw
          refine ⟨mem_image_of_mem _ hw.1, ?_⟩
          have hwF := hQ.1.1 hw.2
          rw [hFV] at hwF
          exact hwF
        rintro (rfl | hz)
        · exact hV x hxy.1
        · rw [mem_singleton_iff.mp hz]; exact hV y hxy.2
  exact exists_path_image_of_isCarry hc hclosed hcarry hQ.2.2 hends

/-- A path of the cut disc from `(1, 2π)`, on which the projection is injective, projects to a
curve whose lift from the chosen lift of `s₁` is the cut path itself. -/
theorem exists_parameterized_projection_of_injOn {Q : Drawing D} {s t : D}
    (hQ : IsPathDrawing Q s t) (hscoord : s.1 = (1, 2 * π)) (hinj : InjOn (cutProj D) Q.U)
    {P : Drawing ClosedCylinder} (hPU : P.U = cutProj D '' Q.U) :
    ∃ q : Curve ClosedCylinder,
      ParametrizesSet q P.U (cylinderM1Point 1 0) (cutProj D t) ∧
      range (cylinderCurveLiftAt q (cylinderInitialLift 1 0).2) = cutCov D '' Q.U ∧
      cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1 = cutCov D t := by
  obtain ⟨c, hc⟩ := hQ.2
  let q : Curve ClosedCylinder := ⟨fun u => cutProj D (c u), continuous_cutProj.comp c.continuous⟩
  let qCover : C(unitInterval, CylinderCover) :=
    ⟨fun u => cutCov D (c u), continuous_cutCov.comp c.continuous⟩
  have hqinj : Function.Injective q := by
    intro u v huv
    apply hc.1
    apply hinj
    · rw [← hc.2.1]; exact mem_range_self u
    · rw [← hc.2.1]; exact mem_range_self v
    · exact huv
  have hqRange : range q = P.U := by
    change range (cutProj D ∘ c) = _
    rw [range_comp, hc.2.1, ← hPU]
  have hq0 : q 0 = cylinderM1Point 1 0 := by
    change radialCylinderProjection (c 0).1 = _
    rw [hc.2.2.1, hscoord, radialCylinderProjection_one_two_pi]
  have hq1 : q 1 = cutProj D t := by
    change cutProj D (c 1) = _
    rw [hc.2.2.2]
  have hcov0 : (qCover 0).2 = (cylinderInitialLift 1 0).2 := by
    change (c 0).1.2 = _
    rw [hc.2.2.1, hscoord]
    norm_num [cylinderInitialLift]
  have hLift := cylinderCurveLiftAt_eq_of_cover_lift q qCover (fun _ => rfl)
  rw [hcov0] at hLift
  refine ⟨q, ⟨hqinj, hqRange, hq0, hq1⟩, ?_, ?_⟩
  · rw [hLift]
    change range (cutCov D ∘ c) = _
    rw [range_comp, hc.2.1]
  · rw [hLift]
    change cutCov D (c 1) = cutCov D t
    rw [hc.2.2.2]

/-- **Lemma 13, soundness, for `k = 1`.** Let `Q̃` be a path of the cut drawing from the left copy
`(1, 2π)` of `s₁` to the left copy `Γ₁ u` of a vertex `v = P₁(u)`, `u > 0`. Suppose that `Q̃` misses
the right lift `Γ₂`, that its edges project to edges of `G`, that it lies in the closure of the
lifted region, that its projection meets the tail `T` of `P₁` after `v` only at `v`, and that the
lift of the prefix `P₁[s₁, v]` does not lie in the closure of the lifted region. Then the
one-path Reduction 4 applies. -/
theorem exists_reduction4Step_one_of_cut_path (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) {F : Drawing D}
    (hFV : F.V = cutProj D ⁻¹' G.V) {Q : Drawing D} {s t : D} (hQ : IsSubpathOf F Q s t)
    (hscoord : s.1 = (1, 2 * π)) {u : unitInterval} (hu : 0 < u)
    (huV : L.curve 0 u ∈ (L.pathDrawing 0).V) (ht : t.1 = liftedLinkageCurve hG.1 L 1 u)
    (hright : ∀ p ∈ Q.U, p.1 ∉ range (liftedLinkageCurve hG.1 L 2))
    (hE : ∀ ec ∈ Q.E, cutProj D '' ec ∈ G.E)
    (hR : cutCov D '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0))
    (hpre : ¬ (cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 '' Icc 0 u ⊆
      closure (cylinderCoverRegion 1 G 0)))
    {T : Drawing ClosedCylinder} (hT : IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1))
    (hQT : cutProj D '' Q.U ∩ T.U ⊆ {L.curve 0 u}) :
    ∃ L' : CylinderLinkage 1 G, Section5Reduction4Step 1 G L G L' := by
  have hinj := injOn_cutProj_of_not_mem_right L hG hθ hD hBd hstrip hright
  have hs : cutProj D s = cylinderM1Point 1 0 := by
    change radialCylinderProjection s.1 = _
    rw [hscoord, radialCylinderProjection_one_two_pi]
  have htP : cutProj D t = L.curve 0 u := by
    change radialCylinderProjection t.1 = _
    rw [ht, radialCylinderProjection_lift_one]
  have hvs : L.curve 0 u ≠ cylinderM1Point 1 0 := by
    intro h
    have heq : L.curve 0 u = L.curve 0 0 := h.trans (L.curve_parametrizes 0).2.2.1.symm
    exact hu.ne' ((L.curve_parametrizes 0).1 heq)
  have hends : cutProj D s ≠ cutProj D t := by rw [hs, htP]; exact hvs.symm
  obtain ⟨P, hP, hPU⟩ := exists_projected_path_of_injOn hD hFV hQ hinj hE hends
  rw [hs, htP] at hP
  obtain ⟨q, hq, hqR, hqEnd⟩ := exists_parameterized_projection_of_injOn hQ.2.2 hscoord hinj hPU
  rw [htP] at hq
  have hst : cylinderM1Point 1 0 ≠ L.curve 0 1 := isPathDrawing_start_ne_end (L.isPath 0)
  have hPT : P.U ∩ T.U ⊆ {L.curve 0 u} := by rw [hPU]; exact hQT
  obtain ⟨R', hRG, hR', hRU⟩ := exists_path_append_tail (L.isSubdrawing 0).1 hP.1 hP.2.2 hT hst hPT
  have hdisj : ∀ j : Fin 1, j ≠ 0 → Disjoint R'.U (L.pathDrawing j).U := by
    intro j hj
    exact False.elim (hj (Subsingleton.elim _ _))
  obtain ⟨L', hRi, -, hunchanged⟩ := exists_linkage_replacing_path L 0 hRG hR' hdisj
  have hlift : cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u = cutCov D t := by
    rw [cylinderCurveLiftAt_linkage_one L hG.1 u]
    change _ = planeToCylinderCover t.1
    rw [ht]
  have htQ : t ∈ Q.U := Q.V_subset_U (isPathDrawing_end_vertices hQ.2.2).2
  have huR : cylinderCurveLiftAt (L.curve 0) (cylinderInitialLift 1 0).2 u ∈
      closure (cylinderCoverRegion 1 G 0) := by
    rw [hlift]; exact hR (mem_image_of_mem _ htQ)
  refine ⟨L', rfl, Or.inr ⟨rfl, 0, u, T, P, q, huV, huR, hpre, hT, hP.1, hP.2.1, hP.2.2, hq,
    by rw [hqR]; exact hR, by rw [hqEnd, hlift], ?_, hunchanged⟩⟩
  rw [hRi, hRU]

end GraphMinor.GM06
