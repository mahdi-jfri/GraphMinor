module

public import GraphMinor.GM06.Section5StripCuffs
import GraphMinor.GM06.Section5TerminalGap
import GraphMinor.GM06.Section5GapEdge
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# An outer cuff edge contains a linkage terminal in its closure

For VI (5.1), page 129, an added outer cuff edge in the strip
closure must span the terminal angular gap. The gap has no drawing
vertex in its open part. Its open curve therefore stays in that edge,
and its two ends lie in the edge closure. We record the end on Pᵢ,
which will exclude such an edge when Rᵢ meets Pᵢ only at sᵢ.
-/

public section

namespace GraphMinor.GM06

open Set Topology Real GraphMinor.Surface

/-- Every added terminal-cuff edge in the strip closure is incident
with the terminal vertex of Pᵢ. -/
theorem curve_one_mem_closure_of_terminal_cuff_edge
    {k : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hFV : F.V = G.V) (i : Fin k) {e : Set ClosedCylinder} (he : e ∈ F.E)
    (heC : e ⊆ cylinderCuff2) (heS : e ⊆ closure (cylinderStrip L i)) :
    L.curve i 1 ∈ closure e := by
  let m : ℤ := (i.val : ℤ) + 1
  let a : ℝ := (liftedLinkageCurve hG.1 L m 1).2
  let b : ℝ := (liftedLinkageCurve hG.1 L (m + 1) 1).2
  have hab : a < b := (liftedLinkageCurve_consecutive_ends hG.1 L hθ m).2
  have hpoint (n : ℤ) : cylinderPoint 2 (by norm_num) (liftedLinkageCurve hG.1 L n 1).2 =
      L.curve (modIdx k hG.1 n) 1 := by
    rw [← radialCylinderProjection_liftedLinkageCurve hG.1 L n 1]
    apply Subtype.ext
    apply Prod.ext
    · change 2 = max 1 (min 2 (liftedLinkageCurve hG.1 L n 1).1)
      rw [(liftedLinkageCurve_props_raw hG.1 L n).2.2.1]
      norm_num
    · rfl
  have hendV (n : ℤ) : cylinderPoint 2 (by norm_num) (liftedLinkageCurve hG.1 L n 1).2 ∈ G.V := by
    rw [hpoint]
    exact (L.isSubdrawing _).1.1 (isPathDrawing_end_vertices (L.isPath _)).2
  obtain ⟨x, hx⟩ := he.1
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ m
  obtain ⟨p, hp, hpx⟩ := (image_stripDisc_eq_closure_strip L hG hθ i hD hBd hstrip).symm ▸ heS hx
  have hp2 : p.1 = 2 := (radialCylinderProjection_fst (hstrip hp)).symm.trans
    ((congrArg (fun z : ClosedCylinder => z.1.1) hpx).trans (heC hx))
  have hang : p.2 ∈ Icc a b := stripDisc_radius_two_mem_interval L hG hθ m hD hBd hstrip hp hp2
  have hxV : x ∉ G.V := by
    rw [← hFV]
    exact (he.2.1 hx).2
  have hxc : cylinderPoint 2 (by norm_num) p.2 = x := by
    rw [← hpx]
    apply Subtype.ext
    apply Prod.ext
    · change 2 = (radialCylinderProjection p).1.1
      rw [radialCylinderProjection_fst (hstrip hp), hp2]
    · rfl
  have hpa : p.2 ≠ a := by
    intro hh
    have hv := hendV m
    change cylinderPoint 2 (by norm_num) a ∈ G.V at hv
    rw [← hh, hxc] at hv
    exact hxV hv
  have hpb : p.2 ≠ b := by
    intro hh
    have hv := hendV (m + 1)
    change cylinderPoint 2 (by norm_num) b ∈ G.V at hv
    rw [← hh, hxc] at hv
    exact hxV hv
  have hstrict : a < p.2 ∧ p.2 < b :=
    ⟨lt_of_le_of_ne hang.1 hpa.symm, lt_of_le_of_ne hang.2 hpb⟩
  let f : Curve ClosedCylinder :=
    ⟨fun t => cylinderPoint 2 (by norm_num) (a + (b - a) * (t : ℝ)), by
      dsimp [cylinderPoint]
      fun_prop⟩
  have hf : f '' Ioo 0 1 ⊆ F.U \ F.V := by
    rintro y ⟨t, ht, rfl⟩
    constructor
    · rw [hFU, bd_closedCylinder]
      exact Or.inr (Or.inr rfl)
    · rw [hFV]
      apply terminal_gap_point_not_mem_V L hG hθ m
      change a < a + (b - a) * (t : ℝ) ∧ a + (b - a) * (t : ℝ) < b
      have ht0 : (0 : ℝ) < (t : ℝ) := ht.1
      have ht1 : (t : ℝ) < 1 := ht.2
      constructor <;> nlinarith only [hab, ht0, ht1]
  let t : unitInterval := ⟨(p.2 - a) / (b - a),
    (div_pos (sub_pos.mpr hstrict.1) (sub_pos.mpr hab)).le,
    ((div_lt_one₀ (sub_pos.mpr hab)).mpr (by linarith only [hstrict.2])).le⟩
  have htI : t ∈ Ioo (0 : unitInterval) 1 :=
    ⟨div_pos (sub_pos.mpr hstrict.1) (sub_pos.mpr hab),
      (div_lt_one₀ (sub_pos.mpr hab)).mpr (by linarith only [hstrict.2])⟩
  have hft : f t = x := by
    rw [← hxc]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp (a + (b - a) * ((p.2 - a) / (b - a))) = Circle.exp p.2
      rw [mul_div_cancel₀ _ (sub_ne_zero.mpr hab.ne'), add_sub_cancel]
  obtain ⟨_, hends⟩ := arc_interior_subset_edge he hf ⟨x, hx, t, htI, hft⟩
  have hf0 : f 0 = L.curve i 1 := by
    have hh := hpoint m
    rw [modIdx_natCast_succ] at hh
    convert hh using 1
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp (a + (b - a) * ((0 : unitInterval) : ℝ)) = Circle.exp a
      simp
  exact hf0 ▸ hends (mem_range_self 0)

end GraphMinor.GM06
