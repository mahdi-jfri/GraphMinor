module

public import GraphMinor.LPPS22.TheoremA2
public import GraphMinor.Surface.Cap
public import GraphMinor.Surface.Wedge
public import GraphMinor.Surface.OrientSign

/-!
# Star-Forest Normalization and Shared Boundary Detachment

Helper constructions for proving Graph Minors VII (3.6) with the explicit LPPS22 bound:

1. `subset_disc_of_open_diff_bd`: if `O` is open in a surface `S`, `D` is a closed disc with
   `Disjoint (discInt D) (bd S)` and `O \ bd S ⊆ discInt D`, then `O ⊆ D` and
   `O ∩ bd S ⊆ discBd D`.
2. `exists_shared_bd_half_disc`: at an endpoint `s ∈ bd S` of a proper `I`-arc `F`, inside any
   open neighbourhood `W ∋ s` avoiding the other endpoint `t`, constructs a tiny boundary
   closed disc `D ⊆ W` meeting `F` only at `{s}`, with a separating proper `I`-arc
   `A ⊆ discBd D`, `IsOpen (D \ A)`, a midpoint `y_mid ∈ A \ {s, t_D}`, and an arc `seg ⊆ D`
   from `s` to `y_mid`.
3. `exists_star_in_disc`: given a closed disc `D_sub`, a closed set `G_U` with `p ∈ discInt D_sub \ G_U`,
   and `r` distinct boundary points `q : Fin r → S` on `discBd D_sub`, builds a small interior
   closed disc `Δ ⊆ discInt D_sub \ G_U` around `p` and radial star arcs from `p` to `q i`
   split into inner segments in `Δ` and pairwise disjoint outer proper `I`-arcs in `D_sub \ discInt Δ`.
4. `drawing_of_arcs` and `isGraphForest_of_star_arcs`: builds a `Drawing S` from a finite vertex
   set and pairwise interior-disjoint `I`-arcs, and proves acyclicity (`IsGraphForest`) when every
   arc connects a hub to a unique leaf.
-/

@[expose] public section

namespace GraphMinor.LPPS22

open Set Topology Metric Filter
open GraphMinor.Surface GraphMinor.GHR18 GraphMinor.GM07

/-! ### Section 1: Boundary closure helper -/

/-- In a surface `S`, every open set `O` satisfies `O ⊆ closure (O \ bd S)`. -/
theorem subset_closure_diff_bd {S : Type} [TopologicalSpace S] (hS : IsSurface S)
    {O : Set S} (hO : IsOpen O) : O ⊆ closure (O \ bd S) := by
  intro x hxO
  obtain ⟨ch, hxU⟩ := exists_surfChart (hS.2.2 x)
  rw [_root_.mem_closure_iff]
  intro U hU hxU'
  have hOU_open : IsOpen (O ∩ U) := hO.inter hU
  have hxOU : x ∈ O ∩ U := ⟨hxO, hxU'⟩
  have hcont : ContinuousWithinAt ch.k (ch.O ∩ halfPlane) (ch.j x) := ch.hk (ch.j x) (ch.hm hxU)
  have hnhd : ch.k ⁻¹' (O ∩ U) ∈ 𝓝[ch.O ∩ halfPlane] (ch.j x) :=
    hcont (hOU_open.mem_nhds (by rwa [ch.hl hxU]))
  rw [Metric.mem_nhdsWithin_iff] at hnhd
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := hnhd
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp ch.hO (ch.j x) (ch.hm hxU).1
  let ε : ℝ := min (δ / 2) (r / 2)
  have hε_pos : 0 < ε := lt_min (by linarith) (by linarith)
  let w : ℂ := ch.j x + (ε : ℂ)
  have hw_dist : dist w (ch.j x) = ε := by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hε_pos.le]
  have hw_re : 0 < w.re := by
    have hre : 0 ≤ (ch.j x).re := (ch.hm hxU).2
    simp only [w, Complex.add_re, Complex.ofReal_re]
    linarith
  have hw_mem : w ∈ ch.O ∩ halfPlane :=
    ⟨hr_ball (by rw [Metric.mem_ball, hw_dist]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)),
     hw_re.le⟩
  have hw_ball : w ∈ Metric.ball (ch.j x) δ := by
    rw [Metric.mem_ball, hw_dist]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hkw_OU : ch.k w ∈ O ∩ U := hδ_sub ⟨hw_ball, hw_mem⟩
  have hkw_U : ch.k w ∈ ch.U := ch.hk' hw_mem
  have hkw_nb : ch.k w ∉ bd S := by
    rw [ch.not_mem_bd_iff hkw_U, ch.hr hw_mem]
    exact hw_re
  exact ⟨ch.k w, hkw_OU.2, hkw_OU.1, hkw_nb⟩

/-- If `O` is open in a surface `S`, `D` is a closed disc with `Disjoint (discInt D) (bd S)`,
and `O \ bd S ⊆ discInt D`, then `O ⊆ D` and `O ∩ bd S ⊆ discBd D`. -/
theorem subset_disc_of_open_diff_bd {S : Type} [TopologicalSpace S] (hS : IsSurface S)
    {O D : Set S} (hO : IsOpen O) (hD : IsClosedDisc D)
    (hDbd : Disjoint (discInt D) (bd S)) (hsub : O \ bd S ⊆ discInt D) :
    O ⊆ D ∧ O ∩ bd S ⊆ discBd D := by
  have ht2S : T2Space S := hS.2.1
  have hOD : O ⊆ D := by
    calc O ⊆ closure (O \ bd S) := subset_closure_diff_bd hS hO
      _ ⊆ closure (discInt D) := closure_mono hsub
      _ ⊆ closure D := closure_mono (discInt_subset D)
      _ = D := hD.isClosed.closure_eq
  refine ⟨hOD, fun x ⟨hxO, hxbd⟩ => ?_⟩
  by_contra hnb
  exact Set.disjoint_left.mp hDbd ⟨hOD hxO, hnb⟩ hxbd

/-! ### Section 2: Shared boundary half-disc detachment (`exists_shared_bd_half_disc`) -/

/-- The unit square `Q = [0, 1] × [0, 1] ⊆ ℂ` and its 3-sided interior boundary arc `A_Q` and
diagonal segment `seg_Q` to the right-side midpoint `(1, 1/2)`. -/
private theorem unit_square_half_disc_data :
    let Q : Set ℂ := Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1
    let A_Q : Set ℂ :=
      segment ℝ (⟨0, 0⟩ : ℂ) ⟨1, 0⟩ ∪ segment ℝ (⟨1, 0⟩ : ℂ) ⟨1, 1⟩ ∪
        segment ℝ (⟨1, 1⟩ : ℂ) ⟨0, 1⟩
    let w_mid : ℂ := ⟨1, 1 / 2⟩
    let seg_Q : Set ℂ := segment ℝ (⟨0, 0⟩ : ℂ) w_mid
    IsClosedDisc Q ∧ IsCompact Q ∧
      A_Q ⊆ discBd Q ∧
      IsLineWithEnds A_Q (⟨0, 0⟩ : ℂ) ⟨0, 1⟩ ∧
      A_Q ∩ {w : ℂ | w.re = 0} = {⟨0, 0⟩, ⟨0, 1⟩} ∧
      Q \ A_Q = (Ioo (-1 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1) ∩ halfPlane ∧
      w_mid ∈ A_Q \ {⟨0, 0⟩, ⟨0, 1⟩} ∧
      IsLineWithEnds seg_Q (⟨0, 0⟩ : ℂ) w_mid ∧
      seg_Q ⊆ Q ∧
      seg_Q \ {⟨0, 0⟩, w_mid} ⊆ discInt Q := by
  intro Q A_Q w_mid seg_Q
  obtain ⟨hQ, hQbd⟩ := isClosedDisc_rect (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hQcomp : IsCompact Q := isCompact_Icc.reProdIm isCompact_Icc
  have hQint : interior Q = Ioo (0 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1 := by
    show interior (Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1) = _
    rw [Complex.interior_reProdIm, interior_Icc]
  have hQfr : frontier Q = Q \ (Ioo (0 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1) := by
    rw [hQcomp.isClosed.frontier_eq, hQint]
  have hQdiscInt : discInt Q = Ioo (0 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1 := by
    change Q \ discBd Q = _
    rw [hQbd, hQfr]
    ext z
    simp only [Set.mem_sdiff, Complex.mem_reProdIm, mem_Ioo]
    constructor
    · rintro ⟨hz, hnot⟩
      by_contra h
      exact hnot ⟨hz, h⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact ⟨⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩, fun h => h.2 ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩⟩
  -- Explicit characterizations of the three sides of `A_Q`.
  let s1 : Set ℂ := segment ℝ (⟨0, 0⟩ : ℂ) ⟨1, 0⟩
  let s2 : Set ℂ := segment ℝ (⟨1, 0⟩ : ℂ) ⟨1, 1⟩
  let s3 : Set ℂ := segment ℝ (⟨1, 1⟩ : ℂ) ⟨0, 1⟩
  have hs1_iff : ∀ z : ℂ, z ∈ s1 ↔ z.re ∈ Icc (0 : ℝ) 1 ∧ z.im = 0 := fun z => by
    constructor
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨⟨by linarith, by linarith⟩, by ring⟩
    · rintro ⟨⟨h0, h1⟩, him⟩
      refine ⟨1 - z.re, z.re, by linarith, h0, by ring, ?_⟩
      apply Complex.ext <;>
        simp [Complex.real_smul, him]
  have hs2_iff : ∀ z : ℂ, z ∈ s2 ↔ z.re = 1 ∧ z.im ∈ Icc (0 : ℝ) 1 := fun z => by
    constructor
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨by linarith, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨hre, ⟨h0, h1⟩⟩
      refine ⟨1 - z.im, z.im, by linarith, h0, by ring, ?_⟩
      apply Complex.ext <;>
        simp [Complex.real_smul, hre]
  have hs3_iff : ∀ z : ℂ, z ∈ s3 ↔ z.re ∈ Icc (0 : ℝ) 1 ∧ z.im = 1 := fun z => by
    constructor
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · rintro ⟨⟨h0, h1⟩, him⟩
      refine ⟨z.re, 1 - z.re, h0, by linarith, by ring, ?_⟩
      apply Complex.ext <;>
        simp [Complex.real_smul, him]
  have hAQ_sub : A_Q ⊆ discBd Q := by
    rw [hQbd, hQfr]
    intro z hz
    simp only [Set.mem_sdiff, Complex.mem_reProdIm, mem_Ioo]
    rcases hz with (h | h) | h
    · obtain ⟨hre, him⟩ := (hs1_iff z).mp h
      exact ⟨⟨hre, ⟨by linarith, by linarith⟩⟩, fun h' => by linarith [h'.2.1]⟩
    · obtain ⟨hre, him⟩ := (hs2_iff z).mp h
      exact ⟨⟨⟨by linarith, by linarith⟩, him⟩, fun h' => by linarith [h'.1.2]⟩
    · obtain ⟨hre, him⟩ := (hs3_iff z).mp h
      exact ⟨⟨hre, ⟨by linarith, by linarith⟩⟩, fun h' => by linarith [h'.2.2]⟩
  have hline1 : IsLineWithEnds s1 (⟨0, 0⟩ : ℂ) ⟨1, 0⟩ :=
    isLineWithEnds_segment (by intro h; have := congrArg Complex.re h; norm_num at this)
  have hline2 : IsLineWithEnds s2 (⟨1, 0⟩ : ℂ) ⟨1, 1⟩ :=
    isLineWithEnds_segment (by intro h; have := congrArg Complex.im h; norm_num at this)
  have hline3 : IsLineWithEnds s3 (⟨1, 1⟩ : ℂ) ⟨0, 1⟩ :=
    isLineWithEnds_segment (by intro h; have := congrArg Complex.re h; norm_num at this)
  have h12_inter : s1 ∩ s2 = {⟨1, 0⟩} := by
    ext z
    simp only [mem_inter_iff, hs1_iff, hs2_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨-, him⟩, ⟨hre, -⟩⟩
      exact Complex.ext hre him
    · rintro rfl; norm_num
  have hline12 : IsLineWithEnds (s1 ∪ s2) (⟨0, 0⟩ : ℂ) ⟨1, 1⟩ :=
    hline1.union hline2 h12_inter
  have h123_inter : (s1 ∪ s2) ∩ s3 = {⟨1, 1⟩} := by
    ext z
    simp only [mem_inter_iff, mem_union, hs1_iff, hs2_iff, hs3_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨-, him0⟩ | ⟨hre1, -⟩, ⟨-, him1⟩⟩
      · linarith
      · exact Complex.ext hre1 him1
    · rintro rfl; exact ⟨Or.inr ⟨rfl, by norm_num⟩, ⟨by norm_num, rfl⟩⟩
  have hlineAQ : IsLineWithEnds A_Q (⟨0, 0⟩ : ℂ) ⟨0, 1⟩ :=
    hline12.union hline3 h123_inter
  have hAQ_eq : A_Q = s1 ∪ s2 ∪ s3 := rfl
  have hAQ_re0 : A_Q ∩ {w : ℂ | w.re = 0} = {⟨0, 0⟩, ⟨0, 1⟩} := by
    rw [hAQ_eq]
    ext z
    simp only [mem_inter_iff, mem_union, hs1_iff, hs2_iff, hs3_iff, mem_ofPred_eq,
      mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨(⟨-, him⟩ | ⟨hre, -⟩) | ⟨-, him⟩, hre0⟩
      · exact Or.inl (Complex.ext hre0 him)
      · linarith
      · exact Or.inr (Complex.ext hre0 him)
    · rintro (rfl | rfl)
      · exact ⟨Or.inl (Or.inl ⟨by norm_num, rfl⟩), rfl⟩
      · exact ⟨Or.inr ⟨by norm_num, rfl⟩, rfl⟩
  have hQAQ : Q \ A_Q = (Ioo (-1 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1) ∩ halfPlane := by
    rw [hAQ_eq]
    ext z
    simp only [Q, Set.mem_sdiff, mem_union, hs1_iff, hs2_iff, hs3_iff, mem_inter_iff,
      Complex.mem_reProdIm, mem_Icc, mem_Ioo, halfPlane, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨hre0, hre1⟩, ⟨him0, him1⟩⟩, hnot⟩
      have him0' : 0 < z.im := lt_of_le_of_ne him0 fun h =>
        hnot (Or.inl (Or.inl ⟨⟨hre0, hre1⟩, h.symm⟩))
      have hre1' : z.re < 1 := lt_of_le_of_ne hre1 fun h =>
        hnot (Or.inl (Or.inr ⟨h, ⟨him0, him1⟩⟩))
      have him1' : z.im < 1 := lt_of_le_of_ne him1 fun h =>
        hnot (Or.inr ⟨⟨hre0, hre1⟩, h⟩)
      exact ⟨⟨⟨by linarith, hre1'⟩, ⟨him0', him1'⟩⟩, hre0⟩
    · rintro ⟨⟨⟨_, hre1⟩, ⟨him0, him1⟩⟩, hre0⟩
      refine ⟨⟨⟨hre0, hre1.le⟩, ⟨him0.le, him1.le⟩⟩, ?_⟩
      rintro ((⟨-, him⟩ | ⟨hre, -⟩) | ⟨-, him⟩) <;> linarith
  have hwmid_mem : w_mid ∈ A_Q \ {⟨0, 0⟩, ⟨0, 1⟩} := by
    refine ⟨Or.inl (Or.inr ((hs2_iff w_mid).mpr ⟨rfl, by norm_num⟩)), ?_⟩
    rintro (h | h) <;> have := congrArg Complex.re h <;> norm_num [w_mid] at this
  have hseg_line : IsLineWithEnds seg_Q (⟨0, 0⟩ : ℂ) w_mid :=
    isLineWithEnds_segment (by intro h; have := congrArg Complex.re h; norm_num [w_mid] at this)
  have hseg_sub : seg_Q ⊆ Q := by
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    simp only [Q, Complex.mem_reProdIm, mem_Icc, Complex.add_re, Complex.add_im,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, w_mid]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hseg_int : seg_Q \ {⟨0, 0⟩, w_mid} ⊆ discInt Q := by
    rw [hQdiscInt]
    rintro z ⟨⟨a, b, ha, hb, hab, rfl⟩, hne⟩
    have hb0 : 0 < b := lt_of_le_of_ne hb fun h => by
      subst h
      have ha1 : a = 1 := by linarith
      subst ha1
      exact hne (Or.inl (by simp))
    have ha0 : 0 < a := lt_of_le_of_ne ha fun h => by
      subst h
      have hb1 : b = 1 := by linarith
      subst hb1
      exact hne (Or.inr (by simp))
    simp only [Complex.mem_reProdIm, mem_Ioo, Complex.add_re, Complex.add_im,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, w_mid]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  exact ⟨hQ, hQcomp, hAQ_sub, hlineAQ, hAQ_re0, hQAQ, hwmid_mem, hseg_line, hseg_sub, hseg_int⟩

/-- At an endpoint `s ∈ bd S` of a proper `I`-arc `F` (with other endpoint `t ≠ s`), inside any
open neighbourhood `W` of `s` avoiding `t`, there is a boundary closed disc `D ⊆ W` meeting `F`
only at `{s}`, with a separating proper `I`-arc `A ⊆ discBd D` (`IsOpen (D \ A)`), a midpoint
`y_mid ∈ A \ {s, t_D}`, and an arc `seg ⊆ D` from `s` to `y_mid` whose open interior lies in
`discInt D`. -/
theorem exists_shared_bd_half_disc {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {F : Set S} {s t : S}
    (hst : s ≠ t) (hFb : F ∩ bd S = {s, t}) (hFl : IsLineWithEnds F s t)
    {W : Set S} (hWopen : IsOpen W) (hsW : s ∈ W) (_htW : t ∉ W) :
    ∃ (D A seg : Set S) (t_D y_mid : S),
      IsClosedDisc D ∧ D ⊆ W ∧ D ∩ F = {s} ∧
      A ⊆ discBd D ∧ s ≠ t_D ∧ IsLineWithEnds A s t_D ∧ A ∩ bd S = {s, t_D} ∧
      IsOpen (D \ A) ∧
      y_mid ∈ A \ {s, t_D} ∧
      IsLineWithEnds seg s y_mid ∧ seg ⊆ D ∧ seg \ {s, y_mid} ⊆ discInt D ∧
      Disjoint (discInt D) (bd S) := by
  classical
  have ht2S : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  have hFcl : IsClosed F := hFl.isCompact.isClosed
  -- Step 1: Cut `S` along `F`.
  obtain ⟨Z, _, _, ψ, hZ, hψ, X, X', hP⟩ := exists_cut_arc hS hst hFb hFl
  have ht2Z : T2Space Z := hZ.2.1
  have hcZ : CompactSpace Z := hZ.1
  obtain ⟨x0, x1, y0, y1, l1, l2, hXX', hun, hbx, hbx', hψx0, hψy0, -, -⟩ := hP
  have hx0X : x0 ∈ X := by
    obtain ⟨f, hf0, -⟩ := l1
    exact hf0 ▸ (f 0).2
  have hx0bd : x0 ∈ bd Z := hψ.2.2.2.2 (hun ▸ Or.inl hx0X)
  have hX'cl : IsClosed X' := l2.isCompact.isClosed
  have hx0_nX' : x0 ∉ X' := fun h => Set.disjoint_left.mp hXX' hx0X h
  -- Step 2: Take a `SurfChart` `ch` at `x0` in `Z`, and intersect with `ψ ⁻¹' W \ X'`.
  obtain ⟨ch, hx0U⟩ := exists_surfChart (hZ.2.2 x0)
  let W0 : Set Z := ψ ⁻¹' W ∩ X'ᶜ ∩ ch.U
  have hW0_open : IsOpen W0 := ((hWopen.preimage hψ.1).inter hX'cl.isOpen_compl).inter ch.hU
  have hx0_W0 : x0 ∈ W0 := ⟨⟨by show ψ x0 ∈ W; rwa [hψx0], hx0_nX'⟩, hx0U⟩
  -- `ψ` is injective on `W0` because `W0 ∩ X' = ∅`.
  have hψ_inj_W0 : InjOn ψ W0 := fun u hu v hv huv => by
    by_cases huF : ψ u ∈ F
    · have hvF : ψ v ∈ F := huv ▸ huF
      have huX : u ∈ X := (hun ▸ huF : u ∈ X ∪ X').resolve_right hu.1.2
      have hvX : v ∈ X := (hun ▸ hvF : v ∈ X ∪ X').resolve_right hv.1.2
      exact hbx.2.1 huX hvX huv
    · have hvF : ψ v ∉ F := fun h => huF (huv.symm ▸ h)
      exact hψ.2.2.1 huF hvF huv
  -- Step 3: Find an initial segment `f_X '' [0, ε₀] ⊆ W0` of `X` and determine which side of
  -- `v₀ := (ch.j x0).im` it goes into!
  have hx0_re : (ch.j x0).re = 0 := (ch.mem_bd_iff hx0U).mp hx0bd
  let v₀ : ℝ := (ch.j x0).im
  have hch_x0 : ch.j x0 = ⟨0, v₀⟩ := Complex.ext hx0_re rfl
  have hXcl : IsClosed X := l1.isCompact.isClosed
  obtain ⟨fX, hfX0, hfX1⟩ := l1
  have hpre_W0 : IsOpen ((fun u : unitInterval => (fX u).1) ⁻¹' W0) :=
    hW0_open.preimage (continuous_subtype_val.comp fX.continuous)
  have h0_in : (0 : unitInterval) ∈ (fun u : unitInterval => (fX u).1) ⁻¹' W0 := by
    show (fX 0).1 ∈ W0; rwa [hfX0]
  obtain ⟨r_u, hr_u_pos, hr_u_ball⟩ := Metric.isOpen_iff.mp hpre_W0 0 h0_in
  let ε₀_val : ℝ := min (r_u / 2) (1 / 2)
  have hε₀_pos : 0 < ε₀_val := lt_min (by linarith) (by norm_num)
  have hε₀_lt1 : ε₀_val < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let ε₀ : unitInterval := ⟨ε₀_val, hε₀_pos.le, hε₀_lt1.le⟩
  have hfX_init_W0 : ∀ u : unitInterval, u ≤ ε₀ → (fX u).1 ∈ W0 := fun u hu => by
    apply hr_u_ball
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := u.2.1
    have huε : (u : ℝ) ≤ ε₀_val := hu
    have hεr : ε₀_val ≤ r_u / 2 := min_le_left _ _
    simp only [Set.Icc.coe_zero, sub_zero, abs_of_nonneg hu0]
    linarith
  -- Tail `T_X := fX '' [ε₀, 1]` is compact (closed) and does not contain `x0`.
  let T_X : Set Z := (fun u : unitInterval => (fX u).1) '' Icc ε₀ 1
  have hTX_cl : IsClosed T_X :=
    (isCompact_Icc.image (continuous_subtype_val.comp fX.continuous)).isClosed
  have hx0_nTX : x0 ∉ T_X := by
    rintro ⟨u, hu, hfu⟩
    have hu0 : u = 0 := fX.injective (Subtype.ext (hfu.trans hfX0.symm))
    have hle : ε₀_val ≤ (u : ℝ) := hu.1
    rw [hu0] at hle
    simp only [Set.Icc.coe_zero] at hle
    linarith
  -- Sign of `(ch.j (fX ε₀).1).im - v₀` is nonzero and constant on `(0, ε₀]`.
  let imX : ℝ → ℝ := fun τ => (ch.j (fX (projIcc (0 : ℝ) 1 zero_le_one τ)).1).im
  have himX_cont : ContinuousOn imX (Icc 0 ε₀_val) := by
    have hmap : ContinuousOn (fun τ : ℝ => (fX (projIcc (0 : ℝ) 1 zero_le_one τ)).1)
        (Icc 0 ε₀_val) :=
      (continuous_subtype_val.comp (fX.continuous.comp continuous_projIcc)).continuousOn
    have hsubU : MapsTo (fun τ : ℝ => (fX (projIcc (0 : ℝ) 1 zero_le_one τ)).1)
        (Icc 0 ε₀_val) ch.U := fun τ hτ => by
      have hτI : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans hε₀_lt1.le⟩
      have hproj : projIcc (0 : ℝ) 1 zero_le_one τ = ⟨τ, hτI⟩ :=
        projIcc_of_mem zero_le_one hτI
      have hle : projIcc (0 : ℝ) 1 zero_le_one τ ≤ ε₀ := by
        rw [hproj]; exact hτ.2
      exact (hfX_init_W0 _ hle).2
    exact Complex.continuous_im.comp_continuousOn (ch.hj.comp hmap hsubU)
  have himX_ne : ∀ τ ∈ Ioc (0 : ℝ) ε₀_val, imX τ ≠ v₀ := fun τ hτ heq => by
    have hτI : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1.le, hτ.2.trans hε₀_lt1.le⟩
    let u : unitInterval := ⟨τ, hτI⟩
    have hproj : projIcc (0 : ℝ) 1 zero_le_one τ = u := projIcc_of_mem zero_le_one hτI
    have huU : (fX u).1 ∈ ch.U := (hfX_init_W0 u hτ.2).2
    have hu_bd : (fX u).1 ∈ bd Z := hψ.2.2.2.2 (hun ▸ Or.inl (fX u).2)
    have hu_re : (ch.j (fX u).1).re = 0 := (ch.mem_bd_iff huU).mp hu_bd
    have hu_im : (ch.j (fX u).1).im = v₀ := by simpa [imX, hproj] using heq
    have hj_eq : ch.j (fX u).1 = ch.j x0 := Complex.ext (hu_re.trans hx0_re.symm) hu_im
    have hfx_eq : (fX u).1 = x0 := ch.injOn_j huU hx0U hj_eq
    have hu0 : u = 0 := fX.injective (Subtype.ext (hfx_eq.trans hfX0.symm))
    have : (u : ℝ) = 0 := congrArg Subtype.val hu0
    exact hτ.1.ne' this
  -- Choose `σ ∈ {1, -1}` pointing OPPOSITE to `imX ε₀_val - v₀`, so for all `u ∈ (0, ε₀]`,
  -- `σ * ((ch.j (fX u).1).im - v₀) < 0`!
  have hε₀_ne : imX ε₀_val ≠ v₀ := himX_ne ε₀_val ⟨hε₀_pos, le_rfl⟩
  let σ : ℝ := if v₀ < imX ε₀_val then -1 else 1
  have hσ_abs : σ = 1 ∨ σ = -1 := by dsimp only [σ]; split_ifs <;> simp
  have hσ_sq : σ * σ = 1 := by rcases hσ_abs with h | h <;> rw [h] <;> norm_num
  have hσ_ne : σ ≠ 0 := by rcases hσ_abs with h | h <;> rw [h] <;> norm_num
  have hσ_eps : σ * (imX ε₀_val - v₀) < 0 := by
    dsimp only [σ]
    split_ifs with hlt
    · linarith
    · have hgt : imX ε₀_val < v₀ := lt_of_le_of_ne (not_lt.mp hlt) hε₀_ne
      linarith
  have hσ_all : ∀ τ ∈ Ioc (0 : ℝ) ε₀_val, σ * (imX τ - v₀) < 0 := fun τ hτ => by
    by_contra hnot
    push Not at hnot
    have hpos : 0 < σ * (imX τ - v₀) := lt_of_le_of_ne hnot fun h0 => by
      have : imX τ - v₀ = 0 := (mul_eq_zero.mp h0.symm).resolve_left hσ_ne
      exact himX_ne τ hτ (sub_eq_zero.mp this)
    -- By IVT on `g(t) = σ * (imX t - v₀)` on `[τ, ε₀_val]`, some `t ∈ [τ, ε₀_val]` has `g(t) = 0`!
    have hg_cont : ContinuousOn (fun t => σ * (imX t - v₀)) (Icc τ ε₀_val) :=
      (continuousOn_const.mul ((himX_cont.mono (Icc_subset_Icc_left hτ.1.le)).sub continuousOn_const))
    have h0_mem : (0 : ℝ) ∈ Icc (σ * (imX ε₀_val - v₀)) (σ * (imX τ - v₀)) :=
      ⟨hσ_eps.le, hpos.le⟩
    obtain ⟨t', ht'I, ht'0⟩ := intermediate_value_Icc' hτ.2 hg_cont h0_mem
    have ht'_eq : imX t' = v₀ := sub_eq_zero.mp ((mul_eq_zero.mp ht'0).resolve_left hσ_ne)
    exact himX_ne t' ⟨lt_of_lt_of_le hτ.1 ht'I.1, ht'I.2⟩ ht'_eq
  -- Step 4: Shrink `δ > 0` so the affine image `α '' Q` lies in `ch.O ∩ halfPlane` and
  -- `ch.k '' (α '' Q) ⊆ W0 \ T_X`.
  let W1 : Set Z := W0 ∩ T_Xᶜ
  have hW1_open : IsOpen W1 := hW0_open.inter hTX_cl.isOpen_compl
  have hx0_W1 : x0 ∈ W1 := ⟨hx0_W0, hx0_nTX⟩
  have hcont_k : ContinuousWithinAt ch.k (ch.O ∩ halfPlane) (ch.j x0) := ch.hk (ch.j x0) (ch.hm hx0U)
  have hnhd_k : ch.k ⁻¹' W1 ∈ 𝓝[ch.O ∩ halfPlane] (ch.j x0) :=
    hcont_k (hW1_open.mem_nhds (by rwa [ch.hl hx0U]))
  rw [Metric.mem_nhdsWithin_iff] at hnhd_k
  obtain ⟨r1, hr1_pos, hr1_sub⟩ := hnhd_k
  obtain ⟨r2, hr2_pos, hr2_ball⟩ := Metric.isOpen_iff.mp ch.hO (ch.j x0) (ch.hm hx0U).1
  let δ : ℝ := min (r1 / 4) (r2 / 4)
  have hδ_pos : 0 < δ := lt_min (by linarith) (by linarith)
  -- Affine homeomorphism `α : ℂ ≃ₜ ℂ` mapping `Q = [0, 1] × [0, 1]` into `ball (ch.j x0) (min r1 r2) ∩ halfPlane`.
  let α_fun : ℂ → ℂ := fun z => ((δ * z.re : ℝ) : ℂ) + ((v₀ + σ * δ * z.im : ℝ) : ℂ) * Complex.I
  let α_inv : ℂ → ℂ := fun w => ((w.re / δ : ℝ) : ℂ) + ((σ * (w.im - v₀) / δ : ℝ) : ℂ) * Complex.I
  have hα_re : ∀ z, (α_fun z).re = δ * z.re := fun z => by
    simp [α_fun]
  have hα_im : ∀ z, (α_fun z).im = v₀ + σ * δ * z.im := fun z => by
    simp [α_fun]
  have hα_left : Function.LeftInverse α_inv α_fun := fun z => by
    apply Complex.ext
    · simp only [α_inv, hα_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      field_simp [hδ_pos.ne']
    · simp only [α_inv, hα_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      have : σ * (v₀ + σ * δ * z.im - v₀) / δ = (σ * σ) * δ * z.im / δ := by ring
      rw [this, hσ_sq, one_mul]; field_simp [hδ_pos.ne']
  have hα_right : Function.RightInverse α_inv α_fun := fun w => by
    apply Complex.ext
    · simp only [hα_re, α_inv, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      field_simp [hδ_pos.ne']
    · simp only [hα_im, α_inv, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      have : v₀ + σ * δ * (σ * (w.im - v₀) / δ) = v₀ + (σ * σ) * (w.im - v₀) * (δ / δ) := by ring
      rw [this, hσ_sq, div_self hδ_pos.ne']; ring
  let α : ℂ ≃ₜ ℂ :=
    { toFun := α_fun
      invFun := α_inv
      left_inv := hα_left
      right_inv := hα_right
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  obtain ⟨hQ, hQcomp, hAQ_sub, hAQ_line, hAQ_re0, hQAQ, hwmid_mem, hseg_line, hseg_sub, hseg_int⟩ :=
    unit_square_half_disc_data
  let Q : Set ℂ := Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1
  let A_Q : Set ℂ :=
    segment ℝ (⟨0, 0⟩ : ℂ) ⟨1, 0⟩ ∪ segment ℝ (⟨1, 0⟩ : ℂ) ⟨1, 1⟩ ∪
      segment ℝ (⟨1, 1⟩ : ℂ) ⟨0, 1⟩
  let w_mid : ℂ := ⟨1, 1 / 2⟩
  let seg_Q : Set ℂ := segment ℝ (⟨0, 0⟩ : ℂ) w_mid
  have hαQ_ball : ∀ z ∈ Q, dist (α z) (ch.j x0) < min r1 r2 := fun z hz => by
    rw [hch_x0, dist_eq_norm]
    have hre0 : 0 ≤ z.re := hz.1.1
    have hre1 : z.re ≤ 1 := hz.1.2
    have him0 : 0 ≤ z.im := hz.2.1
    have him1 : z.im ≤ 1 := hz.2.2
    have hsub : α z - ⟨0, v₀⟩ = ⟨δ * z.re, σ * δ * z.im⟩ := by
      apply Complex.ext
      · simp [α, hα_re]
      · simp [α, hα_im]
    rw [hsub]
    have hsq : ‖(⟨δ * z.re, σ * δ * z.im⟩ : ℂ)‖ ≤ 2 * δ := by
      rw [← Real.sqrt_sq (by linarith : 0 ≤ 2 * δ), Complex.norm_def, Complex.normSq_apply]
      apply Real.sqrt_le_sqrt
      have h1 : (δ * z.re) * (δ * z.re) ≤ δ * δ := by
        nlinarith [mul_nonneg hδ_pos.le hre0, mul_le_mul_of_nonneg_left hre1 hδ_pos.le]
      have h2 : (σ * δ * z.im) * (σ * δ * z.im) = (σ * σ) * (δ * z.im) * (δ * z.im) := by ring
      rw [h2, hσ_sq, one_mul]
      have h3 : (δ * z.im) * (δ * z.im) ≤ δ * δ := by
        nlinarith [mul_nonneg hδ_pos.le him0, mul_le_mul_of_nonneg_left him1 hδ_pos.le]
      nlinarith
    have h2δ : 2 * δ < min r1 r2 := by
      rw [lt_min_iff]
      exact ⟨by linarith [min_le_left (r1 / 4) (r2 / 4)], by linarith [min_le_right (r1 / 4) (r2 / 4)]⟩
    exact lt_of_le_of_lt hsq h2δ
  have hαQ_hp : ∀ z ∈ Q, α z ∈ ch.O ∩ halfPlane := fun z hz =>
    ⟨hr2_ball (by rw [Metric.mem_ball]; exact lt_of_lt_of_le (hαQ_ball z hz) (min_le_right _ _)),
     by show 0 ≤ (α z).re; rw [show (α z).re = δ * z.re from hα_re z]; exact mul_nonneg hδ_pos.le hz.1.1⟩
  have hkαQ_W1 : ∀ z ∈ Q, ch.k (α z) ∈ W1 := fun z hz =>
    hr1_sub ⟨by rw [Metric.mem_ball]; exact lt_of_lt_of_le (hαQ_ball z hz) (min_le_left _ _), hαQ_hp z hz⟩
  -- Composite map `g := ψ ∘ ch.k ∘ α : ℂ → S` is continuous and injective on `Q`.
  let g : ℂ → S := fun z => ψ (ch.k (α z))
  have hg_cont : ContinuousOn g Q :=
    hψ.1.comp_continuousOn ((ch.hk.comp α.continuous.continuousOn hαQ_hp))
  have hg_inj : InjOn g Q := fun z₁ hz₁ z₂ hz₂ h => by
    have hk1 : ch.k (α z₁) ∈ W0 := (hkαQ_W1 z₁ hz₁).1
    have hk2 : ch.k (α z₂) ∈ W0 := (hkαQ_W1 z₂ hz₂).1
    have heq_k : ch.k (α z₁) = ch.k (α z₂) := hψ_inj_W0 hk1 hk2 h
    have heq_α : α z₁ = α z₂ := ch.injOn_k (hαQ_hp z₁ hz₁) (hαQ_hp z₂ hz₂) heq_k
    exact α.injective heq_α
  have hg0 : g ⟨0, 0⟩ = s := by
    have hα0 : α ⟨0, 0⟩ = ch.j x0 := by
      apply Complex.ext
      · simp [α, hα_re, hch_x0]
      · simp [α, hα_im, hch_x0]
    simp only [g, hα0, ch.hl hx0U, hψx0]
  -- Key property: `g '' Q ∩ F = {s}`!
  have hgQ_F : g '' Q ∩ F = {s} := by
    ext p
    simp only [mem_inter_iff, mem_image, mem_singleton_iff]
    constructor
    · rintro ⟨⟨z, hzQ, rfl⟩, hgzF⟩
      have hkW1 : ch.k (α z) ∈ W1 := hkαQ_W1 z hzQ
      have hkX : ch.k (α z) ∈ X := (hun ▸ hgzF : ch.k (α z) ∈ X ∪ X').resolve_right hkW1.1.1.2
      let u : unitInterval := fX.symm ⟨ch.k (α z), hkX⟩
      have hfu : (fX u).1 = ch.k (α z) := congrArg Subtype.val (fX.apply_symm_apply ⟨_, hkX⟩)
      have hu_le : u ≤ ε₀ := by
        by_contra hgt
        push Not at hgt
        exact hkW1.2 ⟨u, ⟨hgt.le, u.2.2⟩, hfu⟩
      have hu0 : u = 0 := by
        by_contra hne0
        have hu_pos : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 fun h => hne0 (Subtype.ext h.symm)
        have hproj : projIcc (0 : ℝ) 1 zero_le_one (u : ℝ) = u := projIcc_of_mem zero_le_one u.2
        have hlt := hσ_all (u : ℝ) ⟨hu_pos, hu_le⟩
        have him_eq : imX (u : ℝ) = (α z).im := by
          dsimp only [imX]
          rw [hproj, hfu, ch.hr (hαQ_hp z hzQ)]
        rw [him_eq] at hlt
        have hαim : (α z).im - v₀ = σ * δ * z.im := by rw [show (α z).im = v₀ + σ * δ * z.im from hα_im z]; ring
        rw [hαim] at hlt
        have hnn : 0 ≤ σ * (σ * δ * z.im) := by
          have : σ * (σ * δ * z.im) = (σ * σ) * (δ * z.im) := by ring
          rw [this, hσ_sq, one_mul]
          exact mul_nonneg hδ_pos.le hzQ.2.1
        linarith
      change ψ (ch.k (α z)) = s
      rw [← hfu, hu0, hfX0, hψx0]
    · intro hp
      rw [hp]
      refine ⟨⟨⟨0, 0⟩, ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩, hg0⟩, ?_⟩
      exact (show s ∈ F ∩ bd S from hFb ▸ Or.inl rfl).1
  -- Homeomorphism `ψ` restricts to a homeomorphism between open sets `(X ∪ X')ᶜ` and `Fᶜ`.
  have hpre_iff : ∀ w : Z, ψ w ∈ F ↔ w ∈ X ∪ X' := fun w => by
    change w ∈ ψ ⁻¹' F ↔ w ∈ X ∪ X'
    rw [hun]
  have hψ_open_map : ∀ U : Set Z, IsOpen U → Disjoint U (X ∪ X') → IsOpen (ψ '' U) := fun U hU hdisj => by
    have hcomp_eq : ψ '' U = (ψ '' Uᶜ)ᶜ := by
      ext p
      simp only [mem_image, mem_compl_iff, not_exists, not_and]
      constructor
      · rintro ⟨z, hzU, rfl⟩ z' hz'U hzz'
        have hzF : ψ z ∉ F := fun h => Set.disjoint_left.mp hdisj hzU ((hpre_iff z).mp h)
        have hz'F : ψ z' ∉ F := fun h => hzF (hzz'.symm ▸ h)
        exact hz'U (hψ.2.2.1 hz'F hzF hzz' ▸ hzU)
      · intro h
        obtain ⟨z, rfl⟩ := hψ.2.1 p
        by_contra hnot
        exact h z (fun hzU => hnot ⟨z, hzU, rfl⟩) rfl
    rw [hcomp_eq]
    exact (hU.isClosed_compl.isCompact.image hψ.1).isClosed.isOpen_compl
  have hψ_bd_iff : ∀ z ∈ (X ∪ X')ᶜ, ψ z ∈ bd S ↔ z ∈ bd Z := fun z hzZ => by
    have hopenZ : IsOpen (X ∪ X')ᶜ := (hXcl.union hX'cl).isOpen_compl
    have hopenS : IsOpen Fᶜ := hFcl.isOpen_compl
    have hψzS : ψ z ∈ Fᶜ := fun h => hzZ ((hpre_iff z).mp h)
    let invFn : ↥Fᶜ → ↥(X ∪ X')ᶜ := fun p =>
      ⟨Classical.choose (hψ.2.1 p.1), fun h => p.2 (Classical.choose_spec (hψ.2.1 p.1) ▸ (hpre_iff _).mpr h)⟩
    let e_int : ↥(X ∪ X')ᶜ ≃ₜ ↥Fᶜ :=
      { toFun := fun w => ⟨ψ w.1, fun h => w.2 ((hpre_iff w.1).mp h)⟩
        invFun := invFn
        left_inv := fun w => by
          apply Subtype.ext
          have hw := Classical.choose_spec (hψ.2.1 (ψ w.1))
          have hwF : ψ (Classical.choose (hψ.2.1 (ψ w.1))) ∉ F := by
            rw [hw]; exact fun h => w.2 ((hpre_iff w.1).mp h)
          exact hψ.2.2.1 hwF (fun h => w.2 ((hpre_iff w.1).mp h)) hw
        right_inv := fun p => Subtype.ext (Classical.choose_spec (hψ.2.1 p.1))
        continuous_toFun := Continuous.subtype_mk (hψ.1.comp continuous_subtype_val) _
        continuous_invFun := by
          rw [continuous_def]
          intro V hV
          have hV_openZ : IsOpen (Subtype.val '' V : Set Z) := hopenZ.isOpenEmbedding_subtypeVal.isOpenMap V hV
          have hV_disj : Disjoint (Subtype.val '' V : Set Z) (X ∪ X') :=
            Set.disjoint_left.mpr (by rintro _ ⟨w, -, rfl⟩ hw; exact w.2 hw)
          have himg_open : IsOpen (ψ '' (Subtype.val '' V)) := hψ_open_map _ hV_openZ hV_disj
          have hpre_eq : invFn ⁻¹' V = Subtype.val ⁻¹' (ψ '' (Subtype.val '' V)) := by
            ext p
            simp only [mem_preimage, mem_image]
            constructor
            · intro hp
              exact ⟨(invFn p).1, ⟨invFn p, hp, rfl⟩, Classical.choose_spec (hψ.2.1 p.1)⟩
            · rintro ⟨w, ⟨w', hw'V, rfl⟩, hw_eq⟩
              have hw_eq' : (invFn p).1 = w'.1 := by
                have h1 := Classical.choose_spec (hψ.2.1 p.1)
                have hcF : ψ (invFn p).1 ∉ F := by show ψ (Classical.choose (hψ.2.1 p.1)) ∉ F; rw [h1]; exact p.2
                have hw'F : ψ w'.1 ∉ F := by rw [hw_eq]; exact p.2
                exact hψ.2.2.1 hcF hw'F (h1.trans hw_eq.symm)
              have hsub_eq : invFn p = w' := Subtype.ext hw_eq'
              rwa [hsub_eq]
          rw [hpre_eq]
          exact himg_open.preimage continuous_subtype_val }
    have h1 := isInteriorPoint_sub hopenZ (x := ⟨z, hzZ⟩)
    have h2 := isInteriorPoint_sub hopenS (x := ⟨ψ z, hψzS⟩)
    have h3 := isInteriorPoint_homeomorph_iff e_int ⟨z, hzZ⟩
    change ¬ IsInteriorPoint (ψ z) ↔ ¬ IsInteriorPoint z
    exact not_congr (h2.symm.trans (h3.trans h1))
  -- Build `D, A, seg, t_D, y_mid`!
  let D : Set S := g '' Q
  let A : Set S := g '' A_Q
  let seg : Set S := g '' seg_Q
  let t_D : S := g ⟨0, 1⟩
  let y_mid : S := g w_mid
  have hQ_ne : Nonempty ℂ := ⟨0⟩
  obtain ⟨hD, hDbd⟩ := isClosedDisc_image_injOn hQ hQcomp hg_cont hg_inj
  have hD_sub_W : D ⊆ W := by
    rintro _ ⟨z, hzQ, rfl⟩
    exact (hkαQ_W1 z hzQ).1.1.1
  have hA_sub_bd : A ⊆ discBd D := by
    rw [hDbd]; exact image_mono hAQ_sub
  have hst_D : s ≠ t_D := by
    rw [← hg0]
    intro h
    have h01 : (⟨0, 0⟩ : ℂ) = ⟨0, 1⟩ := hg_inj
      ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
      ⟨⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩⟩ h
    have := congrArg Complex.im h01
    norm_num at this
  have hAQ_subQ : A_Q ⊆ Q := hAQ_sub.trans (discBd_subset Q)
  have hA_line : IsLineWithEnds A s t_D := by
    rw [← hg0]
    exact hAQ_line.image_injOn (hg_cont.mono hAQ_subQ) (hg_inj.mono hAQ_subQ)
  -- For `z ∈ Q`: `g z ∈ bd S ↔ z.re = 0`.
  have hg_bd_iff : ∀ z ∈ Q, g z ∈ bd S ↔ z.re = 0 := fun z hzQ => by
    by_cases hz0 : z = ⟨0, 0⟩
    · subst hz0
      rw [hg0]
      exact ⟨fun _ => rfl, fun _ => (show s ∈ F ∩ bd S from hFb ▸ Or.inl rfl).2⟩
    · have hgz_nF : g z ∉ F := fun h => by
        have hgs : g z = s := by
          have : g z ∈ ({s} : Set S) := hgQ_F ▸ ⟨⟨z, hzQ, rfl⟩, h⟩
          exact this
        exact hz0 (hg_inj hzQ ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩ (hgs.trans hg0.symm))
      have hk_nXX : ch.k (α z) ∈ (X ∪ X')ᶜ := fun h => hgz_nF ((hpre_iff _).mpr h)
      rw [show g z = ψ (ch.k (α z)) from rfl, hψ_bd_iff _ hk_nXX,
        ch.mem_bd_iff (hkαQ_W1 z hzQ).1.2, ch.hr (hαQ_hp z hzQ), show (α z).re = δ * z.re from hα_re z]
      exact mul_eq_zero.trans (or_iff_right hδ_pos.ne')
  have hA_bd : A ∩ bd S = {s, t_D} := by
    ext p
    simp only [A, mem_inter_iff, mem_image, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨⟨z, hzA, rfl⟩, hzbd⟩
      have hzre : z.re = 0 := (hg_bd_iff z (hAQ_subQ hzA)).mp hzbd
      have hz01 : z ∈ ({⟨0, 0⟩, ⟨0, 1⟩} : Set ℂ) := hAQ_re0 ▸ ⟨hzA, hzre⟩
      rcases hz01 with rfl | rfl
      · exact Or.inl hg0
      · exact Or.inr rfl
    · rintro (hp | hp)
      · rw [hp]
        have h0A : (⟨0, 0⟩ : ℂ) ∈ A_Q := by
          have hmem : (⟨0, 0⟩ : ℂ) ∈ A_Q ∩ {w : ℂ | w.re = 0} := hAQ_re0.symm ▸ Or.inl rfl
          exact hmem.1
        exact ⟨⟨⟨0, 0⟩, h0A, hg0⟩, (show s ∈ F ∩ bd S from hFb ▸ Or.inl rfl).2⟩
      · rw [hp]
        have h1A : (⟨0, 1⟩ : ℂ) ∈ A_Q := by
          have hmem : (⟨0, 1⟩ : ℂ) ∈ A_Q ∩ {w : ℂ | w.re = 0} := hAQ_re0.symm ▸ Or.inr rfl
          exact hmem.1
        exact ⟨⟨⟨0, 1⟩, h1A, rfl⟩,
          (hg_bd_iff ⟨0, 1⟩ ⟨⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩⟩).mpr rfl⟩
  have hD_diff_A_open : IsOpen (D \ A) := by
    have heq : D \ A = g '' (Q \ A_Q) := by
      ext p
      simp only [D, A, Set.mem_sdiff, mem_image]
      constructor
      · rintro ⟨⟨z, hzQ, rfl⟩, hnot⟩
        exact ⟨z, ⟨hzQ, fun hzA => hnot ⟨z, hzA, rfl⟩⟩, rfl⟩
      · rintro ⟨z, ⟨hzQ, hzA⟩, rfl⟩
        exact ⟨⟨z, hzQ, rfl⟩, fun ⟨z', hz'A, he⟩ =>
          hzA (hg_inj hzQ (hAQ_subQ hz'A) he.symm ▸ hz'A)⟩
    rw [heq]
    have hQAQ_eq : g '' (Q \ A_Q) = ψ '' (ch.k '' (α '' (Q \ A_Q))) := by
      rw [image_image, image_image]
    rw [hQAQ_eq]
    have hU_open_Z : IsOpen (ch.k '' (α '' (Q \ A_Q))) := by
      -- `α '' (Q \ A_Q) = (α '' (Ioo (-1) 1 ×ℂ Ioo 0 1)) ∩ halfPlane`
      let O_open : Set ℂ := α '' (Ioo (-1 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1)
      have hO_open : IsOpen O_open :=
        α.isOpenMap _ ((isOpen_Ioo.preimage Complex.continuous_re).inter
          (isOpen_Ioo.preimage Complex.continuous_im))
      have himg_eq : α '' (Q \ A_Q) = O_open ∩ halfPlane := by
        rw [hQAQ]
        ext w
        simp only [O_open, mem_image, mem_inter_iff, halfPlane, mem_ofPred_eq]
        constructor
        · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
          exact ⟨⟨z, hz1, rfl⟩, by rw [show (α z).re = δ * z.re from hα_re z]; exact mul_nonneg hδ_pos.le hz2⟩
        · rintro ⟨⟨z, hz1, rfl⟩, hw_hp⟩
          refine ⟨z, ⟨hz1, ?_⟩, rfl⟩
          have : 0 ≤ δ * z.re := by rwa [show (α z).re = δ * z.re from hα_re z] at hw_hp
          exact nonneg_of_mul_nonneg_right this hδ_pos
      have hsub_chO : O_open ∩ halfPlane ⊆ ch.O ∩ halfPlane := by
        rw [← himg_eq]
        rintro _ ⟨z, hz, rfl⟩
        exact hαQ_hp z hz.1
      have hk_eq : ch.k '' (α '' (Q \ A_Q)) = ch.U ∩ ch.j ⁻¹' O_open := by
        rw [himg_eq]
        ext x
        constructor
        · rintro ⟨w, hw, rfl⟩
          refine ⟨ch.hk' (hsub_chO hw), ?_⟩
          show ch.j (ch.k w) ∈ O_open
          rw [ch.hr (hsub_chO hw)]
          exact hw.1
        · rintro ⟨hxU, hxj⟩
          refine ⟨ch.j x, ⟨hxj, (ch.hm hxU).2⟩, ch.hl hxU⟩
      rw [hk_eq, isOpen_iff_mem_nhds]
      intro x hx
      have hca : ContinuousAt ch.j x := ch.hj.continuousAt (ch.hU.mem_nhds hx.1)
      exact Filter.inter_mem (ch.hU.mem_nhds hx.1) (hca (hO_open.mem_nhds hx.2))
    have hU_disj : Disjoint (ch.k '' (α '' (Q \ A_Q))) (X ∪ X') := by
      rw [Set.disjoint_left]
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ hmem
      have hgzF : g z ∈ F := (hpre_iff _).mpr hmem
      have hgs : g z = s := by
        have : g z ∈ ({s} : Set S) := hgQ_F ▸ ⟨⟨z, hz.1, rfl⟩, hgzF⟩
        exact this
      have hz0 : z = ⟨0, 0⟩ := hg_inj hz.1 ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩
        (hgs.trans hg0.symm)
      have h0A : (⟨0, 0⟩ : ℂ) ∈ A_Q := by
        have hmem' : (⟨0, 0⟩ : ℂ) ∈ A_Q ∩ {w : ℂ | w.re = 0} := hAQ_re0.symm ▸ Or.inl rfl
        exact hmem'.1
      exact hz.2 (hz0.symm ▸ h0A)
    exact hψ_open_map _ hU_open_Z hU_disj
  have hymid_A : y_mid ∈ A \ {s, t_D} := by
    refine ⟨⟨w_mid, hwmid_mem.1, rfl⟩, ?_⟩
    rintro (h | h)
    · exact hwmid_mem.2 (Or.inl (hg_inj (hAQ_subQ hwmid_mem.1)
        ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩ (h.trans hg0.symm)))
    · exact hwmid_mem.2 (Or.inr (hg_inj (hAQ_subQ hwmid_mem.1)
        ⟨⟨le_rfl, zero_le_one⟩, ⟨zero_le_one, le_rfl⟩⟩ h))
  have hseg_line_S : IsLineWithEnds seg s y_mid := by
    rw [← hg0]
    exact hseg_line.image_injOn (hg_cont.mono hseg_sub) (hg_inj.mono hseg_sub)
  have hseg_sub_D : seg ⊆ D := image_mono hseg_sub
  have hseg_int_D : seg \ {s, y_mid} ⊆ discInt D := by
    rintro p ⟨⟨z, hzseg, rfl⟩, hne⟩
    have hz_ne : z ∈ seg_Q \ {⟨0, 0⟩, w_mid} := ⟨hzseg, by
      rintro (rfl | rfl)
      · exact hne (Or.inl hg0)
      · exact hne (Or.inr rfl)⟩
    have hz_intQ : z ∈ discInt Q := hseg_int hz_ne
    refine ⟨⟨z, hz_intQ.1, rfl⟩, ?_⟩
    rw [hDbd]
    rintro ⟨z', hz'bd, he⟩
    exact hz_intQ.2 (hg_inj hz_intQ.1 (discBd_subset Q hz'bd) he.symm ▸ hz'bd)
  have hDint_disj_bd : Disjoint (discInt D) (bd S) := by
    rw [Set.disjoint_left]
    rintro p ⟨⟨z, hzQ, rfl⟩, hznb⟩ hbd
    have hzre : z.re = 0 := (hg_bd_iff z hzQ).mp hbd
    apply hznb
    rw [hDbd]
    refine ⟨z, ?_, rfl⟩
    have hQfr : discBd Q = Q \ (Ioo (0 : ℝ) 1 ×ℂ Ioo (0 : ℝ) 1) := by
      have h1 := (isClosedDisc_rect (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num)).2
      rw [h1, hQcomp.isClosed.frontier_eq, Complex.interior_reProdIm, interior_Icc]
    rw [hQfr]
    exact ⟨hzQ, fun h => by linarith [h.1.1]⟩
  exact ⟨D, A, seg, t_D, y_mid, hD, hD_sub_W, hgQ_F, hA_sub_bd, hst_D, hA_line, hA_bd,
    hD_diff_A_open, hymid_A, hseg_line_S, hseg_sub_D, hseg_int_D, hDint_disj_bd⟩

/-! ### Section 3: Radial star construction inside a closed disc (`exists_star_in_disc`) -/

/-- A ray from an interior point `w₀ ∈ ball 0 1` meets `sphere 0 1` at a unique point. -/
private theorem unit_circle_ray_unique {w₀ z₁ z₂ : ℂ} (hw₀ : ‖w₀‖ < 1)
    (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (heq : w₀ + (t₁ : ℂ) * (z₁ - w₀) = w₀ + (t₂ : ℂ) * (z₂ - w₀)) : z₁ = z₂ := by
  have h1 : (t₁ : ℂ) * (z₁ - w₀) = (t₂ : ℂ) * (z₂ - w₀) := add_left_cancel heq
  let c : ℝ := t₁ / t₂
  have hc_pos : 0 < c := div_pos ht₁ ht₂
  let d : ℂ := z₁ - w₀
  have hd_ne : d ≠ 0 := fun h => by
    have : z₁ = w₀ := sub_eq_zero.mp h
    rw [this] at hz₁; linarith
  have hz₂_eq : z₂ = w₀ + (c : ℂ) * d := by
    have h2 : z₂ - w₀ = (c : ℂ) * d := by
      have ht2_ne : (t₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₂.ne'
      apply mul_left_cancel₀ ht2_ne
      rw [← h1]
      dsimp only [c, d]
      push_cast
      field_simp [ht2_ne]
    linear_combination h2
  have hz₁_eq : z₁ = w₀ + d := by simp [d]
  have hn_w₀ : Complex.normSq w₀ < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w₀]
  have hn_d : 0 < Complex.normSq d := Complex.normSq_pos.mpr hd_ne
  have hn_z1 : Complex.normSq (w₀ + d) = 1 := by
    rw [← hz₁_eq, Complex.normSq_eq_norm_sq, hz₁]; norm_num
  have hn_z2 : Complex.normSq (w₀ + (c : ℂ) * d) = 1 := by
    rw [← hz₂_eq, Complex.normSq_eq_norm_sq, hz₂]; norm_num
  have hexp1 : Complex.normSq (w₀ + d) =
      Complex.normSq w₀ + 2 * (w₀.re * d.re + w₀.im * d.im) + Complex.normSq d := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]; ring
  have hexp2 : Complex.normSq (w₀ + (c : ℂ) * d) =
      Complex.normSq w₀ + 2 * c * (w₀.re * d.re + w₀.im * d.im) + c ^ 2 * Complex.normSq d := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [hexp1] at hn_z1
  rw [hexp2] at hn_z2
  have hfactor : (c - 1) * ((1 - Complex.normSq w₀) + c * Complex.normSq d) = 0 := by
    nlinarith
  have hpos_fac : 0 < (1 - Complex.normSq w₀) + c * Complex.normSq d := by nlinarith
  have hc1 : c = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hpos_fac.ne')
  rw [hz₂_eq, hc1, Complex.ofReal_one, one_mul, hz₁_eq]

/-- Inside a closed disc `D_sub`, given an interior point `p ∈ discInt D_sub \ G_U` (with `G_U`
closed) and `r` distinct boundary points `q : Fin r → S` on `discBd D_sub`, builds a tiny closed
disc `Δ ⊆ discInt D_sub \ G_U` containing `p` in its interior, together with radial star arcs
`ray i = R_in i ∪ L i` from `p` to `q i`, where `R_in i ⊆ Δ` and `L i` are pairwise disjoint
proper `I`-arcs in `D_sub \ discInt Δ`. -/
theorem exists_star_in_disc {S : Type} [TopologicalSpace S] [T2Space S]
    {D_sub G_U : Set S} (hD : IsClosedDisc D_sub) (hGU_cl : IsClosed G_U)
    {p : S} (hp_int : p ∈ discInt D_sub) (hp_nG : p ∉ G_U)
    {r : ℕ} {q : Fin r → S} (hq_bd : ∀ i, q i ∈ discBd D_sub) (hq_inj : Function.Injective q) :
    ∃ (Δ : Set S) (R_in L ray : Fin r → Set S) (u : Fin r → S),
      IsClosedDisc Δ ∧ Δ ⊆ discInt D_sub ∧ Disjoint Δ G_U ∧ p ∈ discInt Δ ∧
      (∀ i, R_in i ⊆ Δ ∧ IsLineWithEnds (R_in i) p (u i) ∧ R_in i ∩ discBd Δ = {u i}) ∧
      (∀ i, L i ⊆ D_sub \ discInt Δ ∧ u i ≠ q i ∧ IsLineWithEnds (L i) (u i) (q i) ∧
        L i ∩ (discBd D_sub ∪ discBd Δ) = {u i, q i}) ∧
      (∀ i, ray i = R_in i ∪ L i ∧ p ≠ q i ∧ IsLineWithEnds (ray i) p (q i) ∧
        ray i ⊆ D_sub ∧ ray i \ {q i} ⊆ discInt D_sub) ∧
      (Pairwise fun i j => ray i ∩ ray j = {p}) ∧
      (Pairwise fun i j => Disjoint (L i) (L j)) := by
  classical
  obtain ⟨h, g, hc⟩ := hD.exists_isChart
  have hg_bd_iff : ∀ z ∈ closedBall (0 : ℂ) 1, g z ∈ discBd D_sub ↔ ‖z‖ = 1 := fun z hz => by
    rw [← hc.g_sphere]
    constructor
    · rintro ⟨w, hw, he⟩
      have hzw : w = z := hc.injOn (Metric.sphere_subset_closedBall hw) hz he
      subst hzw
      simpa [Metric.mem_sphere] using hw
    · intro hnorm
      exact ⟨z, by simpa [Metric.mem_sphere] using hnorm, rfl⟩
  let w₀ : ℂ := h p
  have hw₀_cl1 : w₀ ∈ closedBall (0 : ℂ) 1 := hc.hm hp_int.1
  have hgw₀ : g w₀ = p := hc.gh hp_int.1
  have hw₀_lt1 : ‖w₀‖ < 1 := by
    have hle : ‖w₀‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hw₀_cl1
    refine lt_of_le_of_ne hle fun heq => hp_int.2 ?_
    rw [← hgw₀]
    exact (hg_bd_iff w₀ hw₀_cl1).mpr heq
  -- Choose `ρ > 0` with `ρ < (1 - ‖w₀‖) / 2` and `g '' closedBall w₀ ρ ⊆ G_Uᶜ`.
  have hnhd_nG : g ⁻¹' G_Uᶜ ∈ 𝓝[closedBall (0 : ℂ) 1] w₀ :=
    hc.gc w₀ hw₀_cl1 (hGU_cl.isOpen_compl.mem_nhds (by rwa [hgw₀]))
  rw [Metric.mem_nhdsWithin_iff] at hnhd_nG
  obtain ⟨rG, hrG_pos, hrG_sub⟩ := hnhd_nG
  let ρ : ℝ := min ((1 - ‖w₀‖) / 2) (rG / 2)
  have hρ_pos : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρ_lt_dist : ρ < 1 - ‖w₀‖ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρ_lt_rG : ρ < rG := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  -- Closed ball `B := closedBall w₀ ρ ⊆ ball 0 1`.
  let B : Set ℂ := Metric.closedBall w₀ ρ
  have hB_sub_ball1 : B ⊆ Metric.ball (0 : ℂ) 1 := fun z hz => by
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖z - w₀‖ ≤ ρ := by simpa [B, dist_eq_norm] using hz
    calc ‖z‖ = ‖(z - w₀) + w₀‖ := by ring_nf
      _ ≤ ‖z - w₀‖ + ‖w₀‖ := norm_add_le _ _
      _ ≤ ρ + ‖w₀‖ := by linarith
      _ < 1 := by linarith
  have hB_sub_cl1 : B ⊆ closedBall (0 : ℂ) 1 := hB_sub_ball1.trans Metric.ball_subset_closedBall
  let Δ : Set S := g '' B
  have hB_disc := isClosedDisc_closedBall_of_pos w₀ hρ_pos
  have hC_ne : Nonempty ℂ := ⟨0⟩
  obtain ⟨hΔ, hΔbd⟩ := isClosedDisc_image_injOn hB_disc.1 (isCompact_closedBall w₀ ρ)
    (hc.gc.mono hB_sub_cl1) (hc.injOn.mono hB_sub_cl1)
  have hΔbd_sphere : discBd Δ = g '' Metric.sphere w₀ ρ := by
    rw [hΔbd, hB_disc.2]
  have hΔ_sub_int : Δ ⊆ discInt D_sub := by
    rintro _ ⟨z, hzB, rfl⟩
    have hz1 : z ∈ closedBall (0 : ℂ) 1 := hB_sub_cl1 hzB
    refine ⟨hc.gm hz1, ?_⟩
    rw [hg_bd_iff z hz1]
    have hz_lt : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hB_sub_ball1 hzB
    exact hz_lt.ne
  have hΔ_disj_G : Disjoint Δ G_U := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hzB, rfl⟩ hzG
    have hz1 : z ∈ closedBall (0 : ℂ) 1 := hB_sub_cl1 hzB
    have hz_ball : z ∈ Metric.ball w₀ rG := by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hzB) hρ_lt_rG
    exact hrG_sub ⟨hz_ball, hz1⟩ hzG
  have hp_in_Δint : p ∈ discInt Δ := by
    refine ⟨⟨w₀, Metric.mem_closedBall_self hρ_pos.le, hgw₀⟩, ?_⟩
    rw [hΔbd_sphere]
    rintro ⟨z, hzsp, he⟩
    have hzw : z = w₀ := hc.injOn (hB_sub_cl1 (Metric.sphere_subset_closedBall hzsp)) hw₀_cl1
      (he.trans hgw₀.symm)
    rw [hzw, Metric.mem_sphere, dist_self] at hzsp
    linarith
  -- Boundary coordinates `z_q i ∈ sphere 0 1` for each `q i ∈ discBd D_sub`.
  let z_q : Fin r → ℂ := fun i => h (q i)
  have hz_q_sphere : ∀ i, z_q i ∈ Metric.sphere (0 : ℂ) 1 := fun i => by
    rw [← hc.bd]; exact ⟨q i, hq_bd i, rfl⟩
  have hz_q_cl1 : ∀ i, z_q i ∈ closedBall (0 : ℂ) 1 := fun i =>
    Metric.sphere_subset_closedBall (hz_q_sphere i)
  have hz_q_norm : ∀ i, ‖z_q i‖ = 1 := fun i => by
    simpa [Metric.mem_sphere] using hz_q_sphere i
  have hgz_q : ∀ i, g (z_q i) = q i := fun i => hc.gh (discBd_subset D_sub (hq_bd i))
  have hz_q_inj : Function.Injective z_q := fun i j hij =>
    hq_inj (by rw [← hgz_q i, ← hgz_q j, hij])
  have hz_q_dist : ∀ i, ρ < ‖z_q i - w₀‖ := fun i => by
    have htri : ‖z_q i‖ ≤ ‖z_q i - w₀‖ + ‖w₀‖ := by
      calc ‖z_q i‖ = ‖(z_q i - w₀) + w₀‖ := by ring_nf
        _ ≤ ‖z_q i - w₀‖ + ‖w₀‖ := norm_add_le _ _
    rw [hz_q_norm i] at htri
    linarith
  -- Split point `u_c i := w₀ + (ρ / ‖z_q i - w₀‖) • (z_q i - w₀)` on `sphere w₀ ρ`.
  let τ_u : Fin r → ℝ := fun i => ρ / ‖z_q i - w₀‖
  have hτ_pos : ∀ i, 0 < τ_u i := fun i => div_pos hρ_pos (lt_trans hρ_pos (hz_q_dist i))
  have hτ_lt1 : ∀ i, τ_u i < 1 := fun i =>
    (div_lt_one (lt_trans hρ_pos (hz_q_dist i))).mpr (hz_q_dist i)
  let u_c : Fin r → ℂ := fun i => w₀ + ((τ_u i : ℝ) : ℂ) * (z_q i - w₀)
  have hu_c_sphere : ∀ i, u_c i ∈ Metric.sphere w₀ ρ := fun i => by
    rw [Metric.mem_sphere, dist_eq_norm]
    have hsub : u_c i - w₀ = ((τ_u i : ℝ) : ℂ) * (z_q i - w₀) := by simp [u_c]
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hτ_pos i).le]
    dsimp only [τ_u]
    have hne : ‖z_q i - w₀‖ ≠ 0 := (lt_trans hρ_pos (hz_q_dist i)).ne'
    field_simp [hne]
  have hu_c_mem_cl1 : ∀ i, u_c i ∈ closedBall (0 : ℂ) 1 := fun i =>
    hB_sub_cl1 (Metric.sphere_subset_closedBall (hu_c_sphere i))
  let R_in_c : Fin r → Set ℂ := fun i => segment ℝ w₀ (u_c i)
  let L_c : Fin r → Set ℂ := fun i => segment ℝ (u_c i) (z_q i)
  let ray_c : Fin r → Set ℂ := fun i => segment ℝ w₀ (z_q i)
  -- Basic complex segment facts for `R_in_c`, `L_c`, `ray_c`.
  have hR_sub_B : ∀ i, R_in_c i ⊆ B := fun i =>
    (convex_closedBall w₀ ρ).segment_subset (Metric.mem_closedBall_self hρ_pos.le)
      (Metric.sphere_subset_closedBall (hu_c_sphere i))
  have hray_sub_cl1 : ∀ i, ray_c i ⊆ closedBall (0 : ℂ) 1 := fun i =>
    (convex_closedBall (0 : ℂ) 1).segment_subset hw₀_cl1 (hz_q_cl1 i)
  have hL_sub_cl1 : ∀ i, L_c i ⊆ closedBall (0 : ℂ) 1 := fun i =>
    (convex_closedBall (0 : ℂ) 1).segment_subset (hu_c_mem_cl1 i) (hz_q_cl1 i)
  have hray_param : ∀ i (z : ℂ), z ∈ ray_c i ↔
      ∃ t ∈ Icc (0 : ℝ) 1, z = w₀ + (t : ℂ) * (z_q i - w₀) := fun i z => by
    constructor
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      refine ⟨b, ⟨hb, by linarith⟩, ?_⟩
      have ha_eq : (a : ℂ) = 1 - (b : ℂ) := by exact_mod_cast (show a = 1 - b by linarith)
      simp only [Complex.real_smul, ha_eq]; ring
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
      simp only [Complex.real_smul]; push_cast; ring
  have hR_param : ∀ i (z : ℂ), z ∈ R_in_c i ↔
      ∃ t ∈ Icc (0 : ℝ) (τ_u i), z = w₀ + (t : ℂ) * (z_q i - w₀) := fun i z => by
    constructor
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      refine ⟨b * τ_u i, ⟨mul_nonneg hb (hτ_pos i).le, by nlinarith [hτ_pos i]⟩, ?_⟩
      have ha_eq : (a : ℂ) = 1 - (b : ℂ) := by exact_mod_cast (show a = 1 - b by linarith)
      simp only [u_c, Complex.real_smul, ha_eq]; push_cast; ring
    · rintro ⟨t, ⟨ht0, htτ⟩, rfl⟩
      let s_p : ℝ := t / τ_u i
      have hs0 : 0 ≤ s_p := div_nonneg ht0 (hτ_pos i).le
      have hs1 : s_p ≤ 1 := (div_le_one (hτ_pos i)).mpr htτ
      refine ⟨1 - s_p, s_p, by linarith, hs0, by ring, ?_⟩
      have hsτ : s_p * τ_u i = t := div_mul_cancel₀ t (hτ_pos i).ne'
      simp only [u_c, Complex.real_smul]
      have h1 : ((s_p : ℂ) * (τ_u i : ℂ)) = (t : ℂ) := by exact_mod_cast hsτ
      calc ((1 - s_p : ℝ) : ℂ) * w₀ + (s_p : ℂ) * (w₀ + (τ_u i : ℂ) * (z_q i - w₀))
          = w₀ + ((s_p : ℂ) * (τ_u i : ℂ)) * (z_q i - w₀) := by push_cast; ring
        _ = w₀ + (t : ℂ) * (z_q i - w₀) := by rw [h1]
  have hL_param : ∀ i (z : ℂ), z ∈ L_c i ↔
      ∃ t ∈ Icc (τ_u i) 1, z = w₀ + (t : ℂ) * (z_q i - w₀) := fun i z => by
    constructor
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      refine ⟨a * τ_u i + b, ⟨by nlinarith [hτ_lt1 i], by nlinarith [hτ_lt1 i]⟩, ?_⟩
      have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
      simp only [u_c, Complex.real_smul]; push_cast
      calc (a : ℂ) * (w₀ + (τ_u i : ℂ) * (z_q i - w₀)) + (b : ℂ) * z_q i
          = ((a : ℂ) + (b : ℂ)) * w₀ + ((a : ℂ) * (τ_u i : ℂ) + (b : ℂ)) * (z_q i - w₀) := by ring
        _ = w₀ + ((a : ℂ) * (τ_u i : ℂ) + (b : ℂ)) * (z_q i - w₀) := by rw [hab', one_mul]
    · rintro ⟨t, ⟨htτ, ht1⟩, rfl⟩
      let denom : ℝ := 1 - τ_u i
      have hden_pos : 0 < denom := by linarith [hτ_lt1 i]
      let b : ℝ := (t - τ_u i) / denom
      have hb0 : 0 ≤ b := div_nonneg (by linarith) hden_pos.le
      have hb1 : b ≤ 1 := (div_le_one hden_pos).mpr (by linarith)
      refine ⟨1 - b, b, by linarith, hb0, by ring, ?_⟩
      have hcomb : (1 - b) * τ_u i + b = t := by
        have hne : 1 - τ_u i ≠ 0 := hden_pos.ne'
        dsimp only [b, denom]; field_simp [hne]; ring
      have hcomb_c : ((1 - b : ℝ) : ℂ) * (τ_u i : ℂ) + (b : ℂ) = (t : ℂ) := by
        exact_mod_cast hcomb
      simp only [u_c, Complex.real_smul]
      calc ((1 - b : ℝ) : ℂ) * (w₀ + (τ_u i : ℂ) * (z_q i - w₀)) + (b : ℂ) * z_q i
          = (((1 - b : ℝ) : ℂ) + (b : ℂ)) * w₀ +
              (((1 - b : ℝ) : ℂ) * (τ_u i : ℂ) + (b : ℂ)) * (z_q i - w₀) := by ring
        _ = w₀ + (t : ℂ) * (z_q i - w₀) := by
            rw [hcomb_c]; push_cast; ring
  have hray_eq_union : ∀ i, ray_c i = R_in_c i ∪ L_c i := fun i => by
    ext z
    simp only [mem_union, hray_param, hR_param, hL_param]
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      by_cases h : t ≤ τ_u i
      · exact Or.inl ⟨t, ⟨ht0, h⟩, rfl⟩
      · exact Or.inr ⟨t, ⟨le_of_not_ge h, ht1⟩, rfl⟩
    · rintro (⟨t, ⟨ht0, htτ⟩, rfl⟩ | ⟨t, ⟨htτ, ht1⟩, rfl⟩)
      · exact ⟨t, ⟨ht0, htτ.trans (hτ_lt1 i).le⟩, rfl⟩
      · exact ⟨t, ⟨(hτ_pos i).le.trans htτ, ht1⟩, rfl⟩
  -- Norm of `w₀ + t * (z_q i - w₀)`: `< 1` for `t ∈ [0, 1)`, distance from `w₀` is `t * ‖z_q i - w₀‖`.
  have hdist_param : ∀ i (t : ℝ), 0 ≤ t →
      dist (w₀ + (t : ℂ) * (z_q i - w₀)) w₀ = t * ‖z_q i - w₀‖ := fun i t ht => by
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
  have hnorm_lt1_param : ∀ i (t : ℝ), 0 ≤ t → t < 1 →
      ‖w₀ + (t : ℂ) * (z_q i - w₀)‖ < 1 := fun i t ht0 ht1 => by
    have hrew : w₀ + (t : ℂ) * (z_q i - w₀) = ((1 - t : ℝ) : ℂ) * w₀ + (t : ℂ) * z_q i := by
      push_cast; ring
    rw [hrew]
    calc ‖((1 - t : ℝ) : ℂ) * w₀ + (t : ℂ) * z_q i‖
        ≤ ‖((1 - t : ℝ) : ℂ) * w₀‖ + ‖(t : ℂ) * z_q i‖ := norm_add_le _ _
      _ = (1 - t) * ‖w₀‖ + t * ‖z_q i‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht0]
      _ < (1 - t) * 1 + t * 1 := by rw [hz_q_norm i]; nlinarith
      _ = 1 := by ring
  -- Define the image arcs in `S`!
  let R_in : Fin r → Set S := fun i => g '' R_in_c i
  let L : Fin r → Set S := fun i => g '' L_c i
  let ray : Fin r → Set S := fun i => g '' ray_c i
  let u : Fin r → S := fun i => g (u_c i)
  refine ⟨Δ, R_in, L, ray, u, hΔ, hΔ_sub_int, hΔ_disj_G, hp_in_Δint, ?_, ?_, ?_, ?_, ?_⟩
  · -- Properties of `R_in i`
    intro i
    have hne_wu : w₀ ≠ u_c i := fun h => by
      have hs := hu_c_sphere i
      rw [← h, Metric.mem_sphere, dist_self] at hs
      linarith
    refine ⟨image_mono (hR_sub_B i), ?_, ?_⟩
    · rw [← hgw₀]
      exact (isLineWithEnds_segment hne_wu).image_injOn
        (hc.gc.mono ((hR_sub_B i).trans hB_sub_cl1)) (hc.injOn.mono ((hR_sub_B i).trans hB_sub_cl1))
    · rw [hΔbd_sphere]
      ext x
      simp only [R_in, u, mem_inter_iff, mem_image, mem_singleton_iff]
      constructor
      · rintro ⟨⟨z, hzR, rfl⟩, ⟨z', hz'sp, he⟩⟩
        have hzz' : z = z' := hc.injOn (hB_sub_cl1 (hR_sub_B i hzR))
          (hB_sub_cl1 (Metric.sphere_subset_closedBall hz'sp)) he.symm
        subst hzz'
        obtain ⟨t, ⟨ht0, htτ⟩, rfl⟩ := (hR_param i z).mp hzR
        have hd : t * ‖z_q i - w₀‖ = ρ := by
          rw [← hdist_param i t ht0]; exact Metric.mem_sphere.mp hz'sp
        have ht_eq : t = τ_u i := by
          dsimp only [τ_u]
          have hne : ‖z_q i - w₀‖ ≠ 0 := (lt_trans hρ_pos (hz_q_dist i)).ne'
          field_simp [hne]; linarith
        rw [ht_eq]
      · rintro rfl
        exact ⟨⟨u_c i, right_mem_segment _ _ _, rfl⟩, ⟨u_c i, hu_c_sphere i, rfl⟩⟩
  · -- Properties of `L i`
    intro i
    have hne_uz : u_c i ≠ z_q i := fun h => by
      have h1 := Metric.mem_sphere.mp (hu_c_sphere i)
      rw [h, dist_eq_norm] at h1
      linarith [hz_q_dist i]
    refine ⟨?_, fun h => hne_uz (hc.injOn (hu_c_mem_cl1 i) (hz_q_cl1 i) (by rw [hgz_q i]; exact h)), ?_, ?_⟩
    · rintro _ ⟨z, hzL, rfl⟩
      obtain ⟨t, ⟨htτ, ht1⟩, rfl⟩ := (hL_param i z).mp hzL
      have hz1 : w₀ + (t : ℂ) * (z_q i - w₀) ∈ closedBall (0 : ℂ) 1 := hL_sub_cl1 i hzL
      refine ⟨hc.gm hz1, ?_⟩
      rintro ⟨⟨z', hz'B, he⟩, hnb⟩
      have hzz' : w₀ + (t : ℂ) * (z_q i - w₀) = z' := hc.injOn hz1 (hB_sub_cl1 hz'B) he.symm
      have hd_ge : ρ ≤ dist (w₀ + (t : ℂ) * (z_q i - w₀)) w₀ := by
        rw [hdist_param i t ((hτ_pos i).le.trans htτ)]
        have hne : 0 < ‖z_q i - w₀‖ := lt_trans hρ_pos (hz_q_dist i)
        have : τ_u i * ‖z_q i - w₀‖ = ρ := div_mul_cancel₀ ρ hne.ne'
        nlinarith
      have hd_le : dist z' w₀ ≤ ρ := Metric.mem_closedBall.mp hz'B
      rw [hzz'] at hd_ge
      have hd_eq : dist z' w₀ = ρ := le_antisymm hd_le hd_ge
      apply hnb
      rw [hΔbd_sphere]
      exact ⟨z', Metric.mem_sphere.mpr hd_eq, he⟩
    · rw [← hgz_q i]
      exact (isLineWithEnds_segment hne_uz).image_injOn
        (hc.gc.mono (hL_sub_cl1 i)) (hc.injOn.mono (hL_sub_cl1 i))
    · ext x
      simp only [L, u, mem_inter_iff, mem_union, mem_image, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨⟨z, hzL, rfl⟩, hbd | hΔb⟩
        · obtain ⟨t, ⟨htτ, ht1⟩, rfl⟩ := (hL_param i z).mp hzL
          have ht_eq : t = 1 := by
            by_contra hne1
            have hlt : ‖w₀ + (t : ℂ) * (z_q i - w₀)‖ < 1 :=
              hnorm_lt1_param i t ((hτ_pos i).le.trans htτ) (lt_of_le_of_ne ht1 hne1)
            have hz1 : w₀ + (t : ℂ) * (z_q i - w₀) ∈ closedBall (0 : ℂ) 1 := hL_sub_cl1 i hzL
            rw [hg_bd_iff _ hz1] at hbd
            linarith
          subst ht_eq
          right
          have : w₀ + ((1 : ℝ) : ℂ) * (z_q i - w₀) = z_q i := by simp
          rw [this, hgz_q i]
        · rw [hΔbd_sphere] at hΔb
          obtain ⟨z', hz'sp, he⟩ := hΔb
          have hzz' : z = z' := hc.injOn (hL_sub_cl1 i hzL)
            (hB_sub_cl1 (Metric.sphere_subset_closedBall hz'sp)) he.symm
          subst hzz'
          obtain ⟨t, ⟨htτ, ht1⟩, rfl⟩ := (hL_param i z).mp hzL
          have hd : t * ‖z_q i - w₀‖ = ρ := by
            rw [← hdist_param i t ((hτ_pos i).le.trans htτ)]; exact Metric.mem_sphere.mp hz'sp
          have ht_eq : t = τ_u i := by
            dsimp only [τ_u]
            have hne : ‖z_q i - w₀‖ ≠ 0 := (lt_trans hρ_pos (hz_q_dist i)).ne'
            field_simp [hne]; linarith
          left; rw [ht_eq]
      · rintro (rfl | rfl)
        · exact ⟨⟨u_c i, left_mem_segment _ _ _, rfl⟩, Or.inr (hΔbd_sphere ▸ ⟨u_c i, hu_c_sphere i, rfl⟩)⟩
        · exact ⟨⟨z_q i, right_mem_segment _ _ _, hgz_q i⟩, Or.inl (hq_bd i)⟩
  · -- Properties of `ray i`
    intro i
    have hne_wz : w₀ ≠ z_q i := fun h => by
      have := hz_q_norm i; rw [← h] at this; linarith
    refine ⟨by simp only [ray, R_in, L, ← image_union, hray_eq_union i],
      fun h => hne_wz (hc.injOn hw₀_cl1 (hz_q_cl1 i) (hgw₀.trans (h.trans (hgz_q i).symm))), ?_, ?_, ?_⟩
    · rw [← hgw₀, ← hgz_q i]
      exact (isLineWithEnds_segment hne_wz).image_injOn
        (hc.gc.mono (hray_sub_cl1 i)) (hc.injOn.mono (hray_sub_cl1 i))
    · rintro _ ⟨z, hz, rfl⟩
      exact hc.gm (hray_sub_cl1 i hz)
    · rintro _ ⟨⟨z, hz, rfl⟩, hne⟩
      obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := (hray_param i z).mp hz
      have ht_lt1 : t < 1 := lt_of_le_of_ne ht1 fun h => by
        subst h
        have : w₀ + ((1 : ℝ) : ℂ) * (z_q i - w₀) = z_q i := by simp
        exact hne (by rw [this, hgz_q i]; rfl)
      have hz1 : w₀ + (t : ℂ) * (z_q i - w₀) ∈ closedBall (0 : ℂ) 1 := hray_sub_cl1 i hz
      refine ⟨hc.gm hz1, ?_⟩
      rw [hg_bd_iff _ hz1]
      exact (hnorm_lt1_param i t ht0 ht_lt1).ne
  · -- Pairwise `ray i ∩ ray j = {p}`
    intro i j hij
    ext x
    simp only [ray, mem_inter_iff, mem_image, mem_singleton_iff]
    constructor
    · rintro ⟨⟨z₁, hz₁, rfl⟩, ⟨z₂, hz₂, he⟩⟩
      have h12 : z₁ = z₂ := hc.injOn (hray_sub_cl1 i hz₁) (hray_sub_cl1 j hz₂) he.symm
      subst h12
      obtain ⟨t₁, ⟨ht10, _⟩, htz1⟩ := (hray_param i z₁).mp hz₁
      obtain ⟨t₂, ⟨ht20, _⟩, htz2⟩ := (hray_param j z₁).mp hz₂
      by_cases ht1 : t₁ = 0
      · subst ht1; simp only [Complex.ofReal_zero, zero_mul, add_zero] at htz1
        rw [htz1, hgw₀]
      · have ht1p : 0 < t₁ := lt_of_le_of_ne ht10 (Ne.symm ht1)
        by_cases ht2 : t₂ = 0
        · subst ht2; simp only [Complex.ofReal_zero, zero_mul, add_zero] at htz2
          rw [htz2, hgw₀]
        · have ht2p : 0 < t₂ := lt_of_le_of_ne ht20 (Ne.symm ht2)
          have hzq := unit_circle_ray_unique hw₀_lt1 (hz_q_norm i) (hz_q_norm j) ht1p ht2p
            (htz1.symm.trans htz2)
          exact (hij (hz_q_inj hzq)).elim
    · rintro rfl
      exact ⟨⟨w₀, left_mem_segment _ _ _, hgw₀⟩, ⟨w₀, left_mem_segment _ _ _, hgw₀⟩⟩
  · -- Pairwise `Disjoint (L i) (L j)`
    intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, he⟩
    have h12 : z₁ = z₂ := hc.injOn (hL_sub_cl1 i hz₁) (hL_sub_cl1 j hz₂) he.symm
    subst h12
    obtain ⟨t₁, ⟨ht1τ, _⟩, htz1⟩ := (hL_param i z₁).mp hz₁
    obtain ⟨t₂, ⟨ht2τ, _⟩, htz2⟩ := (hL_param j z₁).mp hz₂
    have hzq := unit_circle_ray_unique hw₀_lt1 (hz_q_norm i) (hz_q_norm j)
      (lt_of_lt_of_le (hτ_pos i) ht1τ) (lt_of_lt_of_le (hτ_pos j) ht2τ) (htz1.symm.trans htz2)
    exact hij (hz_q_inj hzq)

/-! ### Section 4: Drawing constructor from arcs and acyclicity of star forests -/

/-- Build a `Drawing S` from a finite vertex set `V` and a finite family of `I`-arcs
`E_arc : Fin m → Set S` whose open interiors `E_arc i \ {a i, b i}` are pairwise disjoint and
disjoint from `V`. -/
noncomputable def drawing_of_arcs {S : Type} [TopologicalSpace S] [T2Space S]
    {V : Set S} (hVfin : V.Finite)
    {m : ℕ} {E_arc : Fin m → Set S} {a b : Fin m → S}
    (hab : ∀ i, a i ≠ b i)
    (_haV : ∀ i, a i ∈ V) (_hbV : ∀ i, b i ∈ V)
    (hE_line : ∀ i, IsLineWithEnds (E_arc i) (a i) (b i))
    (hE_capV : ∀ i, E_arc i ∩ V = {a i, b i})
    (hE_disj : Pairwise fun i j => Disjoint (E_arc i \ {a i, b i}) (E_arc j \ {a j, b j})) :
    Drawing S where
  U := V ∪ ⋃ i : Fin m, E_arc i
  V := V
  V_subset_U := subset_union_left
  isClosed_U := hVfin.isClosed.union (isClosed_iUnion_of_finite fun i => (hE_line i).isCompact.isClosed)
  finite_V := hVfin
  finite_edges := by
    have hdiff : (V ∪ ⋃ i : Fin m, E_arc i) \ V = ⋃ i : Fin m, (E_arc i \ {a i, b i}) := by
      ext z
      simp only [Set.mem_sdiff, mem_union, mem_iUnion]
      constructor
      · rintro ⟨hzV | ⟨i, hzi⟩, hznV⟩
        · exact (hznV hzV).elim
        · exact ⟨i, hzi, fun h => hznV (hE_capV i ▸ h).2⟩
      · rintro ⟨i, hzi, hzn⟩
        exact ⟨Or.inr ⟨i, hzi⟩, fun hzV => hzn (hE_capV i ▸ ⟨hzi, hzV⟩)⟩
    have he_pc : ∀ i, IsPathConnected (E_arc i \ {a i, b i}) := fun i => by
      obtain ⟨f, hf0, hf1⟩ := hE_line i
      let J : Set unitInterval := {u : unitInterval | 0 < (u : ℝ) ∧ (u : ℝ) < 1}
      have hJ_pc : IsPathConnected J := by
        refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, fun u hu => ?_⟩
        refine ⟨⟨⟨fun τ => ⟨(1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ),
          by nlinarith [τ.2.1, τ.2.2, u.2.1, u.2.2], by nlinarith [τ.2.1, τ.2.2, u.2.1, u.2.2]⟩,
          Continuous.subtype_mk (by fun_prop) _⟩,
          by ext; simp, by ext; simp⟩, fun τ => ?_⟩
        show 0 < (1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ) ∧
          (1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ) < 1
        have hτ0 : 0 ≤ (τ : ℝ) := τ.2.1
        have hτ1 : (τ : ℝ) ≤ 1 := τ.2.2
        have hu1 : 0 < (u : ℝ) := hu.1
        have hu2 : (u : ℝ) < 1 := hu.2
        rcases eq_or_lt_of_le hτ0 with h0 | h0
        · rw [← h0]; norm_num
        · exact ⟨by nlinarith, by nlinarith⟩
      have himg : (fun u : unitInterval => (f u).1) '' J = E_arc i \ {a i, b i} := by
        ext z
        constructor
        · rintro ⟨u, hu, rfl⟩
          refine ⟨(f u).2, ?_⟩
          rintro (h | h)
          · exact hu.1.ne' (congrArg Subtype.val (f.injective (Subtype.ext (h.trans hf0.symm))))
          · exact hu.2.ne (congrArg Subtype.val (f.injective (Subtype.ext (h.trans hf1.symm))))
        · rintro ⟨hz, hzst⟩
          let u := f.symm ⟨z, hz⟩
          have hu0 : u ≠ 0 := fun h => hzst (Or.inl (by
            have : f u = f 0 := congrArg f h
            simpa [u, hf0] using congrArg Subtype.val this))
          have hu1 : u ≠ 1 := fun h => hzst (Or.inr (by
            have : f u = f 1 := congrArg f h
            simpa [u, hf1] using congrArg Subtype.val this))
          refine ⟨u, ⟨lt_of_le_of_ne u.2.1 fun h => hu0 (Subtype.ext h.symm),
            lt_of_le_of_ne u.2.2 fun h => hu1 (Subtype.ext h)⟩, ?_⟩
          exact congrArg Subtype.val (f.apply_symm_apply ⟨z, hz⟩)
      rw [← himg]
      exact hJ_pc.image (continuous_subtype_val.comp f.continuous)
    have hE_eq : arcComponentsIn ((V ∪ ⋃ i : Fin m, E_arc i) \ V) ⊆
        range (fun i : Fin m => E_arc i \ {a i, b i}) := by
      intro C hC
      obtain ⟨x, hxC⟩ := hC.1
      have hx_diff : x ∈ ⋃ i : Fin m, (E_arc i \ {a i, b i}) := hdiff ▸ hC.2.1 hxC
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx_diff
      refine ⟨i, ?_⟩
      -- Show `C = E_arc i \ {a i, b i}`: `C ⊆ E_arc i \ {a i, b i}` because `E_arc i \ {a i, b i}` is
      -- clopen in `(V ∪ ⋃ E_arc) \ V`!
      have hC_sub_i : C ⊆ E_arc i \ {a i, b i} := fun y hyC => by
        obtain ⟨γ, hγ⟩ := hC.2.2.1.joinedIn x hxC y hyC
        -- `γ ⁻¹' (E_arc i \ {a i, b i})` is clopen in `unitInterval` and contains `0`.
        let A_cl : Set unitInterval := γ ⁻¹' E_arc i
        let B_cl : Set unitInterval := γ ⁻¹' (⋃ j ∈ ({j : Fin m | j ≠ i} : Set (Fin m)), E_arc j)
        have hA_cl : IsClosed A_cl := (hE_line i).isCompact.isClosed.preimage γ.continuous
        have hB_cl : IsClosed B_cl :=
          (Set.toFinite _ |>.isClosed_biUnion fun j _ => (hE_line j).isCompact.isClosed).preimage
            γ.continuous
        have hcov : A_cl ∪ B_cl = univ := by
          ext τ
          simp only [A_cl, B_cl, mem_union, mem_preimage, mem_iUnion, mem_univ, iff_true]
          have hτ := hdiff ▸ hC.2.1 (hγ τ)
          obtain ⟨j, hj⟩ := mem_iUnion.mp hτ
          by_cases hji : j = i
          · exact Or.inl (hji ▸ hj.1)
          · exact Or.inr ⟨j, hji, hj.1⟩
        have hdisj : Disjoint A_cl B_cl := by
          rw [Set.disjoint_left]
          intro τ h1 h2
          obtain ⟨j, hji, hj⟩ := mem_iUnion₂.mp h2
          have hτ := hdiff ▸ hC.2.1 (hγ τ)
          have hznV : γ τ ∉ V := (hC.2.1 (hγ τ)).2
          have h1' : γ τ ∈ E_arc i \ {a i, b i} := ⟨h1, fun h => hznV (hE_capV i ▸ h).2⟩
          have h2' : γ τ ∈ E_arc j \ {a j, b j} := ⟨hj, fun h => hznV (hE_capV j ▸ h).2⟩
          exact Set.disjoint_left.mp (hE_disj (Ne.symm hji)) h1' h2'
        have hA_clopen : IsClopen A_cl := ⟨hA_cl, by
          have : A_cl = B_clᶜ := by
            ext τ; simp only [mem_compl_iff]
            exact ⟨fun h1 h2 => Set.disjoint_left.mp hdisj h1 h2,
              fun h2 => ((mem_union _ _ _).mp (hcov.symm ▸ mem_univ τ)).resolve_right h2⟩
          rw [this]; exact hB_cl.isOpen_compl⟩
        have h0A : (0 : unitInterval) ∈ A_cl := by show γ 0 ∈ E_arc i; rw [γ.source]; exact hxi.1
        have hA_univ : A_cl = univ := by
          rcases (connectedSpace_iff_clopen.mp inferInstance).2 A_cl hA_clopen with h0 | h1
          · exact ((Set.eq_empty_iff_forall_notMem.mp h0 0) h0A).elim
          · exact h1
        have h1A : γ 1 ∈ E_arc i := by
          have : (1 : unitInterval) ∈ A_cl := hA_univ.symm ▸ mem_univ (1 : unitInterval)
          exact this
        rw [γ.target] at h1A
        exact ⟨h1A, fun h => (hC.2.1 hyC).2 (hE_capV i ▸ h).2⟩
      have hi_sub : E_arc i \ {a i, b i} ⊆ (V ∪ ⋃ j : Fin m, E_arc j) \ V := by
        rw [hdiff]; exact subset_iUnion (fun i => E_arc i \ {a i, b i}) i
      exact hC.2.2.2 _ hi_sub (he_pc i) hC_sub_i
    exact (Set.finite_range _).subset hE_eq
  edge_cond := by
    have hdiff : (V ∪ ⋃ i : Fin m, E_arc i) \ V = ⋃ i : Fin m, (E_arc i \ {a i, b i}) := by
      ext z
      simp only [Set.mem_sdiff, mem_union, mem_iUnion]
      constructor
      · rintro ⟨hzV | ⟨i, hzi⟩, hznV⟩
        · exact (hznV hzV).elim
        · exact ⟨i, hzi, fun h => hznV (hE_capV i ▸ h).2⟩
      · rintro ⟨i, hzi, hzn⟩
        exact ⟨Or.inr ⟨i, hzi⟩, fun hzV => hzn (hE_capV i ▸ ⟨hzi, hzV⟩)⟩
    intro e he
    obtain ⟨x, hxe⟩ := he.1
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hdiff ▸ he.2.1 hxe)
    have he_pc : IsPathConnected (E_arc i \ {a i, b i}) := by
      obtain ⟨f, hf0, hf1⟩ := hE_line i
      let J : Set unitInterval := {u : unitInterval | 0 < (u : ℝ) ∧ (u : ℝ) < 1}
      have hJ_pc : IsPathConnected J := by
        refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, fun u hu => ?_⟩
        refine ⟨⟨⟨fun τ => ⟨(1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ),
          by nlinarith [τ.2.1, τ.2.2, u.2.1, u.2.2], by nlinarith [τ.2.1, τ.2.2, u.2.1, u.2.2]⟩,
          Continuous.subtype_mk (by fun_prop) _⟩,
          by ext; simp, by ext; simp⟩, fun τ => ?_⟩
        show 0 < (1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ) ∧
          (1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ) < 1
        have hτ0 : 0 ≤ (τ : ℝ) := τ.2.1
        have hτ1 : (τ : ℝ) ≤ 1 := τ.2.2
        have hu1 : 0 < (u : ℝ) := hu.1
        have hu2 : (u : ℝ) < 1 := hu.2
        rcases eq_or_lt_of_le hτ0 with h0 | h0
        · rw [← h0]; norm_num
        · exact ⟨by nlinarith, by nlinarith⟩
      have himg : (fun u : unitInterval => (f u).1) '' J = E_arc i \ {a i, b i} := by
        ext z
        constructor
        · rintro ⟨u, hu, rfl⟩
          refine ⟨(f u).2, ?_⟩
          rintro (h | h)
          · exact hu.1.ne' (congrArg Subtype.val (f.injective (Subtype.ext (h.trans hf0.symm))))
          · exact hu.2.ne (congrArg Subtype.val (f.injective (Subtype.ext (h.trans hf1.symm))))
        · rintro ⟨hz, hzst⟩
          let u := f.symm ⟨z, hz⟩
          have hu0 : u ≠ 0 := fun h => hzst (Or.inl (by
            have : f u = f 0 := congrArg f h
            simpa [u, hf0] using congrArg Subtype.val this))
          have hu1 : u ≠ 1 := fun h => hzst (Or.inr (by
            have : f u = f 1 := congrArg f h
            simpa [u, hf1] using congrArg Subtype.val this))
          refine ⟨u, ⟨lt_of_le_of_ne u.2.1 fun h => hu0 (Subtype.ext h.symm),
            lt_of_le_of_ne u.2.2 fun h => hu1 (Subtype.ext h)⟩, ?_⟩
          exact congrArg Subtype.val (f.apply_symm_apply ⟨z, hz⟩)
      rw [← himg]
      exact hJ_pc.image (continuous_subtype_val.comp f.continuous)
    have he_eq : e = E_arc i \ {a i, b i} := by
      have hsub_i : e ⊆ E_arc i \ {a i, b i} := fun y hy => by
        obtain ⟨γ, hγ⟩ := he.2.2.1.joinedIn x hxe y hy
        let A_cl : Set unitInterval := γ ⁻¹' E_arc i
        let B_cl : Set unitInterval := γ ⁻¹' (⋃ j ∈ ({j : Fin m | j ≠ i} : Set (Fin m)), E_arc j)
        have hA_cl : IsClosed A_cl := (hE_line i).isCompact.isClosed.preimage γ.continuous
        have hB_cl : IsClosed B_cl :=
          (Set.toFinite _ |>.isClosed_biUnion fun j _ => (hE_line j).isCompact.isClosed).preimage
            γ.continuous
        have hcov : A_cl ∪ B_cl = univ := by
          ext τ
          simp only [A_cl, B_cl, mem_union, mem_preimage, mem_iUnion, mem_univ, iff_true]
          obtain ⟨j, hj⟩ := mem_iUnion.mp (hdiff ▸ he.2.1 (hγ τ))
          by_cases hji : j = i
          · exact Or.inl (hji ▸ hj.1)
          · exact Or.inr ⟨j, hji, hj.1⟩
        have hdisj : Disjoint A_cl B_cl := by
          rw [Set.disjoint_left]
          intro τ h1 h2
          obtain ⟨j, hji, hj⟩ := mem_iUnion₂.mp h2
          have hznV : γ τ ∉ V := (he.2.1 (hγ τ)).2
          exact Set.disjoint_left.mp (hE_disj (Ne.symm hji))
            ⟨h1, fun h => hznV (hE_capV i ▸ h).2⟩ ⟨hj, fun h => hznV (hE_capV j ▸ h).2⟩
        have hA_clopen : IsClopen A_cl := ⟨hA_cl, by
          have : A_cl = B_clᶜ := by
            ext τ; simp only [mem_compl_iff]
            exact ⟨fun h1 h2 => Set.disjoint_left.mp hdisj h1 h2,
              fun h2 => ((mem_union _ _ _).mp (hcov.symm ▸ mem_univ τ)).resolve_right h2⟩
          rw [this]; exact hB_cl.isOpen_compl⟩
        have h0A : (0 : unitInterval) ∈ A_cl := by show γ 0 ∈ E_arc i; rw [γ.source]; exact hxi.1
        have hA_univ : A_cl = univ := by
          rcases (connectedSpace_iff_clopen.mp inferInstance).2 A_cl hA_clopen with h0 | h1
          · exact ((Set.eq_empty_iff_forall_notMem.mp h0 0) h0A).elim
          · exact h1
        have h1A : γ 1 ∈ E_arc i := by
          have : (1 : unitInterval) ∈ A_cl := hA_univ.symm ▸ mem_univ (1 : unitInterval)
          exact this
        rw [γ.target] at h1A
        exact ⟨h1A, fun h => (he.2.1 hy).2 (hE_capV i ▸ h).2⟩
      exact (he.2.2.2 _ (hdiff.symm ▸ subset_iUnion (fun i => E_arc i \ {a i, b i}) i) he_pc hsub_i).symm
    have hcl_e : closure e = E_arc i := by
      rw [he_eq]
      exact Subset.antisymm (closure_minimal sdiff_subset (hE_line i).isCompact.isClosed)
        (hE_line i).subset_closure_diff
    left
    exact ⟨a i, b i, hab i, by rw [hcl_e, hE_capV i], by rw [hcl_e]; exact hE_line i⟩

/-- Characterization of the edges and closures of `drawing_of_arcs`. -/
theorem drawing_of_arcs_E {S : Type} [TopologicalSpace S] [T2Space S]
    {V : Set S} (hVfin : V.Finite)
    {m : ℕ} {E_arc : Fin m → Set S} {a b : Fin m → S}
    (hab : ∀ i, a i ≠ b i)
    (haV : ∀ i, a i ∈ V) (hbV : ∀ i, b i ∈ V)
    (hE_line : ∀ i, IsLineWithEnds (E_arc i) (a i) (b i))
    (hE_capV : ∀ i, E_arc i ∩ V = {a i, b i})
    (hE_disj : Pairwise fun i j => Disjoint (E_arc i \ {a i, b i}) (E_arc j \ {a j, b j})) :
    let H := drawing_of_arcs hVfin hab haV hbV hE_line hE_capV hE_disj
    H.E = range (fun i : Fin m => E_arc i \ {a i, b i}) ∧
      ∀ i, closure (E_arc i \ {a i, b i}) = E_arc i := by
  intro H
  have hcl_i : ∀ i, closure (E_arc i \ {a i, b i}) = E_arc i := fun i =>
    Subset.antisymm (closure_minimal sdiff_subset (hE_line i).isCompact.isClosed)
      (hE_line i).subset_closure_diff
  refine ⟨?_, hcl_i⟩
  have hdiff : H.U \ H.V = ⋃ i : Fin m, (E_arc i \ {a i, b i}) := by
    ext z
    simp only [H, drawing_of_arcs, Set.mem_sdiff, mem_union, mem_iUnion]
    constructor
    · rintro ⟨hzV | ⟨i, hzi⟩, hznV⟩
      · exact (hznV hzV).elim
      · exact ⟨i, hzi, fun h => hznV (hE_capV i ▸ h).2⟩
    · rintro ⟨i, hzi, hzn⟩
      exact ⟨Or.inr ⟨i, hzi⟩, fun hzV => hzn (hE_capV i ▸ ⟨hzi, hzV⟩)⟩
  have he_pc : ∀ i, IsPathConnected (E_arc i \ {a i, b i}) := fun i => by
    obtain ⟨f, hf0, hf1⟩ := hE_line i
    let J : Set unitInterval := {u : unitInterval | 0 < (u : ℝ) ∧ (u : ℝ) < 1}
    have hJ_pc : IsPathConnected J := by
      refine ⟨⟨1 / 2, by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, fun u hu => ?_⟩
      refine ⟨⟨⟨fun τ => ⟨(1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ),
        by nlinarith [τ.2.1, τ.2.2, u.2.1, u.2.2], by nlinarith [τ.2.1, τ.2.2, u.2.1, u.2.2]⟩,
        Continuous.subtype_mk (by fun_prop) _⟩,
        by ext; simp, by ext; simp⟩, fun τ => ?_⟩
      show 0 < (1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ) ∧
        (1 - (τ : ℝ)) * (1 / 2) + (τ : ℝ) * (u : ℝ) < 1
      have hτ0 : 0 ≤ (τ : ℝ) := τ.2.1
      have hτ1 : (τ : ℝ) ≤ 1 := τ.2.2
      have hu1 : 0 < (u : ℝ) := hu.1
      have hu2 : (u : ℝ) < 1 := hu.2
      rcases eq_or_lt_of_le hτ0 with h0 | h0
      · rw [← h0]; norm_num
      · exact ⟨by nlinarith, by nlinarith⟩
    have himg : (fun u : unitInterval => (f u).1) '' J = E_arc i \ {a i, b i} := by
      ext z
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨(f u).2, ?_⟩
        rintro (h | h)
        · exact hu.1.ne' (congrArg Subtype.val (f.injective (Subtype.ext (h.trans hf0.symm))))
        · exact hu.2.ne (congrArg Subtype.val (f.injective (Subtype.ext (h.trans hf1.symm))))
      · rintro ⟨hz, hzst⟩
        let u := f.symm ⟨z, hz⟩
        have hu0 : u ≠ 0 := fun h => hzst (Or.inl (by
          have : f u = f 0 := congrArg f h
          simpa [u, hf0] using congrArg Subtype.val this))
        have hu1 : u ≠ 1 := fun h => hzst (Or.inr (by
          have : f u = f 1 := congrArg f h
          simpa [u, hf1] using congrArg Subtype.val this))
        refine ⟨u, ⟨lt_of_le_of_ne u.2.1 fun h => hu0 (Subtype.ext h.symm),
          lt_of_le_of_ne u.2.2 fun h => hu1 (Subtype.ext h)⟩, ?_⟩
        exact congrArg Subtype.val (f.apply_symm_apply ⟨z, hz⟩)
    rw [← himg]
    exact hJ_pc.image (continuous_subtype_val.comp f.continuous)
  have hclopen_sub : ∀ (D : Set S) (i : Fin m), D ⊆ H.U \ H.V → IsPathConnected D →
      (D ∩ (E_arc i \ {a i, b i})).Nonempty → D ⊆ E_arc i \ {a i, b i} := fun D i hDsub hDpc ⟨x, hxD, hxi⟩ y hyD => by
    obtain ⟨γ, hγ⟩ := hDpc.joinedIn x hxD y hyD
    let A_cl : Set unitInterval := γ ⁻¹' E_arc i
    let B_cl : Set unitInterval := γ ⁻¹' (⋃ j ∈ ({j : Fin m | j ≠ i} : Set (Fin m)), E_arc j)
    have hA_cl : IsClosed A_cl := (hE_line i).isCompact.isClosed.preimage γ.continuous
    have hB_cl : IsClosed B_cl :=
      (Set.toFinite _ |>.isClosed_biUnion fun j _ => (hE_line j).isCompact.isClosed).preimage
        γ.continuous
    have hcov : A_cl ∪ B_cl = univ := by
      ext τ
      simp only [A_cl, B_cl, mem_union, mem_preimage, mem_iUnion, mem_univ, iff_true]
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hdiff ▸ hDsub (hγ τ))
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj.1)
      · exact Or.inr ⟨j, hji, hj.1⟩
    have hdisj : Disjoint A_cl B_cl := by
      rw [Set.disjoint_left]
      intro τ h1 h2
      obtain ⟨j, hji, hj⟩ := mem_iUnion₂.mp h2
      have hznV : γ τ ∉ V := (hDsub (hγ τ)).2
      exact Set.disjoint_left.mp (hE_disj (Ne.symm hji))
        ⟨h1, fun h => hznV (hE_capV i ▸ h).2⟩ ⟨hj, fun h => hznV (hE_capV j ▸ h).2⟩
    have hA_clopen : IsClopen A_cl := ⟨hA_cl, by
      have : A_cl = B_clᶜ := by
        ext τ; simp only [mem_compl_iff]
        exact ⟨fun h1 h2 => Set.disjoint_left.mp hdisj h1 h2,
          fun h2 => ((mem_union _ _ _).mp (hcov.symm ▸ mem_univ τ)).resolve_right h2⟩
      rw [this]; exact hB_cl.isOpen_compl⟩
    have h0A : (0 : unitInterval) ∈ A_cl := by show γ 0 ∈ E_arc i; rw [γ.source]; exact hxi.1
    have hA_univ : A_cl = univ := by
      rcases (connectedSpace_iff_clopen.mp inferInstance).2 A_cl hA_clopen with h0 | h1
      · exact ((Set.eq_empty_iff_forall_notMem.mp h0 0) h0A).elim
      · exact h1
    have h1A : γ 1 ∈ E_arc i := by
      have : (1 : unitInterval) ∈ A_cl := hA_univ.symm ▸ mem_univ (1 : unitInterval)
      exact this
    rw [γ.target] at h1A
    exact ⟨h1A, fun h => (hDsub hyD).2 (hE_capV i ▸ h).2⟩
  ext e
  constructor
  · intro he
    obtain ⟨x, hxe⟩ := he.1
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hdiff ▸ he.2.1 hxe)
    refine ⟨i, ?_⟩
    exact he.2.2.2 _ (hdiff.symm ▸ subset_iUnion (fun i => E_arc i \ {a i, b i}) i) (he_pc i)
      (hclopen_sub e i he.2.1 he.2.2.1 ⟨x, hxe, hxi⟩)
  · rintro ⟨i, rfl⟩
    refine ⟨(he_pc i).nonempty, hdiff.symm ▸ subset_iUnion (fun i => E_arc i \ {a i, b i}) i,
      he_pc i, fun D hDsub hDpc hsub => ?_⟩
    obtain ⟨x, hx⟩ := (he_pc i).nonempty
    exact Subset.antisymm (hclopen_sub D i hDsub hDpc ⟨x, hsub hx, hx⟩) hsub

/-- Any drawing built by `drawing_of_arcs` where the endpoints `b i` are pairwise distinct and
disjoint from `range a` is acyclic (`IsGraphForest`). -/
theorem isGraphForest_of_star_arcs {S : Type} [TopologicalSpace S] [T2Space S]
    {V : Set S} (hVfin : V.Finite)
    {m : ℕ} {E_arc : Fin m → Set S} {a b : Fin m → S}
    (hab : ∀ i, a i ≠ b i)
    (haV : ∀ i, a i ∈ V) (hbV : ∀ i, b i ∈ V)
    (hE_line : ∀ i, IsLineWithEnds (E_arc i) (a i) (b i))
    (hE_capV : ∀ i, E_arc i ∩ V = {a i, b i})
    (hE_disj : Pairwise fun i j => Disjoint (E_arc i \ {a i, b i}) (E_arc j \ {a j, b j}))
    (hb_inj : Function.Injective b)
    (hab_disj : Disjoint (range a) (range b)) :
    IsGraphForest (drawing_of_arcs hVfin hab haV hbV hE_line hE_capV hE_disj).toGraph := by
  let H := drawing_of_arcs hVfin hab haV hbV hE_line hE_capV hE_disj
  obtain ⟨hHE, hcl_i⟩ := drawing_of_arcs_E hVfin hab haV hbV hE_line hE_capV hE_disj
  -- Uniqueness: every leaf `b i` is incident to a unique edge `E_arc i \ {a i, b i}`.
  have hleaf_uniq : ∀ (i : Fin m) {e : Set S} {x y : S},
      H.toGraph.IsLink e x y → (x = b i ∨ y = b i) → e = E_arc i \ {a i, b i} := by
    intro i e x y hlink hxy
    obtain ⟨j, rfl⟩ := hHE ▸ hlink.1
    have hcap : E_arc j ∩ V = {x, y} := by
      have h1 := hlink.2.2.2
      rwa [hcl_i j] at h1
    have hbi_in : b i ∈ ({a j, b j} : Set S) := by
      rw [← hE_capV j, hcap]
      rcases hxy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hbi_in with h1 | h2
    · exact (Set.disjoint_left.mp hab_disj ⟨j, h1.symm⟩ ⟨i, rfl⟩).elim
    · rw [hb_inj h2]
  -- Helpers: any walk from `x` to `y` with `x ≠ y` starts with an edge at `x` and ends with one at `y`.
  have hwalk_start : ∀ {x y : S} (W : GraphWalk H.toGraph x y), x ≠ y →
      ∃ e ∈ W.edges, ∃ w, H.toGraph.IsLink e x w := by
    intro x y W hne
    cases W with
    | nil _ => exact (hne rfl).elim
    | @cons _ w _ e hlink _ => exact ⟨e, List.mem_cons_self .., w, hlink⟩
  have hwalk_end : ∀ {x y : S} (W : GraphWalk H.toGraph x y), x ≠ y →
      ∃ e ∈ W.edges, ∃ w, H.toGraph.IsLink e w y := by
    intro x y W
    induction W with
    | nil _ => intro h; exact (h rfl).elim
    | @cons u v w e hlink rest ih =>
      intro hne
      by_cases hvw : v = w
      · subst hvw
        exact ⟨e, List.mem_cons_self .., u, hlink⟩
      · obtain ⟨e', he', z, hz⟩ := ih hvw
        exact ⟨e', List.mem_cons_of_mem _ he', z, hz⟩
  intro u W hsc
  cases W with
  | nil _ => rfl
  | @cons _ v _ e₁ hlink₁ rest =>
    exfalso
    obtain ⟨i, hi_eq⟩ := hHE ▸ hlink₁.1
    have hi_eq' : E_arc i \ {a i, b i} = e₁ := hi_eq
    have hcap₁ : ({a i, b i} : Set S) = {u, v} := by
      have h1 : closure e₁ ∩ V = {u, v} := hlink₁.2.2.2
      rw [← hi_eq', hcl_i i, hE_capV i] at h1
      exact h1
    have hnodup : e₁ ∉ rest.edges := (List.nodup_cons.mp hsc.2).1
    have hu_in : u ∈ ({a i, b i} : Set S) := hcap₁.symm ▸ Or.inl rfl
    have hv_in : v ∈ ({a i, b i} : Set S) := hcap₁.symm ▸ Or.inr rfl
    have huv : u ≠ v := fun huv => by
      subst huv
      have hbi : b i ∈ ({u} : Set S) := by
        have : b i ∈ ({u, u} : Set S) := hcap₁ ▸ Or.inr rfl
        simpa using this
      have hai : a i ∈ ({u} : Set S) := by
        have : a i ∈ ({u, u} : Set S) := hcap₁ ▸ Or.inl rfl
        simpa using this
      exact hab i (hai.trans hbi.symm)
    rcases hu_in with rfl | rfl
    · -- `u = a i`, so `v = b i`
      have hv_eq : v = b i := hv_in.resolve_left huv.symm
      subst hv_eq
      obtain ⟨e₂, he₂_mem, w, hlink₂⟩ := hwalk_start rest huv.symm
      have he₂ : e₂ = E_arc i \ {a i, b i} := hleaf_uniq i hlink₂ (Or.inl rfl)
      have he_eq : e₁ = e₂ := hi_eq'.symm.trans he₂.symm
      exact hnodup (he_eq ▸ he₂_mem)
    · -- `u = b i`, so `v = a i`, and `rest : GraphWalk v (b i)` must end with an edge incident to `b i`!
      obtain ⟨e', he'_mem, z, hz⟩ := hwalk_end rest huv.symm
      have he' : e' = E_arc i \ {a i, b i} := hleaf_uniq i hz (Or.inr rfl)
      have he_eq : e₁ = e' := hi_eq'.symm.trans he'.symm
      exact hnodup (he_eq ▸ he'_mem)

end GraphMinor.LPPS22
