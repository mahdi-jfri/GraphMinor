module

public import GraphMinor.Surface.OrientSign
public import GraphMinor.Surface.Cuffs

/-!
# Surface orientation cocycle (`w1`) and boundary orientations

This file constructs the first Stiefel–Whitney orientation local cocycle `w1 : S → S → ZMod 2` on
any surface `S` (`IsSurface S`) from a finite half-plane atlas `SurfAtlas S`, together with
compatible cuff orientation signs `cuffSign`:

- `SurfChart S`: a half-plane chart `(U, O, j, k)` mapping an open `U ⊆ S` homeomorphically onto
  `O ∩ halfPlane ⊆ ℂ` (every point of `IsSurface S` has one by `IsManifoldPoint.exists_chart`).
- `chartPos` / `chartSign`: the local orientation comparison (`0` or `1` in `ZMod 2`) between two
  overlapping charts `c₁, c₂` at `x ∈ c₁.U ∩ c₂.U`, locally constant and satisfying the chain rule.
- `SurfAtlas S` and `exists_surfAtlas`: a finite shrunk atlas on any compact surface.
- `w1 A`: the orientation local cocycle of an atlas `A`, with:
  - `isCoc_w1 : IsCoc (w1 A)`,
  - `cohRel_w1_atlas`: any two atlases give cohomologous cocycles with explicit coboundary,
  - `cohRel_w1_homeo`: pullback along any homeomorphism `e : S ≃ₜ S'` is cohomologous to `w1`.
- `cuffPos` / `cuffSign`: local boundary orientation of a circle parameterization `φ : Circle ≃ₜ C`
  (`C ⊆ bd S`) relative to a chart or atlas, satisfying:
  - `cuffPos_iff_chartPos`: chart transitions change `cuffPos` precisely by `chartPos` (proved via
    nested rectangles and `PlaneOrientation.order_of_nested`),
  - `cuffSign_diff`: `cuffSign A φ y - cuffSign A φ x = w1 A x y` near the diagonal of `C`,
  - `bdTriv_w1 : BdTriv (w1 A)`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Metric Topology Filter Function

universe u v

/-! ### Surface charts and transition signs -/

/-- A half-plane chart of a surface `S`, mapping an open set `U ⊆ S` homeomorphically onto
`O ∩ halfPlane ⊆ ℂ`. -/
structure SurfChart (S : Type u) [TopologicalSpace S] where
  U : Set S
  O : Set ℂ
  j : S → ℂ
  k : ℂ → S
  hU : IsOpen U
  hO : IsOpen O
  hj : ContinuousOn j U
  hk : ContinuousOn k (O ∩ halfPlane)
  hm : MapsTo j U (O ∩ halfPlane)
  hk' : MapsTo k (O ∩ halfPlane) U
  hl : LeftInvOn k j U
  hr : LeftInvOn j k (O ∩ halfPlane)

section Chart

variable {S : Type u} [TopologicalSpace S]

/-- Every manifold point lies in a `SurfChart`. -/
theorem exists_surfChart {x : S} (hx : IsManifoldPoint x) :
    ∃ c : SurfChart S, x ∈ c.U := by
  obtain ⟨U, O, j, k, hU, hO, hxU, hj, hk, hm, hk', hl, hr⟩ := hx.exists_chart
  exact ⟨⟨U, O, j, k, hU, hO, hj, hk, hm, hk', hl, hr⟩, hxU⟩

theorem SurfChart.injOn_j (c : SurfChart S) : InjOn c.j c.U := c.hl.injOn

theorem SurfChart.injOn_k (c : SurfChart S) : InjOn c.k (c.O ∩ halfPlane) := c.hr.injOn

/-- A point of a chart lies in `bd S` iff its chart coordinate has `re = 0`. -/
theorem SurfChart.mem_bd_iff (c : SurfChart S) {x : S} (hx : x ∈ c.U) :
    x ∈ bd S ↔ (c.j x).re = 0 := by
  constructor
  · intro hbd
    exact le_antisymm (not_lt.mp fun hpos => hbd
      (isInteriorPoint_of_chart c.hU c.hO c.hj c.hk c.hm c.hk' c.hl c.hr hx hpos)) (c.hm hx).2
  · intro hre
    exact not_isInteriorPoint_of_chart c.hU c.hj c.hm c.injOn_j hx hre

theorem SurfChart.not_mem_bd_iff (c : SurfChart S) {x : S} (hx : x ∈ c.U) :
    x ∉ bd S ↔ 0 < (c.j x).re := by
  rw [c.mem_bd_iff hx]
  have hge : 0 ≤ (c.j x).re := (c.hm hx).2
  constructor
  · intro hne; exact lt_of_le_of_ne hge (Ne.symm hne)
  · intro hpos; exact hpos.ne'

/-- Pull back a `SurfChart` along a homeomorphism `e : S' ≃ₜ S`. -/
def SurfChart.pull {S' : Type v} [TopologicalSpace S'] (e : S' ≃ₜ S) (c : SurfChart S) :
    SurfChart S' where
  U := e ⁻¹' c.U
  O := c.O
  j := c.j ∘ e
  k := e.symm ∘ c.k
  hU := c.hU.preimage e.continuous
  hO := c.hO
  hj := c.hj.comp e.continuous.continuousOn (fun _ hx => hx)
  hk := e.symm.continuous.comp_continuousOn c.hk
  hm := fun _ hx => c.hm hx
  hk' := fun _ hz => by show e (e.symm (c.k _)) ∈ c.U; rw [e.apply_symm_apply]; exact c.hk' hz
  hl := fun x hx => by show e.symm (c.k (c.j (e x))) = x; rw [c.hl hx, e.symm_apply_apply]
  hr := fun z hz => by show c.j (e (e.symm (c.k z))) = z; rw [e.apply_symm_apply, c.hr hz]

/-- Every open neighborhood `W ⊆ c.U` of `x ∈ c.U` contains a ball-shaped open neighborhood `B`
of `x` whose interior `B ∩ (bd S)ᶜ` is nonempty and maps to a convex open set in `ℂ`. -/
theorem SurfChart.exists_ball_nbhd (c : SurfChart S) {x : S} {W : Set S} (hW : IsOpen W)
    (hxW : x ∈ W) (hWU : W ⊆ c.U) :
    ∃ r > 0, ball (c.j x) r ⊆ c.O ∧
      (∀ z ∈ ball (c.j x) r ∩ halfPlane, c.k z ∈ W) ∧
      IsOpen (c.U ∩ c.j ⁻¹' ball (c.j x) r) ∧
      x ∈ c.U ∩ c.j ⁻¹' ball (c.j x) r ∧
      c.U ∩ c.j ⁻¹' ball (c.j x) r ⊆ W ∧
      (c.U ∩ c.j ⁻¹' ball (c.j x) r ∩ (bd S)ᶜ).Nonempty ∧
      IsPreconnected (c.j '' (c.U ∩ c.j ⁻¹' ball (c.j x) r ∩ (bd S)ᶜ)) := by
  have hxU : x ∈ c.U := hWU hxW
  have h1 : c.k ⁻¹' W ∈ 𝓝[c.O ∩ halfPlane] (c.j x) := by
    have hkx : c.k (c.j x) ∈ W := by rwa [c.hl hxU]
    exact c.hk (c.j x) (c.hm hxU) (hW.mem_nhds hkx)
  rw [Metric.mem_nhdsWithin_iff] at h1
  obtain ⟨r₁, hr₁, hr₁_sub⟩ := h1
  obtain ⟨r₂, hr₂, hr₂_sub⟩ := Metric.isOpen_iff.mp c.hO (c.j x) (c.hm hxU).1
  set r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hBO : ball (c.j x) r ⊆ c.O := (ball_subset_ball (min_le_right _ _)).trans hr₂_sub
  have hBW : ∀ z ∈ ball (c.j x) r ∩ halfPlane, c.k z ∈ W := fun z hz =>
    hr₁_sub ⟨ball_subset_ball (min_le_left _ _) hz.1, hBO hz.1, hz.2⟩
  have hopen : IsOpen (c.U ∩ c.j ⁻¹' ball (c.j x) r) := c.hj.isOpen_inter_preimage c.hU isOpen_ball
  have hxB : x ∈ c.U ∩ c.j ⁻¹' ball (c.j x) r := ⟨hxU, mem_ball_self hr⟩
  have hBsub : c.U ∩ c.j ⁻¹' ball (c.j x) r ⊆ W := fun y hy => by
    rw [← c.hl hy.1]
    exact hBW (c.j y) ⟨hy.2, (c.hm hy.1).2⟩
  have hint_eq : c.j '' (c.U ∩ c.j ⁻¹' ball (c.j x) r ∩ (bd S)ᶜ) =
      ball (c.j x) r ∩ {z : ℂ | 0 < z.re} := by
    ext z
    constructor
    · rintro ⟨y, ⟨⟨hyU, hyB⟩, hyInt⟩, rfl⟩
      exact ⟨hyB, (c.not_mem_bd_iff hyU).mp hyInt⟩
    · rintro ⟨hzB, hzre⟩
      have hzre' : 0 < z.re := hzre
      have hzH : z ∈ c.O ∩ halfPlane := ⟨hBO hzB, hzre'.le⟩
      refine ⟨c.k z, ⟨⟨c.hk' hzH, ?_⟩, ?_⟩, c.hr hzH⟩
      · show c.j (c.k z) ∈ ball (c.j x) r; rwa [c.hr hzH]
      · rw [mem_compl_iff, c.not_mem_bd_iff (c.hk' hzH), c.hr hzH]; exact hzre'
  have hne : (c.U ∩ c.j ⁻¹' ball (c.j x) r ∩ (bd S)ᶜ).Nonempty := by
    set z₀ : ℂ := c.j x + ((r / 2 : ℝ) : ℂ)
    have hzB : z₀ ∈ ball (c.j x) r := by
      rw [mem_ball, dist_eq_norm]
      simp only [z₀, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hr)]
      exact half_lt_self hr
    have hzre : 0 < z₀.re := by
      have : 0 ≤ (c.j x).re := (c.hm hxU).2
      simp only [z₀, Complex.add_re, Complex.ofReal_re]; linarith
    have hzmem : z₀ ∈ c.j '' (c.U ∩ c.j ⁻¹' ball (c.j x) r ∩ (bd S)ᶜ) := by
      rw [hint_eq]; exact ⟨hzB, hzre⟩
    obtain ⟨y, hy, -⟩ := hzmem
    exact ⟨y, hy⟩
  have hconv : Convex ℝ (ball (c.j x) r ∩ {z : ℂ | 0 < z.re}) := by
    refine (convex_ball (c.j x) r).inter ?_
    intro a ha b hb u v hu hv huv
    show 0 < (u • a + v • b).re
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    have ha' : 0 < a.re := ha
    have hb' : 0 < b.re := hb
    rcases eq_or_lt_of_le hu with rfl | hu'
    · have : v = 1 := by linarith
      rw [this]; linarith
    · nlinarith
  exact ⟨r, hr, hBO, hBW, hopen, hxB, hBsub, hne, hint_eq ▸ hconv.isPreconnected⟩

/-- The image of `c₁.U ∩ c₂.U ∩ (bd S)ᶜ` under `c₁.j` is open in `ℂ`, and `c₂.j ∘ c₁.k` is
continuous and injective on it. -/
theorem SurfChart.trans_open (c₁ c₂ : SurfChart S) :
    IsOpen (c₁.j '' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ)) ∧
      ContinuousOn (c₂.j ∘ c₁.k) (c₁.j '' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ)) ∧
      InjOn (c₂.j ∘ c₁.k) (c₁.j '' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ)) := by
  have hopenS : IsOpen (c₁.U ∩ c₂.U ∩ (bd S)ᶜ) :=
    (c₁.hU.inter c₂.hU).inter (isClosed_bd S).isOpen_compl
  have hO_eq : c₁.j '' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ) =
      (c₁.O ∩ {z : ℂ | 0 < z.re}) ∩ c₁.k ⁻¹' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨(c₁.hm hy.1.1).1, (c₁.not_mem_bd_iff hy.1.1).mp hy.2⟩, ?_⟩
      show c₁.k (c₁.j y) ∈ c₁.U ∩ c₂.U ∩ (bd S)ᶜ; rwa [c₁.hl hy.1.1]
    · rintro ⟨⟨hzO, hzre⟩, hzk⟩
      have hzre' : 0 < z.re := hzre
      exact ⟨c₁.k z, hzk, c₁.hr ⟨hzO, hzre'.le⟩⟩
  have hopen1 : IsOpen (c₁.O ∩ {z : ℂ | 0 < z.re}) :=
    c₁.hO.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hsub1 : c₁.O ∩ {z : ℂ | 0 < z.re} ⊆ c₁.O ∩ halfPlane := fun z hz => ⟨hz.1, (show 0 < z.re from hz.2).le⟩
  have hopen : IsOpen (c₁.j '' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ)) := by
    rw [hO_eq]
    exact (c₁.hk.mono hsub1).isOpen_inter_preimage hopen1 hopenS
  have hsub_dom : c₁.j '' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ) ⊆ c₁.O ∩ halfPlane := by
    rw [hO_eq]; exact inter_subset_left.trans hsub1
  have hc : ContinuousOn (c₂.j ∘ c₁.k) (c₁.j '' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ)) :=
    c₂.hj.comp (c₁.hk.mono hsub_dom) (fun z hz => by rw [hO_eq] at hz; exact hz.2.1.2)
  have hi : InjOn (c₂.j ∘ c₁.k) (c₁.j '' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ)) := by
    intro a ha b hb he
    rw [hO_eq] at ha hb
    have h1 := c₂.injOn_j ha.2.1.2 hb.2.1.2 he
    exact c₁.injOn_k (hsub1 ha.1) (hsub1 hb.1) h1
  exact ⟨hopen, hc, hi⟩

/-- Two overlapping charts `c₁, c₂` agree in orientation at `x ∈ c₁.U ∩ c₂.U` if on some open
neighborhood `W ⊆ c₁.U ∩ c₂.U` of `x`, `c₂.j ∘ c₁.k` is `IsPosLocal` at every interior point of `W`. -/
def chartPos (c₁ c₂ : SurfChart S) (x : S) : Prop :=
  ∃ W : Set S, IsOpen W ∧ x ∈ W ∧ W ⊆ c₁.U ∩ c₂.U ∧
    ∀ y ∈ W, y ∉ bd S → IsPosLocal (c₂.j ∘ c₁.k) (c₁.j y)

/-- Characterization of `chartPos c₁ c₂ x` by checking `IsPosLocal` at a single interior point of a
connected-interior open neighborhood `W ⊆ c₁.U ∩ c₂.U`. -/
theorem chartPos_iff_of_int {c₁ c₂ : SurfChart S} {x y₀ : S} {W : Set S} (hW : IsOpen W)
    (hxW : x ∈ W) (hy₀W : y₀ ∈ W) (hy₀ : y₀ ∉ bd S) (hWsub : W ⊆ c₁.U ∩ c₂.U)
    (hconn : IsPreconnected (c₁.j '' (W ∩ (bd S)ᶜ))) :
    chartPos c₁ c₂ x ↔ IsPosLocal (c₂.j ∘ c₁.k) (c₁.j y₀) := by
  obtain ⟨hO, htc, hti⟩ := SurfChart.trans_open c₁ c₂
  have hWint_sub : c₁.j '' (W ∩ (bd S)ᶜ) ⊆ c₁.j '' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ) :=
    image_mono (inter_subset_inter_left _ hWsub)
  have hWint_open : IsOpen (c₁.j '' (W ∩ (bd S)ᶜ)) := by
    have h1 : c₁.j '' (W ∩ (bd S)ᶜ) = (c₁.O ∩ {z : ℂ | 0 < z.re}) ∩ c₁.k ⁻¹' (W ∩ (bd S)ᶜ) := by
      ext z
      constructor
      · rintro ⟨y, ⟨hyW, hyI⟩, rfl⟩
        refine ⟨⟨(c₁.hm (hWsub hyW).1).1, (c₁.not_mem_bd_iff (hWsub hyW).1).mp hyI⟩, ?_⟩
        show c₁.k (c₁.j y) ∈ W ∩ (bd S)ᶜ
        rw [c₁.hl (hWsub hyW).1]
        exact ⟨hyW, hyI⟩
      · rintro ⟨⟨hzO, hzre⟩, hzk⟩
        exact ⟨c₁.k z, hzk, c₁.hr ⟨hzO, (show 0 < z.re from hzre).le⟩⟩
    rw [h1]
    exact (c₁.hk.mono (fun z hz => ⟨hz.1, (show 0 < z.re from hz.2).le⟩)).isOpen_inter_preimage
      (c₁.hO.inter (isOpen_lt continuous_const Complex.continuous_re))
      (hW.inter (isClosed_bd S).isOpen_compl)
  constructor
  · rintro ⟨W', hW', hxW', hW'sub, hpos⟩
    obtain ⟨r, -, -, -, -, -, hBsub, ⟨y₁, hy₁B, hy₁Int⟩, -⟩ :=
      c₁.exists_ball_nbhd (hW.inter hW') ⟨hxW, hxW'⟩ (fun y hy => (hWsub hy.1).1)
    have hy₁W : y₁ ∈ W := (hBsub hy₁B).1
    have hy₁W' : y₁ ∈ W' := (hBsub hy₁B).2
    have h1 : IsPosLocal (c₂.j ∘ c₁.k) (c₁.j y₁) := hpos y₁ hy₁W' hy₁Int
    exact (isPosLocal_const_of_isPreconnected hWint_open hconn (htc.mono hWint_sub)
      (hti.mono hWint_sub) ⟨y₁, ⟨hy₁W, hy₁Int⟩, rfl⟩ ⟨y₀, ⟨hy₀W, hy₀⟩, rfl⟩).mp h1
  · intro hpos
    refine ⟨W, hW, hxW, hWsub, fun y hyW hyInt => ?_⟩
    exact (isPosLocal_const_of_isPreconnected hWint_open hconn (htc.mono hWint_sub)
      (hti.mono hWint_sub) ⟨y₀, ⟨hy₀W, hy₀⟩, rfl⟩ ⟨y, ⟨hyW, hyInt⟩, rfl⟩).mp hpos

theorem chartPos_refl {c : SurfChart S} {x : S} (hx : x ∈ c.U) : chartPos c c x := by
  refine ⟨c.U, c.hU, hx, subset_inter Subset.rfl Subset.rfl, fun y hyU hyInt => ?_⟩
  have hO_int : IsOpen (c.O ∩ {z : ℂ | 0 < z.re}) :=
    c.hO.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hmem : c.j y ∈ c.O ∩ {z : ℂ | 0 < z.re} := ⟨(c.hm hyU).1, (c.not_mem_bd_iff hyU).mp hyInt⟩
  have hfg : (c.j ∘ c.k) =ᶠ[𝓝 (c.j y)] id := by
    filter_upwards [hO_int.mem_nhds hmem] with z hz
    exact c.hr ⟨hz.1, (show 0 < z.re from hz.2).le⟩
  exact (isPosLocal_congr hfg).mpr (isPosLocal_id (c.j y))

theorem chartPos_trans_iff {c₁ c₂ c₃ : SurfChart S} {x : S}
    (h1 : x ∈ c₁.U) (h2 : x ∈ c₂.U) (h3 : x ∈ c₃.U) :
    chartPos c₁ c₃ x ↔ (chartPos c₁ c₂ x ↔ chartPos c₂ c₃ x) := by
  have hW : IsOpen (c₁.U ∩ c₂.U ∩ c₃.U) := (c₁.hU.inter c₂.hU).inter c₃.hU
  obtain ⟨r, -, -, -, hBo, hxB, hBsub, ⟨y₀, hy₀B, hy₀Int⟩, hBconn⟩ :=
    c₁.exists_ball_nbhd hW ⟨⟨h1, h2⟩, h3⟩ (fun y hy => hy.1.1)
  set B := c₁.U ∩ c₁.j ⁻¹' ball (c₁.j x) r
  have hy₀1 : y₀ ∈ c₁.U := (hBsub hy₀B).1.1
  have hy₀2 : y₀ ∈ c₂.U := (hBsub hy₀B).1.2
  have hy₀3 : y₀ ∈ c₃.U := (hBsub hy₀B).2
  rw [chartPos_iff_of_int hBo hxB hy₀B hy₀Int (fun y hy => ⟨(hBsub hy).1.1, (hBsub hy).2⟩) hBconn,
    chartPos_iff_of_int hBo hxB hy₀B hy₀Int (fun y hy => (hBsub hy).1) hBconn]
  -- Also express `chartPos c₂ c₃ x` at `y₀` using a ball in `c₂`!
  obtain ⟨r₂, -, -, -, hB2o, hxB2, hB2sub, -, hB2conn⟩ :=
    c₂.exists_ball_nbhd hBo hxB (fun y hy => (hBsub hy).1.2)
  set B₂ := c₂.U ∩ c₂.j ⁻¹' ball (c₂.j x) r₂
  -- Pick an interior point `y₁` in `B₂` (which is also in `B`)!
  obtain ⟨r₃, -, -, -, hB3o, hxB3, hB3sub, ⟨y₁, hy₁B3, hy₁Int⟩, hB3conn⟩ :=
    c₁.exists_ball_nbhd (hBo.inter hB2o) ⟨hxB, hxB2⟩ (fun y hy => (hBsub hy.1).1.1)
  have hy₁B : y₁ ∈ B := (hB3sub hy₁B3).1
  have hy₁B2 : y₁ ∈ B₂ := (hB3sub hy₁B3).2
  have hy₁1 : y₁ ∈ c₁.U := (hBsub hy₁B).1.1
  have hy₁2 : y₁ ∈ c₂.U := (hBsub hy₁B).1.2
  have hy₁3 : y₁ ∈ c₃.U := (hBsub hy₁B).2
  -- Rewrite all three at the single interior point `y₁`!
  rw [← chartPos_iff_of_int hBo hxB hy₀B hy₀Int (fun y hy => ⟨(hBsub hy).1.1, (hBsub hy).2⟩) hBconn,
    ← chartPos_iff_of_int hBo hxB hy₀B hy₀Int (fun y hy => (hBsub hy).1) hBconn,
    chartPos_iff_of_int hBo hxB hy₁B hy₁Int (fun y hy => ⟨(hBsub hy).1.1, (hBsub hy).2⟩) hBconn,
    chartPos_iff_of_int hBo hxB hy₁B hy₁Int (fun y hy => (hBsub hy).1) hBconn,
    chartPos_iff_of_int hB2o hxB2 hy₁B2 hy₁Int (fun y hy => ⟨(hBsub (hB2sub hy)).1.2, (hBsub (hB2sub hy)).2⟩) hB2conn]
  -- Apply `isPosLocal_comp` at `c₁.j y₁`!
  obtain ⟨hO12, hc12, hi12⟩ := SurfChart.trans_open c₁ c₂
  obtain ⟨hO23, hc23, hi23⟩ := SurfChart.trans_open c₂ c₃
  set U123 := c₁.j '' (c₁.U ∩ c₂.U ∩ c₃.U ∩ (bd S)ᶜ)
  have hU123_sub12 : U123 ⊆ c₁.j '' (c₁.U ∩ c₂.U ∩ (bd S)ᶜ) :=
    image_mono (fun y hy => ⟨hy.1.1, hy.2⟩)
  have hU123_open : IsOpen U123 := by
    have heq : U123 = (c₁.O ∩ {z : ℂ | 0 < z.re}) ∩ c₁.k ⁻¹' (c₁.U ∩ c₂.U ∩ c₃.U ∩ (bd S)ᶜ) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨⟨(c₁.hm hy.1.1.1).1, (c₁.not_mem_bd_iff hy.1.1.1).mp hy.2⟩, ?_⟩
        show c₁.k (c₁.j y) ∈ c₁.U ∩ c₂.U ∩ c₃.U ∩ (bd S)ᶜ; rwa [c₁.hl hy.1.1.1]
      · rintro ⟨⟨hzO, hzre⟩, hzk⟩
        exact ⟨c₁.k z, hzk, c₁.hr ⟨hzO, (show 0 < z.re from hzre).le⟩⟩
    rw [heq]
    exact (c₁.hk.mono (fun z hz => ⟨hz.1, (show 0 < z.re from hz.2).le⟩)).isOpen_inter_preimage
      (c₁.hO.inter (isOpen_lt continuous_const Complex.continuous_re))
      (hW.inter (isClosed_bd S).isOpen_compl)
  have hmap : (c₂.j ∘ c₁.k) '' U123 ⊆ c₂.j '' (c₂.U ∩ c₃.U ∩ (bd S)ᶜ) := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y, ⟨⟨hy.1.1.2, hy.1.2⟩, hy.2⟩, ?_⟩
    show c₂.j y = c₂.j (c₁.k (c₁.j y)); rw [c₁.hl hy.1.1.1]
  have hy₁_mem : c₁.j y₁ ∈ U123 := ⟨y₁, ⟨⟨⟨hy₁1, hy₁2⟩, hy₁3⟩, hy₁Int⟩, rfl⟩
  have hcomp_germ : ((c₃.j ∘ c₂.k) ∘ (c₂.j ∘ c₁.k)) =ᶠ[𝓝 (c₁.j y₁)] (c₃.j ∘ c₁.k) := by
    filter_upwards [hU123_open.mem_nhds hy₁_mem] with z hz
    obtain ⟨y, hy, rfl⟩ := hz
    simp only [Function.comp_apply, c₁.hl hy.1.1.1, c₂.hl hy.1.1.2]
  have hcomp := isPosLocal_comp hU123_open (hc12.mono hU123_sub12) (hi12.mono hU123_sub12)
    hmap hc23 hi23 hy₁_mem
  rw [isPosLocal_congr hcomp_germ] at hcomp
  have hval : (c₂.j ∘ c₁.k) (c₁.j y₁) = c₂.j y₁ := by simp [c₁.hl hy₁1]
  rw [hval] at hcomp
  tauto

/-- Orientation transition sign in `ZMod 2`: `0` if `chartPos`, `1` otherwise. -/
noncomputable def chartSign (c₁ c₂ : SurfChart S) (x : S) : ZMod 2 :=
  open Classical in if chartPos c₁ c₂ x then 0 else 1

theorem chartSign_refl {c : SurfChart S} {x : S} (hx : x ∈ c.U) : chartSign c c x = 0 := by
  classical
  simp [chartSign, chartPos_refl hx]

theorem chartSign_trans {c₁ c₂ c₃ : SurfChart S} {x : S}
    (h1 : x ∈ c₁.U) (h2 : x ∈ c₂.U) (h3 : x ∈ c₃.U) :
    chartSign c₁ c₂ x + chartSign c₂ c₃ x = chartSign c₁ c₃ x := by
  classical
  have h := chartPos_trans_iff h1 h2 h3
  unfold chartSign
  by_cases h12 : chartPos c₁ c₂ x <;> by_cases h23 : chartPos c₂ c₃ x
  · have h13 : chartPos c₁ c₃ x := h.mpr (by tauto)
    simp [h12, h23, h13]
  · have h13 : ¬ chartPos c₁ c₃ x := fun hc => h23 ((h.mp hc).mp h12)
    simp [h12, h23, h13]
  · have h13 : ¬ chartPos c₁ c₃ x := fun hc => h12 ((h.mp hc).mpr h23)
    simp [h12, h23, h13]
  · have h13 : chartPos c₁ c₃ x := h.mpr (by tauto)
    simp [h12, h23, h13]
    decide

theorem chartSign_symm {c₁ c₂ : SurfChart S} {x : S} (h1 : x ∈ c₁.U) (h2 : x ∈ c₂.U) :
    chartSign c₂ c₁ x = chartSign c₁ c₂ x := by
  have h := chartSign_trans h1 h2 h1
  rw [chartSign_refl h1] at h
  have : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  exact this _ _ h

/-- `chartSign c₁ c₂` is constant on any connected-interior open set `W ⊆ c₁.U ∩ c₂.U`. -/
theorem chartSign_eq_of_ball {c₁ c₂ : SurfChart S} {W : Set S} (hW : IsOpen W)
    (hWsub : W ⊆ c₁.U ∩ c₂.U) (hne : (W ∩ (bd S)ᶜ).Nonempty)
    (hconn : IsPreconnected (c₁.j '' (W ∩ (bd S)ᶜ))) {x y : S} (hx : x ∈ W) (hy : y ∈ W) :
    chartSign c₁ c₂ x = chartSign c₁ c₂ y := by
  classical
  obtain ⟨y₀, hy₀W, hy₀Int⟩ := hne
  have h1 := chartPos_iff_of_int hW hx hy₀W hy₀Int hWsub hconn
  have h2 := chartPos_iff_of_int hW hy hy₀W hy₀Int hWsub hconn
  simp [chartSign, h1.trans h2.symm]

/-- `chartSign` is invariant under pulling charts back along a homeomorphism `e : S' ≃ₜ S`. -/
theorem chartPos_pull {S' : Type v} [TopologicalSpace S'] (e : S' ≃ₜ S)
    {c₁ c₂ : SurfChart S} {x : S'} :
    chartPos (c₁.pull e) (c₂.pull e) x ↔ chartPos c₁ c₂ (e x) := by
  have htrans : (c₂.pull e).j ∘ (c₁.pull e).k = c₂.j ∘ c₁.k := by
    funext z; simp [SurfChart.pull]
  have hbd : ∀ y : S', y ∈ bd S' ↔ e y ∈ bd S := fun y => by
    have h := image_bd_homeomorph e
    constructor
    · intro hy; rw [← h]; exact mem_image_of_mem e hy
    · intro hy; rw [← h] at hy; obtain ⟨y', hy', he⟩ := hy; rwa [← e.injective he]
  constructor
  · rintro ⟨W, hW, hxW, hWsub, hpos⟩
    refine ⟨e '' W, e.isOpenMap W hW, mem_image_of_mem e hxW, ?_, ?_⟩
    · rintro _ ⟨y, hyW, rfl⟩; exact hWsub hyW
    · rintro _ ⟨y, hyW, rfl⟩ hyInt
      have := hpos y hyW (fun h => hyInt ((hbd y).mp h))
      rwa [htrans] at this
  · rintro ⟨W, hW, hxW, hWsub, hpos⟩
    refine ⟨e ⁻¹' W, hW.preimage e.continuous, hxW, fun y hy => hWsub hy, fun y hyW hyInt => ?_⟩
    rw [htrans]
    exact hpos (e y) hyW (fun h => hyInt ((hbd y).mpr h))

theorem chartSign_pull {S' : Type v} [TopologicalSpace S'] (e : S' ≃ₜ S)
    {c₁ c₂ : SurfChart S} {x : S'} :
    chartSign (c₁.pull e) (c₂.pull e) x = chartSign c₁ c₂ (e x) := by
  classical
  simp [chartSign, chartPos_pull]

end Chart

/-! ### Finite atlases and the orientation cocycle `w1` -/

/-- A finite shrunk half-plane atlas on a surface `S`. -/
structure SurfAtlas (S : Type u) [TopologicalSpace S] where
  m : ℕ
  chart : Fin m → SurfChart S
  V : Fin m → Set S
  hV_open : ∀ i, IsOpen (V i)
  hV_sub : ∀ i, closure (V i) ⊆ (chart i).U
  idx : S → Fin m
  hidx : ∀ x, x ∈ V (idx x)

section Atlas

variable {S : Type u} [TopologicalSpace S]

private theorem exists_open_closure_subset [CompactSpace S] [T2Space S] {U : Set S} {x : S}
    (hU : U ∈ 𝓝 x) : ∃ V : Set S, IsOpen V ∧ x ∈ V ∧ closure V ⊆ U := by
  obtain ⟨V, hVo, hxV, hVcl⟩ := (isCompact_singleton (x := x)).exists_isOpen_closure_subset (by simpa using hU)
  exact ⟨V, hVo, singleton_subset_iff.mp hxV, hVcl⟩

/-- Every surface has a finite shrunk atlas. -/
theorem exists_surfAtlas (hS : IsSurface S) : Nonempty (SurfAtlas S) := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hex : ∀ x : S, ∃ (c : SurfChart S) (V : Set S), IsOpen V ∧ x ∈ V ∧ closure V ⊆ c.U := by
    intro x
    obtain ⟨c, hxU⟩ := exists_surfChart (hS.2.2 x)
    obtain ⟨V, hVopen, hxV, hVcl⟩ := exists_open_closure_subset (c.hU.mem_nhds hxU)
    exact ⟨c, V, hVopen, hxV, hVcl⟩
  choose c V hVo hxV hVcl using hex
  have hcov : (univ : Set S) ⊆ ⋃ x : S, V x := fun x _ => mem_iUnion.mpr ⟨x, hxV x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo hcov
  let e : Fin t.card ≃ t := (Fintype.equivFinOfCardEq (Fintype.card_coe t)).symm
  have hmem : ∀ x : S, ∃ i : Fin t.card, x ∈ V (e i).1 := fun x => by
    have hx := ht (mem_univ x)
    simp only [mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨e.symm ⟨y, hy⟩, by simpa using hxy⟩
  choose idx hidx using hmem
  exact ⟨⟨t.card, fun i => c (e i).1, fun i => V (e i).1, fun i => hVo (e i).1,
    fun i => hVcl (e i).1, idx, hidx⟩⟩

/-- Pull back a `SurfAtlas` along a homeomorphism `e : S' ≃ₜ S`. -/
def SurfAtlas.pull {S' : Type v} [TopologicalSpace S'] (e : S' ≃ₜ S) (A : SurfAtlas S) :
    SurfAtlas S' where
  m := A.m
  chart := fun i => (A.chart i).pull e
  V := fun i => e ⁻¹' A.V i
  hV_open := fun i => (A.hV_open i).preimage e.continuous
  hV_sub := fun i => by
    rw [← e.preimage_closure]
    exact preimage_mono (A.hV_sub i)
  idx := fun x => A.idx (e x)
  hidx := fun x => A.hidx (e x)

/-- The first Stiefel–Whitney orientation local cocycle of an atlas `A`. -/
noncomputable def w1 (A : SurfAtlas S) (x y : S) : ZMod 2 :=
  chartSign (A.chart (A.idx x)) (A.chart (A.idx y)) x

theorem w1_pull {S' : Type v} [TopologicalSpace S'] (e : S' ≃ₜ S) (A : SurfAtlas S) :
    w1 (A.pull e) = pbk e (w1 A) := by
  funext x y
  exact chartSign_pull e

/-- Every surface with a finite shrunk atlas admits a `NearDiag` neighborhood on which triples lie
inside a single ball neighborhood contained in all active charts. -/
private theorem exists_triple_nearDiag (hS : IsSurface S) (A : SurfAtlas S) :
    ∃ N : Set (S × S), NearDiag N ∧
      ∀ x y z, (x, y) ∈ N → (x, z) ∈ N →
        ∃ (c₀ : SurfChart S) (W : Set S), IsOpen W ∧ x ∈ W ∧ y ∈ W ∧ z ∈ W ∧
          W ⊆ (A.chart (A.idx x)).U ∧ W ⊆ (A.chart (A.idx y)).U ∧ W ⊆ (A.chart (A.idx z)).U ∧
          W ⊆ c₀.U ∧ (W ∩ (bd S)ᶜ).Nonempty ∧ IsPreconnected (c₀.j '' (W ∩ (bd S)ᶜ)) := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hex : ∀ w : S, ∃ (c₀ : SurfChart S) (B D : Set S),
      IsOpen B ∧ IsOpen D ∧ w ∈ D ∧ closure D ⊆ B ∧ B ⊆ c₀.U ∧
      (∀ i : Fin A.m, w ∈ closure (A.V i) → B ⊆ (A.chart i).U) ∧
      (∀ j : Fin A.m, w ∉ closure (A.V j) → Disjoint B (closure (A.V j))) ∧
      (B ∩ (bd S)ᶜ).Nonempty ∧ IsPreconnected (c₀.j '' (B ∩ (bd S)ᶜ)) := by
    intro w
    let c₀ := A.chart (A.idx w)
    have hwU : w ∈ c₀.U := A.hV_sub _ (subset_closure (A.hidx w))
    let W₁ : Set S := ⋂ i ∈ Finset.univ.filter (fun i : Fin A.m => w ∈ closure (A.V i)), (A.chart i).U
    let W₂ : Set S := ⋂ j ∈ Finset.univ.filter (fun j : Fin A.m => w ∉ closure (A.V j)), (closure (A.V j))ᶜ
    have hW₁ : IsOpen W₁ := isOpen_biInter_finset fun i _ => (A.chart i).hU
    have hW₂ : IsOpen W₂ := isOpen_biInter_finset fun j _ => isClosed_closure.isOpen_compl
    have hwW : w ∈ c₀.U ∩ (W₁ ∩ W₂) := by
      refine ⟨hwU, ?_, ?_⟩
      · simp only [W₁, mem_iInter, Finset.mem_filter]; exact fun i hi => A.hV_sub i hi.2
      · simp only [W₂, mem_iInter, Finset.mem_filter, mem_compl_iff]; exact fun j hj => hj.2
    obtain ⟨r, -, -, -, hBo, hwB, hBsub, hBne, hBconn⟩ :=
      c₀.exists_ball_nbhd (c₀.hU.inter (hW₁.inter hW₂)) hwW inter_subset_left
    set B := c₀.U ∩ c₀.j ⁻¹' ball (c₀.j w) r
    obtain ⟨D, hDo, hwD, hDcl⟩ := exists_open_closure_subset (hBo.mem_nhds hwB)
    refine ⟨c₀, B, D, hBo, hDo, hwD, hDcl, fun y hy => (hBsub hy).1, ?_, ?_, hBne, hBconn⟩
    · intro i hi y hy
      have h1 := (hBsub hy).2.1
      simp only [W₁, mem_iInter, Finset.mem_filter] at h1
      exact h1 i ⟨Finset.mem_univ _, hi⟩
    · intro j hj
      rw [Set.disjoint_left]
      intro y hyB hyV
      have h1 := (hBsub hyB).2.2
      simp only [W₂, mem_iInter, Finset.mem_filter, mem_compl_iff] at h1
      exact h1 j ⟨Finset.mem_univ _, hj⟩ hyV
  choose c₀ B D hBo hDo hwD hDcl hBc hB_in hB_disj hBne hBconn using hex
  have hcov : (univ : Set S) ⊆ ⋃ w : S, D w := fun x _ => mem_iUnion.mpr ⟨x, hwD x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover D hDo hcov
  let N : Set (S × S) := {p | ∀ w ∈ t, p.1 ∈ closure (D w) → p.2 ∈ B w}
  refine ⟨N, ?_, ?_⟩
  · intro x
    let O₁ : Set S := ⋂ w ∈ t.filter (fun w => x ∈ closure (D w)), B w
    let O₂ : Set S := ⋂ w ∈ t.filter (fun w => x ∉ closure (D w)), (closure (D w))ᶜ
    have hO₁ : IsOpen O₁ := isOpen_biInter_finset fun w _ => hBo w
    have hO₂ : IsOpen O₂ := isOpen_biInter_finset fun w _ => isClosed_closure.isOpen_compl
    have hxO : x ∈ O₁ ∩ O₂ := by
      refine ⟨?_, ?_⟩
      · simp only [O₁, mem_iInter, Finset.mem_filter]; exact fun w hw => hDcl w hw.2
      · simp only [O₂, mem_iInter, Finset.mem_filter, mem_compl_iff]; exact fun w hw => hw.2
    refine Filter.mem_of_superset ((hO₁.inter hO₂).prod (hO₁.inter hO₂) |>.mem_nhds ⟨hxO, hxO⟩) ?_
    rintro ⟨a, b⟩ ⟨⟨ha1, ha2⟩, ⟨hb1, -⟩⟩ w hwt haw
    have hxw : x ∈ closure (D w) := by
      by_contra hxn
      simp only [O₂, mem_iInter, Finset.mem_filter, mem_compl_iff] at ha2
      exact ha2 w ⟨hwt, hxn⟩ haw
    simp only [O₁, mem_iInter, Finset.mem_filter] at hb1
    exact hb1 w ⟨hwt, hxw⟩
  · intro x y z hxy hxz
    have hx := ht (mem_univ x)
    simp only [mem_iUnion] at hx
    obtain ⟨w, hwt, hxw⟩ := hx
    have hxcl : x ∈ closure (D w) := subset_closure hxw
    have hxB : x ∈ B w := hDcl w hxcl
    have hyB : y ∈ B w := hxy w hwt hxcl
    have hzB : z ∈ B w := hxz w hwt hxcl
    have hact : ∀ p ∈ B w, B w ⊆ (A.chart (A.idx p)).U := fun p hp => by
      refine hB_in w (A.idx p) ?_
      by_contra hnot
      exact Set.disjoint_left.mp (hB_disj w (A.idx p) hnot) hp (subset_closure (A.hidx p))
    exact ⟨c₀ w, B w, hBo w, hxB, hyB, hzB, hact x hxB, hact y hyB, hact z hzB, hBc w, hBne w, hBconn w⟩

/-- `w1 A` is a local cocycle on `S`. -/
theorem isCoc_w1 (hS : IsSurface S) (A : SurfAtlas S) : IsCoc (w1 A) := by
  obtain ⟨N, hN, htr⟩ := exists_triple_nearDiag hS A
  refine ⟨N, hN, fun x y z hxy _hyz hxz => ?_⟩
  obtain ⟨c₀, W, hWo, hxW, hyW, hzW, hWx, hWy, hWz, hWc₀, hWne, hWconn⟩ := htr x y z hxy hxz
  have hx_eq : chartSign (A.chart (A.idx y)) (A.chart (A.idx z)) y =
      chartSign (A.chart (A.idx y)) (A.chart (A.idx z)) x := by
    -- Express both via `c₀` where `c₀.j '' (W ∩ (bd S)ᶜ)` is connected!
    have e1 := chartSign_trans (hWy hyW) (hWc₀ hyW) (hWz hyW)
    have e2 := chartSign_trans (hWy hxW) (hWc₀ hxW) (hWz hxW)
    rw [← e1, ← e2, chartSign_symm (hWc₀ hyW) (hWy hyW), chartSign_symm (hWc₀ hxW) (hWy hxW),
      chartSign_eq_of_ball hWo (subset_inter hWc₀ hWy) hWne hWconn hyW hxW,
      chartSign_eq_of_ball hWo (subset_inter hWc₀ hWz) hWne hWconn hyW hxW]
  unfold w1
  rw [hx_eq]
  exact chartSign_trans (hWx hxW) (hWy hxW) (hWz hxW)

/-- Any two atlases on `S` produce cohomologous orientation cocycles, with explicit coboundary
`x ↦ chartSign (A.chart (A.idx x)) (A'.chart (A'.idx x)) x`. -/
theorem cohRel_w1_atlas_explicit (hS : IsSurface S) (A A' : SurfAtlas S) :
    ∃ N : Set (S × S), NearDiag N ∧ ∀ x y, (x, y) ∈ N →
      w1 A x y - w1 A' x y =
        chartSign (A.chart (A.idx y)) (A'.chart (A'.idx y)) y -
          chartSign (A.chart (A.idx x)) (A'.chart (A'.idx x)) x := by
  obtain ⟨N₁, hN₁, htr₁⟩ := exists_triple_nearDiag hS A
  obtain ⟨N₂, hN₂, htr₂⟩ := exists_triple_nearDiag hS A'
  -- Intersect `N₁` and `N₂` and refine so `x, y` lie in ONE connected-interior open set inside all 4 charts!
  -- Even simpler: build a merged atlas `A ⊕ A'`? Or just do a direct finite open cover around each `w`!
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hex : ∀ w : S, ∃ (c₀ : SurfChart S) (B D : Set S),
      IsOpen B ∧ IsOpen D ∧ w ∈ D ∧ closure D ⊆ B ∧ B ⊆ c₀.U ∧
      (∀ i : Fin A.m, w ∈ closure (A.V i) → B ⊆ (A.chart i).U) ∧
      (∀ j : Fin A.m, w ∉ closure (A.V j) → Disjoint B (closure (A.V j))) ∧
      (∀ i : Fin A'.m, w ∈ closure (A'.V i) → B ⊆ (A'.chart i).U) ∧
      (∀ j : Fin A'.m, w ∉ closure (A'.V j) → Disjoint B (closure (A'.V j))) ∧
      (B ∩ (bd S)ᶜ).Nonempty ∧ IsPreconnected (c₀.j '' (B ∩ (bd S)ᶜ)) := by
    intro w
    let c₀ := A.chart (A.idx w)
    have hwU : w ∈ c₀.U := A.hV_sub _ (subset_closure (A.hidx w))
    let W₁ : Set S :=
      (⋂ i ∈ Finset.univ.filter (fun i : Fin A.m => w ∈ closure (A.V i)), (A.chart i).U) ∩
      (⋂ i ∈ Finset.univ.filter (fun i : Fin A'.m => w ∈ closure (A'.V i)), (A'.chart i).U)
    let W₂ : Set S :=
      (⋂ j ∈ Finset.univ.filter (fun j : Fin A.m => w ∉ closure (A.V j)), (closure (A.V j))ᶜ) ∩
      (⋂ j ∈ Finset.univ.filter (fun j : Fin A'.m => w ∉ closure (A'.V j)), (closure (A'.V j))ᶜ)
    have hW₁ : IsOpen W₁ :=
      (isOpen_biInter_finset fun i _ => (A.chart i).hU).inter
      (isOpen_biInter_finset fun i _ => (A'.chart i).hU)
    have hW₂ : IsOpen W₂ :=
      (isOpen_biInter_finset fun j _ => isClosed_closure.isOpen_compl).inter
      (isOpen_biInter_finset fun j _ => isClosed_closure.isOpen_compl)
    have hwW : w ∈ c₀.U ∩ (W₁ ∩ W₂) := by
      refine ⟨hwU, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · simp only [mem_iInter, Finset.mem_filter]; exact fun i hi => A.hV_sub i hi.2
      · simp only [mem_iInter, Finset.mem_filter]; exact fun i hi => A'.hV_sub i hi.2
      · simp only [mem_iInter, Finset.mem_filter, mem_compl_iff]; exact fun j hj => hj.2
      · simp only [mem_iInter, Finset.mem_filter, mem_compl_iff]; exact fun j hj => hj.2
    obtain ⟨r, -, -, -, hBo, hwB, hBsub, hBne, hBconn⟩ :=
      c₀.exists_ball_nbhd (c₀.hU.inter (hW₁.inter hW₂)) hwW inter_subset_left
    set B := c₀.U ∩ c₀.j ⁻¹' ball (c₀.j w) r
    obtain ⟨D, hDo, hwD, hDcl⟩ := exists_open_closure_subset (hBo.mem_nhds hwB)
    refine ⟨c₀, B, D, hBo, hDo, hwD, hDcl, fun y hy => (hBsub hy).1, ?_, ?_, ?_, ?_, hBne, hBconn⟩
    · intro i hi y hy; have := (hBsub hy).2.1.1; simp only [mem_iInter, Finset.mem_filter] at this; exact this i ⟨Finset.mem_univ _, hi⟩
    · intro j hj; rw [Set.disjoint_left]; intro y hyB hyV
      have := (hBsub hyB).2.2.1; simp only [mem_iInter, Finset.mem_filter, mem_compl_iff] at this; exact this j ⟨Finset.mem_univ _, hj⟩ hyV
    · intro i hi y hy; have := (hBsub hy).2.1.2; simp only [mem_iInter, Finset.mem_filter] at this; exact this i ⟨Finset.mem_univ _, hi⟩
    · intro j hj; rw [Set.disjoint_left]; intro y hyB hyV
      have := (hBsub hyB).2.2.2; simp only [mem_iInter, Finset.mem_filter, mem_compl_iff] at this; exact this j ⟨Finset.mem_univ _, hj⟩ hyV
  choose c₀ B D hBo hDo hwD hDcl hBc hB_in hB_disj hB'_in hB'_disj hBne hBconn using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover D hDo (fun x _ => mem_iUnion.mpr ⟨x, hwD x⟩)
  let N : Set (S × S) := {p | ∀ w ∈ t, p.1 ∈ closure (D w) → p.2 ∈ B w}
  refine ⟨N, ?_, ?_⟩
  · intro x
    let O₁ : Set S := ⋂ w ∈ t.filter (fun w => x ∈ closure (D w)), B w
    let O₂ : Set S := ⋂ w ∈ t.filter (fun w => x ∉ closure (D w)), (closure (D w))ᶜ
    have hO₁ : IsOpen O₁ := isOpen_biInter_finset fun w _ => hBo w
    have hO₂ : IsOpen O₂ := isOpen_biInter_finset fun w _ => isClosed_closure.isOpen_compl
    have hxO : x ∈ O₁ ∩ O₂ := ⟨by simp [O₁]; exact fun w _ hw => hDcl w hw, by simp [O₂]⟩
    refine Filter.mem_of_superset ((hO₁.inter hO₂).prod (hO₁.inter hO₂) |>.mem_nhds ⟨hxO, hxO⟩) ?_
    rintro ⟨a, b⟩ ⟨⟨-, ha2⟩, ⟨hb1, -⟩⟩ w hwt haw
    have hxw : x ∈ closure (D w) := by
      by_contra hxn; simp only [O₂, mem_iInter, Finset.mem_filter, mem_compl_iff] at ha2
      exact ha2 w ⟨hwt, hxn⟩ haw
    simp only [O₁, mem_iInter, Finset.mem_filter] at hb1
    exact hb1 w ⟨hwt, hxw⟩
  · intro x y hxy
    have hx := ht (mem_univ x); simp only [mem_iUnion] at hx
    obtain ⟨w, hwt, hxw⟩ := hx
    have hxB : x ∈ B w := hDcl w (subset_closure hxw)
    have hyB : y ∈ B w := hxy w hwt (subset_closure hxw)
    have hact : ∀ p ∈ B w, B w ⊆ (A.chart (A.idx p)).U := fun p hp =>
      hB_in w _ (by by_contra hn; exact Set.disjoint_left.mp (hB_disj w _ hn) hp (subset_closure (A.hidx p)))
    have hact' : ∀ p ∈ B w, B w ⊆ (A'.chart (A'.idx p)).U := fun p hp =>
      hB'_in w _ (by by_contra hn; exact Set.disjoint_left.mp (hB'_disj w _ hn) hp (subset_closure (A'.hidx p)))
    have hy_eq : chartSign (A.chart (A.idx y)) (A'.chart (A'.idx y)) y =
        chartSign (A.chart (A.idx y)) (A'.chart (A'.idx y)) x := by
      have e1 := chartSign_trans (hact y hyB hyB) (hBc w hyB) (hact' y hyB hyB)
      have e2 := chartSign_trans (hact y hyB hxB) (hBc w hxB) (hact' y hyB hxB)
      rw [← e1, ← e2, chartSign_symm (hBc w hyB) (hact y hyB hyB),
        chartSign_symm (hBc w hxB) (hact y hyB hxB),
        chartSign_eq_of_ball (hBo w) (subset_inter (hBc w) (hact y hyB)) (hBne w) (hBconn w) hyB hxB,
        chartSign_eq_of_ball (hBo w) (subset_inter (hBc w) (hact' y hyB)) (hBne w) (hBconn w) hyB hxB]
    rw [hy_eq]
    unfold w1
    have t1 := chartSign_trans (hact x hxB hxB) (hact y hyB hxB) (hact' y hyB hxB)
    have t2 := chartSign_trans (hact x hxB hxB) (hact' x hxB hxB) (hact' y hyB hxB)
    have hcomb := t1.trans t2.symm
    have : ∀ a b c d : ZMod 2, a + b = c + d → a - d = b - c := by decide
    exact this _ _ _ _ hcomb

theorem cohRel_w1_atlas (hS : IsSurface S) (A A' : SurfAtlas S) : CohRel (w1 A) (w1 A') := by
  obtain ⟨N, hN, hrel⟩ := cohRel_w1_atlas_explicit hS A A'
  exact ⟨fun x => chartSign (A.chart (A.idx x)) (A'.chart (A'.idx x)) x, N, hN, hrel⟩

theorem cohRel_w1_homeo {S' : Type v} [TopologicalSpace S'] (hS : IsSurface S) (e : S ≃ₜ S')
    (A : SurfAtlas S) (A' : SurfAtlas S') : CohRel (pbk e (w1 A')) (w1 A) := by
  rw [← w1_pull e A']
  exact cohRel_w1_atlas hS (A'.pull e) A

end Atlas

/-! ### Boundary orientation (`cuffPos` and `cuffSign`) -/

section Boundary

variable {S : Type u} [TopologicalSpace S]

/-- Positive boundary orientation of a circle parameterization `φ : Circle ≃ₜ C` (`C ⊆ bd S`) in a
chart `c : SurfChart S` at `x ∈ C ∩ c.U`: locally near `x`, `t ↦ (c.j (φ (ee (u₀ + t))).1).im` is
strictly increasing. -/
def cuffPos (c : SurfChart S) {C : Set S} (φ : Circle ≃ₜ C) (x : S) : Prop :=
  ∃ (u₀ δ : ℝ), 0 < δ ∧ (φ (ee u₀)).1 = x ∧
    (∀ t ∈ Icc (-δ) δ, (φ (ee (u₀ + t))).1 ∈ c.U) ∧
    StrictMonoOn (fun t => (c.j (φ (ee (u₀ + t))).1).im) (Icc (-δ) δ)

/-- Every point `x ∈ C ∩ c.U` (`C ⊆ bd S`) has a small interval `[-δ, δ]` on which
`t ↦ (c.j (φ (ee (u₀ + t))).1).im` is either strictly increasing or strictly decreasing. -/
theorem cuff_im_mono_or_anti {c : SurfChart S} {C : Set S} (hC : C ⊆ bd S) (φ : Circle ≃ₜ C)
    {x : S} (hxC : x ∈ C) (hxU : x ∈ c.U) :
    ∃ (u₀ δ : ℝ), 0 < δ ∧ δ < 1 / 4 ∧ (φ (ee u₀)).1 = x ∧
      (∀ t ∈ Icc (-δ) δ, (φ (ee (u₀ + t))).1 ∈ c.U) ∧
      (StrictMonoOn (fun t => (c.j (φ (ee (u₀ + t))).1).im) (Icc (-δ) δ) ∨
        StrictAntiOn (fun t => (c.j (φ (ee (u₀ + t))).1).im) (Icc (-δ) δ)) := by
  obtain ⟨u₀, hu₀⟩ := ee_surjective (φ.symm ⟨x, hxC⟩)
  have hx0 : (φ (ee u₀)).1 = x := by rw [hu₀]; simp
  let γ : ℝ → S := fun t => (φ (ee (u₀ + t))).1
  have hγc : Continuous γ := continuous_subtype_val.comp (φ.continuous.comp (continuous_ee.comp (continuous_const.add continuous_id)))
  have hmem : γ ⁻¹' c.U ∈ 𝓝 (0 : ℝ) := hγc.continuousAt.preimage_mem_nhds (c.hU.mem_nhds (by simpa [γ] using hx0 ▸ hxU))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hmem
  set δ := min (r / 2) (1 / 8)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ4 : δ < 1 / 4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδU : ∀ t ∈ Icc (-δ) δ, γ t ∈ c.U := fun t ht => hrsub (by
    rw [mem_ball, Real.dist_eq, sub_zero]
    have h1 : |t| ≤ δ := abs_le.mpr ht
    have h2 : δ ≤ r / 2 := min_le_left _ _
    linarith)
  have hre : ∀ t ∈ Icc (-δ) δ, (c.j (γ t)).re = 0 := fun t ht =>
    (c.mem_bd_iff (hδU t ht)).mp (hC (φ _).2)
  have him_c : ContinuousOn (fun t => (c.j (γ t)).im) (Icc (-δ) δ) :=
    Complex.continuous_im.comp_continuousOn (c.hj.comp hγc.continuousOn hδU)
  have him_i : InjOn (fun t => (c.j (γ t)).im) (Icc (-δ) δ) := by
    intro s hs t ht he
    have hcz : c.j (γ s) = c.j (γ t) := Complex.ext ((hre s hs).trans (hre t ht).symm) he
    have hγeq : γ s = γ t := c.injOn_j (hδU s hs) (hδU t ht) hcz
    have hee : ee (u₀ + s) = ee (u₀ + t) := φ.injective (Subtype.ext hγeq)
    obtain ⟨k, hk⟩ := ee_eq_iff.mp hee
    have h1 : |s - t| < 1 := by
      rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2, hδ4]
    have h2 : (k : ℝ) = s - t := by linarith
    have hk0 : k = 0 := by
      have : |(k : ℝ)| < 1 := h2 ▸ h1
      have : |k| < 1 := by exact_mod_cast this
      exact Int.abs_lt_one_iff.mp this
    rw [hk0] at h2; simp at h2; linarith
  exact ⟨u₀, δ, hδ, hδ4, hx0, hδU, him_c.strictMonoOn_of_injOn_Icc' (by linarith) him_i⟩

/-- Positive boundary parameterization of a closed square `[0, 2 * L] × [a - L, a + L]` (`L > 0`),
going counterclockwise: on the left edge `Re = 0`, positive order is decreasing `Im`. -/
private theorem rect_isPosParam (a : ℝ) {L : ℝ} (hL : 0 < L) :
    let R : Set ℂ := Icc 0 (2 * L) ×ℂ Icc (a - L) (a + L)
    ∃ φ : Circle → ℂ, IsPosParam R φ ∧
      ∀ s₁ s₂ s₃ : ℝ, a - L < s₃ → s₃ < s₂ → s₂ < s₁ → s₁ < a + L →
        ∃ w₁ w₂ w₃ : Circle, CircleCyclic w₁ w₂ w₃ ∧
          φ w₁ = (s₁ : ℂ) * Complex.I ∧ φ w₂ = (s₂ : ℂ) * Complex.I ∧ φ w₃ = (s₃ : ℂ) * Complex.I := by
  intro R
  let p : ℂ := (L : ℂ) + (a : ℂ) * Complex.I
  let ρ : Circle → ℝ := fun w => L / max |(w : ℂ).re| |(w : ℂ).im|
  have hmax_pos : ∀ w : Circle, 0 < max |(w : ℂ).re| |(w : ℂ).im| := fun w => by
    by_contra h
    push Not at h
    have h1 : (w : ℂ).re = 0 := abs_nonpos_iff.mp ((le_max_left _ _).trans h)
    have h2 : (w : ℂ).im = 0 := abs_nonpos_iff.mp ((le_max_right _ _).trans h)
    exact Circle.coe_ne_zero w (Complex.ext h1 h2)
  have hρ_pos : ∀ w : Circle, 0 < ρ w := fun w => div_pos hL (hmax_pos w)
  have hρ_c : Continuous ρ :=
    continuous_const.div (((Complex.continuous_re.comp continuous_induced_dom).abs).max
      ((Complex.continuous_im.comp continuous_induced_dom).abs)) (fun w => (hmax_pos w).ne')
  let φ : Circle → ℂ := fun w => p + (ρ w : ℂ) * (w : ℂ)
  have hφ_c : Continuous φ := continuous_const.add ((Complex.continuous_ofReal.comp hρ_c).mul continuous_induced_dom)
  have hφ_i : Injective φ := by
    intro w₁ w₂ he
    have h1 : (ρ w₁ : ℂ) * (w₁ : ℂ) = (ρ w₂ : ℂ) * (w₂ : ℂ) := by linear_combination he
    have hn : ρ w₁ = ρ w₂ := by
      have := congrArg norm h1
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρ_pos _), Circle.norm_coe] using this
    rw [hn] at h1
    exact Circle.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (hρ_pos w₂).ne') h1)
  obtain ⟨hRdisc, hRbd⟩ := isClosedDisc_rect (by linarith : (0 : ℝ) < 2 * L) (by linarith : a - L < a + L)
  have hR_iff : ∀ z : ℂ, z ∈ R ↔ |z.re - L| ≤ L ∧ |z.im - a| ≤ L := fun z => by
    simp only [R, Complex.mem_reProdIm, mem_Icc, abs_le]
    constructor <;> rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ <;> constructor <;> constructor <;> linarith
  have hR_int : ∀ z : ℂ, z ∈ interior R ↔ |z.re - L| < L ∧ |z.im - a| < L := fun z => by
    have hopen : IsOpen (Ioo 0 (2 * L) ×ℂ Ioo (a - L) (a + L)) :=
      (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
    constructor
    · intro hz
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
      have hsub : ∀ d : ℂ, ‖d‖ < ε → z + d ∈ R := fun d hd => interior_subset (hball (by simpa [mem_ball, dist_eq_norm] using hd))
      have hε2 : ‖((ε / 2 : ℝ) : ℂ)‖ < ε := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]; exact half_lt_self hε
      have hε2i : ‖((ε / 2 : ℝ) : ℂ) * Complex.I‖ < ε := by
        rw [norm_mul, Complex.norm_I, mul_one]; exact hε2
      have h1 := (hR_iff (z + ((ε / 2 : ℝ) : ℂ))).mp (hsub _ hε2)
      have h2 := (hR_iff (z + (-((ε / 2 : ℝ) : ℂ)))).mp (hsub _ (by rwa [norm_neg]))
      have h3 := (hR_iff (z + ((ε / 2 : ℝ) : ℂ) * Complex.I)).mp (hsub _ hε2i)
      have h4 := (hR_iff (z + (-(((ε / 2 : ℝ) : ℂ) * Complex.I)))).mp (hsub _ (by rwa [norm_neg]))
      simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, add_zero,
        Complex.add_im, Complex.neg_im, Complex.mul_im, mul_one, abs_le] at h1 h2 h3 h4
      rw [abs_lt, abs_lt]
      constructor <;> constructor <;> linarith
    · rintro ⟨h1, h2⟩
      rw [abs_lt] at h1 h2
      refine mem_interior.mpr ⟨Ioo 0 (2 * L) ×ℂ Ioo (a - L) (a + L), fun w hw => ?_, hopen, ?_⟩
      · obtain ⟨hw1, hw2⟩ := Complex.mem_reProdIm.mp hw
        exact Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self hw1, Ioo_subset_Icc_self hw2⟩
      · exact Complex.mem_reProdIm.mpr ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hfr_iff : ∀ z : ℂ, z ∈ discBd R ↔ max |z.re - L| |z.im - a| = L := fun z => by
    rw [hRbd, (isCompact_Icc.reProdIm isCompact_Icc).isClosed.frontier_eq, Set.mem_sdiff, hR_iff, hR_int]
    constructor
    · rintro ⟨⟨h1, h2⟩, hni⟩
      refine le_antisymm (max_le h1 h2) ?_
      by_contra hlt; push Not at hlt
      exact hni ⟨lt_of_le_of_lt (le_max_left _ _) hlt, lt_of_le_of_lt (le_max_right _ _) hlt⟩
    · intro hmax
      refine ⟨⟨(le_max_left _ _).trans hmax.le, (le_max_right _ _).trans hmax.le⟩, fun ⟨h1, h2⟩ => ?_⟩
      have := max_lt h1 h2; linarith
  have hφ_r : range φ = discBd R := by
    ext z
    rw [hfr_iff]
    constructor
    · rintro ⟨w, rfl⟩
      have hre : (φ w).re - L = ρ w * (w : ℂ).re := by simp [φ, p]
      have him : (φ w).im - a = ρ w * (w : ℂ).im := by simp [φ, p]
      rw [hre, him, abs_mul, abs_mul, abs_of_pos (hρ_pos w), ← mul_max_of_nonneg _ _ (hρ_pos w).le]
      exact div_mul_cancel₀ L (hmax_pos w).ne'
    · intro hmax
      have hz0 : z - p ≠ 0 := by
        intro he
        have hre : z.re = L := by have := congrArg Complex.re he; simp [p] at this; linarith
        have him : z.im = a := by have := congrArg Complex.im he; simp [p] at this; linarith
        rw [hre, him, sub_self, sub_self, abs_zero, max_self] at hmax; linarith
      set w : Circle := unitC (z - p) hz0
      refine ⟨w, ?_⟩
      have hwn : ((‖z - p‖ : ℝ) : ℂ) * (w : ℂ) = z - p := norm_mul_unitC hz0
      have hre : ‖z - p‖ * (w : ℂ).re = z.re - L := by
        have := congrArg Complex.re hwn; simpa [p] using this
      have him : ‖z - p‖ * (w : ℂ).im = z.im - a := by
        have := congrArg Complex.im hwn; simpa [p] using this
      have hρ_eq : ρ w = ‖z - p‖ := by
        dsimp only [ρ]
        rw [div_eq_iff (hmax_pos w).ne']
        have h1 : ‖z - p‖ * max |(w : ℂ).re| |(w : ℂ).im| = max |z.re - L| |z.im - a| := by
          rw [mul_max_of_nonneg _ _ (norm_nonneg _), ← abs_of_pos (norm_pos_iff.mpr hz0),
            ← abs_mul, ← abs_mul, hre, him]
        rw [h1, hmax]
      show p + (ρ w : ℂ) * (w : ℂ) = z
      rw [hρ_eq, hwn]; ring
  have hwind : wind φ p = 2 * Real.pi := by
    let cl : ℝ → ℝ := fun u => max 0 (min u 1)
    let F : ℝ → Circle → ℂ := fun u w => p + (((1 - cl u) * ρ w + cl u * L : ℝ) : ℂ) * (w : ℂ)
    have hFc : Continuous fun q : ℝ × Circle => F q.1 q.2 := by unfold F cl; fun_prop
    have hne : ∀ u w, F u w ≠ p := fun u w h => by
      have h1 : (((1 - cl u) * ρ w + cl u * L : ℝ) : ℂ) * (w : ℂ) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h1 with h2 | h2
      · have h3 : (1 - cl u) * ρ w + cl u * L = 0 := Complex.ofReal_eq_zero.mp h2
        have hc0 : 0 ≤ cl u := le_max_left _ _
        have hc1 : cl u ≤ 1 := max_le zero_le_one (min_le_right _ _)
        have hρp := hρ_pos w
        rcases eq_or_lt_of_le hc0 with hc0' | hc0'
        · rw [← hc0'] at h3; linarith
        · nlinarith
      · exact Circle.coe_ne_zero w h2
    have hh := wind_eq_of_family hFc continuous_const hne 0 1
    have h0 : cl 0 = 0 := by simp [cl]
    have h1 : cl 1 = 1 := by simp [cl]
    have hF0 : F 0 = φ := by funext w; simp [F, h0, φ]
    have hF1 : F 1 = fun w : Circle => p + (L : ℂ) * (w : ℂ) := by funext w; simp [F, h1]
    rw [hF0, hF1] at hh
    rw [hh, wind_circle_pos p hL]
  have hp_int : p ∈ discInt R := by
    rw [← interior_eq_discInt_complex hRdisc, hR_int]
    simp [p, hL]
  have hpos : IsPosParam R φ := by
    rcases isPosParam_or_inv hRdisc hφ_c hφ_i hφ_r with h | h
    · exact h
    · exfalso
      have h1 := h.2.2.2 p hp_int
      have hoff : ∀ w, φ w ≠ p := fun w he => hp_int.2 (hφ_r ▸ (he ▸ mem_range_self w))
      rw [wind_inv hφ_c hoff, hwind] at h1
      linarith [Real.pi_pos]
  refine ⟨φ, hpos, fun s₁ s₂ s₃ h3 h32 h21 h1 => ?_⟩
  have hangle : ∀ s : ℝ, a - L < s → s < a + L →
      let θ := Real.pi - Real.arctan ((s - a) / L)
      Real.pi / 2 < θ ∧ θ < 3 * Real.pi / 2 ∧ φ (Circle.exp θ) = (s : ℂ) * Complex.I := by
    intro s hs1 hs2 θ
    have harc_lo : -(Real.pi / 2) < Real.arctan ((s - a) / L) := Real.neg_pi_div_two_lt_arctan _
    have harc_hi : Real.arctan ((s - a) / L) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    refine ⟨by dsimp only [θ]; linarith, by dsimp only [θ]; linarith, ?_⟩
    set α := Real.arctan ((s - a) / L)
    have hcos_pos : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨harc_lo, harc_hi⟩
    have htan : Real.tan α = (s - a) / L := Real.tan_arctan _
    have hcre : ((Circle.exp θ : Circle) : ℂ).re = - Real.cos α := by
      rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
      exact Real.cos_pi_sub α
    have hcim : ((Circle.exp θ : Circle) : ℂ).im = Real.sin α := by
      rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
      exact Real.sin_pi_sub α
    have hle_im : |Real.sin α| ≤ Real.cos α := by
      have h1' : |Real.tan α| ≤ 1 := by
        rw [htan, abs_div, abs_of_pos hL, div_le_one hL, abs_le]
        exact ⟨by linarith, by linarith⟩
      rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcos_pos, div_le_one hcos_pos] at h1'
      exact h1'
    have hmax_eq : max |((Circle.exp θ : Circle) : ℂ).re| |((Circle.exp θ : Circle) : ℂ).im| = Real.cos α := by
      rw [hcre, hcim, abs_neg, abs_of_pos hcos_pos]
      exact max_eq_left hle_im
    have hρ_val : ρ (Circle.exp θ) = L / Real.cos α := by dsimp only [ρ]; rw [hmax_eq]
    apply Complex.ext
    · simp only [φ, p, hρ_val, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero, hcre]
      field_simp [hcos_pos.ne']; ring
    · simp only [φ, p, hρ_val, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, hcim]
      have hsin : Real.sin α / Real.cos α = (s - a) / L := by rw [← Real.tan_eq_sin_div_cos, htan]
      have : L / Real.cos α * Real.sin α = L * (Real.sin α / Real.cos α) := by ring
      rw [this, hsin]; field_simp [hL.ne']; ring
  obtain ⟨hθ1_lo, hθ1_hi, hφ1⟩ := hangle s₁ (by linarith) h1
  obtain ⟨hθ2_lo, hθ2_hi, hφ2⟩ := hangle s₂ (by linarith) (by linarith)
  obtain ⟨hθ3_lo, hθ3_hi, hφ3⟩ := hangle s₃ h3 (by linarith)
  have h12 : Real.pi - Real.arctan ((s₁ - a) / L) < Real.pi - Real.arctan ((s₂ - a) / L) := by
    have := Real.arctan_strictMono (div_lt_div_of_pos_right (by linarith : s₂ - a < s₁ - a) hL)
    linarith
  have h23 : Real.pi - Real.arctan ((s₂ - a) / L) < Real.pi - Real.arctan ((s₃ - a) / L) := by
    have := Real.arctan_strictMono (div_lt_div_of_pos_right (by linarith : s₃ - a < s₂ - a) hL)
    linarith
  exact ⟨Circle.exp (Real.pi - Real.arctan ((s₁ - a) / L)),
    Circle.exp (Real.pi - Real.arctan ((s₂ - a) / L)),
    Circle.exp (Real.pi - Real.arctan ((s₃ - a) / L)),
    circleCyclic_exp_of_lt h12 h23 (by linarith), hφ1, hφ2, hφ3⟩

/-- Comparing `IsPosParam` of `g '' R` with `IsPosLocal g` at the center of a square `R`. -/
private theorem isPosParam_image_rect_iff {g : ℂ → ℂ} {a L : ℝ} (hL : 0 < L)
    (hc : ContinuousOn g (Icc 0 (2 * L) ×ℂ Icc (a - L) (a + L)))
    (hi : InjOn g (Icc 0 (2 * L) ×ℂ Icc (a - L) (a + L)))
    {φ : Circle → ℂ} (hφ : IsPosParam (Icc 0 (2 * L) ×ℂ Icc (a - L) (a + L)) φ) :
    IsPosParam (g '' (Icc 0 (2 * L) ×ℂ Icc (a - L) (a + L))) (g ∘ φ) ↔
      IsPosLocal g ((L : ℂ) + (a : ℂ) * Complex.I) := by
  classical
  set R : Set ℂ := Icc 0 (2 * L) ×ℂ Icc (a - L) (a + L)
  set p : ℂ := (L : ℂ) + (a : ℂ) * Complex.I
  obtain ⟨hR, hRbd⟩ := isClosedDisc_rect (by linarith : (0 : ℝ) < 2 * L) (by linarith : a - L < a + L)
  have : CompactSpace R := isCompact_iff_compactSpace.mp (isCompact_Icc.reProdIm isCompact_Icc)
  let gR : R → ℂ := R.domRestrict g
  let eR : R ≃ₜ range gR := ((continuousOn_iff_continuous_domRestrict.mp hc).isClosedEmbedding
    (fun x y h => Subtype.ext (hi x.2 y.2 h))).isEmbedding.toHomeomorph
  have hrange : range gR = g '' R := by
    ext y; exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
  let g' : ℂ → ℂ := fun y => if hy : y ∈ range gR then (eR.symm ⟨y, hy⟩).1 else 0
  have hg'c : ContinuousOn g' (g '' R) := by
    rw [← hrange, continuousOn_iff_continuous_domRestrict]
    have : (range gR).domRestrict g' = fun y : range gR => (eR.symm y).1 := by
      funext y; show (if hy : y.1 ∈ range gR then (eR.symm ⟨y.1, hy⟩).1 else 0) = _
      rw [dite_eq_left y.2]
    rw [this]; exact continuous_subtype_val.comp eR.symm.continuous
  have hg'l : LeftInvOn g' g R := fun z hz => by
    have hm : g z ∈ range gR := ⟨⟨z, hz⟩, rfl⟩
    show (if hy : g z ∈ range gR then (eR.symm ⟨g z, hy⟩).1 else 0) = z
    rw [dite_eq_left hm]; exact congrArg Subtype.val (eR.symm_apply_apply ⟨z, hz⟩)
  obtain ⟨hD, hDb⟩ := hR.image hc hg'c hg'l
  set ρ := L / 2
  have hρ : 0 < ρ := by positivity
  have hB_in : closedBall p ρ ⊆ discInt R := by
    rw [← interior_eq_discInt_complex hR]
    have hopen : IsOpen (Ioo 0 (2 * L) ×ℂ Ioo (a - L) (a + L)) :=
      (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
    intro z hz
    refine mem_interior.mpr ⟨Ioo 0 (2 * L) ×ℂ Ioo (a - L) (a + L), fun w hw =>
      Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1,
        Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩, hopen, ?_⟩
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre : |z.re - L| ≤ L / 2 := by
      have := Complex.abs_re_le_norm (z - p)
      simp only [Complex.sub_re, p, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_self, add_zero] at this
      dsimp only [ρ] at hz; linarith
    have him : |z.im - a| ≤ L / 2 := by
      have := Complex.abs_im_le_norm (z - p)
      simp only [Complex.sub_im, p, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at this
      dsimp only [ρ] at hz; linarith
    rw [abs_le] at hre him
    exact Complex.mem_reProdIm.mpr ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨hB, hBb⟩ := isClosedDisc_closedBall_of_pos p hρ
  let qFun : Circle → discBd (closedBall p ρ) := fun w =>
    ⟨p + (ρ : ℂ) * (w : ℂ), by
      rw [hBb, mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hρ, Circle.norm_coe, mul_one]⟩
  have hqc : Continuous qFun := Continuous.subtype_mk (by fun_prop) _
  have hqi : Injective qFun := fun x y h => by
    have h1 : p + (ρ : ℂ) * (x : ℂ) = p + (ρ : ℂ) * (y : ℂ) := congrArg Subtype.val h
    exact Circle.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hρ.ne') (by linear_combination h1))
  have hqs : Surjective qFun := fun ⟨y, hy⟩ => by
    rw [hBb, mem_sphere, dist_eq_norm] at hy
    have hy0 : y - p ≠ 0 := by intro h; simp [h] at hy; linarith
    refine ⟨unitC (y - p) hy0, Subtype.ext ?_⟩
    show p + (ρ : ℂ) * (unitC (y - p) hy0 : ℂ) = y
    rw [← hy, norm_mul_unitC hy0]; ring
  let q : Circle ≃ₜ discBd (closedBall p ρ) :=
    hqc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective qFun ⟨hqi, hqs⟩)
  obtain ⟨c, c', hcc, -, hcm, -, hcl, -, hcin, hcs, hcp⟩ := exists_disc_collar hB hR hB_in q
  have hc_inj : InjOn c (closedBall 0 2) := fun u hu v hv he => by rw [← hcl hu, ← hcl hv, he]
  have hc_ne : ∀ (t : ℝ) (w : Circle), 1 ≤ t → t ≤ 2 → c ((t : ℂ) * (w : ℂ)) ≠ p := by
    intro t w ht1 ht2 he
    have hm2 : (t : ℂ) * (w : ℂ) ∈ closedBall (0 : ℂ) 2 := by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), Circle.norm_coe, mul_one]; exact ht2
    rcases eq_or_lt_of_le ht1 with rfl | hgt
    · simp only [Complex.ofReal_one, one_mul, hcp] at he
      have : (q w).1 ∈ sphere p ρ := hBb ▸ (q w).2
      rw [he, mem_sphere_iff_norm, sub_self, norm_zero] at this; linarith
    · obtain ⟨u, hu, hue⟩ : p ∈ c '' closedBall 0 1 := by rw [hcin]; exact mem_closedBall_self hρ.le
      have h1 := hc_inj hm2 (closedBall_subset_closedBall (by norm_num) hu) (he.trans hue.symm)
      have hn1 : ‖(t : ℂ) * (w : ℂ)‖ = t := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), Circle.norm_coe, mul_one]
      have hn2 : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp hu
      rw [h1] at hn1; linarith
  -- Homotopy `t ↦ c (t * w)` on `[1, 2]` gives `ψ(w) := c (2 * w)` is `IsPosParam R ψ` and
  -- `wind (g ∘ ψ) (g p) = wind (fun w => g (p + ρ * w)) (g p)`.
  let cl : ℝ → ℝ := fun u => max 1 (min u 2)
  have hcl_m : ∀ u, 1 ≤ cl u ∧ cl u ≤ 2 := fun u => ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  have hcl_b : ∀ x : ℝ × Circle, (cl x.1 : ℂ) * (x.2 : ℂ) ∈ closedBall (0 : ℂ) 2 := fun x => by
    rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [(hcl_m x.1).1]), Circle.norm_coe, mul_one]
    exact (hcl_m x.1).2
  have hF1 : Continuous fun x : ℝ × Circle => c ((cl x.1 : ℂ) * (x.2 : ℂ)) :=
    hcc.comp_continuous (by unfold cl; fun_prop) hcl_b
  let ψ : Circle → ℂ := fun w => c ((2 : ℂ) * (w : ℂ))
  have hψ_sub : ∀ w : Circle, (2 : ℂ) * (w : ℂ) ∈ closedBall (0 : ℂ) 2 := fun w => by
    rw [mem_closedBall_zero_iff, norm_mul, Circle.norm_coe, mul_one]; norm_num
  have hψ_c : Continuous ψ := hcc.comp_continuous (by fun_prop) hψ_sub
  have hψ_i : Injective ψ := fun a b h =>
    Circle.ext (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) (hc_inj (hψ_sub a) (hψ_sub b) h))
  have hψ_r : range ψ = discBd R := by
    rw [← hcs]
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(2 : ℂ) * (w : ℂ), by rw [mem_sphere_zero_iff_norm, norm_mul, Circle.norm_coe, mul_one]; norm_num, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      have hzn : ‖z‖ = 2 := mem_sphere_zero_iff_norm.mp hz
      have hz0 : z ≠ 0 := by intro h; simp [h] at hzn
      refine ⟨unitC z hz0, ?_⟩
      show c ((2 : ℂ) * (unitC z hz0 : ℂ)) = c z
      have h2 : (2 : ℂ) = ((‖z‖ : ℝ) : ℂ) := by rw [hzn]; norm_num
      rw [h2, norm_mul_unitC hz0]
  have hwind_c : wind ψ p = 2 * Real.pi := by
    have hh := wind_eq_of_family (F := fun u (w : Circle) => c ((cl u : ℂ) * (w : ℂ)))
      hF1 continuous_const (fun u w => hc_ne _ w (hcl_m u).1 (hcl_m u).2) 2 1
    have h2 : cl 2 = 2 := by simp [cl]
    have h1 : cl 1 = 1 := by simp [cl]
    simp only [h2, h1, Complex.ofReal_ofNat, Complex.ofReal_one, one_mul, hcp] at hh
    rw [show wind ψ p = wind (fun w : Circle => c ((2 : ℂ) * (w : ℂ))) p from rfl, hh]
    exact wind_circle_pos p hρ
  have hp_int : p ∈ discInt R := hB_in (mem_closedBall_self hρ.le)
  have hψ_pos : IsPosParam R ψ := by
    rcases isPosParam_or_inv hR hψ_c hψ_i hψ_r with h | h
    · exact h
    · exfalso
      have h1 := h.2.2.2 p hp_int
      rw [wind_inv hψ_c (fun w => hc_ne 2 w (by norm_num) le_rfl), hwind_c] at h1
      linarith [Real.pi_pos]
  -- Compare `φ` and `ψ` on `discBd R`: `H := ψ⁻¹ ∘ φ` preserves circle orientation!
  let eφ : Circle ≃ₜ discBd R :=
    (hφ.1.subtype_mk (fun w => hφ.2.2.1 ▸ mem_range_self w)).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective _ ⟨fun a b h => hφ.2.1 (congrArg Subtype.val h), fun ⟨y, hy⟩ => by
        obtain ⟨w, hw⟩ := hφ.2.2.1.symm ▸ hy; exact ⟨w, Subtype.ext hw⟩⟩)
  let eψ : Circle ≃ₜ discBd R :=
    (hψ_c.subtype_mk (fun w => hψ_r ▸ mem_range_self w)).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective _ ⟨fun a b h => hψ_i (congrArg Subtype.val h), fun ⟨y, hy⟩ => by
        obtain ⟨w, hw⟩ := hψ_r.symm ▸ hy; exact ⟨w, Subtype.ext hw⟩⟩)
  let H : Circle ≃ₜ Circle := eφ.trans eψ.symm
  have hH : ∀ w, ψ (H w) = φ w := fun w => congrArg Subtype.val (eψ.apply_symm_apply (eφ w))
  have hH_pos : PreservesCircleOrientation H := preservesCircleOrientation_of_cyclic fun x y z hxyz =>
    order_of_nested hR hR Subset.rfl hφ hψ_pos hxyz (hH x).symm (hH y).symm (hH z).symm
  -- Now apply `g` to the homotopy `c (cl u * w)`!
  have hF2 : Continuous fun x : ℝ × Circle => g (c ((cl x.1 : ℂ) * (x.2 : ℂ))) :=
    hc.comp_continuous hF1 (fun x => hcm (hcl_b x))
  have hF2_ne : ∀ (u : ℝ) (w : Circle), g (c ((cl u : ℂ) * (w : ℂ))) ≠ g p := fun u w h =>
    hc_ne _ w (hcl_m u).1 (hcl_m u).2 (hi (hcm (hcl_b (u, w))) hp_int.1 h)
  have hwind_gψ : wind (g ∘ ψ) (g p) = wind (fun w : Circle => g (p + (ρ : ℂ) * (w : ℂ))) (g p) := by
    have hh := wind_eq_of_family (F := fun u (w : Circle) => g (c ((cl u : ℂ) * (w : ℂ))))
      hF2 continuous_const hF2_ne 2 1
    have h2 : cl 2 = 2 := by simp [cl]
    have h1 : cl 1 = 1 := by simp [cl]
    simp only [h2, h1, Complex.ofReal_ofNat, Complex.ofReal_one, one_mul, hcp] at hh
    exact hh
  have hgψ_c : Continuous (g ∘ ψ) := hc.comp_continuous hψ_c (fun w => hcm (hψ_sub w))
  have hgψ_ne : ∀ w, (g ∘ ψ) w ≠ g p := fun w h =>
    hc_ne 2 w (by norm_num) le_rfl (hi (hcm (hψ_sub w)) hp_int.1 h)
  have hgφ_eq : g ∘ φ = (g ∘ ψ) ∘ H := by funext w; simp [Function.comp_apply, hH]
  have hwind_eq : wind (g ∘ φ) (g p) = wind (fun w : Circle => g (p + (ρ : ℂ) * (w : ℂ))) (g p) := by
    rw [hgφ_eq, wind_comp_preserves hgψ_c hgψ_ne hH_pos, hwind_gψ]
  have hgp_int : g p ∈ discInt (g '' R) := by
    refine ⟨mem_image_of_mem g hp_int.1, fun hmem => ?_⟩
    rw [hDb] at hmem
    obtain ⟨z, hz, he⟩ := hmem
    have := hi (discBd_subset R hz) hp_int.1 he
    subst this; exact hp_int.2 hz
  have hBR : closedBall p ρ ⊆ R := fun z hz => (hB_in hz).1
  rw [isPosLocal_iff_wind_pos hρ (hc.mono hBR) (hi.mono hBR)]
  have hgφ_c : Continuous (g ∘ φ) :=
    hc.comp_continuous hφ.1 (fun w => discBd_subset R (hφ.2.2.1 ▸ mem_range_self w))
  have hgφ_i : Injective (g ∘ φ) := fun x y h =>
    hφ.2.1 (hi (discBd_subset R (hφ.2.2.1 ▸ mem_range_self x))
      (discBd_subset R (hφ.2.2.1 ▸ mem_range_self y)) h)
  have hgφ_r : range (g ∘ φ) = discBd (g '' R) := by
    rw [hDb, range_comp, hφ.2.2.1]
  constructor
  · intro hpos; rw [← hwind_eq]; exact hpos.2.2.2 _ hgp_int
  · intro hpos
    rcases isPosParam_or_inv hD hgφ_c hgφ_i hgφ_r with h | h
    · exact h
    · exfalso
      have h1 := h.2.2.2 _ hgp_int
      have hoff : ∀ w, (g ∘ φ) w ≠ g p := fun w he => hgp_int.2 (hgφ_r ▸ (he ▸ mem_range_self w))
      rw [wind_inv hgφ_c hoff, hwind_eq] at h1
      linarith

/-- **Key boundary transition lemma**: changing half-plane charts from `c₁` to `c₂` at a boundary
point `x ∈ C ∩ c₁.U ∩ c₂.U` flips `cuffPos` precisely when `¬ chartPos c₁ c₂ x`. -/
theorem cuffPos_iff_chartPos {c₁ c₂ : SurfChart S} {C : Set S} (hC : C ⊆ bd S) (φ : Circle ≃ₜ C)
    {x : S} (hxC : x ∈ C) (hx1 : x ∈ c₁.U) (hx2 : x ∈ c₂.U) :
    cuffPos c₂ φ x ↔ (cuffPos c₁ φ x ↔ chartPos c₁ c₂ x) := by
  -- Pick a small rectangle `R₁ = [0, L] × [a - L, a + L]` inside `c₁.j(c₁.U ∩ c₂.U)` around `c₁.j x = a * I`!
  have hxre1 : (c₁.j x).re = 0 := (c₁.mem_bd_iff hx1).mp (hC hxC)
  have hxre2 : (c₂.j x).re = 0 := (c₂.mem_bd_iff hx2).mp (hC hxC)
  set a := (c₁.j x).im
  set b := (c₂.j x).im
  have hjx1 : c₁.j x = (a : ℂ) * Complex.I := Complex.ext (by simp [hxre1]) (by simp [a])
  have hjx2 : c₂.j x = (b : ℂ) * Complex.I := Complex.ext (by simp [hxre2]) (by simp [b])
  obtain ⟨r, hr, hBO, hBW, hBo, hxB, hBsub, -, hBconn⟩ :=
    c₁.exists_ball_nbhd (c₁.hU.inter c₂.hU) ⟨hx1, hx2⟩ inter_subset_left
  set L := r / 4
  have hL : 0 < L := by positivity
  set R₁ : Set ℂ := Icc 0 (2 * L) ×ℂ Icc (a - L) (a + L)
  have hR₁_ball : R₁ ⊆ ball (c₁.j x) r ∩ halfPlane := fun z hz => by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := Complex.mem_reProdIm.mp hz
    refine ⟨?_, h1⟩
    rw [mem_ball, dist_eq_norm, hjx1]
    have hsq : ‖z - (a : ℂ) * Complex.I‖ ^ 2 ≤ (2 * L) ^ 2 + L ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, sub_self, sub_zero, Complex.sub_im,
        Complex.mul_im, mul_one, add_zero]
      nlinarith
    have hlt : (2 * L) ^ 2 + L ^ 2 < r ^ 2 := by dsimp only [L]; nlinarith
    nlinarith [norm_nonneg (z - (a : ℂ) * Complex.I)]
  have hR₁_dom : R₁ ⊆ c₁.O ∩ halfPlane := fun z hz => ⟨hBO (hR₁_ball hz).1, (hR₁_ball hz).2⟩
  let g : ℂ → ℂ := c₂.j ∘ c₁.k
  have hgc : ContinuousOn g R₁ := c₂.hj.comp (c₁.hk.mono hR₁_dom) (fun z hz => (hBW z (hR₁_ball hz)).2)
  have hgi : InjOn g R₁ := fun z₁ hz₁ z₂ hz₂ he =>
    c₁.injOn_k (hR₁_dom hz₁) (hR₁_dom hz₂) (c₂.injOn_j (hBW z₁ (hR₁_ball hz₁)).2 (hBW z₂ (hR₁_ball hz₂)).2 he)
  have hgR_sub : g '' R₁ ⊆ halfPlane := by
    rintro _ ⟨z, hz, rfl⟩; exact (c₂.hm (hBW z (hR₁_ball hz)).2).2
  have hgR_bdd : Bornology.IsBounded (g '' R₁) :=
    ((isCompact_Icc.reProdIm isCompact_Icc).image_of_continuousOn hgc).isBounded
  obtain ⟨M₀, hM₀⟩ := (Metric.isBounded_iff_subset_closedBall (c₂.j x)).mp hgR_bdd
  set M := max M₀ 1 + 1
  have hM : 0 < M := by positivity
  set R₂ : Set ℂ := Icc 0 (2 * M) ×ℂ Icc (b - M) (b + M)
  have hgR_in : g '' R₁ ⊆ R₂ := by
    rintro y ⟨z, hz, rfl⟩
    have hdist : ‖g z - c₂.j x‖ ≤ M₀ := by simpa [mem_closedBall, dist_eq_norm] using hM₀ ⟨z, hz, rfl⟩
    have hre_ge : 0 ≤ (g z).re := hgR_sub ⟨z, hz, rfl⟩
    have hre_le : (g z).re ≤ M₀ := by
      have := (Complex.abs_re_le_norm (g z - c₂.j x)).trans hdist
      rw [Complex.sub_re, hxre2, sub_zero] at this
      exact (le_abs_self _).trans this
    have him_le : |(g z).im - b| ≤ M₀ := by
      have := (Complex.abs_im_le_norm (g z - c₂.j x)).trans hdist
      simpa [b] using this
    rw [abs_le] at him_le
    exact Complex.mem_reProdIm.mpr ⟨⟨hre_ge, by dsimp only [M]; linarith [le_max_left M₀ 1, le_max_right M₀ 1]⟩,
      ⟨by dsimp only [M]; linarith [le_max_left M₀ 1], by dsimp only [M]; linarith [le_max_left M₀ 1]⟩⟩
  set p : ℂ := (L : ℂ) + (a : ℂ) * Complex.I
  have hpR₁ : p ∈ R₁ := Complex.mem_reProdIm.mpr
    ⟨⟨by simp [p]; exact hL.le, by simp [p]; linarith⟩,
     ⟨by simp [p]; linarith, by simp [p]; linarith⟩⟩
  have hkpB : c₁.k p ∈ c₁.U ∩ c₁.j ⁻¹' ball (c₁.j x) r := by
    refine ⟨c₁.hk' (hR₁_dom hpR₁), ?_⟩
    show c₁.j (c₁.k p) ∈ ball (c₁.j x) r; rw [c₁.hr (hR₁_dom hpR₁)]; exact (hR₁_ball hpR₁).1
  have hkpInt : c₁.k p ∉ bd S := by
    rw [c₁.not_mem_bd_iff hkpB.1, c₁.hr (hR₁_dom hpR₁)]; simp [p, hL]
  have hchart_iff : chartPos c₁ c₂ x ↔ IsPosLocal g p := by
    rw [chartPos_iff_of_int hBo hxB hkpB hkpInt hBsub hBconn, c₁.hr (hR₁_dom hpR₁)]
  have hseg_re : ∀ s ∈ Icc (a - L) (a + L), (g ((s : ℂ) * Complex.I)).re = 0 := fun s hs => by
    have hm : (s : ℂ) * Complex.I ∈ R₁ := Complex.mem_reProdIm.mpr ⟨by simp; linarith, by simpa using hs⟩
    have hbd_k : c₁.k ((s : ℂ) * Complex.I) ∈ bd S := by
      rw [c₁.mem_bd_iff (c₁.hk' (hR₁_dom hm)), c₁.hr (hR₁_dom hm)]; simp
    exact (c₂.mem_bd_iff (hBW _ (hR₁_ball hm)).2).mp hbd_k
  have hg_im_mono_or_anti :
      StrictMonoOn (fun s : ℝ => (g ((s : ℂ) * Complex.I)).im) (Icc (a - L) (a + L)) ∨
        StrictAntiOn (fun s : ℝ => (g ((s : ℂ) * Complex.I)).im) (Icc (a - L) (a + L)) := by
    have h1 : ContinuousOn (fun s : ℝ => (g ((s : ℂ) * Complex.I)).im) (Icc (a - L) (a + L)) :=
      Complex.continuous_im.comp_continuousOn (hgc.comp (by fun_prop) (fun s hs =>
        Complex.mem_reProdIm.mpr ⟨by simp; linarith, by simpa using hs⟩))
    have h2 : InjOn (fun s : ℝ => (g ((s : ℂ) * Complex.I)).im) (Icc (a - L) (a + L)) := fun s₁ hs₁ s₂ hs₂ he => by
      have hm1 : (s₁ : ℂ) * Complex.I ∈ R₁ := Complex.mem_reProdIm.mpr ⟨by simp; linarith, by simpa using hs₁⟩
      have hm2 : (s₂ : ℂ) * Complex.I ∈ R₁ := Complex.mem_reProdIm.mpr ⟨by simp; linarith, by simpa using hs₂⟩
      have heq := hgi hm1 hm2 (Complex.ext ((hseg_re s₁ hs₁).trans (hseg_re s₂ hs₂).symm) he)
      have := congrArg Complex.im heq; simpa using this
    exact h1.strictMonoOn_of_injOn_Icc' (by linarith) h2
  obtain ⟨φ₁, hφ₁, htri₁⟩ := rect_isPosParam a hL
  obtain ⟨φ₂, hφ₂, htri₂⟩ := rect_isPosParam b hM
  obtain ⟨hR₁_disc, -⟩ := isClosedDisc_rect (by linarith : (0 : ℝ) < 2 * L) (by linarith : a - L < a + L)
  obtain ⟨hR₂_disc, -⟩ := isClosedDisc_rect (by linarith : (0 : ℝ) < 2 * M) (by linarith : b - M < b + M)
  have hgR_disc : IsClosedDisc (g '' R₁) := by
    classical
    have : CompactSpace R₁ := isCompact_iff_compactSpace.mp (isCompact_Icc.reProdIm isCompact_Icc)
    let gR : R₁ → ℂ := R₁.domRestrict g
    let eR : R₁ ≃ₜ range gR := ((continuousOn_iff_continuous_domRestrict.mp hgc).isClosedEmbedding
      (fun x y h => Subtype.ext (hgi x.2 y.2 h))).isEmbedding.toHomeomorph
    have hr' : range gR = g '' R₁ := by
      ext y; exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
    let g' : ℂ → ℂ := fun y => if hy : y ∈ range gR then (eR.symm ⟨y, hy⟩).1 else 0
    have hg'c : ContinuousOn g' (g '' R₁) := by
      rw [← hr', continuousOn_iff_continuous_domRestrict]
      have : (range gR).domRestrict g' = fun y : range gR => (eR.symm y).1 := by
        funext y; show (if hy : y.1 ∈ range gR then (eR.symm ⟨y.1, hy⟩).1 else 0) = _
        rw [dite_eq_left y.2]
      rw [this]; exact continuous_subtype_val.comp eR.symm.continuous
    have hg'l : LeftInvOn g' g R₁ := fun z hz => by
      have hm : g z ∈ range gR := ⟨⟨z, hz⟩, rfl⟩
      show (if hy : g z ∈ range gR then (eR.symm ⟨g z, hy⟩).1 else 0) = z
      rw [dite_eq_left hm]; exact congrArg Subtype.val (eR.symm_apply_apply ⟨z, hz⟩)
    exact (hR₁_disc.image hgc hg'c hg'l).1
  have hpos_iff_mono : IsPosLocal g p ↔
      StrictMonoOn (fun s : ℝ => (g ((s : ℂ) * Complex.I)).im) (Icc (a - L) (a + L)) := by
    rw [← isPosParam_image_rect_iff hL hgc hgi hφ₁]
    set s₁ := a + L / 2 with hs₁_def
    set s₂ := a with hs₂_def
    set s₃ := a - L / 2 with hs₃_def
    obtain ⟨w₁, w₂, w₃, hcyc, hw₁, hw₂, hw₃⟩ := htri₁ s₁ s₂ s₃ (by linarith) (by linarith) (by linarith) (by linarith)
    have hs1 : s₁ ∈ Icc (a - L) (a + L) := ⟨by linarith, by linarith⟩
    have hs2 : s₂ ∈ Icc (a - L) (a + L) := ⟨by linarith, by linarith⟩
    have hs3 : s₃ ∈ Icc (a - L) (a + L) := ⟨by linarith, by linarith⟩
    have ht_eq : ∀ s ∈ Icc (a - L) (a + L), g ((s : ℂ) * Complex.I) = ((g ((s : ℂ) * Complex.I)).im : ℂ) * Complex.I :=
      fun s hs => Complex.ext (by simp [hseg_re s hs]) (by simp)
    have ht_in : ∀ s ∈ Icc (a - L) (a + L), b - M < (g ((s : ℂ) * Complex.I)).im ∧ (g ((s : ℂ) * Complex.I)).im < b + M := by
      intro s hs
      have hm : (s : ℂ) * Complex.I ∈ R₁ := Complex.mem_reProdIm.mpr ⟨by simp; linarith, by simpa using hs⟩
      have hdist : ‖g ((s : ℂ) * Complex.I) - c₂.j x‖ ≤ M₀ := by
        simpa [mem_closedBall, dist_eq_norm] using hM₀ ⟨_, hm, rfl⟩
      have him := (Complex.abs_im_le_norm (g ((s : ℂ) * Complex.I) - c₂.j x)).trans hdist
      simp only [Complex.sub_im] at him
      rw [abs_le] at him
      exact ⟨by dsimp only [M, b]; linarith [le_max_left M₀ 1], by dsimp only [M, b]; linarith [le_max_left M₀ 1]⟩
    rcases hg_im_mono_or_anti with hmono | hanti
    · have ht21 : (g ((s₂ : ℂ) * Complex.I)).im < (g ((s₁ : ℂ) * Complex.I)).im := hmono hs2 hs1 (by linarith)
      have ht32 : (g ((s₃ : ℂ) * Complex.I)).im < (g ((s₂ : ℂ) * Complex.I)).im := hmono hs3 hs2 (by linarith)
      obtain ⟨v₁, v₂, v₃, hcyc2, hv₁, hv₂, hv₃⟩ := htri₂ _ _ _ (ht_in s₃ hs3).1 ht32 ht21 (ht_in s₁ hs1).2
      refine ⟨fun _ => hmono, fun _ => ?_⟩
      have hgφ_c : Continuous (g ∘ φ₁) := hgc.comp_continuous hφ₁.1 (fun w => discBd_subset R₁ (hφ₁.2.2.1 ▸ mem_range_self w))
      have hgφ_i : Injective (g ∘ φ₁) := fun x y h =>
        hφ₁.2.1 (hgi (discBd_subset R₁ (hφ₁.2.2.1 ▸ mem_range_self x)) (discBd_subset R₁ (hφ₁.2.2.1 ▸ mem_range_self y)) h)
      have hgφ_r : range (g ∘ φ₁) = discBd (g '' R₁) := by
        have : IsClosedDisc (g '' R₁) ∧ discBd (g '' R₁) = g '' discBd R₁ := by
          classical
          have : CompactSpace R₁ := isCompact_iff_compactSpace.mp (isCompact_Icc.reProdIm isCompact_Icc)
          let gR : R₁ → ℂ := R₁.domRestrict g
          let eR : R₁ ≃ₜ range gR := ((continuousOn_iff_continuous_domRestrict.mp hgc).isClosedEmbedding
            (fun x y h => Subtype.ext (hgi x.2 y.2 h))).isEmbedding.toHomeomorph
          have hr' : range gR = g '' R₁ := by
            ext y; exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, hy⟩ => ⟨⟨x, hx⟩, hy⟩⟩
          let g' : ℂ → ℂ := fun y => if hy : y ∈ range gR then (eR.symm ⟨y, hy⟩).1 else 0
          have hg'c : ContinuousOn g' (g '' R₁) := by
            rw [← hr', continuousOn_iff_continuous_domRestrict]
            have : (range gR).domRestrict g' = fun y : range gR => (eR.symm y).1 := by
              funext y; show (if hy : y.1 ∈ range gR then (eR.symm ⟨y.1, hy⟩).1 else 0) = _
              rw [dite_eq_left y.2]
            rw [this]; exact continuous_subtype_val.comp eR.symm.continuous
          have hg'l : LeftInvOn g' g R₁ := fun z hz => by
            have hm : g z ∈ range gR := ⟨⟨z, hz⟩, rfl⟩
            show (if hy : g z ∈ range gR then (eR.symm ⟨g z, hy⟩).1 else 0) = z
            rw [dite_eq_left hm]; exact congrArg Subtype.val (eR.symm_apply_apply ⟨z, hz⟩)
          exact hR₁_disc.image hgc hg'c hg'l
        rw [this.2, range_comp, hφ₁.2.2.1]
      rcases isPosParam_or_inv hgR_disc hgφ_c hgφ_i hgφ_r with h | h
      · exact h
      · exfalso
        have hinv := order_of_nested hgR_disc hR₂_disc hgR_in h hφ₂ (circleCyclic_inv hcyc)
          (by show g (φ₁ (w₁⁻¹)⁻¹) = φ₂ v₁; rw [inv_inv, hw₁, hv₁]; exact ht_eq s₁ hs1)
          (by show g (φ₁ (w₃⁻¹)⁻¹) = φ₂ v₃; rw [inv_inv, hw₃, hv₃]; exact ht_eq s₃ hs3)
          (by show g (φ₁ (w₂⁻¹)⁻¹) = φ₂ v₂; rw [inv_inv, hw₂, hv₂]; exact ht_eq s₂ hs2)
        exact not_circleCyclic_both hcyc2 hinv
    · have ht12 : (g ((s₁ : ℂ) * Complex.I)).im < (g ((s₂ : ℂ) * Complex.I)).im := hanti hs2 hs1 (by linarith)
      have ht23 : (g ((s₂ : ℂ) * Complex.I)).im < (g ((s₃ : ℂ) * Complex.I)).im := hanti hs3 hs2 (by linarith)
      obtain ⟨v₃, v₂, v₁, hcyc2, hv₃, hv₂, hv₁⟩ := htri₂ _ _ _ (ht_in s₁ hs1).1 ht12 ht23 (ht_in s₃ hs3).2
      refine ⟨fun hpos => ?_, fun hmono => ?_⟩
      · exfalso
        have hord := order_of_nested hgR_disc hR₂_disc hgR_in hpos hφ₂ hcyc
          (by show g (φ₁ w₁) = φ₂ v₁; rw [hw₁, hv₁]; exact ht_eq s₁ hs1)
          (by show g (φ₁ w₂) = φ₂ v₂; rw [hw₂, hv₂]; exact ht_eq s₂ hs2)
          (by show g (φ₁ w₃) = φ₂ v₃; rw [hw₃, hv₃]; exact ht_eq s₃ hs3)
        obtain ⟨α, β, hα, hαβ, hβ, hv2_eq, hv1_eq⟩ := hcyc2
        have hpi := Real.pi_pos
        have hrev : CircleCyclic v₁ v₃ v₂ := by
          refine ⟨2 * Real.pi - β, 2 * Real.pi - β + α, by linarith, by linarith, by linarith, ?_, ?_⟩
          · rw [hv1_eq, mul_assoc, ← Circle.exp_add]; simp
          · rw [hv1_eq, hv2_eq, mul_assoc, ← Circle.exp_add]
            have : β + (2 * Real.pi - β + α) = α + 2 * Real.pi := by ring
            rw [this, exp_add_two_pi']
        exact not_circleCyclic_both hord hrev
      · exfalso
        have := hmono hs2 hs1 (by linarith)
        linarith
  rw [hchart_iff, hpos_iff_mono]
  obtain ⟨u₀, δ, hδ, hδ4, hx0, hδ1, hmo1⟩ := cuff_im_mono_or_anti hC φ hxC hx1
  let γ : ℝ → S := fun t => (φ (ee (u₀ + t))).1
  have hγc : Continuous γ := continuous_subtype_val.comp (φ.continuous.comp (continuous_ee.comp (continuous_const.add continuous_id)))
  have hmemB : γ ⁻¹' (c₁.U ∩ c₁.j ⁻¹' ball (c₁.j x) L) ∈ 𝓝 (0 : ℝ) := by
    have hopenL : IsOpen (c₁.U ∩ c₁.j ⁻¹' ball (c₁.j x) L) := c₁.hj.isOpen_inter_preimage c₁.hU isOpen_ball
    have h0U : γ 0 ∈ c₁.U := by simp only [γ, add_zero, hx0]; exact hx1
    exact hγc.continuousAt.preimage_mem_nhds (hopenL.mem_nhds ⟨h0U, by simp [γ, hx0, hL]⟩)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hmemB
  set δ' := min δ (ε / 2)
  have hδ' : 0 < δ' := lt_min hδ (half_pos hε)
  have hδ'4 : δ' < 1 / 4 := lt_of_le_of_lt (min_le_left _ _) hδ4
  have hδ'L : ∀ t ∈ Icc (-δ') δ', γ t ∈ c₁.U ∧ (c₁.j (γ t)).im ∈ Icc (a - L) (a + L) := by
    intro t ht
    have hm : γ t ∈ c₁.U ∩ c₁.j ⁻¹' ball (c₁.j x) L := hεsub (by
      rw [mem_ball, Real.dist_eq, sub_zero]
      have h1 : |t| ≤ δ' := abs_le.mpr ht
      have h2 : δ' ≤ ε / 2 := min_le_right _ _; linarith)
    refine ⟨hm.1, ?_⟩
    have hdist : ‖c₁.j (γ t) - c₁.j x‖ < L := by simpa [mem_ball, dist_eq_norm] using hm.2
    have him := (Complex.abs_im_le_norm (c₁.j (γ t) - c₁.j x)).trans hdist.le
    rw [Complex.sub_im, abs_le] at him
    exact ⟨by dsimp only [a]; linarith, by dsimp only [a]; linarith⟩
  have hδ'2 : ∀ t ∈ Icc (-δ') δ', γ t ∈ c₂.U := fun t ht => by
    have hm := hδ'L t ht
    have hre : (c₁.j (γ t)).re = 0 := (c₁.mem_bd_iff hm.1).mp (hC (φ _).2)
    have hmR : c₁.j (γ t) ∈ R₁ := Complex.mem_reProdIm.mpr ⟨by simp [hre]; linarith, hm.2⟩
    have h2 := (hBW _ (hR₁_ball hmR)).2
    rwa [c₁.hl hm.1] at h2
  have hgγ : ∀ t ∈ Icc (-δ') δ', (c₂.j (γ t)).im = (g (((c₁.j (γ t)).im : ℂ) * Complex.I)).im := fun t ht => by
    have hm := hδ'L t ht
    have hre : (c₁.j (γ t)).re = 0 := (c₁.mem_bd_iff hm.1).mp (hC (φ _).2)
    have hce : c₁.j (γ t) = ((c₁.j (γ t)).im : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp)
    show (c₂.j (γ t)).im = (c₂.j (c₁.k (((c₁.j (γ t)).im : ℂ) * Complex.I))).im
    rw [← hce, c₁.hl hm.1]
  have hcuff_iff : ∀ (c : SurfChart S), (∀ t ∈ Icc (-δ') δ', γ t ∈ c.U) →
      (cuffPos c φ x ↔ StrictMonoOn (fun t => (c.j (γ t)).im) (Icc (-δ') δ')) := by
    intro c hγU
    constructor
    · rintro ⟨u₁, δ₁, hδ₁, hx1', -, hmono1⟩
      obtain ⟨k, hk⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext (hx1'.trans hx0.symm)))
      have heq_γ : ∀ t, (φ (ee (u₁ + t))).1 = γ t := fun t => by
        have : ee (u₁ + t) = ee (u₀ + t) := ee_eq_iff.mpr ⟨k, by linarith⟩
        simp [γ, this]
      have hre_c : ∀ t ∈ Icc (-δ') δ', (c.j (γ t)).re = 0 := fun t ht => (c.mem_bd_iff (hγU t ht)).mp (hC (φ _).2)
      have hc_im : ContinuousOn (fun t => (c.j (γ t)).im) (Icc (-δ') δ') :=
        Complex.continuous_im.comp_continuousOn (c.hj.comp hγc.continuousOn hγU)
      have hi_im : InjOn (fun t => (c.j (γ t)).im) (Icc (-δ') δ') := by
        intro s hs t ht he
        have hcz := Complex.ext ((hre_c s hs).trans (hre_c t ht).symm) he
        have hγeq := c.injOn_j (hγU s hs) (hγU t ht) hcz
        obtain ⟨m, hm⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext hγeq))
        have h1 : |s - t| < 1 := by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, ht.1, ht.2, hδ'4]
        have h2 : (m : ℝ) = s - t := by linarith
        have hm0 : m = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast (h2 ▸ h1 : |(m : ℝ)| < 1))
        rw [hm0] at h2; simp at h2; linarith
      rcases hc_im.strictMonoOn_of_injOn_Icc' (by linarith) hi_im with h | h
      · exact h
      · exfalso
        set η := min δ' δ₁
        have hη : 0 < η := lt_min hδ' hδ₁
        have hlt1 : (c.j (γ 0)).im < (c.j (γ η)).im := by
          have := hmono1 ⟨by linarith, hδ₁.le⟩ ⟨by linarith [min_le_right δ' δ₁], min_le_right _ _⟩ hη
          have h0' : (φ (ee u₁)).1 = γ 0 := by simpa using heq_γ 0
          simpa [h0', heq_γ] using this
        have hlt2 : (c.j (γ η)).im < (c.j (γ 0)).im :=
          h ⟨by linarith, hδ'.le⟩ ⟨by linarith [min_le_left δ' δ₁], min_le_left _ _⟩ hη
        linarith
    · exact fun h => ⟨u₀, δ', hδ', hx0, hγU, h⟩
  rw [hcuff_iff c₁ (fun t ht => (hδ'L t ht).1), hcuff_iff c₂ hδ'2]
  have hsubI : Icc (-δ') δ' ⊆ Icc (-δ) δ := Icc_subset_Icc (by linarith [min_le_left δ (ε / 2)]) (min_le_left _ _)
  rcases hmo1 with h1m | h1a <;> rcases hg_im_mono_or_anti with hgm | hga
  · have h1m' := h1m.mono hsubI
    have h2m : StrictMonoOn (fun t => (c₂.j (γ t)).im) (Icc (-δ') δ') := fun s hs t ht hst => by
      dsimp only; rw [hgγ s hs, hgγ t ht]; exact hgm (hδ'L s hs).2 (hδ'L t ht).2 (h1m' hs ht hst)
    exact ⟨fun _ => ⟨fun _ => hgm, fun _ => h1m'⟩, fun _ => h2m⟩
  · have h1m' := h1m.mono hsubI
    have h2a : StrictAntiOn (fun t => (c₂.j (γ t)).im) (Icc (-δ') δ') := fun s hs t ht hst => by
      dsimp only; rw [hgγ s hs, hgγ t ht]; exact hga (hδ'L s hs).2 (hδ'L t ht).2 (h1m' hs ht hst)
    have h2nm : ¬ StrictMonoOn (fun t => (c₂.j (γ t)).im) (Icc (-δ') δ') := fun hm => by
      have h1 := hm ⟨by linarith, hδ'.le⟩ ⟨by linarith, le_rfl⟩ hδ'
      have h2 := h2a ⟨by linarith, hδ'.le⟩ ⟨by linarith, le_rfl⟩ hδ'
      linarith
    have hgnm : ¬ StrictMonoOn (fun s : ℝ => (g ((s : ℂ) * Complex.I)).im) (Icc (a - L) (a + L)) := fun hm => by
      have h1 := hm ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : a < a + L)
      have h2 := hga ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : a < a + L)
      linarith
    tauto
  · have h1a' := h1a.mono hsubI
    have h2a : StrictAntiOn (fun t => (c₂.j (γ t)).im) (Icc (-δ') δ') := fun s hs t ht hst => by
      dsimp only; rw [hgγ s hs, hgγ t ht]; exact hgm (hδ'L t ht).2 (hδ'L s hs).2 (h1a' hs ht hst)
    have h1nm : ¬ StrictMonoOn (fun t => (c₁.j (γ t)).im) (Icc (-δ') δ') := fun hm => by
      have h1 := hm ⟨by linarith, hδ'.le⟩ ⟨by linarith, le_rfl⟩ hδ'
      have h2 := h1a' ⟨by linarith, hδ'.le⟩ ⟨by linarith, le_rfl⟩ hδ'
      linarith
    have h2nm : ¬ StrictMonoOn (fun t => (c₂.j (γ t)).im) (Icc (-δ') δ') := fun hm => by
      have h1 := hm ⟨by linarith, hδ'.le⟩ ⟨by linarith, le_rfl⟩ hδ'
      have h2 := h2a ⟨by linarith, hδ'.le⟩ ⟨by linarith, le_rfl⟩ hδ'
      linarith
    tauto
  · have h1a' := h1a.mono hsubI
    have h2m : StrictMonoOn (fun t => (c₂.j (γ t)).im) (Icc (-δ') δ') := fun s hs t ht hst => by
      dsimp only; rw [hgγ s hs, hgγ t ht]; exact hga (hδ'L t ht).2 (hδ'L s hs).2 (h1a' hs ht hst)
    have h1nm : ¬ StrictMonoOn (fun t => (c₁.j (γ t)).im) (Icc (-δ') δ') := fun hm => by
      have h1 := hm ⟨by linarith, hδ'.le⟩ ⟨by linarith, le_rfl⟩ hδ'
      have h2 := h1a' ⟨by linarith, hδ'.le⟩ ⟨by linarith, le_rfl⟩ hδ'
      linarith
    have hgnm : ¬ StrictMonoOn (fun s : ℝ => (g ((s : ℂ) * Complex.I)).im) (Icc (a - L) (a + L)) := fun hm => by
      have h1 := hm ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : a < a + L)
      have h2 := hga ⟨by linarith, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith : a < a + L)
      linarith
    tauto

/-- Boundary orientation sign in `ZMod 2` of a circle parameterization `φ : Circle ≃ₜ C` at `x ∈ C`
with respect to a chart `c`. -/
noncomputable def cuffSignChart (c : SurfChart S) {C : Set S} (φ : Circle ≃ₜ C) (x : S) : ZMod 2 :=
  open Classical in if cuffPos c φ x then 0 else 1

/-- Boundary orientation sign in `ZMod 2` of `φ : Circle ≃ₜ C` at `x ∈ C` with respect to an atlas `A`. -/
noncomputable def cuffSign (A : SurfAtlas S) {C : Set S} (φ : Circle ≃ₜ C) (x : S) : ZMod 2 :=
  cuffSignChart (A.chart (A.idx x)) φ x

theorem cuffSignChart_change {c₁ c₂ : SurfChart S} {C : Set S} (hC : C ⊆ bd S) (φ : Circle ≃ₜ C)
    {x : S} (hxC : x ∈ C) (hx1 : x ∈ c₁.U) (hx2 : x ∈ c₂.U) :
    cuffSignChart c₂ φ x - cuffSignChart c₁ φ x = chartSign c₁ c₂ x := by
  classical
  have h := cuffPos_iff_chartPos hC φ hxC hx1 hx2
  unfold cuffSignChart chartSign
  by_cases h1 : cuffPos c₁ φ x <;> by_cases h12 : chartPos c₁ c₂ x
  · have h2 : cuffPos c₂ φ x := h.mpr (by tauto); simp [h1, h12, h2]
  · have h2 : ¬ cuffPos c₂ φ x := fun hc => h12 ((h.mp hc).mp h1); simp [h1, h12, h2]
  · have h2 : ¬ cuffPos c₂ φ x := fun hc => h1 ((h.mp hc).mpr h12); simp [h1, h12, h2]
  · have h2 : cuffPos c₂ φ x := h.mpr (by tauto); simp [h1, h12, h2]

/-- `cuffPos c φ` is locally constant on `C ∩ c.U`. -/
theorem cuffPos_const_of_near {c : SurfChart S} {C : Set S} (hC : C ⊆ bd S) (φ : Circle ≃ₜ C)
    {x : S} (hxC : x ∈ C) (hxU : x ∈ c.U) :
    ∃ W : Set S, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, y ∈ C → (cuffPos c φ y ↔ cuffPos c φ x) := by
  obtain ⟨u₀, δ, hδ, hδ4, hx0, hδU, hmo⟩ := cuff_im_mono_or_anti hC φ hxC hxU
  let γ : ℝ → S := fun t => (φ (ee (u₀ + t))).1
  -- The open arc `γ '' Ioo (-δ) δ` is open in `C`, hence `C ∩ W` for some open `W ⊆ c.U`!
  have hopenC : IsOpen ((φ ⁻¹' ((Subtype.val : C → S) ⁻¹' c.U)) ∩ ee '' Ioo (u₀ - δ) (u₀ + δ)) := by
    refine (c.hU.preimage (continuous_subtype_val.comp φ.continuous)).inter ?_
    -- `ee` is a local homeomorphism (open map); even simpler, `Ioo (u₀ - δ) (u₀ + δ)` has open image in `Circle`!
    rw [← isQuotientMap_ee.isOpen_preimage]
    have heq : ee ⁻¹' (ee '' Ioo (u₀ - δ) (u₀ + δ)) = ⋃ k : ℤ, Ioo (u₀ - δ + k) (u₀ + δ + k) := by
      ext t
      simp only [mem_preimage, mem_image, mem_iUnion, mem_Ioo]
      constructor
      · rintro ⟨s, ⟨hs1, hs2⟩, he⟩
        obtain ⟨k, hk⟩ := ee_eq_iff.mp he.symm
        exact ⟨k, by linarith, by linarith⟩
      · rintro ⟨k, h1, h2⟩
        exact ⟨t - k, ⟨by linarith, by linarith⟩, ee_eq_iff.mpr ⟨-k, by push_cast; ring⟩⟩
    rw [heq]; exact isOpen_iUnion fun _ => isOpen_Ioo
  have hopenSub : IsOpen (Subtype.val ⁻¹' (γ '' Ioo (-δ) δ) : Set C) := by
    have heq : (Subtype.val ⁻¹' (γ '' Ioo (-δ) δ) : Set C) = φ.symm ⁻¹' (ee '' Ioo (u₀ - δ) (u₀ + δ)) := by
      ext ⟨y, hy⟩
      simp only [mem_preimage, mem_image, mem_Ioo, γ]
      constructor
      · rintro ⟨t, ⟨h1, h2⟩, he⟩
        refine ⟨u₀ + t, ⟨by linarith, by linarith⟩, ?_⟩
        exact φ.symm_apply_eq.mpr (Subtype.ext he.symm) |>.symm
      · rintro ⟨s, ⟨h1, h2⟩, he⟩
        refine ⟨s - u₀, ⟨by linarith, by linarith⟩, ?_⟩
        have h3 : φ (ee s) = ⟨y, hy⟩ := ((φ.symm_apply_eq).mp he.symm).symm
        have h4 : u₀ + (s - u₀) = s := by ring
        rw [h4, h3]
    rw [heq]
    have hoo : IsOpen (ee '' Ioo (u₀ - δ) (u₀ + δ)) := by
      rw [← isQuotientMap_ee.isOpen_preimage]
      have heq2 : ee ⁻¹' (ee '' Ioo (u₀ - δ) (u₀ + δ)) = ⋃ k : ℤ, Ioo (u₀ - δ + k) (u₀ + δ + k) := by
        ext t; simp only [mem_preimage, mem_image, mem_iUnion, mem_Ioo]
        constructor
        · rintro ⟨s, ⟨hs1, hs2⟩, he⟩; obtain ⟨k, hk⟩ := ee_eq_iff.mp he.symm; exact ⟨k, by linarith, by linarith⟩
        · rintro ⟨k, h1, h2⟩; exact ⟨t - k, ⟨by linarith, by linarith⟩, ee_eq_iff.mpr ⟨-k, by push_cast; ring⟩⟩
      rw [heq2]; exact isOpen_iUnion fun _ => isOpen_Ioo
    exact hoo.preimage φ.symm.continuous
  obtain ⟨W₀, hW₀, hW₀eq⟩ := isOpen_induced_iff.mp hopenSub
  have hxW₀ : x ∈ W₀ := by
    have : (⟨x, hxC⟩ : C) ∈ Subtype.val ⁻¹' W₀ := by
      rw [hW₀eq]; exact ⟨0, ⟨by linarith, hδ⟩, by simp [γ, hx0]⟩
    exact this
  refine ⟨W₀ ∩ c.U, hW₀.inter c.hU, ⟨hxW₀, hxU⟩, fun y hyW hyC => ?_⟩
  have hyγ : y ∈ γ '' Ioo (-δ) δ := by
    have : (⟨y, hyC⟩ : C) ∈ Subtype.val ⁻¹' W₀ := hyW.1
    rwa [hW₀eq] at this
  obtain ⟨t₀, ht₀, rfl⟩ := hyγ
  set η := min (t₀ + δ) (δ - t₀)
  have hη : 0 < η := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
  have hsub : ∀ s ∈ Icc (-η) η, t₀ + s ∈ Icc (-δ) δ := fun s hs =>
    ⟨by linarith [hs.1, min_le_left (t₀ + δ) (δ - t₀)], by linarith [hs.2, min_le_right (t₀ + δ) (δ - t₀)]⟩
  have hγ_shift : ∀ s, (φ (ee ((u₀ + t₀) + s))).1 = γ (t₀ + s) := fun s => by simp [γ, add_assoc]
  rcases hmo with hm | ha
  · have hpos_x : cuffPos c φ x := ⟨u₀, δ, hδ, hx0, hδU, hm⟩
    have hpos_y : cuffPos c φ (γ t₀) := ⟨u₀ + t₀, η, hη, rfl,
      fun s hs => by rw [hγ_shift]; exact hδU _ (hsub s hs),
      fun s₁ hs₁ s₂ hs₂ h12 => by dsimp only; rw [hγ_shift, hγ_shift]; exact hm (hsub s₁ hs₁) (hsub s₂ hs₂) (by linarith)⟩
    tauto
  · have hneg_x : ¬ cuffPos c φ x := by
      rintro ⟨u₁, δ₁, hδ₁, hx1', -, hm1⟩
      obtain ⟨k, hk⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext (hx1'.trans hx0.symm)))
      have heq_γ : ∀ t, (φ (ee (u₁ + t))).1 = γ t := fun t => by
        have : ee (u₁ + t) = ee (u₀ + t) := ee_eq_iff.mpr ⟨k, by linarith⟩
        simp [γ, this]
      set ρ := min δ δ₁
      have hρ : 0 < ρ := lt_min hδ hδ₁
      have h1 := hm1 ⟨by linarith, hδ₁.le⟩ ⟨by linarith [min_le_right δ δ₁], min_le_right _ _⟩ hρ
      have h2 := ha ⟨by linarith, hδ.le⟩ ⟨by linarith [min_le_left δ δ₁], min_le_left _ _⟩ hρ
      simp only [heq_γ] at h1; linarith
    have hneg_y : ¬ cuffPos c φ (γ t₀) := by
      rintro ⟨u₁, δ₁, hδ₁, hy1', -, hm1⟩
      obtain ⟨k, hk⟩ := ee_eq_iff.mp (φ.injective (Subtype.ext hy1'))
      have heq_γ : ∀ s, (φ (ee (u₁ + s))).1 = γ (t₀ + s) := fun s => by
        have : ee (u₁ + s) = ee (u₀ + (t₀ + s)) := ee_eq_iff.mpr ⟨k, by linarith⟩
        simp [γ, this]
      set ρ := min η δ₁
      have hρ : 0 < ρ := lt_min hη hδ₁
      have h1 := hm1 ⟨by linarith, hδ₁.le⟩ ⟨by linarith [min_le_right η δ₁], min_le_right _ _⟩ hρ
      have h2 := ha (hsub 0 ⟨by linarith, hη.le⟩) (hsub ρ ⟨by linarith [min_le_left η δ₁], min_le_left _ _⟩) (by linarith)
      simp only [heq_γ, add_zero] at h1
      rw [hy1'] at h1
      change (c.j (γ t₀)).im < (c.j (γ (t₀ + ρ))).im at h1
      change (c.j (γ (t₀ + ρ))).im < (c.j (γ (t₀ + 0))).im at h2
      rw [add_zero] at h2
      linarith
    tauto

/-- On a cuff `C`, near the diagonal, `w1 A x y = cuffSign A φ y - cuffSign A φ x`. -/
theorem cuffSign_diff (hS : IsSurface S) (A : SurfAtlas S) {C : Set S} (hC : C ⊆ bd S)
    (φ : Circle ≃ₜ C) :
    ∃ N : Set (S × S), NearDiag N ∧ ∀ x ∈ C, ∀ y ∈ C, (x, y) ∈ N →
      w1 A x y = cuffSign A φ y - cuffSign A φ x := by
  classical
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨N₀, hN₀, htr⟩ := exists_triple_nearDiag hS A
  have hCcl : IsClosed C := by
    have hcomp : IsCompact C := by
      have := isCompact_univ.image (continuous_subtype_val.comp φ.continuous)
      convert this using 1
      ext y
      exact ⟨fun hy => ⟨φ.symm ⟨y, hy⟩, mem_univ _, by simp⟩, fun ⟨z, _, hz⟩ => hz ▸ (φ z).2⟩
    exact hcomp.isClosed
  have hnear_i : ∀ i : Fin A.m, ∃ Ni : Set (S × S), NearDiag Ni ∧
      ∀ x ∈ C, ∀ y ∈ C, (x, y) ∈ Ni → x ∈ A.V i →
        cuffSignChart (A.chart i) φ y = cuffSignChart (A.chart i) φ x := by
    intro i
    have hex : ∀ w : S, ∃ O : Set S, IsOpen O ∧ w ∈ O ∧
        ∀ x ∈ O, ∀ y ∈ O, x ∈ C → y ∈ C → x ∈ A.V i →
          cuffSignChart (A.chart i) φ y = cuffSignChart (A.chart i) φ x := by
      intro w
      by_cases hwC : w ∈ C
      · by_cases hwV : w ∈ closure (A.V i)
        · obtain ⟨Ox, hOx, hwO, hconst⟩ := cuffPos_const_of_near hC φ hwC (A.hV_sub i hwV)
          exact ⟨Ox, hOx, hwO, fun x hx y hy hxC hyC _ => by
            simp [cuffSignChart, hconst x hx hxC, hconst y hy hyC]⟩
        · exact ⟨(closure (A.V i))ᶜ, isClosed_closure.isOpen_compl, hwV,
            fun x hx _ _ _ _ hxV => absurd (subset_closure hxV) hx⟩
      · exact ⟨Cᶜ, hCcl.isOpen_compl, hwC, fun x hx _ _ hxC _ _ => absurd hxC hx⟩
    choose O hOo hwO hOconst using hex
    refine ⟨⋃ w : S, O w ×ˢ O w, fun x => Filter.mem_of_superset ((hOo x).prod (hOo x) |>.mem_nhds ⟨hwO x, hwO x⟩)
      (subset_iUnion (fun w => O w ×ˢ O w) x), fun x hxC y hyC hxy hxV => ?_⟩
    obtain ⟨w, hxw, hyw⟩ := mem_iUnion.mp hxy
    exact hOconst w x hxw y hyw hxC hyC hxV
  choose Ni hNi hNiconst using hnear_i
  let N : Set (S × S) := N₀ ∩ ⋂ i : Fin A.m, Ni i
  have hN : NearDiag N := fun x => Filter.inter_mem (hN₀ x) (Filter.iInter_mem.mpr fun i => hNi i x)
  refine ⟨N, hN, fun x hxC y hyC hxy => ?_⟩
  have hxy0 : (x, y) ∈ N₀ := hxy.1
  have hxyi : (x, y) ∈ Ni (A.idx x) := mem_iInter.mp hxy.2 (A.idx x)
  obtain ⟨c₀, W, hWo, hxW, hyW, -, hWx, hWy, -, hWc₀, hWne, hWconn⟩ := htr x y x hxy0 (hN₀.mem x)
  have hconst_x : cuffSignChart (A.chart (A.idx x)) φ y = cuffSignChart (A.chart (A.idx x)) φ x :=
    hNiconst (A.idx x) x hxC y hyC hxyi (A.hidx x)
  have hch_y := cuffSignChart_change hC φ hyC (hWx hyW) (hWy hyW)
  have hsign_eq : chartSign (A.chart (A.idx x)) (A.chart (A.idx y)) y =
      chartSign (A.chart (A.idx x)) (A.chart (A.idx y)) x := by
    have e1 := chartSign_trans (hWx hyW) (hWc₀ hyW) (hWy hyW)
    have e2 := chartSign_trans (hWx hxW) (hWc₀ hxW) (hWy hxW)
    rw [← e1, ← e2, chartSign_symm (hWc₀ hyW) (hWx hyW), chartSign_symm (hWc₀ hxW) (hWx hxW),
      chartSign_eq_of_ball hWo (subset_inter hWc₀ hWx) hWne hWconn hyW hxW,
      chartSign_eq_of_ball hWo (subset_inter hWc₀ hWy) hWne hWconn hyW hxW]
  unfold w1 cuffSign
  rw [← hsign_eq, ← hch_y, hconst_x]

/-- `w1 A` is trivial on the boundary (`BdTriv (w1 A)`). -/
theorem bdTriv_w1 (hS : IsSurface S) (A : SurfAtlas S) : BdTriv (w1 A) := by
  classical
  have : T2Space S := hS.2.1
  have hcuff := cuff_statement.{u} S hS
  have hex_φ : ∀ C : Set S, C ∈ cuffs S → ∃ φ : Circle ≃ₜ C, True := fun C hC => by
    obtain ⟨φ⟩ := hcuff.2.2 C hC; exact ⟨φ, trivial⟩
  let h : S → ZMod 2 := fun x =>
    if hx : x ∈ bd S then
      let C := connectedComponentIn (bd S) x
      have hC : C ∈ cuffs S := ⟨x, hx, rfl⟩
      cuffSign A (hex_φ C hC).choose x
    else 0
  have hfin : (cuffs S).Finite := hcuff.2.1
  have hnear_C : ∀ C ∈ cuffs S, ∃ NC : Set (S × S), NearDiag NC ∧
      ∀ x ∈ C, ∀ y ∈ C, (x, y) ∈ NC → w1 A x y = -h x + h y := by
    intro C hC
    have hCbd : C ⊆ bd S := by obtain ⟨z, -, rfl⟩ := hC; exact connectedComponentIn_subset _ _
    let φ := (hex_φ C hC).choose
    obtain ⟨NC, hNC, hdiff⟩ := cuffSign_diff hS A hCbd φ
    refine ⟨NC, hNC, fun x hxC y hyC hxy => ?_⟩
    have hcx : connectedComponentIn (bd S) x = C := by
      obtain ⟨z, -, hEq⟩ := hC
      rw [← hEq] at hxC ⊢
      exact (connectedComponentIn_eq hxC).symm
    have hcy : connectedComponentIn (bd S) y = C := by
      obtain ⟨z, -, hEq⟩ := hC
      rw [← hEq] at hyC ⊢
      exact (connectedComponentIn_eq hyC).symm
    have h_eq : ∀ {p : S} {C₁ C₂ : Set S} (h1 : C₁ ∈ cuffs S) (h2 : C₂ ∈ cuffs S), C₁ = C₂ →
        cuffSign A (hex_φ C₁ h1).choose p = cuffSign A (hex_φ C₂ h2).choose p := by
      rintro p _ _ h1 h2 rfl; rfl
    have hx_val : h x = cuffSign A φ x := by
      simp only [h, dite_eq_left (hCbd hxC)]
      exact h_eq ⟨x, hCbd hxC, rfl⟩ hC hcx
    have hy_val : h y = cuffSign A φ y := by
      simp only [h, dite_eq_left (hCbd hyC)]
      exact h_eq ⟨y, hCbd hyC, rfl⟩ hC hcy
    rw [hdiff x hxC y hyC hxy, hx_val, hy_val]; abel
  -- Also separate distinct cuffs using a `NearDiag` `N_sep`:
  have hsep : ∃ Nsep : Set (S × S), NearDiag Nsep ∧
      ∀ x ∈ bd S, ∀ y ∈ bd S, (x, y) ∈ Nsep → connectedComponentIn (bd S) y = connectedComponentIn (bd S) x := by
    have hcl_cuff : ∀ C ∈ cuffs S, IsClosed C := fun C hC => (hcuff.2.2 C hC).isCompact.isClosed
    have hopen : ∀ x : S, ∃ O : Set S, IsOpen O ∧ x ∈ O ∧
        ∀ a ∈ O, ∀ b ∈ O, a ∈ bd S → b ∈ bd S → connectedComponentIn (bd S) b = connectedComponentIn (bd S) a := by
      intro x
      by_cases hx : x ∈ bd S
      · set C := connectedComponentIn (bd S) x
        have hC : C ∈ cuffs S := ⟨x, hx, rfl⟩
        have hrest_cl : IsClosed (⋃₀ (cuffs S \ {C})) :=
          (hfin.subset sdiff_subset).isClosed_sUnion fun D hD => hcl_cuff D hD.1
        have hx_in : x ∈ (⋃₀ (cuffs S \ {C}))ᶜ := by
          rintro ⟨D, ⟨hD, hne⟩, hxD⟩
          exact hne (mem_singleton_iff.mpr (by obtain ⟨z, -, rfl⟩ := hD; exact connectedComponentIn_eq hxD))
        refine ⟨(⋃₀ (cuffs S \ {C}))ᶜ, hrest_cl.isOpen_compl, hx_in, fun a ha b hb ha_bd hb_bd => ?_⟩
        have haC : connectedComponentIn (bd S) a = C := by
          by_contra hne
          exact ha ⟨connectedComponentIn (bd S) a, ⟨⟨a, ha_bd, rfl⟩, hne⟩, mem_connectedComponentIn ha_bd⟩
        have hbC : connectedComponentIn (bd S) b = C := by
          by_contra hne
          exact hb ⟨connectedComponentIn (bd S) b, ⟨⟨b, hb_bd, rfl⟩, hne⟩, mem_connectedComponentIn hb_bd⟩
        exact hbC.trans haC.symm
      · exact ⟨(bd S)ᶜ, hcuff.1.isOpen_compl, hx, fun a ha _ _ ha_bd _ => absurd ha_bd ha⟩
    choose O hOo hxO hOeq using hopen
    refine ⟨⋃ x : S, O x ×ˢ O x, fun x => Filter.mem_of_superset ((hOo x).prod (hOo x) |>.mem_nhds ⟨hxO x, hxO x⟩)
      (subset_iUnion (fun w => O w ×ˢ O w) x), fun x hx y hy hxy => ?_⟩
    obtain ⟨w, hxw, hyw⟩ := mem_iUnion.mp hxy
    exact hOeq w x hxw y hyw hx hy
  obtain ⟨Nsep, hNsep, hsep_eq⟩ := hsep
  let NC : Set S → Set (S × S) := fun C =>
    if hC : C ∈ cuffs S then (hnear_C C hC).choose else univ
  have hNC_nd : ∀ C ∈ cuffs S, NearDiag (NC C) := fun C hC => by
    simp only [NC, dite_eq_left hC]; exact (hnear_C C hC).choose_spec.1
  let N : Set (S × S) := Nsep ∩ ⋂ C ∈ cuffs S, NC C
  have hN : NearDiag N := fun x =>
    Filter.inter_mem (hNsep x) ((Filter.biInter_mem hfin).mpr fun C hC => hNC_nd C hC x)
  refine ⟨h, N, hN, fun x hx y hy hxy => ?_⟩
  set C := connectedComponentIn (bd S) x
  have hC : C ∈ cuffs S := ⟨x, hx, rfl⟩
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hyC : y ∈ C := by
    change y ∈ connectedComponentIn (bd S) x
    rw [← hsep_eq x hx y hy hxy.1]
    exact mem_connectedComponentIn hy
  have hxyC : (x, y) ∈ NC C := mem_iInter₂.mp hxy.2 C hC
  simp only [NC, dite_eq_left hC] at hxyC
  exact (hnear_C C hC).choose_spec.2 x hxC y hyC hxyC

/-- Reversing or preserving circle orientation of `φ : Circle ≃ₜ C` changes `cuffPos` accordingly. -/
theorem cuffPos_comp_circle {c : SurfChart S} {C : Set S} (hC : C ⊆ bd S) (φ : Circle ≃ₜ C)
    (k : Circle ≃ₜ Circle) {x : S} (hxC : x ∈ C) (hxU : x ∈ c.U) :
    cuffPos c (k.trans φ) x ↔ (cuffPos c φ x ↔ PreservesCircleOrientation k) := by
  have hpi := Real.pi_pos
  obtain ⟨u₀, δ, hδ, hδ4, hx0, hδU, hmo⟩ := cuff_im_mono_or_anti hC φ hxC hxU
  -- Helper: either `k` or `k.trans inv` preserves circle orientation!
  have hor : PreservesCircleOrientation k ∨ PreservesCircleOrientation (k.trans (Homeomorph.inv Circle)) := by
    -- Lift `k` on `[0, 1]` via `exists_lift`:
    let φid : Circle ≃ₜ (univ : Set Circle) := (Homeomorph.Set.univ Circle).symm
    obtain ⟨m, hm_c, hm_e⟩ := exists_lift φid (k.continuous.comp continuous_ee).continuousOn (fun _ _ => mem_univ _)
    have hm_ee : ∀ u ∈ Icc (0 : ℝ) 1, ee (m u) = k (ee u) := fun u hu => by simpa [φid] using hm_e u hu
    have h_inj : InjOn (fun u => ee (m u)) (Ico 0 1) := by
      intro a ha b hb he; dsimp only at he
      rw [hm_ee a (Ico_subset_Icc_self ha), hm_ee b (Ico_subset_Icc_self hb)] at he
      obtain ⟨n, hn⟩ := ee_eq_iff.mp (k.injective he)
      have hn0 : n = 0 := by
        have h1 : (-1 : ℝ) < n := by linarith [ha.1, hb.2]
        have h2 : (n : ℝ) < 1 := by linarith [ha.2, hb.1]
        have : -1 < n := by exact_mod_cast h1
        have : n < 1 := by exact_mod_cast h2
        omega
      rw [hn, hn0]; simp
    have hee01 : ee (1 : ℝ) = ee 0 := by simpa using ee_add_one 0
    have hm01 : ee (m 1) = ee (m 0) := by rw [hm_ee 1 (by simp), hm_ee 0 (by simp), hee01]
    obtain ⟨d, hd⟩ := ee_eq_iff.mp hm01
    rcases lift_mono_loop hm_c h_inj with hmono | hanti
    · left
      have hpos : (0 : ℝ) < d := by have := hmono (by simp) (by simp) zero_lt_one; linarith
      have hd1 : 1 ≤ d := by exact_mod_cast hpos
      have hd_eq : d = 1 := by
        by_contra hne
        have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
        obtain ⟨t, ht, htm⟩ := intermediate_value_Ioo zero_le_one hm_c
          (show m 0 + 1 ∈ Ioo (m 0) (m 1) by rw [hd]; constructor <;> linarith)
        have := h_inj ⟨ht.1.le, ht.2⟩ ⟨le_rfl, zero_lt_one⟩ (by dsimp only; rw [htm, ee_add_one])
        linarith [ht.1]
      obtain ⟨h', hh', hh'_e⟩ := exists_circle_homeo hm_c hmono (by rw [hd, hd_eq]; norm_num)
      have heq : h' = k := by
        refine Homeomorph.ext fun z => ?_
        obtain ⟨t, rfl⟩ := ee_surjective z
        have hu : Int.fract t ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩
        have hft : ee (Int.fract t) = ee t := ee_eq_iff.mpr ⟨-⌊t⌋, by rw [Int.fract]; push_cast; ring⟩
        rw [← hft, hh'_e _ (Ico_subset_Icc_self hu), hm_ee _ (Ico_subset_Icc_self hu)]
      exact heq ▸ hh'
    · right
      have hneg : (d : ℝ) < 0 := by have := hanti (by simp) (by simp) zero_lt_one; linarith
      have hd_le : d ≤ -1 := by
        have : d < 0 := by exact_mod_cast hneg
        omega
      have hd_eq : d = -1 := by
        by_contra hne
        have hd2 : (d : ℝ) ≤ -2 := by exact_mod_cast (show d ≤ -2 by omega)
        obtain ⟨t, ht, htm⟩ := intermediate_value_Ioo' zero_le_one hm_c
          (show m 0 - 1 ∈ Ioo (m 1) (m 0) by rw [hd]; constructor <;> linarith)
        have := h_inj ⟨ht.1.le, ht.2⟩ ⟨le_rfl, zero_lt_one⟩
          (by dsimp only; rw [htm]; exact ee_eq_iff.mpr ⟨-1, by push_cast; ring⟩)
        linarith [ht.1]
      have hper : -m 1 = -m 0 + 1 := by rw [hd, hd_eq]; push_cast; ring
      obtain ⟨h', hh', hh'_e⟩ := exists_circle_homeo hm_c.neg (fun a ha b hb hab => neg_lt_neg (hanti ha hb hab)) hper
      have heq : h' = k.trans (Homeomorph.inv Circle) := by
        refine Homeomorph.ext fun z => ?_
        obtain ⟨t, rfl⟩ := ee_surjective z
        have hu : Int.fract t ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩
        have hft : ee (Int.fract t) = ee t := ee_eq_iff.mpr ⟨-⌊t⌋, by rw [Int.fract]; push_cast; ring⟩
        rw [← hft, hh'_e _ (Ico_subset_Icc_self hu)]
        show ee (-m (Int.fract t)) = (k (ee (Int.fract t)))⁻¹
        rw [← hm_ee _ (Ico_subset_Icc_self hu)]
        simp [ee, Circle.exp_neg]
      exact heq ▸ hh'
  -- Helper: `PreservesCircleOrientation k` and `PreservesCircleOrientation (k.trans inv)` cannot both hold.
  have hnot_both : PreservesCircleOrientation k → ¬ PreservesCircleOrientation (k.trans (Homeomorph.inv Circle)) := by
    rintro ⟨l₁, hc₁, hm₁, hl₁⟩ ⟨l₂, hc₂, hm₂, hl₂⟩
    have hrel : ∀ t, Circle.exp (l₁ t + l₂ t) = 1 := fun t => by
      rw [Circle.exp_add, ← hl₁, ← hl₂]; simp
    have hd : ∀ t, ∃ m : ℤ, l₁ t + l₂ t = m * (2 * Real.pi) := fun t => by
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp ((hrel t).trans Circle.exp_zero.symm)
      exact ⟨m, by linarith⟩
    have hcont : Continuous (fun t => (l₁ t + l₂ t) / (2 * Real.pi)) := (hc₁.add hc₂).div_const _
    have hconst : (l₁ 1 + l₂ 1) / (2 * Real.pi) = (l₁ 0 + l₂ 0) / (2 * Real.pi) := by
      have hconn : IsPreconnected (range fun t : ℝ => (l₁ t + l₂ t) / (2 * Real.pi)) := isPreconnected_range hcont
      have hint : ∀ y ∈ range (fun t : ℝ => (l₁ t + l₂ t) / (2 * Real.pi)), ∃ m : ℤ, y = m := by
        rintro _ ⟨t, rfl⟩; obtain ⟨m, hm⟩ := hd t; exact ⟨m, by dsimp only; rw [hm]; field_simp⟩
      by_contra hne
      obtain ⟨m0, hm0⟩ := hint _ ⟨0, rfl⟩
      obtain ⟨m1, hm1⟩ := hint _ ⟨1, rfl⟩
      have hmid : (m0 : ℝ) + 1 / 2 ∉ range (fun t : ℝ => (l₁ t + l₂ t) / (2 * Real.pi)) := by
        intro hmem; obtain ⟨m, hm⟩ := hint _ hmem
        have : (2 * m : ℤ) = 2 * m0 + 1 := by exact_mod_cast (by linarith : (2 * (m : ℝ)) = 2 * (m0 : ℝ) + 1)
        omega
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (m1 : ℝ) + 1 ≤ m0 := by
          have : m1 < m0 := by exact_mod_cast (by linarith : (m1 : ℝ) < m0)
          exact_mod_cast (by omega : m1 + 1 ≤ m0)
        have hmid' : (m1 : ℝ) + 1 / 2 ∉ range (fun t : ℝ => (l₁ t + l₂ t) / (2 * Real.pi)) := by
          intro hmem; obtain ⟨m, hm⟩ := hint _ hmem
          have : (2 * m : ℤ) = 2 * m1 + 1 := by exact_mod_cast (by linarith : (2 * (m : ℝ)) = 2 * (m1 : ℝ) + 1)
          omega
        exact hmid' (hconn.Icc_subset ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨by linarith, by linarith⟩)
      · have hle : (m0 : ℝ) + 1 ≤ m1 := by
          have : m0 < m1 := by exact_mod_cast (by linarith : (m0 : ℝ) < m1)
          exact_mod_cast (by omega : m0 + 1 ≤ m1)
        exact hmid (hconn.Icc_subset ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨by linarith, by linarith⟩)
    have hlt1 := hm₁ zero_lt_one
    have hlt2 := hm₂ zero_lt_one
    have hEq : l₁ 1 + l₂ 1 = l₁ 0 + l₂ 0 := (div_left_inj' (by positivity)).mp hconst
    linarith
  -- Now compare `cuffPos c (k.trans φ) x` with `cuffPos c φ x` using a lift `l` of `k`!
  have lift_case : ∀ (sgn : Bool),
      (∃ l : ℝ → ℝ, Continuous l ∧ (if sgn then StrictMono l else StrictAnti l) ∧
        ∀ t, k (ee t) = ee (l t)) →
      (cuffPos c (k.trans φ) x ↔ (if sgn then cuffPos c φ x else ¬ cuffPos c φ x)) := by
    intro sgn ⟨l, hlc, hlm, hle⟩
    obtain ⟨v₀, hv₀⟩ := ee_surjective (k.symm (ee u₀))
    have hkv₀ : k (ee v₀) = ee u₀ := by rw [hv₀, k.apply_symm_apply]
    have hx_v₀ : ((k.trans φ) (ee v₀)).1 = x := by simp [hkv₀, hx0]
    obtain ⟨m₀, hm₀⟩ := ee_eq_iff.mp ((hle v₀).symm.trans hkv₀)
    -- `l v₀ = u₀ + m₀`, so `l (v₀ + t) - m₀` is near `u₀` for small `t`!
    let τ : ℝ → ℝ := fun t => l (v₀ + t) - m₀ - u₀
    have hτc : Continuous τ := (hlc.comp (continuous_const.add continuous_id)).sub continuous_const |>.sub continuous_const
    have hτ0 : τ 0 = 0 := by simp [τ, hm₀]
    have hτ_ee : ∀ t, (k.trans φ) (ee (v₀ + t)) = φ (ee (u₀ + τ t)) := fun t => by
      simp only [Homeomorph.trans_apply, hle]
      congr 1; exact ee_eq_iff.mpr ⟨m₀, by simp only [τ]; ring⟩
    have hmem : τ ⁻¹' Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) :=
      hτc.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by rw [hτ0]; exact ⟨by linarith, hδ⟩))
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp hmem
    set η' := min (η / 2) (1 / 8)
    have hη' : 0 < η' := lt_min (half_pos hη) (by norm_num)
    have hη'_mem : ∀ t ∈ Icc (-η') η', τ t ∈ Icc (-δ) δ := fun t ht =>
      Ioo_subset_Icc_self (hηsub (by
        rw [mem_ball, Real.dist_eq, sub_zero]
        have := abs_le.mpr ht
        have : η' ≤ η / 2 := min_le_left _ _
        linarith))
    have hη'_U : ∀ t ∈ Icc (-η') η', ((k.trans φ) (ee (v₀ + t))).1 ∈ c.U := fun t ht => by
      rw [hτ_ee]; exact hδU _ (hη'_mem t ht)
    have hcomp_im : ∀ t, (c.j ((k.trans φ) (ee (v₀ + t))).1).im = (c.j (φ (ee (u₀ + τ t))).1).im :=
      fun t => by rw [hτ_ee]
    -- Helper: `StrictAntiOn` on `[-r, r]` implies `¬ cuffPos`!
    have not_of_anti : ∀ {ψ : Circle ≃ₜ C} {w₀ r : ℝ}, 0 < r → (ψ (ee w₀)).1 = x →
        StrictAntiOn (fun t => (c.j (ψ (ee (w₀ + t))).1).im) (Icc (-r) r) → ¬ cuffPos c ψ x := by
      intro ψ w₀ r hr hw₀ ha ⟨w₁, r₁, hr₁, hw₁, _, hm₁⟩
      obtain ⟨n, hn⟩ := ee_eq_iff.mp (ψ.injective (Subtype.ext (hw₁.trans hw₀.symm)))
      have heq : ∀ t, ψ (ee (w₁ + t)) = ψ (ee (w₀ + t)) := fun t => by
        congr 1; exact ee_eq_iff.mpr ⟨n, by linarith⟩
      set ρ := min r r₁
      have hρ : 0 < ρ := lt_min hr hr₁
      have h1 := hm₁ ⟨by linarith, hr₁.le⟩ ⟨by linarith [min_le_right r r₁], min_le_right _ _⟩ hρ
      have h2 := ha ⟨by linarith, hr.le⟩ ⟨by linarith [min_le_left r r₁], min_le_left _ _⟩ hρ
      simp only [heq] at h1; linarith
    cases sgn
    · -- `sgn = false`: `l` is `StrictAnti`, hence `τ` is `StrictAnti`!
      simp only [Bool.false_eq_true, ↓reduceIte] at hlm ⊢
      have hτa : StrictAnti τ := fun a b hab => by
        have := hlm (show v₀ + a < v₀ + b by linarith); simp only [τ]; linarith
      rcases hmo with hm | ha
      · have h1 : cuffPos c φ x := ⟨u₀, δ, hδ, hx0, hδU, hm⟩
        have h2a : StrictAntiOn (fun t => (c.j ((k.trans φ) (ee (v₀ + t))).1).im) (Icc (-η') η') :=
          fun a ha' b hb' hab => by dsimp only; rw [hcomp_im, hcomp_im]; exact hm (hη'_mem b hb') (hη'_mem a ha') (hτa hab)
        exact ⟨fun h => absurd h (not_of_anti hη' hx_v₀ h2a), fun h => absurd h1 h⟩
      · have h1 : ¬ cuffPos c φ x := not_of_anti hδ hx0 ha
        have h2m : StrictMonoOn (fun t => (c.j ((k.trans φ) (ee (v₀ + t))).1).im) (Icc (-η') η') :=
          fun a ha' b hb' hab => by dsimp only; rw [hcomp_im, hcomp_im]; exact ha (hη'_mem b hb') (hη'_mem a ha') (hτa hab)
        exact ⟨fun _ => h1, fun _ => ⟨v₀, η', hη', hx_v₀, hη'_U, h2m⟩⟩
    · -- `sgn = true`: `l` is `StrictMono`, hence `τ` is `StrictMono`!
      simp only [↓reduceIte] at hlm ⊢
      have hτm : StrictMono τ := fun a b hab => by
        have := hlm (show v₀ + a < v₀ + b by linarith); simp only [τ]; linarith
      rcases hmo with hm | ha
      · have h1 : cuffPos c φ x := ⟨u₀, δ, hδ, hx0, hδU, hm⟩
        have h2m : StrictMonoOn (fun t => (c.j ((k.trans φ) (ee (v₀ + t))).1).im) (Icc (-η') η') :=
          fun a ha' b hb' hab => by dsimp only; rw [hcomp_im, hcomp_im]; exact hm (hη'_mem a ha') (hη'_mem b hb') (hτm hab)
        exact ⟨fun _ => h1, fun _ => ⟨v₀, η', hη', hx_v₀, hη'_U, h2m⟩⟩
      · have h1 : ¬ cuffPos c φ x := not_of_anti hδ hx0 ha
        have h2a : StrictAntiOn (fun t => (c.j ((k.trans φ) (ee (v₀ + t))).1).im) (Icc (-η') η') :=
          fun a ha' b hb' hab => by dsimp only; rw [hcomp_im, hcomp_im]; exact ha (hη'_mem a ha') (hη'_mem b hb') (hτm hab)
        exact ⟨fun h => absurd h (not_of_anti hη' hx_v₀ h2a), fun h => absurd h h1⟩
  rcases hor with hkpos | hkneg
  · obtain ⟨l, hlc, hlm, hle⟩ := id hkpos
    have h1 := lift_case true ⟨fun t => l (2 * Real.pi * t) / (2 * Real.pi),
      (hlc.comp (continuous_const.mul continuous_id)).div_const _,
      by simp only [↓reduceIte]; intro a b hab
         exact div_lt_div_of_pos_right (hlm (mul_lt_mul_of_pos_left hab (by positivity))) (by positivity),
      fun t => by
        show k (Circle.exp (2 * Real.pi * t)) = Circle.exp (2 * Real.pi * (l (2 * Real.pi * t) / (2 * Real.pi)))
        rw [mul_div_cancel₀ _ (by positivity), hle]⟩
    simpa [hkpos] using h1
  · have hnp : ¬ PreservesCircleOrientation k := fun h => hnot_both h hkneg
    obtain ⟨l, hlc, hlm, hle⟩ := hkneg
    have h1 := lift_case false ⟨fun t => -(l (2 * Real.pi * t) / (2 * Real.pi)),
      ((hlc.comp (continuous_const.mul continuous_id)).div_const _).neg,
      by simp only [Bool.false_eq_true, ↓reduceIte]; intro a b hab
         exact neg_lt_neg (div_lt_div_of_pos_right (hlm (mul_lt_mul_of_pos_left hab (by positivity))) (by positivity)),
      fun t => by
        have h' : (k (Circle.exp (2 * Real.pi * t)))⁻¹ = Circle.exp (l (2 * Real.pi * t)) := hle (2 * Real.pi * t)
        have hk : k (Circle.exp (2 * Real.pi * t)) = (Circle.exp (l (2 * Real.pi * t)))⁻¹ := by
          rw [← h', inv_inv]
        show k (Circle.exp (2 * Real.pi * t)) = Circle.exp (2 * Real.pi * (-(l (2 * Real.pi * t) / (2 * Real.pi))))
        rw [hk, ← Circle.exp_neg]
        congr 1; field_simp [hpi.ne']⟩
    simpa [hnp] using h1

end Boundary

end GraphMinor.Surface


