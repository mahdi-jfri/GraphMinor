module

public import GraphMinor.GHR18.BandThicken
public import GraphMinor.GM07.Section11f
import GraphMinor.GM07.StarDisc

/-!
# Eliminating `O`-arcs via multi-crossing band sums (GHR18 Theorem 2.6, Step 2b)

This file completes Step 2 of Geelen–Huynh–Richter (2018), Theorem 2.6: starting from the
transverse `ProperManifold` `M` produced by `parity_surgery` (with `|M.U ∩ Q i| ≤ 1` for all `i`),
we iteratively merge components of `M` via `band_surgery_along_arc` until `M.Os = []`, leaving a
single proper `I`-arc `P'` with `|P' ∩ Q i| ≤ 2` for every `i`, preserving `w1Total AS` and
`BdCohRel s t`.

## Invariant & proof structure
We maintain a partition `A : Finset (Fin m)` / `Aᶜ` such that:
- for `j ∈ A`: `M.U ∩ Q j` is nonempty, finite, of size `≤ 2`, and `IsSimpleCrossing M.U (Q j)`;
- for `i ∉ A`: `Disjoint M.U (Q i)`.

Let `W_all := (bd S)ᶜ \ ⋃_{i ∉ A} Q i` and `X_A := M.U ∪ ⋃_{j ∈ A} Q j`.
1. **Case 1**: Some connected component `W` of `W_all` contains `≥ 2` components of `M`.
   By the RED/BLUE lemma (`exists_two_comp_touch`), some component `Ω` of `W \ X_A` touches two
   distinct components of `M` at interior points avoiding `⋃ Q`. A simple arc in `Ω` yields a
   `BandArcData` with `k = 0`; `band_surgery_along_arc` decreases `M.Os.length` by 1 keeping `A`.
2. **Case 2**: Every component of `W_all` contains `≤ 1` component of `M`.
   Since `(bd S)ᶜ` is connected, a shortest chain `W_0 —(i_1)— W_1 — ... —(i_k)— W_k` (`k ≥ 1`,
   `i_r ∉ A`) between two `M`-containing components has pairwise distinct `W_r`, pairwise distinct
   `i_r`, and empty intermediate `W_r ∩ X_A` (because every `Q j` for `j ∈ A` meets `M.U` and thus
   lies in an `M`-containing component). Concatenating simple arcs across `W_0, ..., W_k` yields a
   `BandArcData` with `idxs = [i_1, ..., i_k]`; `band_surgery_along_arc` decreases `M.Os.length` by
   1 and moves `{i_1, ..., i_k}` into `A`.
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Function Metric Complex GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-! ### Section 1: Interior connectivity, local boxes, and multi-segment concatenation -/

section LocalBoxes

/-- Connected components of an open subset `U ⊆ (bd S)ᶜ` are open. -/
theorem isOpen_connectedComponentIn_of_subset_compl_bd (_hS : IsSurface S) {U : Set S}
    (hUo : IsOpen U) (hUint : U ⊆ (bd S)ᶜ) {x : S} (_hx : x ∈ U) :
    IsOpen (connectedComponentIn U x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hyU : y ∈ U := connectedComponentIn_subset U x hy
  have hyint : IsInteriorPoint y := not_not.mp (hUint hyU)
  obtain ⟨V, h, g, c, hVU, hg0⟩ := hyint.exists_ballChart hUo hyU (R := 1) one_pos
  have hVo : IsOpen V := c.isOpen
  have hyV : y ∈ V := hg0 ▸ c.gm (mem_ball_self one_pos)
  have hVeq : V = g '' ball (0 : ℂ) 1 := by
    ext z; constructor
    · intro hz; exact ⟨h z, c.hm hz, c.gh hz⟩
    · rintro ⟨w, hw, rfl⟩; exact c.gm hw
  have hVconn : IsPreconnected V := by
    rw [hVeq]
    exact (convex_ball (0 : ℂ) 1).isPreconnected.image g c.gc
  have hVsub : V ⊆ connectedComponentIn U y :=
    hVconn.subset_connectedComponentIn hyV hVU
  rw [← connectedComponentIn_eq hy] at hVsub
  exact Filter.mem_of_superset (hVo.mem_nhds hyV) hVsub

/-- Every connected open subset `V ⊆ (bd S)ᶜ` is path-connected. -/
theorem isPathConnected_of_open_connected_compl_bd (_hS : IsSurface S) {V : Set S}
    (hVo : IsOpen V) (hVint : V ⊆ (bd S)ᶜ) (hVconn : IsConnected V) :
    IsPathConnected V := by
  obtain ⟨x₀, hx₀⟩ := hVconn.nonempty
  refine ⟨x₀, hx₀, fun y hy => ?_⟩
  let P : Set S := {z ∈ V | JoinedIn V x₀ z}
  let Q : Set S := {z ∈ V | ¬ JoinedIn V x₀ z}
  have hball_joined : ∀ z ∈ V, ∃ W, IsOpen W ∧ z ∈ W ∧ W ⊆ V ∧ ∀ w ∈ W, JoinedIn V z w := by
    intro z hz
    obtain ⟨W, h, g, c, hWV, hg0⟩ := (not_not.mp (hVint hz) : IsInteriorPoint z).exists_ballChart hVo hz (R := 1) one_pos
    refine ⟨W, c.isOpen, hg0 ▸ c.gm (mem_ball_self one_pos), hWV, fun w hw => ?_⟩
    have hhw : h w ∈ ball (0 : ℂ) 1 := c.hm hw
    have hseg : ∀ t : unitInterval, ((t : ℝ) : ℂ) * h w ∈ ball (0 : ℂ) 1 := fun t => by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.2.1]
      have h1 := mem_ball_zero_iff.mp hhw
      nlinarith [t.2.2, norm_nonneg (h w)]
    refine ⟨{ toFun := fun t => g (((t : ℝ) : ℂ) * h w)
              continuous_toFun := c.gc.comp_continuous (by fun_prop) hseg
              source' := by simp [hg0]
              target' := by simp [c.gh hw] }, fun t => hWV (c.gm (hseg t))⟩
  have hPo : IsOpen P := by
    rw [isOpen_iff_mem_nhds]; intro z ⟨hzV, hzj⟩
    obtain ⟨W, hWo, hzW, hWV, hWj⟩ := hball_joined z hzV
    exact Filter.mem_of_superset (hWo.mem_nhds hzW) fun w hw => ⟨hWV hw, hzj.trans (hWj w hw)⟩
  have hQo : IsOpen Q := by
    rw [isOpen_iff_mem_nhds]; intro z ⟨hzV, hznj⟩
    obtain ⟨W, hWo, hzW, hWV, hWj⟩ := hball_joined z hzV
    exact Filter.mem_of_superset (hWo.mem_nhds hzW) fun w hw =>
      ⟨hWV hw, fun h => hznj (h.trans (hWj w hw).symm)⟩
  have hcov : V ⊆ P ∪ Q := fun z hz => by
    by_cases h : JoinedIn V x₀ z; exact Or.inl ⟨hz, h⟩; exact Or.inr ⟨hz, h⟩
  by_contra hnot
  have hne := hVconn.isPreconnected P Q hPo hQo hcov ⟨x₀, hx₀, hx₀, JoinedIn.refl hx₀⟩ ⟨y, hy, hy, hnot⟩
  obtain ⟨z, -, ⟨-, h1⟩, ⟨-, h2⟩⟩ := hne
  exact h2 h1

/-- Connected components of an open subset `U ⊆ (bd S)ᶜ` are path-connected. -/
theorem isPathConnected_connectedComponentIn_of_subset_compl_bd (hS : IsSurface S) {U : Set S}
    (hUo : IsOpen U) (hUint : U ⊆ (bd S)ᶜ) {x : S} (hx : x ∈ U) :
    IsPathConnected (connectedComponentIn U x) :=
  isPathConnected_of_open_connected_compl_bd hS
    (isOpen_connectedComponentIn_of_subset_compl_bd hS hUo hUint hx)
    ((connectedComponentIn_subset U x).trans hUint)
    ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩

/-- On a connected surface `S`, the interior `(bd S)ᶜ` is preconnected. -/
theorem isPreconnected_compl_bd [ConnectedSpace S] (hS : IsSurface S) :
    IsPreconnected (bd S)ᶜ := by
  have heq : (bd S)ᶜ = (univ : Set S) \ bd S := by ext x; simp
  rw [heq]
  exact GraphMinor.GM07.isPreconnected_diff_bd hS isOpen_univ isPreconnected_univ

/-- Product `A ×ℂ B` of two preconnected sets in `ℝ` is preconnected in `ℂ`. -/
theorem isPreconnected_reProdIm {A B : Set ℝ} (hA : IsPreconnected A) (hB : IsPreconnected B) :
    IsPreconnected (A ×ℂ B) := by
  have heq : A ×ℂ B = (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) '' (A ×ˢ B) := by
    ext z; constructor
    · intro hz; rw [Complex.mem_reProdIm] at hz
      exact ⟨(z.re, z.im), hz, by apply Complex.ext <;> simp⟩
    · rintro ⟨p, hp, rfl⟩; rw [Complex.mem_reProdIm]; simp [hp.1, hp.2]
  rw [heq]
  exact (hA.prod hB).image _ (by fun_prop)

/-- An embedded closed box `g : [-a, a] × [-b, b] → (bd S)ᶜ` centered on `A` (`A ∩ box = g '' ({0} × [-b, b])`). -/
structure BoxChart (S : Type) [TopologicalSpace S] (A : Set S) where
  g : ℂ → S
  a : ℝ
  b : ℝ
  ha : 0 < a
  hb : 0 < b
  hgc : ContinuousOn g (Icc (-a) a ×ℂ Icc (-b) b)
  hgi : InjOn g (Icc (-a) a ×ℂ Icc (-b) b)
  hopen : IsOpen (g '' (Ioo (-a) a ×ℂ Ioo (-b) b))
  hgint : g '' (Icc (-a) a ×ℂ Icc (-b) b) ⊆ (bd S)ᶜ
  hA_eq : A ∩ g '' (Icc (-a) a ×ℂ Icc (-b) b) = g '' (({0} : Set ℝ) ×ℂ Icc (-b) b)

namespace BoxChart

variable {A : Set S}

def R (bc : BoxChart S A) : Set ℂ := Icc (-bc.a) bc.a ×ℂ Icc (-bc.b) bc.b
def box (bc : BoxChart S A) : Set S := bc.g '' (Icc (-bc.a) bc.a ×ℂ Icc (-bc.b) bc.b)
def openBox (bc : BoxChart S A) : Set S := bc.g '' (Ioo (-bc.a) bc.a ×ℂ Ioo (-bc.b) bc.b)
def leftHalf (bc : BoxChart S A) : Set S := bc.g '' (Ioo (-bc.a) 0 ×ℂ Ioo (-bc.b) bc.b)
def rightHalf (bc : BoxChart S A) : Set S := bc.g '' (Ioo 0 bc.a ×ℂ Ioo (-bc.b) bc.b)
def clLeftHalf (bc : BoxChart S A) : Set S := bc.g '' (Ico (-bc.a) 0 ×ℂ Icc (-bc.b) bc.b)
def clRightHalf (bc : BoxChart S A) : Set S := bc.g '' (Ioc 0 bc.a ×ℂ Icc (-bc.b) bc.b)

theorem isClosed_box [T2Space S] (bc : BoxChart S A) : IsClosed bc.box :=
  ((isCompact_Icc.reProdIm isCompact_Icc).image_of_continuousOn bc.hgc).isClosed

theorem center_mem_openBox (bc : BoxChart S A) : bc.g 0 ∈ bc.openBox :=
  ⟨0, Complex.mem_reProdIm.mpr ⟨by simp [bc.ha], by simp [bc.hb]⟩, rfl⟩

theorem center_mem_box (bc : BoxChart S A) : bc.g 0 ∈ bc.box :=
  ⟨0, Complex.mem_reProdIm.mpr ⟨by simp [bc.ha.le], by simp [bc.hb.le]⟩, rfl⟩

theorem openBox_subset_box (bc : BoxChart S A) : bc.openBox ⊆ bc.box :=
  image_mono fun _ h => Complex.mem_reProdIm.mpr
    ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).2⟩

theorem leftHalf_subset_clLeft (bc : BoxChart S A) : bc.leftHalf ⊆ bc.clLeftHalf :=
  image_mono fun _ h => Complex.mem_reProdIm.mpr
    ⟨Ioo_subset_Ico_self (Complex.mem_reProdIm.mp h).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).2⟩

theorem rightHalf_subset_clRight (bc : BoxChart S A) : bc.rightHalf ⊆ bc.clRightHalf :=
  image_mono fun _ h => Complex.mem_reProdIm.mpr
    ⟨Ioo_subset_Ioc_self (Complex.mem_reProdIm.mp h).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).2⟩

theorem clLeftHalf_subset_box (bc : BoxChart S A) : bc.clLeftHalf ⊆ bc.box :=
  image_mono fun _ h => Complex.mem_reProdIm.mpr
    ⟨⟨(Complex.mem_reProdIm.mp h).1.1, (Complex.mem_reProdIm.mp h).1.2.le.trans bc.ha.le⟩,
     (Complex.mem_reProdIm.mp h).2⟩

theorem clRightHalf_subset_box (bc : BoxChart S A) : bc.clRightHalf ⊆ bc.box :=
  image_mono fun _ h => Complex.mem_reProdIm.mpr
    ⟨⟨(neg_nonpos.mpr bc.ha.le).trans (Complex.mem_reProdIm.mp h).1.1.le, (Complex.mem_reProdIm.mp h).1.2⟩,
     (Complex.mem_reProdIm.mp h).2⟩

theorem leftHalf_nonempty (bc : BoxChart S A) : bc.leftHalf.Nonempty :=
  ⟨bc.g ((-(bc.a / 2) : ℝ) : ℂ), (-(bc.a / 2) : ℝ),
    Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [bc.ha], by simp; linarith [bc.ha]⟩,
      ⟨by simp; linarith [bc.hb], by simp; linarith [bc.hb]⟩⟩, rfl⟩

theorem rightHalf_nonempty (bc : BoxChart S A) : bc.rightHalf.Nonempty :=
  ⟨bc.g ((bc.a / 2 : ℝ) : ℂ), (bc.a / 2 : ℝ),
    Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [bc.ha], by simp; linarith [bc.ha]⟩,
      ⟨by simp; linarith [bc.hb], by simp; linarith [bc.hb]⟩⟩, rfl⟩

theorem isConnected_box (bc : BoxChart S A) : IsConnected bc.box :=
  ⟨⟨bc.g 0, bc.center_mem_box⟩,
    (isPreconnected_reProdIm isPreconnected_Icc isPreconnected_Icc).image bc.g bc.hgc⟩

theorem isConnected_leftHalf (bc : BoxChart S A) : IsConnected bc.leftHalf :=
  ⟨bc.leftHalf_nonempty, (isPreconnected_reProdIm isPreconnected_Ioo isPreconnected_Ioo).image bc.g
    (bc.hgc.mono fun _ h => Complex.mem_reProdIm.mpr
      ⟨⟨(Complex.mem_reProdIm.mp h).1.1.le, (Complex.mem_reProdIm.mp h).1.2.le.trans bc.ha.le⟩,
       Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).2⟩)⟩

theorem isConnected_rightHalf (bc : BoxChart S A) : IsConnected bc.rightHalf :=
  ⟨bc.rightHalf_nonempty, (isPreconnected_reProdIm isPreconnected_Ioo isPreconnected_Ioo).image bc.g
    (bc.hgc.mono fun _ h => Complex.mem_reProdIm.mpr
      ⟨⟨(neg_nonpos.mpr bc.ha.le).trans (Complex.mem_reProdIm.mp h).1.1.le, (Complex.mem_reProdIm.mp h).1.2.le⟩,
       Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).2⟩)⟩

theorem isConnected_clLeftHalf (bc : BoxChart S A) : IsConnected bc.clLeftHalf :=
  ⟨bc.leftHalf_nonempty.mono bc.leftHalf_subset_clLeft,
    (isPreconnected_reProdIm isPreconnected_Ico isPreconnected_Icc).image bc.g
      (bc.hgc.mono fun _ h => Complex.mem_reProdIm.mpr
        ⟨⟨(Complex.mem_reProdIm.mp h).1.1, (Complex.mem_reProdIm.mp h).1.2.le.trans bc.ha.le⟩,
         (Complex.mem_reProdIm.mp h).2⟩)⟩

theorem isConnected_clRightHalf (bc : BoxChart S A) : IsConnected bc.clRightHalf :=
  ⟨bc.rightHalf_nonempty.mono bc.rightHalf_subset_clRight,
    (isPreconnected_reProdIm isPreconnected_Ioc isPreconnected_Icc).image bc.g
      (bc.hgc.mono fun _ h => Complex.mem_reProdIm.mpr
        ⟨⟨(neg_nonpos.mpr bc.ha.le).trans (Complex.mem_reProdIm.mp h).1.1.le, (Complex.mem_reProdIm.mp h).1.2⟩,
         (Complex.mem_reProdIm.mp h).2⟩)⟩

theorem clLeftHalf_disj_A (bc : BoxChart S A) : Disjoint bc.clLeftHalf A := by
  rw [Set.disjoint_left]; rintro _ ⟨z, hz, rfl⟩ hzA
  have h1 : bc.g z ∈ A ∩ bc.box := ⟨hzA, bc.clLeftHalf_subset_box ⟨z, hz, rfl⟩⟩
  rw [BoxChart.box, bc.hA_eq] at h1
  obtain ⟨w, hw, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hw hz
  have hwR : w ∈ bc.R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith [bc.ha], bc.ha.le⟩, hw.2⟩
  have hzR : z ∈ bc.R := Complex.mem_reProdIm.mpr ⟨⟨hz.1.1, hz.1.2.le.trans bc.ha.le⟩, hz.2⟩
  have hzw := bc.hgi hzR hwR hfe.symm
  have : z.re = 0 := by rw [hzw]; exact mem_singleton_iff.mp hw.1
  linarith [hz.1.2]

theorem clRightHalf_disj_A (bc : BoxChart S A) : Disjoint bc.clRightHalf A := by
  rw [Set.disjoint_left]; rintro _ ⟨z, hz, rfl⟩ hzA
  have h1 : bc.g z ∈ A ∩ bc.box := ⟨hzA, bc.clRightHalf_subset_box ⟨z, hz, rfl⟩⟩
  rw [BoxChart.box, bc.hA_eq] at h1
  obtain ⟨w, hw, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hw hz
  have hwR : w ∈ bc.R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith [bc.ha], bc.ha.le⟩, hw.2⟩
  have hzR : z ∈ bc.R := Complex.mem_reProdIm.mpr ⟨⟨(neg_nonpos.mpr bc.ha.le).trans hz.1.1.le, hz.1.2⟩, hz.2⟩
  have hzw := bc.hgi hzR hwR hfe.symm
  have : z.re = 0 := by rw [hzw]; exact mem_singleton_iff.mp hw.1
  linarith [hz.1.1]

theorem openBox_diff_A (bc : BoxChart S A) : bc.openBox \ A = bc.leftHalf ∪ bc.rightHalf := by
  ext y; constructor
  · rintro ⟨⟨z, hz, rfl⟩, hyA⟩
    rw [Complex.mem_reProdIm] at hz
    have hne : z.re ≠ 0 := fun h0 => hyA (by
      have h1 : bc.g z ∈ A ∩ bc.box := by
        rw [BoxChart.box, bc.hA_eq]; exact ⟨z, Complex.mem_reProdIm.mpr ⟨h0, Ioo_subset_Icc_self hz.2⟩, rfl⟩
      exact h1.1)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨z, Complex.mem_reProdIm.mpr ⟨⟨hz.1.1, hlt⟩, hz.2⟩, rfl⟩
    · exact Or.inr ⟨z, Complex.mem_reProdIm.mpr ⟨⟨hgt, hz.1.2⟩, hz.2⟩, rfl⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨⟨z, Complex.mem_reProdIm.mpr ⟨⟨(Complex.mem_reProdIm.mp hz).1.1, (Complex.mem_reProdIm.mp hz).1.2.trans bc.ha⟩,
        (Complex.mem_reProdIm.mp hz).2⟩, rfl⟩,
        Set.disjoint_left.mp bc.clLeftHalf_disj_A (bc.leftHalf_subset_clLeft ⟨z, hz, rfl⟩)⟩
    · exact ⟨⟨z, Complex.mem_reProdIm.mpr ⟨⟨(neg_lt_zero.mpr bc.ha).trans (Complex.mem_reProdIm.mp hz).1.1, (Complex.mem_reProdIm.mp hz).1.2⟩,
        (Complex.mem_reProdIm.mp hz).2⟩, rfl⟩,
        Set.disjoint_left.mp bc.clRightHalf_disj_A (bc.rightHalf_subset_clRight ⟨z, hz, rfl⟩)⟩

theorem mid_subset_closure_leftHalf (bc : BoxChart S A) :
    bc.g '' (({0} : Set ℝ) ×ℂ Ioo (-bc.b) bc.b) ⊆ closure bc.leftHalf := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Complex.mem_reProdIm] at hz
  have hzre : z.re = 0 := mem_singleton_iff.mp hz.1
  have hzR : z ∈ bc.R := Complex.mem_reProdIm.mpr ⟨by rw [hzre]; exact ⟨by linarith [bc.ha], bc.ha.le⟩, Ioo_subset_Icc_self hz.2⟩
  let seq : ℕ → ℂ := fun n => z - (((bc.a / ((n : ℝ) + 2)) : ℝ) : ℂ)
  have hlim : Filter.Tendsto (fun n => bc.g (seq n)) Filter.atTop (𝓝 (bc.g z)) := by
    refine (bc.hgc.continuousWithinAt hzR).tendsto.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Filter.Eventually.of_forall fun n => ?_)
    · have h0 : Filter.Tendsto (fun n : ℕ => bc.a / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
        have ht0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
        simpa [div_eq_mul_inv, mul_comm] using (tendsto_const_nhds (x := bc.a)).mul (ht0.congr fun n => by simp; ring)
      simpa [seq] using tendsto_const_nhds.sub (Complex.continuous_ofReal.continuousAt.tendsto.comp h0)
    · rw [Complex.mem_reProdIm]
      have hpos : 0 < bc.a / ((n : ℝ) + 2) := by positivity [bc.ha]
      have hle : bc.a / ((n : ℝ) + 2) < bc.a := (div_lt_iff₀ (by positivity)).mpr (by nlinarith [bc.ha])
      simp only [seq, sub_re, sub_im, ofReal_re, ofReal_im, hzre, zero_sub, sub_zero]
      exact ⟨⟨by linarith, by linarith⟩, Ioo_subset_Icc_self hz.2⟩
  refine mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  refine ⟨seq n, ?_, rfl⟩
  rw [Complex.mem_reProdIm]
  have hpos : 0 < bc.a / ((n : ℝ) + 2) := by positivity [bc.ha]
  have hle : bc.a / ((n : ℝ) + 2) < bc.a := (div_lt_iff₀ (by positivity)).mpr (by nlinarith [bc.ha])
  simp only [seq, sub_re, sub_im, ofReal_re, ofReal_im, hzre, zero_sub, sub_zero]
  exact ⟨⟨by linarith, by linarith⟩, hz.2⟩

theorem mid_subset_closure_rightHalf (bc : BoxChart S A) :
    bc.g '' (({0} : Set ℝ) ×ℂ Ioo (-bc.b) bc.b) ⊆ closure bc.rightHalf := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Complex.mem_reProdIm] at hz
  have hzre : z.re = 0 := mem_singleton_iff.mp hz.1
  have hzR : z ∈ bc.R := Complex.mem_reProdIm.mpr ⟨by rw [hzre]; exact ⟨by linarith [bc.ha], bc.ha.le⟩, Ioo_subset_Icc_self hz.2⟩
  let seq : ℕ → ℂ := fun n => z + (((bc.a / ((n : ℝ) + 2)) : ℝ) : ℂ)
  have hlim : Filter.Tendsto (fun n => bc.g (seq n)) Filter.atTop (𝓝 (bc.g z)) := by
    refine (bc.hgc.continuousWithinAt hzR).tendsto.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Filter.Eventually.of_forall fun n => ?_)
    · have h0 : Filter.Tendsto (fun n : ℕ => bc.a / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
        have ht0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
        simpa [div_eq_mul_inv, mul_comm] using (tendsto_const_nhds (x := bc.a)).mul (ht0.congr fun n => by simp; ring)
      simpa [seq] using tendsto_const_nhds.add (Complex.continuous_ofReal.continuousAt.tendsto.comp h0)
    · rw [Complex.mem_reProdIm]
      have hpos : 0 < bc.a / ((n : ℝ) + 2) := by positivity [bc.ha]
      have hle : bc.a / ((n : ℝ) + 2) < bc.a := (div_lt_iff₀ (by positivity)).mpr (by nlinarith [bc.ha])
      simp only [seq, add_re, add_im, ofReal_re, ofReal_im, hzre, zero_add, add_zero]
      exact ⟨⟨by linarith, by linarith⟩, Ioo_subset_Icc_self hz.2⟩
  refine mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  refine ⟨seq n, ?_, rfl⟩
  rw [Complex.mem_reProdIm]
  have hpos : 0 < bc.a / ((n : ℝ) + 2) := by positivity [bc.ha]
  have hle : bc.a / ((n : ℝ) + 2) < bc.a := (div_lt_iff₀ (by positivity)).mpr (by nlinarith [bc.ha])
  simp only [seq, add_re, add_im, ofReal_re, ofReal_im, hzre, zero_add, add_zero]
  exact ⟨⟨by linarith, by linarith⟩, hz.2⟩

theorem center_mem_closure_leftHalf (bc : BoxChart S A) : bc.g 0 ∈ closure bc.leftHalf :=
  bc.mid_subset_closure_leftHalf ⟨0, Complex.mem_reProdIm.mpr ⟨rfl, by simp [bc.hb]⟩, rfl⟩

theorem center_mem_closure_rightHalf (bc : BoxChart S A) : bc.g 0 ∈ closure bc.rightHalf :=
  bc.mid_subset_closure_rightHalf ⟨0, Complex.mem_reProdIm.mpr ⟨rfl, by simp [bc.hb]⟩, rfl⟩

/-- Horizontal reflection `z ↦ -z` of a `BoxChart`, swapping `leftHalf` and `rightHalf`. -/
def flip (bc : BoxChart S A) : BoxChart S A where
  g := fun z => bc.g (-z)
  a := bc.a
  b := bc.b
  ha := bc.ha
  hb := bc.hb
  hgc := bc.hgc.comp continuous_neg.continuousOn fun z hz => by
    rw [Complex.mem_reProdIm] at hz ⊢
    simp only [neg_re, neg_im]; exact ⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩, ⟨by linarith [hz.2.2], by linarith [hz.2.1]⟩⟩
  hgi := fun z₁ hz₁ z₂ hz₂ he => neg_injective (bc.hgi
    (by rw [Complex.mem_reProdIm] at hz₁ ⊢; simp only [neg_re, neg_im]; exact ⟨⟨by linarith [hz₁.1.2], by linarith [hz₁.1.1]⟩, ⟨by linarith [hz₁.2.2], by linarith [hz₁.2.1]⟩⟩)
    (by rw [Complex.mem_reProdIm] at hz₂ ⊢; simp only [neg_re, neg_im]; exact ⟨⟨by linarith [hz₂.1.2], by linarith [hz₂.1.1]⟩, ⟨by linarith [hz₂.2.2], by linarith [hz₂.2.1]⟩⟩) he)
  hopen := by
    have heq : (fun z => bc.g (-z)) '' (Ioo (-bc.a) bc.a ×ℂ Ioo (-bc.b) bc.b) = bc.openBox := by
      ext y; constructor
      · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
        exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩,
          ⟨by simp; linarith [hz.2.2], by simp; linarith [hz.2.1]⟩⟩, rfl⟩
      · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
        exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩,
          ⟨by simp; linarith [hz.2.2], by simp; linarith [hz.2.1]⟩⟩, by simp⟩
    rw [heq]; exact bc.hopen
  hgint := by
    rintro _ ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
    exact bc.hgint ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩,
      ⟨by simp; linarith [hz.2.2], by simp; linarith [hz.2.1]⟩⟩, rfl⟩
  hA_eq := by
    have hbox : (fun z => bc.g (-z)) '' (Icc (-bc.a) bc.a ×ℂ Icc (-bc.b) bc.b) = bc.box := by
      ext y; constructor
      · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
        exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩,
          ⟨by simp; linarith [hz.2.2], by simp; linarith [hz.2.1]⟩⟩, rfl⟩
      · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
        exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp; linarith [hz.1.2], by simp; linarith [hz.1.1]⟩,
          ⟨by simp; linarith [hz.2.2], by simp; linarith [hz.2.1]⟩⟩, by simp⟩
    rw [hbox, BoxChart.box, bc.hA_eq]
    ext y; constructor
    · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
      exact ⟨-z, Complex.mem_reProdIm.mpr ⟨by simp [mem_singleton_iff.mp hz.1],
        ⟨by simp; linarith [hz.2.2], by simp; linarith [hz.2.1]⟩⟩, by simp⟩
    · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
      exact ⟨-z, Complex.mem_reProdIm.mpr ⟨by simp [mem_singleton_iff.mp hz.1],
        ⟨by simp; linarith [hz.2.2], by simp; linarith [hz.2.1]⟩⟩, rfl⟩

theorem flip_box (bc : BoxChart S A) : bc.flip.box = bc.box := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩; dsimp only [flip] at hz ⊢; rw [Complex.mem_reProdIm] at hz
    exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp only [neg_re]; linarith [hz.1.2], by simp only [neg_re]; linarith [hz.1.1]⟩,
      ⟨by simp only [neg_im]; linarith [hz.2.2], by simp only [neg_im]; linarith [hz.2.1]⟩⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩; dsimp only [flip] at hz ⊢; rw [Complex.mem_reProdIm] at hz
    exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp only [neg_re]; linarith [hz.1.2], by simp only [neg_re]; linarith [hz.1.1]⟩,
      ⟨by simp only [neg_im]; linarith [hz.2.2], by simp only [neg_im]; linarith [hz.2.1]⟩⟩, by simp⟩

theorem flip_leftHalf (bc : BoxChart S A) : bc.flip.leftHalf = bc.rightHalf := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩; dsimp only [flip] at hz ⊢; rw [Complex.mem_reProdIm] at hz
    exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp only [neg_re]; linarith [hz.1.2], by simp only [neg_re]; linarith [hz.1.1]⟩,
      ⟨by simp only [neg_im]; linarith [hz.2.2], by simp only [neg_im]; linarith [hz.2.1]⟩⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩; dsimp only [flip] at hz ⊢; rw [Complex.mem_reProdIm] at hz
    exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp only [neg_re]; linarith [hz.1.2], by simp only [neg_re]; linarith [hz.1.1]⟩,
      ⟨by simp only [neg_im]; linarith [hz.2.2], by simp only [neg_im]; linarith [hz.2.1]⟩⟩, by simp⟩

theorem flip_rightHalf (bc : BoxChart S A) : bc.flip.rightHalf = bc.leftHalf := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩; dsimp only [flip] at hz ⊢; rw [Complex.mem_reProdIm] at hz
    exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp only [neg_re]; linarith [hz.1.2], by simp only [neg_re]; linarith [hz.1.1]⟩,
      ⟨by simp only [neg_im]; linarith [hz.2.2], by simp only [neg_im]; linarith [hz.2.1]⟩⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩; dsimp only [flip] at hz ⊢; rw [Complex.mem_reProdIm] at hz
    exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp only [neg_re]; linarith [hz.1.2], by simp only [neg_re]; linarith [hz.1.1]⟩,
      ⟨by simp only [neg_im]; linarith [hz.2.2], by simp only [neg_im]; linarith [hz.2.1]⟩⟩, by simp⟩

theorem flip_clLeftHalf (bc : BoxChart S A) : bc.flip.clLeftHalf = bc.clRightHalf := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩; dsimp only [flip] at hz ⊢; rw [Complex.mem_reProdIm] at hz
    exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp only [neg_re]; linarith [hz.1.2], by simp only [neg_re]; linarith [hz.1.1]⟩,
      ⟨by simp only [neg_im]; linarith [hz.2.2], by simp only [neg_im]; linarith [hz.2.1]⟩⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩; dsimp only [flip] at hz ⊢; rw [Complex.mem_reProdIm] at hz
    exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp only [neg_re]; linarith [hz.1.2], by simp only [neg_re]; linarith [hz.1.1]⟩,
      ⟨by simp only [neg_im]; linarith [hz.2.2], by simp only [neg_im]; linarith [hz.2.1]⟩⟩, by simp⟩

theorem flip_clRightHalf (bc : BoxChart S A) : bc.flip.clRightHalf = bc.clLeftHalf := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩; dsimp only [flip] at hz ⊢; rw [Complex.mem_reProdIm] at hz
    exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp only [neg_re]; linarith [hz.1.2], by simp only [neg_re]; linarith [hz.1.1]⟩,
      ⟨by simp only [neg_im]; linarith [hz.2.2], by simp only [neg_im]; linarith [hz.2.1]⟩⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩; dsimp only [flip] at hz ⊢; rw [Complex.mem_reProdIm] at hz
    exact ⟨-z, Complex.mem_reProdIm.mpr ⟨⟨by simp only [neg_re]; linarith [hz.1.2], by simp only [neg_re]; linarith [hz.1.1]⟩,
      ⟨by simp only [neg_im]; linarith [hz.2.2], by simp only [neg_im]; linarith [hz.2.1]⟩⟩, by simp⟩

/-- Shrink a `BoxChart` into any open neighborhood `W` of its center `bc.g 0`. -/
theorem exists_shrink_subset (hS : IsSurface S) (bc : BoxChart S A) {W : Set S}
    (hWo : IsOpen W) (h0W : bc.g 0 ∈ W) :
    ∃ bc' : BoxChart S A, bc'.g 0 = bc.g 0 ∧ bc'.box ⊆ bc.box ∧ bc'.box ⊆ W := by
  have h0R : (0 : ℂ) ∈ bc.R := Complex.mem_reProdIm.mpr ⟨by simp [bc.ha.le], by simp [bc.hb.le]⟩
  have hpre : bc.g ⁻¹' W ∈ 𝓝[bc.R] (0 : ℂ) := bc.hgc.continuousWithinAt h0R (hWo.mem_nhds h0W)
  rw [Metric.mem_nhdsWithin_iff] at hpre
  obtain ⟨r, hr, hrsub⟩ := hpre
  let a' : ℝ := min bc.a (r / 4)
  let b' : ℝ := min bc.b (r / 4)
  have ha' : 0 < a' := lt_min bc.ha (div_pos hr (by norm_num))
  have hb' : 0 < b' := lt_min bc.hb (div_pos hr (by norm_num))
  have hsubR : Icc (-a') a' ×ℂ Icc (-b') b' ⊆ bc.R := fun z hz => by
    dsimp only [BoxChart.R]; rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨⟨by linarith [hz.1.1, min_le_left bc.a (r / 4)], by linarith [hz.1.2, min_le_left bc.a (r / 4)]⟩,
      ⟨by linarith [hz.2.1, min_le_left bc.b (r / 4)], by linarith [hz.2.2, min_le_left bc.b (r / 4)]⟩⟩
  have hsubW : bc.g '' (Icc (-a') a' ×ℂ Icc (-b') b') ⊆ W := by
    rintro _ ⟨z, hz, rfl⟩
    refine hrsub ⟨?_, hsubR hz⟩
    rw [mem_ball_zero_iff]; rw [Complex.mem_reProdIm] at hz
    have hnorm : ‖z‖ ≤ |z.re| + |z.im| := by
      calc ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * I‖ := by congr 1; apply Complex.ext <;> simp
        _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have ha'4 : a' ≤ r / 4 := min_le_right _ _
    have hb'4 : b' ≤ r / 4 := min_le_right _ _
    linarith [abs_le.mpr hz.1, abs_le.mpr hz.2]
  have hA' : A ∩ bc.g '' (Icc (-a') a' ×ℂ Icc (-b') b') = bc.g '' (({0} : Set ℝ) ×ℂ Icc (-b') b') := by
    ext y; constructor
    · rintro ⟨hyA, z, hz, rfl⟩
      have h1 : bc.g z ∈ A ∩ bc.box := ⟨hyA, z, hsubR hz, rfl⟩
      rw [BoxChart.box, bc.hA_eq] at h1
      obtain ⟨w, hw, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hw
      have hwR : w ∈ bc.R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith [bc.ha], bc.ha.le⟩, hw.2⟩
      have hzw := bc.hgi (hsubR hz) hwR hfe.symm
      exact ⟨z, Complex.mem_reProdIm.mpr ⟨by rw [hzw]; exact hw.1, (Complex.mem_reProdIm.mp hz).2⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Complex.mem_reProdIm] at hz
      have hz' : z ∈ Icc (-a') a' ×ℂ Icc (-b') b' :=
        Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by linarith, ha'.le⟩, hz.2⟩
      have h1 : bc.g z ∈ A ∩ bc.box := by
        rw [BoxChart.box, bc.hA_eq]
        exact ⟨z, Complex.mem_reProdIm.mpr ⟨hz.1, (Complex.mem_reProdIm.mp (hsubR hz')).2⟩, rfl⟩
      exact ⟨h1.1, z, hz', rfl⟩
  let bc' : BoxChart S A := {
    g := bc.g, a := a', b := b', ha := ha', hb := hb',
    hgc := bc.hgc.mono hsubR, hgi := bc.hgi.mono hsubR,
    hopen := isOpen_image_of_manifold (isOpen_Ioo.reProdIm isOpen_Ioo)
      (bc.hgc.mono fun z hz => hsubR (Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩))
      (bc.hgi.mono fun z hz => hsubR (Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩))
      (fun _ _ => hS.2.2 _),
    hgint := (image_mono hsubR).trans bc.hgint,
    hA_eq := hA' }
  exact ⟨bc', rfl, image_mono hsubR, hsubW⟩

end BoxChart

/-- Build a local `BoxChart S A` around an interior point `p ∈ A` inside an open neighborhood `W ⊆ (bd S)ᶜ`,
given a local injective arc `γ : [0, 1] → A` with `γ t₀ = p` (`t₀ ∈ (0, 1)`) and an open `W₀ ∋ p`
such that `A ∩ W₀ ⊆ γ '' [0, 1]`. -/
theorem exists_local_arc_box (hS : IsSurface S) {A : Set S} {p : S}
    {γ : ℝ → S} {t₀ : ℝ} {W₀ W : Set S}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγA : γ '' Icc 0 1 ⊆ A) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hp : γ t₀ = p)
    (hW₀o : IsOpen W₀) (hpW₀ : p ∈ W₀) (hAW₀ : A ∩ W₀ ⊆ γ '' Icc 0 1)
    (hWo : IsOpen W) (hpW : p ∈ W) (hWint : W ⊆ (bd S)ᶜ) :
    ∃ bc : BoxChart S A, bc.g 0 = p ∧ bc.box ⊆ W := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  -- Restrict `γ` to `[t₀ - δ, t₀ + δ] ⊆ (0, 1)` mapped into `W ∩ W₀`:
  have hpre : γ ⁻¹' (W ∩ W₀) ∈ 𝓝[Icc (0 : ℝ) 1] t₀ :=
    hγc.continuousWithinAt (Ioo_subset_Icc_self ht₀) ((hWo.inter hW₀o).mem_nhds (hp.symm ▸ ⟨hpW, hpW₀⟩))
  rw [Metric.mem_nhdsWithin_iff] at hpre
  obtain ⟨r₁, hr₁, hr₁sub⟩ := hpre
  let δ : ℝ := min (r₁ / 2) (min (t₀ / 2) ((1 - t₀) / 2))
  have hδ : 0 < δ := lt_min (half_pos hr₁) (lt_min (half_pos ht₀.1) (half_pos (by linarith [ht₀.2])))
  have hsub01 : Icc (t₀ - δ) (t₀ + δ) ⊆ Icc (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1, min_le_right (r₁ / 2) (min (t₀ / 2) ((1 - t₀) / 2)), min_le_left (t₀ / 2) ((1 - t₀) / 2)],
     by linarith [ht.2, min_le_right (r₁ / 2) (min (t₀ / 2) ((1 - t₀) / 2)), min_le_right (t₀ / 2) ((1 - t₀) / 2)]⟩
  have hsubWW₀ : γ '' Icc (t₀ - δ) (t₀ + δ) ⊆ W ∩ W₀ := by
    rintro _ ⟨t, ht, rfl⟩
    refine hr₁sub ⟨?_, hsub01 ht⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hδle : δ ≤ r₁ / 2 := min_le_left _ _
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- Cap `S` to closed surface `T` and build strip chart for `subArc γ (t₀ - δ) (t₀ + δ)`:
  let γs : ℝ → S := subArc γ (t₀ - δ) (t₀ + δ)
  have hγsc : ContinuousOn γs (Icc 0 1) := continuousOn_subArc (by linarith) (hγc.mono hsub01)
  have hγsi : InjOn γs (Icc 0 1) := injOn_subArc (by linarith) (hγi.mono hsub01)
  have hγsim : γs '' Icc 0 1 = γ '' Icc (t₀ - δ) (t₀ + δ) := subArc_image (by linarith)
  have hγs_half : γs (1 / 2) = p := by
    simp only [γs, subArc, lin]; ring_nf; exact hp
  obtain ⟨T, _, j, Kcap, hT, hj, hKcap, hcov, hinter, -⟩ := exists_capAll S hS
  have : T2Space T := hT.2.1
  have hji := hj.injective
  obtain ⟨O₀, K₀, θ, hK₀, hθc, hθm, hθ⟩ := GraphMinor.GM07.exists_stripChart_of_arc hT
    ⟨hj.continuous.comp (continuousOn_iff_continuous_domRestrict.mp hγsc),
     hji.comp fun r₁ r₂ he => Subtype.ext (hγsi r₁.2 r₂.2 he)⟩
  have hjint_open : IsOpen (j '' (bd S)ᶜ) := by
    have heq : j '' (bd S)ᶜ = Kcapᶜ := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩ hyK
        obtain ⟨x', hx', he⟩ := (hinter ▸ ⟨⟨x, rfl⟩, hyK⟩ : j x ∈ j '' bd S)
        exact hx (hji he ▸ hx')
      · intro hyK
        obtain ⟨x, rfl⟩ := ((Set.ext_iff.mp hcov y).mpr (mem_univ y)).resolve_right hyK
        exact ⟨x, fun hx => hyK (hinter.symm ▸ ⟨x, hx, rfl⟩ : j x ∈ range j ∩ Kcap).2, rfl⟩
    rw [heq]; exact hKcap.isOpen_compl
  let O : Set ℂ := O₀ ∩ K₀ ⁻¹' (j '' (bd S)ᶜ)
  have hOo : IsOpen O := by
    rw [isOpen_iff_mem_nhds]; intro z ⟨hz0, hz1⟩
    have h1 := hK₀.hc.continuousWithinAt hz0 (hjint_open.mem_nhds hz1)
    rw [nhdsWithin_eq_nhds.mpr (hK₀.isOpen.mem_nhds hz0)] at h1
    exact Filter.inter_mem (hK₀.isOpen.mem_nhds hz0) h1
  classical
  let K : ℂ → S := fun z => if hz : K₀ z ∈ range j then Classical.choose hz else p
  have hjK : ∀ z ∈ O, j (K z) = K₀ z := fun z hz => by
    have hr : K₀ z ∈ range j := by obtain ⟨x, -, hx⟩ := hz.2; exact ⟨x, hx⟩
    simp only [K, dite_eq_left hr]; exact Classical.choose_spec hr
  have hKc : ContinuousOn K O := by
    rw [continuousOn_iff_continuous_domRestrict, hj.continuous_iff]
    exact (hK₀.hc.mono inter_subset_left).domRestrict.congr fun z => (hjK z.1 z.2).symm
  have hKi : InjOn K O := fun z₁ hz₁ z₂ hz₂ he =>
    hK₀.hi hz₁.1 hz₂.1 (by rw [← hjK z₁ hz₁, ← hjK z₂ hz₂, he])
  have hθ_O : ∀ r : unitInterval, (θ r : ℂ) ∈ O ∧ K (θ r) = γs r.1 := fun r => by
    have h1 := hθ r
    have hm : K₀ (θ r) ∈ j '' (bd S)ᶜ := h1.2.symm ▸
      ⟨γs r.1, hWint (hsubWW₀ (hγsim ▸ ⟨r.1, r.2, rfl⟩)).1, rfl⟩
    refine ⟨⟨h1.1, hm⟩, hji ((hjK _ ⟨h1.1, hm⟩).trans h1.2)⟩
  -- Exclude the closed outer part `Z_out := γ '' (Icc 0 (t₀ - δ) ∪ Icc (t₀ + δ) 1)` from `W ∩ W₀`:
  have hsubL : 0 ≤ t₀ - δ := (hsub01 ⟨le_rfl, by linarith⟩).1
  have hsubL1 : t₀ - δ ≤ 1 := (hsub01 ⟨le_rfl, by linarith⟩).2
  have hsubR0 : 0 ≤ t₀ + δ := (hsub01 ⟨by linarith, le_rfl⟩).1
  let Z_out : Set S := γ '' (Icc 0 (t₀ - δ) ∪ Icc (t₀ + δ) 1)
  have hZ_closed : IsClosed Z_out :=
    ((isCompact_Icc.union isCompact_Icc).image_of_continuousOn
      (hγc.mono (union_subset (Icc_subset_Icc_right hsubL1) (Icc_subset_Icc_left hsubR0)))).isClosed
  have hp_notZ : p ∉ Z_out := by
    rintro ⟨t, ht | ht, hte⟩
    · have h1 := hγi ⟨ht.1, ht.2.trans hsubL1⟩ (Ioo_subset_Icc_self ht₀) (hte.trans hp.symm)
      linarith [ht.2]
    · have h1 := hγi ⟨hsubR0.trans ht.1, ht.2⟩ (Ioo_subset_Icc_self ht₀) (hte.trans hp.symm)
      linarith [ht.1]
  let W₁ : Set S := W ∩ W₀ ∩ Z_outᶜ
  have hW₁o : IsOpen W₁ := (hWo.inter hW₀o).inter hZ_closed.isOpen_compl
  have hpW₁ : p ∈ W₁ := ⟨⟨hpW, hpW₀⟩, hp_notZ⟩
  let r_half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let x₀ : ℝ := θ r_half
  have hx₀O : (x₀ : ℂ) ∈ O := (hθ_O r_half).1
  have hKx₀ : K (x₀ : ℂ) = p := (hθ_O r_half).2.trans hγs_half
  have hU_open : IsOpen (O ∩ K ⁻¹' W₁) := by
    rw [isOpen_iff_mem_nhds]; intro z ⟨hzO, hzW⟩
    have h1 := hKc.continuousWithinAt hzO (hW₁o.mem_nhds hzW)
    rw [nhdsWithin_eq_nhds.mpr (hOo.mem_nhds hzO)] at h1
    exact Filter.inter_mem (hOo.mem_nhds hzO) h1
  obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ := Metric.isOpen_iff.mp hU_open (x₀ : ℂ) ⟨hx₀O, show K (x₀ : ℂ) ∈ W₁ by rw [hKx₀]; exact hpW₁⟩
  have hltL : θ 0 < x₀ := hθm (show (0 : unitInterval) < r_half by change (0 : ℝ) < 1 / 2; norm_num)
  have hltR : x₀ < θ 1 := hθm (show r_half < (1 : unitInterval) by change (1 / 2 : ℝ) < 1; norm_num)
  let ρ : ℝ := min (ρ₀ / 4) (min ((x₀ - θ 0) / 2) ((θ 1 - x₀) / 2))
  have hρ : 0 < ρ := lt_min (div_pos hρ₀ (by norm_num)) (lt_min (half_pos (by linarith)) (half_pos (by linarith)))
  let rot : ℂ → ℂ := fun z => (x₀ : ℂ) - z * I
  let g : ℂ → S := fun z => K (rot z)
  have hrot_maps : MapsTo rot (Icc (-ρ) ρ ×ℂ Icc (-ρ) ρ) (O ∩ K ⁻¹' W₁) := fun z hz => by
    refine hρ₀sub ?_
    rw [mem_ball, dist_eq_norm]; rw [Complex.mem_reProdIm] at hz
    have heq : rot z - (x₀ : ℂ) = -(z * I) := by simp [rot]
    rw [heq, norm_neg, norm_mul, Complex.norm_I, mul_one]
    have hnorm : ‖z‖ ≤ |z.re| + |z.im| := by
      calc ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * I‖ := by congr 1; apply Complex.ext <;> simp
        _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hρ4 : ρ ≤ ρ₀ / 4 := min_le_left _ _
    linarith [abs_le.mpr hz.1, abs_le.mpr hz.2]
  have hrot_inj : Function.Injective rot := fun z₁ z₂ he => by
    have h1 : z₁ * I = z₂ * I := by linear_combination -he
    exact mul_right_cancel₀ Complex.I_ne_zero h1
  have hA_eq : A ∩ g '' (Icc (-ρ) ρ ×ℂ Icc (-ρ) ρ) = g '' (({0} : Set ℝ) ×ℂ Icc (-ρ) ρ) := by
    ext y; constructor
    · rintro ⟨hyA, z, hz, rfl⟩
      have hm := hrot_maps hz
      have hγmem : g z ∈ γ '' Icc 0 1 := hAW₀ ⟨hyA, hm.2.1.2⟩
      obtain ⟨t, ht, hte⟩ := hγmem
      have htin : t ∈ Icc (t₀ - δ) (t₀ + δ) := by
        by_contra hnot
        refine hm.2.2 ⟨t, ?_, hte⟩
        rcases lt_or_ge t (t₀ - δ) with h1 | h1
        · exact Or.inl ⟨ht.1, h1.le⟩
        · exact Or.inr ⟨le_of_not_ge fun h2 => hnot ⟨h1, h2⟩, ht.2⟩
      have hγsm : g z ∈ γs '' Icc 0 1 := hγsim.symm ▸ ⟨t, htin, hte⟩
      obtain ⟨r, hr, hre⟩ := hγsm
      let ru : unitInterval := ⟨r, hr⟩
      have hKr : K (θ ru : ℂ) = g z := (hθ_O ru).2.trans hre
      have heq := hKi (hθ_O ru).1 hm.1 hKr
      have him0 : (rot z).im = 0 := by rw [← heq]; simp
      have hzre : z.re = 0 := by
        simp only [rot, sub_im, ofReal_im, mul_im, I_im, I_re, mul_one, mul_zero, add_zero, zero_sub, neg_eq_zero] at him0
        exact him0
      exact ⟨z, Complex.mem_reProdIm.mpr ⟨hzre, (Complex.mem_reProdIm.mp hz).2⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      rw [Complex.mem_reProdIm] at hz
      have hzre : z.re = 0 := mem_singleton_iff.mp hz.1
      have hzsq : z ∈ Icc (-ρ) ρ ×ℂ Icc (-ρ) ρ :=
        Complex.mem_reProdIm.mpr ⟨by rw [hzre]; exact ⟨by linarith, hρ.le⟩, hz.2⟩
      have hrot_re : (rot z).re = x₀ + z.im := by
        simp only [rot, sub_re, ofReal_re, mul_re, I_re, I_im, mul_zero, mul_one, zero_sub, sub_neg_eq_add]
      have hrot_im : (rot z).im = 0 := by
        simp only [rot, sub_im, ofReal_im, mul_im, I_im, I_re, mul_one, mul_zero, add_zero, zero_sub, hzre, neg_zero]
      have hleL : θ 0 ≤ x₀ + z.im := by
        have := (min_le_right (ρ₀ / 4) _).trans (min_le_left ((x₀ - θ 0) / 2) ((θ 1 - x₀) / 2))
        linarith [hz.2.1]
      have hleR : x₀ + z.im ≤ θ 1 := by
        have := (min_le_right (ρ₀ / 4) _).trans (min_le_right ((x₀ - θ 0) / 2) ((θ 1 - x₀) / 2))
        linarith [hz.2.2]
      let fn : ℝ → ℝ := fun r => if hr : r ∈ Icc (0 : ℝ) 1 then θ ⟨r, hr⟩ else 0
      have hfn_c : ContinuousOn fn (Icc 0 1) := by
        rw [continuousOn_iff_continuous_domRestrict]
        exact hθc.congr fun r => by simp only [Set.domRestrict, fn, dite_eq_left r.2]
      have hfn0 : fn 0 = θ 0 := by simp [fn]
      have hfn1 : fn 1 = θ 1 := by simp [fn]
      obtain ⟨r, hr, hreq⟩ := intermediate_value_Icc zero_le_one hfn_c
        (show x₀ + z.im ∈ Icc (fn 0) (fn 1) from by rw [hfn0, hfn1]; exact ⟨hleL, hleR⟩)
      simp only [fn, dite_eq_left hr] at hreq
      have hrot_eq : rot z = (θ ⟨r, hr⟩ : ℂ) := Complex.ext (by rw [hrot_re, ofReal_re, hreq]) (by simp [hrot_im])
      have hgzA : g z ∈ A := by
        dsimp only [g]; rw [hrot_eq, (hθ_O ⟨r, hr⟩).2]
        obtain ⟨t, ht, hte⟩ := hγsim.subset ⟨r, hr, rfl⟩
        exact hte ▸ hγA ⟨t, hsub01 ht, rfl⟩
      exact ⟨hgzA, z, hzsq, rfl⟩
  have hopen_im : IsOpen (g '' (Ioo (-ρ) ρ ×ℂ Ioo (-ρ) ρ)) := by
    have hsub_oo : Ioo (-ρ) ρ ×ℂ Ioo (-ρ) ρ ⊆ Icc (-ρ) ρ ×ℂ Icc (-ρ) ρ := fun _ h =>
      Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).2⟩
    exact isOpen_image_of_manifold (isOpen_Ioo.reProdIm isOpen_Ioo)
      ((hKc.comp (by fun_prop) (hrot_maps.mono_right inter_subset_left)).mono hsub_oo)
      (fun z₁ hz₁ z₂ hz₂ he => hrot_inj (hKi (hrot_maps (hsub_oo hz₁)).1 (hrot_maps (hsub_oo hz₂)).1 he))
      (fun _ _ => hS.2.2 _)
  let bc : BoxChart S A :=
    { g := g, a := ρ, b := ρ, ha := hρ, hb := hρ,
      hgc := hKc.comp (by fun_prop) (hrot_maps.mono_right inter_subset_left),
      hgi := fun z₁ hz₁ z₂ hz₂ he => hrot_inj (hKi (hrot_maps hz₁).1 (hrot_maps hz₂).1 he),
      hopen := hopen_im,
      hgint := by rintro _ ⟨z, hz, rfl⟩; exact hWint (hrot_maps hz).2.1.1,
      hA_eq := hA_eq }
  exact ⟨bc, by simp [bc, g, rot, hKx₀], by rintro _ ⟨z, hz, rfl⟩; exact (hrot_maps hz).2.1.1⟩

/-- Local `BoxChart` around any interior point `p ∈ L \ bd S` of a proper `I`-arc `L` with
`L ∩ bd S = {u, v}` and `IsLineWithEnds L u v`. -/
theorem exists_box_on_iArc (hS : IsSurface S) {L : Set S} {u v p : S}
    (hLb : L ∩ bd S = {u, v}) (hLl : IsLineWithEnds L u v)
    (hpL : p ∈ L) (hpint : p ∈ (bd S)ᶜ) {W : Set S} (hWo : IsOpen W) (hpW : p ∈ W) (hWint : W ⊆ (bd S)ᶜ) :
    ∃ bc : BoxChart S L, bc.g 0 = p ∧ bc.box ⊆ W := by
  obtain ⟨φ, hφ0, hφ1⟩ := hLl
  let γ : ℝ → S := fun r => if hr : r ∈ Icc (0 : ℝ) 1 then (φ ⟨r, hr⟩).1 else u
  have hγc : ContinuousOn γ (Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp φ.continuous).congr fun r => by simp only [Set.domRestrict, γ, Function.comp, dite_eq_left r.2]
  have hγi : InjOn γ (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ he => by
    simp only [γ, dite_eq_left hr₁, dite_eq_left hr₂] at he
    exact congrArg Subtype.val (φ.injective (Subtype.ext he))
  have hγim : γ '' Icc 0 1 = L := by
    ext y; constructor
    · rintro ⟨r, hr, rfl⟩; simp only [γ, dite_eq_left hr]; exact (φ ⟨r, hr⟩).2
    · intro hy; let t := φ.symm ⟨y, hy⟩
      refine ⟨t.1, t.2, ?_⟩; simp only [γ, dite_eq_left t.2]
      exact congrArg Subtype.val (φ.apply_symm_apply _)
  let t₀ := φ.symm ⟨p, hpL⟩
  have ht₀p : γ t₀.1 = p := by
    simp only [γ, dite_eq_left t₀.2]; exact congrArg Subtype.val (φ.apply_symm_apply _)
  have ht₀_ne0 : t₀.1 ≠ 0 := fun h => by
    have hpu : p = u := by rw [← ht₀p]; simp only [γ, h, dite_eq_left (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)]; exact hφ0
    exact hpint (hpu ▸ (hLb ▸ Or.inl rfl : u ∈ L ∩ bd S).2)
  have ht₀_ne1 : t₀.1 ≠ 1 := fun h => by
    have hpv : p = v := by rw [← ht₀p]; simp only [γ, h, dite_eq_left (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)]; exact hφ1
    exact hpint (hpv ▸ (hLb ▸ Or.inr rfl : v ∈ L ∩ bd S).2)
  have ht₀_oo : t₀.1 ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne t₀.2.1 ht₀_ne0.symm, lt_of_le_of_ne t₀.2.2 ht₀_ne1⟩
  exact exists_local_arc_box hS hγc hγi hγim.subset ht₀_oo ht₀p isOpen_univ (mem_univ p)
    (fun _ h => hγim.symm ▸ h.1) hWo hpW hWint

/-- Local `BoxChart` around any point `p ∈ a.O` of an `OArcData` `a`. -/
theorem exists_box_on_oArc (hS : IsSurface S) (a : OArcData S) {p : S} (hp : p ∈ a.O)
    {W : Set S} (hWo : IsOpen W) (hpW : p ∈ W) (hWint : W ⊆ (bd S)ᶜ) :
    ∃ bc : BoxChart S a.O, bc.g 0 = p ∧ bc.box ⊆ W := by
  have : T2Space S := hS.2.1
  obtain ⟨t_raw, ht_raw, htp⟩ := a.hαim ▸ hp
  -- Ensure a loop parameterization `β` with `β t₀ = p` and `t₀ ∈ Ioo 0 1`:
  have hex_param : ∃ (β : ℝ → S) (t₀ : ℝ), ContinuousOn β (Icc 0 1) ∧ InjOn β (Ico 0 1) ∧
      β 0 = β 1 ∧ β '' Icc 0 1 = a.O ∧ t₀ ∈ Ioo (0 : ℝ) 1 ∧ β t₀ = p := by
    by_cases h01 : t_raw = 0 ∨ t_raw = 1
    · obtain ⟨hβc, hβi, hβ01, _, hβim, -⟩ := oArc_rebase a.hαc a.hαi a.hα01 (c := 1 / 2) (by norm_num) (by norm_num)
      refine ⟨conc2 (subArc a.α (1 / 2) 1) (subArc a.α 0 (1 / 2)), 1 / 2, hβc, hβi, hβ01, hβim.trans a.hαim, by norm_num, ?_⟩
      simp only [conc2, le_rfl, ite_true, subArc, lin]
      norm_num; rcases h01 with rfl | rfl
      · exact a.hα01.symm.trans htp
      · exact htp
    · push Not at h01
      exact ⟨a.α, t_raw, a.hαc, a.hαi, a.hα01, a.hαim,
        ⟨lt_of_le_of_ne ht_raw.1 (Ne.symm h01.1), lt_of_le_of_ne ht_raw.2 h01.2⟩, htp⟩
  obtain ⟨β, t₀, hβc, hβi, hβ01, hβim, ht₀, hβt₀⟩ := hex_param
  let d : ℝ := min (t₀ / 2) ((1 - t₀) / 2)
  have hd : 0 < d := lt_min (half_pos ht₀.1) (half_pos (by linarith [ht₀.2]))
  have hsubIco : Icc (t₀ - d) (t₀ + d) ⊆ Ico (0 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1, min_le_left (t₀ / 2) ((1 - t₀) / 2)],
     by linarith [ht.2, min_le_right (t₀ / 2) ((1 - t₀) / 2)]⟩
  let γ := subArc β (t₀ - d) (t₀ + d)
  have hγc : ContinuousOn γ (Icc 0 1) := continuousOn_subArc (by linarith) (hβc.mono (hsubIco.trans Ico_subset_Icc_self))
  have hγi : InjOn γ (Icc 0 1) := injOn_subArc (by linarith) (hβi.mono hsubIco)
  have hγim : γ '' Icc 0 1 = β '' Icc (t₀ - d) (t₀ + d) := subArc_image (by linarith)
  have hγ_half : γ (1 / 2) = p := by simp only [γ, subArc, lin]; ring_nf; exact hβt₀
  let Z : Set S := β '' (Icc 0 (t₀ - d) ∪ Icc (t₀ + d) 1)
  have hZcl : IsClosed Z :=
    ((isCompact_Icc.union isCompact_Icc).image_of_continuousOn
      (hβc.mono (union_subset (Icc_subset_Icc_right (by linarith [(hsubIco ⟨le_rfl, by linarith⟩).2]))
        (Icc_subset_Icc_left (by linarith [(hsubIco ⟨by linarith, le_rfl⟩).1]))))).isClosed
  have hp_notZ : p ∉ Z := by
    rintro ⟨t, ht | ht, hte⟩
    · have h1 := hβi ⟨ht.1, ht.2.trans_lt (by linarith [(hsubIco ⟨le_rfl, by linarith⟩).2])⟩
        (Ioo_subset_Ico_self ht₀) (hte.trans hβt₀.symm)
      linarith [ht.2]
    · rcases ht.2.eq_or_lt with rfl | hlt
      · have h1 := hβi ⟨le_rfl, zero_lt_one⟩ (Ioo_subset_Ico_self ht₀) (hβ01.trans (hte.trans hβt₀.symm))
        linarith [ht₀.1]
      · have h1 := hβi ⟨(show (0 : ℝ) ≤ t₀ + d by linarith [(hsubIco ⟨by linarith, le_rfl⟩).1]).trans ht.1, hlt⟩
          (Ioo_subset_Ico_self ht₀) (hte.trans hβt₀.symm)
        linarith [ht.1]
  refine exists_local_arc_box hS hγc hγi (hγim ▸ (image_mono (hsubIco.trans Ico_subset_Icc_self)).trans hβim.subset)
    (by norm_num) hγ_half hZcl.isOpen_compl hp_notZ ?_ hWo hpW hWint
  rintro y ⟨hyO, hynotZ⟩
  obtain ⟨t, ht, rfl⟩ := hβim ▸ hyO
  rw [hγim]
  refine ⟨t, ?_, rfl⟩
  by_contra hnot
  refine hynotZ ⟨t, ?_, rfl⟩
  rcases lt_or_ge t (t₀ - d) with h1 | h1
  · exact Or.inl ⟨ht.1, h1.le⟩
  · exact Or.inr ⟨le_of_not_ge fun h2 => hnot ⟨h1, h2⟩, ht.2⟩

/-- Uniform piecewise concatenation of `N ≥ 1` curves `seg : Fin N → ℝ → S` on `[0, 1]`. -/
noncomputable def concatSeq {N : ℕ} (hN : 0 < N) (seg : Fin N → ℝ → S) (x : ℝ) : S :=
  let idx := min (N - 1) (max 0 ⌊(N : ℝ) * x⌋).toNat
  seg ⟨idx, by omega⟩ ((N : ℝ) * x - idx)

section ConcatSeq

variable {N : ℕ} (hN : 0 < N) (seg : Fin N → ℝ → S)

omit [TopologicalSpace S] in
theorem concatSeq_on_piece (hmatch : ∀ (i : ℕ) (hi : i + 1 < N), seg ⟨i, by omega⟩ 1 = seg ⟨i + 1, hi⟩ 0)
    (i : Fin N) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    concatSeq hN seg (((i : ℝ) + r) / N) = seg i r := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmul : (N : ℝ) * (((i : ℝ) + r) / N) = (i : ℝ) + r := mul_div_cancel₀ _ hNpos.ne'
  simp only [concatSeq, hmul]
  rcases hr.2.eq_or_lt with rfl | hlt
  · have hfl : ⌊(i : ℝ) + 1⌋ = (i.1 + 1 : ℤ) := by
      have : (i : ℝ) + 1 = ((i.1 + 1 : ℤ) : ℝ) := by push_cast; ring
      rw [this, Int.floor_intCast]
    have htoNat : (max 0 ⌊(i : ℝ) + 1⌋).toNat = i.1 + 1 := by
      rw [hfl, max_eq_right (by omega : (0 : ℤ) ≤ i.1 + 1)]; omega
    simp only [htoNat]
    by_cases hlast : i.1 + 1 < N
    · have hmin : min (N - 1) (i.1 + 1) = i.1 + 1 := Nat.min_eq_right (by omega)
      simp only [hmin]
      have harg : (i : ℝ) + 1 - ((i.1 + 1 : ℕ) : ℝ) = 0 := by push_cast; ring
      rw [harg, ← hmatch i.1 hlast]
    · have hiN : i.1 = N - 1 := by omega
      have hmin : min (N - 1) (i.1 + 1) = i.1 := by omega
      simp only [hmin]
      have harg : (i : ℝ) + 1 - (i : ℝ) = 1 := by ring
      rw [harg]
  · have hfl : ⌊(i : ℝ) + r⌋ = (i.1 : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; exact ⟨by linarith [hr.1], by linarith⟩
    have htoNat : (max 0 ⌊(i : ℝ) + r⌋).toNat = i.1 := by
      rw [hfl, max_eq_right (Int.natCast_nonneg i.1), Int.toNat_natCast]
    have hmin : min (N - 1) i.1 = i.1 := Nat.min_eq_right (by omega)
    simp only [htoNat, hmin, add_sub_cancel_left]

theorem concatSeq_continuousOn (hmatch : ∀ (i : ℕ) (hi : i + 1 < N), seg ⟨i, by omega⟩ 1 = seg ⟨i + 1, hi⟩ 0)
    (hc : ∀ i : Fin N, ContinuousOn (seg i) (Icc 0 1)) :
    ContinuousOn (concatSeq hN seg) (Icc 0 1) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpiece : ∀ i : Fin N, ContinuousOn (concatSeq hN seg) (Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) := fun i => by
    have hmap : MapsTo (fun x : ℝ => (N : ℝ) * x - i) (Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) (Icc 0 1) := fun x hx => by
      have h1 : (i : ℝ) ≤ (N : ℝ) * x := (div_le_iff₀' hNpos).mp hx.1
      have h2 : (N : ℝ) * x ≤ (i : ℝ) + 1 := (le_div_iff₀' hNpos).mp hx.2
      exact ⟨by linarith, by linarith⟩
    refine ((hc i).comp (by fun_prop) hmap).congr fun x hx => ?_
    have hr : (N : ℝ) * x - i ∈ Icc (0 : ℝ) 1 := hmap hx
    have hx_eq : x = ((i : ℝ) + ((N : ℝ) * x - i)) / N := by field_simp [hNpos.ne']; ring
    conv_lhs => rw [hx_eq]
    exact concatSeq_on_piece hN seg hmatch i hr
  have hcov : Icc (0 : ℝ) 1 ⊆ ⋃ i : Fin N, Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N) := fun x hx => by
    let idx := min (N - 1) (max 0 ⌊(N : ℝ) * x⌋).toNat
    refine mem_iUnion.mpr ⟨⟨idx, by omega⟩, ?_⟩
    have h0 : 0 ≤ (N : ℝ) * x := mul_nonneg hNpos.le hx.1
    have hfl0 : (0 : ℤ) ≤ ⌊(N : ℝ) * x⌋ := Int.floor_nonneg.mpr h0
    have h1 : (N : ℝ) * x ≤ N := by nlinarith [hx.2]
    by_cases hlt : ⌊(N : ℝ) * x⌋ < N
    · have hidx : idx = ⌊(N : ℝ) * x⌋.toNat := by dsimp [idx]; rw [max_eq_right hfl0]; omega
      have hidxR : (idx : ℝ) = (⌊(N : ℝ) * x⌋ : ℝ) := by rw [hidx]; exact_mod_cast Int.toNat_of_nonneg hfl0
      exact ⟨(div_le_iff₀' hNpos).mpr (by rw [hidxR]; exact Int.floor_le _),
        (le_div_iff₀' hNpos).mpr (by rw [hidxR]; exact (Int.lt_floor_add_one _).le)⟩
    · have hEq : (N : ℝ) * x = N := le_antisymm h1 (by
        have : (N : ℝ) ≤ (⌊(N : ℝ) * x⌋ : ℝ) := by exact_mod_cast le_of_not_gt hlt
        exact this.trans (Int.floor_le _))
      have hidx : idx = N - 1 := by dsimp [idx]; rw [max_eq_right hfl0]; omega
      have hidxR : (idx : ℝ) + 1 = (N : ℝ) := by rw [hidx]; exact_mod_cast Nat.sub_add_cancel hN
      exact ⟨(div_le_iff₀' hNpos).mpr (by linarith), (le_div_iff₀' hNpos).mpr (by linarith)⟩
  -- Finite union of closed sets:
  have hunion : ContinuousOn (concatSeq hN seg) (⋃ i : Fin N, Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) := by
    have hfin : ∀ (s : Finset (Fin N)), ContinuousOn (concatSeq hN seg) (⋃ i ∈ s, Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) := by
      intro s; induction s using Finset.cons_induction with
      | empty => simp [continuousOn_empty]
      | cons a s ha ih =>
        have hEq : (⋃ i ∈ Finset.cons a s ha, Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) =
            Icc ((a : ℝ) / N) (((a : ℝ) + 1) / N) ∪ (⋃ i ∈ s, Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) := by
          ext y; simp
        rw [hEq]
        have hcl : IsClosed (⋃ i ∈ s, Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) :=
          isClosed_iUnion_of_finite fun _ => isClosed_iUnion_of_finite fun _ => isClosed_Icc
        exact (hpiece a).union_of_isClosed ih isClosed_Icc hcl
    simpa using hfin Finset.univ
  exact hunion.mono hcov

omit [TopologicalSpace S] in
theorem concatSeq_image (hmatch : ∀ (i : ℕ) (hi : i + 1 < N), seg ⟨i, by omega⟩ 1 = seg ⟨i + 1, hi⟩ 0) :
    concatSeq hN seg '' Icc 0 1 = ⋃ i : Fin N, seg i '' Icc 0 1 := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  ext y; constructor
  · rintro ⟨x, hx, rfl⟩
    let idx := min (N - 1) (max 0 ⌊(N : ℝ) * x⌋).toNat
    refine mem_iUnion.mpr ⟨⟨idx, by omega⟩, (N : ℝ) * x - idx, ?_, rfl⟩
    have h0 : 0 ≤ (N : ℝ) * x := mul_nonneg hNpos.le hx.1
    have hfl0 : (0 : ℤ) ≤ ⌊(N : ℝ) * x⌋ := Int.floor_nonneg.mpr h0
    have h1 : (N : ℝ) * x ≤ N := by nlinarith [hx.2]
    by_cases hlt : ⌊(N : ℝ) * x⌋ < N
    · have hidx : idx = ⌊(N : ℝ) * x⌋.toNat := by dsimp [idx]; rw [max_eq_right hfl0]; omega
      have hidxR : (idx : ℝ) = (⌊(N : ℝ) * x⌋ : ℝ) := by rw [hidx]; exact_mod_cast Int.toNat_of_nonneg hfl0
      rw [hidxR]; exact ⟨by linarith [Int.floor_le ((N : ℝ) * x)], by linarith [Int.lt_floor_add_one ((N : ℝ) * x)]⟩
    · have hEq : (N : ℝ) * x = N := le_antisymm h1 (by
        have : (N : ℝ) ≤ (⌊(N : ℝ) * x⌋ : ℝ) := by exact_mod_cast le_of_not_gt hlt
        exact this.trans (Int.floor_le _))
      have hidx : idx = N - 1 := by dsimp [idx]; rw [max_eq_right hfl0]; omega
      have hidxR : (idx : ℝ) + 1 = (N : ℝ) := by rw [hidx]; exact_mod_cast Nat.sub_add_cancel hN
      rw [hEq]; exact ⟨by linarith, by linarith⟩
  · intro hy; obtain ⟨i, r, hr, rfl⟩ := mem_iUnion.mp hy
    refine ⟨((i : ℝ) + r) / N, ?_, concatSeq_on_piece hN seg hmatch i hr⟩
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast i.2
    exact ⟨div_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) i.1, hr.1]) hNpos.le,
      (div_le_one hNpos).mpr (by linarith [hr.2])⟩

omit [TopologicalSpace S] in
theorem concatSeq_injOn (hmatch : ∀ (i : ℕ) (hi : i + 1 < N), seg ⟨i, by omega⟩ 1 = seg ⟨i + 1, hi⟩ 0)
    (hinj : ∀ i : Fin N, InjOn (seg i) (Icc 0 1))
    (hadj : ∀ (i : ℕ) (hi : i + 1 < N),
      ∀ r₁ ∈ Icc (0 : ℝ) 1, ∀ r₂ ∈ Icc (0 : ℝ) 1,
        seg ⟨i, by omega⟩ r₁ = seg ⟨i + 1, hi⟩ r₂ → r₁ = 1 ∧ r₂ = 0)
    (hfar : ∀ i j : Fin N, i.1 + 1 < j.1 → Disjoint (seg i '' Icc 0 1) (seg j '' Icc 0 1)) :
    InjOn (concatSeq hN seg) (Icc 0 1) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hrep : ∀ x ∈ Icc (0 : ℝ) 1, ∃ (i : Fin N) (r : ℝ), r ∈ Icc (0 : ℝ) 1 ∧ x = ((i : ℝ) + r) / N := fun x hx => by
    let idx := min (N - 1) (max 0 ⌊(N : ℝ) * x⌋).toNat
    refine ⟨⟨idx, by omega⟩, (N : ℝ) * x - idx, ?_, by field_simp [hNpos.ne']; ring⟩
    have h0 : 0 ≤ (N : ℝ) * x := mul_nonneg hNpos.le hx.1
    have hfl0 : (0 : ℤ) ≤ ⌊(N : ℝ) * x⌋ := Int.floor_nonneg.mpr h0
    have h1 : (N : ℝ) * x ≤ N := by nlinarith [hx.2]
    by_cases hlt : ⌊(N : ℝ) * x⌋ < N
    · have hidx : idx = ⌊(N : ℝ) * x⌋.toNat := by dsimp [idx]; rw [max_eq_right hfl0]; omega
      have hidxR : (idx : ℝ) = (⌊(N : ℝ) * x⌋ : ℝ) := by rw [hidx]; exact_mod_cast Int.toNat_of_nonneg hfl0
      rw [hidxR]; exact ⟨by linarith [Int.floor_le ((N : ℝ) * x)], by linarith [Int.lt_floor_add_one ((N : ℝ) * x)]⟩
    · have hEq : (N : ℝ) * x = N := le_antisymm h1 (by
        have : (N : ℝ) ≤ (⌊(N : ℝ) * x⌋ : ℝ) := by exact_mod_cast le_of_not_gt hlt
        exact this.trans (Int.floor_le _))
      have hidx : idx = N - 1 := by dsimp [idx]; rw [max_eq_right hfl0]; omega
      have hidxR : (idx : ℝ) + 1 = (N : ℝ) := by rw [hidx]; exact_mod_cast Nat.sub_add_cancel hN
      rw [hEq]; exact ⟨by linarith, by linarith⟩
  intro x₁ hx₁ x₂ hx₂ he
  obtain ⟨i₁, r₁, hr₁, rfl⟩ := hrep x₁ hx₁
  obtain ⟨i₂, r₂, hr₂, rfl⟩ := hrep x₂ hx₂
  rw [concatSeq_on_piece hN seg hmatch i₁ hr₁, concatSeq_on_piece hN seg hmatch i₂ hr₂] at he
  rcases lt_trichotomy i₁.1 i₂.1 with hlt | heq | hgt
  · by_cases hstep : i₁.1 + 1 = i₂.1
    · have hi2 : i₂ = ⟨i₁.1 + 1, by omega⟩ := Fin.ext hstep.symm
      rw [hi2] at he
      obtain ⟨rfl, rfl⟩ := hadj i₁.1 (by omega) r₁ hr₁ r₂ hr₂ he
      congr 1; push_cast [hi2]; ring
    · exact (Set.disjoint_left.mp (hfar i₁ i₂ (by omega)) ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, he.symm⟩).elim
  · have hi : i₁ = i₂ := Fin.ext heq; subst hi
    rw [hinj i₁ hr₁ hr₂ he]
  · by_cases hstep : i₂.1 + 1 = i₁.1
    · have hi1 : i₁ = ⟨i₂.1 + 1, by omega⟩ := Fin.ext hstep.symm
      rw [hi1] at he
      obtain ⟨rfl, rfl⟩ := hadj i₂.1 (by omega) r₂ hr₂ r₁ hr₁ he.symm
      congr 1; push_cast [hi1]; ring
    · exact (Set.disjoint_left.mp (hfar i₂ i₁ (by omega)) ⟨r₂, hr₂, rfl⟩ ⟨r₁, hr₁, he⟩).elim

end ConcatSeq

end LocalBoxes

/-! ### Section 2: Assembling `BandArcData` from boxes and disjoint open bridges -/

section BuildBandArc

/-- Trim an injective path `e : 𝕀 → Ω` from `box₁` to `box₂` to a simple bridge `β : [0, 1] → Ω`
exiting `box₁` at `β 0 = bc₁.g wR` (`wR ∈ frontier bc₁.R`) and entering `box₂` at
`β 1 = bc₂.g wL` (`wL ∈ frontier bc₂.R`), with `β '' (0, 1)` disjoint from `box₁ ∪ box₂`. -/
private theorem trim_bridge [T2Space S] {A₁ A₂ : Set S} (bc₁ : BoxChart S A₁) (bc₂ : BoxChart S A₂)
    (hdisj : Disjoint bc₁.box bc₂.box) {Ω : Set S}
    {e : unitInterval → S} (hec : Continuous e) (hei : Function.Injective e)
    (heΩ : range e ⊆ Ω) (he0 : e 0 ∈ bc₁.box) (he1 : e 1 ∈ bc₂.box)
    (hΩ_disj_A₁ : Disjoint Ω A₁) (hΩ_disj_A₂ : Disjoint Ω A₂) :
    ∃ (β : ℝ → S) (wR wL : ℂ),
      ContinuousOn β (Icc 0 1) ∧ InjOn β (Icc 0 1) ∧
      β '' Icc 0 1 ⊆ Ω ∧
      wR ∈ frontier bc₁.R ∧ wR.re ≠ 0 ∧ β 0 = bc₁.g wR ∧
      wL ∈ frontier bc₂.R ∧ wL.re ≠ 0 ∧ β 1 = bc₂.g wL ∧
      Disjoint (β '' Ioc 0 1) bc₁.box ∧
      Disjoint (β '' Ico 0 1) bc₂.box := by
  let ef : ℝ → S := fun r => if hr : r ∈ Icc (0 : ℝ) 1 then e ⟨r, hr⟩ else e 0
  have hefc : ContinuousOn ef (Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hec.congr fun r => by simp only [Set.domRestrict, ef, dite_eq_left r.2]
  have hefi : InjOn ef (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ he => by
    simp only [ef, dite_eq_left hr₁, dite_eq_left hr₂] at he
    exact congrArg Subtype.val (hei he)
  have hcl_pre : ∀ {B : Set S}, IsClosed B → IsClosed (Icc (0 : ℝ) 1 ∩ ef ⁻¹' B) := fun {B} hBcl => by
    rw [isClosed_iff_forall_filter]; intro x F _ hFT hFx
    have hFT' := Filter.le_principal_iff.mp hFT
    have hxIcc : x ∈ Icc (0 : ℝ) 1 := isClosed_Icc.mem_of_tendsto hFx (Filter.mem_of_superset hFT' fun _ h => h.1)
    have hlim : Filter.Tendsto ef F (𝓝 (ef x)) :=
      (hefc.continuousWithinAt hxIcc).tendsto.mono_left
        (le_inf hFx (Filter.le_principal_iff.mpr (Filter.mem_of_superset hFT' fun _ h => h.1)))
    exact ⟨hxIcc, hBcl.mem_of_tendsto hlim (Filter.mem_of_superset hFT' fun _ h => h.2)⟩
  let T₁ : Set ℝ := Icc (0 : ℝ) 1 ∩ ef ⁻¹' bc₁.box
  have hT₁_cl : IsClosed T₁ := hcl_pre bc₁.isClosed_box
  have h0T₁ : (0 : ℝ) ∈ T₁ := ⟨⟨le_rfl, zero_le_one⟩, by simp only [mem_preimage, ef, dite_eq_left (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)]; exact he0⟩
  have hT₁_bdd : BddAbove T₁ := ⟨1, fun _ h => h.1.2⟩
  let t₁ : ℝ := sSup T₁
  have ht₁_mem : t₁ ∈ T₁ := hT₁_cl.csSup_mem ⟨0, h0T₁⟩ hT₁_bdd
  have ht₁_lt1 : t₁ < 1 := lt_of_le_of_ne ht₁_mem.1.2 fun h =>
    Set.disjoint_left.mp hdisj (h ▸ ht₁_mem.2) (by simp only [ef, dite_eq_left (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)]; exact he1)
  have hout₁ : ∀ r ∈ Ioc t₁ 1, ef r ∉ bc₁.box := fun r hr hmem =>
    not_lt_of_ge (le_csSup hT₁_bdd ⟨⟨ht₁_mem.1.1.trans hr.1.le, hr.2⟩, hmem⟩) hr.1
  let T₂ : Set ℝ := Icc t₁ 1 ∩ ef ⁻¹' bc₂.box
  have hT₂_cl : IsClosed T₂ := by
    have : T₂ = Icc t₁ 1 ∩ (Icc (0 : ℝ) 1 ∩ ef ⁻¹' bc₂.box) := by
      ext r; constructor
      · rintro ⟨hr, hm⟩; exact ⟨hr, ⟨ht₁_mem.1.1.trans hr.1, hr.2⟩, hm⟩
      · rintro ⟨hr, -, hm⟩; exact ⟨hr, hm⟩
    rw [this]; exact isClosed_Icc.inter (hcl_pre bc₂.isClosed_box)
  have h1T₂ : (1 : ℝ) ∈ T₂ := ⟨⟨ht₁_lt1.le, le_rfl⟩, by simp only [mem_preimage, ef, dite_eq_left (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)]; exact he1⟩
  have hT₂_bdd : BddBelow T₂ := ⟨t₁, fun _ h => h.1.1⟩
  let t₂ : ℝ := sInf T₂
  have ht₂_mem : t₂ ∈ T₂ := hT₂_cl.csInf_mem ⟨1, h1T₂⟩ hT₂_bdd
  have ht₁_lt_t₂ : t₁ < t₂ := lt_of_le_of_ne ht₂_mem.1.1 fun h =>
    Set.disjoint_left.mp hdisj ht₁_mem.2 (h ▸ ht₂_mem.2)
  have hout₂ : ∀ r ∈ Ico t₁ t₂, ef r ∉ bc₂.box := fun r hr hmem =>
    not_lt_of_ge (csInf_le hT₂_bdd ⟨⟨hr.1, hr.2.le.trans ht₂_mem.1.2⟩, hmem⟩) hr.2
  -- Extract `wR ∈ frontier bc₁.R` and `wL ∈ frontier bc₂.R`:
  obtain ⟨wR, hwRR, hwReq⟩ := ht₁_mem.2
  obtain ⟨wL, hwLR, hwLeq⟩ := ht₂_mem.2
  have hR_int : ∀ {A : Set S} (bc : BoxChart S A), interior bc.R = Ioo (-bc.a) bc.a ×ℂ Ioo (-bc.b) bc.b := fun bc => by
    rw [BoxChart.R, interior_reProdIm, interior_Icc, interior_Icc]
  have hwR_fr : wR ∈ frontier bc₁.R := by
    refine ⟨subset_closure hwRR, fun hint => ?_⟩
    rw [hR_int bc₁] at hint
    have hmem : ef t₁ ∈ bc₁.openBox := hwReq ▸ ⟨wR, hint, rfl⟩
    have hpre : ef ⁻¹' bc₁.openBox ∈ 𝓝[Icc (0 : ℝ) 1] t₁ := hefc.continuousWithinAt ht₁_mem.1 (bc₁.hopen.mem_nhds hmem)
    rw [Metric.mem_nhdsWithin_iff] at hpre
    obtain ⟨δ, hδ, hδsub⟩ := hpre
    let r' := min 1 (t₁ + δ / 2)
    have hr' : r' ∈ Ioc t₁ 1 := ⟨lt_min ht₁_lt1 (by linarith), min_le_left _ _⟩
    have hr'01 : r' ∈ Icc (0 : ℝ) 1 := ⟨ht₁_mem.1.1.trans hr'.1.le, hr'.2⟩
    have hr'ball : r' ∈ ball t₁ δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hr'.1], by linarith [min_le_right 1 (t₁ + δ / 2)]⟩
    exact hout₁ r' hr' (bc₁.openBox_subset_box (hδsub ⟨hr'ball, hr'01⟩))
  have hwL_fr : wL ∈ frontier bc₂.R := by
    refine ⟨subset_closure hwLR, fun hint => ?_⟩
    rw [hR_int bc₂] at hint
    have hmem : ef t₂ ∈ bc₂.openBox := hwLeq ▸ ⟨wL, hint, rfl⟩
    have hpre : ef ⁻¹' bc₂.openBox ∈ 𝓝[Icc (0 : ℝ) 1] t₂ := hefc.continuousWithinAt ⟨ht₁_mem.1.1.trans ht₂_mem.1.1, ht₂_mem.1.2⟩ (bc₂.hopen.mem_nhds hmem)
    rw [Metric.mem_nhdsWithin_iff] at hpre
    obtain ⟨δ, hδ, hδsub⟩ := hpre
    let r' := max t₁ (t₂ - δ / 2)
    have hr' : r' ∈ Ico t₁ t₂ := ⟨le_max_left _ _, max_lt ht₁_lt_t₂ (by linarith)⟩
    have hr'01 : r' ∈ Icc (0 : ℝ) 1 := ⟨ht₁_mem.1.1.trans hr'.1, hr'.2.le.trans ht₂_mem.1.2⟩
    have hr'ball : r' ∈ ball t₂ δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [le_max_right t₁ (t₂ - δ / 2)], by linarith [hr'.2]⟩
    exact hout₂ r' hr' (bc₂.openBox_subset_box (hδsub ⟨hr'ball, hr'01⟩))
  have hwR_re : wR.re ≠ 0 := fun h0 => by
    have hA : bc₁.g wR ∈ A₁ := (show bc₁.g wR ∈ A₁ ∩ bc₁.box by
      rw [BoxChart.box, bc₁.hA_eq]; exact ⟨wR, Complex.mem_reProdIm.mpr ⟨h0, (Complex.mem_reProdIm.mp hwRR).2⟩, rfl⟩).1
    have hΩ : bc₁.g wR ∈ Ω := by
      rw [hwReq]; simp only [ef, dite_eq_left ht₁_mem.1]; exact heΩ ⟨_, rfl⟩
    exact Set.disjoint_left.mp hΩ_disj_A₁ hΩ hA
  have hwL_re : wL.re ≠ 0 := fun h0 => by
    have hA : bc₂.g wL ∈ A₂ := (show bc₂.g wL ∈ A₂ ∩ bc₂.box by
      rw [BoxChart.box, bc₂.hA_eq]; exact ⟨wL, Complex.mem_reProdIm.mpr ⟨h0, (Complex.mem_reProdIm.mp hwLR).2⟩, rfl⟩).1
    have hΩ : bc₂.g wL ∈ Ω := by
      rw [hwLeq]; simp only [ef, dite_eq_left (show t₂ ∈ Icc (0 : ℝ) 1 from ⟨ht₁_mem.1.1.trans ht₂_mem.1.1, ht₂_mem.1.2⟩)]; exact heΩ ⟨_, rfl⟩
    exact Set.disjoint_left.mp hΩ_disj_A₂ hΩ hA
  let β := subArc ef t₁ t₂
  have hsub01 : Icc t₁ t₂ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ht₁_mem.1.1 ht₂_mem.1.2
  refine ⟨β, wR, wL, continuousOn_subArc ht₁_lt_t₂.le (hefc.mono hsub01),
    injOn_subArc ht₁_lt_t₂ (hefi.mono hsub01), ?_, hwR_fr, hwR_re, (subArc_zero ef t₁ t₂).trans hwReq.symm,
    hwL_fr, hwL_re, (subArc_one ef t₁ t₂).trans hwLeq.symm, ?_, ?_⟩
  · rintro _ ⟨r, hr, rfl⟩
    have hr' := hsub01 (lin_mapsTo_Icc ht₁_lt_t₂.le hr)
    simp only [β, subArc, ef, dite_eq_left hr']; exact heΩ ⟨_, rfl⟩
  · rw [Set.disjoint_left]; rintro _ ⟨r, hr, rfl⟩ hbox
    have hlin : lin t₁ t₂ r ∈ Ioc t₁ 1 := ⟨by dsimp [lin]; nlinarith [hr.1, ht₁_lt_t₂],
      (lin_mapsTo_Icc ht₁_lt_t₂.le (Ioc_subset_Icc_self hr)).2.trans ht₂_mem.1.2⟩
    exact hout₁ _ hlin hbox
  · rw [Set.disjoint_left]; rintro _ ⟨r, hr, rfl⟩ hbox
    have hlin : lin t₁ t₂ r ∈ Ico t₁ t₂ := ⟨(lin_mapsTo_Icc ht₁_lt_t₂.le (Ico_subset_Icc_self hr)).1,
      by dsimp [lin]; nlinarith [hr.2, ht₁_lt_t₂]⟩
    exact hout₂ _ hlin hbox

/-- Step 1 of `build_bandArcData`: construct oriented boundary boxes and trimmed bridges `β j ⊆ Ω j`. -/
private theorem build_bandArcData_bridges (hS : IsSurface S) {s t : S} (M : ProperManifold S s t)
    {m : ℕ} {Q : Fin m → Set S} {k : ℕ}
    (idxs : Fin k → Fin m)
    (bcL : BoxChart S M.U) (bcR : BoxChart S M.U)
    (bcM : ∀ r : Fin k, BoxChart S (Q (idxs r)))
    (hL_disj_R : Disjoint bcL.box bcR.box)
    (hL_disj_M : ∀ r : Fin k, Disjoint bcL.box (bcM r).box)
    (hR_disj_M : ∀ r : Fin k, Disjoint bcR.box (bcM r).box)
    (hM_disj : ∀ r₁ r₂ : Fin k, r₁ ≠ r₂ → Disjoint (bcM r₁).box (bcM r₂).box)
    (Ω : Fin (k + 1) → Set S)
    (hΩ_open : ∀ j, IsOpen (Ω j))
    (hΩ_conn : ∀ j, IsConnected (Ω j))
    (hΩ_free : ∀ j, Ω j ⊆ (bd S)ᶜ \ (M.U ∪ ⋃ q : Fin m, Q q))
    (hΩ_disj : Pairwise fun j₁ j₂ => Disjoint (Ω j₁) (Ω j₂))
    (hL_Ω : (bcL.box ∩ Ω 0).Nonempty)
    (hR_Ω : (bcR.box ∩ Ω (Fin.last k)).Nonempty)
    (hM_left_Ω : ∀ r : Fin k, (bcM r).clLeftHalf ⊆ Ω r.castSucc)
    (hM_right_Ω : ∀ r : Fin k, (bcM r).clRightHalf ⊆ Ω r.succ) :
    ∃ (bcL' bcR' : BoxChart S M.U) (wR_L wL_R : ℂ) (wL_M wR_M : Fin k → ℂ)
      (β : Fin (k + 1) → ℝ → S),
      bcL'.g 0 = bcL.g 0 ∧ bcL'.box = bcL.box ∧
      bcR'.g 0 = bcR.g 0 ∧ bcR'.box = bcR.box ∧
      wR_L ∈ frontier bcL'.R ∧ 0 < wR_L.re ∧
      wL_R ∈ frontier bcR'.R ∧ wL_R.re < 0 ∧
      (∀ r : Fin k, wL_M r ∈ frontier (bcM r).R ∧ (wL_M r).re < 0) ∧
      (∀ r : Fin k, wR_M r ∈ frontier (bcM r).R ∧ 0 < (wR_M r).re) ∧
      (∀ j : Fin (k + 1), ContinuousOn (β j) (Icc 0 1) ∧ InjOn (β j) (Icc 0 1) ∧ β j '' Icc 0 1 ⊆ Ω j) ∧
      (β 0 0 = bcL'.g wR_L) ∧
      (β (Fin.last k) 1 = bcR'.g wL_R) ∧
      (∀ r : Fin k, β r.castSucc 1 = (bcM r).g (wL_M r) ∧ β r.succ 0 = (bcM r).g (wR_M r)) ∧
      (Disjoint (β 0 '' Ioc 0 1) bcL'.box) ∧
      (Disjoint (β (Fin.last k) '' Ico 0 1) bcR'.box) ∧
      (∀ r : Fin k, Disjoint (β r.castSucc '' Ico 0 1) (bcM r).box ∧ Disjoint (β r.succ '' Ioc 0 1) (bcM r).box) := by
  classical
  have : T2Space S := hS.2.1
  have hΩ_disj_M : ∀ j, Disjoint (Ω j) M.U := fun j =>
    Set.disjoint_left.mpr fun x hx hM => (hΩ_free j hx).2 (Or.inl hM)
  have hΩ_disj_Q : ∀ j q, Disjoint (Ω j) (Q q) := fun j q =>
    Set.disjoint_left.mpr fun x hx hQ => (hΩ_free j hx).2 (Or.inr (mem_iUnion.mpr ⟨q, hQ⟩))
  have hpath_in : ∀ (j : Fin (k + 1)) {x y : S}, x ∈ Ω j → y ∈ Ω j → x ≠ y →
      ∃ e : unitInterval → S, Continuous e ∧ Function.Injective e ∧ e 0 = x ∧ e 1 = y ∧ range e ⊆ Ω j := fun j x y hx hy hne => by
    have hpc := isPathConnected_of_open_connected_compl_bd hS (hΩ_open j)
      ((hΩ_free j).trans sdiff_subset) (hΩ_conn j)
    obtain ⟨γ, hγΩ⟩ := hpc.joinedIn x hx y hy
    obtain ⟨e, hec, hei, he0, he1, her⟩ := exists_arc_of_path γ.continuous (by simpa using hne)
    exact ⟨e, hec, hei, he0.trans γ.source, he1.trans γ.target, her.trans (range_subset_iff.mpr hγΩ)⟩
  have hbridges : ∃ (bcL' bcR' : BoxChart S M.U) (wR_L wL_R : ℂ) (wL_M wR_M : Fin k → ℂ)
      (β : Fin (k + 1) → ℝ → S),
      bcL'.g 0 = bcL.g 0 ∧ bcL'.box = bcL.box ∧
      bcR'.g 0 = bcR.g 0 ∧ bcR'.box = bcR.box ∧
      wR_L ∈ frontier bcL'.R ∧ 0 < wR_L.re ∧
      wL_R ∈ frontier bcR'.R ∧ wL_R.re < 0 ∧
      (∀ r : Fin k, wL_M r ∈ frontier (bcM r).R ∧ (wL_M r).re < 0) ∧
      (∀ r : Fin k, wR_M r ∈ frontier (bcM r).R ∧ 0 < (wR_M r).re) ∧
      (∀ j : Fin (k + 1), ContinuousOn (β j) (Icc 0 1) ∧ InjOn (β j) (Icc 0 1) ∧ β j '' Icc 0 1 ⊆ Ω j) ∧
      (β 0 0 = bcL'.g wR_L) ∧
      (β (Fin.last k) 1 = bcR'.g wL_R) ∧
      (∀ r : Fin k, β r.castSucc 1 = (bcM r).g (wL_M r) ∧ β r.succ 0 = (bcM r).g (wR_M r)) ∧
      (Disjoint (β 0 '' Ioc 0 1) bcL'.box) ∧
      (Disjoint (β (Fin.last k) '' Ico 0 1) bcR'.box) ∧
      (∀ r : Fin k, Disjoint (β r.castSucc '' Ico 0 1) (bcM r).box ∧ Disjoint (β r.succ '' Ioc 0 1) (bcM r).box) := by
    -- Helper: if `w ∈ frontier bc.R` and `w.re ≠ 0`, flip `bc` if needed to get `0 < w'.re` (or `w'.re < 0`).
    have hflip_pos : ∀ (bc : BoxChart S M.U) (w : ℂ), w ∈ frontier bc.R → w.re ≠ 0 →
        ∃ (bc' : BoxChart S M.U) (w' : ℂ),
          bc'.g 0 = bc.g 0 ∧ bc'.box = bc.box ∧ w' ∈ frontier bc'.R ∧ 0 < w'.re ∧ bc'.g w' = bc.g w := fun bc w hfr hne => by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine ⟨bc.flip, -w, by simp [BoxChart.flip], bc.flip_box, ?_, by simp; linarith, by simp [BoxChart.flip]⟩
        have hR : bc.flip.R = bc.R := rfl
        rw [hR]
        have hneg_map : Homeomorph.neg ℂ '' bc.R = bc.R := by
          ext z; constructor
          · rintro ⟨u, hu, rfl⟩; rw [BoxChart.R, Complex.mem_reProdIm] at hu ⊢
            simp; exact ⟨⟨by linarith [hu.1.2], by linarith [hu.1.1]⟩, ⟨by linarith [hu.2.2], by linarith [hu.2.1]⟩⟩
          · intro hz; refine ⟨-z, ?_, by simp⟩; rw [BoxChart.R, Complex.mem_reProdIm] at hz ⊢
            simp; exact ⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩, ⟨by linarith [hz.2.2], by linarith [hz.2.1]⟩⟩
        have h1 : Homeomorph.neg ℂ w ∈ frontier (Homeomorph.neg ℂ '' bc.R) :=
          (Homeomorph.neg ℂ).image_frontier bc.R ▸ ⟨w, hfr, rfl⟩
        rwa [hneg_map] at h1
      · exact ⟨bc, w, rfl, rfl, hfr, hgt, rfl⟩
    have hflip_neg : ∀ (bc : BoxChart S M.U) (w : ℂ), w ∈ frontier bc.R → w.re ≠ 0 →
        ∃ (bc' : BoxChart S M.U) (w' : ℂ),
          bc'.g 0 = bc.g 0 ∧ bc'.box = bc.box ∧ w' ∈ frontier bc'.R ∧ w'.re < 0 ∧ bc'.g w' = bc.g w := fun bc w hfr hne => by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨bc, w, rfl, rfl, hfr, hlt, rfl⟩
      · refine ⟨bc.flip, -w, by simp [BoxChart.flip], bc.flip_box, ?_, by simp; linarith, by simp [BoxChart.flip]⟩
        have hR : bc.flip.R = bc.R := rfl
        rw [hR]
        have hneg_map : Homeomorph.neg ℂ '' bc.R = bc.R := by
          ext z; constructor
          · rintro ⟨u, hu, rfl⟩; rw [BoxChart.R, Complex.mem_reProdIm] at hu ⊢
            simp; exact ⟨⟨by linarith [hu.1.2], by linarith [hu.1.1]⟩, ⟨by linarith [hu.2.2], by linarith [hu.2.1]⟩⟩
          · intro hz; refine ⟨-z, ?_, by simp⟩; rw [BoxChart.R, Complex.mem_reProdIm] at hz ⊢
            simp; exact ⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩, ⟨by linarith [hz.2.2], by linarith [hz.2.1]⟩⟩
        have h1 : Homeomorph.neg ℂ w ∈ frontier (Homeomorph.neg ℂ '' bc.R) :=
          (Homeomorph.neg ℂ).image_frontier bc.R ▸ ⟨w, hfr, rfl⟩
        rwa [hneg_map] at h1
    -- Helper: for `r : Fin k`, any `w ∈ frontier (bcM r).R` with `w.re ≠ 0` and `(bcM r).g w ∈ Ω r.castSucc` has `w.re < 0`!
    have hM_sign_L : ∀ (r : Fin k) (w : ℂ), w ∈ frontier (bcM r).R → w.re ≠ 0 → (bcM r).g w ∈ Ω r.castSucc → w.re < 0 := by
      intro r w hfr hne hΩ
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hlt
      · have hwR := (isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hfr
        have hmem : (bcM r).g w ∈ (bcM r).clRightHalf :=
          ⟨w, Complex.mem_reProdIm.mpr ⟨⟨hgt, (Complex.mem_reProdIm.mp hwR).1.2⟩, (Complex.mem_reProdIm.mp hwR).2⟩, rfl⟩
        exact (Set.disjoint_left.mp (hΩ_disj (Fin.castSucc_lt_succ (i := r)).ne) hΩ (hM_right_Ω r hmem)).elim
    have hM_sign_R : ∀ (r : Fin k) (w : ℂ), w ∈ frontier (bcM r).R → w.re ≠ 0 → (bcM r).g w ∈ Ω r.succ → 0 < w.re := by
      intro r w hfr hne hΩ
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hwR := (isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hfr
        have hmem : (bcM r).g w ∈ (bcM r).clLeftHalf :=
          ⟨w, Complex.mem_reProdIm.mpr ⟨⟨(Complex.mem_reProdIm.mp hwR).1.1, hlt⟩, (Complex.mem_reProdIm.mp hwR).2⟩, rfl⟩
        exact (Set.disjoint_left.mp (hΩ_disj (Fin.castSucc_lt_succ (i := r)).ne) (hM_left_Ω r hmem) hΩ).elim
      · exact hgt
    cases k with
    | zero =>
      obtain ⟨x₀, hx₀L, hx₀Ω⟩ := hL_Ω
      obtain ⟨y₀, hy₀R, hy₀Ω⟩ := hR_Ω
      have hne : x₀ ≠ y₀ := fun h => Set.disjoint_left.mp hL_disj_R hx₀L (h ▸ hy₀R)
      obtain ⟨e, hec, hei, he0, he1, her⟩ := hpath_in 0 hx₀Ω hy₀Ω hne
      obtain ⟨β₀, wR, wL, hβc, hβi, hβΩ, hwRfr, hwRne, hβ0, hwLfr, hwLne, hβ1, hd1, hd2⟩ :=
        trim_bridge bcL bcR hL_disj_R hec hei her (he0.symm ▸ hx₀L) (he1.symm ▸ hy₀R) (hΩ_disj_M 0) (hΩ_disj_M 0)
      obtain ⟨bcL', wR', hL0, hLb, hwR'fr, hwR'pos, hLg⟩ := hflip_pos bcL wR hwRfr hwRne
      obtain ⟨bcR', wL', hR0, hRb, hwL'fr, hwL'neg, hRg⟩ := hflip_neg bcR wL hwLfr hwLne
      refine ⟨bcL', bcR', wR', wL', Fin.elim0, Fin.elim0, fun _ => β₀,
        hL0, hLb, hR0, hRb, hwR'fr, hwR'pos, hwL'fr, hwL'neg,
        fun r => Fin.elim0 r, fun r => Fin.elim0 r,
        fun j => by rw [Fin.eq_zero j]; exact ⟨hβc, hβi, hβΩ⟩,
        hβ0.trans hLg.symm, hβ1.trans hRg.symm, fun r => Fin.elim0 r,
        hLb ▸ hd1, hRb ▸ hd2, fun r => Fin.elim0 r⟩
    | succ k' =>
      -- Bridge 0: `bcL` to `bcM 0` in `Ω 0`:
      let r0 : Fin (k' + 1) := ⟨0, by omega⟩
      let rlast : Fin (k' + 1) := ⟨k', by omega⟩
      obtain ⟨xL, hxL_box, hxL_Ω⟩ := hL_Ω
      obtain ⟨y0, hy0_half⟩ := (bcM r0).leftHalf_nonempty
      have hy0_box : y0 ∈ (bcM r0).box := (bcM r0).clLeftHalf_subset_box ((bcM r0).leftHalf_subset_clLeft hy0_half)
      have hy0_Ω : y0 ∈ Ω 0 := hM_left_Ω r0 ((bcM r0).leftHalf_subset_clLeft hy0_half)
      obtain ⟨e0, he0c, he0i, he00, he01, he0r⟩ := hpath_in 0 hxL_Ω hy0_Ω
        (fun h => Set.disjoint_left.mp (hL_disj_M r0) hxL_box (h ▸ hy0_box))
      obtain ⟨β0, wRL0, wLM0, hβ0c, hβ0i, hβ0Ω, hwRLfr, hwRLne, hβ00, hwLM0fr, hwLM0ne, hβ01, hdL, hdM0⟩ :=
        trim_bridge bcL (bcM r0) (hL_disj_M r0) he0c he0i he0r (he00.symm ▸ hxL_box) (he01.symm ▸ hy0_box)
          (hΩ_disj_M 0) (hΩ_disj_Q 0 (idxs r0))
      obtain ⟨bcL', wR_L, hL0, hLb, hwR_L_fr, hwR_L_pos, hLg⟩ := hflip_pos bcL wRL0 hwRLfr hwRLne
      have hwLM0_neg : wLM0.re < 0 := hM_sign_L r0 wLM0 hwLM0fr hwLM0ne (hβ01 ▸ hβ0Ω ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩)
      -- Bridge `last`: `bcM rlast` to `bcR` in `Ω (Fin.last (k' + 1))`:
      obtain ⟨xlast, hxlast_half⟩ := (bcM rlast).rightHalf_nonempty
      have hxlast_box : xlast ∈ (bcM rlast).box := (bcM rlast).clRightHalf_subset_box ((bcM rlast).rightHalf_subset_clRight hxlast_half)
      have hxlast_Ω : xlast ∈ Ω (Fin.last (k' + 1)) := by
        have h := hM_right_Ω rlast ((bcM rlast).rightHalf_subset_clRight hxlast_half)
        have heq : rlast.succ = Fin.last (k' + 1) := Fin.ext rfl
        rwa [heq] at h
      obtain ⟨yR, hyR_box, hyR_Ω⟩ := hR_Ω
      obtain ⟨elast, helc, heli, hel0, hel1, helr⟩ := hpath_in (Fin.last (k' + 1)) hxlast_Ω hyR_Ω
        (fun h => Set.disjoint_left.mp (hR_disj_M rlast) hyR_box (h ▸ hxlast_box))
      obtain ⟨βlast, wRMlast, wLR0, hβlc, hβli, hβlΩ, hwRMlfr, hwRMlne, hβl0, hwLRfr, hwLRne, hβl1, hdMl, hdR⟩ :=
        trim_bridge (bcM rlast) bcR (hR_disj_M rlast).symm helc heli helr (hel0.symm ▸ hxlast_box) (hel1.symm ▸ hyR_box)
          (hΩ_disj_Q (Fin.last (k' + 1)) (idxs rlast)) (hΩ_disj_M (Fin.last (k' + 1)))
      obtain ⟨bcR', wL_R, hR0, hRb, hwL_R_fr, hwL_R_neg, hRg⟩ := hflip_neg bcR wLR0 hwLRfr hwLRne
      have hwRMl_pos : 0 < wRMlast.re := hM_sign_R rlast wRMlast hwRMlfr hwRMlne (by
        have h : (bcM rlast).g wRMlast ∈ Ω (Fin.last (k' + 1)) := hβl0 ▸ hβlΩ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
        have heq : rlast.succ = Fin.last (k' + 1) := Fin.ext rfl
        rwa [heq])
      -- Intermediate bridges `q : Fin k'`: from `bcM q.castSucc` to `bcM q.succ` in `Ω ⟨q.1 + 1, _⟩`:
      have hmid_ex : ∀ q : Fin k', ∃ (βq : ℝ → S) (wR wL : ℂ),
          ContinuousOn βq (Icc 0 1) ∧ InjOn βq (Icc 0 1) ∧ βq '' Icc 0 1 ⊆ Ω q.castSucc.succ ∧
          wR ∈ frontier (bcM q.castSucc).R ∧ 0 < wR.re ∧ βq 0 = (bcM q.castSucc).g wR ∧
          wL ∈ frontier (bcM q.succ).R ∧ wL.re < 0 ∧ βq 1 = (bcM q.succ).g wL ∧
          Disjoint (βq '' Ioc 0 1) (bcM q.castSucc).box ∧ Disjoint (βq '' Ico 0 1) (bcM q.succ).box := fun q => by
        obtain ⟨xq, hxq_half⟩ := (bcM q.castSucc).rightHalf_nonempty
        obtain ⟨yq, hyq_half⟩ := (bcM q.succ).leftHalf_nonempty
        have hxq_box := (bcM q.castSucc).clRightHalf_subset_box ((bcM q.castSucc).rightHalf_subset_clRight hxq_half)
        have hyq_box := (bcM q.succ).clLeftHalf_subset_box ((bcM q.succ).leftHalf_subset_clLeft hyq_half)
        have hxq_Ω : xq ∈ Ω q.castSucc.succ := hM_right_Ω q.castSucc ((bcM q.castSucc).rightHalf_subset_clRight hxq_half)
        have hyq_Ω : yq ∈ Ω q.castSucc.succ := by
          have h := hM_left_Ω q.succ ((bcM q.succ).leftHalf_subset_clLeft hyq_half)
          have heq : q.succ.castSucc = q.castSucc.succ := Fin.ext rfl
          rwa [heq] at h
        have hdj := hM_disj q.castSucc q.succ (Fin.castSucc_lt_succ (i := q)).ne
        obtain ⟨eq, heqc, heqi, heq0, heq1, heqr⟩ := hpath_in q.castSucc.succ hxq_Ω hyq_Ω
          (fun h => Set.disjoint_left.mp hdj hxq_box (h ▸ hyq_box))
        obtain ⟨βq, wR, wL, hc, hi, hΩq, hwRfr, hwRne, h0, hwLfr, hwLne, h1, hd1, hd2⟩ :=
          trim_bridge (bcM q.castSucc) (bcM q.succ) hdj heqc heqi heqr (heq0.symm ▸ hxq_box) (heq1.symm ▸ hyq_box)
            (hΩ_disj_Q q.castSucc.succ (idxs q.castSucc)) (hΩ_disj_Q q.castSucc.succ (idxs q.succ))
        have hwRpos : 0 < wR.re := hM_sign_R q.castSucc wR hwRfr hwRne (h0 ▸ hΩq ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
        have hwLneg : wL.re < 0 := hM_sign_L q.succ wL hwLfr hwLne (by
          have heq : q.succ.castSucc = q.castSucc.succ := Fin.ext rfl
          rw [heq]; exact h1 ▸ hΩq ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩)
        exact ⟨βq, wR, wL, hc, hi, hΩq, hwRfr, hwRpos, h0, hwLfr, hwLneg, h1, hd1, hd2⟩
      choose βmid wRmid wLmid hβmc hβmi hβmΩ hwRmfr hwRmpos hβm0 hwLmfr hwLmneg hβm1 hdm1 hdm2 using hmid_ex
      -- Assemble `β : Fin (k' + 2) → ℝ → S`, `wL_M`, `wR_M`:
      let β : Fin (k' + 2) → ℝ → S := fun j =>
        if h0 : j.1 = 0 then β0
        else if hk : j.1 = k' + 1 then βlast
        else βmid ⟨j.1 - 1, by omega⟩
      let wL_M : Fin (k' + 1) → ℂ := fun r =>
        if h0 : r.1 = 0 then wLM0 else wLmid ⟨r.1 - 1, by omega⟩
      let wR_M : Fin (k' + 1) → ℂ := fun r =>
        if hk : r.1 = k' then wRMlast else wRmid ⟨r.1, by omega⟩
      have hβ_0 : β 0 = β0 := by simp [β]
      have hβ_last : β (Fin.last (k' + 1)) = βlast := by simp [β]
      have hβ_mid : ∀ q : Fin k', β q.castSucc.succ = βmid q := fun q => by
        simp [β, q.2.ne]
      refine ⟨bcL', bcR', wR_L, wL_R, wL_M, wR_M, β, hL0, hLb, hR0, hRb,
        hwR_L_fr, hwR_L_pos, hwL_R_fr, hwL_R_neg, ?_, ?_, ?_,
        by rw [hβ_0]; exact hβ00.trans hLg.symm,
        by rw [hβ_last]; exact hβl1.trans hRg.symm, ?_,
        by rw [hβ_0, hLb]; exact hdL,
        by rw [hβ_last, hRb]; exact hdR, ?_⟩
      · intro r; dsimp only [wL_M]; split_ifs with h0
        · have hr : r = r0 := Fin.ext h0; subst hr; exact ⟨hwLM0fr, hwLM0_neg⟩
        · generalize hq : (⟨r.1 - 1, by omega⟩ : Fin k') = q
          have hr : r = q.succ := Fin.ext (by simp [← hq]; omega)
          rw [hr]; exact ⟨hwLmfr q, hwLmneg q⟩
      · intro r; dsimp only [wR_M]; split_ifs with hk
        · have hr : r = rlast := Fin.ext hk; subst hr; exact ⟨hwRMlfr, hwRMl_pos⟩
        · generalize hq : (⟨r.1, by omega⟩ : Fin k') = q
          have hr : r = q.castSucc := Fin.ext (by simp [← hq])
          rw [hr]; exact ⟨hwRmfr q, hwRmpos q⟩
      · intro j; dsimp only [β]; split_ifs with h0 hk
        · have hj : j = 0 := Fin.ext h0; subst hj; exact ⟨hβ0c, hβ0i, hβ0Ω⟩
        · have hj : j = Fin.last (k' + 1) := Fin.ext hk; subst hj; exact ⟨hβlc, hβli, hβlΩ⟩
        · generalize hq : (⟨j.1 - 1, by omega⟩ : Fin k') = q
          have hj : j = q.castSucc.succ := Fin.ext (by simp [← hq]; omega)
          rw [hj]; exact ⟨hβmc q, hβmi q, hβmΩ q⟩
      · intro r; constructor
        · dsimp only [wL_M]; split_ifs with h0
          · have hr : r = r0 := Fin.ext h0; subst hr
            have hcs : r0.castSucc = 0 := Fin.ext rfl
            rw [hcs, hβ_0]; exact hβ01
          · generalize hq : (⟨r.1 - 1, by omega⟩ : Fin k') = q
            have hr : r = q.succ := Fin.ext (by simp [← hq]; omega)
            have hcs : r.castSucc = q.castSucc.succ := Fin.ext (by simp [hr])
            rw [hcs, hβ_mid q, hr]; exact hβm1 q
        · dsimp only [wR_M]; split_ifs with hk
          · have hr : r = rlast := Fin.ext hk; subst hr
            have hs : rlast.succ = Fin.last (k' + 1) := Fin.ext rfl
            rw [hs, hβ_last]; exact hβl0
          · generalize hq : (⟨r.1, by omega⟩ : Fin k') = q
            have hr : r = q.castSucc := Fin.ext (by simp [← hq])
            have hs : r.succ = q.castSucc.succ := Fin.ext (by simp [hr])
            rw [hs, hβ_mid q, hr]; exact hβm0 q
      · intro r; constructor
        · by_cases h0 : r.1 = 0
          · have hr : r = r0 := Fin.ext h0; subst hr
            have hcs : r0.castSucc = 0 := Fin.ext rfl
            rw [hcs, hβ_0]; exact hdM0
          · generalize hq : (⟨r.1 - 1, by omega⟩ : Fin k') = q
            have hr : r = q.succ := Fin.ext (by simp [← hq]; omega)
            have hcs : r.castSucc = q.castSucc.succ := Fin.ext (by simp [hr])
            rw [hcs, hβ_mid q, hr]; exact hdm2 q
        · by_cases hk : r.1 = k'
          · have hr : r = rlast := Fin.ext hk; subst hr
            have hs : rlast.succ = Fin.last (k' + 1) := Fin.ext rfl
            rw [hs, hβ_last]; exact hdMl
          · generalize hq : (⟨r.1, by omega⟩ : Fin k') = q
            have hr : r = q.castSucc := Fin.ext (by simp [← hq])
            have hs : r.succ = q.castSucc.succ := Fin.ext (by simp [hr])
            rw [hs, hβ_mid q, hr]; exact hdm1 q
  exact hbridges

/-- Step 2 of `build_bandArcData`: build the `3k+5` segments and prove concatenation continuity,
injectivity, image, and container classification. -/
private theorem build_bandArcData_concat {s t : S} (M : ProperManifold S s t)
    {m : ℕ} {Q : Fin m → Set S} {k : ℕ}
    (idxs : Fin k → Fin m)
    (bcL' bcR' : BoxChart S M.U)
    (bcM : ∀ r : Fin k, BoxChart S (Q (idxs r)))
    (hL_disj_R : Disjoint bcL'.box bcR'.box)
    (hL_disj_M : ∀ r : Fin k, Disjoint bcL'.box (bcM r).box)
    (hR_disj_M : ∀ r : Fin k, Disjoint bcR'.box (bcM r).box)
    (hM_disj : ∀ r₁ r₂ : Fin k, r₁ ≠ r₂ → Disjoint (bcM r₁).box (bcM r₂).box)
    (Ω : Fin (k + 1) → Set S)
    (hΩ_free : ∀ j, Ω j ⊆ (bd S)ᶜ \ (M.U ∪ ⋃ q : Fin m, Q q))
    (hΩ_disj : Pairwise fun j₁ j₂ => Disjoint (Ω j₁) (Ω j₂))
    (hL_disj_Ω : ∀ j : Fin (k + 1), j.1 ≠ 0 → Disjoint bcL'.box (Ω j))
    (hR_disj_Ω : ∀ j : Fin (k + 1), j.1 ≠ k → Disjoint bcR'.box (Ω j))
    (hM_disj_Ω : ∀ (r : Fin k) (j : Fin (k + 1)), j.1 ≠ r.1 → j.1 ≠ r.1 + 1 → Disjoint (bcM r).box (Ω j))
    (wR_L wL_R : ℂ) (wL_M wR_M : Fin k → ℂ) (β : Fin (k + 1) → ℝ → S)
    (hwR_L_fr : wR_L ∈ frontier bcL'.R) (hwR_L_pos : 0 < wR_L.re)
    (hwL_R_fr : wL_R ∈ frontier bcR'.R) (hwL_R_neg : wL_R.re < 0)
    (hwLM : ∀ r : Fin k, wL_M r ∈ frontier (bcM r).R ∧ (wL_M r).re < 0)
    (hwRM : ∀ r : Fin k, wR_M r ∈ frontier (bcM r).R ∧ 0 < (wR_M r).re)
    (hβ_prop : ∀ j : Fin (k + 1), ContinuousOn (β j) (Icc 0 1) ∧ InjOn (β j) (Icc 0 1) ∧ β j '' Icc 0 1 ⊆ Ω j)
    (hβ00 : β 0 0 = bcL'.g wR_L)
    (hβl1 : β (Fin.last k) 1 = bcR'.g wL_R)
    (hβM : ∀ r : Fin k, β r.castSucc 1 = (bcM r).g (wL_M r) ∧ β r.succ 0 = (bcM r).g (wR_M r))
    (hdL : Disjoint (β 0 '' Ioc 0 1) bcL'.box)
    (hdR : Disjoint (β (Fin.last k) '' Ico 0 1) bcR'.box)
    (hdM : ∀ r : Fin k, Disjoint (β r.castSucc '' Ico 0 1) (bcM r).box ∧ Disjoint (β r.succ '' Ioc 0 1) (bcM r).box) :
    let N : ℕ := 3 * k + 5
    have hN : 0 < N := by omega
    ∃ seg : Fin N → ℝ → S,
      (seg ⟨0, hN⟩ = fun r : ℝ => bcL'.g (((1 - r : ℝ) : ℂ) * (-bcL'.a : ℂ))) ∧
      (seg ⟨1, by omega⟩ = fun r : ℝ => bcL'.g ((r : ℂ) * wR_L)) ∧
      (seg ⟨2, by omega⟩ = β 0) ∧
      (seg ⟨3 * k + 3, by omega⟩ = fun r : ℝ => bcR'.g (((1 - r : ℝ) : ℂ) * wL_R)) ∧
      (seg ⟨3 * k + 4, by omega⟩ = fun r : ℝ => bcR'.g ((r : ℂ) * (bcR'.a : ℂ))) ∧
      (∀ r : Fin k, seg ⟨3 * (r.1 + 1), by omega⟩ = fun x : ℝ => (bcM r).g (((1 - x : ℝ) : ℂ) * wL_M r)) ∧
      (∀ r : Fin k, seg ⟨3 * (r.1 + 1) + 1, by omega⟩ = fun x : ℝ => (bcM r).g ((x : ℂ) * wR_M r)) ∧
      (∀ r : Fin k, seg ⟨3 * (r.1 + 1) + 2, by omega⟩ = β r.succ) ∧
      (∀ (i : ℕ) (hi : i + 1 < N), seg ⟨i, by omega⟩ 1 = seg ⟨i + 1, hi⟩ 0) ∧
      (∀ i : Fin N,
        (i.1 / 3 = 0 ∧ i.1 % 3 < 2 ∧ seg i '' Icc 0 1 ⊆ bcL'.box) ∨
        (i.1 / 3 = k + 1 ∧ i.1 % 3 < 2 ∧ seg i '' Icc 0 1 ⊆ bcR'.box) ∨
        (∃ r : Fin k, i.1 / 3 = r.1 + 1 ∧ i.1 % 3 < 2 ∧ seg i '' Icc 0 1 ⊆ (bcM r).box) ∨
        (∃ j : Fin (k + 1), i.1 = 3 * j.1 + 2 ∧ seg i = β j ∧ seg i '' Icc 0 1 ⊆ Ω j)) ∧
      ContinuousOn (concatSeq hN seg) (Icc 0 1) ∧
      InjOn (concatSeq hN seg) (Icc 0 1) ∧
      concatSeq hN seg '' Icc 0 1 = ⋃ i : Fin N, seg i '' Icc 0 1 ∧
      concatSeq hN seg '' Icc 0 1 ⊆ (bd S)ᶜ := by
  classical
  have hLb : bcL'.box = bcL'.box := rfl
  have hRb : bcR'.box = bcR'.box := rfl
  -- Step 2: Build the `N = 3 * k + 5` segments and concatenate them via `concatSeq`!
  let N : ℕ := 3 * k + 5
  have hN_def : N = 3 * k + 5 := rfl
  have hN : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let wL_L : ℂ := (-bcL'.a : ℂ)
  let wR_R : ℂ := (bcR'.a : ℂ)
  have hwLL_fr : wL_L ∈ frontier bcL'.R := by
    refine ⟨subset_closure (Complex.mem_reProdIm.mpr ⟨by simp [wL_L, bcL'.ha.le], by simp [wL_L, bcL'.hb.le]⟩), fun h => ?_⟩
    rw [BoxChart.R, interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at h
    simp [wL_L] at h
  have hwRR_fr : wR_R ∈ frontier bcR'.R := by
    refine ⟨subset_closure (Complex.mem_reProdIm.mpr ⟨by simp [wR_R, bcR'.ha.le], by simp [wR_R, bcR'.hb.le]⟩), fun h => ?_⟩
    rw [BoxChart.R, interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at h
    simp [wR_R] at h
  -- Segment `i : Fin N`:
  --   `i = 3 * l`: left chord of box `l` (`0 ≤ l ≤ k + 1`)
  --   `i = 3 * l + 1`: right chord of box `l` (`0 ≤ l ≤ k + 1`)
  --   `i = 3 * l + 2`: bridge `β l` (`0 ≤ l ≤ k`)
  let seg : Fin N → ℝ → S := fun i r =>
    let q := i.1 / 3
    let rem := i.1 % 3
    if hq0 : q = 0 then
      if rem = 0 then bcL'.g (((1 - r : ℝ) : ℂ) * wL_L)
      else if rem = 1 then bcL'.g ((r : ℂ) * wR_L)
      else β 0 r
    else if hqk : q = k + 1 then
      if rem = 0 then bcR'.g (((1 - r : ℝ) : ℂ) * wL_R)
      else bcR'.g ((r : ℂ) * wR_R)
    else
      if rem = 0 then (bcM ⟨q - 1, by omega⟩).g (((1 - r : ℝ) : ℂ) * wL_M ⟨q - 1, by omega⟩)
      else if rem = 1 then (bcM ⟨q - 1, by omega⟩).g ((r : ℂ) * wR_M ⟨q - 1, by omega⟩)
      else β ⟨q, by omega⟩ r
  -- Helper properties of linear radial segments inside any `BoxChart`:
  have hseg_L_mem : ∀ {A' : Set S} (bc : BoxChart S A') {w : ℂ}, w ∈ frontier bc.R →
      ∀ r ∈ Icc (0 : ℝ) 1, ((1 - r : ℝ) : ℂ) * w ∈ bc.R := by
    intro A' bc w hfr r hr
    have hwR := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hfr)
    rw [BoxChart.R, Complex.mem_reProdIm]
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
    exact ⟨⟨by nlinarith [hwR.1.1, hr.1, hr.2, bc.ha], by nlinarith [hwR.1.2, hr.1, hr.2, bc.ha]⟩,
      ⟨by nlinarith [hwR.2.1, hr.1, hr.2, bc.hb], by nlinarith [hwR.2.2, hr.1, hr.2, bc.hb]⟩⟩
  have hseg_R_mem : ∀ {A' : Set S} (bc : BoxChart S A') {w : ℂ}, w ∈ frontier bc.R →
      ∀ r ∈ Icc (0 : ℝ) 1, (r : ℂ) * w ∈ bc.R := by
    intro A' bc w hfr r hr
    have hwR := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hfr)
    rw [BoxChart.R, Complex.mem_reProdIm]
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
    exact ⟨⟨by nlinarith [hwR.1.1, hr.1, hr.2, bc.ha], by nlinarith [hwR.1.2, hr.1, hr.2, bc.ha]⟩,
      ⟨by nlinarith [hwR.2.1, hr.1, hr.2, bc.hb], by nlinarith [hwR.2.2, hr.1, hr.2, bc.hb]⟩⟩
  have hseg_L_inj : ∀ {A' : Set S} (bc : BoxChart S A') {w : ℂ}, w ∈ frontier bc.R → w.re < 0 →
      InjOn (fun r : ℝ => bc.g (((1 - r : ℝ) : ℂ) * w)) (Icc 0 1) := by
    intro A' bc w hfr hw r₁ hr₁ r₂ hr₂ he
    have h1 := congrArg Complex.re (bc.hgi (hseg_L_mem bc hfr r₁ hr₁) (hseg_L_mem bc hfr r₂ hr₂) he)
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at h1
    nlinarith
  have hseg_R_inj : ∀ {A' : Set S} (bc : BoxChart S A') {w : ℂ}, w ∈ frontier bc.R → 0 < w.re →
      InjOn (fun r : ℝ => bc.g ((r : ℂ) * w)) (Icc 0 1) := by
    intro A' bc w hfr hw r₁ hr₁ r₂ hr₂ he
    have h1 := congrArg Complex.re (bc.hgi (hseg_R_mem bc hfr r₁ hr₁) (hseg_R_mem bc hfr r₂ hr₂) he)
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at h1
    nlinarith
  -- Evaluate `seg` on each specific index cleanly:
  have hseg_0 : seg ⟨0, by omega⟩ = fun (r : ℝ) => bcL'.g (((1 - r : ℝ) : ℂ) * wL_L) := by
    funext r; dsimp only [seg]; norm_num
  have hseg_1 : seg ⟨1, by omega⟩ = fun (r : ℝ) => bcL'.g ((r : ℂ) * wR_L) := by
    funext r; dsimp only [seg]; norm_num
  have hseg_2 : seg ⟨2, by omega⟩ = β 0 := by
    funext r; dsimp only [seg]; norm_num
  have hseg_RL : seg ⟨3 * k + 3, by omega⟩ = fun (r : ℝ) => bcR'.g (((1 - r : ℝ) : ℂ) * wL_R) := by
    funext r; have hq : (3 * k + 3) / 3 = k + 1 := by omega
    have hrm : (3 * k + 3) % 3 = 0 := by omega
    simp [seg, hq, hrm]
  have hseg_RR : seg ⟨3 * k + 4, by omega⟩ = fun (r : ℝ) => bcR'.g ((r : ℂ) * wR_R) := by
    funext r; have hq : (3 * k + 4) / 3 = k + 1 := by omega
    have hrm : (3 * k + 4) % 3 = 1 := by omega
    simp [seg, hq, hrm]
  have hseg_ML : ∀ r : Fin k, seg ⟨3 * (r.1 + 1), by omega⟩ =
      fun (x : ℝ) => (bcM r).g (((1 - x : ℝ) : ℂ) * wL_M r) := fun r => by
    funext x
    have hq : 3 * (r.1 + 1) / 3 = r.1 + 1 := by omega
    have hrm : 3 * (r.1 + 1) % 3 = 0 := by omega
    have hne : r.1 + 1 ≠ k + 1 := by omega
    have hfin : (⟨3 * (r.1 + 1) / 3 - 1, by omega⟩ : Fin k) = r := Fin.ext (by dsimp; omega)
    dsimp only [seg]
    simp only [hq, hrm, Nat.succ_ne_zero, hne, ↓reduceDIte, ↓reduceIte]
    rw [hfin, show (⟨r.1 + 1 - 1, by omega⟩ : Fin k) = r from Fin.ext (by simp)]
  have hseg_MR : ∀ r : Fin k, seg ⟨3 * (r.1 + 1) + 1, by omega⟩ =
      fun (x : ℝ) => (bcM r).g ((x : ℂ) * wR_M r) := fun r => by
    funext x
    have hq : (3 * (r.1 + 1) + 1) / 3 = r.1 + 1 := by omega
    have hrm : (3 * (r.1 + 1) + 1) % 3 = 1 := by omega
    have hne : r.1 + 1 ≠ k + 1 := by omega
    have hfin : (⟨(3 * (r.1 + 1) + 1) / 3 - 1, by omega⟩ : Fin k) = r := Fin.ext (by dsimp; omega)
    dsimp only [seg]
    simp only [hq, hrm, Nat.succ_ne_zero, hne, one_ne_zero, ↓reduceDIte, ↓reduceIte]
    rw [hfin, show (⟨r.1 + 1 - 1, by omega⟩ : Fin k) = r from Fin.ext (by simp)]
  have hseg_Mβ : ∀ r : Fin k, seg ⟨3 * (r.1 + 1) + 2, by omega⟩ = β r.succ := fun r => by
    funext x
    have hq : (3 * (r.1 + 1) + 2) / 3 = r.1 + 1 := by omega
    have hrm : (3 * (r.1 + 1) + 2) % 3 = 2 := by omega
    have hne : r.1 + 1 ≠ k + 1 := by omega
    dsimp only [seg]
    simp only [hq, hrm, Nat.succ_ne_zero, hne, ↓reduceDIte, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte]
    rfl
  -- Verify `hmatch`, `hseg_c`, `hseg_inj`, `hadj`, `hfar`!
  have hmatch : ∀ (i : ℕ) (hi : i + 1 < N), seg ⟨i, by omega⟩ 1 = seg ⟨i + 1, hi⟩ 0 := by
    intro i hi
    have hq : i / 3 ≤ k + 1 := by omega
    rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h0 | h1 | h2
    · by_cases hq0 : i / 3 = 0
      · have hi0 : i = 0 := by omega
        subst hi0; rw [hseg_0, hseg_1]; simp
      · by_cases hqk : i / 3 = k + 1
        · have hiL : i = 3 * k + 3 := by omega
          subst hiL; rw [hseg_RL, hseg_RR]; simp
        · let r : Fin k := ⟨i / 3 - 1, by omega⟩
          have hir : i = 3 * (r.1 + 1) := by dsimp [r]; omega
          have hi1 : (⟨i, by omega⟩ : Fin N) = ⟨3 * (r.1 + 1), by omega⟩ := Fin.ext hir
          have hi2 : (⟨i + 1, hi⟩ : Fin N) = ⟨3 * (r.1 + 1) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hi1, hi2, hseg_ML r, hseg_MR r]; simp
    · by_cases hq0 : i / 3 = 0
      · have hi1 : i = 1 := by omega
        subst hi1; rw [hseg_1, hseg_2, hβ00]; simp
      · have hqk : i / 3 ≠ k + 1 := by omega
        let r : Fin k := ⟨i / 3 - 1, by omega⟩
        have hir : i = 3 * (r.1 + 1) + 1 := by dsimp [r]; omega
        have hi1 : (⟨i, by omega⟩ : Fin N) = ⟨3 * (r.1 + 1) + 1, by omega⟩ := Fin.ext hir
        have hi2 : (⟨i + 1, hi⟩ : Fin N) = ⟨3 * (r.1 + 1) + 2, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hi1, hi2, hseg_MR r, hseg_Mβ r, (hβM r).2]; simp
    · have hqk : i / 3 ≤ k := by omega
      by_cases hq0 : i / 3 = 0
      · have hi2 : i = 2 := by omega
        subst hi2; rw [hseg_2]
        by_cases hk0 : k = 0
        · subst hk0
          have h3 : (⟨2 + 1, hi⟩ : Fin N) = ⟨3 * 0 + 3, by omega⟩ := Fin.ext rfl
          have h0 : (0 : Fin 1) = Fin.last 0 := rfl
          rw [h3, hseg_RL, h0, hβl1]; simp
        · let r0 : Fin k := ⟨0, by omega⟩
          have h3 : (⟨2 + 1, hi⟩ : Fin N) = ⟨3 * (r0.1 + 1), by omega⟩ := Fin.ext (by simp [r0])
          have h0 : (0 : Fin (k + 1)) = r0.castSucc := Fin.ext rfl
          rw [h3, hseg_ML r0, h0, (hβM r0).1]; simp
      · let r : Fin k := ⟨i / 3 - 1, by omega⟩
        have hir : i = 3 * (r.1 + 1) + 2 := by dsimp [r]; omega
        have hi1 : (⟨i, by omega⟩ : Fin N) = ⟨3 * (r.1 + 1) + 2, by omega⟩ := Fin.ext hir
        rw [hi1, hseg_Mβ r]
        by_cases hlast : r.1 + 1 = k
        · have hi2 : (⟨i + 1, hi⟩ : Fin N) = ⟨3 * k + 3, by omega⟩ := Fin.ext (by dsimp; omega)
          have hrs : r.succ = Fin.last k := Fin.ext hlast
          rw [hi2, hseg_RL, hrs]; simp [hβl1]
        · let r' : Fin k := ⟨r.1 + 1, by omega⟩
          have hi2 : (⟨i + 1, hi⟩ : Fin N) = ⟨3 * (r'.1 + 1), by omega⟩ := Fin.ext (by dsimp [r']; omega)
          have hrs : r.succ = r'.castSucc := Fin.ext rfl
          rw [hi2, hseg_ML r', hrs]; simp [(hβM r').1]
  -- Helper: which container (`bcL'.box`, `bcR'.box`, `(bcM r).box`, `Ω j`) holds `seg i '' Icc 0 1`!
  have hseg_c : ∀ i : Fin N, ContinuousOn (seg i) (Icc 0 1) := fun i => by
    rcases (show i.1 % 3 = 0 ∨ i.1 % 3 = 1 ∨ i.1 % 3 = 2 by omega) with h0 | h1 | h2
    · by_cases hq0 : i.1 / 3 = 0
      · have : i = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega); rw [this, hseg_0]
        exact bcL'.hgc.comp (by fun_prop) (hseg_L_mem bcL' hwLL_fr)
      · by_cases hqk : i.1 / 3 = k + 1
        · have : i = ⟨3 * k + 3, by omega⟩ := Fin.ext (by dsimp; omega); rw [this, hseg_RL]
          exact bcR'.hgc.comp (by fun_prop) (hseg_L_mem bcR' hwL_R_fr)
        · let r : Fin k := ⟨i.1 / 3 - 1, by omega⟩
          have : i = ⟨3 * (r.1 + 1), by omega⟩ := Fin.ext (by dsimp [r]; omega); rw [this, hseg_ML r]
          exact (bcM r).hgc.comp (by fun_prop) (hseg_L_mem (bcM r) (hwLM r).1)
    · by_cases hq0 : i.1 / 3 = 0
      · have : i = ⟨1, by omega⟩ := Fin.ext (show i.1 = 1 by omega); rw [this, hseg_1]
        exact bcL'.hgc.comp (by fun_prop) (hseg_R_mem bcL' hwR_L_fr)
      · by_cases hqk : i.1 / 3 = k + 1
        · have : i = ⟨3 * k + 4, by omega⟩ := Fin.ext (by dsimp; omega); rw [this, hseg_RR]
          exact bcR'.hgc.comp (by fun_prop) (hseg_R_mem bcR' hwRR_fr)
        · let r : Fin k := ⟨i.1 / 3 - 1, by omega⟩
          have : i = ⟨3 * (r.1 + 1) + 1, by omega⟩ := Fin.ext (by dsimp [r]; omega); rw [this, hseg_MR r]
          exact (bcM r).hgc.comp (by fun_prop) (hseg_R_mem (bcM r) (hwRM r).1)
    · by_cases hq0 : i.1 / 3 = 0
      · have : i = ⟨2, by omega⟩ := Fin.ext (by dsimp; omega); rw [this, hseg_2]; exact (hβ_prop 0).1
      · let r : Fin k := ⟨i.1 / 3 - 1, by omega⟩
        have : i = ⟨3 * (r.1 + 1) + 2, by omega⟩ := Fin.ext (by dsimp [r]; omega); rw [this, hseg_Mβ r]
        exact (hβ_prop r.succ).1
  have hseg_i : ∀ i : Fin N, InjOn (seg i) (Icc 0 1) := fun i => by
    rcases (show i.1 % 3 = 0 ∨ i.1 % 3 = 1 ∨ i.1 % 3 = 2 by omega) with h0 | h1 | h2
    · by_cases hq0 : i.1 / 3 = 0
      · have : i = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega); rw [this, hseg_0]
        exact hseg_L_inj bcL' hwLL_fr (by simp [wL_L, bcL'.ha])
      · by_cases hqk : i.1 / 3 = k + 1
        · have : i = ⟨3 * k + 3, by omega⟩ := Fin.ext (by dsimp; omega); rw [this, hseg_RL]
          exact hseg_L_inj bcR' hwL_R_fr hwL_R_neg
        · let r : Fin k := ⟨i.1 / 3 - 1, by omega⟩
          have : i = ⟨3 * (r.1 + 1), by omega⟩ := Fin.ext (by dsimp [r]; omega); rw [this, hseg_ML r]
          exact hseg_L_inj (bcM r) (hwLM r).1 (hwLM r).2
    · by_cases hq0 : i.1 / 3 = 0
      · have : i = ⟨1, by omega⟩ := Fin.ext (show i.1 = 1 by omega); rw [this, hseg_1]
        exact hseg_R_inj bcL' hwR_L_fr hwR_L_pos
      · by_cases hqk : i.1 / 3 = k + 1
        · have : i = ⟨3 * k + 4, by omega⟩ := Fin.ext (by dsimp; omega); rw [this, hseg_RR]
          exact hseg_R_inj bcR' hwRR_fr (by simp [wR_R, bcR'.ha])
        · let r : Fin k := ⟨i.1 / 3 - 1, by omega⟩
          have : i = ⟨3 * (r.1 + 1) + 1, by omega⟩ := Fin.ext (by dsimp [r]; omega); rw [this, hseg_MR r]
          exact hseg_R_inj (bcM r) (hwRM r).1 (hwRM r).2
    · by_cases hq0 : i.1 / 3 = 0
      · have : i = ⟨2, by omega⟩ := Fin.ext (by dsimp; omega); rw [this, hseg_2]; exact (hβ_prop 0).2.1
      · let r : Fin k := ⟨i.1 / 3 - 1, by omega⟩
        have : i = ⟨3 * (r.1 + 1) + 2, by omega⟩ := Fin.ext (by dsimp [r]; omega); rw [this, hseg_Mβ r]
        exact (hβ_prop r.succ).2.1
  -- Adjacent-segment intersection lemma (`hadj`):
  have hLR_meet : ∀ {A' : Set S} (bc : BoxChart S A') {wL wR : ℂ},
      wL ∈ frontier bc.R → wL.re < 0 → wR ∈ frontier bc.R → 0 < wR.re →
      ∀ r₁ ∈ Icc (0 : ℝ) 1, ∀ r₂ ∈ Icc (0 : ℝ) 1,
        bc.g (((1 - r₁ : ℝ) : ℂ) * wL) = bc.g ((r₂ : ℂ) * wR) → r₁ = 1 ∧ r₂ = 0 := by
    intro A' bc wL wR hLfr hLre hRfr hRre r₁ hr₁ r₂ hr₂ he
    have h1 := congrArg Complex.re (bc.hgi (hseg_L_mem bc hLfr r₁ hr₁) (hseg_R_mem bc hRfr r₂ hr₂) he)
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at h1
    exact ⟨by nlinarith [hr₁.1, hr₁.2, hr₂.1, hr₂.2], by nlinarith [hr₁.1, hr₁.2, hr₂.1, hr₂.2]⟩
  have hadj : ∀ (i : ℕ) (hi : i + 1 < N),
      ∀ r₁ ∈ Icc (0 : ℝ) 1, ∀ r₂ ∈ Icc (0 : ℝ) 1,
        seg ⟨i, by omega⟩ r₁ = seg ⟨i + 1, hi⟩ r₂ → r₁ = 1 ∧ r₂ = 0 := by
    intro i hi r₁ hr₁ r₂ hr₂ he
    rcases (show i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 by omega) with h0 | h1 | h2
    · by_cases hq0 : i / 3 = 0
      · have hi0 : i = 0 := by omega
        subst hi0; rw [hseg_0, hseg_1] at he
        exact hLR_meet bcL' hwLL_fr (by simp [wL_L, bcL'.ha]) hwR_L_fr hwR_L_pos r₁ hr₁ r₂ hr₂ he
      · by_cases hqk : i / 3 = k + 1
        · have hiL : i = 3 * k + 3 := by omega
          subst hiL; rw [hseg_RL, hseg_RR] at he
          exact hLR_meet bcR' hwL_R_fr hwL_R_neg hwRR_fr (by simp [wR_R, bcR'.ha]) r₁ hr₁ r₂ hr₂ he
        · let r : Fin k := ⟨i / 3 - 1, by omega⟩
          have h1' : (⟨i, by omega⟩ : Fin N) = ⟨3 * (r.1 + 1), by omega⟩ := Fin.ext (by dsimp [r]; omega)
          have h2' : (⟨i + 1, hi⟩ : Fin N) = ⟨3 * (r.1 + 1) + 1, by omega⟩ := Fin.ext (by dsimp [r]; omega)
          rw [h1', h2', hseg_ML r, hseg_MR r] at he
          exact hLR_meet (bcM r) (hwLM r).1 (hwLM r).2 (hwRM r).1 (hwRM r).2 r₁ hr₁ r₂ hr₂ he
    · -- Right chord to bridge: `r₂ = 0` by `Disjoint (β '' Ioc 0 1) box`, then `r₁ = 1` by injectivity!
      by_cases hq0 : i / 3 = 0
      · have hi1 : i = 1 := by omega
        subst hi1; rw [hseg_1, hseg_2] at he
        have hr2_0 : r₂ = 0 := by
          by_contra hne
          exact Set.disjoint_left.mp hdL ⟨r₂, ⟨lt_of_le_of_ne hr₂.1 (Ne.symm hne), hr₂.2⟩, rfl⟩
            (he ▸ ⟨_, hseg_R_mem bcL' hwR_L_fr r₁ hr₁, rfl⟩)
        subst hr2_0; rw [hβ00] at he
        have h1' := hseg_R_inj bcL' hwR_L_fr hwR_L_pos hr₁ ⟨zero_le_one, le_rfl⟩ (he.trans (by simp))
        exact ⟨h1', rfl⟩
      · let r : Fin k := ⟨i / 3 - 1, by omega⟩
        have h1' : (⟨i, by omega⟩ : Fin N) = ⟨3 * (r.1 + 1) + 1, by omega⟩ := Fin.ext (by dsimp [r]; omega)
        have h2' : (⟨i + 1, hi⟩ : Fin N) = ⟨3 * (r.1 + 1) + 2, by omega⟩ := Fin.ext (by dsimp [r]; omega)
        rw [h1', h2', hseg_MR r, hseg_Mβ r] at he
        have hr2_0 : r₂ = 0 := by
          by_contra hne
          exact Set.disjoint_left.mp (hdM r).2 ⟨r₂, ⟨lt_of_le_of_ne hr₂.1 (Ne.symm hne), hr₂.2⟩, rfl⟩
            (he ▸ ⟨_, hseg_R_mem (bcM r) (hwRM r).1 r₁ hr₁, rfl⟩)
        subst hr2_0; rw [(hβM r).2] at he
        have h1'' := hseg_R_inj (bcM r) (hwRM r).1 (hwRM r).2 hr₁ ⟨zero_le_one, le_rfl⟩ (he.trans (by simp))
        exact ⟨h1'', rfl⟩
    · -- Bridge to left chord: `r₁ = 1` by `Disjoint (β '' Ico 0 1) box`, then `r₂ = 0` by injectivity!
      by_cases hq0 : i / 3 = 0
      · have hi2 : i = 2 := by omega
        subst hi2; rw [hseg_2] at he
        by_cases hk0 : k = 0
        · subst hk0
          have h3 : (⟨2 + 1, hi⟩ : Fin N) = ⟨3 * 0 + 3, by omega⟩ := Fin.ext rfl
          rw [h3, hseg_RL] at he
          have hr1_1 : r₁ = 1 := by
            by_contra hne
            exact Set.disjoint_left.mp hdR ⟨r₁, ⟨hr₁.1, lt_of_le_of_ne hr₁.2 hne⟩, rfl⟩
              (he.symm ▸ ⟨_, hseg_L_mem bcR' hwL_R_fr r₂ hr₂, rfl⟩)
          subst hr1_1; rw [show (0 : Fin 1) = Fin.last 0 from rfl, hβl1] at he
          have h2' := hseg_L_inj bcR' hwL_R_fr hwL_R_neg hr₂ ⟨le_rfl, zero_le_one⟩ (he.symm.trans (by simp))
          exact ⟨rfl, h2'⟩
        · let r0 : Fin k := ⟨0, by omega⟩
          have h3 : (⟨2 + 1, hi⟩ : Fin N) = ⟨3 * (r0.1 + 1), by omega⟩ := Fin.ext (by simp [r0])
          rw [h3, hseg_ML r0] at he
          have hr1_1 : r₁ = 1 := by
            by_contra hne
            exact Set.disjoint_left.mp (hdM r0).1 ⟨r₁, ⟨hr₁.1, lt_of_le_of_ne hr₁.2 hne⟩, rfl⟩
              (he.symm ▸ ⟨_, hseg_L_mem (bcM r0) (hwLM r0).1 r₂ hr₂, rfl⟩)
          subst hr1_1; rw [show (0 : Fin (k + 1)) = r0.castSucc from Fin.ext rfl, (hβM r0).1] at he
          have h2' := hseg_L_inj (bcM r0) (hwLM r0).1 (hwLM r0).2 hr₂ ⟨le_rfl, zero_le_one⟩ (he.symm.trans (by simp))
          exact ⟨rfl, h2'⟩
      · let r : Fin k := ⟨i / 3 - 1, by omega⟩
        have h1' : (⟨i, by omega⟩ : Fin N) = ⟨3 * (r.1 + 1) + 2, by omega⟩ := Fin.ext (by dsimp [r]; omega)
        rw [h1', hseg_Mβ r] at he
        by_cases hlast : r.1 + 1 = k
        · have hi2 : (⟨i + 1, hi⟩ : Fin N) = ⟨3 * k + 3, by omega⟩ := Fin.ext (by dsimp [r] at hlast ⊢; omega)
          have hrs : r.succ = Fin.last k := Fin.ext hlast
          rw [hi2, hseg_RL, hrs] at he
          have hr1_1 : r₁ = 1 := by
            by_contra hne
            exact Set.disjoint_left.mp hdR ⟨r₁, ⟨hr₁.1, lt_of_le_of_ne hr₁.2 hne⟩, rfl⟩
              (he.symm ▸ ⟨_, hseg_L_mem bcR' hwL_R_fr r₂ hr₂, rfl⟩)
          subst hr1_1; rw [hβl1] at he
          have h2' := hseg_L_inj bcR' hwL_R_fr hwL_R_neg hr₂ ⟨le_rfl, zero_le_one⟩ (he.symm.trans (by simp))
          exact ⟨rfl, h2'⟩
        · let r' : Fin k := ⟨r.1 + 1, by omega⟩
          have hi2 : (⟨i + 1, hi⟩ : Fin N) = ⟨3 * (r'.1 + 1), by omega⟩ := Fin.ext (by dsimp [r, r'] at hlast ⊢; omega)
          have hrs : r.succ = r'.castSucc := Fin.ext rfl
          rw [hi2, hseg_ML r', hrs] at he
          have hr1_1 : r₁ = 1 := by
            by_contra hne
            exact Set.disjoint_left.mp (hdM r').1 ⟨r₁, ⟨hr₁.1, lt_of_le_of_ne hr₁.2 hne⟩, rfl⟩
              (he.symm ▸ ⟨_, hseg_L_mem (bcM r') (hwLM r').1 r₂ hr₂, rfl⟩)
          subst hr1_1; rw [(hβM r').1] at he
          have h2' := hseg_L_inj (bcM r') (hwLM r').1 (hwLM r').2 hr₂ ⟨le_rfl, zero_le_one⟩ (he.symm.trans (by simp))
          exact ⟨rfl, h2'⟩
  -- Non-adjacent segment disjointness (`hfar`) and box containment:
  have hseg_in_boxL : seg ⟨0, by omega⟩ '' Icc 0 1 ⊆ bcL'.box ∧ seg ⟨1, by omega⟩ '' Icc 0 1 ⊆ bcL'.box :=
    ⟨by rw [hseg_0]; rintro _ ⟨r, hr, rfl⟩; exact ⟨_, hseg_L_mem bcL' hwLL_fr r hr, rfl⟩,
     by rw [hseg_1]; rintro _ ⟨r, hr, rfl⟩; exact ⟨_, hseg_R_mem bcL' hwR_L_fr r hr, rfl⟩⟩
  have hseg_in_boxR : seg ⟨3 * k + 3, by omega⟩ '' Icc 0 1 ⊆ bcR'.box ∧ seg ⟨3 * k + 4, by omega⟩ '' Icc 0 1 ⊆ bcR'.box :=
    ⟨by rw [hseg_RL]; rintro _ ⟨r, hr, rfl⟩; exact ⟨_, hseg_L_mem bcR' hwL_R_fr r hr, rfl⟩,
     by rw [hseg_RR]; rintro _ ⟨r, hr, rfl⟩; exact ⟨_, hseg_R_mem bcR' hwRR_fr r hr, rfl⟩⟩
  have hseg_in_boxM : ∀ r : Fin k,
      seg ⟨3 * (r.1 + 1), by omega⟩ '' Icc 0 1 ⊆ (bcM r).box ∧
      seg ⟨3 * (r.1 + 1) + 1, by omega⟩ '' Icc 0 1 ⊆ (bcM r).box := fun r =>
    ⟨by rw [hseg_ML r]; rintro _ ⟨x, hx, rfl⟩; exact ⟨_, hseg_L_mem (bcM r) (hwLM r).1 x hx, rfl⟩,
     by rw [hseg_MR r]; rintro _ ⟨x, hx, rfl⟩; exact ⟨_, hseg_R_mem (bcM r) (hwRM r).1 x hx, rfl⟩⟩
  -- For `seg 0` (left chord of `bcL'`) and `β 0`: `seg 0 '' [0, 1]` has `re ≤ 0` while `β 0` is disjoint from `bcL'.box` except at `wR_L` (`re > 0`)!
  have hL0_disj_β0 : Disjoint (seg ⟨0, by omega⟩ '' Icc 0 1) (β 0 '' Icc 0 1) := by
    rw [Set.disjoint_left, hseg_0]; rintro _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, he⟩
    by_cases h0 : r₂ = 0
    · subst h0; rw [hβ00] at he
      have h1 := congrArg Complex.re (bcL'.hgi (hseg_L_mem bcL' hwLL_fr r₁ hr₁)
        ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hwR_L_fr) he.symm)
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, wL_L, neg_re] at h1
      nlinarith [hr₁.1, hr₁.2, bcL'.ha, hwR_L_pos]
    · exact Set.disjoint_left.mp hdL ⟨r₂, ⟨lt_of_le_of_ne hr₂.1 (Ne.symm h0), hr₂.2⟩, rfl⟩
        (he ▸ ⟨_, hseg_L_mem bcL' hwLL_fr r₁ hr₁, rfl⟩)
  have hR1_disj_βlast : Disjoint (β (Fin.last k) '' Icc 0 1) (seg ⟨3 * k + 4, by omega⟩ '' Icc 0 1) := by
    rw [Set.disjoint_left, hseg_RR]; rintro _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, he⟩
    by_cases h1 : r₁ = 1
    · subst h1; rw [hβl1] at he
      have h2 := congrArg Complex.re (bcR'.hgi ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hwL_R_fr)
        (hseg_R_mem bcR' hwRR_fr r₂ hr₂) he.symm)
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, wR_R] at h2
      nlinarith [hr₂.1, hr₂.2, bcR'.ha, hwL_R_neg]
    · exact Set.disjoint_left.mp hdR ⟨r₁, ⟨hr₁.1, lt_of_le_of_ne hr₁.2 h1⟩, rfl⟩
        (he.symm ▸ ⟨_, hseg_R_mem bcR' hwRR_fr r₂ hr₂, rfl⟩)
  have hM0_disj_βR : ∀ r : Fin k, Disjoint (seg ⟨3 * (r.1 + 1), by omega⟩ '' Icc 0 1) (β r.succ '' Icc 0 1) := fun r => by
    rw [Set.disjoint_left, hseg_ML r]; rintro _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, he⟩
    by_cases h0 : r₂ = 0
    · subst h0; rw [(hβM r).2] at he
      have h1 := congrArg Complex.re ((bcM r).hgi (hseg_L_mem (bcM r) (hwLM r).1 r₁ hr₁)
        ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset (hwRM r).1) he.symm)
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at h1
      nlinarith [hr₁.1, hr₁.2, (hwLM r).2, (hwRM r).2]
    · exact Set.disjoint_left.mp (hdM r).2 ⟨r₂, ⟨lt_of_le_of_ne hr₂.1 (Ne.symm h0), hr₂.2⟩, rfl⟩
        (he ▸ ⟨_, hseg_L_mem (bcM r) (hwLM r).1 r₁ hr₁, rfl⟩)
  have hM1_disj_βL : ∀ r : Fin k, Disjoint (β r.castSucc '' Icc 0 1) (seg ⟨3 * (r.1 + 1) + 1, by omega⟩ '' Icc 0 1) := fun r => by
    rw [Set.disjoint_left, hseg_MR r]; rintro _ ⟨r₁, hr₁, rfl⟩ ⟨r₂, hr₂, he⟩
    by_cases h1 : r₁ = 1
    · subst h1; rw [(hβM r).1] at he
      have h2 := congrArg Complex.re ((bcM r).hgi ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset (hwLM r).1)
        (hseg_R_mem (bcM r) (hwRM r).1 r₂ hr₂) he.symm)
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at h2
      nlinarith [hr₂.1, hr₂.2, (hwLM r).2, (hwRM r).2]
    · exact Set.disjoint_left.mp (hdM r).1 ⟨r₁, ⟨hr₁.1, lt_of_le_of_ne hr₁.2 h1⟩, rfl⟩
        (he.symm ▸ ⟨_, hseg_R_mem (bcM r) (hwRM r).1 r₂ hr₂, rfl⟩)
  -- Helper: classify any `i : Fin N` as either in `bcL'.box` (`i/3 = 0, i%3 < 2`), `bcR'.box` (`i/3 = k+1`),
  -- `(bcM r).box` (`i/3 = r+1, i%3 < 2`), or `Ω j` (`i%3 = 2, j = i/3`)!
  have hseg_box_or_Ω : ∀ i : Fin N,
      (i.1 / 3 = 0 ∧ i.1 % 3 < 2 ∧ seg i '' Icc 0 1 ⊆ bcL'.box) ∨
      (i.1 / 3 = k + 1 ∧ i.1 % 3 < 2 ∧ seg i '' Icc 0 1 ⊆ bcR'.box) ∨
      (∃ r : Fin k, i.1 / 3 = r.1 + 1 ∧ i.1 % 3 < 2 ∧ seg i '' Icc 0 1 ⊆ (bcM r).box) ∨
      (∃ j : Fin (k + 1), i.1 = 3 * j.1 + 2 ∧ seg i = β j ∧ seg i '' Icc 0 1 ⊆ Ω j) := fun i => by
    rcases (show i.1 % 3 = 0 ∨ i.1 % 3 = 1 ∨ i.1 % 3 = 2 by omega) with h0 | h1 | h2
    · by_cases hq0 : i.1 / 3 = 0
      · have hi : i = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega); exact Or.inl ⟨hq0, by omega, hi ▸ hseg_in_boxL.1⟩
      · by_cases hqk : i.1 / 3 = k + 1
        · have hi : i = ⟨3 * k + 3, by omega⟩ := Fin.ext (by dsimp; omega); exact Or.inr (Or.inl ⟨hqk, by omega, hi ▸ hseg_in_boxR.1⟩)
        · let r : Fin k := ⟨i.1 / 3 - 1, by omega⟩
          have hi : i = ⟨3 * (r.1 + 1), by omega⟩ := Fin.ext (by dsimp [r]; omega)
          exact Or.inr (Or.inr (Or.inl ⟨r, by dsimp [r]; omega, by omega, hi ▸ (hseg_in_boxM r).1⟩))
    · by_cases hq0 : i.1 / 3 = 0
      · have hi : i = ⟨1, by omega⟩ := Fin.ext (show i.1 = 1 by omega); exact Or.inl ⟨hq0, by omega, hi ▸ hseg_in_boxL.2⟩
      · by_cases hqk : i.1 / 3 = k + 1
        · have hi : i = ⟨3 * k + 4, by omega⟩ := Fin.ext (by dsimp; omega); exact Or.inr (Or.inl ⟨hqk, by omega, hi ▸ hseg_in_boxR.2⟩)
        · let r : Fin k := ⟨i.1 / 3 - 1, by omega⟩
          have hi : i = ⟨3 * (r.1 + 1) + 1, by omega⟩ := Fin.ext (by dsimp [r]; omega)
          exact Or.inr (Or.inr (Or.inl ⟨r, by dsimp [r]; omega, by omega, hi ▸ (hseg_in_boxM r).2⟩))
    · by_cases hq0 : i.1 / 3 = 0
      · have hi : i = ⟨2, by omega⟩ := Fin.ext (by dsimp; omega)
        exact Or.inr (Or.inr (Or.inr ⟨0, by dsimp; omega, hi ▸ hseg_2, hi ▸ hseg_2 ▸ (hβ_prop 0).2.2⟩))
      · let r : Fin k := ⟨i.1 / 3 - 1, by omega⟩
        have hi : i = ⟨3 * (r.1 + 1) + 2, by omega⟩ := Fin.ext (by dsimp [r]; omega)
        exact Or.inr (Or.inr (Or.inr ⟨r.succ, by dsimp [r]; omega, hi ▸ hseg_Mβ r, hi ▸ hseg_Mβ r ▸ (hβ_prop r.succ).2.2⟩))
  have hfar : ∀ i j : Fin N, i.1 + 1 < j.1 → Disjoint (seg i '' Icc 0 1) (seg j '' Icc 0 1) := by
    intro i j hij
    rcases hseg_box_or_Ω i with ⟨hiq, hir, his⟩ | ⟨hiq, hir, his⟩ | ⟨ri, hiq, hir, his⟩ | ⟨ji, hiq, hiseg, his⟩ <;>
    rcases hseg_box_or_Ω j with ⟨hjq, hjr, hjs⟩ | ⟨hjq, hjr, hjs⟩ | ⟨rj, hjq, hjr, hjs⟩ | ⟨jj, hjq, hjseg, hjs⟩
    · omega
    · exact (hLb ▸ hRb ▸ hL_disj_R).mono his hjs
    · exact (hLb ▸ hL_disj_M rj).mono his hjs
    · by_cases hjj0 : jj.1 = 0
      · have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
        have hjj : jj = 0 := Fin.ext hjj0
        rw [hi0, hjseg, hjj]; exact hL0_disj_β0
      · exact (hLb ▸ hL_disj_Ω jj hjj0).mono his hjs
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact (hRb ▸ hR_disj_M ri).symm.mono his hjs
    · exact (hM_disj ri rj (by intro h; subst h; omega)).mono his hjs
    · by_cases hjj : jj.1 = ri.1 + 1
      · have hjjeq : jj = ri.succ := Fin.ext hjj
        rw [hjseg, hjjeq]
        have hi0 : i = ⟨3 * (ri.1 + 1), by have := ri.2; omega⟩ := Fin.ext (by dsimp; omega)
        rw [hi0]; exact hM0_disj_βR ri
      · exact (hM_disj_Ω ri jj (by omega) hjj).mono his hjs
    · omega
    · by_cases hjik : ji.1 = k
      · have hj4 : j = ⟨3 * k + 4, by omega⟩ := Fin.ext (by dsimp; omega)
        have hjieq : ji = Fin.last k := Fin.ext hjik
        rw [hj4, hiseg, hjieq]; exact hR1_disj_βlast
      · exact (hRb ▸ hR_disj_Ω ji hjik).symm.mono his hjs
    · by_cases hji : ji.1 = rj.1
      · have hj1 : j = ⟨3 * (rj.1 + 1) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        have hjieq : ji = rj.castSucc := Fin.ext hji
        rw [hj1, hiseg, hjieq]; exact hM1_disj_βL rj
      · exact (hM_disj_Ω rj ji hji (by omega)).symm.mono his hjs
    · exact (hΩ_disj (by intro h; subst h; omega)).mono his hjs
  -- Step 3: Define `γ_ext := concatSeq hN seg` and construct `rcL`, `rcR`, `rcM`!
  let γ_ext : ℝ → S := concatSeq hN seg
  have hγc : ContinuousOn γ_ext (Icc 0 1) := concatSeq_continuousOn hN seg hmatch hseg_c
  have hγi : InjOn γ_ext (Icc 0 1) := concatSeq_injOn hN seg hmatch hseg_i hadj hfar
  have hγim : γ_ext '' Icc 0 1 = ⋃ i : Fin N, seg i '' Icc 0 1 := concatSeq_image hN seg hmatch
  have hγint : γ_ext '' Icc 0 1 ⊆ (bd S)ᶜ := by
    rw [hγim]; refine iUnion_subset fun i => ?_
    rcases hseg_box_or_Ω i with ⟨-, -, hs⟩ | ⟨-, -, hs⟩ | ⟨r, -, -, hs⟩ | ⟨j, -, -, hs⟩
    · exact hs.trans bcL'.hgint
    · exact hs.trans bcR'.hgint
    · exact hs.trans (bcM r).hgint
    · exact hs.trans ((hΩ_free j).trans sdiff_subset)
  exact ⟨seg, hseg_0, hseg_1, hseg_2, hseg_RL, hseg_RR, hseg_ML, hseg_MR, hseg_Mβ,
    hmatch, hseg_box_or_Ω, hγc, hγi, hγim, hγint⟩

set_option maxHeartbeats 400000 in
/-- **Master `BandArcData` builder**: given `k : ℕ`, `idxs : Fin k → Fin m`, `k + 2` pairwise
disjoint `BoxChart`s (`bcL` on `M.U`, `bcM r` on `Q (idxs r)`, `bcR` on `M.U`), and `k + 1`
pairwise disjoint open connected regions `Ω j ⊆ (bd S)ᶜ \ (M.U ∪ ⋃ Q)` linking adjacent boxes
and disjoint from all non-adjacent boxes, constructs `BandArcData S M Q k` with `data.idxs = idxs`! -/
private theorem build_bandArcData (hS : IsSurface S) {s t : S} (M : ProperManifold S s t)
    {m : ℕ} {Q : Fin m → Set S} {k : ℕ}
    (idxs : Fin k → Fin m) (hidxs_inj : Function.Injective idxs)
    (hidxs_disj : ∀ r : Fin k, Disjoint M.U (Q (idxs r)))
    (bcL : BoxChart S M.U) (bcR : BoxChart S M.U)
    (bcM : ∀ r : Fin k, BoxChart S (Q (idxs r)))
    (hL_disj_R : Disjoint bcL.box bcR.box)
    (hL_disj_M : ∀ r : Fin k, Disjoint bcL.box (bcM r).box)
    (hR_disj_M : ∀ r : Fin k, Disjoint bcR.box (bcM r).box)
    (hM_disj : ∀ r₁ r₂ : Fin k, r₁ ≠ r₂ → Disjoint (bcM r₁).box (bcM r₂).box)
    (hL_disj_Q : ∀ j : Fin m, Disjoint bcL.box (Q j))
    (hR_disj_Q : ∀ j : Fin m, Disjoint bcR.box (Q j))
    (hM_disj_M : ∀ r : Fin k, Disjoint (bcM r).box M.U)
    (hM_disj_Q : ∀ r : Fin k, ∀ j : Fin m, j ≠ idxs r → Disjoint (bcM r).box (Q j))
    (hdiff_comp : ¬ (bcL.g 0 ∈ M.P₀ ∧ bcR.g 0 ∈ M.P₀) ∧
      ∀ a ∈ M.Os, ¬ (bcL.g 0 ∈ a.O ∧ bcR.g 0 ∈ a.O))
    (Ω : Fin (k + 1) → Set S)
    (hΩ_open : ∀ j, IsOpen (Ω j))
    (hΩ_conn : ∀ j, IsConnected (Ω j))
    (hΩ_free : ∀ j, Ω j ⊆ (bd S)ᶜ \ (M.U ∪ ⋃ q : Fin m, Q q))
    (hΩ_disj : Pairwise fun j₁ j₂ => Disjoint (Ω j₁) (Ω j₂))
    (hL_Ω : (bcL.box ∩ Ω 0).Nonempty)
    (hR_Ω : (bcR.box ∩ Ω (Fin.last k)).Nonempty)
    (hM_left_Ω : ∀ r : Fin k, (bcM r).clLeftHalf ⊆ Ω r.castSucc)
    (hM_right_Ω : ∀ r : Fin k, (bcM r).clRightHalf ⊆ Ω r.succ)
    (hL_disj_Ω : ∀ j : Fin (k + 1), j.1 ≠ 0 → Disjoint bcL.box (Ω j))
    (hR_disj_Ω : ∀ j : Fin (k + 1), j.1 ≠ k → Disjoint bcR.box (Ω j))
    (hM_disj_Ω : ∀ (r : Fin k) (j : Fin (k + 1)), j.1 ≠ r.1 → j.1 ≠ r.1 + 1 → Disjoint (bcM r).box (Ω j)) :
    ∃ data : BandArcData S M Q k, data.idxs = idxs := by
  classical
  have hΩ_disj_M : ∀ j, Disjoint (Ω j) M.U := fun j =>
    Set.disjoint_left.mpr fun x hx hM => (hΩ_free j hx).2 (Or.inl hM)
  have hΩ_disj_Q : ∀ j q, Disjoint (Ω j) (Q q) := fun j q =>
    Set.disjoint_left.mpr fun x hx hQ => (hΩ_free j hx).2 (Or.inr (mem_iUnion.mpr ⟨q, hQ⟩))
  obtain ⟨bcL', bcR', wR_L, wL_R, wL_M, wR_M, β, hL0, hLb, hR0, hRb,
    hwR_L_fr, hwR_L_pos, hwL_R_fr, hwL_R_neg, hwLM, hwRM, hβ_prop,
    hβ00, hβl1, hβM, hdL, hdR, hdM⟩ :=
    build_bandArcData_bridges hS M idxs bcL bcR bcM hL_disj_R hL_disj_M hR_disj_M hM_disj
      Ω hΩ_open hΩ_conn hΩ_free hΩ_disj hL_Ω hR_Ω hM_left_Ω hM_right_Ω
  let N : ℕ := 3 * k + 5
  have hN_def : N = 3 * k + 5 := rfl
  have hN : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let wL_L : ℂ := (-bcL'.a : ℂ)
  let wR_R : ℂ := (bcR'.a : ℂ)
  have hwLL_fr : wL_L ∈ frontier bcL'.R := by
    refine ⟨subset_closure (Complex.mem_reProdIm.mpr ⟨by simp [wL_L, bcL'.ha.le], by simp [wL_L, bcL'.hb.le]⟩), fun h => ?_⟩
    rw [BoxChart.R, interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at h
    simp [wL_L] at h
  have hwRR_fr : wR_R ∈ frontier bcR'.R := by
    refine ⟨subset_closure (Complex.mem_reProdIm.mpr ⟨by simp [wR_R, bcR'.ha.le], by simp [wR_R, bcR'.hb.le]⟩), fun h => ?_⟩
    rw [BoxChart.R, interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at h
    simp [wR_R] at h
  have hseg_L_mem : ∀ {A' : Set S} (bc : BoxChart S A') {w : ℂ}, w ∈ frontier bc.R →
      ∀ r ∈ Icc (0 : ℝ) 1, ((1 - r : ℝ) : ℂ) * w ∈ bc.R := by
    intro A' bc w hfr r hr
    have hwR := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hfr)
    rw [BoxChart.R, Complex.mem_reProdIm]
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
    exact ⟨⟨by nlinarith only [hwR.1.1, hr.1, hr.2, bc.ha], by nlinarith only [hwR.1.2, hr.1, hr.2, bc.ha]⟩,
      ⟨by nlinarith only [hwR.2.1, hr.1, hr.2, bc.hb], by nlinarith only [hwR.2.2, hr.1, hr.2, bc.hb]⟩⟩
  have hseg_R_mem : ∀ {A' : Set S} (bc : BoxChart S A') {w : ℂ}, w ∈ frontier bc.R →
      ∀ r ∈ Icc (0 : ℝ) 1, (r : ℂ) * w ∈ bc.R := by
    intro A' bc w hfr r hr
    have hwR := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hfr)
    rw [BoxChart.R, Complex.mem_reProdIm]
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
    exact ⟨⟨by nlinarith only [hwR.1.1, hr.1, hr.2, bc.ha], by nlinarith only [hwR.1.2, hr.1, hr.2, bc.ha]⟩,
      ⟨by nlinarith only [hwR.2.1, hr.1, hr.2, bc.hb], by nlinarith only [hwR.2.2, hr.1, hr.2, bc.hb]⟩⟩
  obtain ⟨seg, hseg_0, hseg_1, hseg_2, hseg_RL, hseg_RR, hseg_ML, hseg_MR, hseg_Mβ,
    hmatch, hseg_box_or_Ω, hγc, hγi, hγim, hγint⟩ :=
    build_bandArcData_concat M idxs bcL' bcR' bcM
      (hLb ▸ hRb ▸ hL_disj_R) (fun r => hLb ▸ hL_disj_M r) (fun r => hRb ▸ hR_disj_M r) hM_disj
      Ω hΩ_free hΩ_disj (fun j h => hLb ▸ hL_disj_Ω j h) (fun j h => hRb ▸ hR_disj_Ω j h) hM_disj_Ω
      wR_L wL_R wL_M wR_M β hwR_L_fr hwR_L_pos hwL_R_fr hwL_R_neg hwLM hwRM hβ_prop
      hβ00 hβl1 hβM hdL hdR hdM
  let γ_ext : ℝ → S := concatSeq hN seg
  -- Helper: scaling `w ∈ frontier bc.R` by `1/2` lands in `frontier ([-a/2, a/2] × [-b/2, b/2])`:
  have hhalf_fr : ∀ {A' : Set S} (bc : BoxChart S A') {w : ℂ}, w ∈ frontier bc.R →
      ((1 / 2 : ℝ) : ℂ) * w ∈ frontier (Icc (-(bc.a / 2)) (bc.a / 2) ×ℂ Icc (-(bc.b / 2)) (bc.b / 2)) := by
    intro A' bc w hw
    have hwR := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hw)
    have hnotint := hw.2
    rw [BoxChart.R, interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at hnotint
    refine ⟨subset_closure ?_, fun hint => hnotint ?_⟩
    · rw [Complex.mem_reProdIm]; simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
      exact ⟨⟨by linarith [hwR.1.1], by linarith [hwR.1.2]⟩, ⟨by linarith [hwR.2.1], by linarith [hwR.2.2]⟩⟩
    · rw [interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at hint
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero] at hint
      exact ⟨⟨by linarith [hint.1.1], by linarith [hint.1.2]⟩, ⟨by linarith [hint.2.1], by linarith [hint.2.2]⟩⟩
  have hhalf_le : ∀ {A' : Set S} (bc : BoxChart S A') {w : ℂ} {c : ℝ}, w ∈ frontier bc.R → 0 ≤ c →
      (c : ℂ) * w ∈ Icc (-(bc.a / 2)) (bc.a / 2) ×ℂ Icc (-(bc.b / 2)) (bc.b / 2) → c ≤ 1 / 2 := by
    intro A' bc w c hw hc0 hcR
    by_contra hgt; push Not at hgt
    have hnotint := hw.2
    rw [BoxChart.R, interior_reProdIm, interior_Icc, interior_Icc, Complex.mem_reProdIm] at hnotint
    rw [Complex.mem_reProdIm] at hcR
    simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero] at hcR
    exact hnotint ⟨⟨by nlinarith [hcR.1.1, bc.ha], by nlinarith [hcR.1.2, bc.ha]⟩,
      ⟨by nlinarith [hcR.2.1, bc.hb], by nlinarith [hcR.2.2, bc.hb]⟩⟩
  have hhalf_sub : ∀ {A' : Set S} (bc : BoxChart S A'),
      Icc (-(bc.a / 2)) (bc.a / 2) ×ℂ Icc (-(bc.b / 2)) (bc.b / 2) ⊆ bc.R := by
    intro A' bc z hz
    rw [Complex.mem_reProdIm] at hz; rw [BoxChart.R, Complex.mem_reProdIm]
    exact ⟨⟨by linarith [hz.1.1, bc.ha], by linarith [hz.1.2, bc.ha]⟩, ⟨by linarith [hz.2.1, bc.hb], by linarith [hz.2.2, bc.hb]⟩⟩
  have hhalf_A : ∀ {A' : Set S} (bc : BoxChart S A'),
      A' ∩ bc.g '' (Icc (-(bc.a / 2)) (bc.a / 2) ×ℂ Icc (-(bc.b / 2)) (bc.b / 2)) =
        bc.g '' (({0} : Set ℝ) ×ℂ Icc (-(bc.b / 2)) (bc.b / 2)) := by
    intro A' bc
    ext y; constructor
    · rintro ⟨hyA, z, hz, rfl⟩
      have h1 : bc.g z ∈ A' ∩ bc.box := ⟨hyA, z, hhalf_sub bc hz, rfl⟩
      rw [BoxChart.box, bc.hA_eq] at h1
      obtain ⟨w, hw, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hw
      have hwR : w ∈ bc.R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith [bc.ha], bc.ha.le⟩, hw.2⟩
      have hzw := bc.hgi (hhalf_sub bc hz) hwR hfe.symm
      exact ⟨z, Complex.mem_reProdIm.mpr ⟨by rw [hzw]; exact hw.1, (Complex.mem_reProdIm.mp hz).2⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩; rw [Complex.mem_reProdIm] at hz
      have hz' : z ∈ Icc (-(bc.a / 2)) (bc.a / 2) ×ℂ Icc (-(bc.b / 2)) (bc.b / 2) :=
        Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hz.1]; exact ⟨by linarith [bc.ha], by linarith [bc.ha]⟩, hz.2⟩
      have h1 : bc.g z ∈ A' ∩ bc.box := by
        rw [BoxChart.box, bc.hA_eq]
        exact ⟨z, Complex.mem_reProdIm.mpr ⟨hz.1, (Complex.mem_reProdIm.mp (hhalf_sub bc hz')).2⟩, rfl⟩
      exact ⟨h1.1, z, hz', rfl⟩
  -- Build `rcL : RectCross S γ_ext M.U` on the half-box of `bcL'` (`s = 1/(2N)`, `t_mid = 1/N`, `e = 3/(2N)`):
  let rcL : RectCross S γ_ext M.U := {
    g := bcL'.g, a := bcL'.a / 2, b := bcL'.b / 2,
    ha := half_pos bcL'.ha, hb := half_pos bcL'.hb,
    hgc := bcL'.hgc.mono (hhalf_sub bcL'), hgi := bcL'.hgi.mono (hhalf_sub bcL'),
    hgint := (image_mono (hhalf_sub bcL')).trans bcL'.hgint,
    hA_eq := hhalf_A bcL',
    s := (1 / 2 : ℝ) / N, t_mid := (1 : ℝ) / N, e := (3 / 2 : ℝ) / N,
    hs0 := by positivity, hst := div_lt_div_of_pos_right (by norm_num) hNpos,
    hte := div_lt_div_of_pos_right (by norm_num) hNpos,
    he1 := (div_lt_one hNpos).mpr (by have : (5 : ℝ) ≤ N := (by exact_mod_cast (show 5 ≤ N by omega)); linarith),
    wL := ((1 / 2 : ℝ) : ℂ) * wL_L, wR := ((1 / 2 : ℝ) : ℂ) * wR_L,
    hwL := hhalf_fr bcL' hwLL_fr, hwR := hhalf_fr bcL' hwR_L_fr,
    hwL_re := by simp [wL_L, bcL'.ha],
    hwR_re := by simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]; positivity,
    hγ_L := fun r hr => by
      have heq : lin ((1 / 2 : ℝ) / N) ((1 : ℝ) / N) r = (((⟨0, by omega⟩ : Fin N) : ℝ) + (1 / 2 + r / 2)) / N := by
        simp only [lin]; push_cast; ring
      change concatSeq hN seg _ = _
      rw [heq, concatSeq_on_piece hN seg hmatch ⟨0, by omega⟩ ⟨by linarith only [hr.1], by linarith only [hr.2]⟩, hseg_0]
      dsimp only [wL_L]; congr 1; push_cast; ring
    hγ_R := fun r hr => by
      have heq : lin ((1 : ℝ) / N) ((3 / 2 : ℝ) / N) r = (((⟨1, by omega⟩ : Fin N) : ℝ) + r / 2) / N := by
        simp only [lin]; push_cast; ring
      change concatSeq hN seg _ = _
      rw [heq, concatSeq_on_piece hN seg hmatch ⟨1, by omega⟩ ⟨by linarith [hr.1], by linarith [hr.2]⟩, hseg_1]
      dsimp only; congr 1; push_cast; ring
    hγD := by
      ext y; constructor
      · rintro ⟨hyγ, z, hz, rfl⟩
        rw [hγim] at hyγ; obtain ⟨i, r, hr, hre⟩ := mem_iUnion.mp hyγ
        have hz_in_L : bcL'.g z ∈ bcL'.box := ⟨z, hhalf_sub bcL' hz, rfl⟩
        rcases hseg_box_or_Ω i with ⟨hiq, hir, -⟩ | ⟨-, -, hs⟩ | ⟨q, -, -, hs⟩ | ⟨j, hiq, hiseg, hs⟩
        · rcases (show i.1 = 0 ∨ i.1 = 1 by omega) with hi0 | hi1
          · have hi' : i = ⟨0, by omega⟩ := Fin.ext hi0; rw [hi', hseg_0] at hre
            have hzeq := bcL'.hgi (hseg_L_mem bcL' hwLL_fr r hr) (hhalf_sub bcL' hz) hre
            have hle : 1 - r ≤ 1 / 2 := hhalf_le bcL' hwLL_fr (by linarith [hr.2]) (hzeq ▸ hz)
            refine ⟨r / N, ⟨div_le_div_of_nonneg_right (by linarith) hNpos.le,
              div_le_div_of_nonneg_right (by linarith [hr.2]) hNpos.le⟩, ?_⟩
            have h1 := concatSeq_on_piece hN seg hmatch ⟨0, by omega⟩ hr
            have harg : ((((⟨0, by omega⟩ : Fin N) : ℕ) : ℝ) + r) / N = r / N := by push_cast; ring
            rw [harg, hseg_0, hre] at h1; exact h1
          · have hi' : i = ⟨1, by omega⟩ := Fin.ext hi1; rw [hi', hseg_1] at hre
            have hzeq := bcL'.hgi (hseg_R_mem bcL' hwR_L_fr r hr) (hhalf_sub bcL' hz) hre
            have hle : r ≤ 1 / 2 := hhalf_le bcL' hwR_L_fr hr.1 (hzeq ▸ hz)
            refine ⟨(1 + r) / N, ⟨div_le_div_of_nonneg_right (by linarith [hr.1]) hNpos.le,
              div_le_div_of_nonneg_right (by linarith) hNpos.le⟩, ?_⟩
            have h1 := concatSeq_on_piece hN seg hmatch ⟨1, by omega⟩ hr
            have harg : ((((⟨1, by omega⟩ : Fin N) : ℕ) : ℝ) + r) / N = (1 + r) / N := by push_cast; ring
            rw [harg, hseg_1, hre] at h1; exact h1
        · exact (Set.disjoint_left.mp (hLb ▸ hRb ▸ hL_disj_R) hz_in_L (hs ⟨r, hr, hre⟩)).elim
        · exact (Set.disjoint_left.mp (hLb ▸ hL_disj_M q) hz_in_L (hs ⟨r, hr, hre⟩)).elim
        · by_cases hj0 : j.1 = 0
          · have hjeq : j = 0 := Fin.ext hj0; rw [hiseg, hjeq] at hre
            by_cases hr0 : r = 0
            · subst hr0; rw [hβ00] at hre
              have hzeq := bcL'.hgi ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hwR_L_fr) (hhalf_sub bcL' hz) hre
              have := hhalf_le bcL' hwR_L_fr zero_le_one (by simpa [hzeq] using hz)
              norm_num at this
            · exact (Set.disjoint_left.mp hdL ⟨r, ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), hr.2⟩, rfl⟩ (hre ▸ hz_in_L)).elim
          · exact (Set.disjoint_left.mp (hLb ▸ hL_disj_Ω j hj0) hz_in_L (hs ⟨r, hr, hre⟩)).elim
      · rintro ⟨x, hx, rfl⟩
        have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨(by positivity : (0 : ℝ) ≤ (1 / 2) / N).trans hx.1,
          hx.2.trans ((div_lt_one hNpos).mpr (by have : (5 : ℝ) ≤ N := (by exact_mod_cast (show 5 ≤ N by omega)); linarith)).le⟩
        refine ⟨⟨x, hx01, rfl⟩, ?_⟩
        by_cases hle : x ≤ 1 / N
        · let r := (N : ℝ) * x
          have hr : r ∈ Icc (1 / 2 : ℝ) 1 := ⟨(div_le_iff₀' hNpos).mp hx.1, (le_div_iff₀' hNpos).mp hle⟩
          have hx_eq : x = ((((⟨0, by omega⟩ : Fin N) : ℕ) : ℝ) + r) / N := by simp only [r]; push_cast; field_simp [hNpos.ne']; ring
          change concatSeq hN seg x ∈ _
          rw [hx_eq, concatSeq_on_piece hN seg hmatch ⟨0, by omega⟩ ⟨by linarith [hr.1], hr.2⟩, hseg_0]
          refine ⟨_, ?_, rfl⟩
          have hwR := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hwLL_fr)
          rw [Complex.mem_reProdIm]; simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
          exact ⟨⟨by nlinarith only [hwR.1.1, hr.1, hr.2, bcL'.ha], by nlinarith only [hwR.1.2, hr.1, hr.2, bcL'.ha]⟩,
            ⟨by nlinarith only [hwR.2.1, hr.1, hr.2, bcL'.hb], by nlinarith only [hwR.2.2, hr.1, hr.2, bcL'.hb]⟩⟩
        · let r := (N : ℝ) * x - 1
          have hr : r ∈ Icc (0 : ℝ) (1 / 2) := ⟨by have := (div_lt_iff₀' hNpos).mp (lt_of_not_ge hle); linarith,
            by have := (le_div_iff₀' hNpos).mp hx.2; linarith⟩
          have hx_eq : x = ((((⟨1, by omega⟩ : Fin N) : ℕ) : ℝ) + r) / N := by simp only [r]; push_cast; field_simp [hNpos.ne']; ring
          change concatSeq hN seg x ∈ _
          rw [hx_eq, concatSeq_on_piece hN seg hmatch ⟨1, by omega⟩ ⟨hr.1, by linarith [hr.2]⟩, hseg_1]
          refine ⟨_, ?_, rfl⟩
          have hwR := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hwR_L_fr)
          rw [Complex.mem_reProdIm]; simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
          exact ⟨⟨by nlinarith only [hwR.1.1, hr.1, hr.2, bcL'.ha], by nlinarith only [hwR.1.2, hr.1, hr.2, bcL'.ha]⟩,
            ⟨by nlinarith only [hwR.2.1, hr.1, hr.2, bcL'.hb], by nlinarith only [hwR.2.2, hr.1, hr.2, bcL'.hb]⟩⟩ }
  -- Build `rcR : RectCross S γ_ext M.U` on the half-box of `bcR'` (`s = (3k+3.5)/N`, `t_mid = (3k+4)/N`, `e = (3k+4.5)/N`):
  let rcR : RectCross S γ_ext M.U := {
    g := bcR'.g, a := bcR'.a / 2, b := bcR'.b / 2,
    ha := half_pos bcR'.ha, hb := half_pos bcR'.hb,
    hgc := bcR'.hgc.mono (hhalf_sub bcR'), hgi := bcR'.hgi.mono (hhalf_sub bcR'),
    hgint := (image_mono (hhalf_sub bcR')).trans bcR'.hgint,
    hA_eq := hhalf_A bcR',
    s := ((3 * k + 3 : ℝ) + 1 / 2) / N, t_mid := ((3 * k + 4 : ℝ)) / N, e := ((3 * k + 4 : ℝ) + 1 / 2) / N,
    hs0 := by positivity, hst := div_lt_div_of_pos_right (by linarith) hNpos,
    hte := div_lt_div_of_pos_right (by linarith) hNpos,
    he1 := (div_lt_one hNpos).mpr (by have : (N : ℝ) = 3 * k + 5 := (by exact_mod_cast hN_def); linarith),
    wL := ((1 / 2 : ℝ) : ℂ) * wL_R, wR := ((1 / 2 : ℝ) : ℂ) * wR_R,
    hwL := hhalf_fr bcR' hwL_R_fr, hwR := hhalf_fr bcR' hwRR_fr,
    hwL_re := by simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]; linarith,
    hwR_re := by simp [wR_R, bcR'.ha],
    hγ_L := fun r hr => by
      have heq : lin (((3 * k + 3 : ℝ) + 1 / 2) / N) ((3 * k + 4 : ℝ) / N) r =
          ((((⟨3 * k + 3, by omega⟩ : Fin N) : ℕ) : ℝ) + (1 / 2 + r / 2)) / N := by
        simp only [lin]; push_cast; ring
      change concatSeq hN seg _ = _
      rw [heq, concatSeq_on_piece hN seg hmatch ⟨3 * k + 3, by omega⟩ ⟨by linarith [hr.1], by linarith [hr.2]⟩, hseg_RL]
      dsimp only; congr 1; push_cast; ring
    hγ_R := fun r hr => by
      have heq : lin ((3 * k + 4 : ℝ) / N) (((3 * k + 4 : ℝ) + 1 / 2) / N) r =
          ((((⟨3 * k + 4, by omega⟩ : Fin N) : ℕ) : ℝ) + r / 2) / N := by
        simp only [lin]; push_cast; ring
      change concatSeq hN seg _ = _
      rw [heq, concatSeq_on_piece hN seg hmatch ⟨3 * k + 4, by omega⟩ ⟨by linarith only [hr.1], by linarith only [hr.2]⟩, hseg_RR]
      dsimp only [wR_R]; congr 1; push_cast; ring
    hγD := by
      ext y; constructor
      · rintro ⟨hyγ, z, hz, rfl⟩
        rw [hγim] at hyγ; obtain ⟨i, r, hr, hre⟩ := mem_iUnion.mp hyγ
        have hz_in_R : bcR'.g z ∈ bcR'.box := ⟨z, hhalf_sub bcR' hz, rfl⟩
        rcases hseg_box_or_Ω i with ⟨-, -, hs⟩ | ⟨hiq, hir, -⟩ | ⟨q, -, -, hs⟩ | ⟨j, hiq, hiseg, hs⟩
        · exact (Set.disjoint_left.mp (hLb ▸ hRb ▸ hL_disj_R) (hs ⟨r, hr, hre⟩) hz_in_R).elim
        · rcases (show i.1 = 3 * k + 3 ∨ i.1 = 3 * k + 4 by omega) with hiL | hiR
          · have hi' : i = ⟨3 * k + 3, by omega⟩ := Fin.ext hiL; rw [hi', hseg_RL] at hre
            have hzeq := bcR'.hgi (hseg_L_mem bcR' hwL_R_fr r hr) (hhalf_sub bcR' hz) hre
            have hle : 1 - r ≤ 1 / 2 := hhalf_le bcR' hwL_R_fr (by linarith [hr.2]) (hzeq ▸ hz)
            refine ⟨((3 * k + 3 : ℝ) + r) / N, ⟨div_le_div_of_nonneg_right (by linarith) hNpos.le,
              div_le_div_of_nonneg_right (by linarith [hr.2]) hNpos.le⟩, ?_⟩
            have h1 := concatSeq_on_piece hN seg hmatch ⟨3 * k + 3, by omega⟩ hr
            have harg : ((((⟨3 * k + 3, by omega⟩ : Fin N) : ℕ) : ℝ) + r) / N = ((3 * k + 3 : ℝ) + r) / N := by push_cast; ring
            rw [harg, hseg_RL, hre] at h1; exact h1
          · have hi' : i = ⟨3 * k + 4, by omega⟩ := Fin.ext hiR; rw [hi', hseg_RR] at hre
            have hzeq := bcR'.hgi (hseg_R_mem bcR' hwRR_fr r hr) (hhalf_sub bcR' hz) hre
            have hle : r ≤ 1 / 2 := hhalf_le bcR' hwRR_fr hr.1 (hzeq ▸ hz)
            refine ⟨((3 * k + 4 : ℝ) + r) / N, ⟨div_le_div_of_nonneg_right (by linarith [hr.1]) hNpos.le,
              div_le_div_of_nonneg_right (by linarith) hNpos.le⟩, ?_⟩
            have h1 := concatSeq_on_piece hN seg hmatch ⟨3 * k + 4, by omega⟩ hr
            have harg : ((((⟨3 * k + 4, by omega⟩ : Fin N) : ℕ) : ℝ) + r) / N = ((3 * k + 4 : ℝ) + r) / N := by push_cast; ring
            rw [harg, hseg_RR, hre] at h1; exact h1
        · exact (Set.disjoint_left.mp (hRb ▸ hR_disj_M q) hz_in_R (hs ⟨r, hr, hre⟩)).elim
        · by_cases hjk : j.1 = k
          · have hjeq : j = Fin.last k := Fin.ext hjk; rw [hiseg, hjeq] at hre
            by_cases hr1 : r = 1
            · subst hr1; rw [hβl1] at hre
              have hzeq := bcR'.hgi ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hwL_R_fr) (hhalf_sub bcR' hz) hre
              have := hhalf_le bcR' hwL_R_fr zero_le_one (by simpa [hzeq] using hz)
              norm_num at this
            · exact (Set.disjoint_left.mp hdR ⟨r, ⟨hr.1, lt_of_le_of_ne hr.2 hr1⟩, rfl⟩ (hre ▸ hz_in_R)).elim
          · exact (Set.disjoint_left.mp (hRb ▸ hR_disj_Ω j hjk) hz_in_R (hs ⟨r, hr, hre⟩)).elim
      · rintro ⟨x, hx, rfl⟩
        have hN_eq : (N : ℝ) = 3 * k + 5 := by exact_mod_cast (rfl : N = 3 * k + 5)
        have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨(by positivity : (0 : ℝ) ≤ ((3 * k + 3 : ℝ) + 1 / 2) / N).trans hx.1,
          hx.2.trans ((div_le_one hNpos).mpr (by linarith))⟩
        refine ⟨⟨x, hx01, rfl⟩, ?_⟩
        by_cases hle : x ≤ (3 * k + 4 : ℝ) / N
        · let r := (N : ℝ) * x - (3 * k + 3)
          have hr : r ∈ Icc (1 / 2 : ℝ) 1 := ⟨by have := (div_le_iff₀' hNpos).mp hx.1; linarith,
            by have := (le_div_iff₀' hNpos).mp hle; linarith⟩
          have hx_eq : x = (((⟨3 * k + 3, by omega⟩ : Fin N) : ℝ) + r) / N := by
            simp only [r]; push_cast; field_simp [hNpos.ne']; ring
          change concatSeq hN seg x ∈ _
          rw [hx_eq, concatSeq_on_piece hN seg hmatch ⟨3 * k + 3, by omega⟩ ⟨by linarith only [hr.1], hr.2⟩, hseg_RL]
          refine ⟨_, ?_, rfl⟩
          have hwR := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hwL_R_fr)
          rw [Complex.mem_reProdIm]; simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
          exact ⟨⟨by nlinarith only [hwR.1.1, hr.1, hr.2, bcR'.ha], by nlinarith only [hwR.1.2, hr.1, hr.2, bcR'.ha]⟩,
            ⟨by nlinarith only [hwR.2.1, hr.1, hr.2, bcR'.hb], by nlinarith only [hwR.2.2, hr.1, hr.2, bcR'.hb]⟩⟩
        · let r := (N : ℝ) * x - (3 * k + 4)
          have hr : r ∈ Icc (0 : ℝ) (1 / 2) := ⟨by have := (div_lt_iff₀' hNpos).mp (lt_of_not_ge hle); linarith only [this],
            by have := (le_div_iff₀' hNpos).mp hx.2; linarith only [this]⟩
          have hx_eq : x = (((⟨3 * k + 4, by omega⟩ : Fin N) : ℝ) + r) / N := by
            simp only [r]; push_cast; field_simp [hNpos.ne']; ring
          change concatSeq hN seg x ∈ _
          rw [hx_eq, concatSeq_on_piece hN seg hmatch ⟨3 * k + 4, by omega⟩ ⟨hr.1, by linarith only [hr.2]⟩, hseg_RR]
          refine ⟨_, ?_, rfl⟩
          have hwR := Complex.mem_reProdIm.mp ((isClosed_Icc.reProdIm isClosed_Icc).frontier_subset hwRR_fr)
          rw [Complex.mem_reProdIm]; simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
          exact ⟨⟨by nlinarith only [hwR.1.1, hr.1, hr.2, bcR'.ha], by nlinarith only [hwR.1.2, hr.1, hr.2, bcR'.ha]⟩,
            ⟨by nlinarith only [hwR.2.1, hr.1, hr.2, bcR'.hb], by nlinarith only [hwR.2.2, hr.1, hr.2, bcR'.hb]⟩⟩ }
  -- Build `rcM r : RectCross S γ_ext (Q (idxs r))` on the FULL box `(bcM r).box`!
  let rcM : ∀ r : Fin k, RectCross S γ_ext (Q (idxs r)) := fun q => {
    g := (bcM q).g, a := (bcM q).a, b := (bcM q).b,
    ha := (bcM q).ha, hb := (bcM q).hb,
    hgc := (bcM q).hgc, hgi := (bcM q).hgi,
    hgint := (bcM q).hgint, hA_eq := (bcM q).hA_eq,
    s := ((3 * (q.1 + 1) : ℕ) : ℝ) / N,
    t_mid := ((3 * (q.1 + 1) + 1 : ℕ) : ℝ) / N,
    e := ((3 * (q.1 + 1) + 2 : ℕ) : ℝ) / N,
    hs0 := by positivity,
    hst := div_lt_div_of_pos_right (by push_cast; linarith) hNpos,
    hte := div_lt_div_of_pos_right (by push_cast; linarith) hNpos,
    he1 := (div_lt_one hNpos).mpr (by exact_mod_cast (show 3 * (q.1 + 1) + 2 < N by omega)),
    wL := wL_M q, wR := wR_M q,
    hwL := (hwLM q).1, hwR := (hwRM q).1,
    hwL_re := (hwLM q).2, hwR_re := (hwRM q).2,
    hγ_L := fun r hr => by
      have heq : lin (((3 * (q.1 + 1) : ℕ) : ℝ) / N) (((3 * (q.1 + 1) + 1 : ℕ) : ℝ) / N) r =
          ((((⟨3 * (q.1 + 1), by omega⟩ : Fin N) : ℕ) : ℝ) + r) / N := by
        simp only [lin]; push_cast; ring
      change concatSeq hN seg _ = _
      rw [heq, concatSeq_on_piece hN seg hmatch ⟨3 * (q.1 + 1), by omega⟩ hr, hseg_ML q]
    hγ_R := fun r hr => by
      have heq : lin (((3 * (q.1 + 1) + 1 : ℕ) : ℝ) / N) (((3 * (q.1 + 1) + 2 : ℕ) : ℝ) / N) r =
          ((((⟨3 * (q.1 + 1) + 1, by omega⟩ : Fin N) : ℕ) : ℝ) + r) / N := by
        simp only [lin]; push_cast; ring
      change concatSeq hN seg _ = _
      rw [heq, concatSeq_on_piece hN seg hmatch ⟨3 * (q.1 + 1) + 1, by omega⟩ hr, hseg_MR q]
    hγD := by
      ext y; constructor
      · rintro ⟨hyγ, z, hz, rfl⟩
        rw [hγim] at hyγ; obtain ⟨i, r, hr, hre⟩ := mem_iUnion.mp hyγ
        have hz_in : (bcM q).g z ∈ (bcM q).box := ⟨z, hz, rfl⟩
        rcases hseg_box_or_Ω i with ⟨-, -, hs⟩ | ⟨-, -, hs⟩ | ⟨q', hiq, hir, hs⟩ | ⟨j, hiq, hiseg, hs⟩
        · exact (Set.disjoint_left.mp (hLb ▸ hL_disj_M q) (hs ⟨r, hr, hre⟩) hz_in).elim
        · exact (Set.disjoint_left.mp (hRb ▸ hR_disj_M q) (hs ⟨r, hr, hre⟩) hz_in).elim
        · have hqq' : q' = q := by
            by_contra hne; exact Set.disjoint_left.mp (hM_disj q' q hne) (hs ⟨r, hr, hre⟩) hz_in
          subst q'
          rcases (show i.1 = 3 * (q.1 + 1) ∨ i.1 = 3 * (q.1 + 1) + 1 by omega) with hiL | hiR
          · have hi' : i = ⟨3 * (q.1 + 1), by omega⟩ := Fin.ext hiL
            refine ⟨((3 * (q.1 + 1) : ℕ) + r) / N, ⟨div_le_div_of_nonneg_right (by linarith only [hr.1]) hNpos.le,
              div_le_div_of_nonneg_right (by push_cast; linarith only [hr.2]) hNpos.le⟩, ?_⟩
            have h1 := concatSeq_on_piece hN seg hmatch ⟨3 * (q.1 + 1), by omega⟩ hr
            rw [← hi', hre] at h1; rwa [hiL] at h1
          · have hi' : i = ⟨3 * (q.1 + 1) + 1, by omega⟩ := Fin.ext hiR
            refine ⟨((3 * (q.1 + 1) + 1 : ℕ) + r) / N, ⟨div_le_div_of_nonneg_right (by push_cast; linarith only [hr.1]) hNpos.le,
              div_le_div_of_nonneg_right (by push_cast; linarith only [hr.2]) hNpos.le⟩, ?_⟩
            have h1 := concatSeq_on_piece hN seg hmatch ⟨3 * (q.1 + 1) + 1, by omega⟩ hr
            rw [← hi', hre] at h1; rwa [hiR] at h1
        · by_cases hj1 : j.1 = q.1
          · have hjeq : j = q.castSucc := Fin.ext hj1; rw [hiseg, hjeq] at hre
            by_cases hr1 : r = 1
            · subst hr1
              refine ⟨((3 * (q.1 + 1) : ℕ) : ℝ) / N, ⟨le_rfl, div_le_div_of_nonneg_right (by push_cast; linarith) hNpos.le⟩, ?_⟩
              have h1 := concatSeq_on_piece hN seg hmatch ⟨3 * (q.1 + 1), by omega⟩ ⟨le_rfl, zero_le_one⟩
              rw [hseg_ML q] at h1
              have harg : ((((⟨3 * (q.1 + 1), by omega⟩ : Fin N) : ℕ) : ℝ) + 0) / N = ((3 * (q.1 + 1) : ℕ) : ℝ) / N := by push_cast; ring
              rw [harg] at h1; change concatSeq hN seg _ = _; rw [h1]; simpa [(hβM q).1] using hre
            · exact (Set.disjoint_left.mp (hdM q).1 ⟨r, ⟨hr.1, lt_of_le_of_ne hr.2 hr1⟩, rfl⟩ (hre ▸ hz_in)).elim
          · by_cases hj2 : j.1 = q.1 + 1
            · have hjeq : j = q.succ := Fin.ext hj2; rw [hiseg, hjeq] at hre
              by_cases hr0 : r = 0
              · subst hr0
                refine ⟨((3 * (q.1 + 1) + 2 : ℕ) : ℝ) / N, ⟨div_le_div_of_nonneg_right (by push_cast; linarith) hNpos.le, le_rfl⟩, ?_⟩
                have h1 := concatSeq_on_piece hN seg hmatch ⟨3 * (q.1 + 1) + 1, by omega⟩ ⟨zero_le_one, le_rfl⟩
                rw [hseg_MR q] at h1
                have hnum : ((((⟨3 * (q.1 + 1) + 1, by omega⟩ : Fin N) : ℕ) : ℝ) + 1) / N = ((3 * (q.1 + 1) + 2 : ℕ) : ℝ) / N := by push_cast; ring
                rw [hnum] at h1; change concatSeq hN seg _ = _; rw [h1]; simpa [(hβM q).2] using hre
              · exact (Set.disjoint_left.mp (hdM q).2 ⟨r, ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), hr.2⟩, rfl⟩ (hre ▸ hz_in)).elim
            · exact (Set.disjoint_left.mp (hM_disj_Ω q j hj1 hj2) hz_in (hs ⟨r, hr, hre⟩)).elim
      · rintro ⟨x, hx, rfl⟩
        have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨(by positivity : (0 : ℝ) ≤ ((3 * (q.1 + 1) : ℕ) : ℝ) / N).trans hx.1,
          hx.2.trans ((div_lt_one hNpos).mpr (by exact_mod_cast (show 3 * (q.1 + 1) + 2 < N by omega))).le⟩
        refine ⟨⟨x, hx01, rfl⟩, ?_⟩
        by_cases hle : x ≤ ((3 * (q.1 + 1) + 1 : ℕ) : ℝ) / N
        · let r := (N : ℝ) * x - ((3 * (q.1 + 1) : ℕ) : ℝ)
          have hr : r ∈ Icc (0 : ℝ) 1 := ⟨by have := (div_le_iff₀' hNpos).mp hx.1; dsimp only [r]; linarith only [this],
            by have := (le_div_iff₀' hNpos).mp hle; dsimp only [r]; push_cast at this ⊢; linarith only [this]⟩
          have hx_eq : x = ((((⟨3 * (q.1 + 1), by omega⟩ : Fin N) : ℕ) : ℝ) + r) / N := by simp only [r]; push_cast; field_simp [hNpos.ne']; ring
          change concatSeq hN seg x ∈ _
          rw [hx_eq, concatSeq_on_piece hN seg hmatch ⟨3 * (q.1 + 1), by omega⟩ hr, hseg_ML q]
          exact ⟨_, hseg_L_mem (bcM q) (hwLM q).1 r hr, rfl⟩
        · let r := (N : ℝ) * x - ((3 * (q.1 + 1) + 1 : ℕ) : ℝ)
          have hr : r ∈ Icc (0 : ℝ) 1 := ⟨by have := (div_lt_iff₀' hNpos).mp (lt_of_not_ge hle); dsimp only [r]; linarith only [this],
            by have := (le_div_iff₀' hNpos).mp hx.2; dsimp only [r]; push_cast at this ⊢; linarith only [this]⟩
          have hx_eq : x = ((((⟨3 * (q.1 + 1) + 1, by omega⟩ : Fin N) : ℕ) : ℝ) + r) / N := by simp only [r]; push_cast; field_simp [hNpos.ne']; ring
          change concatSeq hN seg x ∈ _
          rw [hx_eq, concatSeq_on_piece hN seg hmatch ⟨3 * (q.1 + 1) + 1, by omega⟩ hr, hseg_MR q]
          exact ⟨_, hseg_R_mem (bcM q) (hwRM q).1 r hr, rfl⟩ }
  -- Step 4: Verify cleanliness of `γ_ext` on `[rcL.t_mid, rcR.t_mid]` and assemble `BandArcData`!
  have hrcL_sub : rcL.box ⊆ bcL.box := hLb ▸ image_mono (hhalf_sub bcL')
  have hrcR_sub : rcR.box ⊆ bcR.box := hRb ▸ image_mono (hhalf_sub bcR')
  have hrcM_box : ∀ r : Fin k, (rcM r).box = (bcM r).box := fun _ => rfl
  have hγ_tL : γ_ext rcL.t_mid = bcL.g 0 := rcL.mid_eq.trans hL0
  have hγ_tR : γ_ext rcR.t_mid = bcR.g 0 := rcR.mid_eq.trans hR0
  -- Cleanliness on `[rcL.t_mid, rcR.t_mid] = [1/N, (3k+4)/N]`:
  have hclean_M : ∀ x ∈ Icc rcL.t_mid rcR.t_mid, γ_ext x ∈ M.U → x = rcL.t_mid ∨ x = rcR.t_mid := by
    intro x hx hxM
    have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨rcL.hs0.le.trans (rcL.hst.le.trans hx.1), hx.2.trans (rcR.hte.le.trans rcR.he1.le)⟩
    have hmem : γ_ext x ∈ ⋃ i : Fin N, seg i '' Icc 0 1 := hγim ▸ ⟨x, hx01, rfl⟩
    obtain ⟨i, r, hr, hre⟩ := mem_iUnion.mp hmem
    have hx_eq : x = ((i : ℝ) + r) / N := hγi hx01
      ⟨div_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) i.1, hr.1]) hNpos.le,
       (div_le_one hNpos).mpr (by have hiN : (i : ℝ) + 1 ≤ N := (by exact_mod_cast i.2); linarith only [hiN, hr.2])⟩
      (hre.symm.trans (concatSeq_on_piece hN seg hmatch i hr).symm)
    rcases hseg_box_or_Ω i with ⟨hiq, hir, -⟩ | ⟨hiq, hir, -⟩ | ⟨q, -, -, hs⟩ | ⟨j, -, -, hs⟩
    · rcases (show i.1 = 0 ∨ i.1 = 1 by omega) with hi0 | hi1
      · have hi' : i = ⟨0, by omega⟩ := Fin.ext hi0
        have hr1 : r = 1 := by
          have : (1 : ℝ) / N ≤ ((i : ℝ) + r) / N := hx_eq ▸ hx.1
          have := (div_le_div_iff_of_pos_right hNpos).mp this
          simp only [hi0, Nat.cast_zero, zero_add] at this; linarith only [this, hr.2]
        left; rw [hx_eq, hi0, hr1]; simp [rcL]
      · have hi' : i = ⟨1, by omega⟩ := Fin.ext hi1; rw [hi', hseg_1] at hre; dsimp only at hre
        have h1 : bcL'.g ((r : ℂ) * wR_L) ∈ M.U ∩ bcL'.box := ⟨hre ▸ hxM, _, hseg_R_mem bcL' hwR_L_fr r hr, rfl⟩
        rw [BoxChart.box, bcL'.hA_eq] at h1
        obtain ⟨w, hw, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hw
        have hwR : w ∈ bcL'.R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith only [bcL'.ha], bcL'.ha.le⟩, hw.2⟩
        have hre0 := congrArg Complex.re (bcL'.hgi (hseg_R_mem bcL' hwR_L_fr r hr) hwR hfe.symm)
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mem_singleton_iff.mp hw.1] at hre0
        have hr0 : r = 0 := by nlinarith only [hre0, hwR_L_pos]
        left; rw [hx_eq, hi1, hr0]; simp [rcL]
    · rcases (show i.1 = 3 * k + 3 ∨ i.1 = 3 * k + 4 by omega) with hiL | hiR
      · have hi' : i = ⟨3 * k + 3, by omega⟩ := Fin.ext hiL; rw [hi', hseg_RL] at hre; dsimp only at hre
        have h1 : bcR'.g (((1 - r : ℝ) : ℂ) * wL_R) ∈ M.U ∩ bcR'.box := ⟨hre ▸ hxM, _, hseg_L_mem bcR' hwL_R_fr r hr, rfl⟩
        rw [BoxChart.box, bcR'.hA_eq] at h1
        obtain ⟨w, hw, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hw
        have hwR : w ∈ bcR'.R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith only [bcR'.ha], bcR'.ha.le⟩, hw.2⟩
        have hre0 := congrArg Complex.re (bcR'.hgi (hseg_L_mem bcR' hwL_R_fr r hr) hwR hfe.symm)
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mem_singleton_iff.mp hw.1] at hre0
        have hr1 : r = 1 := by nlinarith only [hre0, hwL_R_neg]
        right; rw [hx_eq, hiL, hr1]; dsimp [rcR]; push_cast; ring
      · have hi' : i = ⟨3 * k + 4, by omega⟩ := Fin.ext hiR
        have hr0 : r = 0 := by
          have : ((i : ℝ) + r) / N ≤ (3 * k + 4 : ℝ) / N := hx_eq ▸ hx.2
          have := (div_le_div_iff_of_pos_right hNpos).mp this
          rw [hiR] at this; push_cast at this; linarith only [this, hr.1]
        right; rw [hx_eq, hiR, hr0]; dsimp [rcR]; push_cast; ring
    · exact (Set.disjoint_left.mp (hM_disj_M q) (hs ⟨r, hr, hre⟩) hxM).elim
    · exact (Set.disjoint_left.mp (hΩ_disj_M j) (hs ⟨r, hr, hre⟩) hxM).elim
  have hclean_Q : ∀ x ∈ Icc rcL.t_mid rcR.t_mid, ∀ j : Fin m, γ_ext x ∈ Q j →
      ∃ q : Fin k, j = idxs q ∧ x = (rcM q).t_mid := by
    intro x hx j hxQ
    have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨rcL.hs0.le.trans (rcL.hst.le.trans hx.1), hx.2.trans (rcR.hte.le.trans rcR.he1.le)⟩
    have hmem : γ_ext x ∈ ⋃ i : Fin N, seg i '' Icc 0 1 := hγim ▸ ⟨x, hx01, rfl⟩
    obtain ⟨i, r, hr, hre⟩ := mem_iUnion.mp hmem
    have hx_eq : x = ((i : ℝ) + r) / N := hγi hx01
      ⟨div_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) i.1, hr.1]) hNpos.le,
       (div_le_one hNpos).mpr (by have hiN : (i : ℝ) + 1 ≤ N := (by exact_mod_cast i.2); linarith only [hiN, hr.2])⟩
      (hre.symm.trans (concatSeq_on_piece hN seg hmatch i hr).symm)
    rcases hseg_box_or_Ω i with ⟨-, -, hs⟩ | ⟨-, -, hs⟩ | ⟨q, hiq, hir, hs⟩ | ⟨l, -, -, hs⟩
    · exact (Set.disjoint_left.mp (hLb ▸ hL_disj_Q j) (hs ⟨r, hr, hre⟩) hxQ).elim
    · exact (Set.disjoint_left.mp (hRb ▸ hR_disj_Q j) (hs ⟨r, hr, hre⟩) hxQ).elim
    · have hjq : j = idxs q := by
        by_contra hne; exact Set.disjoint_left.mp (hM_disj_Q q j hne) (hs ⟨r, hr, hre⟩) hxQ
      subst hjq; refine ⟨q, rfl, ?_⟩
      rcases (show i.1 = 3 * (q.1 + 1) ∨ i.1 = 3 * (q.1 + 1) + 1 by omega) with hiL | hiR
      · have hi' : i = ⟨3 * (q.1 + 1), by omega⟩ := Fin.ext hiL; rw [hi', hseg_ML q] at hre; dsimp only at hre
        have h1 : (bcM q).g (((1 - r : ℝ) : ℂ) * wL_M q) ∈ Q (idxs q) ∩ (bcM q).box :=
          ⟨hre ▸ hxQ, _, hseg_L_mem (bcM q) (hwLM q).1 r hr, rfl⟩
        rw [BoxChart.box, (bcM q).hA_eq] at h1
        obtain ⟨w, hw, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hw
        have hwR : w ∈ (bcM q).R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith only [(bcM q).ha], (bcM q).ha.le⟩, hw.2⟩
        have hre0 := congrArg Complex.re ((bcM q).hgi (hseg_L_mem (bcM q) (hwLM q).1 r hr) hwR hfe.symm)
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mem_singleton_iff.mp hw.1] at hre0
        have hr1 : r = 1 := by nlinarith only [hre0, (hwLM q).2]
        rw [hx_eq, hiL, hr1]; dsimp [rcM]; push_cast; ring
      · have hi' : i = ⟨3 * (q.1 + 1) + 1, by omega⟩ := Fin.ext hiR; rw [hi', hseg_MR q] at hre; dsimp only at hre
        have h1 : (bcM q).g ((r : ℂ) * wR_M q) ∈ Q (idxs q) ∩ (bcM q).box :=
          ⟨hre ▸ hxQ, _, hseg_R_mem (bcM q) (hwRM q).1 r hr, rfl⟩
        rw [BoxChart.box, (bcM q).hA_eq] at h1
        obtain ⟨w, hw, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hw
        have hwR : w ∈ (bcM q).R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith only [(bcM q).ha], (bcM q).ha.le⟩, hw.2⟩
        have hre0 := congrArg Complex.re ((bcM q).hgi (hseg_R_mem (bcM q) (hwRM q).1 r hr) hwR hfe.symm)
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mem_singleton_iff.mp hw.1] at hre0
        have hr0 : r = 0 := by nlinarith only [hre0, (hwRM q).2]
        rw [hx_eq, hiR, hr0]; dsimp [rcM]; push_cast; ring
    · exact (Set.disjoint_left.mp (hΩ_disj_Q l j) (hs ⟨r, hr, hre⟩) hxQ).elim
  exact ⟨{
    γ_ext := γ_ext, idxs := idxs, hidxs_inj := hidxs_inj, hidxs_disj := hidxs_disj,
    hγc := hγc, hγi := hγi, hγint := hγint, rcL := rcL, rcR := rcR, rcM := rcM,
    hL_lt_R := div_lt_div_of_pos_right (by linarith [Nat.cast_nonneg (α := ℝ) k]) hNpos,
    hM_order := fun r => ⟨div_lt_div_of_pos_right (by push_cast; linarith only [Nat.cast_nonneg (α := ℝ) r.1]) hNpos,
      div_lt_div_of_pos_right (by have hrk : (r.1 + 1 : ℝ) ≤ k := (by exact_mod_cast r.2); push_cast; linarith only [hrk]) hNpos⟩,
    hM_disj := fun r₁ r₂ hne => by rw [hrcM_box, hrcM_box]; exact hM_disj r₁ r₂ hne,
    hL_disj_R := hL_disj_R.mono hrcL_sub hrcR_sub,
    hL_disj_M := fun r => (hL_disj_M r).mono hrcL_sub (hrcM_box r ▸ subset_rfl),
    hR_disj_M := fun r => (hR_disj_M r).mono hrcR_sub (hrcM_box r ▸ subset_rfl),
    hL_disj_Q := fun j => (hL_disj_Q j).mono_left hrcL_sub,
    hR_disj_Q := fun j => (hR_disj_Q j).mono_left hrcR_sub,
    hM_disj_M := fun r => hrcM_box r ▸ hM_disj_M r,
    hM_disj_Q := fun r j hne => hrcM_box r ▸ hM_disj_Q r j hne,
    hγ_clean_M := hclean_M, hγ_clean_Q := hclean_Q,
    hdiff_comp := by rw [hγ_tL, hγ_tR]; exact hdiff_comp }, rfl⟩

end BuildBandArc

/-! ### Section 3: Components of `M`, RED/BLUE touching lemma, and shortest path in `W_all` -/

section RedBlueAndChain

/-- Index type for components of a `ProperManifold`: `none` is `M.P₀`, `some i` is `M.Os.get i`. -/
abbrev Comp {s t : S} (M : ProperManifold S s t) := Option (Fin M.Os.length)

def compSet {s t : S} (M : ProperManifold S s t) : Comp M → Set S
  | none => M.P₀
  | some i => (M.Os.get i).O

def compInt {s t : S} (M : ProperManifold S s t) (c : Comp M) : Set S :=
  compSet M c \ bd S

def compPure {s t : S} (M : ProperManifold S s t) {m : ℕ} (Q : Fin m → Set S) (c : Comp M) : Set S :=
  compSet M c \ (bd S ∪ ⋃ j : Fin m, Q j)

theorem compSet_subset_U {s t : S} (M : ProperManifold S s t) (c : Comp M) :
    compSet M c ⊆ M.U := by
  cases c with
  | none => exact subset_union_left
  | some i => exact fun x hx => Or.inr (mem_iUnion₂.mpr ⟨M.Os.get i, List.get_mem M.Os i, hx⟩)

theorem isClosed_compSet [T2Space S] {s t : S} (M : ProperManifold S s t) (c : Comp M) :
    IsClosed (compSet M c) := by
  cases c with
  | none => exact M.hP₀l.isCompact.isClosed
  | some i => exact (M.Os.get i).hO.isCompact.isClosed

theorem compSet_pairwise_disj {s t : S} (M : ProperManifold S s t) :
    Pairwise fun c₁ c₂ : Comp M => Disjoint (compSet M c₁) (compSet M c₂) := by
  intro c₁ c₂ hne
  cases c₁ with
  | none =>
    cases c₂ with
    | none => exact (hne rfl).elim
    | some i => exact M.hP₀_disj _ (List.get_mem M.Os i)
  | some i =>
    cases c₂ with
    | none => exact (M.hP₀_disj _ (List.get_mem M.Os i)).symm
    | some j =>
      have hij : i ≠ j := fun h => hne (congrArg some h)
      have hpw := List.pairwise_iff_get.mp M.hOs_disj
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
      · exact hpw i j hlt
      · exact (hpw j i hgt).symm

theorem mem_U_iff_exists_comp {s t : S} (M : ProperManifold S s t) {x : S} :
    x ∈ M.U ↔ ∃ c : Comp M, x ∈ compSet M c := by
  constructor
  · rintro (hP | hO)
    · exact ⟨none, hP⟩
    · obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hO
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
      exact ⟨some i, hxa⟩
  · rintro ⟨c, hc⟩; exact compSet_subset_U M c hc

theorem compInt_nonempty {s t : S} (M : ProperManifold S s t) (c : Comp M) :
    (compInt M c).Nonempty := by
  cases c with
  | none =>
    dsimp only [compInt, compSet]
    refine ⟨M.γ₀ (1 / 2), M.hγ₀im ▸ ⟨1 / 2, by norm_num, rfl⟩, fun hbd => ?_⟩
    have hm : M.γ₀ (1 / 2) ∈ M.P₀ ∩ bd S := ⟨M.hγ₀im ▸ ⟨1 / 2, by norm_num, rfl⟩, hbd⟩
    rw [M.hP₀b] at hm
    rcases hm with hs | ht
    · have := M.hγ₀i (by norm_num) ⟨le_rfl, zero_le_one⟩ (hs.trans M.hγ₀0.symm); norm_num at this
    · have := M.hγ₀i (by norm_num) ⟨zero_le_one, le_rfl⟩ ((mem_singleton_iff.mp ht).trans M.hγ₀1.symm); norm_num at this
  | some i =>
    dsimp only [compInt, compSet]
    let a := M.Os.get i
    exact ⟨a.α 0, a.hαim ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, a.hOint (a.hαim ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)⟩

theorem compInt_isPreconnected {s t : S} (M : ProperManifold S s t) (c : Comp M) :
    IsPreconnected (compInt M c) := by
  cases c with
  | none =>
    have heq : compInt M none = M.γ₀ '' Ioo (0 : ℝ) 1 := by
      dsimp only [compInt, compSet]
      ext y; constructor
      · rintro ⟨hyP, hybd⟩
        obtain ⟨r, hr, rfl⟩ := M.hγ₀im ▸ hyP
        refine ⟨r, ⟨lt_of_le_of_ne hr.1 fun h0 => hybd (by
          rw [← h0, M.hγ₀0]; exact (M.hP₀b ▸ Or.inl rfl : s ∈ M.P₀ ∩ bd S).2),
          lt_of_le_of_ne hr.2 fun h1 => hybd (by
          rw [h1, M.hγ₀1]; exact (M.hP₀b ▸ Or.inr rfl : t ∈ M.P₀ ∩ bd S).2)⟩, rfl⟩
      · rintro ⟨r, hr, rfl⟩
        refine ⟨M.hγ₀im ▸ ⟨r, Ioo_subset_Icc_self hr, rfl⟩, fun hbd => ?_⟩
        have hm : M.γ₀ r ∈ M.P₀ ∩ bd S := ⟨M.hγ₀im ▸ ⟨r, Ioo_subset_Icc_self hr, rfl⟩, hbd⟩
        rw [M.hP₀b] at hm
        rcases hm with hs | ht
        · have := M.hγ₀i (Ioo_subset_Icc_self hr) ⟨le_rfl, zero_le_one⟩ (hs.trans M.hγ₀0.symm); linarith [hr.1]
        · have := M.hγ₀i (Ioo_subset_Icc_self hr) ⟨zero_le_one, le_rfl⟩ ((mem_singleton_iff.mp ht).trans M.hγ₀1.symm); linarith [hr.2]
    rw [heq]; exact isPreconnected_Ioo.image M.γ₀ (M.hγ₀c.mono Ioo_subset_Icc_self)
  | some i =>
    let a := M.Os.get i
    have heq : compInt M (some i) = a.O := by
      dsimp only [compInt, compSet]
      ext y; exact ⟨fun h => h.1, fun h => ⟨h, a.hOint h⟩⟩
    rw [heq, ← a.hαim]; exact isPreconnected_Icc.image a.α a.hαc

theorem exists_box_on_comp (hS : IsSurface S) {s t : S} (M : ProperManifold S s t)
    (c : Comp M) {p : S} (hp : p ∈ compInt M c) {W : Set S}
    (hWo : IsOpen W) (hpW : p ∈ W) (hWint : W ⊆ (bd S)ᶜ) :
    ∃ bc : BoxChart S M.U, bc.g 0 = p ∧ bc.box ⊆ W := by
  have : T2Space S := hS.2.1
  let Z : Set S := ⋃ (c' : Comp M) (_ : c' ≠ c), compSet M c'
  have hZcl : IsClosed Z := isClosed_iUnion_of_finite fun c' =>
    isClosed_iUnion_of_finite fun _ => isClosed_compSet M c'
  have hp_notZ : p ∉ Z := by
    intro h; obtain ⟨c', hne, hpc'⟩ := mem_iUnion₂.mp h
    exact Set.disjoint_left.mp (compSet_pairwise_disj M hne) hpc' hp.1
  let W' := W ∩ Zᶜ
  have hW'o : IsOpen W' := hWo.inter hZcl.isOpen_compl
  have hbox_c : ∃ bc : BoxChart S (compSet M c), bc.g 0 = p ∧ bc.box ⊆ W' := by
    cases c with
    | none => exact exists_box_on_iArc hS M.hP₀b M.hP₀l hp.1 hp.2 hW'o ⟨hpW, hp_notZ⟩ (inter_subset_left.trans hWint)
    | some i => exact exists_box_on_oArc hS (M.Os.get i) hp.1 hW'o ⟨hpW, hp_notZ⟩ (inter_subset_left.trans hWint)
  obtain ⟨bc, hbc0, hbcW⟩ := hbox_c
  have hMu_eq : M.U ∩ bc.box = compSet M c ∩ bc.box := by
    ext y; constructor
    · rintro ⟨hyM, hyb⟩
      obtain ⟨c', hyc'⟩ := (mem_U_iff_exists_comp M).mp hyM
      by_cases hcc : c' = c
      · exact ⟨hcc ▸ hyc', hyb⟩
      · exact ((hbcW hyb).2 (mem_iUnion₂.mpr ⟨c', hcc, hyc'⟩)).elim
    · rintro ⟨hyc, hyb⟩; exact ⟨compSet_subset_U M c hyc, hyb⟩
  let bc' : BoxChart S M.U :=
    { g := bc.g, a := bc.a, b := bc.b, ha := bc.ha, hb := bc.hb,
      hgc := bc.hgc, hgi := bc.hgi, hopen := bc.hopen, hgint := bc.hgint,
      hA_eq := by rw [← BoxChart.box, hMu_eq, BoxChart.box, bc.hA_eq] }
  exact ⟨bc', hbc0, hbcW.trans inter_subset_left⟩

/-- If `y ∈ M.U ∩ Q j` (`j ∈ A`) lies in `closure Ω` for a component `Ω` of `W \ X_A`,
then `Ω` touches `compPure M Q c` where `y ∈ compInt M c`. -/
private theorem touches_of_mem_inter_closure (hS : IsSurface S) {s t : S}
    (M : ProperManifold S s t) {m : ℕ} {Q : Fin m → Set S}
    (hQclosed : ∀ j, IsClosed (Q j)) (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    {A : Finset (Fin m)} (hA : ∀ j ∈ A, IsSimpleCrossing M.U (Q j))
    {W : Set S} (hW_comp : ∃ x₀ ∈ (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i,
      W = connectedComponentIn ((bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i) x₀)
    {Ω : Set S} (hΩ_comp : ∃ y₀ ∈ W \ (M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j),
      Ω = connectedComponentIn (W \ (M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j)) y₀)
    {j : Fin m} (hjA : j ∈ A) {y : S} (hyM : y ∈ M.U) (hyQ : y ∈ Q j) (hyW : y ∈ W)
    (hy_cl : y ∈ closure Ω) :
    ∃ c : Comp M, y ∈ compInt M c ∧ (compPure M Q c ∩ closure Ω).Nonempty := by
  have : T2Space S := hS.2.1
  let W_all := (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i
  let X_A := M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j
  obtain ⟨c, hyc⟩ := (mem_U_iff_exists_comp M).mp hyM
  obtain ⟨x₀, hx₀, rfl⟩ := hW_comp
  obtain ⟨y₀, hy₀, rfl⟩ := hΩ_comp
  have hyint : y ∈ (bd S)ᶜ := (connectedComponentIn_subset W_all x₀ hyW).1
  obtain ⟨g, ε, hε, hgc, hgi, _, hgint, hg0, hMbox, hQbox⟩ := hA j hjA y ⟨hyM, hyQ⟩
  -- Shrink `ε` so `box` avoids `⋃_{k ≠ j} Q k` and `⋃_{c' ≠ c} compSet M c'`:
  let Z : Set S := (⋃ (k : Fin m) (_ : k ≠ j), Q k) ∪ (⋃ (c' : Comp M) (_ : c' ≠ c), compSet M c')
  have hZcl : IsClosed Z :=
    (isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hQclosed k).union
      (isClosed_iUnion_of_finite fun c' => isClosed_iUnion_of_finite fun _ => isClosed_compSet M c')
  have hy_notZ : y ∉ Z := by
    rintro (h1 | h2)
    · obtain ⟨k, hkj, hyk⟩ := mem_iUnion₂.mp h1; exact Set.disjoint_left.mp (hQdisj hkj) hyk hyQ
    · obtain ⟨c', hcc, hyc'⟩ := mem_iUnion₂.mp h2; exact Set.disjoint_left.mp (compSet_pairwise_disj M hcc) hyc' hyc
  have h0sq : (0 : ℂ) ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by simp [hε.le], by simp [hε.le]⟩
  have hpre : g ⁻¹' Zᶜ ∈ 𝓝[Icc (-ε) ε ×ℂ Icc (-ε) ε] (0 : ℂ) := hgc.continuousWithinAt h0sq (hZcl.isOpen_compl.mem_nhds (hg0.symm ▸ hy_notZ))
  rw [Metric.mem_nhdsWithin_iff] at hpre
  obtain ⟨r₁, hr₁, hr₁sub⟩ := hpre
  let ε' : ℝ := min ε (r₁ / 4)
  have hε' : 0 < ε' := lt_min hε (div_pos hr₁ (by norm_num))
  have hsub_sq : Icc (-ε') ε' ×ℂ Icc (-ε') ε' ⊆ Icc (-ε) ε ×ℂ Icc (-ε) ε := fun w hw => by
    rw [Complex.mem_reProdIm] at hw ⊢
    exact ⟨⟨by linarith [hw.1.1, min_le_left ε (r₁ / 4)], by linarith [hw.1.2, min_le_left ε (r₁ / 4)]⟩,
      ⟨by linarith [hw.2.1, min_le_left ε (r₁ / 4)], by linarith [hw.2.2, min_le_left ε (r₁ / 4)]⟩⟩
  have hbox_notZ : ∀ w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε', g w ∉ Z := fun w hw => by
    refine hr₁sub ⟨?_, hsub_sq hw⟩
    rw [mem_ball_zero_iff]; rw [Complex.mem_reProdIm] at hw
    have hnorm : ‖w‖ ≤ |w.re| + |w.im| := by
      calc ‖w‖ = ‖(w.re : ℂ) + (w.im : ℂ) * I‖ := by congr 1; apply Complex.ext <;> simp
        _ ≤ ‖(w.re : ℂ)‖ + ‖(w.im : ℂ) * I‖ := norm_add_le _ _
        _ = |w.re| + |w.im| := by rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h4 : ε' ≤ r₁ / 4 := min_le_right _ _
    linarith [abs_le.mpr hw.1, abs_le.mpr hw.2]
  have hbox_in_W : g '' (Icc (-ε') ε' ×ℂ Icc (-ε') ε') ⊆ connectedComponentIn W_all x₀ := by
    rw [connectedComponentIn_eq hyW]
    refine ((isPreconnected_reProdIm isPreconnected_Icc isPreconnected_Icc).image g (hgc.mono hsub_sq)).subset_connectedComponentIn
      ⟨0, Complex.mem_reProdIm.mpr ⟨by simp [hε'.le], by simp [hε'.le]⟩, hg0⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨hgint ⟨w, hsub_sq hw, rfl⟩, fun h => ?_⟩
    obtain ⟨i, hiA, hwi⟩ := mem_iUnion₂.mp h
    have hij : i ≠ j := fun h => hiA (h ▸ hjA)
    exact hbox_notZ w hw (Or.inl (mem_iUnion₂.mpr ⟨i, hij, hwi⟩))
  have hopen_V : IsOpen (g '' (Ioo (-ε') ε' ×ℂ Ioo (-ε') ε')) := by
    have hsub_oo : Ioo (-ε') ε' ×ℂ Ioo (-ε') ε' ⊆ Icc (-ε') ε' ×ℂ Icc (-ε') ε' := fun _ h =>
      Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).2⟩
    exact isOpen_image_of_manifold (isOpen_Ioo.reProdIm isOpen_Ioo)
      (hgc.mono (hsub_oo.trans hsub_sq)) (hgi.mono (hsub_oo.trans hsub_sq)) (fun _ _ => hS.2.2 _)
  have hyV : y ∈ g '' (Ioo (-ε') ε' ×ℂ Ioo (-ε') ε') :=
    ⟨0, Complex.mem_reProdIm.mpr ⟨by simp [hε'], by simp [hε']⟩, hg0⟩
  obtain ⟨z, ⟨w, hw, rfl⟩, hzΩ⟩ := mem_closure_iff.mp hy_cl _ hopen_V hyV
  have hw_sq : w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' :=
    Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩
  have hnotXA : g w ∉ X_A := (connectedComponentIn_subset (connectedComponentIn W_all x₀ \ X_A) y₀ hzΩ).2
  have hwre_ne : w.re ≠ 0 := fun h0 => hnotXA (Or.inr (mem_iUnion₂.mpr ⟨j, hjA,
    (show g w ∈ Q j ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
      rw [hQbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨h0, (Complex.mem_reProdIm.mp (hsub_sq hw_sq)).2⟩, rfl⟩).1⟩))
  have hwim_ne : w.im ≠ 0 := fun h0 => hnotXA (Or.inl
    (show g w ∈ M.U ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
      rw [hMbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp (hsub_sq hw_sq)).1, h0⟩, rfl⟩).1)
  -- The quadrant containing `w` is a connected subset of `W \ X_A`, hence `⊆ Ω`, and its closure hits `g (σ₁ * ε'/2)`!
  let I_re : Set ℝ := if 0 < w.re then Ioo 0 ε' else Ioo (-ε') 0
  let I_im : Set ℝ := if 0 < w.im then Ioo 0 ε' else Ioo (-ε') 0
  let Quad : Set ℂ := I_re ×ℂ I_im
  have hwQ : w ∈ Quad := by
    rw [Complex.mem_reProdIm] at hw ⊢
    constructor
    · dsimp [I_re]; split_ifs with h; exact ⟨h, hw.1.2⟩; exact ⟨hw.1.1, lt_of_le_of_ne (le_of_not_gt h) hwre_ne⟩
    · dsimp [I_im]; split_ifs with h; exact ⟨h, hw.2.2⟩; exact ⟨hw.2.1, lt_of_le_of_ne (le_of_not_gt h) hwim_ne⟩
  have hQuad_sub : Quad ⊆ Icc (-ε') ε' ×ℂ Icc (-ε') ε' := fun u hu => by
    rw [Complex.mem_reProdIm] at hu ⊢
    constructor
    · dsimp [I_re] at hu; split_ifs at hu; exact ⟨by linarith [hu.1.1], hu.1.2.le⟩; exact ⟨hu.1.1.le, by linarith [hu.1.2]⟩
    · dsimp [I_im] at hu; split_ifs at hu; exact ⟨by linarith [hu.2.1], hu.2.2.le⟩; exact ⟨hu.2.1.le, by linarith [hu.2.2]⟩
  have hQuad_conn : IsPreconnected Quad := by
    refine isPreconnected_reProdIm ?_ ?_
    · dsimp [I_re]; split_ifs <;> exact isPreconnected_Ioo
    · dsimp [I_im]; split_ifs <;> exact isPreconnected_Ioo
  have hQuad_in_Ω : g '' Quad ⊆ connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀ := by
    rw [connectedComponentIn_eq hzΩ]
    refine (hQuad_conn.image g (hgc.mono (hQuad_sub.trans hsub_sq))).subset_connectedComponentIn ⟨w, hwQ, rfl⟩ ?_
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨hbox_in_W ⟨u, hQuad_sub hu, rfl⟩, ?_⟩
    have hu_re_ne : u.re ≠ 0 := by
      have h := (Complex.mem_reProdIm.mp hu).1; dsimp [I_re] at h; split_ifs at h; exact h.1.ne'; exact h.2.ne
    have hu_im_ne : u.im ≠ 0 := by
      have h := (Complex.mem_reProdIm.mp hu).2; dsimp [I_im] at h; split_ifs at h; exact h.1.ne'; exact h.2.ne
    rintro (huM | huQ)
    · have h1 : g u ∈ M.U ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨huM, u, hsub_sq (hQuad_sub hu), rfl⟩
      rw [hMbox] at h1; obtain ⟨u', hu', hfe⟩ := h1; rw [Complex.mem_reProdIm] at hu'
      have hu'sq : u' ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨hu'.1, by rw [mem_singleton_iff.mp hu'.2]; exact ⟨by linarith, hε.le⟩⟩
      have := congrArg Complex.im (hgi (hsub_sq (hQuad_sub hu)) hu'sq hfe.symm)
      exact hu_im_ne (this.trans (mem_singleton_iff.mp hu'.2))
    · obtain ⟨k, -, huk⟩ := mem_iUnion₂.mp huQ
      by_cases hkj : k = j
      · subst hkj
        have h1 : g u ∈ Q k ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨huk, u, hsub_sq (hQuad_sub hu), rfl⟩
        rw [hQbox] at h1; obtain ⟨u', hu', hfe⟩ := h1; rw [Complex.mem_reProdIm] at hu'
        have hu'sq : u' ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hu'.1]; exact ⟨by linarith, hε.le⟩, hu'.2⟩
        have := congrArg Complex.re (hgi (hsub_sq (hQuad_sub hu)) hu'sq hfe.symm)
        exact hu_re_ne (this.trans (mem_singleton_iff.mp hu'.1))
      · exact hbox_notZ u (hQuad_sub hu) (Or.inl (mem_iUnion₂.mpr ⟨k, hkj, huk⟩))
  -- Target pure point `p' := g (σ₁ * ε'/2)`:
  let σ₁ : ℝ := if 0 < w.re then 1 else -1
  let σ₂ : ℝ := if 0 < w.im then 1 else -1
  let p' : S := g ((σ₁ * (ε' / 2) : ℝ) : ℂ)
  have hp'_sq : ((σ₁ * (ε' / 2) : ℝ) : ℂ) ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' := by
    rw [Complex.mem_reProdIm, ofReal_re, ofReal_im]; dsimp [σ₁]
    split_ifs <;> exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hp'_M : p' ∈ M.U := (show p' ∈ M.U ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
    rw [hMbox]; exact ⟨_, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp (hsub_sq hp'_sq)).1, by simp⟩, rfl⟩).1
  have hp'_c : p' ∈ compSet M c := by
    obtain ⟨c', hc'⟩ := (mem_U_iff_exists_comp M).mp hp'_M
    by_cases hcc : c' = c; exact hcc ▸ hc'
    exact (hbox_notZ _ hp'_sq (Or.inr (mem_iUnion₂.mpr ⟨c', hcc, hc'⟩))).elim
  have hp'_pure : p' ∈ compPure M Q c := by
    refine ⟨hp'_c, ?_⟩
    rintro (hbd | hQ)
    · exact hgint ⟨_, hsub_sq hp'_sq, rfl⟩ hbd
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hQ
      by_cases hkj : k = j
      · subst hkj
        have h1 : p' ∈ Q k ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hk, _, hsub_sq hp'_sq, rfl⟩
        rw [hQbox] at h1; obtain ⟨u', hu', hfe⟩ := h1; rw [Complex.mem_reProdIm] at hu'
        have hu'sq : u' ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hu'.1]; exact ⟨by linarith, hε.le⟩, hu'.2⟩
        have hre0 := congrArg Complex.re (hgi (hsub_sq hp'_sq) hu'sq hfe.symm)
        rw [ofReal_re, mem_singleton_iff.mp hu'.1] at hre0
        dsimp [σ₁] at hre0; split_ifs at hre0 <;> linarith
      · exact hbox_notZ _ hp'_sq (Or.inl (mem_iUnion₂.mpr ⟨k, hkj, hk⟩))
  have hp'_cl : p' ∈ closure (connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀) := by
    refine closure_mono hQuad_in_Ω ?_
    let seq : ℕ → ℂ := fun n => ((σ₁ * (ε' / 2) : ℝ) : ℂ) + ((σ₂ * (ε' / ((n : ℝ) + 2)) : ℝ) : ℂ) * I
    have hlim : Filter.Tendsto (fun n => g (seq n)) Filter.atTop (𝓝 p') := by
      refine (hgc.continuousWithinAt (hsub_sq hp'_sq)).tendsto.comp ?_
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Filter.Eventually.of_forall fun n => hsub_sq (hQuad_sub ?_))
      · have h0 : Filter.Tendsto (fun n : ℕ => σ₂ * (ε' / ((n : ℝ) + 2))) Filter.atTop (𝓝 0) := by
          have ht0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) :=
            ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)).congr fun n => by
              simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]; ring
          have h1 : Filter.Tendsto (fun n : ℕ => (σ₂ * ε') * ((1 : ℝ) / ((n : ℝ) + 2))) Filter.atTop (𝓝 ((σ₂ * ε') * 0)) :=
            tendsto_const_nhds.mul ht0
          rw [mul_zero] at h1
          exact h1.congr fun n => by ring
        simpa [seq] using tendsto_const_nhds.add ((Complex.continuous_ofReal.continuousAt.tendsto.comp h0).mul tendsto_const_nhds)
      · rw [Complex.mem_reProdIm]
        have hpos : 0 < ε' / ((n : ℝ) + 2) := by positivity
        have hlt : ε' / ((n : ℝ) + 2) < ε' := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
        simp only [seq, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, zero_add]
        constructor
        · dsimp [I_re, σ₁]; split_ifs <;> constructor <;> linarith
        · dsimp [I_im, σ₂]; split_ifs <;> constructor <;> linarith
    refine mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun n => ⟨seq n, ?_, rfl⟩)
    rw [Complex.mem_reProdIm]
    have hpos : 0 < ε' / ((n : ℝ) + 2) := by positivity
    have hlt : ε' / ((n : ℝ) + 2) < ε' := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
    simp only [seq, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im, zero_add]
    constructor
    · dsimp [I_re, σ₁]; split_ifs <;> constructor <;> linarith
    · dsimp [I_im, σ₂]; split_ifs <;> constructor <;> linarith
  exact ⟨c, ⟨hyc, hyint⟩, p', hp'_pure, hp'_cl⟩

/-- Clopen walk along `Q j` (`j ∈ A`): if `y ∈ Q j \ (bd S ∪ M.U)` lies in `closure Ω` for a
component `Ω` of `W \ X_A`, and `M.U ∩ Q j` is nonempty and finite, then some crossing
`p* ∈ M.U ∩ Q j` lies in `W ∩ closure Ω`. -/
private theorem exists_crossing_in_closure_of_Q (hS : IsSurface S) {s t : S}
    (M : ProperManifold S s t) {m : ℕ} {Q : Fin m → Set S} {uQ vQ : Fin m → S}
    (hQb : ∀ j, Q j ∩ bd S = {uQ j, vQ j})
    (hQl : ∀ j, IsLineWithEnds (Q j) (uQ j) (vQ j))
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    {A : Finset (Fin m)} (hAne : ∀ j ∈ A, (M.U ∩ Q j).Nonempty)
    (hAfin : ∀ j ∈ A, (M.U ∩ Q j).Finite)
    (hQ_disj_st : ∀ j, s ∉ Q j ∧ t ∉ Q j)
    {W : Set S} (hW_comp : ∃ x₀ ∈ (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i,
      W = connectedComponentIn ((bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i) x₀)
    {j : Fin m} (hjA : j ∈ A) {y : S} (hyQ : y ∈ Q j) (hyM : y ∉ M.U) (hyW : y ∈ W) :
    ∃ p : S, p ∈ M.U ∩ Q j ∧ p ∈ W ∧
      ∀ y₀ ∈ W \ (M.U ∪ ⋃ (k : Fin m) (_ : k ∈ A), Q k),
        y ∈ closure (connectedComponentIn (W \ (M.U ∪ ⋃ (k : Fin m) (_ : k ∈ A), Q k)) y₀) →
        p ∈ closure (connectedComponentIn (W \ (M.U ∪ ⋃ (k : Fin m) (_ : k ∈ A), Q k)) y₀) := by
  classical
  have : T2Space S := hS.2.1
  let W_all := (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i
  let X_A := M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j
  obtain ⟨x₀, hx₀, rfl⟩ := hW_comp
  obtain ⟨φ, hφ0, hφ1⟩ := hQl j
  have hQ_cl : ∀ k, IsClosed (Q k) := fun k => (hQl k).isCompact.isClosed
  have hφ_int : ∀ r : unitInterval, r.1 ∈ Ioo (0 : ℝ) 1 → (φ r).1 ∈ (bd S)ᶜ := fun r hr hbd => by
    have hm : (φ r).1 ∈ Q j ∩ bd S := ⟨(φ r).2, hbd⟩
    rw [hQb j] at hm
    rcases hm with hu | hv
    · have h0 : r.1 = 0 := congrArg Subtype.val (φ.injective (Subtype.ext (hu.trans hφ0.symm))); linarith [hr.1]
    · have h1 : r.1 = 1 := congrArg Subtype.val (φ.injective (Subtype.ext ((mem_singleton_iff.mp hv).trans hφ1.symm))); linarith [hr.2]
  have hQint_sub_W : Q j \ bd S ⊆ connectedComponentIn W_all x₀ := by
    rw [connectedComponentIn_eq hyW]
    have hconn : IsPreconnected (Q j \ bd S) := by
      have heq : Q j \ bd S = (fun r : unitInterval => (φ r).1) '' {r : unitInterval | r.1 ∈ Ioo (0 : ℝ) 1} := by
        ext z; constructor
        · rintro ⟨hzQ, hzbd⟩
          let r := φ.symm ⟨z, hzQ⟩
          refine ⟨r, ⟨lt_of_le_of_ne r.2.1 fun h0 => hzbd ?_, lt_of_le_of_ne r.2.2 fun h1 => hzbd ?_⟩,
            congrArg Subtype.val (φ.apply_symm_apply _)⟩
          · have : z = uQ j := by
              have h : (φ (φ.symm ⟨z, hzQ⟩)).1 = z := congrArg Subtype.val (φ.apply_symm_apply ⟨z, hzQ⟩)
              rw [← h, show φ.symm ⟨z, hzQ⟩ = 0 from Subtype.ext h0.symm]; exact hφ0
            exact this ▸ (hQb j ▸ Or.inl rfl : uQ j ∈ Q j ∩ bd S).2
          · have : z = vQ j := by
              have h : (φ (φ.symm ⟨z, hzQ⟩)).1 = z := congrArg Subtype.val (φ.apply_symm_apply ⟨z, hzQ⟩)
              rw [← h, show φ.symm ⟨z, hzQ⟩ = 1 from Subtype.ext h1]; exact hφ1
            exact this ▸ (hQb j ▸ Or.inr rfl : vQ j ∈ Q j ∩ bd S).2
        · rintro ⟨r, hr, rfl⟩; exact ⟨(φ r).2, hφ_int r hr⟩
      rw [heq]
      have hIoo_conn : IsPreconnected {r : unitInterval | r.1 ∈ Ioo (0 : ℝ) 1} := by
        have hsub : {r : unitInterval | r.1 ∈ Ioo (0 : ℝ) 1} =
            (fun x : ℝ => (⟨max 0 (min 1 x), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩ : unitInterval)) '' Ioo 0 1 := by
          ext r; constructor
          · intro hr; refine ⟨r.1, hr, Subtype.ext ?_⟩; dsimp; rw [min_eq_right hr.2.le, max_eq_right hr.1.le]
          · rintro ⟨x, hx, rfl⟩; dsimp; rw [min_eq_right hx.2.le, max_eq_right hx.1.le]; exact hx
        rw [hsub]; exact isPreconnected_Ioo.image _ (by fun_prop)
      exact hIoo_conn.image _ (continuous_subtype_val.comp φ.continuous).continuousOn
    refine hconn.subset_connectedComponentIn ⟨hyQ, (connectedComponentIn_subset W_all x₀ hyW).1⟩ ?_
    rintro z ⟨hzQ, hzbd⟩
    refine ⟨hzbd, fun h => ?_⟩
    obtain ⟨i, hiA, hzi⟩ := mem_iUnion₂.mp h
    exact Set.disjoint_left.mp (hQdisj (show i ≠ j from fun he => hiA (he ▸ hjA))) hzi hzQ
  -- Finite nonempty crossing parameter set `F ⊆ (0, 1)`:
  let Fset : Set ℝ := (fun p : S => if hp : p ∈ Q j then (φ.symm ⟨p, hp⟩).1 else 0) '' (M.U ∩ Q j)
  have hF_fin : Fset.Finite := (hAfin j hjA).image _
  have hF_ne : Fset.Nonempty := (hAne j hjA).image _
  let Ffin : Finset ℝ := hF_fin.toFinset
  have hFfin_ne : Ffin.Nonempty := hF_fin.toFinset_nonempty.mpr hF_ne
  let t₀ : ℝ := (φ.symm ⟨y, hyQ⟩).1
  have ht₀_oo : t₀ ∈ Ioo (0 : ℝ) 1 := by
    have hybd := (connectedComponentIn_subset W_all x₀ hyW).1
    refine ⟨lt_of_le_of_ne (φ.symm ⟨y, hyQ⟩).2.1 fun h0 => hybd ?_,
      lt_of_le_of_ne (φ.symm ⟨y, hyQ⟩).2.2 fun h1 => hybd ?_⟩
    · have : y = uQ j := by
        have h : (φ (φ.symm ⟨y, hyQ⟩)).1 = y := congrArg Subtype.val (φ.apply_symm_apply ⟨y, hyQ⟩)
        rw [← h, show φ.symm ⟨y, hyQ⟩ = 0 from Subtype.ext h0.symm]; exact hφ0
      exact this ▸ (hQb j ▸ Or.inl rfl : uQ j ∈ Q j ∩ bd S).2
    · have : y = vQ j := by
        have h : (φ (φ.symm ⟨y, hyQ⟩)).1 = y := congrArg Subtype.val (φ.apply_symm_apply ⟨y, hyQ⟩)
        rw [← h, show φ.symm ⟨y, hyQ⟩ = 1 from Subtype.ext h1]; exact hφ1
      exact this ▸ (hQb j ▸ Or.inr rfl : vQ j ∈ Q j ∩ bd S).2
  -- Pick `t₁ ∈ Ffin` minimizing `|t - t₀|`:
  obtain ⟨t₁, ht₁F, ht₁min⟩ := Finset.exists_min_image Ffin (fun t => |t - t₀|) hFfin_ne
  obtain ⟨p, ⟨hpM, hpQ⟩, hp_eq⟩ := hF_fin.mem_toFinset.mp ht₁F
  simp only [dite_eq_left hpQ] at hp_eq
  have hp_notbd : p ∈ (bd S)ᶜ := fun hbd => by
    have hm : p ∈ M.U ∩ bd S := ⟨hpM, hbd⟩
    rw [M.U_inter_bd] at hm
    rcases hm with rfl | htp
    · exact (hQ_disj_st j).1 hpQ
    · exact (hQ_disj_st j).2 (mem_singleton_iff.mp htp ▸ hpQ)
  have ht₁_oo : t₁ ∈ Ioo (0 : ℝ) 1 := by
    rw [← hp_eq]
    refine ⟨lt_of_le_of_ne (φ.symm ⟨p, hpQ⟩).2.1 fun h0 => hp_notbd ?_,
      lt_of_le_of_ne (φ.symm ⟨p, hpQ⟩).2.2 fun h1 => hp_notbd ?_⟩
    · have : p = uQ j := by
        have h : (φ (φ.symm ⟨p, hpQ⟩)).1 = p := congrArg Subtype.val (φ.apply_symm_apply ⟨p, hpQ⟩)
        rw [← h, show φ.symm ⟨p, hpQ⟩ = 0 from Subtype.ext h0.symm]; exact hφ0
      exact this ▸ (hQb j ▸ Or.inl rfl : uQ j ∈ Q j ∩ bd S).2
    · have : p = vQ j := by
        have h : (φ (φ.symm ⟨p, hpQ⟩)).1 = p := congrArg Subtype.val (φ.apply_symm_apply ⟨p, hpQ⟩)
        rw [← h, show φ.symm ⟨p, hpQ⟩ = 1 from Subtype.ext h1]; exact hφ1
      exact this ▸ (hQb j ▸ Or.inr rfl : vQ j ∈ Q j ∩ bd S).2
  have ht₀_ne_t₁ : t₀ ≠ t₁ := fun h => by
    have hpy : y = p := by
      have he : φ.symm ⟨y, hyQ⟩ = φ.symm ⟨p, hpQ⟩ := Subtype.ext (h.trans hp_eq.symm)
      exact congrArg Subtype.val (φ.symm.injective he)
    exact hyM (hpy ▸ hpM)
  -- Local openness of `closure Ω` along `Q j \ (bd S ∪ M.U)`:
  let ψ : ℝ → S := fun r => if hr : r ∈ Icc (0 : ℝ) 1 then (φ ⟨r, hr⟩).1 else y
  have hψc : ContinuousOn ψ (Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp φ.continuous).congr fun r => by simp only [Set.domRestrict, ψ, Function.comp, dite_eq_left r.2]
  have hψ_t₀ : ψ t₀ = y := by
    simp only [ψ, dite_eq_left (Ioo_subset_Icc_self ht₀_oo)]
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨y, hyQ⟩)
  have hψ_t₁ : ψ t₁ = p := by
    simp only [ψ, dite_eq_left (Ioo_subset_Icc_self ht₁_oo)]
    have he : (⟨t₁, Ioo_subset_Icc_self ht₁_oo⟩ : unitInterval) = φ.symm ⟨p, hpQ⟩ := Subtype.ext hp_eq.symm
    rw [he]; exact congrArg Subtype.val (φ.apply_symm_apply ⟨p, hpQ⟩)
  refine ⟨p, ⟨hpM, hpQ⟩, hQint_sub_W ⟨hpQ, hp_notbd⟩, fun y₀ hy₀ hy_cl => ?_⟩
  have hopen_step : ∀ r ∈ Ioo (0 : ℝ) 1, ψ r ∉ M.U → ψ r ∈ closure (connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀) →
      ∃ δ > 0, ∀ r' ∈ Ioo (r - δ) (r + δ) ∩ Ioo (0 : ℝ) 1, ψ r' ∈ closure (connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀) := by
    intro r hr hnotM hcl
    have hrQ : ψ r ∈ Q j := by simp only [ψ, dite_eq_left (Ioo_subset_Icc_self hr)]; exact (φ ⟨r, Ioo_subset_Icc_self hr⟩).2
    have hrint : ψ r ∈ (bd S)ᶜ := by simp only [ψ, dite_eq_left (Ioo_subset_Icc_self hr)]; exact hφ_int ⟨r, Ioo_subset_Icc_self hr⟩ hr
    let Z : Set S := M.U ∪ ⋃ (k : Fin m) (_ : k ≠ j), Q k
    have hZcl : IsClosed Z := M.isClosed_U.union
      (isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hQ_cl k)
    have hr_notZ : ψ r ∉ Z := by
      rintro (hM | hQ); exact hnotM hM
      obtain ⟨k, hkj, hrk⟩ := mem_iUnion₂.mp hQ; exact Set.disjoint_left.mp (hQdisj hkj) hrk hrQ
    let W_loc := (bd S)ᶜ \ Z
    obtain ⟨bc, hbc0, hbcW⟩ := exists_box_on_iArc hS (hQb j) (hQl j) hrQ hrint
      ((isClosed_bd S).isOpen_compl.sdiff hZcl) ⟨hrint, hr_notZ⟩ sdiff_subset
    have hbc_in_W : bc.box ⊆ connectedComponentIn W_all x₀ := by
      rw [connectedComponentIn_eq (hQint_sub_W ⟨hrQ, hrint⟩)]
      refine bc.isConnected_box.isPreconnected.subset_connectedComponentIn (hbc0 ▸ bc.center_mem_box) ?_
      intro z hz; refine ⟨(hbcW hz).1, fun h => ?_⟩
      obtain ⟨i, hiA, hzi⟩ := mem_iUnion₂.mp h
      exact (hbcW hz).2 (Or.inr (mem_iUnion₂.mpr ⟨i, fun he => hiA (he ▸ hjA), hzi⟩))
    obtain ⟨z, hzopen, hzΩ⟩ := mem_closure_iff.mp hcl _ bc.hopen (hbc0.symm ▸ bc.center_mem_openBox)
    have hznotQ : z ∉ Q j := fun h => (connectedComponentIn_subset _ y₀ hzΩ).2 (Or.inr (mem_iUnion₂.mpr ⟨j, hjA, h⟩))
    have hzhalf : z ∈ bc.leftHalf ∪ bc.rightHalf := bc.openBox_diff_A ▸ ⟨hzopen, hznotQ⟩
    have hmid_cl : bc.g '' (({0} : Set ℝ) ×ℂ Ioo (-bc.b) bc.b) ⊆
        closure (connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀) := by
      rcases hzhalf with hL | hR
      · have hLsub : bc.leftHalf ⊆ connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀ := by
          rw [connectedComponentIn_eq hzΩ]
          refine bc.isConnected_leftHalf.isPreconnected.subset_connectedComponentIn hL ?_
          intro w hw; refine ⟨hbc_in_W (bc.clLeftHalf_subset_box (bc.leftHalf_subset_clLeft hw)), ?_⟩
          rintro (hM | hQ)
          · exact (hbcW (bc.clLeftHalf_subset_box (bc.leftHalf_subset_clLeft hw))).2 (Or.inl hM)
          · obtain ⟨k, -, hwk⟩ := mem_iUnion₂.mp hQ
            by_cases hkj : k = j
            · subst hkj; exact Set.disjoint_left.mp bc.clLeftHalf_disj_A (bc.leftHalf_subset_clLeft hw) hwk
            · exact (hbcW (bc.clLeftHalf_subset_box (bc.leftHalf_subset_clLeft hw))).2 (Or.inr (mem_iUnion₂.mpr ⟨k, hkj, hwk⟩))
        exact bc.mid_subset_closure_leftHalf.trans (closure_mono hLsub)
      · have hRsub : bc.rightHalf ⊆ connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀ := by
          rw [connectedComponentIn_eq hzΩ]
          refine bc.isConnected_rightHalf.isPreconnected.subset_connectedComponentIn hR ?_
          intro w hw; refine ⟨hbc_in_W (bc.clRightHalf_subset_box (bc.rightHalf_subset_clRight hw)), ?_⟩
          rintro (hM | hQ)
          · exact (hbcW (bc.clRightHalf_subset_box (bc.rightHalf_subset_clRight hw))).2 (Or.inl hM)
          · obtain ⟨k, -, hwk⟩ := mem_iUnion₂.mp hQ
            by_cases hkj : k = j
            · subst hkj; exact Set.disjoint_left.mp bc.clRightHalf_disj_A (bc.rightHalf_subset_clRight hw) hwk
            · exact (hbcW (bc.clRightHalf_subset_box (bc.rightHalf_subset_clRight hw))).2 (Or.inr (mem_iUnion₂.mpr ⟨k, hkj, hwk⟩))
        exact bc.mid_subset_closure_rightHalf.trans (closure_mono hRsub)
    have hpre : ψ ⁻¹' bc.openBox ∈ 𝓝[Icc (0 : ℝ) 1] r := hψc.continuousWithinAt (Ioo_subset_Icc_self hr) (bc.hopen.mem_nhds (hbc0.symm ▸ bc.center_mem_openBox))
    rw [Metric.mem_nhdsWithin_iff] at hpre
    obtain ⟨δ, hδ, hδsub⟩ := hpre
    refine ⟨δ, hδ, fun r' hr' => hmid_cl ?_⟩
    have hmem_open : ψ r' ∈ bc.openBox := hδsub ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; exact ⟨by linarith [hr'.1.1], by linarith [hr'.1.2]⟩, Ioo_subset_Icc_self hr'.2⟩
    have hmem_Q : ψ r' ∈ Q j := by simp only [ψ, dite_eq_left (Ioo_subset_Icc_self hr'.2)]; exact (φ ⟨r', Ioo_subset_Icc_self hr'.2⟩).2
    obtain ⟨z, hz, hze⟩ := hmem_open
    have hz_in : bc.g z ∈ Q j ∩ bc.box := ⟨hze ▸ hmem_Q, z, Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩, rfl⟩
    rw [BoxChart.box, bc.hA_eq] at hz_in
    obtain ⟨w, hw, hfe⟩ := hz_in; rw [Complex.mem_reProdIm] at hw
    have hwR : w ∈ bc.R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith [bc.ha], bc.ha.le⟩, hw.2⟩
    have hzR : z ∈ bc.R := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩
    have hzw := bc.hgi hzR hwR hfe.symm
    exact ⟨z, Complex.mem_reProdIm.mpr ⟨by rw [hzw]; exact hw.1, (Complex.mem_reProdIm.mp hz).2⟩, hze⟩
  -- Walk from `t₀` to `t₁` along the open segment avoiding `M.U` via `sSup`/`sInf`:
  have hwalk_right : ∀ {a b : ℝ}, a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 → a < b →
      (∀ r ∈ Ico a b, ψ r ∉ M.U) →
      ψ a ∈ closure (connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀) →
      ψ b ∈ closure (connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀) := by
    intro a b ha hb hab havoid ha_cl
    let Ω₀ := connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀
    let S_good : Set ℝ := {r ∈ Icc a b | ∀ x ∈ Icc a r, ψ x ∈ closure Ω₀}
    have haS : a ∈ S_good := ⟨⟨le_rfl, hab.le⟩, fun x hx => (le_antisymm hx.2 hx.1) ▸ ha_cl⟩
    have hSbdd : BddAbove S_good := ⟨b, fun _ h => h.1.2⟩
    let c := sSup S_good
    have hac : a ≤ c := le_csSup hSbdd haS
    have hcb : c ≤ b := csSup_le ⟨a, haS⟩ fun _ h => h.1.2
    have hlt_good : ∀ x ∈ Ico a c, ψ x ∈ closure Ω₀ := fun x hx => by
      obtain ⟨r, hrS, hxr⟩ := exists_lt_of_lt_csSup ⟨a, haS⟩ hx.2
      exact hrS.2 x ⟨hx.1, hxr.le⟩
    have hc_cl : ψ c ∈ closure Ω₀ := by
      rcases hac.eq_or_lt with heq | hlt
      · exact heq ▸ ha_cl
      · have hseq : Filter.Tendsto (fun n : ℕ => c - (c - a) / ((n : ℝ) + 2)) Filter.atTop (𝓝 c) := by
          have ht0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) :=
            ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)).congr fun n => by
              simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]; ring
          have h0 : Filter.Tendsto (fun n : ℕ => (c - a) / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
            have h1 := (tendsto_const_nhds (x := c - a)).mul ht0
            rw [mul_zero] at h1; exact h1.congr fun n => by ring
          simpa using tendsto_const_nhds.sub h0
        have hlim : Filter.Tendsto (fun n : ℕ => ψ (c - (c - a) / ((n : ℝ) + 2))) Filter.atTop (𝓝 (ψ c)) :=
          (hψc.continuousWithinAt ⟨ha.1.le.trans hac, hcb.trans hb.2.le⟩).tendsto.comp
            (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq (Filter.Eventually.of_forall fun n => by
              have hpos : 0 < (c - a) / ((n : ℝ) + 2) := by positivity
              have hlt' : (c - a) / ((n : ℝ) + 2) < c - a := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
              exact ⟨by linarith [ha.1], by linarith [hb.2]⟩))
        exact isClosed_closure.mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => hlt_good _ (by
          have hpos : 0 < (c - a) / ((n : ℝ) + 2) := by positivity
          have hlt' : (c - a) / ((n : ℝ) + 2) < c - a := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
          exact ⟨by linarith, by linarith⟩))
    by_cases hceq : c = b
    · rwa [← hceq]
    · exfalso
      have hc_lt : c < b := lt_of_le_of_ne hcb hceq
      obtain ⟨δ, hδ, hδsub⟩ := hopen_step c ⟨ha.1.trans_le hac, hc_lt.trans hb.2⟩ (havoid c ⟨hac, hc_lt⟩) hc_cl
      let c' := min b (c + δ / 2)
      have hc'_gt : c < c' := lt_min hc_lt (by linarith)
      have hc'_S : c' ∈ S_good := ⟨⟨hac.trans hc'_gt.le, min_le_left _ _⟩, fun x hx => by
        rcases lt_or_ge x c with hxc | hcx
        · exact hlt_good x ⟨hx.1, hxc⟩
        · exact hδsub x ⟨⟨by linarith, by linarith [hx.2, min_le_right b (c + δ / 2)]⟩,
            ⟨ha.1.trans_le hx.1, (hx.2.trans (min_le_left _ _)).trans_lt hb.2⟩⟩⟩
      exact not_lt_of_ge (le_csSup hSbdd hc'_S) hc'_gt
  have hwalk_left : ∀ {a b : ℝ}, a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 → a < b →
      (∀ r ∈ Ioc a b, ψ r ∉ M.U) →
      ψ b ∈ closure (connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀) →
      ψ a ∈ closure (connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀) := by
    intro a b ha hb hab havoid hb_cl
    let Ω₀ := connectedComponentIn (connectedComponentIn W_all x₀ \ X_A) y₀
    let S_good : Set ℝ := {r ∈ Icc a b | ∀ x ∈ Icc r b, ψ x ∈ closure Ω₀}
    have hbS : b ∈ S_good := ⟨⟨hab.le, le_rfl⟩, fun x hx => (le_antisymm hx.1 hx.2) ▸ hb_cl⟩
    have hSbdd : BddBelow S_good := ⟨a, fun _ h => h.1.1⟩
    let c := sInf S_good
    have hac : a ≤ c := le_csInf ⟨b, hbS⟩ fun _ h => h.1.1
    have hcb : c ≤ b := csInf_le hSbdd hbS
    have hgt_good : ∀ x ∈ Ioc c b, ψ x ∈ closure Ω₀ := fun x hx => by
      obtain ⟨r, hrS, hrx⟩ := exists_lt_of_csInf_lt ⟨b, hbS⟩ hx.1
      exact hrS.2 x ⟨hrx.le, hx.2⟩
    have hc_cl : ψ c ∈ closure Ω₀ := by
      rcases hcb.eq_or_lt with heq | hlt
      · exact heq.symm ▸ hb_cl
      · have hseq : Filter.Tendsto (fun n : ℕ => c + (b - c) / ((n : ℝ) + 2)) Filter.atTop (𝓝 c) := by
          have ht0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) :=
            ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)).congr fun n => by
              simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]; ring
          have h0 : Filter.Tendsto (fun n : ℕ => (b - c) / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
            have h1 := (tendsto_const_nhds (x := b - c)).mul ht0
            rw [mul_zero] at h1; exact h1.congr fun n => by ring
          simpa using tendsto_const_nhds.add h0
        have hlim : Filter.Tendsto (fun n : ℕ => ψ (c + (b - c) / ((n : ℝ) + 2))) Filter.atTop (𝓝 (ψ c)) :=
          (hψc.continuousWithinAt ⟨ha.1.le.trans hac, hcb.trans hb.2.le⟩).tendsto.comp
            (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hseq (Filter.Eventually.of_forall fun n => by
              have hpos : 0 < (b - c) / ((n : ℝ) + 2) := by positivity
              have hlt' : (b - c) / ((n : ℝ) + 2) < b - c := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
              exact ⟨by linarith [ha.1], by linarith [hb.2]⟩))
        exact isClosed_closure.mem_of_tendsto hlim (Filter.Eventually.of_forall fun n => hgt_good _ (by
          have hpos : 0 < (b - c) / ((n : ℝ) + 2) := by positivity
          have hlt' : (b - c) / ((n : ℝ) + 2) < b - c := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
          exact ⟨by linarith, by linarith⟩))
    by_cases hceq : c = a
    · rwa [← hceq]
    · exfalso
      have ha_lt : a < c := lt_of_le_of_ne hac (Ne.symm hceq)
      obtain ⟨δ, hδ, hδsub⟩ := hopen_step c ⟨ha.1.trans ha_lt, hcb.trans_lt hb.2⟩ (havoid c ⟨ha_lt, hcb⟩) hc_cl
      let c' := max a (c - δ / 2)
      have hc'_lt : c' < c := max_lt ha_lt (by linarith)
      have hc'_S : c' ∈ S_good := ⟨⟨le_max_left _ _, hc'_lt.le.trans hcb⟩, fun x hx => by
        rcases lt_or_ge c x with hcx | hxc
        · exact hgt_good x ⟨hcx, hx.2⟩
        · exact hδsub x ⟨⟨by linarith [hx.1, le_max_right a (c - δ / 2)], by linarith⟩,
            ⟨ha.1.trans_le ((le_max_left a (c - δ / 2)).trans hx.1), hx.2.trans_lt hb.2⟩⟩⟩
      exact not_lt_of_ge (csInf_le hSbdd hc'_S) hc'_lt
  -- Apply `hwalk_right` or `hwalk_left` between `t₀` and `t₁`!
  have hno_hit : ∀ r ∈ Ioo (min t₀ t₁) (max t₀ t₁), ψ r ∉ M.U := fun r hr hrM => by
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨(lt_min ht₀_oo.1 ht₁_oo.1).trans hr.1, hr.2.trans (max_lt ht₀_oo.2 ht₁_oo.2)⟩
    have hrQ : ψ r ∈ Q j := by simp only [ψ, dite_eq_left (Ioo_subset_Icc_self hr01)]; exact (φ ⟨r, Ioo_subset_Icc_self hr01⟩).2
    have hrF : r ∈ Ffin := hF_fin.mem_toFinset.mpr ⟨ψ r, ⟨hrM, hrQ⟩, by
      have hψr : ψ r = (φ ⟨r, Ioo_subset_Icc_self hr01⟩).1 := by simp only [ψ, dite_eq_left (Ioo_subset_Icc_self hr01)]
      dsimp only; rw [dite_eq_left hrQ]
      have hsub : (⟨ψ r, hrQ⟩ : Q j) = φ ⟨r, Ioo_subset_Icc_self hr01⟩ := Subtype.ext hψr
      rw [hsub]; exact congrArg Subtype.val (φ.symm_apply_apply ⟨r, Ioo_subset_Icc_self hr01⟩)⟩
    have hle := ht₁min r hrF
    rcases lt_or_gt_of_ne ht₀_ne_t₁ with hlt | hgt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hr
      rw [abs_of_pos (sub_pos.mpr hlt), abs_of_pos (sub_pos.mpr hr.1)] at hle; linarith [hr.2]
    · rw [min_eq_right hgt.le, max_eq_left hgt.le] at hr
      rw [abs_of_neg (sub_neg.mpr hgt), abs_of_neg (sub_neg.mpr hr.2)] at hle; linarith [hr.1]
  rcases lt_or_gt_of_ne ht₀_ne_t₁ with hlt | hgt
  · rw [← hψ_t₁]; refine hwalk_right ht₀_oo ht₁_oo hlt (fun r hr => ?_) (hψ_t₀.symm ▸ hy_cl)
    rcases hr.1.eq_or_lt with rfl | hgt0; exact hψ_t₀.symm ▸ hyM
    exact hno_hit r (by rw [min_eq_left hlt.le, max_eq_right hlt.le]; exact ⟨hgt0, hr.2⟩)
  · rw [← hψ_t₁]; refine hwalk_left ht₁_oo ht₀_oo hgt (fun r hr => ?_) (hψ_t₀.symm ▸ hy_cl)
    rcases hr.2.eq_or_lt with rfl | hlt0; exact hψ_t₀.symm ▸ hyM
    exact hno_hit r (by rw [min_eq_right hgt.le, max_eq_left hgt.le]; exact ⟨hr.1, hlt0⟩)

/-- **Claim 1 of RED/BLUE lemma (`exists_owner_of_comp`)**:
If a connected component `W` of `W_all` contains at least one component `c₀` of `M`, then EVERY
connected component `Ω` of `W \ X_A` touches some component `c` of `M` in `W` at a pure interior
point `p ∈ compPure M Q c ∩ closure Ω`. -/
private theorem exists_owner_of_comp (hS : IsSurface S) {s t : S}
    (M : ProperManifold S s t) {m : ℕ} {Q : Fin m → Set S} {uQ vQ : Fin m → S}
    (hQb : ∀ j, Q j ∩ bd S = {uQ j, vQ j})
    (hQl : ∀ j, IsLineWithEnds (Q j) (uQ j) (vQ j))
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hQ_disj_st : ∀ j, s ∉ Q j ∧ t ∉ Q j)
    {A : Finset (Fin m)}
    (hA : ∀ j ∈ A, (M.U ∩ Q j).Nonempty ∧ (M.U ∩ Q j).Finite ∧ IsSimpleCrossing M.U (Q j))
    (hB : ∀ i : Fin m, i ∉ A → Disjoint M.U (Q i))
    {W : Set S} (hW_comp : ∃ x₀ ∈ (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i,
      W = connectedComponentIn ((bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i) x₀)
    {c₀ : Comp M} (hc₀W : compInt M c₀ ⊆ W)
    {y₀ : S} (hy₀ : y₀ ∈ W \ (M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j)) :
    ∃ c : Comp M, compInt M c ⊆ W ∧
      (compPure M Q c ∩ closure (connectedComponentIn (W \ (M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j)) y₀)).Nonempty := by
  have : T2Space S := hS.2.1
  let W_all := (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i
  let X_A := M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j
  have hQcl : ∀ k, IsClosed (Q k) := fun k => (hQl k).isCompact.isClosed
  have hWall_open : IsOpen W_all := (isClosed_bd S).isOpen_compl.sdiff
    (isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => hQcl i)
  have hXA_cl : IsClosed X_A := M.isClosed_U.union
    (isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => hQcl j)
  obtain ⟨x₀, hx₀, hWeq⟩ := hW_comp
  have hW_open : IsOpen W := hWeq ▸ isOpen_connectedComponentIn_of_subset_compl_bd hS hWall_open sdiff_subset hx₀
  have hW_int : W ⊆ (bd S)ᶜ := hWeq ▸ (connectedComponentIn_subset W_all x₀).trans sdiff_subset
  have hW_conn : IsPreconnected W := hWeq ▸ isPreconnected_connectedComponentIn
  let Ω := connectedComponentIn (W \ X_A) y₀
  have hΩ_open : IsOpen Ω := isOpen_connectedComponentIn_of_subset_compl_bd hS
    (hW_open.sdiff hXA_cl) (sdiff_subset.trans hW_int) hy₀
  have hΩ_sub : Ω ⊆ W \ X_A := connectedComponentIn_subset _ y₀
  -- Show `(closure Ω \ Ω) ∩ W` is nonempty:
  have hfr_ne : (closure Ω \ Ω ∩ W).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    have hW_cov : W ⊆ Ω ∪ (closure Ω)ᶜ := fun z hz => by
      by_cases h : z ∈ closure Ω
      · left; by_contra hnot; exact Set.eq_empty_iff_forall_notMem.mp hempty z ⟨⟨h, hnot⟩, hz⟩
      · exact Or.inr h
    obtain ⟨w₀, hw₀⟩ := compInt_nonempty M c₀
    have hw₀W : w₀ ∈ W := hc₀W hw₀
    have hw₀_notcl : w₀ ∉ closure Ω := fun hcl =>
      Set.eq_empty_iff_forall_notMem.mp hempty w₀ ⟨⟨hcl, fun h => (hΩ_sub h).2 (Or.inl (compSet_subset_U M c₀ hw₀.1))⟩, hw₀W⟩
    obtain ⟨z, -, hz1, hz2⟩ := hW_conn Ω (closure Ω)ᶜ hΩ_open isClosed_closure.isOpen_compl hW_cov
      ⟨y₀, hy₀.1, mem_connectedComponentIn hy₀⟩ ⟨w₀, hw₀W, hw₀_notcl⟩
    exact hz2 (subset_closure hz1)
  obtain ⟨y, ⟨hy_cl, hy_notΩ⟩, hyW⟩ := hfr_ne
  have hy_XA : y ∈ X_A := by
    by_contra hnot
    have hΩy_open : IsOpen (connectedComponentIn (W \ X_A) y) :=
      isOpen_connectedComponentIn_of_subset_compl_bd hS (hW_open.sdiff hXA_cl) (sdiff_subset.trans hW_int) ⟨hyW, hnot⟩
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hy_cl _ hΩy_open (mem_connectedComponentIn ⟨hyW, hnot⟩)
    have hEq : connectedComponentIn (W \ X_A) y = Ω := by
      rw [connectedComponentIn_eq hz1, ← connectedComponentIn_eq hz2]
    exact hy_notΩ (hEq ▸ mem_connectedComponentIn ⟨hyW, hnot⟩)
  have hcomp_in_W : ∀ (c : Comp M) {p : S}, p ∈ compInt M c → p ∈ W → compInt M c ⊆ W := fun c {p} hpc hpW => by
    rw [hWeq] at hpW ⊢
    rw [connectedComponentIn_eq hpW]
    refine (compInt_isPreconnected M c).subset_connectedComponentIn hpc ?_
    rintro z ⟨hzc, hzbd⟩
    refine ⟨hzbd, fun h => ?_⟩
    obtain ⟨i, hiA, hzi⟩ := mem_iUnion₂.mp h
    exact Set.disjoint_left.mp (hB i hiA) (compSet_subset_U M c hzc) hzi
  -- Split cases on `y ∈ X_A = M.U ∪ ⋃_{j ∈ A} Q j`:
  by_cases hyM : y ∈ M.U
  · by_cases hyQ : ∃ j ∈ A, y ∈ Q j
    · obtain ⟨j, hjA, hyQj⟩ := hyQ
      obtain ⟨c, hyc, hne⟩ := touches_of_mem_inter_closure hS M hQcl hQdisj (fun j hj => (hA j hj).2.2)
        ⟨x₀, hx₀, hWeq⟩ ⟨y₀, hy₀, rfl⟩ hjA hyM hyQj hyW hy_cl
      exact ⟨c, hcomp_in_W c hyc hyW, hne⟩
    · obtain ⟨c, hyc⟩ := (mem_U_iff_exists_comp M).mp hyM
      have hyint : y ∈ (bd S)ᶜ := hW_int hyW
      have hy_pure : y ∈ compPure M Q c := by
        refine ⟨hyc, ?_⟩
        rintro (hbd | hQ); exact hyint hbd
        obtain ⟨k, hyk⟩ := mem_iUnion.mp hQ
        by_cases hkA : k ∈ A
        · exact hyQ ⟨k, hkA, hyk⟩
        · exact Set.disjoint_left.mp (hB k hkA) hyM hyk
      exact ⟨c, hcomp_in_W c ⟨hyc, hyint⟩ hyW, y, hy_pure, hy_cl⟩
  · have hyQ : y ∈ ⋃ (j : Fin m) (_ : j ∈ A), Q j := hy_XA.resolve_left hyM
    obtain ⟨j, hjA, hyQj⟩ := mem_iUnion₂.mp hyQ
    obtain ⟨p, ⟨hpM, hpQj⟩, hpW, hp_all⟩ := exists_crossing_in_closure_of_Q hS M hQb hQl hQdisj
      (fun j hj => (hA j hj).1) (fun j hj => (hA j hj).2.1) hQ_disj_st
      ⟨x₀, hx₀, hWeq⟩ hjA hyQj hyM hyW
    have hp_cl : p ∈ closure Ω := hp_all y₀ hy₀ hy_cl
    obtain ⟨c, hpc, hne⟩ := touches_of_mem_inter_closure hS M hQcl hQdisj (fun j hj => (hA j hj).2.2)
      ⟨x₀, hx₀, hWeq⟩ ⟨y₀, hy₀, rfl⟩ hjA hpM hpQj hpW hp_cl
    exact ⟨c, hcomp_in_W c hpc hpW, hne⟩

/-- Every component `c` of `M` has at least one pure interior point avoiding `bd S ∪ ⋃ Q`. -/
private theorem compPure_nonempty (hS : IsSurface S) {s t : S}
    (M : ProperManifold S s t) {m : ℕ} {Q : Fin m → Set S}
    (hQcl : ∀ j, IsClosed (Q j)) (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    {A : Finset (Fin m)} (hA : ∀ j ∈ A, IsSimpleCrossing M.U (Q j))
    (hB : ∀ i : Fin m, i ∉ A → Disjoint M.U (Q i)) (c : Comp M) :
    (compPure M Q c).Nonempty := by
  have : T2Space S := hS.2.1
  obtain ⟨y, hyc, hybd⟩ := compInt_nonempty M c
  by_cases hQ : ∃ j : Fin m, y ∈ Q j
  · obtain ⟨j, hyQ⟩ := hQ
    have hjA : j ∈ A := by
      by_contra hnot; exact Set.disjoint_left.mp (hB j hnot) (compSet_subset_U M c hyc) hyQ
    obtain ⟨g, ε, hε, hgc, hgi, _, hgint, hg0, hMbox, hQbox⟩ := hA j hjA y ⟨compSet_subset_U M c hyc, hyQ⟩
    let Z : Set S := (⋃ (k : Fin m) (_ : k ≠ j), Q k) ∪ (⋃ (c' : Comp M) (_ : c' ≠ c), compSet M c')
    have hZcl : IsClosed Z :=
      (isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hQcl k).union
        (isClosed_iUnion_of_finite fun c' => isClosed_iUnion_of_finite fun _ => isClosed_compSet M c')
    have hy_notZ : y ∉ Z := by
      rintro (h1 | h2)
      · obtain ⟨k, hkj, hyk⟩ := mem_iUnion₂.mp h1; exact Set.disjoint_left.mp (hQdisj hkj) hyk hyQ
      · obtain ⟨c', hcc, hyc'⟩ := mem_iUnion₂.mp h2; exact Set.disjoint_left.mp (compSet_pairwise_disj M hcc) hyc' hyc
    have h0sq : (0 : ℂ) ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by simp [hε.le], by simp [hε.le]⟩
    have hpre : g ⁻¹' Zᶜ ∈ 𝓝[Icc (-ε) ε ×ℂ Icc (-ε) ε] (0 : ℂ) := hgc.continuousWithinAt h0sq (hZcl.isOpen_compl.mem_nhds (hg0.symm ▸ hy_notZ))
    rw [Metric.mem_nhdsWithin_iff] at hpre
    obtain ⟨r₁, hr₁, hr₁sub⟩ := hpre
    let d : ℝ := min ε (r₁ / 2)
    have hd : 0 < d := lt_min hε (half_pos hr₁)
    have hd_sq : (d : ℂ) ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε :=
      Complex.mem_reProdIm.mpr ⟨by simp; exact ⟨by linarith [min_le_left ε (r₁ / 2)], min_le_left _ _⟩, by simp [hε.le]⟩
    have hd_notZ : g (d : ℂ) ∉ Z := hr₁sub ⟨by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      linarith [min_le_right ε (r₁ / 2)], hd_sq⟩
    have hd_M : g (d : ℂ) ∈ M.U := (show g (d : ℂ) ∈ M.U ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
      rw [hMbox]; exact ⟨(d : ℂ), Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp hd_sq).1, by simp⟩, rfl⟩).1
    have hd_c : g (d : ℂ) ∈ compSet M c := by
      obtain ⟨c', hc'⟩ := (mem_U_iff_exists_comp M).mp hd_M
      by_cases hcc : c' = c; exact hcc ▸ hc'
      exact (hd_notZ (Or.inr (mem_iUnion₂.mpr ⟨c', hcc, hc'⟩))).elim
    refine ⟨g (d : ℂ), hd_c, ?_⟩
    rintro (hbd | hQk)
    · exact hgint ⟨(d : ℂ), hd_sq, rfl⟩ hbd
    · obtain ⟨k, hgk⟩ := mem_iUnion.mp hQk
      by_cases hkj : k = j
      · subst hkj
        have h1 : g (d : ℂ) ∈ Q k ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hgk, (d : ℂ), hd_sq, rfl⟩
        rw [hQbox] at h1; obtain ⟨w, hw, hfe⟩ := h1; rw [Complex.mem_reProdIm] at hw
        have hwsq : w ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith, hε.le⟩, hw.2⟩
        have := congrArg Complex.re (hgi hd_sq hwsq hfe.symm)
        rw [ofReal_re, mem_singleton_iff.mp hw.1] at this; linarith
      · exact hd_notZ (Or.inl (mem_iUnion₂.mpr ⟨k, hkj, hgk⟩))
  · refine ⟨y, hyc, ?_⟩
    rintro (hbd | hQk); exact hybd hbd
    obtain ⟨k, hyk⟩ := mem_iUnion.mp hQk; exact hQ ⟨k, hyk⟩

/-- **Claim 2 of RED/BLUE lemma (`exists_two_comp_touch`)**:
If a connected component `W` of `W_all` contains two distinct components `c₁ ≠ c₂` of `M`,
then some connected component `Ω` of `W \ X_A` touches two distinct components `c_a ≠ c_b` of `M`
at pure interior points `p_a ∈ compPure M Q c_a ∩ closure Ω`, `p_b ∈ compPure M Q c_b ∩ closure Ω`. -/
private theorem exists_two_comp_touch (hS : IsSurface S) {s t : S}
    (M : ProperManifold S s t) {m : ℕ} {Q : Fin m → Set S} {uQ vQ : Fin m → S}
    (hQb : ∀ j, Q j ∩ bd S = {uQ j, vQ j})
    (hQl : ∀ j, IsLineWithEnds (Q j) (uQ j) (vQ j))
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hQ_disj_st : ∀ j, s ∉ Q j ∧ t ∉ Q j)
    {A : Finset (Fin m)}
    (hA : ∀ j ∈ A, (M.U ∩ Q j).Nonempty ∧ (M.U ∩ Q j).Finite ∧ IsSimpleCrossing M.U (Q j))
    (hB : ∀ i : Fin m, i ∉ A → Disjoint M.U (Q i))
    {W : Set S} (hW_comp : ∃ x₀ ∈ (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i,
      W = connectedComponentIn ((bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i) x₀)
    {c₁ c₂ : Comp M} (hc12 : c₁ ≠ c₂) (hc₁W : compInt M c₁ ⊆ W) (hc₂W : compInt M c₂ ⊆ W) :
    ∃ (y₀ : S) (_ : y₀ ∈ W \ (M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j)) (ca cb : Comp M),
      ca ≠ cb ∧
      (compPure M Q ca ∩ closure (connectedComponentIn (W \ (M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j)) y₀)).Nonempty ∧
      (compPure M Q cb ∩ closure (connectedComponentIn (W \ (M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j)) y₀)).Nonempty := by
  have : T2Space S := hS.2.1
  let W_all := (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i
  let X_A := M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j
  have hQcl : ∀ k, IsClosed (Q k) := fun k => (hQl k).isCompact.isClosed
  have hWall_open : IsOpen W_all := (isClosed_bd S).isOpen_compl.sdiff
    (isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => hQcl i)
  have hXA_cl : IsClosed X_A := M.isClosed_U.union
    (isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => hQcl j)
  obtain ⟨x₀, hx₀, hWeq⟩ := hW_comp
  have hW_open : IsOpen W := hWeq ▸ isOpen_connectedComponentIn_of_subset_compl_bd hS hWall_open sdiff_subset hx₀
  have hW_int : W ⊆ (bd S)ᶜ := hWeq ▸ (connectedComponentIn_subset W_all x₀).trans sdiff_subset
  have hW_conn : IsPreconnected W := hWeq ▸ isPreconnected_connectedComponentIn
  by_contra huniq
  -- Every component `Ω` of `W \ X_A` touches a UNIQUE `c : Comp M`!
  have htouch_uniq : ∀ {y₀ : S} (hy₀ : y₀ ∈ W \ X_A) {ca cb : Comp M},
      (compPure M Q ca ∩ closure (connectedComponentIn (W \ X_A) y₀)).Nonempty →
      (compPure M Q cb ∩ closure (connectedComponentIn (W \ X_A) y₀)).Nonempty → ca = cb := by
    intro y₀ hy₀ ca cb ha hb
    by_contra hne; exact huniq ⟨y₀, hy₀, ca, cb, hne, ha, hb⟩
  let RedComp : Set S → Prop := fun Ω => (compPure M Q c₁ ∩ closure Ω).Nonempty
  let BlueComp : Set S → Prop := fun Ω => ∃ c ≠ c₁, (compPure M Q c ∩ closure Ω).Nonempty
  have hRB_or : ∀ y₀ ∈ W \ X_A, RedComp (connectedComponentIn (W \ X_A) y₀) ∨ BlueComp (connectedComponentIn (W \ X_A) y₀) := fun y₀ hy₀ => by
    obtain ⟨c, -, hc⟩ := exists_owner_of_comp hS M hQb hQl hQdisj hQ_disj_st hA hB ⟨x₀, hx₀, hWeq⟩ hc₁W hy₀
    by_cases hcc : c = c₁
    · exact Or.inl (by dsimp only [RedComp]; rw [← hcc]; exact hc)
    · exact Or.inr ⟨c, hcc, hc⟩
  have hRB_not_both : ∀ y₀ ∈ W \ X_A, ¬ (RedComp (connectedComponentIn (W \ X_A) y₀) ∧ BlueComp (connectedComponentIn (W \ X_A) y₀)) := by
    rintro y₀ hy₀ ⟨hR, c, hne, hB'⟩
    exact hne (htouch_uniq hy₀ hB' hR)
  let U_R : Set S := {x ∈ W | ∀ y ∈ W \ X_A, x ∈ closure (connectedComponentIn (W \ X_A) y) → RedComp (connectedComponentIn (W \ X_A) y)}
  let U_B : Set S := {x ∈ W | ∀ y ∈ W \ X_A, x ∈ closure (connectedComponentIn (W \ X_A) y) → BlueComp (connectedComponentIn (W \ X_A) y)}
  -- Key local lemma: every `x ∈ W` has an open nbhd `V ⊆ W` with `(V ⊆ U_R ∨ V ⊆ U_B)` AND `(V ∩ (W \ X_A)).Nonempty`!
  have hlocal : ∀ x ∈ W, (∃ y ∈ W \ X_A, x ∈ closure (connectedComponentIn (W \ X_A) y)) ∧
      ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ (V ⊆ U_R ∨ V ⊆ U_B) := by
    intro x hxW
    -- Helper: if an open `V ⊆ W` has `V \ X_A = ⋃_{r ∈ S} C_r` where each `C_r` is a connected nonempty subset of `W \ X_A`
    -- all touching the SAME component `c` (via `RedComp` if `c = c₁`, `BlueComp` if `c ≠ c₁`), then `V ⊆ U_R` or `V ⊆ U_B`!
    by_cases hxXA : x ∉ X_A
    · let Ω₀ := connectedComponentIn (W \ X_A) x
      have hΩ₀o : IsOpen Ω₀ := isOpen_connectedComponentIn_of_subset_compl_bd hS (hW_open.sdiff hXA_cl) (sdiff_subset.trans hW_int) ⟨hxW, hxXA⟩
      have hxΩ₀ : x ∈ Ω₀ := mem_connectedComponentIn ⟨hxW, hxXA⟩
      refine ⟨⟨x, ⟨hxW, hxXA⟩, subset_closure hxΩ₀⟩, Ω₀, hΩ₀o, hxΩ₀, (connectedComponentIn_subset _ x).trans sdiff_subset, ?_⟩
      rcases hRB_or x ⟨hxW, hxXA⟩ with hR | hB'
      · left; intro z hzΩ₀; refine ⟨(connectedComponentIn_subset _ x hzΩ₀).1, fun y hy hzcl => ?_⟩
        obtain ⟨w, hwΩ₀, hwΩy⟩ := mem_closure_iff.mp hzcl _ hΩ₀o hzΩ₀
        have heq : connectedComponentIn (W \ X_A) y = Ω₀ := by rw [connectedComponentIn_eq hwΩy, ← connectedComponentIn_eq hwΩ₀]
        rwa [heq]
      · right; intro z hzΩ₀; refine ⟨(connectedComponentIn_subset _ x hzΩ₀).1, fun y hy hzcl => ?_⟩
        obtain ⟨w, hwΩ₀, hwΩy⟩ := mem_closure_iff.mp hzcl _ hΩ₀o hzΩ₀
        have heq : connectedComponentIn (W \ X_A) y = Ω₀ := by rw [connectedComponentIn_eq hwΩy, ← connectedComponentIn_eq hwΩ₀]
        rwa [heq]
    · push Not at hxXA
      by_cases hxM : x ∈ M.U
      · by_cases hxQ : ∃ j ∈ A, x ∈ Q j
        · -- Case C: `x ∈ M.U ∩ Q j` (`j ∈ A`)!
          obtain ⟨j, hjA, hxQj⟩ := hxQ
          obtain ⟨c, hxc⟩ := (mem_U_iff_exists_comp M).mp hxM
          obtain ⟨g, ε, hε, hgc, hgi, _, hgint, hg0, hMbox, hQbox⟩ := (hA j hjA).2.2 x ⟨hxM, hxQj⟩
          let Z : Set S := (⋃ (k : Fin m) (_ : k ≠ j), Q k) ∪ (⋃ (c' : Comp M) (_ : c' ≠ c), compSet M c')
          have hZcl : IsClosed Z :=
            (isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hQcl k).union
              (isClosed_iUnion_of_finite fun c' => isClosed_iUnion_of_finite fun _ => isClosed_compSet M c')
          have hx_notZ : x ∉ Z := by
            rintro (h1 | h2)
            · obtain ⟨k, hkj, hxk⟩ := mem_iUnion₂.mp h1; exact Set.disjoint_left.mp (hQdisj hkj) hxk hxQj
            · obtain ⟨c', hcc, hxc'⟩ := mem_iUnion₂.mp h2; exact Set.disjoint_left.mp (compSet_pairwise_disj M hcc) hxc' hxc
          have h0sq : (0 : ℂ) ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by simp [hε.le], by simp [hε.le]⟩
          have hpre : g ⁻¹' (W ∩ Zᶜ) ∈ 𝓝[Icc (-ε) ε ×ℂ Icc (-ε) ε] (0 : ℂ) := hgc.continuousWithinAt h0sq ((hW_open.inter hZcl.isOpen_compl).mem_nhds (hg0.symm ▸ ⟨hxW, hx_notZ⟩))
          rw [Metric.mem_nhdsWithin_iff] at hpre
          obtain ⟨r₁, hr₁, hr₁sub⟩ := hpre
          let ε' : ℝ := min ε (r₁ / 4)
          have hε' : 0 < ε' := lt_min hε (div_pos hr₁ (by norm_num))
          have hsub_sq : Icc (-ε') ε' ×ℂ Icc (-ε') ε' ⊆ Icc (-ε) ε ×ℂ Icc (-ε) ε := fun w hw => by
            rw [Complex.mem_reProdIm] at hw ⊢
            exact ⟨⟨by linarith [hw.1.1, min_le_left ε (r₁ / 4)], by linarith [hw.1.2, min_le_left ε (r₁ / 4)]⟩,
              ⟨by linarith [hw.2.1, min_le_left ε (r₁ / 4)], by linarith [hw.2.2, min_le_left ε (r₁ / 4)]⟩⟩
          have hbox_WZ : ∀ w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε', g w ∈ W ∧ g w ∉ Z := fun w hw => by
            refine hr₁sub ⟨?_, hsub_sq hw⟩
            rw [mem_ball_zero_iff]; rw [Complex.mem_reProdIm] at hw
            have hnorm : ‖w‖ ≤ |w.re| + |w.im| := by
              calc ‖w‖ = ‖(w.re : ℂ) + (w.im : ℂ) * I‖ := by congr 1; apply Complex.ext <;> simp
                _ ≤ ‖(w.re : ℂ)‖ + ‖(w.im : ℂ) * I‖ := norm_add_le _ _
                _ = |w.re| + |w.im| := by rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
            have h4 : ε' ≤ r₁ / 4 := min_le_right _ _
            linarith [abs_le.mpr hw.1, abs_le.mpr hw.2]
          let V : Set S := g '' (Ioo (-ε') ε' ×ℂ Ioo (-ε') ε')
          have hVo : IsOpen V := by
            have hsub_oo : Ioo (-ε') ε' ×ℂ Ioo (-ε') ε' ⊆ Icc (-ε') ε' ×ℂ Icc (-ε') ε' := fun _ h =>
              Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp h).2⟩
            exact isOpen_image_of_manifold (isOpen_Ioo.reProdIm isOpen_Ioo)
              (hgc.mono (hsub_oo.trans hsub_sq)) (hgi.mono (hsub_oo.trans hsub_sq)) (fun _ _ => hS.2.2 _)
          have hxV : x ∈ V := ⟨0, Complex.mem_reProdIm.mpr ⟨by simp [hε'], by simp [hε']⟩, hg0⟩
          have hVW : V ⊆ W := by
            rintro _ ⟨w, hw, rfl⟩
            exact (hbox_WZ w (Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩)).1
          -- Every point `g w ∈ V \ X_A` lies in a quadrant whose closure contains `x = g 0`!
          have hquad_cl : ∀ w ∈ Ioo (-ε') ε' ×ℂ Ioo (-ε') ε', g w ∉ X_A →
              x ∈ closure (connectedComponentIn (W \ X_A) (g w)) := by
            intro w hw hnotXA
            have hw_sq : w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' :=
              Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw).2⟩
            have hseg_in : ∀ t ∈ Ioc (0 : ℝ) 1, g ((t : ℂ) * w) ∈ W \ X_A := fun t ht => by
              have htw_sq : (t : ℂ) * w ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' := by
                rw [Complex.mem_reProdIm] at hw_sq ⊢
                simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
                exact ⟨⟨by nlinarith [hw_sq.1.1, ht.1, ht.2, hε'], by nlinarith [hw_sq.1.2, ht.1, ht.2, hε']⟩,
                  ⟨by nlinarith [hw_sq.2.1, ht.1, ht.2, hε'], by nlinarith [hw_sq.2.2, ht.1, ht.2, hε']⟩⟩
              refine ⟨(hbox_WZ _ htw_sq).1, ?_⟩
              have hwre_ne : w.re ≠ 0 := fun h0 => hnotXA (Or.inr (mem_iUnion₂.mpr ⟨j, hjA,
                (show g w ∈ Q j ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
                  rw [hQbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨h0, (Complex.mem_reProdIm.mp (hsub_sq hw_sq)).2⟩, rfl⟩).1⟩))
              have hwim_ne : w.im ≠ 0 := fun h0 => hnotXA (Or.inl
                (show g w ∈ M.U ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) by
                  rw [hMbox]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨(Complex.mem_reProdIm.mp (hsub_sq hw_sq)).1, h0⟩, rfl⟩).1)
              rintro (hM | hQ)
              · have h1 : g ((t : ℂ) * w) ∈ M.U ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hM, _, hsub_sq htw_sq, rfl⟩
                rw [hMbox] at h1; obtain ⟨u', hu', hfe⟩ := h1; rw [Complex.mem_reProdIm] at hu'
                have hu'sq : u' ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨hu'.1, by rw [mem_singleton_iff.mp hu'.2]; exact ⟨by linarith, hε.le⟩⟩
                have := congrArg Complex.im (hgi (hsub_sq htw_sq) hu'sq hfe.symm)
                simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, mem_singleton_iff.mp hu'.2] at this
                exact mul_ne_zero ht.1.ne' hwim_ne this
              · obtain ⟨k, -, hk⟩ := mem_iUnion₂.mp hQ
                by_cases hkj : k = j
                · subst hkj
                  have h1 : g ((t : ℂ) * w) ∈ Q k ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hk, _, hsub_sq htw_sq, rfl⟩
                  rw [hQbox] at h1; obtain ⟨u', hu', hfe⟩ := h1; rw [Complex.mem_reProdIm] at hu'
                  have hu'sq : u' ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hu'.1]; exact ⟨by linarith, hε.le⟩, hu'.2⟩
                  have := congrArg Complex.re (hgi (hsub_sq htw_sq) hu'sq hfe.symm)
                  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mem_singleton_iff.mp hu'.1] at this
                  exact mul_ne_zero ht.1.ne' hwre_ne this
                · exact (hbox_WZ _ htw_sq).2 (Or.inl (mem_iUnion₂.mpr ⟨k, hkj, hk⟩))
            have hseg_sub : (fun t : ℝ => g ((t : ℂ) * w)) '' Ioc 0 1 ⊆ connectedComponentIn (W \ X_A) (g w) := by
              refine (isPreconnected_Ioc.image _ (hgc.comp (by fun_prop) fun t ht => hsub_sq (by
                rw [Complex.mem_reProdIm] at hw_sq ⊢
                simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
                exact ⟨⟨by nlinarith [hw_sq.1.1, ht.1, ht.2, hε'], by nlinarith [hw_sq.1.2, ht.1, ht.2, hε']⟩,
                  ⟨by nlinarith [hw_sq.2.1, ht.1, ht.2, hε'], by nlinarith [hw_sq.2.2, ht.1, ht.2, hε']⟩⟩))).subset_connectedComponentIn
                ⟨1, ⟨zero_lt_one, le_rfl⟩, by simp⟩ (by rintro _ ⟨t, ht, rfl⟩; exact hseg_in t ht)
            refine closure_mono hseg_sub ?_
            have hlim : Filter.Tendsto (fun n : ℕ => g (((1 / ((n : ℝ) + 2) : ℝ) : ℂ) * w)) Filter.atTop (𝓝 x) := by
              rw [← hg0]
              refine (hgc.continuousWithinAt h0sq).tendsto.comp ?_
              refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (Filter.Eventually.of_forall fun n => hsub_sq (by
                rw [Complex.mem_reProdIm] at hw_sq ⊢
                have hp : 0 < 1 / ((n : ℝ) + 2) := by positivity
                have hle : 1 / ((n : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
                simp only [mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
                exact ⟨⟨by nlinarith [hw_sq.1.1, hε'], by nlinarith [hw_sq.1.2, hε']⟩,
                  ⟨by nlinarith [hw_sq.2.1, hε'], by nlinarith [hw_sq.2.2, hε']⟩⟩))
              have ht0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
              have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) :=
                ht0.congr fun n => by simp; ring
              simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp h0).mul tendsto_const_nhds (b := w)
            exact mem_closure_of_tendsto hlim (Filter.Eventually.of_forall fun n =>
              ⟨1 / ((n : ℝ) + 2), ⟨by positivity, by rw [div_le_one (by positivity)]; linarith⟩, rfl⟩)
          -- Pick one witness `w0 = (ε'/2) + (ε'/2)*I` in `V \ X_A`:
          let w0 : ℂ := ((ε' / 2 : ℝ) : ℂ) + ((ε' / 2 : ℝ) : ℂ) * I
          have hw0_oo : w0 ∈ Ioo (-ε') ε' ×ℂ Ioo (-ε') ε' := by
            rw [Complex.mem_reProdIm]
            exact ⟨⟨by simp [w0]; linarith, by simp [w0]; linarith⟩, ⟨by simp [w0]; linarith, by simp [w0]; linarith⟩⟩
          have hw0_sq : w0 ∈ Icc (-ε') ε' ×ℂ Icc (-ε') ε' :=
            Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw0_oo).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hw0_oo).2⟩
          have hw0_notXA : g w0 ∉ X_A := by
            rintro (hM | hQ)
            · have h1 : g w0 ∈ M.U ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hM, w0, hsub_sq hw0_sq, rfl⟩
              rw [hMbox] at h1; obtain ⟨u', hu', hfe⟩ := h1; rw [Complex.mem_reProdIm] at hu'
              have hu'sq : u' ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨hu'.1, by rw [mem_singleton_iff.mp hu'.2]; exact ⟨by linarith, hε.le⟩⟩
              have := congrArg Complex.im (hgi (hsub_sq hw0_sq) hu'sq hfe.symm)
              simp [w0, mem_singleton_iff.mp hu'.2] at this; linarith
            · obtain ⟨k, -, hk⟩ := mem_iUnion₂.mp hQ
              by_cases hkj : k = j
              · subst hkj
                have h1 : g w0 ∈ Q k ∩ g '' (Icc (-ε) ε ×ℂ Icc (-ε) ε) := ⟨hk, w0, hsub_sq hw0_sq, rfl⟩
                rw [hQbox] at h1; obtain ⟨u', hu', hfe⟩ := h1; rw [Complex.mem_reProdIm] at hu'
                have hu'sq : u' ∈ Icc (-ε) ε ×ℂ Icc (-ε) ε := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hu'.1]; exact ⟨by linarith, hε.le⟩, hu'.2⟩
                have := congrArg Complex.re (hgi (hsub_sq hw0_sq) hu'sq hfe.symm)
                simp [w0, mem_singleton_iff.mp hu'.1] at this; linarith
              · exact (hbox_WZ w0 hw0_sq).2 (Or.inl (mem_iUnion₂.mpr ⟨k, hkj, hk⟩))
          -- Any component `Ω` whose closure hits `z ∈ V` meets `V \ X_A`, hence has `x ∈ closure Ω`, hence touches `c`!
          have hall_touch_c : ∀ z ∈ V, ∀ y ∈ W \ X_A, z ∈ closure (connectedComponentIn (W \ X_A) y) →
              (compPure M Q c ∩ closure (connectedComponentIn (W \ X_A) y)).Nonempty := fun z hzV y hy hzcl => by
            obtain ⟨u, ⟨w, hw, rfl⟩, huΩ⟩ := mem_closure_iff.mp hzcl _ hVo hzV
            have hEq : connectedComponentIn (W \ X_A) y = connectedComponentIn (W \ X_A) (g w) :=
              connectedComponentIn_eq huΩ
            rw [hEq]
            have hxcl := hquad_cl w hw (connectedComponentIn_subset (W \ X_A) y huΩ).2
            obtain ⟨c', hxc', hne⟩ := touches_of_mem_inter_closure hS M hQcl hQdisj (fun k hk => (hA k hk).2.2)
              ⟨x₀, hx₀, hWeq⟩ ⟨g w, ⟨hVW ⟨w, hw, rfl⟩, (connectedComponentIn_subset (W \ X_A) y huΩ).2⟩, rfl⟩
              hjA hxM hxQj hxW hxcl
            have hcc : c' = c := by
              by_contra hne'; exact Set.disjoint_left.mp (compSet_pairwise_disj M hne') hxc'.1 hxc
            exact hcc ▸ hne
          refine ⟨⟨g w0, ⟨hVW ⟨w0, hw0_oo, rfl⟩, hw0_notXA⟩, hquad_cl w0 hw0_oo hw0_notXA⟩, V, hVo, hxV, hVW, ?_⟩
          by_cases hcc : c = c₁
          · left; intro z hzV; exact ⟨hVW hzV, fun y hy hzcl => by dsimp only [RedComp]; rw [← hcc]; exact hall_touch_c z hzV y hy hzcl⟩
          · right; intro z hzV; exact ⟨hVW hzV, fun y hy hzcl => ⟨c, hcc, hall_touch_c z hzV y hy hzcl⟩⟩
        · -- Case B: `x ∈ compPure M Q c`!
          obtain ⟨c, hxc⟩ := (mem_U_iff_exists_comp M).mp hxM
          have hx_pure : x ∈ compPure M Q c := by
            refine ⟨hxc, ?_⟩; rintro (hbd | hQ); exact hW_int hxW hbd
            obtain ⟨k, hxk⟩ := mem_iUnion.mp hQ
            by_cases hkA : k ∈ A; exact hxQ ⟨k, hkA, hxk⟩
            exact Set.disjoint_left.mp (hB k hkA) hxM hxk
          let Z : Set S := ⋃ j : Fin m, Q j
          have hZcl : IsClosed Z := isClosed_iUnion_of_finite hQcl
          have hx_notZ : x ∉ Z := fun h => hx_pure.2 (Or.inr h)
          obtain ⟨bc, hbc0, hbcW⟩ := exists_box_on_comp hS M c ⟨hxc, hW_int hxW⟩
            (hW_open.sdiff hZcl) ⟨hxW, hx_notZ⟩ (sdiff_subset.trans hW_int)
          have hL_in : bc.leftHalf ⊆ W \ X_A := fun z hz => by
            have hzb := hbcW (bc.clLeftHalf_subset_box (bc.leftHalf_subset_clLeft hz))
            refine ⟨hzb.1, ?_⟩
            rintro (hM | hQ)
            · exact Set.disjoint_left.mp bc.clLeftHalf_disj_A (bc.leftHalf_subset_clLeft hz) hM
            · obtain ⟨j, -, hzj⟩ := mem_iUnion₂.mp hQ; exact hzb.2 (mem_iUnion.mpr ⟨j, hzj⟩)
          have hR_in : bc.rightHalf ⊆ W \ X_A := fun z hz => by
            have hzb := hbcW (bc.clRightHalf_subset_box (bc.rightHalf_subset_clRight hz))
            refine ⟨hzb.1, ?_⟩
            rintro (hM | hQ)
            · exact Set.disjoint_left.mp bc.clRightHalf_disj_A (bc.rightHalf_subset_clRight hz) hM
            · obtain ⟨j, -, hzj⟩ := mem_iUnion₂.mp hQ; exact hzb.2 (mem_iUnion.mpr ⟨j, hzj⟩)
          obtain ⟨wL, hwL⟩ := bc.leftHalf_nonempty
          obtain ⟨wR, hwR⟩ := bc.rightHalf_nonempty
          have hL_sub : bc.leftHalf ⊆ connectedComponentIn (W \ X_A) wL :=
            bc.isConnected_leftHalf.isPreconnected.subset_connectedComponentIn hwL hL_in
          have hR_sub : bc.rightHalf ⊆ connectedComponentIn (W \ X_A) wR :=
            bc.isConnected_rightHalf.isPreconnected.subset_connectedComponentIn hwR hR_in
          have hx_clL : x ∈ closure (connectedComponentIn (W \ X_A) wL) :=
            closure_mono hL_sub (hbc0 ▸ bc.center_mem_closure_leftHalf)
          have hx_clR : x ∈ closure (connectedComponentIn (W \ X_A) wR) :=
            closure_mono hR_sub (hbc0 ▸ bc.center_mem_closure_rightHalf)
          have hall_touch_c : ∀ z ∈ bc.openBox, ∀ y ∈ W \ X_A, z ∈ closure (connectedComponentIn (W \ X_A) y) →
              (compPure M Q c ∩ closure (connectedComponentIn (W \ X_A) y)).Nonempty := fun z hzV y hy hzcl => by
            obtain ⟨u, huV, huΩ⟩ := mem_closure_iff.mp hzcl _ bc.hopen hzV
            have hunotM : u ∉ M.U := fun h => (connectedComponentIn_subset (W \ X_A) y huΩ).2 (Or.inl h)
            rcases (bc.openBox_diff_A ▸ ⟨huV, hunotM⟩ : u ∈ bc.leftHalf ∪ bc.rightHalf) with huL | huR
            · have heq : connectedComponentIn (W \ X_A) y = connectedComponentIn (W \ X_A) wL := by
                rw [connectedComponentIn_eq huΩ, ← connectedComponentIn_eq (hL_sub huL)]
              rw [heq]; exact ⟨x, hx_pure, hx_clL⟩
            · have heq : connectedComponentIn (W \ X_A) y = connectedComponentIn (W \ X_A) wR := by
                rw [connectedComponentIn_eq huΩ, ← connectedComponentIn_eq (hR_sub huR)]
              rw [heq]; exact ⟨x, hx_pure, hx_clR⟩
          refine ⟨⟨wL, hL_in hwL, hx_clL⟩, bc.openBox, bc.hopen, hbc0.symm ▸ bc.center_mem_openBox,
            bc.openBox_subset_box.trans (hbcW.trans sdiff_subset), ?_⟩
          by_cases hcc : c = c₁
          · left; intro z hzV; exact ⟨(hbcW (bc.openBox_subset_box hzV)).1, fun y hy hzcl => by dsimp only [RedComp]; rw [← hcc]; exact hall_touch_c z hzV y hy hzcl⟩
          · right; intro z hzV; exact ⟨(hbcW (bc.openBox_subset_box hzV)).1, fun y hy hzcl => ⟨c, hcc, hall_touch_c z hzV y hy hzcl⟩⟩
      · -- Case D: `x ∈ Q j \ M.U` (`j ∈ A`)!
        have hxQ : x ∈ ⋃ (j : Fin m) (_ : j ∈ A), Q j := hxXA.resolve_left hxM
        obtain ⟨j, hjA, hxQj⟩ := mem_iUnion₂.mp hxQ
        let Z : Set S := M.U ∪ ⋃ (k : Fin m) (_ : k ≠ j), Q k
        have hZcl : IsClosed Z := M.isClosed_U.union
          (isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hQcl k)
        have hx_notZ : x ∉ Z := by
          rintro (hM | hQ); exact hxM hM
          obtain ⟨k, hkj, hxk⟩ := mem_iUnion₂.mp hQ; exact Set.disjoint_left.mp (hQdisj hkj) hxk hxQj
        obtain ⟨bc, hbc0, hbcW⟩ := exists_box_on_iArc hS (hQb j) (hQl j) hxQj (hW_int hxW)
          (hW_open.sdiff hZcl) ⟨hxW, hx_notZ⟩ (sdiff_subset.trans hW_int)
        have hL_in : bc.leftHalf ⊆ W \ X_A := fun z hz => by
          have hzb := hbcW (bc.clLeftHalf_subset_box (bc.leftHalf_subset_clLeft hz))
          refine ⟨hzb.1, ?_⟩
          rintro (hM | hQ); exact hzb.2 (Or.inl hM)
          obtain ⟨k, -, hzk⟩ := mem_iUnion₂.mp hQ
          by_cases hkj : k = j
          · subst hkj; exact Set.disjoint_left.mp bc.clLeftHalf_disj_A (bc.leftHalf_subset_clLeft hz) hzk
          · exact hzb.2 (Or.inr (mem_iUnion₂.mpr ⟨k, hkj, hzk⟩))
        have hR_in : bc.rightHalf ⊆ W \ X_A := fun z hz => by
          have hzb := hbcW (bc.clRightHalf_subset_box (bc.rightHalf_subset_clRight hz))
          refine ⟨hzb.1, ?_⟩
          rintro (hM | hQ); exact hzb.2 (Or.inl hM)
          obtain ⟨k, -, hzk⟩ := mem_iUnion₂.mp hQ
          by_cases hkj : k = j
          · subst hkj; exact Set.disjoint_left.mp bc.clRightHalf_disj_A (bc.rightHalf_subset_clRight hz) hzk
          · exact hzb.2 (Or.inr (mem_iUnion₂.mpr ⟨k, hkj, hzk⟩))
        obtain ⟨wL, hwL⟩ := bc.leftHalf_nonempty
        obtain ⟨wR, hwR⟩ := bc.rightHalf_nonempty
        have hL_sub : bc.leftHalf ⊆ connectedComponentIn (W \ X_A) wL :=
          bc.isConnected_leftHalf.isPreconnected.subset_connectedComponentIn hwL hL_in
        have hR_sub : bc.rightHalf ⊆ connectedComponentIn (W \ X_A) wR :=
          bc.isConnected_rightHalf.isPreconnected.subset_connectedComponentIn hwR hR_in
        have hx_clL : x ∈ closure (connectedComponentIn (W \ X_A) wL) :=
          closure_mono hL_sub (hbc0 ▸ bc.center_mem_closure_leftHalf)
        have hx_clR : x ∈ closure (connectedComponentIn (W \ X_A) wR) :=
          closure_mono hR_sub (hbc0 ▸ bc.center_mem_closure_rightHalf)
        -- Walk along `Q j` from `x` to a single common crossing `p* ∈ M.U ∩ Q j` reached by BOTH `Ω_L` and `Ω_R`!
        obtain ⟨p, ⟨hpM, hpQj⟩, hpW, hp_all⟩ := exists_crossing_in_closure_of_Q hS M hQb hQl hQdisj
          (fun k hk => (hA k hk).1) (fun k hk => (hA k hk).2.1) hQ_disj_st
          ⟨x₀, hx₀, hWeq⟩ hjA hxQj hxM hxW
        obtain ⟨c, hpc⟩ := (mem_U_iff_exists_comp M).mp hpM
        have htouch_of_side : ∀ {w : S} (hw : w ∈ W \ X_A), x ∈ closure (connectedComponentIn (W \ X_A) w) →
            (compPure M Q c ∩ closure (connectedComponentIn (W \ X_A) w)).Nonempty := fun {w} hw hcl => by
          obtain ⟨c', hpc', hne⟩ := touches_of_mem_inter_closure hS M hQcl hQdisj (fun k hk => (hA k hk).2.2)
            ⟨x₀, hx₀, hWeq⟩ ⟨w, hw, rfl⟩ hjA hpM hpQj hpW (hp_all w hw hcl)
          have hcc : c' = c := by
            by_contra hne'; exact Set.disjoint_left.mp (compSet_pairwise_disj M hne') hpc'.1 hpc
          exact hcc ▸ hne
        have htouchL := htouch_of_side (hL_in hwL) hx_clL
        have htouchR := htouch_of_side (hR_in hwR) hx_clR
        have hall_touch_c : ∀ z ∈ bc.openBox, ∀ y ∈ W \ X_A, z ∈ closure (connectedComponentIn (W \ X_A) y) →
            (compPure M Q c ∩ closure (connectedComponentIn (W \ X_A) y)).Nonempty := fun z hzV y hy hzcl => by
          obtain ⟨u, huV, huΩ⟩ := mem_closure_iff.mp hzcl _ bc.hopen hzV
          have hunotQ : u ∉ Q j := fun h => (connectedComponentIn_subset (W \ X_A) y huΩ).2 (Or.inr (mem_iUnion₂.mpr ⟨j, hjA, h⟩))
          rcases (bc.openBox_diff_A ▸ ⟨huV, hunotQ⟩ : u ∈ bc.leftHalf ∪ bc.rightHalf) with huL | huR
          · have heq : connectedComponentIn (W \ X_A) y = connectedComponentIn (W \ X_A) wL := by
              rw [connectedComponentIn_eq huΩ, ← connectedComponentIn_eq (hL_sub huL)]
            rw [heq]; exact htouchL
          · have heq : connectedComponentIn (W \ X_A) y = connectedComponentIn (W \ X_A) wR := by
              rw [connectedComponentIn_eq huΩ, ← connectedComponentIn_eq (hR_sub huR)]
            rw [heq]; exact htouchR
        refine ⟨⟨wL, hL_in hwL, hx_clL⟩, bc.openBox, bc.hopen, hbc0.symm ▸ bc.center_mem_openBox,
          bc.openBox_subset_box.trans (hbcW.trans sdiff_subset), ?_⟩
        by_cases hcc : c = c₁
        · left; intro z hzV; exact ⟨(hbcW (bc.openBox_subset_box hzV)).1, fun y hy hzcl => by dsimp only [RedComp]; rw [← hcc]; exact hall_touch_c z hzV y hy hzcl⟩
        · right; intro z hzV; exact ⟨(hbcW (bc.openBox_subset_box hzV)).1, fun y hy hzcl => ⟨c, hcc, hall_touch_c z hzV y hy hzcl⟩⟩
  -- Finish the connectedness contradiction on `W = U_R ∪ U_B`:
  have hUR_open : IsOpen U_R := by
    rw [isOpen_iff_mem_nhds]; intro x hxR
    obtain ⟨⟨y, hy, hxy⟩, V, hVo, hxV, -, hVR | hVB⟩ := hlocal x hxR.1
    · exact Filter.mem_of_superset (hVo.mem_nhds hxV) hVR
    · exact (hRB_not_both y hy ⟨hxR.2 y hy hxy, (hVB hxV).2 y hy hxy⟩).elim
  have hUB_open : IsOpen U_B := by
    rw [isOpen_iff_mem_nhds]; intro x hxB
    obtain ⟨⟨y, hy, hxy⟩, V, hVo, hxV, -, hVR | hVB⟩ := hlocal x hxB.1
    · exact (hRB_not_both y hy ⟨(hVR hxV).2 y hy hxy, hxB.2 y hy hxy⟩).elim
    · exact Filter.mem_of_superset (hVo.mem_nhds hxV) hVB
  have hcov : W ⊆ U_R ∪ U_B := fun x hxW => by
    obtain ⟨-, V, -, hxV, -, hVR | hVB⟩ := hlocal x hxW
    · exact Or.inl (hVR hxV)
    · exact Or.inr (hVB hxV)
  have hR_ne : (W ∩ U_R).Nonempty := by
    obtain ⟨p₁, hp₁⟩ := compPure_nonempty hS M hQcl hQdisj (fun j hj => (hA j hj).2.2) hB c₁
    have hp₁W : p₁ ∈ W := hc₁W ⟨hp₁.1, fun h => hp₁.2 (Or.inl h)⟩
    refine ⟨p₁, hp₁W, hp₁W, fun y hy hp₁cl => ⟨p₁, hp₁, hp₁cl⟩⟩
  have hB_ne : (W ∩ U_B).Nonempty := by
    obtain ⟨p₂, hp₂⟩ := compPure_nonempty hS M hQcl hQdisj (fun j hj => (hA j hj).2.2) hB c₂
    have hp₂W : p₂ ∈ W := hc₂W ⟨hp₂.1, fun h => hp₂.2 (Or.inl h)⟩
    refine ⟨p₂, hp₂W, hp₂W, fun y hy hp₂cl => ⟨c₂, hc12.symm, p₂, hp₂, hp₂cl⟩⟩
  obtain ⟨z, hzW, hzR, hzB⟩ := hW_conn U_R U_B hUR_open hUB_open hcov hR_ne hB_ne
  obtain ⟨⟨y, hy, hzy⟩, -⟩ := hlocal z hzW
  exact hRB_not_both y hy ⟨hzR.2 y hy hzy, hzB.2 y hy hzy⟩

/-- **Shortest chain in `W_all`** (Case 2):
Suppose `M.Os ≠ []` and every component of `W_all := (bd S)ᶜ \ ⋃_{i ∉ A} Q i` contains at most
one component of `M`. Then there exist `k ≥ 1`, pairwise distinct components `W : Fin (k + 1) → Set S`
of `W_all`, injective `idxs : Fin k → Fin m` with `idxs r ∉ A`, points `q r ∈ Q (idxs r) \ bd S`
with `q r ∈ closure (W r.castSucc) ∩ closure (W r.succ)`, such that `W 0` and `W (Fin.last k)`
each contain a component of `M`, while NO intermediate `W r` (`0 < r < k`) meets `M.U` (nor any `Q j`, `j ∈ A`). -/
private theorem exists_min_chain [ConnectedSpace S] (hS : IsSurface S) {s t : S}
    (M : ProperManifold S s t) (hOs : M.Os ≠ [])
    {m : ℕ} {Q : Fin m → Set S} {uQ vQ : Fin m → S}
    (hQb : ∀ j, Q j ∩ bd S = {uQ j, vQ j})
    (hQl : ∀ j, IsLineWithEnds (Q j) (uQ j) (vQ j))
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hQ_disj_st : ∀ j, s ∉ Q j ∧ t ∉ Q j)
    {A : Finset (Fin m)}
    (hAne : ∀ j ∈ A, (M.U ∩ Q j).Nonempty)
    (hB : ∀ i : Fin m, i ∉ A → Disjoint M.U (Q i))
    (huniq_W : ∀ x₀ ∈ (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i, ∀ c₁ c₂ : Comp M,
      compInt M c₁ ⊆ connectedComponentIn ((bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i) x₀ →
      compInt M c₂ ⊆ connectedComponentIn ((bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i) x₀ → c₁ = c₂) :
    let W_all := (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i
    ∃ (k : ℕ) (_ : 0 < k) (W : Fin (k + 1) → Set S) (idxs : Fin k → Fin m) (q : Fin k → S) (cL cR : Comp M),
      (∀ l : Fin (k + 1), ∃ x ∈ W_all, W l = connectedComponentIn W_all x) ∧
      Function.Injective W ∧
      Function.Injective idxs ∧
      (∀ r : Fin k, idxs r ∉ A) ∧
      (∀ r : Fin k, q r ∈ Q (idxs r) \ bd S ∧ q r ∈ closure (W r.castSucc) ∧ q r ∈ closure (W r.succ)) ∧
      compInt M cL ⊆ W 0 ∧ compInt M cR ⊆ W (Fin.last k) ∧ cL ≠ cR ∧
      (∀ l : Fin (k + 1), 0 < l.1 → l.1 < k → Disjoint (W l) (M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j)) := by
  classical
  have : T2Space S := hS.2.1
  let W_all := (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i
  have hQcl : ∀ j, IsClosed (Q j) := fun j => (hQl j).isCompact.isClosed
  have hWall_open : IsOpen W_all := (isClosed_bd S).isOpen_compl.sdiff
    (isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => hQcl i)
  let IsComp (W : Set S) : Prop := ∃ x ∈ W_all, W = connectedComponentIn W_all x
  have hComp_open : ∀ {W}, IsComp W → IsOpen W := fun ⟨x, hx, heq⟩ =>
    heq ▸ isOpen_connectedComponentIn_of_subset_compl_bd hS hWall_open sdiff_subset hx
  have hComp_disj : ∀ {W₁ W₂}, IsComp W₁ → IsComp W₂ → W₁ ≠ W₂ → Disjoint W₁ W₂ := by
    rintro W₁ W₂ ⟨x₁, -, rfl⟩ ⟨x₂, -, rfl⟩ hne
    rw [Set.disjoint_left]; intro z hz1 hz2
    exact hne (by rw [connectedComponentIn_eq hz1, ← connectedComponentIn_eq hz2])
  have hcomp_in_Wall : ∀ c : Comp M, compInt M c ⊆ W_all := fun c z hz =>
    ⟨hz.2, fun h => by
      obtain ⟨i, hiA, hzi⟩ := mem_iUnion₂.mp h
      exact Set.disjoint_left.mp (hB i hiA) (compSet_subset_U M c hz.1) hzi⟩
  -- For each `c : Comp M`, there is a unique component `compW c` of `W_all` containing `compInt M c`:
  have hex_compW : ∀ c : Comp M, ∃ W, IsComp W ∧ compInt M c ⊆ W := fun c => by
    obtain ⟨x, hx⟩ := compInt_nonempty M c
    exact ⟨connectedComponentIn W_all x, ⟨x, hcomp_in_Wall c hx, rfl⟩,
      (compInt_isPreconnected M c).subset_connectedComponentIn hx (hcomp_in_Wall c)⟩
  -- Local box at any `q ∈ Q i \ bd S` (`i ∉ A`) puts its two halves in two components `WL, WR` of `W_all`:
  have hbox_B : ∀ {i : Fin m}, i ∉ A → ∀ q ∈ Q i \ bd S,
      ∃ (bc : BoxChart S (Q i)) (WL WR : Set S),
        bc.g 0 = q ∧ IsComp WL ∧ IsComp WR ∧
        bc.clLeftHalf ⊆ WL ∧ bc.clRightHalf ⊆ WR ∧
        q ∈ closure WL ∧ q ∈ closure WR ∧
        (∀ W, IsComp W → ∀ z ∈ bc.openBox, z ∈ closure W → W = WL ∨ W = WR) := by
    intro i hiA q hq
    let Z : Set S := ⋃ (k : Fin m) (_ : k ≠ i), Q k
    have hZcl : IsClosed Z := isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hQcl k
    have hq_notZ : q ∉ Z := fun h => by
      obtain ⟨k, hki, hqk⟩ := mem_iUnion₂.mp h; exact Set.disjoint_left.mp (hQdisj hki) hqk hq.1
    obtain ⟨bc, hbc0, hbcW⟩ := exists_box_on_iArc hS (hQb i) (hQl i) hq.1 hq.2
      ((isClosed_bd S).isOpen_compl.sdiff hZcl) ⟨hq.2, hq_notZ⟩ sdiff_subset
    have hL_Wall : bc.clLeftHalf ⊆ W_all := fun z hz => by
      have hzb := hbcW (bc.clLeftHalf_subset_box hz)
      refine ⟨hzb.1, fun h => ?_⟩
      obtain ⟨k, -, hzk⟩ := mem_iUnion₂.mp h
      by_cases hki : k = i
      · subst hki; exact Set.disjoint_left.mp bc.clLeftHalf_disj_A hz hzk
      · exact hzb.2 (mem_iUnion₂.mpr ⟨k, hki, hzk⟩)
    have hR_Wall : bc.clRightHalf ⊆ W_all := fun z hz => by
      have hzb := hbcW (bc.clRightHalf_subset_box hz)
      refine ⟨hzb.1, fun h => ?_⟩
      obtain ⟨k, -, hzk⟩ := mem_iUnion₂.mp h
      by_cases hki : k = i
      · subst hki; exact Set.disjoint_left.mp bc.clRightHalf_disj_A hz hzk
      · exact hzb.2 (mem_iUnion₂.mpr ⟨k, hki, hzk⟩)
    obtain ⟨xL, hxL⟩ := bc.leftHalf_nonempty
    obtain ⟨xR, hxR⟩ := bc.rightHalf_nonempty
    let WL := connectedComponentIn W_all xL
    let WR := connectedComponentIn W_all xR
    have hLsub : bc.clLeftHalf ⊆ WL :=
      bc.isConnected_clLeftHalf.isPreconnected.subset_connectedComponentIn (bc.leftHalf_subset_clLeft hxL) hL_Wall
    have hRsub : bc.clRightHalf ⊆ WR :=
      bc.isConnected_clRightHalf.isPreconnected.subset_connectedComponentIn (bc.rightHalf_subset_clRight hxR) hR_Wall
    refine ⟨bc, WL, WR, hbc0, ⟨xL, hL_Wall (bc.leftHalf_subset_clLeft hxL), rfl⟩,
      ⟨xR, hR_Wall (bc.rightHalf_subset_clRight hxR), rfl⟩, hLsub, hRsub,
      closure_mono (bc.leftHalf_subset_clLeft.trans hLsub) (hbc0 ▸ bc.center_mem_closure_leftHalf),
      closure_mono (bc.rightHalf_subset_clRight.trans hRsub) (hbc0 ▸ bc.center_mem_closure_rightHalf), ?_⟩
    rintro W ⟨xW, -, rfl⟩ z hzV hzcl
    obtain ⟨u, huV, huW⟩ := mem_closure_iff.mp hzcl _ bc.hopen hzV
    have hunotQi : u ∉ Q i := fun h => (connectedComponentIn_subset W_all xW huW).2 (mem_iUnion₂.mpr ⟨i, hiA, h⟩)
    rcases (bc.openBox_diff_A ▸ ⟨huV, hunotQi⟩ : u ∈ bc.leftHalf ∪ bc.rightHalf) with huL | huR
    · left; rw [connectedComponentIn_eq huW, ← connectedComponentIn_eq (hLsub (bc.leftHalf_subset_clLeft huL))]
    · right; rw [connectedComponentIn_eq huW, ← connectedComponentIn_eq (hRsub (bc.rightHalf_subset_clRight huR))]
  -- Define adjacency and chains:
  let Adj (W₁ W₂ : Set S) (i : Fin m) : Prop :=
    i ∉ A ∧ ∃ q ∈ Q i \ bd S, q ∈ closure W₁ ∧ q ∈ closure W₂
  let ValidChain (k : ℕ) : Prop :=
    ∃ (W : Fin (k + 1) → Set S) (idxs : Fin k → Fin m) (cL cR : Comp M),
      (∀ l, IsComp (W l)) ∧ (∀ r : Fin k, Adj (W r.castSucc) (W r.succ) (idxs r)) ∧
      compInt M cL ⊆ W 0 ∧ compInt M cR ⊆ W (Fin.last k) ∧ W 0 ≠ W (Fin.last k)
  -- Step 1: Prove `∃ k, ValidChain k` using connectedness of `(bd S)ᶜ`!
  have hvalid_ex : ∃ k : ℕ, ValidChain k := by
    let c₀ : Comp M := none
    let c₁ : Comp M := some ⟨0, List.length_pos_of_ne_nil hOs⟩
    have hc01 : c₀ ≠ c₁ := by simp [c₀, c₁]
    obtain ⟨W₀, hW₀c, hW₀sub⟩ := hex_compW c₀
    obtain ⟨W₁, hW₁c, hW₁sub⟩ := hex_compW c₁
    have hW01 : W₀ ≠ W₁ := by
      intro h; subst h
      obtain ⟨x₀, hx₀, heq⟩ := hW₀c
      exact hc01 (huniq_W x₀ hx₀ c₀ c₁ (heq ▸ hW₀sub) (heq ▸ hW₁sub))
    -- Set of components reachable from `W₀`:
    let Reach (W : Set S) : Prop := IsComp W ∧ ∃ (k : ℕ) (U : Fin (k + 1) → Set S) (idxs : Fin k → Fin m),
      (∀ l, IsComp (U l)) ∧ (∀ r : Fin k, Adj (U r.castSucc) (U r.succ) (idxs r)) ∧ U 0 = W₀ ∧ U (Fin.last k) = W
    have hR0 : Reach W₀ := ⟨hW₀c, 0, fun _ => W₀, Fin.elim0, fun _ => hW₀c, fun r => Fin.elim0 r, rfl, rfl⟩
    have hR_step : ∀ {U V : Set S} {i : Fin m}, Reach U → IsComp V → Adj U V i → Reach V := by
      rintro U V i ⟨-, k, Uc, idxs, hUc, hAdj, hU0, hUk⟩ hVc hUV
      refine ⟨hVc, k + 1, Fin.snoc Uc V, Fin.snoc idxs i, ?_, ?_, ?_, ?_⟩
      · intro l; refine Fin.lastCases ?_ (fun j => ?_) l
        · simpa using hVc
        · simpa using hUc j
      · intro r; refine Fin.lastCases ?_ (fun j => ?_) r
        · have h1 : (Fin.last k).castSucc = (Fin.last k).castSucc := rfl
          simpa [Fin.snoc_last, Fin.snoc_castSucc, hUk] using hUV
        · have heq : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
          rw [Fin.snoc_castSucc, heq, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hAdj j
      · simpa [Fin.snoc_castSucc] using hU0
      · simp
    let V₁ : Set S := {x ∈ (bd S)ᶜ | ∀ W, IsComp W → x ∈ closure W → Reach W}
    let V₂ : Set S := {x ∈ (bd S)ᶜ | ∀ W, IsComp W → x ∈ closure W → ¬ Reach W}
    have hloc : ∀ x ∈ (bd S)ᶜ, (∃ W, IsComp W ∧ x ∈ closure W) ∧
        ∃ O, IsOpen O ∧ x ∈ O ∧ (O ⊆ V₁ ∨ O ⊆ V₂) := by
      intro x hxbd
      by_cases hxW : x ∈ W_all
      · let Wx := connectedComponentIn W_all x
        have hWxc : IsComp Wx := ⟨x, hxW, rfl⟩
        have hWxo : IsOpen Wx := hComp_open hWxc
        have hxWx : x ∈ Wx := mem_connectedComponentIn hxW
        have hWxint : Wx ⊆ (bd S)ᶜ := (connectedComponentIn_subset W_all x).trans sdiff_subset
        refine ⟨⟨Wx, hWxc, subset_closure hxWx⟩, Wx, hWxo, hxWx, ?_⟩
        by_cases hR : Reach Wx
        · left; intro z hz; refine ⟨hWxint hz, fun W hWc hzcl => ?_⟩
          obtain ⟨u, hu1, hu2⟩ := mem_closure_iff.mp hzcl _ hWxo hz
          obtain ⟨yW, -, rfl⟩ := hWc
          have heq : connectedComponentIn W_all yW = Wx := by rw [connectedComponentIn_eq hu2, ← connectedComponentIn_eq hu1]
          rwa [heq]
        · right; intro z hz; refine ⟨hWxint hz, fun W hWc hzcl => ?_⟩
          obtain ⟨u, hu1, hu2⟩ := mem_closure_iff.mp hzcl _ hWxo hz
          obtain ⟨yW, -, rfl⟩ := hWc
          have heq : connectedComponentIn W_all yW = Wx := by rw [connectedComponentIn_eq hu2, ← connectedComponentIn_eq hu1]
          rwa [heq]
      · have hxQ : x ∈ ⋃ (i : Fin m) (_ : i ∉ A), Q i := by
          by_contra hnot; exact hxW ⟨hxbd, hnot⟩
        obtain ⟨i, hiA, hxQi⟩ := mem_iUnion₂.mp hxQ
        obtain ⟨bc, WL, WR, hbc0, hWLc, hWRc, -, -, hxclL, hxclR, hopen_sides⟩ := hbox_B hiA x ⟨hxQi, hxbd⟩
        have hAdjLR : Adj WL WR i := ⟨hiA, x, ⟨hxQi, hxbd⟩, hxclL, hxclR⟩
        have hAdjRL : Adj WR WL i := ⟨hiA, x, ⟨hxQi, hxbd⟩, hxclR, hxclL⟩
        have hRiff : Reach WL ↔ Reach WR := ⟨fun h => hR_step h hWRc hAdjLR, fun h => hR_step h hWLc hAdjRL⟩
        refine ⟨⟨WL, hWLc, hxclL⟩, bc.openBox, bc.hopen, hbc0.symm ▸ bc.center_mem_openBox, ?_⟩
        by_cases hR : Reach WL
        · left; intro z hz; refine ⟨bc.hgint (bc.openBox_subset_box hz), fun W hWc hzcl => ?_⟩
          rcases hopen_sides W hWc z hz hzcl with rfl | rfl; exact hR; exact hRiff.mp hR
        · right; intro z hz; refine ⟨bc.hgint (bc.openBox_subset_box hz), fun W hWc hzcl => ?_⟩
          rcases hopen_sides W hWc z hz hzcl with rfl | rfl; exact hR; exact fun h => hR (hRiff.mpr h)
    have hV₁o : IsOpen V₁ := by
      rw [isOpen_iff_mem_nhds]; intro x hx
      obtain ⟨⟨W, hWc, hxcl⟩, O, hOo, hxO, hO1 | hO2⟩ := hloc x hx.1
      · exact Filter.mem_of_superset (hOo.mem_nhds hxO) hO1
      · exact ((hO2 hxO).2 W hWc hxcl (hx.2 W hWc hxcl)).elim
    have hV₂o : IsOpen V₂ := by
      rw [isOpen_iff_mem_nhds]; intro x hx
      obtain ⟨⟨W, hWc, hxcl⟩, O, hOo, hxO, hO1 | hO2⟩ := hloc x hx.1
      · exact (hx.2 W hWc hxcl ((hO1 hxO).2 W hWc hxcl)).elim
      · exact Filter.mem_of_superset (hOo.mem_nhds hxO) hO2
    have hcov : (bd S)ᶜ ⊆ V₁ ∪ V₂ := fun x hx => by
      obtain ⟨-, O, -, hxO, hO1 | hO2⟩ := hloc x hx; exact Or.inl (hO1 hxO); exact Or.inr (hO2 hxO)
    have hR1 : Reach W₁ := by
      by_contra hnotR1
      have ⟨x₀, hx₀, hW₀eq⟩ := hW₀c
      have ⟨x₁, hx₁, hW₁eq⟩ := hW₁c
      have hx₀V₁ : x₀ ∈ V₁ := ⟨hx₀.1, fun W hWc hcl => by
        obtain ⟨u, hu1, hu2⟩ := mem_closure_iff.mp hcl _ (hComp_open hW₀c) (hW₀eq ▸ mem_connectedComponentIn hx₀)
        obtain ⟨yW, -, rfl⟩ := hWc; rw [hW₀eq] at hu1
        have heq : connectedComponentIn W_all yW = W₀ := by rw [connectedComponentIn_eq hu2, ← connectedComponentIn_eq hu1, ← hW₀eq]
        exact heq ▸ hR0⟩
      have hx₁V₂ : x₁ ∈ V₂ := ⟨hx₁.1, fun W hWc hcl => by
        obtain ⟨u, hu1, hu2⟩ := mem_closure_iff.mp hcl _ (hComp_open hW₁c) (hW₁eq ▸ mem_connectedComponentIn hx₁)
        obtain ⟨yW, -, rfl⟩ := hWc; rw [hW₁eq] at hu1
        have heq : connectedComponentIn W_all yW = W₁ := by rw [connectedComponentIn_eq hu2, ← connectedComponentIn_eq hu1, ← hW₁eq]
        exact heq ▸ hnotR1⟩
      obtain ⟨z, hzbd, hz1, hz2⟩ := isPreconnected_compl_bd hS V₁ V₂ hV₁o hV₂o hcov ⟨x₀, hx₀.1, hx₀V₁⟩ ⟨x₁, hx₁.1, hx₁V₂⟩
      obtain ⟨⟨W, hWc, hzcl⟩, -⟩ := hloc z hzbd
      exact hz2.2 W hWc hzcl (hz1.2 W hWc hzcl)
    obtain ⟨-, k, U, idxs, hUc, hAdj, hU0, hUk⟩ := hR1
    exact ⟨k, U, idxs, c₀, c₁, hUc, hAdj, hU0.symm ▸ hW₀sub, hUk.symm ▸ hW₁sub, hU0.symm ▸ hUk.symm ▸ hW01⟩
  -- Step 2: Take a MINIMAL `k` with `ValidChain k`!
  let k := Nat.find hvalid_ex
  have hk_valid : ValidChain k := Nat.find_spec hvalid_ex
  have hk_min : ∀ k' < k, ¬ ValidChain k' := fun k' hlt => Nat.find_min hvalid_ex hlt
  obtain ⟨W, idxs, cL, cR, hWc, hAdj, hcL_sub, hcR_sub, hW_ne⟩ := hk_valid
  have hk_pos : 0 < k := by
    by_contra h0; have hk0 : k = 0 := by omega
    have h0last : (0 : Fin (k + 1)) = Fin.last k := Fin.ext (by simp [hk0])
    exact hW_ne (congrArg W h0last)
  -- Check `W` is injective (otherwise splice out the cycle for a shorter valid chain!):
  have hW_inj : Function.Injective W := by
    have hsplice : ∀ a b : Fin (k + 1), W a = W b → a.1 < b.1 → False := by
      intro a b hab hlt
      let k' := k - (b.1 - a.1)
      have hk'lt : k' < k := by have := b.2; omega
      let fW : Fin (k' + 1) → Fin (k + 1) := fun l =>
        if h : l.1 ≤ a.1 then ⟨l.1, by omega⟩ else ⟨l.1 + (b.1 - a.1), by omega⟩
      let fI : Fin k' → Fin k := fun r =>
        if h : r.1 < a.1 then ⟨r.1, by omega⟩ else ⟨r.1 + (b.1 - a.1), by omega⟩
      have h0 : fW 0 = 0 := by simp [fW]
      have hWlast : W (fW (Fin.last k')) = W (Fin.last k) := by
        dsimp only [fW]; split_ifs with h
        · have hb_eq : b = Fin.last k := Fin.ext (by simp [k', Fin.val_last] at h ⊢; have := b.2; omega)
          have ha_eq : (⟨(Fin.last k').1, by omega⟩ : Fin (k + 1)) = a := Fin.ext (by simp [k', Fin.val_last] at h ⊢; have := b.2; omega)
          rw [ha_eq, hab, hb_eq]
        · exact congrArg W (Fin.ext (by simp [k', Fin.val_last]; have := b.2; omega))
      refine hk_min k' hk'lt ⟨fun l => W (fW l), fun r => idxs (fI r), cL, cR,
        fun l => hWc (fW l), ?_, ?_, ?_, ?_⟩
      · intro r; dsimp only [fW, fI]
        by_cases hr1 : r.1 + 1 ≤ a.1
        · have hr0 : r.1 ≤ a.1 := by omega
          have hlt0 : r.1 < a.1 := by omega
          simp only [Fin.val_castSucc, Fin.val_succ, hr0, hr1, hlt0, ↓reduceDIte]
          exact hAdj ⟨r.1, by omega⟩
        · by_cases hr0 : r.1 ≤ a.1
          · have hra : r.1 = a.1 := by omega
            have hlt0 : ¬ r.1 < a.1 := by omega
            simp only [Fin.val_castSucc, Fin.val_succ, hr0, hr1, hlt0, ↓reduceDIte]
            have h1' : W ⟨r.1, by omega⟩ = W a := congrArg W (Fin.ext hra)
            have h2' : W ⟨r.1 + 1 + (b.1 - a.1), by omega⟩ = W (⟨r.1 + (b.1 - a.1), by omega⟩ : Fin k).succ :=
              congrArg W (Fin.ext (by simp; omega))
            have h3' : W (⟨r.1 + (b.1 - a.1), by omega⟩ : Fin k).castSucc = W b :=
              congrArg W (Fin.ext (by simp; omega))
            rw [h1', hab, ← h3', h2']; exact hAdj ⟨r.1 + (b.1 - a.1), by omega⟩
          · have hlt0 : ¬ r.1 < a.1 := by omega
            simp only [Fin.val_castSucc, Fin.val_succ, hr0, hr1, hlt0, ↓reduceDIte]
            have h2 : (⟨r.1 + 1 + (b.1 - a.1), by omega⟩ : Fin (k + 1)) = (⟨r.1 + (b.1 - a.1), by omega⟩ : Fin k).succ :=
              Fin.ext (by simp; omega)
            rw [h2]; exact hAdj ⟨r.1 + (b.1 - a.1), by omega⟩
      · dsimp only; rw [h0]; exact hcL_sub
      · dsimp only; rw [hWlast]; exact hcR_sub
      · dsimp only; rw [h0, hWlast]; exact hW_ne
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hsplice a b hab hlt
    · exact hsplice b a hab.symm hlt
  -- Check NO intermediate `W l` (`0 < l < k`) meets `M.U` (nor `Q j` for `j ∈ A`):
  have hmid_disj : ∀ l : Fin (k + 1), 0 < l.1 → l.1 < k →
      Disjoint (W l) (M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j) := by
    intro l hl0 hlk
    have hno_comp : ∀ c : Comp M, ¬ (compInt M c ⊆ W l) := fun c hcsub => by
      have hW0l : W 0 ≠ W l := fun h => by have := hW_inj h; exact hl0.ne' (congrArg Fin.val this).symm
      refine hk_min l.1 hlk ⟨fun j => W ⟨j.1, by omega⟩, fun r => idxs ⟨r.1, by omega⟩, cL, c,
        fun j => hWc _, fun r => hAdj ⟨r.1, by omega⟩, hcL_sub, ?_, ?_⟩
      · dsimp only
        have heq : (⟨(Fin.last l.1).1, by omega⟩ : Fin (k + 1)) = l := Fin.ext rfl
        rw [heq]; exact hcsub
      · dsimp only
        have heq : (⟨(Fin.last l.1).1, by omega⟩ : Fin (k + 1)) = l := Fin.ext rfl
        rw [heq]; exact hW0l
    rw [Set.disjoint_left]; intro z hzW hzXA
    obtain ⟨xW, hxW, hWeq⟩ := hWc l
    have hzint : z ∈ (bd S)ᶜ := (connectedComponentIn_subset W_all xW (hWeq ▸ hzW)).1
    rcases hzXA with hzM | hzQ
    · obtain ⟨c, hzc⟩ := (mem_U_iff_exists_comp M).mp hzM
      refine hno_comp c ?_
      rw [hWeq] at hzW ⊢; rw [connectedComponentIn_eq hzW]
      exact (compInt_isPreconnected M c).subset_connectedComponentIn ⟨hzc, hzint⟩ (hcomp_in_Wall c)
    · obtain ⟨j, hjA, hzj⟩ := mem_iUnion₂.mp hzQ
      obtain ⟨p, hpM, hpQj⟩ := hAne j hjA
      obtain ⟨c, hpc⟩ := (mem_U_iff_exists_comp M).mp hpM
      have hp_notbd : p ∈ (bd S)ᶜ := fun hbd => by
        have hm : p ∈ M.U ∩ bd S := ⟨hpM, hbd⟩; rw [M.U_inter_bd] at hm
        rcases hm with rfl | htp
        · exact (hQ_disj_st j).1 hpQj
        · exact (hQ_disj_st j).2 (mem_singleton_iff.mp htp ▸ hpQj)
      obtain ⟨φ, hφ0, hφ1⟩ := hQl j
      have hQconn : IsPreconnected (Q j \ bd S) := by
        have heq : Q j \ bd S = (fun r : unitInterval => (φ r).1) '' {r : unitInterval | r.1 ∈ Ioo (0 : ℝ) 1} := by
          ext w; constructor
          · rintro ⟨hwQ, hwbd⟩
            let r := φ.symm ⟨w, hwQ⟩
            refine ⟨r, ⟨lt_of_le_of_ne r.2.1 fun h0 => hwbd ?_, lt_of_le_of_ne r.2.2 fun h1 => hwbd ?_⟩,
              congrArg Subtype.val (φ.apply_symm_apply _)⟩
            · have : w = uQ j := by
                have h : (φ (φ.symm ⟨w, hwQ⟩)).1 = w := congrArg Subtype.val (φ.apply_symm_apply ⟨w, hwQ⟩)
                rw [← h, show φ.symm ⟨w, hwQ⟩ = 0 from Subtype.ext h0.symm]; exact hφ0
              exact this ▸ (hQb j ▸ Or.inl rfl : uQ j ∈ Q j ∩ bd S).2
            · have : w = vQ j := by
                have h : (φ (φ.symm ⟨w, hwQ⟩)).1 = w := congrArg Subtype.val (φ.apply_symm_apply ⟨w, hwQ⟩)
                rw [← h, show φ.symm ⟨w, hwQ⟩ = 1 from Subtype.ext h1]; exact hφ1
              exact this ▸ (hQb j ▸ Or.inr rfl : vQ j ∈ Q j ∩ bd S).2
          · rintro ⟨r, hr, rfl⟩
            refine ⟨(φ r).2, fun hbd => ?_⟩
            have hm : (φ r).1 ∈ Q j ∩ bd S := ⟨(φ r).2, hbd⟩; rw [hQb j] at hm
            rcases hm with hu | hv
            · have h0 : r.1 = 0 := congrArg Subtype.val (φ.injective (Subtype.ext (hu.trans hφ0.symm))); linarith [hr.1]
            · have h1 : r.1 = 1 := congrArg Subtype.val (φ.injective (Subtype.ext ((mem_singleton_iff.mp hv).trans hφ1.symm))); linarith [hr.2]
        rw [heq]
        have hIoo_conn : IsPreconnected {r : unitInterval | r.1 ∈ Ioo (0 : ℝ) 1} := by
          have hsub : {r : unitInterval | r.1 ∈ Ioo (0 : ℝ) 1} =
              (fun x : ℝ => (⟨max 0 (min 1 x), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩ : unitInterval)) '' Ioo 0 1 := by
            ext r; constructor
            · intro hr; refine ⟨r.1, hr, Subtype.ext ?_⟩; dsimp; rw [min_eq_right hr.2.le, max_eq_right hr.1.le]
            · rintro ⟨x, hx, rfl⟩; dsimp; rw [min_eq_right hx.2.le, max_eq_right hx.1.le]; exact hx
          rw [hsub]; exact isPreconnected_Ioo.image _ (by fun_prop)
        exact hIoo_conn.image _ (continuous_subtype_val.comp φ.continuous).continuousOn
      have hQ_in_Wl : Q j \ bd S ⊆ W l := by
        rw [hWeq] at hzW ⊢; rw [connectedComponentIn_eq hzW]
        refine hQconn.subset_connectedComponentIn ⟨hzj, hzint⟩ fun w ⟨hwQ, hwbd⟩ => ⟨hwbd, fun h => ?_⟩
        obtain ⟨i, hiA, hwi⟩ := mem_iUnion₂.mp h
        exact Set.disjoint_left.mp (hQdisj (show i ≠ j from fun he => hiA (he ▸ hjA))) hwi hwQ
      have hpW : p ∈ W l := hQ_in_Wl ⟨hpQj, hp_notbd⟩
      refine hno_comp c ?_
      rw [hWeq] at hpW ⊢; rw [connectedComponentIn_eq hpW]
      exact (compInt_isPreconnected M c).subset_connectedComponentIn ⟨hpc, hp_notbd⟩ (hcomp_in_Wall c)
  -- Check `idxs` is injective (each `Q i \ bd S` is connected and thus touches at most 2 components of `W_all`):
  have hQ_at_most_two : ∀ {i : Fin m}, i ∉ A →
      ∃ U₁ U₂ : Set S, ∀ q ∈ Q i \ bd S, ∀ W', IsComp W' → q ∈ closure W' → W' = U₁ ∨ W' = U₂ := by
    intro i hiA
    obtain ⟨φ, hφ0, hφ1⟩ := hQl i
    let q₀ : S := (φ ⟨1 / 2, by norm_num, by norm_num⟩).1
    have hq₀int : q₀ ∈ Q i \ bd S := by
      refine ⟨(φ _).2, fun hbd => ?_⟩
      have hm : q₀ ∈ Q i ∩ bd S := ⟨(φ _).2, hbd⟩; rw [hQb i] at hm
      rcases hm with hu | hv
      · have h0 : (1 / 2 : ℝ) = 0 := congrArg Subtype.val (φ.injective (Subtype.ext (hu.trans hφ0.symm))); norm_num at h0
      · have h1 : (1 / 2 : ℝ) = 1 := congrArg Subtype.val (φ.injective (Subtype.ext ((mem_singleton_iff.mp hv).trans hφ1.symm))); norm_num at h1
    obtain ⟨bc₀, U₁, U₂, hbc₀0, hU₁c, hU₂c, -, -, hcl1, hcl2, hside0⟩ := hbox_B hiA q₀ hq₀int
    refine ⟨U₁, U₂, ?_⟩
    -- Show `{q ∈ Q i \ bd S | {W' | IsComp W' ∧ q ∈ closure W'} = {U₁, U₂}}` is clopen in connected `Q i \ bd S`!
    let S_pair (q : S) : Set (Set S) := {W' | IsComp W' ∧ q ∈ closure W'}
    have hS0 : S_pair q₀ = {U₁, U₂} := by
      ext W'; constructor
      · rintro ⟨hW'c, hcl⟩; exact hside0 W' hW'c q₀ (hbc₀0.symm ▸ bc₀.center_mem_openBox) hcl
      · rintro (rfl | rfl); exact ⟨hU₁c, hcl1⟩; exact ⟨hU₂c, hcl2⟩
    have hQconn : IsPreconnected (Q i \ bd S) := by
      have heq : Q i \ bd S = (fun r : unitInterval => (φ r).1) '' {r : unitInterval | r.1 ∈ Ioo (0 : ℝ) 1} := by
        ext z; constructor
        · rintro ⟨hzQ, hzbd⟩
          let r := φ.symm ⟨z, hzQ⟩
          refine ⟨r, ⟨lt_of_le_of_ne r.2.1 fun h0 => hzbd ?_, lt_of_le_of_ne r.2.2 fun h1 => hzbd ?_⟩,
            congrArg Subtype.val (φ.apply_symm_apply _)⟩
          · have : z = uQ i := by
              have h : (φ (φ.symm ⟨z, hzQ⟩)).1 = z := congrArg Subtype.val (φ.apply_symm_apply ⟨z, hzQ⟩)
              rw [← h, show φ.symm ⟨z, hzQ⟩ = 0 from Subtype.ext h0.symm]; exact hφ0
            exact this ▸ (hQb i ▸ Or.inl rfl : uQ i ∈ Q i ∩ bd S).2
          · have : z = vQ i := by
              have h : (φ (φ.symm ⟨z, hzQ⟩)).1 = z := congrArg Subtype.val (φ.apply_symm_apply ⟨z, hzQ⟩)
              rw [← h, show φ.symm ⟨z, hzQ⟩ = 1 from Subtype.ext h1]; exact hφ1
            exact this ▸ (hQb i ▸ Or.inr rfl : vQ i ∈ Q i ∩ bd S).2
        · rintro ⟨r, hr, rfl⟩
          refine ⟨(φ r).2, fun hbd => ?_⟩
          have hm : (φ r).1 ∈ Q i ∩ bd S := ⟨(φ r).2, hbd⟩; rw [hQb i] at hm
          rcases hm with hu | hv
          · have h0 : r.1 = 0 := congrArg Subtype.val (φ.injective (Subtype.ext (hu.trans hφ0.symm))); linarith [hr.1]
          · have h1 : r.1 = 1 := congrArg Subtype.val (φ.injective (Subtype.ext ((mem_singleton_iff.mp hv).trans hφ1.symm))); linarith [hr.2]
      rw [heq]
      have hIoo_conn : IsPreconnected {r : unitInterval | r.1 ∈ Ioo (0 : ℝ) 1} := by
        have hsub : {r : unitInterval | r.1 ∈ Ioo (0 : ℝ) 1} =
            (fun x : ℝ => (⟨max 0 (min 1 x), le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩ : unitInterval)) '' Ioo 0 1 := by
          ext r; constructor
          · intro hr; refine ⟨r.1, hr, Subtype.ext ?_⟩; dsimp; rw [min_eq_right hr.2.le, max_eq_right hr.1.le]
          · rintro ⟨x, hx, rfl⟩; dsimp; rw [min_eq_right hx.2.le, max_eq_right hx.1.le]; exact hx
        rw [hsub]; exact isPreconnected_Ioo.image _ (by fun_prop)
      exact hIoo_conn.image _ (continuous_subtype_val.comp φ.continuous).continuousOn
    -- Local constancy of `S_pair` on `Q i \ bd S`:
    have hloc_const : ∀ q ∈ Q i \ bd S, ∃ O, IsOpen O ∧ q ∈ O ∧ ∀ q' ∈ O ∩ (Q i \ bd S), S_pair q' = S_pair q := by
      intro q hq
      obtain ⟨bc, WL, WR, hbc0, hWLc, hWRc, hLsub, hRsub, hclL, hclR, hside⟩ := hbox_B hiA q hq
      refine ⟨bc.openBox, bc.hopen, hbc0.symm ▸ bc.center_mem_openBox, fun q' ⟨hq'O, hq'Q, _⟩ => ?_⟩
      have hSq : S_pair q = {WL, WR} := by
        ext W'; constructor
        · rintro ⟨hW'c, hcl⟩; exact hside W' hW'c q (hbc0.symm ▸ bc.center_mem_openBox) hcl
        · rintro (rfl | rfl); exact ⟨hWLc, hclL⟩; exact ⟨hWRc, hclR⟩
      have hSq' : S_pair q' = {WL, WR} := by
        obtain ⟨z, hz, rfl⟩ := hq'O
        have hz_in : bc.g z ∈ Q i ∩ bc.box := ⟨hq'Q, bc.openBox_subset_box ⟨z, hz, rfl⟩⟩
        rw [BoxChart.box, bc.hA_eq] at hz_in
        obtain ⟨w, hw, hfe⟩ := hz_in; rw [Complex.mem_reProdIm] at hw
        have hwR : w ∈ bc.R := Complex.mem_reProdIm.mpr ⟨by rw [mem_singleton_iff.mp hw.1]; exact ⟨by linarith [bc.ha], bc.ha.le⟩, hw.2⟩
        have hzR : z ∈ bc.R := Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).1, Ioo_subset_Icc_self (Complex.mem_reProdIm.mp hz).2⟩
        have hzw := bc.hgi hzR hwR hfe.symm
        have hzmid : bc.g z ∈ bc.g '' (({0} : Set ℝ) ×ℂ Ioo (-bc.b) bc.b) :=
          ⟨z, Complex.mem_reProdIm.mpr ⟨by rw [hzw]; exact hw.1, (Complex.mem_reProdIm.mp hz).2⟩, rfl⟩
        ext W'; constructor
        · rintro ⟨hW'c, hcl⟩; exact hside W' hW'c (bc.g z) ⟨z, hz, rfl⟩ hcl
        · rintro (rfl | rfl)
          · exact ⟨hWLc, closure_mono (bc.leftHalf_subset_clLeft.trans hLsub) (bc.mid_subset_closure_leftHalf hzmid)⟩
          · exact ⟨hWRc, closure_mono (bc.rightHalf_subset_clRight.trans hRsub) (bc.mid_subset_closure_rightHalf hzmid)⟩
      rw [hSq', hSq]
    let G₁ : Set S := ⋃ (O : Set S) (_ : IsOpen O ∧ ∀ q' ∈ O ∩ (Q i \ bd S), S_pair q' = {U₁, U₂}), O
    let G₂ : Set S := ⋃ (O : Set S) (_ : IsOpen O ∧ ∀ q' ∈ O ∩ (Q i \ bd S), S_pair q' ≠ {U₁, U₂}), O
    have hG₁o : IsOpen G₁ := isOpen_iUnion fun O => isOpen_iUnion fun h => h.1
    have hG₂o : IsOpen G₂ := isOpen_iUnion fun O => isOpen_iUnion fun h => h.1
    have hcov : Q i \ bd S ⊆ G₁ ∪ G₂ := fun q hq => by
      obtain ⟨O, hOo, hqO, hOeq⟩ := hloc_const q hq
      by_cases h : S_pair q = {U₁, U₂}
      · exact Or.inl (mem_iUnion₂.mpr ⟨O, ⟨hOo, fun q' hq' => (hOeq q' hq').trans h⟩, hqO⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨O, ⟨hOo, fun q' hq' => by rw [hOeq q' hq']; exact h⟩, hqO⟩)
    intro q hq W' hW'c hcl
    have hSq : S_pair q = {U₁, U₂} := by
      by_contra hne
      have hqG₂ : q ∈ G₂ := by
        obtain ⟨O, hOo, hqO, hOeq⟩ := hloc_const q hq
        exact mem_iUnion₂.mpr ⟨O, ⟨hOo, fun q' hq' => by rw [hOeq q' hq']; exact hne⟩, hqO⟩
      have hq₀G₁ : q₀ ∈ G₁ := by
        obtain ⟨O, hOo, hqO, hOeq⟩ := hloc_const q₀ hq₀int
        exact mem_iUnion₂.mpr ⟨O, ⟨hOo, fun q' hq' => (hOeq q' hq').trans hS0⟩, hqO⟩
      obtain ⟨z, hzQ, hz1, hz2⟩ := hQconn G₁ G₂ hG₁o hG₂o hcov ⟨q₀, hq₀int, hq₀G₁⟩ ⟨q, hq, hqG₂⟩
      obtain ⟨O₁, ⟨-, h1⟩, hzO₁⟩ := mem_iUnion₂.mp hz1
      obtain ⟨O₂, ⟨-, h2⟩, hzO₂⟩ := mem_iUnion₂.mp hz2
      exact h2 z ⟨hzO₂, hzQ⟩ (h1 z ⟨hzO₁, hzQ⟩)
    have hmem : W' ∈ S_pair q := ⟨hW'c, hcl⟩
    rw [hSq] at hmem; exact hmem
  have hidxs_inj : Function.Injective idxs := by
    have hsame : ∀ r₁ r₂ : Fin k, idxs r₁ = idxs r₂ → r₁.1 < r₂.1 → False := by
      intro r₁ r₂ heq hlt
      obtain ⟨hi1, q₁, hq₁, hcl1L, hcl1R⟩ := hAdj r₁
      obtain ⟨-, q₂, hq₂, hcl2L, hcl2R⟩ := hAdj r₂
      obtain ⟨U₁, U₂, h2⟩ := hQ_at_most_two hi1
      have h1a := h2 q₁ hq₁ (W r₁.castSucc) (hWc _) hcl1L
      have h1b := h2 q₁ hq₁ (W r₁.succ) (hWc _) hcl1R
      have h2b := h2 q₂ (heq ▸ hq₂) (W r₂.succ) (hWc _) hcl2R
      have hne1 : W r₁.castSucc ≠ W r₁.succ := fun h => (Fin.castSucc_lt_succ (i := r₁)).ne (hW_inj h)
      have hne2 : W r₂.succ ≠ W r₁.castSucc := fun h => by
        have := congrArg Fin.val (hW_inj h); simp at this; omega
      have hne3 : W r₂.succ ≠ W r₁.succ := fun h => by
        have := congrArg Fin.val (hW_inj h); simp at this; omega
      rcases h1a with h1a | h1a <;> rcases h1b with h1b | h1b <;> rcases h2b with h2b | h2b
      · exact hne1 (h1a.trans h1b.symm)
      · exact hne1 (h1a.trans h1b.symm)
      · exact hne2 (h2b.trans h1a.symm)
      · exact hne3 (h2b.trans h1b.symm)
      · exact hne3 (h2b.trans h1b.symm)
      · exact hne2 (h2b.trans h1a.symm)
      · exact hne1 (h1a.trans h1b.symm)
      · exact hne1 (h1a.trans h1b.symm)
    intro r₁ r₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact hsame r₁ r₂ heq hlt
    · exact hsame r₂ r₁ heq.symm hlt
  choose q hq using fun r : Fin k => (hAdj r).2
  have hcLR_ne : cL ≠ cR := by
    intro h; subst h
    obtain ⟨p, hp⟩ := compInt_nonempty M cL
    exact Set.disjoint_left.mp (hComp_disj (hWc 0) (hWc (Fin.last k)) hW_ne) (hcL_sub hp) (hcR_sub hp)
  exact ⟨k, hk_pos, W, idxs, q, cL, cR, hWc, hW_inj, hidxs_inj, fun r => (hAdj r).1, hq,
    hcL_sub, hcR_sub, hcLR_ne, hmid_disj⟩

end RedBlueAndChain

/-! ### Section 4: Eliminating `O`-arcs (`eliminate_oArcs`) -/

section EliminateOArcs

/-- Invariant maintained during the `O`-arc elimination loop. -/
def BandSumInv {s t : S} (M : ProperManifold S s t) {m : ℕ} (Q : Fin m → Set S) (A : Finset (Fin m)) : Prop :=
  (∀ j ∈ A, (M.U ∩ Q j).Nonempty ∧ (M.U ∩ Q j).Finite ∧ (M.U ∩ Q j).ncard ≤ 2 ∧ IsSimpleCrossing M.U (Q j)) ∧
  (∀ i : Fin m, i ∉ A → Disjoint M.U (Q i))

/-- One step of `O`-arc elimination: if `M.Os ≠ []` and `BandSumInv M Q A`, merges two distinct
components of `M` via `band_surgery_along_arc` so `M'.Os.length + 1 = M.Os.length`, maintaining
`BandSumInv M' Q A'` for some `A' ⊇ A`. -/
private theorem eliminate_oArcs_step [ConnectedSpace S] (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (hst : s ≠ t) {m : ℕ} {Q : Fin m → Set S} {uQ vQ : Fin m → S}
    (hQb : ∀ j, Q j ∩ bd S = {uQ j, vQ j})
    (hQl : ∀ j, IsLineWithEnds (Q j) (uQ j) (vQ j))
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hQ_disj_st : ∀ j, s ∉ Q j ∧ t ∉ Q j)
    (M : ProperManifold S s t) (hOs : M.Os ≠ [])
    {A : Finset (Fin m)} (hinv : BandSumInv M Q A) :
    ∃ (M' : ProperManifold S s t) (A' : Finset (Fin m)),
      BandSumInv M' Q A' ∧
      M'.Os.length + 1 = M.Os.length ∧
      M'.w1Total AS = M.w1Total AS ∧
      (∀ ωM ωM', IsCrossingCocycle M.U ωM → IsCrossingCocycle M'.U ωM' → BdCohRel s t ωM' ωM) := by
  classical
  have : T2Space S := hS.2.1
  have hQcl : ∀ j, IsClosed (Q j) := fun j => (hQl j).isCompact.isClosed
  let W_all := (bd S)ᶜ \ ⋃ (i : Fin m) (_ : i ∉ A), Q i
  let X_A := M.U ∪ ⋃ (j : Fin m) (_ : j ∈ A), Q j
  have hWall_open : IsOpen W_all := (isClosed_bd S).isOpen_compl.sdiff
    (isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => hQcl i)
  have hXA_cl : IsClosed X_A := M.isClosed_U.union
    (isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => hQcl j)
  have hQall_cl : IsClosed (⋃ j : Fin m, Q j) := isClosed_iUnion_of_finite hQcl
  -- Helper: distinct components `c₁ ≠ c₂` give `hdiff_comp` for points `p₁ ∈ compSet M c₁`, `p₂ ∈ compSet M c₂`:
  have hdiff_of_comp : ∀ {c₁ c₂ : Comp M} {p₁ p₂ : S}, c₁ ≠ c₂ → p₁ ∈ compSet M c₁ → p₂ ∈ compSet M c₂ →
      ¬ (p₁ ∈ M.P₀ ∧ p₂ ∈ M.P₀) ∧ ∀ a ∈ M.Os, ¬ (p₁ ∈ a.O ∧ p₂ ∈ a.O) := by
    intro c₁ c₂ p₁ p₂ hne hp1 hp2
    constructor
    · rintro ⟨h1, h2⟩
      have hc1 : c₁ = none := by by_contra h; exact Set.disjoint_left.mp (compSet_pairwise_disj M h) hp1 h1
      have hc2 : c₂ = none := by by_contra h; exact Set.disjoint_left.mp (compSet_pairwise_disj M h) hp2 h2
      exact hne (hc1.trans hc2.symm)
    · rintro a ha ⟨h1, h2⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
      have hc1 : c₁ = some i := by by_contra h; exact Set.disjoint_left.mp (compSet_pairwise_disj M h) hp1 h1
      have hc2 : c₂ = some i := by by_contra h; exact Set.disjoint_left.mp (compSet_pairwise_disj M h) hp2 h2
      exact hne (hc1.trans hc2.symm)
  -- Helper: from `data : BandArcData S M Q k` with `∀ r, data.idxs r ∉ A`, apply `band_surgery_along_arc` and update `A`:
  have happly_data : ∀ {k : ℕ} (data : BandArcData S M Q k), (∀ r : Fin k, data.idxs r ∉ A) →
      ∃ (M' : ProperManifold S s t) (A' : Finset (Fin m)),
        BandSumInv M' Q A' ∧ M'.Os.length + 1 = M.Os.length ∧ M'.w1Total AS = M.w1Total AS ∧
        (∀ ωM ωM', IsCrossingCocycle M.U ωM → IsCrossingCocycle M'.U ωM' → BdCohRel s t ωM' ωM) := by
    intro k data hnotA
    obtain ⟨M', hlen, hw1, hcoh, hout, hin⟩ := band_surgery_along_arc hS AS hst hQcl M data
    let A' : Finset (Fin m) := A ∪ Finset.image data.idxs Finset.univ
    refine ⟨M', A', ⟨fun j hj => ?_, fun i hi => ?_⟩, hlen, hw1, hcoh⟩
    · rcases Finset.mem_union.mp hj with hjA | hjM
      · have hnotr : j ∉ range data.idxs := by rintro ⟨r, rfl⟩; exact hnotA r hjA
        obtain ⟨heq, hsc⟩ := hout j hnotr
        obtain ⟨hne, hfin, hnc, hsc0⟩ := hinv.1 j hjA
        exact ⟨heq ▸ hne, heq ▸ hfin, heq ▸ hnc, hsc hsc0⟩
      · obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hjM
        exact hin r
    · have hiA : i ∉ A := fun h => hi (Finset.mem_union_left _ h)
      have hnotr : i ∉ range data.idxs := by
        rintro ⟨r, rfl⟩; exact hi (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩))
      obtain ⟨heq, -⟩ := hout i hnotr
      rw [Set.disjoint_iff_inter_eq_empty, heq]
      exact Set.disjoint_iff_inter_eq_empty.mp (hinv.2 i hiA)
  -- Case split: does some component `W` of `W_all` contain two distinct components of `M`?
  by_cases hcase1 : ∃ x₀ ∈ W_all, ∃ c₁ c₂ : Comp M, c₁ ≠ c₂ ∧
      compInt M c₁ ⊆ connectedComponentIn W_all x₀ ∧ compInt M c₂ ⊆ connectedComponentIn W_all x₀
  · -- **CASE 1**: `W` contains `c₁ ≠ c₂` → `k = 0` band surgery!
    obtain ⟨x₀, hx₀, c₁, c₂, hc12, hc₁W, hc₂W⟩ := hcase1
    let W := connectedComponentIn W_all x₀
    have hW_open : IsOpen W := isOpen_connectedComponentIn_of_subset_compl_bd hS hWall_open sdiff_subset hx₀
    have hW_int : W ⊆ (bd S)ᶜ := (connectedComponentIn_subset W_all x₀).trans sdiff_subset
    obtain ⟨y₀, hy₀, ca, cb, hcab, ⟨pL, hpL_pure, hpL_cl⟩, ⟨pR, hpR_pure, hpR_cl⟩⟩ :=
      exists_two_comp_touch hS M hQb hQl hQdisj hQ_disj_st
        (fun j hj => ⟨(hinv.1 j hj).1, (hinv.1 j hj).2.1, (hinv.1 j hj).2.2.2⟩) hinv.2
        ⟨x₀, hx₀, rfl⟩ hc12 hc₁W hc₂W
    let Ω₀ := connectedComponentIn (W \ X_A) y₀
    have hΩ₀_open : IsOpen Ω₀ := isOpen_connectedComponentIn_of_subset_compl_bd hS
      (hW_open.sdiff hXA_cl) (sdiff_subset.trans hW_int) hy₀
    have hΩ₀_conn : IsConnected Ω₀ := ⟨⟨y₀, mem_connectedComponentIn hy₀⟩, isPreconnected_connectedComponentIn⟩
    have hΩ₀_free : Ω₀ ⊆ (bd S)ᶜ \ (M.U ∪ ⋃ j : Fin m, Q j) := fun z hz => by
      have h1 := connectedComponentIn_subset (W \ X_A) y₀ hz
      have h2 := connectedComponentIn_subset W_all x₀ h1.1
      refine ⟨h2.1, ?_⟩
      rintro (hM | hQ); exact h1.2 (Or.inl hM)
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hQ
      by_cases hjA : j ∈ A
      · exact h1.2 (Or.inr (mem_iUnion₂.mpr ⟨j, hjA, hzj⟩))
      · exact h2.2 (mem_iUnion₂.mpr ⟨j, hjA, hzj⟩)
    have hpL_ne_pR : pL ≠ pR := fun h => Set.disjoint_left.mp (compSet_pairwise_disj M hcab) hpL_pure.1 (h ▸ hpR_pure.1)
    have hpL_int : pL ∈ compInt M ca := ⟨hpL_pure.1, fun h => hpL_pure.2 (Or.inl h)⟩
    have hpR_int : pR ∈ compInt M cb := ⟨hpR_pure.1, fun h => hpR_pure.2 (Or.inl h)⟩
    -- Build disjoint `bcL` around `pL` and `bcR` around `pR`, avoiding `⋃ Q`:
    obtain ⟨bcL, hbcL0, hbcLW⟩ := exists_box_on_comp hS M ca hpL_int
      (((isClosed_bd S).isOpen_compl.sdiff hQall_cl).sdiff isClosed_singleton)
      ⟨⟨hpL_int.2, fun h => hpL_pure.2 (Or.inr h)⟩, hpL_ne_pR⟩ (sdiff_subset.trans sdiff_subset)
    have hpR_notL : pR ∉ bcL.box := fun h => (hbcLW h).2 rfl
    obtain ⟨bcR, hbcR0, hbcRW⟩ := exists_box_on_comp hS M cb hpR_int
      (((isClosed_bd S).isOpen_compl.sdiff hQall_cl).sdiff bcL.isClosed_box)
      ⟨⟨hpR_int.2, fun h => hpR_pure.2 (Or.inr h)⟩, hpR_notL⟩ (sdiff_subset.trans sdiff_subset)
    have hL_Ω : (bcL.box ∩ Ω₀).Nonempty := by
      obtain ⟨z, hzV, hzΩ⟩ := mem_closure_iff.mp hpL_cl _ bcL.hopen (hbcL0.symm ▸ bcL.center_mem_openBox)
      exact ⟨z, bcL.openBox_subset_box hzV, hzΩ⟩
    have hR_Ω : (bcR.box ∩ Ω₀).Nonempty := by
      obtain ⟨z, hzV, hzΩ⟩ := mem_closure_iff.mp hpR_cl _ bcR.hopen (hbcR0.symm ▸ bcR.center_mem_openBox)
      exact ⟨z, bcR.openBox_subset_box hzV, hzΩ⟩
    obtain ⟨data, -⟩ := build_bandArcData hS M (k := 0) Fin.elim0
      (fun a => Fin.elim0 a) (fun r => Fin.elim0 r) bcL bcR (fun r => Fin.elim0 r)
      (Set.disjoint_left.mpr fun z hzL hzR => (hbcRW hzR).2 hzL)
      (fun r => Fin.elim0 r) (fun r => Fin.elim0 r) (fun r => Fin.elim0 r)
      (fun j => Set.disjoint_left.mpr fun z hzL hzQ => (hbcLW hzL).1.2 (mem_iUnion.mpr ⟨j, hzQ⟩))
      (fun j => Set.disjoint_left.mpr fun z hzR hzQ => (hbcRW hzR).1.2 (mem_iUnion.mpr ⟨j, hzQ⟩))
      (fun r => Fin.elim0 r) (fun r => Fin.elim0 r)
      (by rw [hbcL0, hbcR0]; exact hdiff_of_comp hcab hpL_pure.1 hpR_pure.1)
      (fun _ => Ω₀) (fun _ => hΩ₀_open) (fun _ => hΩ₀_conn) (fun _ => hΩ₀_free)
      (fun i j hne => (hne ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim)
      hL_Ω hR_Ω (fun r => Fin.elim0 r) (fun r => Fin.elim0 r)
      (fun j hj => (hj (Fin.eq_zero j ▸ rfl)).elim)
      (fun j hj => (hj (Fin.eq_zero j ▸ rfl)).elim) (fun r => Fin.elim0 r)
    exact happly_data data (fun r => Fin.elim0 r)
  · -- **CASE 2**: Every component of `W_all` has `≤ 1` component of `M` → shortest chain with `k ≥ 1`!
    push Not at hcase1
    have huniq_W : ∀ x₀ ∈ W_all, ∀ c₁ c₂ : Comp M,
        compInt M c₁ ⊆ connectedComponentIn W_all x₀ →
        compInt M c₂ ⊆ connectedComponentIn W_all x₀ → c₁ = c₂ := fun x₀ hx₀ c₁ c₂ h1 h2 => by
      by_contra hne; exact hcase1 x₀ hx₀ c₁ c₂ hne h1 h2
    obtain ⟨k, hk_pos, W, idxs, q, cL, cR, hWc, hW_inj, hidxs_inj, hidxs_notA, hq, hcL_sub, hcR_sub, hcLR_ne, hmid_disj⟩ :=
      exists_min_chain hS M hOs hQb hQl hQdisj hQ_disj_st (fun j hj => (hinv.1 j hj).1) hinv.2 huniq_W
    have hW_open : ∀ l, IsOpen (W l) := fun l => by
      obtain ⟨x, hx, heq⟩ := hWc l; exact heq ▸ isOpen_connectedComponentIn_of_subset_compl_bd hS hWall_open sdiff_subset hx
    have hW_conn : ∀ l, IsConnected (W l) := fun l => by
      obtain ⟨x, hx, heq⟩ := hWc l; exact heq ▸ ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩
    have hW_disj : Pairwise fun l₁ l₂ => Disjoint (W l₁) (W l₂) := fun l₁ l₂ hne => by
      obtain ⟨x₁, -, h1⟩ := hWc l₁; obtain ⟨x₂, -, h2⟩ := hWc l₂
      rw [Set.disjoint_left]; intro z hz1 hz2
      apply hne (hW_inj _)
      rw [h1, h2]; rw [h1] at hz1; rw [h2] at hz2
      rw [connectedComponentIn_eq hz1, ← connectedComponentIn_eq hz2]
    have hW_int : ∀ l, W l ⊆ (bd S)ᶜ := fun l => by
      obtain ⟨x, -, heq⟩ := hWc l; exact heq ▸ (connectedComponentIn_subset W_all x).trans sdiff_subset
    -- Step 2a: Build pairwise disjoint oriented `BoxChart`s `bcM r` around `q r ∈ Q (idxs r) \ bd S`
    -- with `clLeftHalf ⊆ W r.castSucc` and `clRightHalf ⊆ W r.succ`!
    -- Since `q r` lie on pairwise disjoint `Q (idxs r)`, build each `bcM r` inside `((bd S)ᶜ \ (M.U ∪ ⋃_{j ≠ idxs r} Q j))`
    -- and note that if we shrink each `bcM r` to avoid `⋃_{j ≠ idxs r} Q j`, wait: boxes on DIFFERENT `Q (idxs r)` can still overlap
    -- unless we make them pairwise disjoint! Shrink them using pairwise open separation of the `k` distinct points `q r`:
    have hq_inj : Function.Injective q := fun r₁ r₂ he => by
      by_contra hne
      exact Set.disjoint_left.mp (hQdisj (hidxs_inj.ne hne)) (hq r₁).1.1 (he ▸ (hq r₂).1.1)
    -- Construct open pairwise-disjoint neighborhoods `U_q r ∋ q r` in `T2Space S`!
    have hex_sep : ∀ (n : ℕ) (pts : Fin n → S), Function.Injective pts →
        ∃ U : Fin n → Set S, (∀ r, IsOpen (U r) ∧ pts r ∈ U r) ∧ Pairwise fun r₁ r₂ => Disjoint (U r₁) (U r₂) := by
      intro n pts hpts
      have hpair : ∀ r₁ r₂ : Fin n, r₁ ≠ r₂ → ∃ u v, IsOpen u ∧ IsOpen v ∧ pts r₁ ∈ u ∧ pts r₂ ∈ v ∧ Disjoint u v :=
        fun r₁ r₂ hne => t2_separation (hpts.ne hne)
      choose u v hu hv h1 h2 hdj using fun r₁ r₂ (h : r₁ ≠ r₂) => hpair r₁ r₂ h
      refine ⟨fun r => ⋂ (r' : Fin n) (h : r ≠ r'), u r r' h ∩ ⋂ (r' : Fin n) (h : r' ≠ r), v r' r h, ?_, ?_⟩
      · intro r
        refine ⟨isOpen_iInter_of_finite fun r' => isOpen_iInter_of_finite fun h => (hu r r' h).inter
            (isOpen_iInter_of_finite fun r'' => isOpen_iInter_of_finite fun h' => hv r'' r h'), ?_⟩
        simp only [mem_iInter, mem_inter_iff]
        exact fun r' h => ⟨h1 r r' h, fun r'' h' => h2 r'' r h'⟩
      · intro r₁ r₂ hne
        rw [Set.disjoint_left]; intro z hz1 hz2
        simp only [mem_iInter, mem_inter_iff] at hz1 hz2
        exact Set.disjoint_left.mp (hdj r₁ r₂ hne) (hz1 r₂ hne).1 ((hz2 r₁ hne.symm).2 r₁ hne)
    obtain ⟨Uq, hUq, hUq_disj⟩ := hex_sep k q hq_inj
    have hbcM_ex : ∀ r : Fin k, ∃ bc : BoxChart S (Q (idxs r)),
        bc.g 0 = q r ∧ bc.box ⊆ Uq r ∧ Disjoint bc.box M.U ∧
        (∀ j : Fin m, j ≠ idxs r → Disjoint bc.box (Q j)) ∧
        bc.clLeftHalf ⊆ W r.castSucc ∧ bc.clRightHalf ⊆ W r.succ := fun r => by
      let Z : Set S := M.U ∪ ⋃ (j : Fin m) (_ : j ≠ idxs r), Q j
      have hZcl : IsClosed Z := M.isClosed_U.union (isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ => hQcl j)
      have hq_notZ : q r ∉ Z := by
        rintro (hM | hQ)
        · exact Set.disjoint_left.mp (hinv.2 (idxs r) (hidxs_notA r)) hM (hq r).1.1
        · obtain ⟨j, hjne, hqj⟩ := mem_iUnion₂.mp hQ; exact Set.disjoint_left.mp (hQdisj hjne) hqj (hq r).1.1
      let W_loc := (Uq r ∩ (bd S)ᶜ) \ Z
      obtain ⟨bc₀, hbc₀0, hbc₀W⟩ := exists_box_on_iArc hS (hQb (idxs r)) (hQl (idxs r)) (hq r).1.1 (hq r).1.2
        (((hUq r).1.inter (isClosed_bd S).isOpen_compl).sdiff hZcl) ⟨⟨(hUq r).2, (hq r).1.2⟩, hq_notZ⟩
        (sdiff_subset.trans inter_subset_right)
      have hhalf_Wall : bc₀.clLeftHalf ⊆ W_all ∧ bc₀.clRightHalf ⊆ W_all := by
        constructor
        · intro z hz
          refine ⟨(hbc₀W (bc₀.clLeftHalf_subset_box hz)).1.2, fun h => ?_⟩
          obtain ⟨j, -, hzj⟩ := mem_iUnion₂.mp h
          by_cases hj : j = idxs r
          · subst hj; exact Set.disjoint_left.mp bc₀.clLeftHalf_disj_A hz hzj
          · exact (hbc₀W (bc₀.clLeftHalf_subset_box hz)).2 (Or.inr (mem_iUnion₂.mpr ⟨j, hj, hzj⟩))
        · intro z hz
          refine ⟨(hbc₀W (bc₀.clRightHalf_subset_box hz)).1.2, fun h => ?_⟩
          obtain ⟨j, -, hzj⟩ := mem_iUnion₂.mp h
          by_cases hj : j = idxs r
          · subst hj; exact Set.disjoint_left.mp bc₀.clRightHalf_disj_A hz hzj
          · exact (hbc₀W (bc₀.clRightHalf_subset_box hz)).2 (Or.inr (mem_iUnion₂.mpr ⟨j, hj, hzj⟩))
      -- Since `q r ∈ closure (W r.castSucc)` and `q r ∈ closure (W r.succ)` and `W r.castSucc ≠ W r.succ`,
      -- one half of `bc₀` lies in `W r.castSucc` and the other in `W r.succ`!
      obtain ⟨uL, huL_open, huL_W⟩ := mem_closure_iff.mp (hq r).2.1 _ bc₀.hopen (hbc₀0.symm ▸ bc₀.center_mem_openBox)
      obtain ⟨uR, huR_open, huR_W⟩ := mem_closure_iff.mp (hq r).2.2 _ bc₀.hopen (hbc₀0.symm ▸ bc₀.center_mem_openBox)
      obtain ⟨xL_w, -, hWL_eq⟩ := hWc r.castSucc
      obtain ⟨xR_w, -, hWR_eq⟩ := hWc r.succ
      have huL_notQ : uL ∉ Q (idxs r) := fun h =>
        (connectedComponentIn_subset W_all xL_w (hWL_eq ▸ huL_W)).2 (mem_iUnion₂.mpr ⟨idxs r, hidxs_notA r, h⟩)
      have huR_notQ : uR ∉ Q (idxs r) := fun h =>
        (connectedComponentIn_subset W_all xR_w (hWR_eq ▸ huR_W)).2 (mem_iUnion₂.mpr ⟨idxs r, hidxs_notA r, h⟩)
      have hdisj_LR_W : Disjoint (W r.castSucc) (W r.succ) := hW_disj (Fin.castSucc_lt_succ (i := r)).ne
      rcases (bc₀.openBox_diff_A ▸ ⟨huL_open, huL_notQ⟩ : uL ∈ bc₀.leftHalf ∪ bc₀.rightHalf) with hL1 | hL2 <;>
      rcases (bc₀.openBox_diff_A ▸ ⟨huR_open, huR_notQ⟩ : uR ∈ bc₀.leftHalf ∪ bc₀.rightHalf) with hR1 | hR2
      · have hLsub : bc₀.clLeftHalf ⊆ W r.castSucc := by
          rw [hWL_eq] at huL_W ⊢; rw [connectedComponentIn_eq huL_W]
          exact bc₀.isConnected_clLeftHalf.isPreconnected.subset_connectedComponentIn (bc₀.leftHalf_subset_clLeft hL1) hhalf_Wall.1
        exact (Set.disjoint_left.mp hdisj_LR_W (hLsub (bc₀.leftHalf_subset_clLeft hR1)) huR_W).elim
      · have hLsub : bc₀.clLeftHalf ⊆ W r.castSucc := by
          rw [hWL_eq] at huL_W ⊢; rw [connectedComponentIn_eq huL_W]
          exact bc₀.isConnected_clLeftHalf.isPreconnected.subset_connectedComponentIn (bc₀.leftHalf_subset_clLeft hL1) hhalf_Wall.1
        have hRsub : bc₀.clRightHalf ⊆ W r.succ := by
          rw [hWR_eq] at huR_W ⊢; rw [connectedComponentIn_eq huR_W]
          exact bc₀.isConnected_clRightHalf.isPreconnected.subset_connectedComponentIn (bc₀.rightHalf_subset_clRight hR2) hhalf_Wall.2
        exact ⟨bc₀, hbc₀0, fun z hz => (hbc₀W hz).1.1,
          Set.disjoint_left.mpr fun z hz hM => (hbc₀W hz).2 (Or.inl hM),
          fun j hjne => Set.disjoint_left.mpr fun z hz hQj => (hbc₀W hz).2 (Or.inr (mem_iUnion₂.mpr ⟨j, hjne, hQj⟩)),
          hLsub, hRsub⟩
      · have hRsub : bc₀.clRightHalf ⊆ W r.castSucc := by
          rw [hWL_eq] at huL_W ⊢; rw [connectedComponentIn_eq huL_W]
          exact bc₀.isConnected_clRightHalf.isPreconnected.subset_connectedComponentIn (bc₀.rightHalf_subset_clRight hL2) hhalf_Wall.2
        have hLsub : bc₀.clLeftHalf ⊆ W r.succ := by
          rw [hWR_eq] at huR_W ⊢; rw [connectedComponentIn_eq huR_W]
          exact bc₀.isConnected_clLeftHalf.isPreconnected.subset_connectedComponentIn (bc₀.leftHalf_subset_clLeft hR1) hhalf_Wall.1
        exact ⟨bc₀.flip, by simp [BoxChart.flip, hbc₀0], fun z hz => (hbc₀W (bc₀.flip_box ▸ hz)).1.1,
          Set.disjoint_left.mpr fun z hz hM => (hbc₀W (bc₀.flip_box ▸ hz)).2 (Or.inl hM),
          fun j hjne => Set.disjoint_left.mpr fun z hz hQj => (hbc₀W (bc₀.flip_box ▸ hz)).2 (Or.inr (mem_iUnion₂.mpr ⟨j, hjne, hQj⟩)),
          bc₀.flip_clLeftHalf.symm ▸ hRsub, bc₀.flip_clRightHalf.symm ▸ hLsub⟩
      · have hRsub : bc₀.clRightHalf ⊆ W r.castSucc := by
          rw [hWL_eq] at huL_W ⊢; rw [connectedComponentIn_eq huL_W]
          exact bc₀.isConnected_clRightHalf.isPreconnected.subset_connectedComponentIn (bc₀.rightHalf_subset_clRight hL2) hhalf_Wall.2
        exact (Set.disjoint_left.mp hdisj_LR_W (hRsub (bc₀.rightHalf_subset_clRight hR2)) huR_W).elim
    choose bcM hbcM0 hbcM_Uq hbcM_M hbcM_Q hbcM_L hbcM_R using hbcM_ex
    -- Step 2b: Choose `Ω 0 ⊆ W 0 \ X_A` containing `(bcM 0).clLeftHalf`, `Ω r = W r` (`1 ≤ r < k`),
    -- and `Ω (Fin.last k) ⊆ W (Fin.last k) \ X_A` containing `(bcM (k-1)).clRightHalf`!
    let r0 : Fin k := ⟨0, hk_pos⟩
    let rlast : Fin k := ⟨k - 1, by omega⟩
    obtain ⟨yL, hyL_half⟩ := (bcM r0).leftHalf_nonempty
    obtain ⟨yR, hyR_half⟩ := (bcM rlast).rightHalf_nonempty
    have hM_clL_notXA : ∀ r : Fin k, Disjoint (bcM r).clLeftHalf X_A := fun r => by
      rw [Set.disjoint_left]; intro z hz hzXA
      rcases hzXA with hM | hQ
      · exact Set.disjoint_left.mp (hbcM_M r) ((bcM r).clLeftHalf_subset_box hz) hM
      · obtain ⟨j, hjA, hzj⟩ := mem_iUnion₂.mp hQ
        exact Set.disjoint_left.mp (hbcM_Q r j fun he => hidxs_notA r (he ▸ hjA)) ((bcM r).clLeftHalf_subset_box hz) hzj
    have hM_clR_notXA : ∀ r : Fin k, Disjoint (bcM r).clRightHalf X_A := fun r => by
      rw [Set.disjoint_left]; intro z hz hzXA
      rcases hzXA with hM | hQ
      · exact Set.disjoint_left.mp (hbcM_M r) ((bcM r).clRightHalf_subset_box hz) hM
      · obtain ⟨j, hjA, hzj⟩ := mem_iUnion₂.mp hQ
        exact Set.disjoint_left.mp (hbcM_Q r j fun he => hidxs_notA r (he ▸ hjA)) ((bcM r).clRightHalf_subset_box hz) hzj
    have hyL_in : yL ∈ W 0 \ X_A :=
      ⟨hbcM_L r0 ((bcM r0).leftHalf_subset_clLeft hyL_half),
       Set.disjoint_left.mp (hM_clL_notXA r0) ((bcM r0).leftHalf_subset_clLeft hyL_half)⟩
    have hyR_in : yR ∈ W (Fin.last k) \ X_A := by
      have hlast : rlast.succ = Fin.last k := Fin.ext (by dsimp [rlast]; omega)
      exact ⟨hlast ▸ hbcM_R rlast ((bcM rlast).rightHalf_subset_clRight hyR_half),
        Set.disjoint_left.mp (hM_clR_notXA rlast) ((bcM rlast).rightHalf_subset_clRight hyR_half)⟩
    let Ω₀ := connectedComponentIn (W 0 \ X_A) yL
    let Ω_last := connectedComponentIn (W (Fin.last k) \ X_A) yR
    let Ω : Fin (k + 1) → Set S := fun l =>
      if l.1 = 0 then Ω₀ else if l.1 = k then Ω_last else W l
    -- By Claim 1 (`exists_owner_of_comp`), `Ω₀` touches `cL'` in `W 0` at `pL`, and `Ω_last` touches `cR'` in `W k` at `pR`!
    obtain ⟨cL', hcL'_W, ⟨pL, hpL_pure, hpL_cl⟩⟩ :=
      exists_owner_of_comp hS M hQb hQl hQdisj hQ_disj_st
        (fun j hj => ⟨(hinv.1 j hj).1, (hinv.1 j hj).2.1, (hinv.1 j hj).2.2.2⟩) hinv.2 (hWc 0) hcL_sub hyL_in
    obtain ⟨cR', hcR'_W, ⟨pR, hpR_pure, hpR_cl⟩⟩ :=
      exists_owner_of_comp hS M hQb hQl hQdisj hQ_disj_st
        (fun j hj => ⟨(hinv.1 j hj).1, (hinv.1 j hj).2.1, (hinv.1 j hj).2.2.2⟩) hinv.2 (hWc (Fin.last k)) hcR_sub hyR_in
    have hcLR'_ne : cL' ≠ cR' := by
      intro h; subst h; obtain ⟨p, hp⟩ := compInt_nonempty M cL'
      exact Set.disjoint_left.mp (hW_disj (Fin.pos_iff_ne_zero.mp hk_pos).symm) (hcL'_W hp) (hcR'_W hp)
    -- Build `bcL ⊆ W 0 \ (⋃ Q ∪ ⋃ r, (bcM r).box)` and `bcR ⊆ W k \ (⋃ Q ∪ ⋃ r, (bcM r).box)`!
    let BM_union : Set S := ⋃ r : Fin k, (bcM r).box
    have hBM_cl : IsClosed BM_union := isClosed_iUnion_of_finite fun r => (bcM r).isClosed_box
    have hpL_notBM : pL ∉ BM_union := fun h => by
      obtain ⟨r, hr⟩ := mem_iUnion.mp h
      exact Set.disjoint_left.mp (hbcM_M r) hr (compSet_subset_U M cL' hpL_pure.1)
    have hpR_notBM : pR ∉ BM_union := fun h => by
      obtain ⟨r, hr⟩ := mem_iUnion.mp h
      exact Set.disjoint_left.mp (hbcM_M r) hr (compSet_subset_U M cR' hpR_pure.1)
    have hpL_int : pL ∈ compInt M cL' := ⟨hpL_pure.1, fun h => hpL_pure.2 (Or.inl h)⟩
    have hpR_int : pR ∈ compInt M cR' := ⟨hpR_pure.1, fun h => hpR_pure.2 (Or.inl h)⟩
    obtain ⟨bcL, hbcL0, hbcLW⟩ := exists_box_on_comp hS M cL' hpL_int
      (((hW_open 0).sdiff hQall_cl).sdiff hBM_cl)
      ⟨⟨hcL'_W hpL_int, fun h => hpL_pure.2 (Or.inr h)⟩, hpL_notBM⟩ (sdiff_subset.trans (sdiff_subset.trans (hW_int 0)))
    obtain ⟨bcR, hbcR0, hbcRW⟩ := exists_box_on_comp hS M cR' hpR_int
      (((hW_open (Fin.last k)).sdiff hQall_cl).sdiff hBM_cl)
      ⟨⟨hcR'_W hpR_int, fun h => hpR_pure.2 (Or.inr h)⟩, hpR_notBM⟩ (sdiff_subset.trans (sdiff_subset.trans (hW_int (Fin.last k))))
    -- Verify all hypotheses of `build_bandArcData`!
    have hΩ_sub_W : ∀ j : Fin (k + 1), Ω j ⊆ W j := fun j => by
      dsimp only [Ω]; split_ifs with h0 hk
      · have hj : j = 0 := Fin.ext h0; subst hj; exact (connectedComponentIn_subset _ yL).trans sdiff_subset
      · have hj : j = Fin.last k := Fin.ext hk; subst hj; exact (connectedComponentIn_subset _ yR).trans sdiff_subset
      · exact subset_rfl
    have hΩ_open : ∀ j : Fin (k + 1), IsOpen (Ω j) := fun j => by
      dsimp only [Ω]; split_ifs with h0 hk
      · exact isOpen_connectedComponentIn_of_subset_compl_bd hS ((hW_open 0).sdiff hXA_cl) (sdiff_subset.trans (hW_int 0)) hyL_in
      · exact isOpen_connectedComponentIn_of_subset_compl_bd hS ((hW_open (Fin.last k)).sdiff hXA_cl) (sdiff_subset.trans (hW_int (Fin.last k))) hyR_in
      · exact hW_open j
    have hΩ_conn : ∀ j : Fin (k + 1), IsConnected (Ω j) := fun j => by
      dsimp only [Ω]; split_ifs with h0 hk
      · exact ⟨⟨yL, mem_connectedComponentIn hyL_in⟩, isPreconnected_connectedComponentIn⟩
      · exact ⟨⟨yR, mem_connectedComponentIn hyR_in⟩, isPreconnected_connectedComponentIn⟩
      · exact hW_conn j
    have hΩ_free : ∀ j : Fin (k + 1), Ω j ⊆ (bd S)ᶜ \ (M.U ∪ ⋃ q : Fin m, Q q) := fun j z hz => by
      have hzW : z ∈ W j := hΩ_sub_W j hz
      obtain ⟨xW, -, hWeq⟩ := hWc j
      have hWall_z := connectedComponentIn_subset W_all xW (hWeq ▸ hzW)
      have hnotXA : z ∉ X_A := by
        dsimp only [Ω] at hz; split_ifs at hz with h0 hk
        · exact (connectedComponentIn_subset _ yL hz).2
        · exact (connectedComponentIn_subset _ yR hz).2
        · exact Set.disjoint_left.mp (hmid_disj j (by omega) (by omega)) hz
      refine ⟨hWall_z.1, ?_⟩
      rintro (hM | hQ); exact hnotXA (Or.inl hM)
      obtain ⟨q, hzq⟩ := mem_iUnion.mp hQ
      by_cases hqA : q ∈ A
      · exact hnotXA (Or.inr (mem_iUnion₂.mpr ⟨q, hqA, hzq⟩))
      · exact hWall_z.2 (mem_iUnion₂.mpr ⟨q, hqA, hzq⟩)
    have hL_Ω : (bcL.box ∩ Ω 0).Nonempty := by
      have h0 : Ω 0 = Ω₀ := by simp [Ω]
      rw [h0]; obtain ⟨z, hzV, hzΩ⟩ := mem_closure_iff.mp hpL_cl _ bcL.hopen (hbcL0.symm ▸ bcL.center_mem_openBox)
      exact ⟨z, bcL.openBox_subset_box hzV, hzΩ⟩
    have hR_Ω : (bcR.box ∩ Ω (Fin.last k)).Nonempty := by
      have hlast : Ω (Fin.last k) = Ω_last := by simp [Ω, hk_pos.ne']
      rw [hlast]; obtain ⟨z, hzV, hzΩ⟩ := mem_closure_iff.mp hpR_cl _ bcR.hopen (hbcR0.symm ▸ bcR.center_mem_openBox)
      exact ⟨z, bcR.openBox_subset_box hzV, hzΩ⟩
    have hM_left_Ω : ∀ r : Fin k, (bcM r).clLeftHalf ⊆ Ω r.castSucc := fun r => by
      dsimp only [Ω]; split_ifs with h0 hk
      · have hr : r = r0 := Fin.ext h0; subst hr
        exact (bcM r0).isConnected_clLeftHalf.isPreconnected.subset_connectedComponentIn
          ((bcM r0).leftHalf_subset_clLeft hyL_half)
          (fun z hz => ⟨hbcM_L r0 hz, Set.disjoint_left.mp (hM_clL_notXA r0) hz⟩)
      · exfalso; simp at hk; omega
      · exact hbcM_L r
    have hM_right_Ω : ∀ r : Fin k, (bcM r).clRightHalf ⊆ Ω r.succ := fun r => by
      dsimp only [Ω]; split_ifs with h0 hk
      · exfalso; simp at h0
      · have hr : r = rlast := Fin.ext (by simp at hk; dsimp [rlast]; omega); subst hr
        have hlast : rlast.succ = Fin.last k := Fin.ext (by dsimp [rlast]; omega)
        exact (bcM rlast).isConnected_clRightHalf.isPreconnected.subset_connectedComponentIn
          ((bcM rlast).rightHalf_subset_clRight hyR_half)
          (fun z hz => ⟨hlast ▸ hbcM_R rlast hz, Set.disjoint_left.mp (hM_clR_notXA rlast) hz⟩)
      · exact hbcM_R r
    have hM_box_sub : ∀ r : Fin k, (bcM r).box ⊆ Q (idxs r) ∪ W r.castSucc ∪ W r.succ := by
      intro r; rintro z ⟨w, hw, rfl⟩
      rw [Complex.mem_reProdIm] at hw
      rcases lt_trichotomy w.re 0 with hlt | heq | hgt
      · exact Or.inl (Or.inr (hbcM_L r ⟨w, Complex.mem_reProdIm.mpr ⟨⟨hw.1.1, hlt⟩, hw.2⟩, rfl⟩))
      · exact Or.inl (Or.inl (show (bcM r).g w ∈ Q (idxs r) ∩ (bcM r).box by
          rw [BoxChart.box, (bcM r).hA_eq]; exact ⟨w, Complex.mem_reProdIm.mpr ⟨heq, hw.2⟩, rfl⟩).1)
      · exact Or.inr (hbcM_R r ⟨w, Complex.mem_reProdIm.mpr ⟨⟨hgt, hw.1.2⟩, hw.2⟩, rfl⟩)
    obtain ⟨data, hdata_idxs⟩ := build_bandArcData hS M idxs hidxs_inj (fun r => hinv.2 (idxs r) (hidxs_notA r))
      bcL bcR bcM
      (Set.disjoint_left.mpr fun z hzL hzR =>
        Set.disjoint_left.mp (hW_disj (Fin.pos_iff_ne_zero.mp hk_pos).symm) (hbcLW hzL).1.1 (hbcRW hzR).1.1)
      (fun r => Set.disjoint_left.mpr fun z hzL hzM => (hbcLW hzL).2 (mem_iUnion.mpr ⟨r, hzM⟩))
      (fun r => Set.disjoint_left.mpr fun z hzR hzM => (hbcRW hzR).2 (mem_iUnion.mpr ⟨r, hzM⟩))
      (fun r₁ r₂ hne => (hUq_disj hne).mono (hbcM_Uq r₁) (hbcM_Uq r₂))
      (fun j => Set.disjoint_left.mpr fun z hzL hzQ => (hbcLW hzL).1.2 (mem_iUnion.mpr ⟨j, hzQ⟩))
      (fun j => Set.disjoint_left.mpr fun z hzR hzQ => (hbcRW hzR).1.2 (mem_iUnion.mpr ⟨j, hzQ⟩))
      hbcM_M hbcM_Q
      (by rw [hbcL0, hbcR0]; exact hdiff_of_comp hcLR'_ne hpL_pure.1 hpR_pure.1)
      Ω hΩ_open hΩ_conn hΩ_free (fun j₁ j₂ hne => (hW_disj hne).mono (hΩ_sub_W j₁) (hΩ_sub_W j₂))
      hL_Ω hR_Ω hM_left_Ω hM_right_Ω
      (fun j hj0 => Set.disjoint_left.mpr fun z hzL hzΩ =>
        Set.disjoint_left.mp (hW_disj (show (0 : Fin (k + 1)) ≠ j from fun h => hj0 (congrArg Fin.val h).symm))
          (hbcLW hzL).1.1 (hΩ_sub_W j hzΩ))
      (fun j hjk => Set.disjoint_left.mpr fun z hzR hzΩ =>
        Set.disjoint_left.mp (hW_disj (show Fin.last k ≠ j from fun h => hjk (congrArg Fin.val h).symm))
          (hbcRW hzR).1.1 (hΩ_sub_W j hzΩ))
      (fun r j hj1 hj2 => Set.disjoint_left.mpr fun z hzM hzΩ => by
        rcases hM_box_sub r hzM with (hzQ | hzWL) | hzWR
        · exact (hΩ_free j hzΩ).2 (Or.inr (mem_iUnion.mpr ⟨idxs r, hzQ⟩))
        · exact Set.disjoint_left.mp (hW_disj (show r.castSucc ≠ j from fun h => hj1 (congrArg Fin.val h).symm)) hzWL (hΩ_sub_W j hzΩ)
        · exact Set.disjoint_left.mp (hW_disj (show r.succ ≠ j from fun h => hj2 (congrArg Fin.val h).symm)) hzWR (hΩ_sub_W j hzΩ))
    exact happly_data data (hdata_idxs ▸ hidxs_notA)

/-- **Eliminating all `O`-arcs**: starting from any `ProperManifold` `M` satisfying `BandSumInv M Q A`,
iteratively applies `eliminate_oArcs_step` until `M.Os = []`, yielding a single proper `I`-arc `P'`
with `|P' ∩ Q i| ≤ 2` for every `i`, the same `w1` integral, and `BdCohRel s t`. -/
theorem eliminate_oArcs [ConnectedSpace S] (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (hst : s ≠ t) {m : ℕ} {Q : Fin m → Set S} {uQ vQ : Fin m → S}
    (hQb : ∀ j, Q j ∩ bd S = {uQ j, vQ j})
    (hQl : ∀ j, IsLineWithEnds (Q j) (uQ j) (vQ j))
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hQ_disj_st : ∀ j, s ∉ Q j ∧ t ∉ Q j)
    (M : ProperManifold S s t) {A : Finset (Fin m)} (hinv : BandSumInv M Q A) :
    ∃ (P' : Set S) (γ' : ℝ → S) (hP'b : P' ∩ bd S = {s, t}) (hP'l : IsLineWithEnds P' s t),
      ContinuousOn γ' (Icc 0 1) ∧ InjOn γ' (Icc 0 1) ∧ γ' 0 = s ∧ γ' 1 = t ∧ γ' '' Icc 0 1 = P' ∧
      cocInt (w1 AS) γ' = M.w1Total AS ∧
      (∀ ωM, IsCrossingCocycle M.U ωM → BdCohRel s t (arcCocycle hS hst hP'b hP'l) ωM) ∧
      (∀ i : Fin m, (P' ∩ Q i).Finite ∧ (P' ∩ Q i).ncard ≤ 2 ∧ IsSimpleCrossing P' (Q i)) := by
  have hind : ∀ (n : ℕ) (M : ProperManifold S s t) (A : Finset (Fin m)),
      M.Os.length = n → BandSumInv M Q A →
      ∃ (P' : Set S) (γ' : ℝ → S) (hP'b : P' ∩ bd S = {s, t}) (hP'l : IsLineWithEnds P' s t),
        ContinuousOn γ' (Icc 0 1) ∧ InjOn γ' (Icc 0 1) ∧ γ' 0 = s ∧ γ' 1 = t ∧ γ' '' Icc 0 1 = P' ∧
        cocInt (w1 AS) γ' = M.w1Total AS ∧
        (∀ ωM, IsCrossingCocycle M.U ωM → BdCohRel s t (arcCocycle hS hst hP'b hP'l) ωM) ∧
        (∀ i : Fin m, (P' ∩ Q i).Finite ∧ (P' ∩ Q i).ncard ≤ 2 ∧ IsSimpleCrossing P' (Q i)) := by
    intro n
    induction n with
    | zero =>
      intro M A hlen hinv
      have hOs : M.Os = [] := List.eq_nil_of_length_eq_zero hlen
      have hMU : M.U = M.P₀ := by simp [ProperManifold.U, ProperManifold.listUnion, hOs]
      have hw1 : cocInt (w1 AS) M.γ₀ = M.w1Total AS := by simp [ProperManifold.w1Total, hOs]
      refine ⟨M.P₀, M.γ₀, M.hP₀b, M.hP₀l, M.hγ₀c, M.hγ₀i, M.hγ₀0, M.hγ₀1, M.hγ₀im, hw1, ?_, ?_⟩
      · intro ωM hωM
        have : T2Space S := hS.2.1
        obtain ⟨z₀, hz₀⟩ := compInt_nonempty M none
        have hint0 : IsInteriorPoint z₀ := not_not.mp hz₀.2
        obtain ⟨U, h, g, c, hUsub, -⟩ := hint0.exists_ballChart (isClosed_bd S).isOpen_compl hz₀.2 (R := 2) (by norm_num)
        have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 2 := closedBall_subset_ball (by norm_num)
        have hΔ : IsClosedDisc (g '' closedBall (0 : ℂ) 1) :=
          (c.image_disc (isClosedDisc_closedBall_of_pos (0 : ℂ) one_pos).1 hsub).1
        have hΔint : g '' closedBall (0 : ℂ) 1 ⊆ (bd S)ᶜ := by rintro _ ⟨w, hw, rfl⟩; exact hUsub (c.gm (hsub hw))
        have hωP := (arcCocycle_isCrossingCocycle hS hst M.hP₀b M.hP₀l).1
        exact bdCohRel_of_agree_outside_disc hS M.isClosed_U hΔ hΔint M.U_inter_bd rfl
          (fun z hz => (M.exists_crossingCocycle hS hst).2 z hz.1) (hMU.symm ▸ hωP) hωM
      · intro i
        by_cases hiA : i ∈ A
        · obtain ⟨-, hfin, hnc, hsc⟩ := hinv.1 i hiA
          exact ⟨hMU ▸ hfin, hMU ▸ hnc, hMU ▸ hsc⟩
        · have hempty : M.P₀ ∩ Q i = ∅ := Set.disjoint_iff_inter_eq_empty.mp (hMU ▸ hinv.2 i hiA)
          refine ⟨by rw [hempty]; exact finite_empty, by rw [hempty]; simp, fun p hp => (hempty ▸ hp).elim⟩
    | succ n ih =>
      intro M A hlen hinv
      have hOs : M.Os ≠ [] := fun h => by simp [h] at hlen
      obtain ⟨M₁, A₁, hinv₁, hlen₁, hw1₁, hcoh₁⟩ :=
        eliminate_oArcs_step hS AS hst hQb hQl hQdisj hQ_disj_st M hOs hinv
      obtain ⟨P', γ', hP'b, hP'l, hγ'c, hγ'i, hγ'0, hγ'1, hγ'im, hw1', hcoh', hcard⟩ :=
        ih M₁ A₁ (by omega) hinv₁
      obtain ⟨⟨ω₁, hω₁⟩, -⟩ := M₁.exists_crossingCocycle hS hst
      exact ⟨P', γ', hP'b, hP'l, hγ'c, hγ'i, hγ'0, hγ'1, hγ'im, hw1'.trans hw1₁,
        fun ωM hωM => bdCohRel_trans (hcoh' ω₁ hω₁) (hcoh₁ ωM ω₁ hωM hω₁), hcard⟩
  exact hind M.Os.length M A rfl hinv

/-- Entry point from `parity_surgery`: given a transverse `ProperManifold` `M` with `|X i| ≤ 1`
for every `i`, eliminates all `O`-arcs to obtain a single proper `I`-arc `P'` meeting every `Q i`
in at most `2` points with simple crossings. -/
theorem eliminate_oArcs_of_transverse [ConnectedSpace S] (hS : IsSurface S) (AS : SurfAtlas S)
    {s t : S} (hst : s ≠ t) {m : ℕ} {Q : Fin m → Set S} {uQ vQ : Fin m → S}
    (hQb : ∀ j, Q j ∩ bd S = {uQ j, vQ j})
    (hQl : ∀ j, IsLineWithEnds (Q j) (uQ j) (vQ j))
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hQ_disj_st : ∀ j, s ∉ Q j ∧ t ∉ Q j)
    {sb : StripBox S Q} (M : ProperManifold S s t) {X : Fin m → Finset ℝ}
    (htr : M.IsTransverse sb X) (hcard : ∀ i : Fin m, (X i).card ≤ 1) :
    ∃ (P' : Set S) (γ' : ℝ → S) (hP'b : P' ∩ bd S = {s, t}) (hP'l : IsLineWithEnds P' s t),
      ContinuousOn γ' (Icc 0 1) ∧ InjOn γ' (Icc 0 1) ∧ γ' 0 = s ∧ γ' 1 = t ∧ γ' '' Icc 0 1 = P' ∧
      cocInt (w1 AS) γ' = M.w1Total AS ∧
      (∀ ωM, IsCrossingCocycle M.U ωM → BdCohRel s t (arcCocycle hS hst hP'b hP'l) ωM) ∧
      (∀ i : Fin m, (P' ∩ Q i).Finite ∧ (P' ∩ Q i).ncard ≤ 2 ∧ IsSimpleCrossing P' (Q i)) := by
  classical
  let A₀ : Finset (Fin m) := Finset.univ.filter fun i => (X i).Nonempty
  have hinv : BandSumInv M Q A₀ := by
    refine ⟨fun j hj => ?_, fun i hi => ?_⟩
    · have hneX : (X j).Nonempty := (Finset.mem_filter.mp hj).2
      rw [htr.inter_Q_eq j]
      refine ⟨(Finset.coe_nonempty.mpr hneX).image _, (X j).finite_toSet.image _, ?_,
        htr.isSimpleCrossing hS j⟩
      calc ((fun x : ℝ => sb.f j (x : ℂ)) '' (X j : Set ℝ)).ncard
          ≤ (X j : Set ℝ).ncard := Set.ncard_image_le (X j).finite_toSet
        _ = (X j).card := Set.ncard_coe_finset (X j)
        _ ≤ 1 := hcard j
        _ ≤ 2 := by norm_num
    · have hempty : X i = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun hne =>
        hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      rw [Set.disjoint_iff_inter_eq_empty, htr.inter_Q_eq i, hempty]; simp
  exact eliminate_oArcs hS AS hst hQb hQl hQdisj hQ_disj_st M hinv

end EliminateOArcs

end GraphMinor.GHR18
