module

public import GraphMinor.GM21.Section6Move
public import GraphMinor.GM19.Defs2
import GraphMinor.GM19.Perimeter
import GraphMinor.GM21.Section6ClaimThreeFind
import GraphMinor.GM21.Section6Induction
import GraphMinor.Surface.Collar

/-!
# Graph Minors XXI, (6.3), the last step: the new disc

The paper ends the proof of (6.3) (page 29 of the preprint) with: "By extending $\Delta$ to a sphere
and removing $R \setminus bd(R)$ from it, we deduce that $G$ has a presentation in a disc $\Sigma'$,
with depth $\le q$ and defect $\le r$."

Here `Σ` has one cuff `bd(Σ)`, `Σ̂` is the capped surface, `j : Σ → Σ̂` is the embedding, and `R`
is the closure of the pasted disc, so that `bd(R) = j(bd(Σ))`. Let `X ⊇ R ∪ j(U(Γ))` be a closed
disc of `Σ̂`. We use `R` itself as the new disc `Σ'`. This is the paper's construction turned inside
out: the sphere `Δ ∪ Δ'` minus `R \ bd(R)` is a disc with boundary `bd(R)`, and so is `R`.

To put `Γ` into `R`, take a closed disc `Δ'` whose interior holds `X` (`exists_disc_around`) and
coordinates `c` on `Δ'` by the disc of radius `2`, in which `R` is the unit disc
(`exists_disc_collar`). Then `j(Σ) ∩ Δ'` is the annulus `1 ≤ |z| ≤ 2`, and the inversion
`z ↦ z / |z|²` maps it onto the annulus `1/2 ≤ |z| ≤ 1` of `R`, fixing the unit circle `bd(R)`.
This gives a `Move` from `Σ` to `R` (`exists_move`), and `Move.presentationHasDepthLe_image` moves
the presentation.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace LastStep

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM19

/-- The inversion in the unit circle, `w ↦ w / |w|²`. -/
noncomputable def inv (w : ℂ) : ℂ := ((‖w‖ ^ 2)⁻¹ : ℝ) • w

/-- The inversion outside the unit disc, and the identity inside it. -/
noncomputable def fold (z : ℂ) : ℂ := ((max 1 ‖z‖ ^ 2)⁻¹ : ℝ) • z

theorem norm_inv {w : ℂ} (hw : w ≠ 0) : ‖inv w‖ = ‖w‖⁻¹ := by
  have : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [inv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

theorem inv_inv' {w : ℂ} (hw : w ≠ 0) : inv (inv w) = w := by
  have h0 : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hn := norm_inv hw
  rw [inv, hn, inv, smul_smul]
  have : (‖w‖⁻¹ ^ 2)⁻¹ * (‖w‖ ^ 2)⁻¹ = 1 := by field_simp
  rw [this, one_smul]

theorem fold_eq_inv {z : ℂ} (hz : 1 ≤ ‖z‖) : fold z = inv z := by
  rw [fold, inv, max_eq_right hz]

theorem fold_eq_self {z : ℂ} (hz : ‖z‖ ≤ 1) : fold z = z := by
  rw [fold, max_eq_left hz]
  simp

theorem norm_fold_le (z : ℂ) : ‖fold z‖ ≤ 1 := by
  rcases le_total ‖z‖ 1 with h | h
  · rwa [fold_eq_self h]
  · have hz : z ≠ 0 := norm_pos_iff.1 (by linarith)
    rw [fold_eq_inv h, norm_inv hz]
    exact inv_le_one_of_one_le₀ h

theorem continuous_fold : Continuous fold := by
  unfold fold
  refine Continuous.smul (Continuous.inv₀ ((continuous_const.max continuous_norm).pow 2)
    fun z => ?_) continuous_id
  have : 0 < max 1 ‖z‖ := lt_max_of_lt_left one_pos
  exact pow_ne_zero 2 this.ne'

theorem continuousOn_inv : ContinuousOn inv {w | w ≠ 0} := by
  unfold inv
  refine ContinuousOn.smul (ContinuousOn.inv₀ (continuous_norm.pow 2).continuousOn
    fun w hw => ?_) continuousOn_id
  have : 0 < ‖w‖ := norm_pos_iff.2 hw
  exact pow_ne_zero 2 this.ne'

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]

/-- With one cuff, a set of `Σ̂` that meets the closed pasted disc `R` only in `bd(R)` lies in the
image of `Σ`: the rest of `Σ̂` is the open pasted disc, which lies in `R \ bd(R)`. -/
theorem subset_range_of_inter (cap : IsCappedSurface S Shat)
    (hC : bd S ∈ cuffs S) {Y : Set Shat}
    (hY : Y ∩ closure (cap.cuffDisc (bd S)) ⊆ discBd (closure (cap.cuffDisc (bd S)))) :
    Y ⊆ range cap.emb := by
  intro y hy
  by_contra hyr
  have hy' : y ∈ (range cap.emb)ᶜ := hyr
  rw [cap.compl_eq] at hy'
  obtain ⟨C', hC', hyC'⟩ := mem_iUnion₂.1 hy'
  have hC'eq : C' = bd S := by
    obtain ⟨x, hx, rfl⟩ := id hC'
    exact Induction.eq_of_mem_cuffs_of_mem hC' hC (mem_connectedComponentIn hx) hx
  rw [hC'eq] at hyC'
  have hyb := hY ⟨hy, subset_closure hyC'⟩
  rw [cap.cuffDisc_bd _ hC] at hyb
  obtain ⟨z, -, rfl⟩ := hyb
  exact hyr (mem_range_self z)

/-- **The move to the new disc.** Let `Σ` have one cuff, and let `X ⊇ R ∪ j(U)` be a closed disc of
`Σ̂`, where `U ⊆ Σ`. Then there is a `Move` from `Σ` to the closed disc `R` whose domain holds `U`.
-/
theorem exists_move (hS : IsSurface S) (cap : IsCappedSurface S Shat) (hC : bd S ∈ cuffs S)
    {X : Set Shat} (hX : IsClosedDisc X) (hRX : closure (cap.cuffDisc (bd S)) ⊆ X) {U : Set S}
    (hUX : cap.emb '' U ⊆ X) :
    ∃ (ψ : S → closure (cap.cuffDisc (bd S))) (φ : closure (cap.cuffDisc (bd S)) → S)
      (K : Set S) (K' : Set (closure (cap.cuffDisc (bd S)))), Move ψ φ K K' ∧ U ⊆ K := by
  classical
  have : T2Space Shat := cap.isSurface.2.1
  have : T2Space S := hS.2.1
  set j := cap.emb with hj_def
  set R := closure (cap.cuffDisc (bd S)) with hR_def
  have hR : IsClosedDisc R := cap.cuffDisc_closedDisc _ hC
  have hRbd : discBd R = j '' bd S := cap.cuffDisc_bd _ hC
  have hemb : IsEmbedding j := cap.isEmbedding
  have hinj := hemb.injective
  have hembR : ∀ {z : S}, j z ∈ R → z ∈ bd S := fun hz =>
    ClaimThree.mem_of_emb_mem_closure_cuffDisc hS cap hC hz
  -- A closed disc `Δ'` whose interior holds `X`, and the coordinates `c` on it.
  obtain ⟨D, hD, hXD, -⟩ := exists_disc_around cap.isSurface.2.2 hX
    (fun x _ => cap.isClosedSurface.2.2 x) isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := hR.isOArc_discBd
  obtain ⟨c, c', hc, hc', hcm, hc'm, hcl, hcr, hc1, -, hcp⟩ :=
    exists_disc_collar hR hD (hRX.trans fun x hx => hXD hx) p
  have hRD : R ⊆ D := fun x hx => (hXD (hRX hx)).1
  have hcinj : InjOn c (closedBall 0 2) := hcl.injOn
  have hball : closedBall (0 : ℂ) 1 ⊆ closedBall 0 2 := closedBall_subset_closedBall one_le_two
  have hsph : c '' sphere 0 1 = discBd R := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz
      have hzc : c z = (p ⟨z, hz⟩).1 := hcp ⟨z, hz⟩
      rw [hzc]
      exact (p _).2
    · intro hy
      obtain ⟨w, hw⟩ := p.surjective ⟨y, hy⟩
      refine ⟨w, mem_sphere_zero_iff_norm.2 (Circle.norm_coe w), ?_⟩
      rw [hcp, hw]
  -- `c` maps the unit disc onto `R`, and nothing else of the disc of radius `2` into `R`.
  have hcR : ∀ {z : ℂ}, z ∈ closedBall 0 2 → (c z ∈ R ↔ ‖z‖ ≤ 1) := by
    intro z hz
    constructor
    · intro hzR
      rw [← hc1] at hzR
      obtain ⟨v, hv, hve⟩ := hzR
      rw [← hcinj (hball hv) hz hve]
      exact mem_closedBall_zero_iff.1 hv
    · intro h1
      rw [← hc1]
      exact mem_image_of_mem c (mem_closedBall_zero_iff.2 h1)
  have hcc' : ∀ {y}, y ∈ D → c (c' y) = y := fun hy => hcr hy
  have hc'c : ∀ {z}, z ∈ closedBall (0 : ℂ) 2 → c' (c z) = z := fun hz => hcl hz
  -- A point of `j(Σ) ∩ Δ'` has coordinate of norm at least `1`.
  have hge : ∀ {x : S}, j x ∈ D → 1 ≤ ‖c' (j x)‖ := by
    intro x hx
    by_contra hlt
    push Not at hlt
    have hz := hc'm hx
    have hxR : j x ∈ R := by rw [← hcc' hx]; exact (hcR hz).2 hlt.le
    have hxb : j x ∈ discBd R := by rw [hRbd]; exact mem_image_of_mem j (hembR hxR)
    rw [← hsph] at hxb
    obtain ⟨v, hv, hve⟩ := hxb
    have hv2 : v ∈ closedBall (0 : ℂ) 2 := hball (sphere_subset_closedBall hv)
    rw [← hcc' hx] at hve
    have := hcinj hv2 hz hve
    rw [← this, mem_sphere_zero_iff_norm.1 hv] at hlt
    exact lt_irrefl _ hlt
  -- The points of `Δ'` outside the open disc `R \ bd(R)` are in `j(Σ)`.
  have hrange : ∀ {y}, y ∈ D → (y ∈ R → y ∈ discBd R) → y ∈ range j := by
    intro y hyD hyR
    refine subset_range_of_inter cap hC (Y := {y}) (fun z hz => ?_) rfl
    rw [mem_singleton_iff.1 hz.1]
    exact hyR (mem_singleton_iff.1 hz.1 ▸ hz.2)
  have hne : Nonempty S := by
    obtain ⟨x, -, -⟩ := hC
    exact ⟨x⟩
  -- The two maps.
  have hfoldR : ∀ z : ℂ, c (fold z) ∈ R := fun z =>
    (hcR (hball (mem_closedBall_zero_iff.2 (norm_fold_le z)))).2 (norm_fold_le z)
  let ψ : S → R := fun x => ⟨c (fold (c' (j x))), hfoldR _⟩
  let φ : R → S := fun y => invFun j (c (inv (c' y.1)))
  let K : Set S := j ⁻¹' D
  let K' : Set R := {y | 1 / 2 ≤ ‖c' y.1‖}
  -- Facts about a point `y` of `K'`.
  have hK'w : ∀ {y : R}, y ∈ K' → c' y.1 ≠ 0 ∧ ‖c' y.1‖ ≤ 1 := by
    intro y hy
    refine ⟨fun h0 => ?_, ?_⟩
    · have : (1 / 2 : ℝ) ≤ ‖c' y.1‖ := hy
      rw [h0, norm_zero] at this
      norm_num at this
    · have hyD : y.1 ∈ D := hRD y.2
      have := (hcR (hc'm hyD)).1 (by rw [hcc' hyD]; exact y.2)
      exact this
  have hK'inv : ∀ {y : R}, y ∈ K' → 1 ≤ ‖inv (c' y.1)‖ ∧ ‖inv (c' y.1)‖ ≤ 2 := by
    intro y hy
    obtain ⟨h0, h1⟩ := hK'w hy
    have h2 : (1 / 2 : ℝ) ≤ ‖c' y.1‖ := hy
    have hpos : 0 < ‖c' y.1‖ := norm_pos_iff.2 h0
    rw [norm_inv h0]
    refine ⟨one_le_inv₀ hpos |>.2 h1, ?_⟩
    rw [inv_le_comm₀ hpos two_pos]
    linarith
  have hK'range : ∀ {y : R}, y ∈ K' → c (inv (c' y.1)) ∈ D ∧ c (inv (c' y.1)) ∈ range j := by
    intro y hy
    obtain ⟨h1, h2⟩ := hK'inv hy
    have hb : inv (c' y.1) ∈ closedBall (0 : ℂ) 2 := mem_closedBall_zero_iff.2 h2
    refine ⟨hcm hb, hrange (hcm hb) fun hR' => ?_⟩
    have hle := (hcR hb).1 hR'
    rw [← hsph]
    exact mem_image_of_mem c (mem_sphere_zero_iff_norm.2 (le_antisymm hle h1))
  have hjφ : ∀ {y : R}, y ∈ K' → j (φ y) = c (inv (c' y.1)) := fun hy =>
    invFun_eq (hK'range hy).2
  have hψv : ∀ x, (ψ x).1 = c (fold (c' (j x))) := fun _ => rfl
  refine ⟨ψ, φ, K, K', ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, fun x hx => hXD (hUX ⟨x, hx, rfl⟩) |>.1⟩
  · exact hD.isClosed.preimage hemb.continuous
  · exact isClosed_le continuous_const
      (continuous_norm.comp (hc'.comp_continuous continuous_subtype_val fun y => hRD y.2))
  · -- `ψ` maps `K` into `K'`.
    intro x hx
    have h1 := hge hx
    have hz0 : c' (j x) ≠ 0 := norm_pos_iff.1 (by linarith)
    have hb : fold (c' (j x)) ∈ closedBall (0 : ℂ) 2 :=
      hball (mem_closedBall_zero_iff.2 (norm_fold_le _))
    show 1 / 2 ≤ ‖c' (c (fold (c' (j x))))‖
    rw [hc'c hb, fold_eq_inv h1, norm_inv hz0, inv_eq_one_div]
    · exact one_div_le_one_div_of_le (norm_pos_iff.2 hz0) (mem_closedBall_zero_iff.1 (hc'm hx))
  · -- `φ` maps `K'` into `K`.
    intro y hy
    show j (φ y) ∈ D
    rw [hjφ hy]
    exact (hK'range hy).1
  · -- `φ ∘ ψ = id` on `K`.
    intro x hx
    have h1 := hge hx
    have hz0 : c' (j x) ≠ 0 := norm_pos_iff.1 (by linarith)
    have hb : fold (c' (j x)) ∈ closedBall (0 : ℂ) 2 :=
      hball (mem_closedBall_zero_iff.2 (norm_fold_le _))
    show invFun j (c (inv (c' (c (fold (c' (j x))))))) = x
    rw [hc'c hb, fold_eq_inv h1, inv_inv' hz0, hcc' hx]
    exact leftInverse_invFun hinj x
  · -- `ψ ∘ φ = id` on `K'`.
    intro y hy
    apply Subtype.ext
    obtain ⟨h0, -⟩ := hK'w hy
    obtain ⟨h1, h2⟩ := hK'inv hy
    rw [hψv, hjφ hy, hc'c (mem_closedBall_zero_iff.2 h2), fold_eq_inv h1, inv_inv' h0,
      hcc' (hRD y.2)]
  · -- `ψ` is continuous on `K`.
    refine IsInducing.subtypeVal.continuousOn_iff.2 ?_
    have hj : ContinuousOn (fun x => c' (j x)) K :=
      hc'.comp hemb.continuous.continuousOn fun x hx => hx
    exact hc.comp (continuous_fold.comp_continuousOn hj) fun x _ =>
      hball (mem_closedBall_zero_iff.2 (norm_fold_le _))
  · -- `φ` is continuous on `K'`.
    refine hemb.isInducing.continuousOn_iff.2 ?_
    have hg : ContinuousOn (fun y : R => c (inv (c' y.1))) K' := by
      have h1 : ContinuousOn (fun y : R => c' y.1) K' :=
        (hc'.comp_continuous continuous_subtype_val fun y => hRD y.2).continuousOn
      have h2 : ContinuousOn (fun y : R => inv (c' y.1)) K' :=
        continuousOn_inv.comp h1 fun y hy => (hK'w hy).1
      exact hc.comp h2 fun y hy => mem_closedBall_zero_iff.2 (hK'inv hy).2
    exact hg.congr fun y hy => hjφ hy
  · -- `bd(Σ) ⊆ K`.
    intro x hx
    exact hRD (discBd_subset R (hRbd ▸ mem_image_of_mem j hx))
  · -- `ψ(bd(Σ)) = bd(R)`.
    have hbdψ : ∀ {x}, x ∈ bd S → (ψ x).1 = j x := by
      intro x hx
      have hxb : j x ∈ discBd R := hRbd ▸ mem_image_of_mem j hx
      have hxD : j x ∈ D := hRD (discBd_subset R hxb)
      have hz : ‖c' (j x)‖ = 1 := by
        rw [← hsph] at hxb
        obtain ⟨v, hv, hve⟩ := hxb
        rw [← hve, hc'c (hball (sphere_subset_closedBall hv))]
        exact mem_sphere_zero_iff_norm.1 hv
      rw [hψv, fold_eq_self hz.le, hcc' hxD]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxb : (ψ x).1 ∈ discBd R := by rw [hbdψ hx, hRbd]; exact mem_image_of_mem j hx
      obtain ⟨y', hy', he⟩ := hxb
      rwa [← Subtype.ext he]
    · intro hy
      have hyb : y.1 ∈ j '' bd S := hRbd ▸ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxe⟩ := hyb
      exact ⟨x, hx, Subtype.ext ((hbdψ hx).trans hxe)⟩

end LastStep
end GM21
end GraphMinor
