module

public import GraphMinor.GM21.Section6DiscStep
public import GraphMinor.GM21.Section6TwoEdges
public import GraphMinor.GM21.Section6ClaimThreeWalk
import GraphMinor.GM21.Section6Disc
import GraphMinor.GM21.Section6DiscLine
import GraphMinor.GM21.Section6FiveOne
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM06.Section3Dual
import GraphMinor.GM07.Section11
import GraphMinor.Surface.Crossing
import GraphMinor.Surface.ArcTools

/-!
# Graph Minors XXI, proofs of (6.6) and (6.7): a region incident with three supports

In the proofs of (6.6) and (6.7) of *Graph Minors XXI* (pages 27–28 of the preprint):
- For $r = 3$, "For $i = 1, 2, 3$, choose $v_i \in V(\Gamma) \cap F_i^*$ such that there is a
  region $r$ of $\Gamma$ in $\Sigma$ incident with $v_1, v_2$ and $v_3$." Then three lines
  $F_1, F_2, F_3$ from an interior point $v_0 \in r_0$ to vertices $v_i \in V(\Gamma) \cap F_i^*$
  cut $\Sigma$ into three closed discs $\Delta_1, \Delta_2, \Delta_3$, each carrying a presentation
  of depth $\le q$ and defect $\le 2$ with an exhaustive vital $(p + 2q)$-linkage, and every
  $\Sigma$-jump belongs to one of $\Delta_1, \Delta_2, \Delta_3$, giving at most $3\lambda'$ jumps.
- For $r \ge 4$, a region incident with vertices in three supports provides a proper line $F$ with
  ends $a, b \in V(\Gamma)$ whose two boundary arcs each miss at least one support, so cutting along
  $F$ (`Side.encard_sigmaJumps_le_of_region`) gives at most $2\lambda'$ jumps.

This file proves:
* `regions_not_cross`: two regions of `Γ` in a disc whose closures contain alternating boundary
  vertices at angles `θ₁ < θ₂ < θ₃ < θ₄` are equal.
* `mem_closure_of_jump_disc`: if the closure of a region `r₀ ∈ Γ.R` contains an edge of a `Σ`-jump
  `J`, then it contains all vertices of `J` (in particular both ends of `J`).
* `exists_region_three_supports`: when `3 ≤ r`, some region `r₀ ∈ Γ.R` is incident with vertices in
  three distinct supports.
* `encard_sigmaJumps_le_three_of_region`: the `r = 3` cutting step of (6.6), giving the bound
  `3 * lam'`.
* `encard_sigmaJumps_le_two_of_region_three`: the `4 ≤ r` cutting step of (6.7), giving the bound
  `lam + lam`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace ThreeSupports

open Set Function Topology Hypergraph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM21.Supports
open GraphMinor.GM21.DiscCut GraphMinor.GM21.Side

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

section RegionLemmas

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  (hD : GM06.IsClosedDiscSpace S)
  (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
  {f : Circle ≃ₜ bd S} {w₀ w₁ : ℝ} {a b : Fin r → ℝ}
  (hW : Window Γ F_star f w₀ w₁ a b)

set_option hygiene false in
local notation "cp" => GM19.cuffPoint f
set_option hygiene false in
local notation "𝒯" => jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))
set_option hygiene false in
local notation "LO" => jumpLo f w₀ w₁ Γ.V ιV
set_option hygiene false in
local notation "HI" => jumpHi f w₀ w₁ Γ.V ιV

private theorem isConnected_of_isLineWithEnds {L : Set S} {x y : S} (h : IsLineWithEnds L x y) :
    IsConnected L := by
  obtain ⟨g, hg, hgr, -, -⟩ := h.exists_arc
  exact hgr ▸ isConnected_range hg.1

include hD h_pres hW in
/-- Two regions of `Γ` in a disc whose closures contain alternating boundary vertices at angles
`w₀ ≤ θ₁ < θ₂ < θ₃ < θ₄ ≤ w₁` are equal. -/
theorem regions_not_cross {r₁ r₂ : Set S} (hr₁ : r₁ ∈ Γ.R) (hr₂ : r₂ ∈ Γ.R)
    {θ₁ θ₂ θ₃ θ₄ : ℝ} (h₀ : w₀ ≤ θ₁) (h12 : θ₁ < θ₂) (h23 : θ₂ < θ₃) (h34 : θ₃ < θ₄)
    (h₄ : θ₄ ≤ w₁) (hv₁ : cp θ₁ ∈ Γ.V) (hv₂ : cp θ₂ ∈ Γ.V) (hv₃ : cp θ₃ ∈ Γ.V)
    (hv₄ : cp θ₄ ∈ Γ.V) (hc₁ : cp θ₁ ∈ closure r₁) (hc₃ : cp θ₃ ∈ closure r₁)
    (hc₂ : cp θ₂ ∈ closure r₂) (hc₄ : cp θ₄ ∈ closure r₂) :
    r₁ = r₂ := by
  have : T2Space S := GM06.t2Space_of_isClosedDiscSpace hD
  have hinj := angle_injOn f hW.lt_add
  have hm₁ : θ₁ ∈ Icc w₀ w₁ := ⟨h₀, (h12.trans (h23.trans h34)).le.trans h₄⟩
  have hm₂ : θ₂ ∈ Icc w₀ w₁ := ⟨h₀.trans h12.le, (h23.trans h34).le.trans h₄⟩
  have hm₃ : θ₃ ∈ Icc w₀ w₁ := ⟨h₀.trans (h12.trans h23).le, h34.le.trans h₄⟩
  have hm₄ : θ₄ ∈ Icc w₀ w₁ := ⟨h₀.trans (h12.trans (h23.trans h34)).le, h₄⟩
  have hne₁₃ : cp θ₁ ≠ cp θ₃ := fun h => (h12.trans h23).ne (hinj hm₁ hm₃ h)
  have hne₂₄ : cp θ₂ ≠ cp θ₄ := fun h => (h23.trans h34).ne (hinj hm₂ hm₄ h)
  obtain ⟨L₁, hL₁, hL₁sub⟩ :=
    DiscLine.exists_line_in_region hD h_pres.is_proper_drawing hr₁ hv₁ hv₃ hne₁₃ hc₁ hc₃
  obtain ⟨L₂, hL₂, hL₂sub⟩ :=
    DiscLine.exists_line_in_region hD h_pres.is_proper_drawing hr₂ hv₂ hv₄ hne₂₄ hc₂ hc₄
  have hcross := pairsCrossOn_of_angles f h12 h23 h34 (by linarith [hW.lt_add])
  obtain ⟨p, hp₁, hp₂⟩ := GM06.discCrossing_of_isClosedDiscSpace hD
    hL₁.isCompact hL₂.isCompact (isConnected_of_isLineWithEnds hL₁)
    (isConnected_of_isLineWithEnds hL₂)
    hL₁.left_mem hL₁.right_mem hL₂.left_mem hL₂.right_mem hcross
  have hp_not₁₃ : p ∉ ({cp θ₁, cp θ₃} : Set S) := by
    rintro (rfl | rfl)
    · rcases hL₂sub hp₂ with (h | h) | hp₂'
      · exact h12.ne (hinj hm₁ hm₂ h)
      · exact (h12.trans (h23.trans h34)).ne (hinj hm₁ hm₄ h)
      · exact hp₂'.2 (GM17.cuffPoint_mem f θ₁)
    · rcases hL₂sub hp₂ with (h | h) | hp₂'
      · exact h23.ne' (hinj hm₃ hm₂ h)
      · exact h34.ne (hinj hm₃ hm₄ h)
      · exact hp₂'.2 (GM17.cuffPoint_mem f θ₃)
  have hp_not₂₄ : p ∉ ({cp θ₂, cp θ₄} : Set S) := by
    rintro (rfl | rfl)
    · rcases hL₁sub hp₁ with (h | h) | hp₁'
      · exact h12.ne' (hinj hm₂ hm₁ h)
      · exact h23.ne (hinj hm₂ hm₃ h)
      · exact hp₁'.2 (GM17.cuffPoint_mem f θ₂)
    · rcases hL₁sub hp₁ with (h | h) | hp₁'
      · exact (h12.trans (h23.trans h34)).ne' (hinj hm₄ hm₁ h)
      · exact h34.ne' (hinj hm₄ hm₃ h)
      · exact hp₁'.2 (GM17.cuffPoint_mem f θ₄)
  have hpr₁ : p ∈ r₁ := ((hL₁sub hp₁).resolve_left hp_not₁₃).1
  have hpr₂ : p ∈ r₂ := ((hL₂sub hp₂).resolve_left hp_not₂₄).1
  rcases hr₁ with ⟨_, _, rfl⟩
  rcases hr₂ with ⟨_, _, rfl⟩
  exact (connectedComponentIn_eq hpr₁).trans (connectedComponentIn_eq hpr₂).symm

include h_pres in
/-- The ends of the edge `ιE e` of `Γ_sub` are the images of the ends of `e`. -/
theorem ends_ιE_eq {e : Set S} (he : e ∈ Γ.E) :
    Γ_sub.ends (ιE e) = ιV '' (closure e ∩ Γ.V) := by
  ext x
  simp only [Hypergraph.ends, mem_ofPred_eq]
  constructor
  · intro hx
    have hxV : x ∈ ιV '' Γ.V := h_pres.ιV_image ▸ Γ_sub.vertex_mem_of_inc hx
    obtain ⟨u, hu, rfl⟩ := hxV
    exact ⟨u, ⟨(h_pres.inc_iff e he u hu).mp hx, hu⟩, rfl⟩
  · rintro ⟨u, ⟨hue, hu⟩, rfl⟩
    exact (h_pres.inc_iff e he u hu).mpr hue

include h_pres in
/-- An edge of `Γ` at a vertex `x` has `x` as one of its two ends. -/
theorem exists_other_end {L : Hypergraph α β} (hL : IsExhaustiveLinkage G Γ_sub r H L)
    {e : Set S} (he : e ∈ Γ.E) {x : S} (hx : x ∈ closure e ∩ Γ.V) :
    ∃ u, u ≠ x ∧ closure e ∩ Γ.V = {x, u} := by
  have hiso := h_pres.drawing_iso
  have hK := IsExhaustiveLinkage.isLinkage h_pres hL
  have heE : ιE e ∈ Γ_sub.edgeSet := hiso.ιE_image ▸ mem_image_of_mem ιE he
  obtain ⟨u', v', huv', hends⟩ := ncard_eq_two.mp (hK.ends_ncard_eq_two heE)
  have hu' : Γ_sub.Inc (ιE e) u' := show u' ∈ Γ_sub.ends (ιE e) from hends ▸ Or.inl rfl
  have hv' : Γ_sub.Inc (ιE e) v' := show v' ∈ Γ_sub.ends (ιE e) from hends ▸ Or.inr rfl
  obtain ⟨u₁, hu₁V, rfl⟩ : u' ∈ ιV '' Γ.V := hiso.ιV_image ▸ Γ_sub.vertex_mem_of_inc hu'
  obtain ⟨u₂, hu₂V, rfl⟩ : v' ∈ ιV '' Γ.V := hiso.ιV_image ▸ Γ_sub.vertex_mem_of_inc hv'
  have hu₁₂ : u₁ ≠ u₂ := fun h => huv' (congrArg ιV h)
  have h : closure e ∩ Γ.V = {u₁, u₂} := by
    ext z
    constructor
    · rintro ⟨hze, hzV⟩
      have hz_end : ιV z ∈ Γ_sub.ends (ιE e) := (hiso.inc_iff e he z hzV).mpr hze
      rw [hends] at hz_end
      rcases hz_end with h1 | h2
      · exact Or.inl (hiso.ιV_injOn hzV hu₁V h1)
      · exact Or.inr (hiso.ιV_injOn hzV hu₂V h2)
    · rintro (rfl | hz)
      · exact ⟨(hiso.inc_iff e he z hu₁V).mp hu', hu₁V⟩
      · rw [mem_singleton_iff] at hz
        subst hz
        exact ⟨(hiso.inc_iff e he z hu₂V).mp hv', hu₂V⟩
  rw [h] at hx
  rcases hx with rfl | hx
  · exact ⟨u₂, hu₁₂.symm, h⟩
  · rw [mem_singleton_iff] at hx
    subst hx
    exact ⟨u₁, hu₁₂, by rw [h, pair_comm]⟩

include hD h_pres in
/-- If the closure of a region `r₀ ∈ Γ.R` contains an edge of a `Σ`-jump `J`, then it contains every
vertex of `J`. -/
theorem mem_closure_of_jump_disc {L : Hypergraph α β}
    (hL : IsExhaustiveLinkage G Γ_sub r H L) {r₀ : Set S} (hr₀ : r₀ ∈ Γ.R)
    {J : Hypergraph α β} (hJ : J ∈ 𝒯) {e₀ : Set S} (he₀ : e₀ ∈ Γ.E) (he₀J : ιE e₀ ∈ J.edgeSet)
    (he₀r : e₀ ⊆ closure r₀) :
    ∀ x ∈ Γ.V, ιV x ∈ J.vertexSet → x ∈ closure r₀ := by
  have : T2Space S := GM06.t2Space_of_isClosedDiscSpace hD
  have hprop := h_pres.is_proper_drawing
  have hiso := h_pres.drawing_iso
  have hdeg := IsExhaustiveLinkage.ncard_incidentEdges_eq_two h_pres hL
  let Z : Set α := {y | ∃ x ∈ Γ.V, ιV x = y ∧ x ∈ closure r₀}
  let ZE : Set β := {f | ∃ e ∈ Γ.E, ιE e = f ∧ e ⊆ closure r₀}
  have hnB : ∀ x ∈ Γ.V, ιV x ∉ ιV '' (Γ.V ∩ bd S) → x ∉ bd S := fun x hx h hxbd =>
    h ⟨x, ⟨hx, hxbd⟩, rfl⟩
  have hsub := ClaimThree.vertexSet_subset_of_propagate (Z := Z) (ZE := ZE) hJ ?_ ?_ ?_
  · intro x hx hxJ
    obtain ⟨y, hy, hyx, hyr⟩ := hsub hxJ
    rwa [hiso.ιV_injOn hy hx hyx] at hyr
  · rintro f hfJ ⟨e, he, rfl, her⟩ y hy
    have hyΓ : Γ_sub.Inc (ιE e) y := GM10.inc_of_le hJ.1 hy
    obtain ⟨x, hx, rfl⟩ : y ∈ ιV '' Γ.V := hiso.ιV_image ▸ Γ_sub.vertex_mem_of_inc hyΓ
    exact ⟨x, hx, rfl, closure_minimal her isClosed_closure ((hiso.inc_iff e he x hx).mp hyΓ)⟩
  · rintro y hyJ ⟨x, hx, rfl, hxr⟩ hyB f hfJ hfx
    have hxbd := hnB x hx hyB
    have hinc := incidentEdges_jump_eq hdeg hJ hyJ hyB
    have hfK : f ∈ incidentEdges Γ_sub (ιV x) := hinc ▸ ⟨hfJ, hfx⟩
    have h2 := hdeg (ιV x) (hJ.1.vertexSet_subset hyJ) hyB
    obtain ⟨f₁, f₂, hf12, hf12'⟩ := ncard_eq_two.mp h2
    obtain ⟨f', hff', hf'K⟩ : ∃ f', f' ≠ f ∧ f' ∈ incidentEdges Γ_sub (ιV x) := by
      rw [hf12'] at hfK ⊢
      rcases hfK with rfl | hfK
      · exact ⟨f₂, hf12.symm, Or.inr rfl⟩
      · rw [mem_singleton_iff] at hfK
        subst hfK
        exact ⟨f₁, hf12, Or.inl rfl⟩
    obtain ⟨e, he, rfl⟩ : f ∈ ιE '' Γ.E := hiso.ιE_image ▸ hfK.1
    obtain ⟨e', he', rfl⟩ : f' ∈ ιE '' Γ.E := hiso.ιE_image ▸ hf'K.1
    have hee : e ≠ e' := fun h => hff' (h ▸ rfl)
    have hxe : x ∈ closure e := (hiso.inc_iff e he x hx).mp hfK.2
    have hxe' : x ∈ closure e' := (hiso.inc_iff e' he' x hx).mp hf'K.2
    obtain ⟨u₁, hu₁x, heu₁⟩ := exists_other_end h_pres hL he ⟨hxe, hx⟩
    obtain ⟨u₂, hu₂x, heu₂⟩ := exists_other_end h_pres hL he' ⟨hxe', hx⟩
    have hu₁₂ : u₁ ≠ u₂ := by
      rintro rfl
      have hf'J : ιE e' ∈ J.edgeSet := (hinc ▸ hf'K : ιE e' ∈ incidentEdges J (ιV x)).1
      have hends : J.ends (ιE e) = J.ends (ιE e') := by
        rw [← hJ.1.ends_eq _ hfJ, ← hJ.1.ends_eq _ hf'J, ends_ιE_eq h_pres he,
          ends_ιE_eq h_pres he', heu₁, heu₂]
      exact hff' (hJ.2.1.2.2.2.2.1 _ hfJ _ hf'J hends).symm
    have hdegΓ : ∀ g ∈ Γ.E, x ∈ closure g → g = e ∨ g = e' := by
      intro g hg hxg
      have h₀ : ιE g ∈ incidentEdges Γ_sub (ιV x) :=
        ⟨hiso.ιE_image ▸ mem_image_of_mem ιE hg, (hiso.inc_iff g hg x hx).mpr hxg⟩
      rw [hf12'] at h₀ hfK hf'K
      simp only [mem_insert_iff, mem_singleton_iff] at h₀ hfK hf'K
      have hcases : ιE g = ιE e ∨ ιE g = ιE e' := by
        rcases h₀ with h₀ | h₀ <;> rcases hfK with h₁ | h₁ <;> rcases hf'K with h₂ | h₂ <;>
          first
          | exact Or.inl (h₀.trans h₁.symm)
          | exact Or.inr (h₀.trans h₂.symm)
          | exact absurd (h₂.trans h₁.symm) hff'
      rcases hcases with h | h
      · exact Or.inl (hiso.ιE_injOn hg he h)
      · exact Or.inr (hiso.ιE_injOn hg he' h)
    have hU := DiscLine.union_subset_closure_of_two_edges_of_edge
      (fun _ hΓ' _ hE _ _ _ _ _ hr' hinc' =>
        GM06.disc_edge_subset_closure_of_incident hD hΓ' hE hr' hinc')
      hprop he he' hee (by rw [heu₁, pair_comm]) heu₂ hu₁x hu₂x hu₁₂ hdegΓ hxbd hr₀
      ⟨x, Or.inl (Or.inr rfl), hxr⟩
    exact ⟨e, he, rfl, fun z hz => hU (Or.inl (Or.inl hz))⟩
  · exact Or.inl ⟨ιE e₀, he₀J, e₀, he₀, rfl, he₀r⟩

include h_pres in
/-- If `(s, e)` contains no angles of vertices of `Γ`, then `cp s` and `cp e` lie in the closure of
a common region of `Γ`. -/
theorem exists_region_of_empty_Ioo {s e : ℝ} (hse : s < e)
    (hempty : ∀ t ∈ Ioo s e, cp t ∉ Γ.V) :
    ∃ r₀ ∈ Γ.R, cp s ∈ closure r₀ ∧ cp e ∈ closure r₀ := by
  have hprop := h_pres.is_proper_drawing
  have hsub : cp '' Ioo s e ⊆ univ \ Γ.U := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨mem_univ _, fun hU => hempty t ht (hprop ⟨GM17.cuffPoint_mem f t, hU⟩)⟩
  let m := (s + e) / 2
  have hm : m ∈ Ioo s e := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hmU : cp m ∈ univ \ Γ.U := hsub ⟨m, hm, rfl⟩
  let r₀ := connectedComponentIn (univ \ Γ.U) (cp m)
  have hr₀ : r₀ ∈ Γ.R := ⟨cp m, hmU, rfl⟩
  have hcont := GM17.cuffPoint_continuous f
  have hpre : IsPreconnected (cp '' Ioo s e) :=
    (isConnected_Ioo hse).isPreconnected.image _ hcont.continuousOn
  have hsub_r₀ : cp '' Ioo s e ⊆ r₀ :=
    hpre.subset_connectedComponentIn ⟨m, hm, rfl⟩ hsub
  have hcl : cp '' Icc s e ⊆ closure r₀ := by
    rw [← closure_Ioo hse.ne]
    exact (image_closure_subset_closure_image hcont).trans (closure_mono hsub_r₀)
  exact ⟨r₀, hr₀, hcl ⟨s, ⟨le_rfl, hse.le⟩, rfl⟩, hcl ⟨e, ⟨hse.le, le_rfl⟩, rfl⟩⟩

include hD h_pres hW in
/-- **A region incident with three supports** (Graph Minors XXI, proofs of (6.6) and (6.7),
pages 27–28 of the preprint). If `3 ≤ r`, there exist a region `r₀ ∈ Γ.R`, three supports
`j₁, j₂, j₃ : Fin r`, and angles `θ₁, θ₂, θ₃ : ℝ` such that
`a j₁ ≤ θ₁ ≤ b j₁ < a j₂ ≤ θ₂ ≤ b j₂ < a j₃ ≤ θ₃ ≤ b j₃`, `cp θᵢ ∈ Γ.V ∩ closure r₀` for
`i = 1, 2, 3`, and every support `j ∉ {j₁, j₂}` satisfies `b j₂ < a j`. -/
theorem exists_region_three_supports {L : Hypergraph α β}
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (hr3 : 3 ≤ r) :
    ∃ (r₀ : Set S) (_ : r₀ ∈ Γ.R) (j₁ j₂ j₃ : Fin r) (θ₁ θ₂ θ₃ : ℝ),
      θ₁ ∈ Icc (a j₁) (b j₁) ∧ θ₂ ∈ Icc (a j₂) (b j₂) ∧ θ₃ ∈ Icc (a j₃) (b j₃) ∧
      b j₁ < a j₂ ∧ b j₂ < a j₃ ∧
      cp θ₁ ∈ Γ.V ∧ cp θ₁ ∈ closure r₀ ∧
      cp θ₂ ∈ Γ.V ∧ cp θ₂ ∈ closure r₀ ∧
      cp θ₃ ∈ Γ.V ∧ cp θ₃ ∈ closure r₀ ∧
      (∀ j : Fin r, j ≠ j₁ → j ≠ j₂ → b j₂ < a j) := by
  classical
  have : T2Space S := GM06.t2Space_of_isClosedDiscSpace hD
  have hK := IsExhaustiveLinkage.isLinkage h_pres hL
  have hdeg := IsExhaustiveLinkage.ncard_incidentEdges_eq_two h_pres hL
  -- Choose the first three supports in the window by minimizing `a j`.
  have hT₁ : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨j₁, -, hj₁_min⟩ := Finset.univ.exists_min_image a hT₁
  have hT₂ : (Finset.univ.erase j₁).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j₁), Finset.card_fin]
    omega
  obtain ⟨j₂, hj₂_mem, hj₂_min⟩ := (Finset.univ.erase j₁).exists_min_image a hT₂
  have hj₂₁ : j₂ ≠ j₁ := (Finset.mem_erase.mp hj₂_mem).1
  have hT₃ : ((Finset.univ.erase j₁).erase j₂).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hj₂_mem,
      Finset.card_erase_of_mem (Finset.mem_univ j₁), Finset.card_fin]
    omega
  obtain ⟨j₃, hj₃_mem, hj₃_min⟩ := ((Finset.univ.erase j₁).erase j₂).exists_min_image a hT₃
  have hj₃₂ : j₃ ≠ j₂ := (Finset.mem_erase.mp hj₃_mem).1
  have hj₃₁ : j₃ ≠ j₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj₃_mem).2).1
  have hmin₁ : ∀ j, a j₁ ≤ a j := fun j => hj₁_min j (Finset.mem_univ j)
  have hmin₂ : ∀ j, j ≠ j₁ → a j₂ ≤ a j := fun j hj =>
    hj₂_min j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  have hmin₃ : ∀ j, j ≠ j₁ → j ≠ j₂ → a j₃ ≤ a j := fun j hj₁ hj₂ =>
    hj₃_min j (Finset.mem_erase.mpr ⟨hj₂, Finset.mem_erase.mpr ⟨hj₁, Finset.mem_univ j⟩⟩)
  have hb₁a₂ : b j₁ < a j₂ := by
    rcases hW.lt_or_lt h_pres hj₂₁.symm with h | h
    · exact h
    · linarith [hmin₁ j₂, hW.a_le_b j₂]
  have hb₂a₃ : b j₂ < a j₃ := by
    rcases hW.lt_or_lt h_pres hj₃₂.symm with h | h
    · exact h
    · linarith [hmin₂ j₃ hj₃₁, hW.a_le_b j₃]
  have hb₂_lt : ∀ j, j ≠ j₁ → j ≠ j₂ → b j₂ < a j := fun j hj₁ hj₂ =>
    hb₂a₃.trans_le (hmin₃ j hj₁ hj₂)
  -- The open boundary arcs `(b j₁, a j₂)` and `(b j₂, a j₃)` contain no vertices of `Γ`.
  have hempty₁₂ : ∀ t ∈ Ioo (b j₁) (a j₂), cp t ∉ Γ.V := by
    intro t ht htV
    have htW : t ∈ Icc w₀ w₁ := ⟨(hW.le_a j₁).trans ((hW.a_le_b j₁).trans ht.1.le),
      ht.2.le.trans ((hW.a_le_b j₂).trans (hW.b_le j₂))⟩
    obtain ⟨j, hj⟩ := hW.exists_support h_pres htW htV
    by_cases hjj₁ : j = j₁
    · subst hjj₁; linarith [hj.2, ht.1]
    · linarith [hmin₂ j hjj₁, hj.1, ht.2]
  have hempty₂₃ : ∀ t ∈ Ioo (b j₂) (a j₃), cp t ∉ Γ.V := by
    intro t ht htV
    have htW : t ∈ Icc w₀ w₁ := ⟨(hW.le_a j₂).trans ((hW.a_le_b j₂).trans ht.1.le),
      ht.2.le.trans ((hW.a_le_b j₃).trans (hW.b_le j₃))⟩
    obtain ⟨j, hj⟩ := hW.exists_support h_pres htW htV
    by_cases hjj₁ : j = j₁
    · subst hjj₁; linarith [hj.2, hb₁a₂, hW.a_le_b j₂, ht.1]
    by_cases hjj₂ : j = j₂
    · subst hjj₂; linarith [hj.2, ht.1]
    · linarith [hmin₃ j hjj₁ hjj₂, hj.1, ht.2]
  obtain ⟨r₁, hr₁, hr₁_b₁, hr₁_a₂⟩ := exists_region_of_empty_Ioo h_pres hb₁a₂ hempty₁₂
  obtain ⟨r₂, hr₂, hr₂_b₂, hr₂_a₃⟩ := exists_region_of_empty_Ioo h_pres hb₂a₃ hempty₂₃
  -- Suppose for contradiction that no region meets `j₁`, `j₂`, and a third support `j_w`.
  by_contra hno
  let HasSupp (r₀ : Set S) (j : Fin r) : Prop :=
    ∃ t ∈ Icc (a j) (b j), cp t ∈ Γ.V ∧ cp t ∈ closure r₀
  have hno_three : ∀ r₀ ∈ Γ.R, ∀ j_w : Fin r, j_w ≠ j₁ → j_w ≠ j₂ →
      ¬ (HasSupp r₀ j₁ ∧ HasSupp r₀ j₂ ∧ HasSupp r₀ j_w) := by
    rintro r₀ hr₀ j_w hjw₁ hjw₂ ⟨⟨θ₁, hθ₁, hv₁, hc₁⟩, ⟨θ₂, hθ₂, hv₂, hc₂⟩, ⟨θ₃, hθ₃, hv₃, hc₃⟩⟩
    exact hno ⟨r₀, hr₀, j₁, j₂, j_w, θ₁, θ₂, θ₃, hθ₁, hθ₂, hθ₃, hb₁a₂, hb₂_lt j_w hjw₁ hjw₂,
      hv₁, hc₁, hv₂, hc₂, hv₃, hc₃, hb₂_lt⟩
  have hr₁_j₁ : HasSupp r₁ j₁ := ⟨b j₁, ⟨hW.a_le_b j₁, le_rfl⟩, hW.b_mem j₁, hr₁_b₁⟩
  have hr₁_j₂ : HasSupp r₁ j₂ := ⟨a j₂, ⟨le_rfl, hW.a_le_b j₂⟩, hW.a_mem j₂, hr₁_a₂⟩
  have hr₂_j₂ : HasSupp r₂ j₂ := ⟨b j₂, ⟨hW.a_le_b j₂, le_rfl⟩, hW.b_mem j₂, hr₂_b₂⟩
  have hr₂_j₃ : HasSupp r₂ j₃ := ⟨a j₃, ⟨le_rfl, hW.a_le_b j₃⟩, hW.a_mem j₃, hr₂_a₃⟩
  -- `S_min₁` is the set of vertex angles in `[a j₁, b j₁]` in the closure of a region meeting `j₂`.
  let S_min₁ : Set ℝ :=
    {s ∈ Icc (a j₁) (b j₁) | cp s ∈ Γ.V ∧ ∃ r₀ ∈ Γ.R, HasSupp r₀ j₂ ∧ cp s ∈ closure r₀}
  have hb₁_min₁ : b j₁ ∈ S_min₁ :=
    ⟨⟨hW.a_le_b j₁, le_rfl⟩, hW.b_mem j₁, r₁, hr₁, hr₁_j₂, hr₁_b₁⟩
  have hS_min_fin : S_min₁.Finite := by
    refine Finite.of_finite_image (f := cp) ?_
      ((angle_injOn f hW.lt_add).mono fun s hs => hW.Icc_subset j₁ hs.1)
    exact Γ.finite_V.subset (by rintro _ ⟨s, hs, rfl⟩; exact hs.2.1)
  have hS_min_ne : hS_min_fin.toFinset.Nonempty :=
    hS_min_fin.toFinset_nonempty.mpr ⟨b j₁, hb₁_min₁⟩
  set θ_min₁ : ℝ := hS_min_fin.toFinset.min' hS_min_ne
  have hθ_min₁_mem : θ_min₁ ∈ S_min₁ :=
    hS_min_fin.mem_toFinset.mp (Finset.min'_mem _ hS_min_ne)
  have hθ_min₁_min : ∀ s ∈ S_min₁, θ_min₁ ≤ s := fun s hs =>
    Finset.min'_le _ s (hS_min_fin.mem_toFinset.mpr hs)
  obtain ⟨hθ_min₁_Icc, hθ_min₁_V, r_min₁, hr_min₁, ⟨θ₂', hθ₂'_Icc, hθ₂'_V, hθ₂'_cl⟩, hθ_min₁_cl⟩ :=
    hθ_min₁_mem
  -- `S_split` is the set of vertex angles in `[a j₂, b j₂]` in the closure of a region meeting `j₁`.
  let S_split : Set ℝ :=
    {s ∈ Icc (a j₂) (b j₂) | cp s ∈ Γ.V ∧ ∃ r₀ ∈ Γ.R, HasSupp r₀ j₁ ∧ cp s ∈ closure r₀}
  have ha₂_split : a j₂ ∈ S_split :=
    ⟨⟨le_rfl, hW.a_le_b j₂⟩, hW.a_mem j₂, r₁, hr₁, hr₁_j₁, hr₁_a₂⟩
  have hS_fin : S_split.Finite := by
    refine Finite.of_finite_image (f := cp) ?_
      ((angle_injOn f hW.lt_add).mono fun s hs => hW.Icc_subset j₂ hs.1)
    exact Γ.finite_V.subset (by rintro _ ⟨s, hs, rfl⟩; exact hs.2.1)
  have hS_ne : hS_fin.toFinset.Nonempty := hS_fin.toFinset_nonempty.mpr ⟨a j₂, ha₂_split⟩
  set θ_split : ℝ := hS_fin.toFinset.max' hS_ne
  have hθ_split_mem : θ_split ∈ S_split := hS_fin.mem_toFinset.mp (Finset.max'_mem _ hS_ne)
  have hθ_split_max : ∀ s ∈ S_split, s ≤ θ_split := fun s hs =>
    Finset.le_max' _ s (hS_fin.mem_toFinset.mpr hs)
  obtain ⟨hθ_split_Icc, hθ_split_V, r_split, hr_split, ⟨θ₁', hθ₁'_Icc, hθ₁'_V, hθ₁'_cl⟩, hθ_split_cl⟩ :=
    hθ_split_mem
  -- A single region `r_bridge` has both `cp θ_min₁` and `cp θ_split` in its closure.
  have hθ_min_le : θ_min₁ ≤ θ₁' :=
    hθ_min₁_min θ₁' ⟨hθ₁'_Icc, hθ₁'_V, r_split, hr_split, ⟨θ_split, hθ_split_Icc, hθ_split_V, hθ_split_cl⟩, hθ₁'_cl⟩
  have hθ_max_ge : θ₂' ≤ θ_split :=
    hθ_split_max θ₂' ⟨hθ₂'_Icc, hθ₂'_V, r_min₁, hr_min₁, ⟨θ_min₁, hθ_min₁_Icc, hθ_min₁_V, hθ_min₁_cl⟩, hθ₂'_cl⟩
  have h_bridge : ∃ r_b ∈ Γ.R, cp θ_min₁ ∈ closure r_b ∧ cp θ_split ∈ closure r_b := by
    rcases eq_or_lt_of_le hθ_min_le with heq₁ | hlt₁
    · exact ⟨r_split, hr_split, heq₁ ▸ hθ₁'_cl, hθ_split_cl⟩
    · rcases eq_or_lt_of_le hθ_max_ge with heq₂ | hlt₂
      · exact ⟨r_min₁, hr_min₁, hθ_min₁_cl, heq₂ ▸ hθ₂'_cl⟩
      · have hreq : r_min₁ = r_split :=
          regions_not_cross hD h_pres hW hr_min₁ hr_split ((hW.le_a j₁).trans hθ_min₁_Icc.1)
            hlt₁ (hθ₁'_Icc.2.trans_lt (hb₁a₂.trans_le hθ₂'_Icc.1)) hlt₂
            (hθ_split_Icc.2.trans (hW.b_le j₂)) hθ_min₁_V hθ₁'_V hθ₂'_V hθ_split_V
            hθ_min₁_cl hθ₂'_cl hθ₁'_cl hθ_split_cl
        exact ⟨r_split, hr_split, hreq ▸ hθ_min₁_cl, hθ_split_cl⟩
  obtain ⟨r_b, hr_b, hθ_min_b, hθ_split_b⟩ := h_bridge
  have hrb_j₁ : HasSupp r_b j₁ := ⟨θ_min₁, hθ_min₁_Icc, hθ_min₁_V, hθ_min_b⟩
  have hrb_j₂ : HasSupp r_b j₂ := ⟨θ_split, hθ_split_Icc, hθ_split_V, hθ_split_b⟩
  -- Define `Mid` and `Z ⊆ Γ.R`.
  let Mid (r₀ : Set S) : Prop :=
    (∃ t ∈ Ioo θ_min₁ θ_split, cp t ∈ Γ.V ∧ cp t ∈ closure r₀) ∨
      (cp θ_min₁ ∈ closure r₀ ∧ cp θ_split ∈ closure r₀)
  let Z : Set (Set S) :=
    {r₀ ∈ Γ.R | Mid r₀ ∧ ∀ j, HasSupp r₀ j → j = j₁ ∨ j = j₂}
  have hr₁_Z : r₁ ∈ Z := by
    refine ⟨hr₁, ?_, fun j hj => ?_⟩
    · rcases eq_or_lt_of_le (hθ_min₁_min (b j₁) hb₁_min₁) with heq₁ | hlt₁
      · rcases eq_or_lt_of_le (hθ_split_max (a j₂) ha₂_split) with heq₂ | hlt₂
        · exact Or.inr ⟨heq₁ ▸ hr₁_b₁, heq₂ ▸ hr₁_a₂⟩
        · exact Or.inl ⟨a j₂, ⟨hθ_min₁_Icc.2.trans_lt hb₁a₂, hlt₂⟩, hW.a_mem j₂, hr₁_a₂⟩
      · exact Or.inl ⟨b j₁, ⟨hlt₁, hb₁a₂.trans_le hθ_split_Icc.1⟩, hW.b_mem j₁, hr₁_b₁⟩
    · by_contra hnot
      push Not at hnot
      exact hno_three r₁ hr₁ j hnot.1 hnot.2 ⟨hr₁_j₁, hr₁_j₂, hj⟩
  have hr₂_notZ : r₂ ∉ Z := fun h => by
    rcases h.2.2 j₃ hr₂_j₃ with h1 | h2
    exacts [hj₃₁ h1, hj₃₂ h2]
  -- Apply `GM06.disc_theorem_5_1` with the empty subdrawing `Γ.span ∅ ∅`.
  let Γ₀ : Drawing S := Γ.span ∅ ∅
  have hsub₀ : Γ₀.IsSubdrawing Γ := Drawing.span_isSubdrawing Γ ∅ ∅
  have hΓ₀E : Γ₀.E = ∅ := by rw [Γ.span_E]; exact empty_inter _
  have hΓ₀V : Γ₀.V = ∅ := by
    change Γ.spanV ∅ ∅ = ∅
    simp [Drawing.spanV]
  have hΓ₀U : Γ₀.U = ∅ := by rw [Γ₀.U_eq, hΓ₀V, hΓ₀E]; simp
  let x₁ : S := cp (b j₁)
  let r' : Set S := connectedComponentIn (univ \ Γ₀.U) x₁
  have hr' : r' ∈ Γ₀.R := ⟨x₁, ⟨mem_univ _, by simp [hΓ₀U]⟩, rfl⟩
  have : ConnectedSpace S := connectedSpace_of_isClosedDiscSpace hD
  have hr'_univ : r' = univ := by
    change connectedComponentIn (univ \ Γ₀.U) x₁ = univ
    rw [hΓ₀U, sdiff_empty]
    exact isPreconnected_univ.connectedComponentIn (mem_univ x₁)
  obtain ⟨e, heΓ, -, c, d, hcZ, hdZ, -, -, hinc_c, hinc_d⟩ :=
    GM06.disc_theorem_5_1 hD h_pres.is_proper_drawing hsub₀ hr' hr₁ hr₁_Z hr₂ hr₂_notZ
      (hr'_univ ▸ subset_univ _) (hr'_univ ▸ subset_univ _)
  have hcR : c ∈ Γ.R := hinc_c.2.1
  have hdR : d ∈ Γ.R := hinc_d.2.1
  have he_cl_c : e ⊆ closure c :=
    GM06.disc_edge_subset_closure_of_incident hD h_pres.is_proper_drawing heΓ hcR hinc_c.2.2
  have he_cl_d : e ⊆ closure d :=
    GM06.disc_edge_subset_closure_of_incident hD h_pres.is_proper_drawing heΓ hdR hinc_d.2.2
  -- `ιE e` belongs to a jump `J ∈ 𝒯`.
  have he_sub : ιE e ∈ Γ_sub.edgeSet := h_pres.ιE_image ▸ mem_image_of_mem ιE heΓ
  obtain ⟨J, hJ, heJ⟩ := exists_jump_of_edge hK hdeg he_sub
  have hspec := hW.jumpAngles_spec h_pres hJ
  have hlo_mem := hW.jumpLo_mem h_pres hJ
  have hhi_mem := hW.jumpHi_mem h_pres hJ
  have hlo_V : cp (LO J) ∈ Γ.V := hspec.2.2.2.1
  have hhi_V : cp (HI J) ∈ Γ.V := hspec.2.2.2.2.1
  have hlo_J : ιV (cp (LO J)) ∈ J.vertexSet :=
    (show ιV (cp (LO J)) ∈ terminals J from hspec.2.2.2.2.2 ▸ Or.inl rfl).1
  have hhi_J : ιV (cp (HI J)) ∈ J.vertexSet :=
    (show ιV (cp (HI J)) ∈ terminals J from hspec.2.2.2.2.2 ▸ Or.inr rfl).1
  have hlo_c : cp (LO J) ∈ closure c :=
    mem_closure_of_jump_disc hD h_pres hL hcR hJ heΓ heJ he_cl_c _ hlo_V hlo_J
  have hhi_c : cp (HI J) ∈ closure c :=
    mem_closure_of_jump_disc hD h_pres hL hcR hJ heΓ heJ he_cl_c _ hhi_V hhi_J
  have hlo_d : cp (LO J) ∈ closure d :=
    mem_closure_of_jump_disc hD h_pres hL hdR hJ heΓ heJ he_cl_d _ hlo_V hlo_J
  have hhi_d : cp (HI J) ∈ closure d :=
    mem_closure_of_jump_disc hD h_pres hL hdR hJ heΓ heJ he_cl_d _ hhi_V hhi_J
  obtain ⟨j_lo, hj_lo⟩ := hW.exists_support h_pres hlo_mem hlo_V
  obtain ⟨j_hi, hj_hi⟩ := hW.exists_support h_pres hhi_mem hhi_V
  have hj_lo_12 : j_lo = j₁ ∨ j_lo = j₂ := hcZ.2.2 j_lo ⟨LO J, hj_lo, hlo_V, hlo_c⟩
  have hj_hi_12 : j_hi = j₁ ∨ j_hi = j₂ := hcZ.2.2 j_hi ⟨HI J, hj_hi, hhi_V, hhi_c⟩
  -- `HI J ≤ θ_split`.
  have hhi_le_split : HI J ≤ θ_split := by
    by_contra hgt
    push Not at hgt
    have hj_hi_2 : j_hi = j₂ := by
      rcases hj_hi_12 with h1 | h2
      · rw [h1] at hj_hi
        exfalso; linarith [hj_hi.2, hb₁a₂, hθ_split_Icc.1]
      · exact h2
    rw [hj_hi_2] at hj_hi
    rcases hcZ.2.1 with ⟨t, ht_Ioo, ht_V, ht_c⟩ | ⟨hc_min, -⟩
    · obtain ⟨j_t, hj_t⟩ := hW.exists_support h_pres
        ⟨((hW.le_a j₁).trans hθ_min₁_Icc.1).trans ht_Ioo.1.le,
          ht_Ioo.2.le.trans (hθ_split_Icc.2.trans (hW.b_le j₂))⟩ ht_V
      rcases hcZ.2.2 j_t ⟨t, hj_t, ht_V, ht_c⟩ with hjt | hjt
      · rw [hjt] at hj_t
        have hhi_split : HI J ∈ S_split :=
          ⟨hj_hi, hhi_V, c, hcR, ⟨t, hj_t, ht_V, ht_c⟩, hhi_c⟩
        linarith [hθ_split_max (HI J) hhi_split]
      · rw [hjt] at hj_t
        have hceq : r_b = c :=
          regions_not_cross hD h_pres hW hr_b hcR ((hW.le_a j₁).trans hθ_min₁_Icc.1)
            ht_Ioo.1 ht_Ioo.2 hgt (hj_hi.2.trans (hW.b_le j₂))
            hθ_min₁_V ht_V hθ_split_V hhi_V hθ_min_b hθ_split_b ht_c hhi_c
        have hhi_split : HI J ∈ S_split :=
          ⟨hj_hi, hhi_V, c, hcR, hceq ▸ hrb_j₁, hhi_c⟩
        linarith [hθ_split_max (HI J) hhi_split]
    · have hhi_split : HI J ∈ S_split :=
        ⟨hj_hi, hhi_V, c, hcR, ⟨θ_min₁, hθ_min₁_Icc, hθ_min₁_V, hc_min⟩, hhi_c⟩
      linarith [hθ_split_max (HI J) hhi_split]
  -- `θ_min₁ ≤ LO J`.
  have hmin_le_lo : θ_min₁ ≤ LO J := by
    by_contra hlt
    push Not at hlt
    have hj_lo_1 : j_lo = j₁ := by
      rcases hj_lo_12 with h1 | h2
      · exact h1
      · rw [h2] at hj_lo
        exfalso; linarith [hj_lo.1, hb₁a₂, hθ_min₁_Icc.2]
    rw [hj_lo_1] at hj_lo
    rcases hcZ.2.1 with ⟨t, ht_Ioo, ht_V, ht_c⟩ | ⟨-, hc_split⟩
    · obtain ⟨j_t, hj_t⟩ := hW.exists_support h_pres
        ⟨((hW.le_a j₁).trans hθ_min₁_Icc.1).trans ht_Ioo.1.le,
          ht_Ioo.2.le.trans (hθ_split_Icc.2.trans (hW.b_le j₂))⟩ ht_V
      rcases hcZ.2.2 j_t ⟨t, hj_t, ht_V, ht_c⟩ with hjt | hjt
      · rw [hjt] at hj_t
        have hceq : c = r_b :=
          regions_not_cross hD h_pres hW hcR hr_b hlo_mem.1 hlt ht_Ioo.1 ht_Ioo.2
            (hθ_split_Icc.2.trans (hW.b_le j₂)) hlo_V hθ_min₁_V ht_V hθ_split_V
            hlo_c ht_c hθ_min_b hθ_split_b
        have hlo_min : LO J ∈ S_min₁ :=
          ⟨hj_lo, hlo_V, c, hcR, hceq.symm ▸ hrb_j₂, hlo_c⟩
        linarith [hθ_min₁_min (LO J) hlo_min]
      · rw [hjt] at hj_t
        have hlo_min : LO J ∈ S_min₁ :=
          ⟨hj_lo, hlo_V, c, hcR, ⟨t, hj_t, ht_V, ht_c⟩, hlo_c⟩
        linarith [hθ_min₁_min (LO J) hlo_min]
    · have hlo_min : LO J ∈ S_min₁ :=
        ⟨hj_lo, hlo_V, c, hcR, ⟨θ_split, hθ_split_Icc, hθ_split_V, hc_split⟩, hlo_c⟩
      linarith [hθ_min₁_min (LO J) hlo_min]
  -- Hence `θ_min₁ ≤ LO J < HI J ≤ θ_split`, so `Mid d` holds and `d` must fail the second conjunct.
  have hd_mid : Mid d := by
    rcases eq_or_lt_of_le hmin_le_lo with heq_lo | hlt_lo
    · rcases eq_or_lt_of_le hhi_le_split with heq_hi | hlt_hi
      · exact Or.inr ⟨heq_lo ▸ hlo_d, heq_hi.symm ▸ hhi_d⟩
      · exact Or.inl ⟨HI J, ⟨hmin_le_lo.trans_lt hspec.2.1, hlt_hi⟩, hhi_V, hhi_d⟩
    · exact Or.inl ⟨LO J, ⟨hlt_lo, hspec.2.1.trans_le hhi_le_split⟩, hlo_V, hlo_d⟩
  have hd_fail : ¬ ∀ j, HasSupp d j → j = j₁ ∨ j = j₂ := fun hall =>
    hdZ ⟨hdR, hd_mid, hall⟩
  push Not at hd_fail
  obtain ⟨j_w, ⟨s_w, hs_w, hs_w_V, hs_w_d⟩, hjw₁, hjw₂⟩ := hd_fail
  have hsw_gt : b j₂ < s_w := (hb₂_lt j_w hjw₁ hjw₂).trans_le hs_w.1
  rcases eq_or_lt_of_le hhi_le_split with heq_hi | hlt_hi
  · rcases eq_or_lt_of_le hmin_le_lo with heq_lo | hlt_lo
    · -- `LO J = θ_min₁` and `HI J = θ_split`: `d` meets `j₁`, `j₂`, and `j_w`.
      exact hno_three d hdR j_w hjw₁ hjw₂
        ⟨⟨θ_min₁, hθ_min₁_Icc, hθ_min₁_V, heq_lo ▸ hlo_d⟩,
          ⟨θ_split, hθ_split_Icc, hθ_split_V, heq_hi.symm ▸ hhi_d⟩,
          ⟨s_w, hs_w, hs_w_V, hs_w_d⟩⟩
    · -- `θ_min₁ < LO J < θ_split < s_w`: `r_b` and `d` cross.
      have hdeq : r_b = d :=
        regions_not_cross hD h_pres hW hr_b hdR ((hW.le_a j₁).trans hθ_min₁_Icc.1)
          hlt_lo (hspec.2.1.trans_le hhi_le_split) (hθ_split_Icc.2.trans_lt hsw_gt)
          (hs_w.2.trans (hW.b_le j_w)) hθ_min₁_V hlo_V hθ_split_V hs_w_V
          hθ_min_b hθ_split_b hlo_d hs_w_d
      exact hno_three d hdR j_w hjw₁ hjw₂ ⟨hdeq ▸ hrb_j₁, hdeq ▸ hrb_j₂, ⟨s_w, hs_w, hs_w_V, hs_w_d⟩⟩
  · -- `θ_min₁ < HI J < θ_split < s_w`: `r_b` and `d` cross.
    have hdeq : r_b = d :=
      regions_not_cross hD h_pres hW hr_b hdR ((hW.le_a j₁).trans hθ_min₁_Icc.1)
        (hmin_le_lo.trans_lt hspec.2.1) hlt_hi (hθ_split_Icc.2.trans_lt hsw_gt)
        (hs_w.2.trans (hW.b_le j_w)) hθ_min₁_V hhi_V hθ_split_V hs_w_V
        hθ_min_b hθ_split_b hhi_d hs_w_d
    exact hno_three d hdR j_w hjw₁ hjw₂ ⟨hdeq ▸ hrb_j₁, hdeq ▸ hrb_j₂, ⟨s_w, hs_w, hs_w_V, hs_w_d⟩⟩

end RegionLemmas

section CuttingSteps

variable [T2Space S] {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {f : Circle ≃ₜ bd S} {w₀ w₁ : ℝ}
  {a b : Fin r → ℝ}

set_option hygiene false in
local notation "cp" => GM19.cuffPoint f

/-- Two points on opposite lines of a circle cross the ends of the lines. -/
private theorem pairsCross_of_lines_disc {C J₁ J₂ : Set S} {x y u v : S}
    (hJ₁ : IsLineWithEnds J₁ x y) (hJ₂ : IsLineWithEnds J₂ x y) (hu : J₁ ∪ J₂ = C)
    (hi : J₁ ∩ J₂ = {x, y}) (h₁ : u ∈ J₁) (h₂ : v ∈ J₂) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) : PairsCrossOn C x y u v := by
  have huC : u ∈ C := hu ▸ .inl h₁
  have hvC : v ∈ C := hu ▸ .inr h₂
  have hne : u ≠ v := by
    rintro rfl
    have h3 : u ∈ J₁ ∩ J₂ := ⟨h₁, h₂⟩
    rw [hi] at h3
    rcases h3 with h3 | h3
    exacts [hux h3, huy h3]
  refine ⟨hu ▸ .inl hJ₁.left_mem, huC, hu ▸ .inl hJ₁.right_mem, hvC, hJ₁.ne', hne, hux.symm,
    hvx.symm, huy.symm, hvy.symm, fun he => ?_⟩
  have hum : u ∈ C \ {x, y} := ⟨huC, by rintro (h | h); exacts [hux h, huy h]⟩
  have hvm : v ∈ C \ {x, y} := ⟨hvC, by rintro (h | h); exacts [hvx h, hvy h]⟩
  have hv' : v ∈ connectedComponentIn (C \ {x, y}) u := he ▸ mem_connectedComponentIn hvm
  have hsub := connectedComponentIn_subset (C \ {x, y}) u
  obtain ⟨z, hz, hz₁, hz₂⟩ := isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn J₁ J₂
    hJ₁.isCompact.isClosed hJ₂.isCompact.isClosed (fun z hz => hu ▸ (hsub hz).1)
    ⟨u, mem_connectedComponentIn hum, h₁⟩ ⟨v, hv', h₂⟩
  exact (hsub hz).2 (hi ▸ ⟨hz₁, hz₂⟩)

/-- If a line `F ⊆ {x, y} ∪ (r₀ \ bd S)` cuts `S` into `S₁, S₂` (`IsSideOfLine Γ S₁ S₂ F x y`),
`S₁` is a closed disc with `IsLineWithEnds (S₁ ∩ bd S) x y`, and `z ∈ (S₁ ∩ bd S) \ {x, y}` is in
`Γ.V ∩ closure r₀`, then no jump `J` with ends `{x, y}` belongs to `sigmaJumps` of the `S₁` side. -/
theorem not_mem_sigmaJumps_of_ends_of_third (hD : GM06.IsClosedDiscSpace S)
    (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    {L : Hypergraph α β} (hL : IsExhaustiveLinkage G Γ_sub r H L)
    {r₀ : Set S} (hr₀ : r₀ ∈ Γ.R) {x y z : S} (hxV : x ∈ Γ.V) (hyV : y ∈ Γ.V) (hzV : z ∈ Γ.V)
    (hzr : z ∈ closure r₀) {F S₁ S₂ : Set S} (hFsub : F ⊆ {x, y} ∪ (r₀ \ bd S))
    (h : IsSideOfLine Γ S₁ S₂ F x y) (hD₁ : GM06.IsClosedDiscSpace S₁)
    (hJ₁ : IsLineWithEnds (S₁ ∩ bd S) x y) (hz : z ∈ (S₁ ∩ bd S) \ {x, y})
    {J : Hypergraph α β} (hJ_sigma : J ∈ sigmaJumps Γ Γ_sub ιV)
    (hterm : terminals J = {ιV x, ιV y}) :
    J ∉ sigmaJumps (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE S₁)
      (ιV ∘ Subtype.val) := by
  intro hJ_side
  have hiso := hP.drawing_iso
  have hK_link := IsExhaustiveLinkage.isLinkage hP hL
  have h2 : ∀ e ∈ Γ_sub.edgeSet, (Γ_sub.ends e).ncard = 2 := fun e he =>
    hK_link.ends_ncard_eq_two he
  have hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)) := by
    rw [← sigmaJumps_eq_jumpSet hiso]
    exact hJ_sigma
  have hxJ : ιV x ∈ J.vertexSet := (show ιV x ∈ terminals J from hterm ▸ Or.inl rfl).1
  have hyJ : ιV y ∈ J.vertexSet := (show ιV y ∈ terminals J from hterm ▸ Or.inr rfl).1
  obtain ⟨w⟩ := hJ.2.1.2.2.1 (ιV x) hxJ (ιV y) hyJ
  obtain ⟨K, hKc, hKconn, hxK, hyK, hKpts⟩ :=
    exists_points_of_walk hiso h2 hJ.1 w hxJ x hxV rfl y hyV rfl
  have hJ_le : J ≤ sideSub Γ Γ_sub ιV ιE S₁ := hJ_side.1
  have hK_S₁ : K ⊆ S₁ := by
    intro p hp
    rcases hKpts p hp with ⟨e, he, heJ, hpe⟩ | ⟨hpV, hpJ⟩
    · obtain ⟨e', ⟨he', he'S₁⟩, he'eq⟩ := (hJ_le.edgeSet_subset heJ).1
      rw [← hiso.ιE_injOn he' he he'eq] at hpe
      exact he'S₁ hpe
    · obtain ⟨p', ⟨hp'V, hp'S₁⟩, hp'eq⟩ := (hJ_le.vertexSet_subset hpJ).1
      rw [← hiso.ιV_injOn hp'V hpV hp'eq]
      exact hp'S₁
  have hK_U : K ⊆ Γ.U := by
    intro p hp
    rcases hKpts p hp with ⟨e, he, -, hpe⟩ | ⟨hpV, -⟩
    · exact (he.2.1 hpe).1
    · exact Γ.V_subset_U hpV
  have hK_bd : K ∩ bd S ⊆ {x, y} := by
    rintro p ⟨hpK, hpbd⟩
    have hpV : p ∈ Γ.V := hP.is_proper_drawing ⟨hpbd, hK_U hpK⟩
    have hpJ : ιV p ∈ J.vertexSet := by
      rcases hKpts p hpK with ⟨e, he, -, hpe⟩ | ⟨-, hpJ⟩
      · exact ((he.2.1 hpe).2 hpV).elim
      · exact hpJ
    have hpT : ιV p ∈ terminals J :=
      mem_terminals_of_mem_jumpSet hJ hpJ (mem_image_of_mem ιV ⟨hpV, hpbd⟩)
    rw [hterm] at hpT
    rcases hpT with h1 | h2
    · exact Or.inl (hiso.ιV_injOn hpV hxV h1)
    · exact Or.inr (hiso.ιV_injOn hpV hyV h2)
  -- Pick an interior point `v₀' ∈ F \ {x, y} ⊆ r₀ \ bd S`.
  obtain ⟨gF, hgF, hgFr, hgF0, hgF1⟩ := h.proper.1.exists_arc
  let thalf : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let v₀' : S := gF thalf
  have hv₀'F : v₀' ∈ F := hgFr ▸ ⟨thalf, rfl⟩
  have hv₀'ne : v₀' ∉ ({x, y} : Set S) := by
    rintro (h1 | h2)
    · have := congrArg Subtype.val (hgF.2 (h1.trans hgF0.symm))
      change (1 / 2 : ℝ) = 0 at this; norm_num at this
    · have := congrArg Subtype.val (hgF.2 (h2.trans hgF1.symm))
      change (1 / 2 : ℝ) = 1 at this; norm_num at this
  have hv₀'r : v₀' ∈ r₀ \ bd S := (hFsub hv₀'F).resolve_left hv₀'ne
  have hjoined := DiscLine.joinedIn_of_mem_closure hD hP.is_proper_drawing hr₀
    (Γ.V_subset_U hzV) hzr hv₀'r
  have hzv₀' : z ≠ v₀' := fun heq => hv₀'r.2 (heq ▸ hz.1.2)
  obtain ⟨L_arc, hL_sub, hL_line⟩ :=
    ((GM07.joinedIn_iff_eq_or_exists_isLineWithEnds hjoined.source_mem hjoined.target_mem).mp
      hjoined).resolve_left hzv₀'
  obtain ⟨gb, hgb, hgbr, hgb0, hgb1⟩ := hL_line.exists_arc
  have hgb_ext0 : extI gb 0 = z := (extI_of_mem gb ⟨le_rfl, zero_le_one⟩).trans hgb0
  have hgb_ext1 : extI gb 1 = v₀' := (extI_of_mem gb ⟨zero_le_one, le_rfl⟩).trans hgb1
  -- Stop `gb` at its first hit `t₀` on the closed set `F`.
  let T : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | extI gb t ∈ F}
  have hT_closed : IsClosed T :=
    isClosed_Icc.inter (h.isClosed_line.preimage (continuous_extI hgb.1))
  have hT_ne : T.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, hgb_ext1.symm ▸ hv₀'F⟩
  have hT_bdd : BddBelow T := bddBelow_Icc.mono fun _ ht => ht.1
  let t₀ : ℝ := sInf T
  have ht₀ : t₀ ∈ T := hT_closed.csInf_mem hT_ne hT_bdd
  have hz_notF : z ∉ F := fun hzF => hz.2 (h.inter_bd ▸ ⟨hzF, hz.1.2⟩)
  have ht₀_pos : 0 < t₀ := by
    refine lt_of_le_of_ne ht₀.1.1 ?_
    intro heq
    apply hz_notF
    have : extI gb 0 ∈ F := heq ▸ ht₀.2
    rwa [hgb_ext0] at this
  let v₀ : S := extI gb t₀
  have hv₀F : v₀ ∈ F := ht₀.2
  have hv₀L : v₀ ∈ L_arc := by
    change extI gb t₀ ∈ L_arc
    rw [← hgbr, extI_of_mem gb ht₀.1]
    exact ⟨⟨t₀, ht₀.1⟩, rfl⟩
  have hv₀z : v₀ ≠ z := by
    intro heq
    have h1 : gb ⟨t₀, ht₀.1⟩ = gb 0 := by
      rw [← extI_of_mem gb ht₀.1, hgb0]
      exact heq
    have h2 := congrArg Subtype.val (hgb.2 h1)
    exact ht₀_pos.ne' h2
  have hv₀r : v₀ ∈ r₀ \ bd S := (hL_sub hv₀L).resolve_left hv₀z
  have hv₀x : v₀ ≠ x := fun heq => hv₀r.2 (heq ▸ h.ends_mem_bd.1)
  have hv₀y : v₀ ≠ y := fun heq => hv₀r.2 (heq ▸ h.ends_mem_bd.2)
  let B : Set S := extI gb '' Icc 0 t₀
  have hBc : IsCompact B := isCompact_Icc.image (continuous_extI hgb.1)
  have hBconn : IsConnected B :=
    (isConnected_Icc ht₀.1.1).image _ (continuous_extI hgb.1).continuousOn
  have hzB : z ∈ B := ⟨0, ⟨le_rfl, ht₀.1.1⟩, hgb_ext0⟩
  have hv₀B : v₀ ∈ B := ⟨t₀, ⟨ht₀.1.1, le_rfl⟩, rfl⟩
  have hB_L : B ⊆ L_arc := by
    rintro _ ⟨t, ht, rfl⟩
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.1.2⟩
    rw [← hgbr, extI_of_mem gb ht1]
    exact ⟨⟨t, ht1⟩, rfl⟩
  have hB₀_S₁ : extI gb '' Ico 0 t₀ ⊆ S₁ := by
    refine Side.subset_side h.isClosed_left h.isClosed_right h.union_eq h.inter_eq
      (isPreconnected_Ico.image _ (continuous_extI hgb.1).continuousOn) ?_
      ⟨z, ⟨0, ⟨le_rfl, ht₀_pos⟩, hgb_ext0⟩, hz.1.1⟩
    rw [disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ htF
    have hle := csInf_le hT_bdd ⟨⟨ht.1, ht.2.le.trans ht₀.1.2⟩, htF⟩
    linarith [ht.2]
  have hB_S₁ : B ⊆ S₁ := by
    rintro _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.2 with rfl | hlt
    · exact h.line_subset_left hv₀F
    · exact hB₀_S₁ ⟨t, ⟨ht.1, hlt⟩, rfl⟩
  -- `(S₁ ∩ bd S)` and `F` form `discBd S₁` and cross at `(x, y)` and `(z, v₀)`.
  have hdiscBd : (S₁ ∩ bd S) ∪ F = discBd S₁ := by
    ext p
    simp only [discBd, mem_image, h.mem_bd_iff hP.is_surface]
    constructor
    · rintro (⟨hpS₁, hpbd⟩ | hpF)
      · exact ⟨⟨p, hpS₁⟩, Or.inr hpbd, rfl⟩
      · exact ⟨⟨p, h.line_subset_left hpF⟩, Or.inl hpF, rfl⟩
    · rintro ⟨⟨a, haS₁⟩, haF | habd, rfl⟩
      · exact Or.inr haF
      · exact Or.inl ⟨haS₁, habd⟩
  have hdiscInter : (S₁ ∩ bd S) ∩ F = {x, y} := by
    rw [Set.inter_assoc, Set.inter_comm (bd S) F, h.inter_bd, inter_eq_right]
    rintro p (rfl | rfl)
    exacts [h.line_subset_left h.proper.1.left_mem, h.line_subset_left h.proper.1.right_mem]
  have hzx : z ≠ x := fun heq => hz.2 (Or.inl heq)
  have hzy : z ≠ y := fun heq => hz.2 (Or.inr heq)
  have hcross := pairsCross_of_lines_disc hJ₁ h.proper.1 hdiscBd hdiscInter
    hz.1 hv₀F hzx hzy hv₀x hv₀y
  obtain ⟨p, hpK, hpB⟩ := disc_crossing S₁ K B x y z v₀ hD₁ hK_S₁ hB_S₁ hKc hBc hKconn hBconn
    hxK hyK hzB hv₀B hcross
  rcases hL_sub (hB_L hpB) with rfl | hpr
  · exact hz.2 (hK_bd ⟨hpK, hz.1.2⟩)
  · rcases hr₀ with ⟨_, _, rfl⟩
    exact (connectedComponentIn_subset _ _ hpr.1).2 (hK_U hpK)

/-- If a side `D` of a line `F` in `S` is a closed disc and meets `F_star` in two supports
`j_a ≠ j_b` while missing the third support `j_c`, then the `D` side has at most `lam'` jumps. -/
theorem encard_side_le_of_two_supports {F_star : Fin 3 → Set S} {H : Fin 3 → Hypergraph α β}
    {q : Fin 3 → ℕ} (hP : IsPresentation G Γ Γ_sub ιV ιE 3 F_star H μ q) (hG : G.IsGraph)
    {d p lam' : ℕ} (hq : ∀ j, q j ≤ d) {L : Hypergraph α β}
    (hL : IsExhaustiveLinkage G Γ_sub 3 H L) (hLp : IsPLinkage G L p)
    {D D' F : Set S} {u v : S} (h : IsSideOfLine Γ D D' F u v) (hD_disc : GM06.IsClosedDiscSpace D)
    {j_a j_b j_c : Fin 3} (hab : j_a ≠ j_b)
    (hsup_a : IsSupportOfDrawing Γ (F_star j_a ∩ D))
    (hsup_b : IsSupportOfDrawing Γ (F_star j_b ∩ D))
    (hemp_c : F_star j_c ∩ D = ∅)
    (hcov : ∀ j : Fin 3, j = j_a ∨ j = j_b ∨ j = j_c)
    (hb : ∀ {S' : Type w} [TopologicalSpace S'] (G' : Hypergraph α β)
      (Γ' : Surface.Drawing S') (Γ_sub' : Hypergraph α β) (ιV' : S' → α) (ιE' : Set S' → β)
      (F' : Fin 2 → Set S') (H' : Fin 2 → Hypergraph α β) (μ' : BoundaryUnit S' → Hypergraph α β)
      (L' : Hypergraph α β), GM06.IsClosedDiscSpace S' → G'.IsGraph →
      PresentationHasDepthLe G' Γ' Γ_sub' ιV' ιE' 2 F' H' μ' d →
      IsExhaustiveLinkage G' Γ_sub' 2 H' L' → IsPLinkage G' L' (p + 2 * d) →
      (sigmaJumps Γ' Γ_sub' ιV').encard ≤ lam') :
    (sigmaJumps (sideDrawing Γ h.isClosed_left) (sideSub Γ Γ_sub ιV ιE D)
      (ιV ∘ Subtype.val)).encard ≤ lam' := by
  let σ : Fin 2 → Fin 3 := ![j_a, j_b]
  have hσ : Injective σ := by
    intro i₁ i₂ h_eq
    fin_cases i₁ <;> fin_cases i₂ <;> simp_all [σ, hab.symm]
  have hsup : ∀ i : Fin 2, IsSupportOfDrawing Γ (F_star (σ i) ∩ D) := by
    rw [Fin.forall_fin_two]
    exact ⟨hsup_a, hsup_b⟩
  have hall : ∀ j : Fin 3, (F_star j ∩ D).Nonempty → ∃ i : Fin 2, σ i = j := by
    intro j hj
    rcases hcov j with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · rw [hemp_c] at hj
      exact hj.ne_empty rfl |>.elim
  have hcD : ConnectedSpace D := connectedSpace_of_isClosedDiscSpace hD_disc
  obtain ⟨hL_D, hLp_D⟩ := isExhaustiveLinkage_side hP h hq hsup hall hL hLp
  exact hb _ _ _ _ _ _ _ _ _ hD_disc (isGraph_of_le (sideGraph_le hP h.isClosed_left) hG)
    (presentationHasDepthLe_side hP h hq hcD hσ hsup hall) hL_D hLp_D

private theorem ends_mem_side_bd (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hW : DiscCut.Window Γ F_star f w₀ w₁ a b) {D D' F : Set S} {u v : S}
    (hs : IsSideOfLine Γ D D' F u v) {J : Hypergraph α β}
    (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)))
    (hJD : J ∈ sigmaJumps (sideDrawing Γ hs.isClosed_left) (sideSub Γ Γ_sub ιV ιE D)
      (ιV ∘ Subtype.val)) :
    cp (jumpLo f w₀ w₁ Γ.V ιV J) ∈ D ∩ bd S ∧ cp (jumpHi f w₀ w₁ Γ.V ιV J) ∈ D ∩ bd S := by
  have hiso := hP.drawing_iso
  have hspec := hW.jumpAngles_spec hP hJ
  have hloJ : ιV (cp (jumpLo f w₀ w₁ Γ.V ιV J)) ∈ J.vertexSet :=
    (show ιV (cp (jumpLo f w₀ w₁ Γ.V ιV J)) ∈ terminals J from hspec.2.2.2.2.2 ▸ Or.inl rfl).1
  have hhiJ : ιV (cp (jumpHi f w₀ w₁ Γ.V ιV J)) ∈ J.vertexSet :=
    (show ιV (cp (jumpHi f w₀ w₁ Γ.V ιV J)) ∈ terminals J from hspec.2.2.2.2.2 ▸ Or.inr rfl).1
  obtain ⟨u₁, ⟨hu₁V, hu₁D⟩, hu₁eq⟩ := (hJD.1.vertexSet_subset hloJ).1
  obtain ⟨u₂, ⟨hu₂V, hu₂D⟩, hu₂eq⟩ := (hJD.1.vertexSet_subset hhiJ).1
  rw [← hiso.ιV_injOn hu₁V hspec.2.2.2.1 hu₁eq]
  rw [← hiso.ιV_injOn hu₂V hspec.2.2.2.2.1 hu₂eq]
  exact ⟨⟨hu₁D, hiso.ιV_injOn hu₁V hspec.2.2.2.1 hu₁eq ▸ GM17.cuffPoint_mem f _⟩,
    ⟨hu₂D, hiso.ιV_injOn hu₂V hspec.2.2.2.2.1 hu₂eq ▸ GM17.cuffPoint_mem f _⟩⟩

private theorem fin3_cover {j₁ j₂ j₃ : Fin 3} (h12 : j₁ ≠ j₂) (h23 : j₂ ≠ j₃) (h13 : j₁ ≠ j₃)
    (j : Fin 3) : j = j₁ ∨ j = j₂ ∨ j = j₃ := by
  omega

set_option maxHeartbeats 400000 in
/-- **The cutting step of (6.6) for `r = 3`** (Graph Minors XXI, page 27 of the preprint).
A region `r₀` incident with vertices in all three supports cuts the disc into three closed discs
`Δ₁, Δ₂, Δ₃`, each carrying a presentation of depth `≤ d` and defect 2 with an exhaustive vital
`(p + 2d)`-linkage, and every `Σ`-jump belongs to one of `Δ₁, Δ₂, Δ₃`. Hence `Γ` has at most
`3 * lam'` jumps. The graph at `Δ₁` is $\Gamma \cap \Delta_1 \cup \mu(F_2^* \cap J_1) \cup
\mu(F_3^* \cap J_1)$; the print writes $\cup$ inside $\mu$, and names the presentation with
$H_1, H_2, H_2$ (see the correction to the proof of (6.6) in `corrections/GM21.md`). -/
theorem encard_sigmaJumps_le_three_of_region {F_star : Fin 3 → Set S} {H : Fin 3 → Hypergraph α β}
    {q : Fin 3 → ℕ} (hD : GM06.IsClosedDiscSpace S)
    (hP : IsPresentation G Γ Γ_sub ιV ιE 3 F_star H μ q) (hG : G.IsGraph) {d p lam' : ℕ}
    (hq : ∀ j, q j ≤ d) {L : Hypergraph α β} (hL : IsExhaustiveLinkage G Γ_sub 3 H L)
    (hLp : IsPLinkage G L p) {a b : Fin 3 → ℝ} (hW : DiscCut.Window Γ F_star f w₀ w₁ a b)
    (hb : ∀ {S' : Type w} [TopologicalSpace S'] (G' : Hypergraph α β)
      (Γ' : Surface.Drawing S') (Γ_sub' : Hypergraph α β) (ιV' : S' → α) (ιE' : Set S' → β)
      (F' : Fin 2 → Set S') (H' : Fin 2 → Hypergraph α β) (μ' : BoundaryUnit S' → Hypergraph α β)
      (L' : Hypergraph α β), GM06.IsClosedDiscSpace S' → G'.IsGraph →
      PresentationHasDepthLe G' Γ' Γ_sub' ιV' ιE' 2 F' H' μ' d →
      IsExhaustiveLinkage G' Γ_sub' 2 H' L' → IsPLinkage G' L' (p + 2 * d) →
      (sigmaJumps Γ' Γ_sub' ιV').encard ≤ lam') :
    (sigmaJumps Γ Γ_sub ιV).encard ≤ 3 * lam' := by
  classical
  have hS := hP.is_surface
  have hC := DiscCut.bd_mem_cuffs hD
  have hpi := Real.pi_pos
  have hlt := hW.lt_add
  have hiso := hP.drawing_iso
  obtain ⟨r₀, hr₀, j₁, j₂, j₃, θ₁, θ₂, θ₃, hθ₁, hθ₂, hθ₃, hb₁a₂, hb₂a₃,
    hv₁, hc₁, hv₂, hc₂, hv₃, hc₃, -⟩ :=
    exists_region_three_supports hD hP hW hL le_rfl
  have h12 : θ₁ < θ₂ := hθ₁.2.trans_lt (hb₁a₂.trans_le hθ₂.1)
  have h23 : θ₂ < θ₃ := hθ₂.2.trans_lt (hb₂a₃.trans_le hθ₃.1)
  have h13 : θ₁ < θ₃ := h12.trans h23
  have hw₁ : w₀ ≤ θ₁ := (hW.le_a j₁).trans hθ₁.1
  have hw₂ : w₀ ≤ θ₂ := (hW.le_a j₂).trans hθ₂.1
  have hw₃ : θ₃ ≤ w₁ := hθ₃.2.trans (hW.b_le j₃)
  have hm₁ : θ₁ ∈ Icc w₀ w₁ := ⟨hw₁, h13.le.trans hw₃⟩
  have hm₂ : θ₂ ∈ Icc w₀ w₁ := ⟨hw₂, h23.le.trans hw₃⟩
  have hm₃ : θ₃ ∈ Icc w₀ w₁ := ⟨hw₁.trans h13.le, hw₃⟩
  have hj₁₂ : j₁ ≠ j₂ := fun h => by subst h; linarith only [hW.a_le_b j₁, hb₁a₂]
  have hj₂₃ : j₂ ≠ j₃ := fun h => by subst h; linarith only [hW.a_le_b j₂, hb₂a₃]
  have hj₁₃ : j₁ ≠ j₃ := fun h => by subst h; linarith only [hW.a_le_b j₁, hW.a_le_b j₂, hb₁a₂, hb₂a₃]
  have hcov : ∀ j : Fin 3, j = j₁ ∨ j = j₂ ∨ j = j₃ := fin3_cover hj₁₂ hj₂₃ hj₁₃
  -- Helper to cut `S` between `θx < θy` in `closure r₀`.
  have hcut : ∀ {θx θy : ℝ}, w₀ ≤ θx → θx < θy → θy ≤ w₁ →
      cp θx ∈ Γ.V → cp θy ∈ Γ.V → cp θx ∈ closure r₀ → cp θy ∈ closure r₀ →
      ∃ F D₁ D₂ : Set S, F ⊆ {cp θx, cp θy} ∪ (r₀ \ bd S) ∧
        IsSideOfLine Γ D₁ D₂ F (cp θx) (cp θy) ∧
        GM06.IsClosedDiscSpace D₁ ∧ GM06.IsClosedDiscSpace D₂ ∧
        D₁ ∩ bd S = cp '' Icc θx θy ∧
        D₂ ∩ bd S = cp '' Icc θy (θx + 2 * Real.pi) := by
    intro θx θy hx hxy hy hxV hyV hxr hyr
    have hne : cp θx ≠ cp θy := fun h =>
      hxy.ne (angle_injOn f hlt ⟨hx, hxy.le.trans hy⟩ ⟨hx.trans hxy.le, hy⟩ h)
    obtain ⟨F, hF, hFsub⟩ :=
      DiscLine.exists_line_in_region hD hP.is_proper_drawing hr₀ hxV hyV hne hxr hyr
    obtain ⟨hFbd', hFU⟩ := DiscLine.inter_eq_of_subset_region hr₀ hFsub
    have hFbd : F ∩ bd S = {cp θx, cp θy} := by
      refine Subset.antisymm hFbd' ?_
      rintro z (rfl | rfl)
      · exact ⟨hF.left_mem, GM17.cuffPoint_mem f θx⟩
      · exact ⟨hF.right_mem, GM17.cuffPoint_mem f θy⟩
    obtain ⟨D₁, D₂, h, hD₁, hD₂, hbd₁, hbd₂⟩ :=
      exists_disc_sides hD f hxy (by linarith only [hx, hy, hlt]) hF hFbd hxV hyV hFU
    exact ⟨F, D₁, D₂, hFsub, h, hD₁, hD₂, hbd₁, hbd₂⟩
  -- Cut 1: between `θ₂` and `θ₃` (`Δ₁` and `Δ₁'`).
  obtain ⟨F₂₃, Δ₁, Δ₁', hF₂₃_sub, h₁, hD₁, hD₁', hbd₁, hbd₁'⟩ :=
    hcut hw₂ h23 hw₃ hv₂ hv₃ hc₂ hc₃
  -- Cut 2: between `θ₁` and `θ₃` (`Δ₂'` and `Δ₂`).
  obtain ⟨F₁₃, Δ₂', Δ₂, hF₁₃_sub, h₂, hD₂', hD₂, hbd₂', hbd₂⟩ :=
    hcut hw₁ h13 hw₃ hv₁ hv₃ hc₁ hc₃
  -- Cut 3: between `θ₁` and `θ₂` (`Δ₃` and `Δ₃'`).
  obtain ⟨F₁₂, Δ₃, Δ₃', hF₁₂_sub, h₃, hD₃, hD₃', hbd₃, hbd₃'⟩ :=
    hcut hw₁ h12 (h23.le.trans hw₃) hv₁ hv₂ hc₁ hc₂
  have hinter : ∀ j D, F_star j ∩ D = F_star j ∩ (D ∩ bd S) := fun j D => by
    rw [← Set.inter_assoc, Set.inter_right_comm, inter_eq_left.mpr
      (subset_bd_of_isSupportOfDrawing (hP.supports_isSupport j))]
  -- Bound on `Δ₁` (supports `j₂, j₃`, misses `j₁`).
  have h_le₁ : (sigmaJumps (sideDrawing Γ h₁.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₁)
      (ιV ∘ Subtype.val)).encard ≤ lam' := by
    refine encard_side_le_of_two_supports hP hG hq hL hLp h₁ hD₁ hj₂₃ ?_ ?_ (j_c := j₁) ?_
      (fun j => ?_) hb
    · rw [hinter, hbd₁, window_inter_left hW j₂ hw₂ hw₃, max_eq_right hθ₂.1,
        min_eq_left (hb₂a₃.le.trans hθ₃.1)]
      exact isSupport_of_Icc hS hC hW hw₂ (hW.b_le j₂) hv₂ (hW.b_mem j₂)
        ⟨cp θ₂, θ₂, ⟨le_rfl, hθ₂.2⟩, rfl⟩
    · rw [hinter, hbd₁, window_inter_left hW j₃ hw₂ hw₃,
        max_eq_left (hθ₂.2.trans hb₂a₃.le), min_eq_right hθ₃.2]
      exact isSupport_of_Icc hS hC hW (hW.le_a j₃) hw₃ (hW.a_mem j₃) hv₃
        ⟨cp θ₃, θ₃, ⟨hθ₃.1, le_rfl⟩, rfl⟩
    · rw [hinter, hbd₁, window_inter_left hW j₁ hw₂ hw₃, Icc_eq_empty, image_empty]
      rw [not_le]
      exact (min_le_left _ _).trans_lt (hb₁a₂.trans_le (hθ₂.1.trans (le_max_right _ _)))
    · rcases hcov j with rfl | rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  -- Bound on `Δ₂` (supports `j₁, j₃`, misses `j₂`).
  have h_le₂ : (sigmaJumps (sideDrawing Γ h₂.symm.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₂)
      (ιV ∘ Subtype.val)).encard ≤ lam' := by
    refine encard_side_le_of_two_supports hP hG hq hL hLp h₂.symm hD₂ hj₁₃ ?_ ?_ (j_c := j₂) ?_
      (fun j => ?_) hb
    · rw [hinter, hbd₂, hW.F_eq j₁]
      have heq₁ : cp '' Icc (a j₁) (b j₁) ∩ cp '' Icc θ₃ (θ₁ + 2 * Real.pi) =
          cp '' Icc (a j₁) θ₁ := by
        ext z; constructor
        · rintro ⟨⟨t, ht, rfl⟩, hz⟩
          rcases (mem_image_right_iff hlt hw₁ h13 hw₃ (hW.Icc_subset j₁ ht)).mp hz with h' | h'
          · exact ⟨t, ⟨ht.1, h'⟩, rfl⟩
          · linarith only [ht.2, hb₁a₂, hθ₂.1, h23, h']
        · rintro ⟨t, ht, rfl⟩
          have ht' : t ∈ Icc (a j₁) (b j₁) := ⟨ht.1, ht.2.trans hθ₁.2⟩
          exact ⟨⟨t, ht', rfl⟩,
            (mem_image_right_iff hlt hw₁ h13 hw₃ (hW.Icc_subset j₁ ht')).mpr (Or.inl ht.2)⟩
      rw [heq₁]
      exact isSupport_of_Icc hS hC hW (hW.le_a j₁) hm₁.2 (hW.a_mem j₁) hv₁
        ⟨cp θ₁, θ₁, ⟨hθ₁.1, le_rfl⟩, rfl⟩
    · rw [hinter, hbd₂, hW.F_eq j₃]
      have heq₃ : cp '' Icc (a j₃) (b j₃) ∩ cp '' Icc θ₃ (θ₁ + 2 * Real.pi) =
          cp '' Icc θ₃ (b j₃) := by
        ext z; constructor
        · rintro ⟨⟨t, ht, rfl⟩, hz⟩
          rcases (mem_image_right_iff hlt hw₁ h13 hw₃ (hW.Icc_subset j₃ ht)).mp hz with h' | h'
          · linarith only [ht.1, hb₁a₂, hθ₁.2, hW.a_le_b j₂, hb₂a₃, h']
          · exact ⟨t, ⟨h', ht.2⟩, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          have ht' : t ∈ Icc (a j₃) (b j₃) := ⟨hθ₃.1.trans ht.1, ht.2⟩
          exact ⟨⟨t, ht', rfl⟩,
            (mem_image_right_iff hlt hw₁ h13 hw₃ (hW.Icc_subset j₃ ht')).mpr (Or.inr ht.1)⟩
      rw [heq₃]
      exact isSupport_of_Icc hS hC hW hm₃.1 (hW.b_le j₃) hv₃ (hW.b_mem j₃)
        ⟨cp θ₃, θ₃, ⟨le_rfl, hθ₃.2⟩, rfl⟩
    · rw [hinter, hbd₂, hW.F_eq j₂, eq_empty_iff_forall_notMem]
      rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
      rcases (mem_image_right_iff hlt hw₁ h13 hw₃ (hW.Icc_subset j₂ ht)).mp hz with h' | h'
      · linarith only [ht.1, hb₁a₂, hθ₁.2, h']
      · linarith only [ht.2, hb₂a₃, hθ₃.1, h']
    · rcases hcov j with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
  -- Bound on `Δ₃` (supports `j₁, j₂`, misses `j₃`).
  have h_le₃ : (sigmaJumps (sideDrawing Γ h₃.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₃)
      (ιV ∘ Subtype.val)).encard ≤ lam' := by
    refine encard_side_le_of_two_supports hP hG hq hL hLp h₃ hD₃ hj₁₂ ?_ ?_ (j_c := j₃) ?_ hcov hb
    · rw [hinter, hbd₃, window_inter_left hW j₁ hw₁ hm₂.2, max_eq_right hθ₁.1,
        min_eq_left (hb₁a₂.le.trans hθ₂.1)]
      exact isSupport_of_Icc hS hC hW hw₁ (hW.b_le j₁) hv₁ (hW.b_mem j₁)
        ⟨cp θ₁, θ₁, ⟨le_rfl, hθ₁.2⟩, rfl⟩
    · rw [hinter, hbd₃, window_inter_left hW j₂ hw₁ hm₂.2,
        max_eq_left (hθ₁.2.trans hb₁a₂.le), min_eq_right hθ₂.2]
      exact isSupport_of_Icc hS hC hW (hW.le_a j₂) hm₂.2 (hW.a_mem j₂) hv₂
        ⟨cp θ₂, θ₂, ⟨hθ₂.1, le_rfl⟩, rfl⟩
    · rw [hinter, hbd₃, window_inter_left hW j₃ hw₁ hm₂.2, Icc_eq_empty, image_empty]
      rw [not_le]
      exact (min_le_right _ _).trans_lt ((hθ₂.2.trans_lt hb₂a₃).trans_le (le_max_left _ _))
  -- Every jump in `sigmaJumps Γ Γ_sub ιV` belongs to `Δ₁`, `Δ₂`, or `Δ₃`.
  have hJ_sub : sigmaJumps Γ Γ_sub ιV ⊆
      (sigmaJumps (sideDrawing Γ h₁.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₁)
        (ιV ∘ Subtype.val) ∪
      sigmaJumps (sideDrawing Γ h₂.symm.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₂)
        (ιV ∘ Subtype.val)) ∪
      sigmaJumps (sideDrawing Γ h₃.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₃)
        (ιV ∘ Subtype.val) := by
    intro J hJ_sigma
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨hnot₁, hnot₂⟩, hnot₃⟩ := hnot
    have hJ₁' : J ∈ sigmaJumps (sideDrawing Γ h₁.symm.isClosed_left)
        (sideSub Γ Γ_sub ιV ιE Δ₁') (ιV ∘ Subtype.val) :=
      (sigmaJumps_subset_side hP h₁ hJ_sigma).resolve_left hnot₁
    have hJ₂' : J ∈ sigmaJumps (sideDrawing Γ h₂.isClosed_left)
        (sideSub Γ Γ_sub ιV ιE Δ₂') (ιV ∘ Subtype.val) :=
      (sigmaJumps_subset_side hP h₂ hJ_sigma).resolve_right hnot₂
    have hJ₃' : J ∈ sigmaJumps (sideDrawing Γ h₃.symm.isClosed_left)
        (sideSub Γ Γ_sub ιV ιE Δ₃') (ιV ∘ Subtype.val) :=
      (sigmaJumps_subset_side hP h₃ hJ_sigma).resolve_left hnot₃
    have hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)) := by
      rw [← sigmaJumps_eq_jumpSet hiso]
      exact hJ_sigma
    have hspec := hW.jumpAngles_spec hP hJ
    have hlo_W := hW.jumpLo_mem hP hJ
    have hhi_W := hW.jumpHi_mem hP hJ
    obtain ⟨hlo₁', hhi₁'⟩ := ends_mem_side_bd hP hW h₁.symm hJ hJ₁'
    obtain ⟨hlo₂', hhi₂'⟩ := ends_mem_side_bd hP hW h₂ hJ hJ₂'
    obtain ⟨hlo₃', hhi₃'⟩ := ends_mem_side_bd hP hW h₃.symm hJ hJ₃'
    rw [hbd₁'] at hlo₁' hhi₁'
    rw [hbd₂'] at hlo₂' hhi₂'
    rw [hbd₃'] at hlo₃' hhi₃'
    have hlo_Icc : jumpLo f w₀ w₁ Γ.V ιV J ∈ Icc θ₁ θ₃ := by
      obtain ⟨t, ht, heq⟩ := hlo₂'
      rw [angle_injOn f hlt hlo_W (Icc_subset_Icc hw₁ hw₃ ht) heq.symm]
      exact ht
    have hhi_Icc : jumpHi f w₀ w₁ Γ.V ιV J ∈ Icc θ₁ θ₃ := by
      obtain ⟨t, ht, heq⟩ := hhi₂'
      rw [angle_injOn f hlt hhi_W (Icc_subset_Icc hw₁ hw₃ ht) heq.symm]
      exact ht
    have hlo_or₁ := (mem_image_right_iff hlt hw₂ h23 hw₃ hlo_W).mp hlo₁'
    have hhi_or₁ := (mem_image_right_iff hlt hw₂ h23 hw₃ hhi_W).mp hhi₁'
    have hlo_or₃ := (mem_image_right_iff hlt hw₁ h12 hm₂.2 hlo_W).mp hlo₃'
    have hhi_or₃ := (mem_image_right_iff hlt hw₁ h12 hm₂.2 hhi_W).mp hhi₃'
    have hlo_cases : jumpLo f w₀ w₁ Γ.V ιV J = θ₁ ∨ jumpLo f w₀ w₁ Γ.V ιV J = θ₂ := by
      rcases hlo_or₃ with h | h
      · exact Or.inl (le_antisymm h hlo_Icc.1)
      · rcases hlo_or₁ with h' | h'
        · exact Or.inr (le_antisymm h' h)
        · exfalso; linarith only [hspec.2.1, hhi_Icc.2, h']
    have hhi_cases : jumpHi f w₀ w₁ Γ.V ιV J = θ₂ ∨ jumpHi f w₀ w₁ Γ.V ιV J = θ₃ := by
      rcases hhi_or₁ with h | h
      · rcases hhi_or₃ with h' | h'
        · exfalso; linarith only [hspec.2.1, hlo_Icc.1, h']
        · exact Or.inl (le_antisymm h h')
      · exact Or.inr (le_antisymm hhi_Icc.2 h)
    have hinj := angle_injOn f hlt
    rcases hlo_cases with hlo_eq | hlo_eq <;> rcases hhi_cases with hhi_eq | hhi_eq
    · -- `(LO J, HI J) = (θ₁, θ₂)`: contradicts `J ∈ sigmaJumps(Δ₃')`.
      have hterm : terminals J = {ιV (cp θ₁), ιV (cp θ₂)} := by
        rw [hspec.2.2.2.2.2, hlo_eq, hhi_eq]
      have hline₃' : IsLineWithEnds (Δ₃' ∩ bd S) (cp θ₁) (cp θ₂) := by
        rw [hbd₃']
        have hl := isLineWithEnds_cuffPoint_Icc f
          (by linarith only [hw₁, hm₂.2, hlt] : θ₂ < θ₁ + 2 * Real.pi) (by linarith only [h12, hpi])
        rw [GM17.cuffPoint_add_two_pi f θ₁] at hl
        exact hl.symm
      have hz₃ : cp θ₃ ∈ (Δ₃' ∩ bd S) \ {cp θ₁, cp θ₂} := by
        rw [hbd₃']
        refine ⟨⟨θ₃, ⟨h23.le, by linarith only [hw₁, hw₃, hlt]⟩, rfl⟩, ?_⟩
        rintro (h | h)
        · exact h13.ne' (hinj hm₃ hm₁ h)
        · exact h23.ne' (hinj hm₃ hm₂ h)
      exact not_mem_sigmaJumps_of_ends_of_third hD hP hL hr₀ hv₁ hv₂ hv₃ hc₃ hF₁₂_sub
        h₃.symm hD₃' hline₃' hz₃ hJ_sigma hterm hJ₃'
    · -- `(LO J, HI J) = (θ₁, θ₃)`: contradicts `J ∈ sigmaJumps(Δ₂')`.
      have hterm : terminals J = {ιV (cp θ₁), ιV (cp θ₃)} := by
        rw [hspec.2.2.2.2.2, hlo_eq, hhi_eq]
      have hline₂' : IsLineWithEnds (Δ₂' ∩ bd S) (cp θ₁) (cp θ₃) := by
        rw [hbd₂']
        exact isLineWithEnds_cuffPoint_Icc f h13 (by linarith only [hw₁, hw₃, hlt])
      have hz₂ : cp θ₂ ∈ (Δ₂' ∩ bd S) \ {cp θ₁, cp θ₃} := by
        rw [hbd₂']
        refine ⟨⟨θ₂, ⟨h12.le, h23.le⟩, rfl⟩, ?_⟩
        rintro (h | h)
        · exact h12.ne' (hinj hm₂ hm₁ h)
        · exact h23.ne (hinj hm₂ hm₃ h)
      exact not_mem_sigmaJumps_of_ends_of_third hD hP hL hr₀ hv₁ hv₃ hv₂ hc₂ hF₁₃_sub
        h₂ hD₂' hline₂' hz₂ hJ_sigma hterm hJ₂'
    · exfalso; linarith only [hspec.2.1, hlo_eq, hhi_eq]
    · -- `(LO J, HI J) = (θ₂, θ₃)`: contradicts `J ∈ sigmaJumps(Δ₁')`.
      have hterm : terminals J = {ιV (cp θ₂), ιV (cp θ₃)} := by
        rw [hspec.2.2.2.2.2, hlo_eq, hhi_eq]
      have hline₁' : IsLineWithEnds (Δ₁' ∩ bd S) (cp θ₂) (cp θ₃) := by
        rw [hbd₁']
        have hl := isLineWithEnds_cuffPoint_Icc f
          (by linarith only [hw₂, hw₃, hlt] : θ₃ < θ₂ + 2 * Real.pi) (by linarith only [h23, hpi])
        rw [GM17.cuffPoint_add_two_pi f θ₂] at hl
        exact hl.symm
      have hz₁ : cp θ₁ ∈ (Δ₁' ∩ bd S) \ {cp θ₂, cp θ₃} := by
        rw [hbd₁']
        refine ⟨⟨θ₁ + 2 * Real.pi, ⟨by linarith only [hw₁, hw₃, hlt], by linarith only [h12]⟩,
          GM17.cuffPoint_add_two_pi f θ₁⟩, ?_⟩
        rintro (h | h)
        · exact h12.ne (hinj hm₁ hm₂ h)
        · exact h13.ne (hinj hm₁ hm₃ h)
      exact not_mem_sigmaJumps_of_ends_of_third hD hP hL hr₀ hv₂ hv₃ hv₁ hc₁ hF₂₃_sub
        h₁.symm hD₁' hline₁' hz₁ hJ_sigma hterm hJ₁'
  calc (sigmaJumps Γ Γ_sub ιV).encard
      ≤ ((sigmaJumps (sideDrawing Γ h₁.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₁)
            (ιV ∘ Subtype.val) ∪
          sigmaJumps (sideDrawing Γ h₂.symm.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₂)
            (ιV ∘ Subtype.val)) ∪
          sigmaJumps (sideDrawing Γ h₃.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₃)
            (ιV ∘ Subtype.val)).encard := encard_le_encard hJ_sub
    _ ≤ (sigmaJumps (sideDrawing Γ h₁.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₁)
            (ιV ∘ Subtype.val) ∪
          sigmaJumps (sideDrawing Γ h₂.symm.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₂)
            (ιV ∘ Subtype.val)).encard +
          (sigmaJumps (sideDrawing Γ h₃.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₃)
            (ιV ∘ Subtype.val)).encard := encard_union_le _ _
    _ ≤ (sigmaJumps (sideDrawing Γ h₁.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₁)
            (ιV ∘ Subtype.val)).encard +
          (sigmaJumps (sideDrawing Γ h₂.symm.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₂)
            (ιV ∘ Subtype.val)).encard +
          (sigmaJumps (sideDrawing Γ h₃.isClosed_left) (sideSub Γ Γ_sub ιV ιE Δ₃)
            (ιV ∘ Subtype.val)).encard := add_le_add (encard_union_le _ _) le_rfl
    _ ≤ (lam' : ℕ∞) + lam' + lam' := add_le_add (add_le_add h_le₁ h_le₂) h_le₃
    _ = 3 * (lam' : ℕ∞) := by
      rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl, add_mul, add_mul, one_mul]

/-- **The cutting step of (6.7) for `4 ≤ r`** (Graph Minors XXI, page 28 of the preprint).
When `4 ≤ r`, a region `r₀` incident with vertices in three supports `j₁, j₂, j₃` provides a pair
of boundary vertices in `closure r₀` satisfying the hypotheses of
`Side.encard_sigmaJumps_le_of_region`, so `Γ` has at most `lam + lam` jumps. -/
theorem encard_sigmaJumps_le_two_of_region_three (hD : GM06.IsClosedDiscSpace S)
    (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (hG : G.IsGraph) {d p lam : ℕ}
    (hq : ∀ j, q j ≤ d) {L : Hypergraph α β} (hL : IsExhaustiveLinkage G Γ_sub r H L)
    (hLp : IsPLinkage G L p) (hW : DiscCut.Window Γ F_star f w₀ w₁ a b)
    (hr4 : 4 ≤ r)
    (hb : ∀ {S' : Type w} [TopologicalSpace S'] {r' : ℕ} (G' : Hypergraph α β)
      (Γ' : Surface.Drawing S') (Γ_sub' : Hypergraph α β) (ιV' : S' → α) (ιE' : Set S' → β)
      (F' : Fin r' → Set S') (H' : Fin r' → Hypergraph α β) (μ' : BoundaryUnit S' → Hypergraph α β)
      (L' : Hypergraph α β), r' < r → GM06.IsClosedDiscSpace S' → G'.IsGraph →
      PresentationHasDepthLe G' Γ' Γ_sub' ιV' ιE' r' F' H' μ' d →
      IsExhaustiveLinkage G' Γ_sub' r' H' L' → IsPLinkage G' L' (p + 2 * d) →
      (sigmaJumps Γ' Γ_sub' ιV').encard ≤ lam) :
    (sigmaJumps Γ Γ_sub ιV).encard ≤ lam + lam := by
  classical
  obtain ⟨r₀, hr₀, j₁, j₂, j₃, θ₁, θ₂, θ₃, hθ₁, hθ₂, hθ₃, hb₁a₂, hb₂a₃,
    hv₁, hc₁, hv₂, hc₂, hv₃, hc₃, hb₂_lt⟩ :=
    exists_region_three_supports hD hP hW hL (by omega)
  have h12 : θ₁ < θ₂ := hθ₁.2.trans_lt (hb₁a₂.trans_le hθ₂.1)
  have h23 : θ₂ < θ₃ := hθ₂.2.trans_lt (hb₂a₃.trans_le hθ₃.1)
  have h13 : θ₁ < θ₃ := h12.trans h23
  -- Since `4 ≤ r`, there is a fourth support `j₄ ∉ {j₁, j₂, j₃}`.
  have hcard : ({j₁, j₂, j₃} : Finset (Fin r)).card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (by simp)))
  have hlt : ({j₁, j₂, j₃} : Finset (Fin r)).card < (Finset.univ : Finset (Fin r)).card := by
    rw [Finset.card_fin]; omega
  obtain ⟨j₄, -, hj₄⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj₄
  have hj₄₁ : j₄ ≠ j₁ := hj₄.1
  have hj₄₂ : j₄ ≠ j₂ := hj₄.2.1
  have hj₄₃ : j₄ ≠ j₃ := hj₄.2.2
  have hb₂a₄ : b j₂ < a j₄ := hb₂_lt j₄ hj₄₁ hj₄₂
  -- Helper: no support contains two angles from different supports.
  have hsep_of_diff : ∀ {j_x j_y : Fin r} {tx ty : ℝ},
      tx ∈ Icc (a j_x) (b j_x) → ty ∈ Icc (a j_y) (b j_y) → b j_x < a j_y →
      ∀ j, ¬ (a j ≤ tx ∧ ty ≤ b j) := by
    intro j_x j_y tx ty htx hty hlt' j ⟨h1, h2⟩
    by_cases hj : j = j_x
    · subst hj; linarith [htx.2, hlt', hty.1]
    · rcases hW.lt_or_lt hP hj with hba | hba <;> linarith [htx.1, htx.2, hty.1, hty.2]
  rcases hW.lt_or_lt hP hj₄₃ with hb₄a₃ | hb₃a₄
  · -- `b j₂ < a j₄ ≤ b j₄ < a j₃`: cut between `θ₂` and `θ₃`.
    exact Side.encard_sigmaJumps_le_of_region hD hP hG hq hL hLp hW hr₀
      ((hW.le_a j₂).trans hθ₂.1) h23 (hθ₃.2.trans (hW.b_le j₃)) hv₂ hv₃ hc₂ hc₃
      (hsep_of_diff hθ₂ hθ₃ hb₂a₃)
      ⟨j₁, Or.inl (hb₁a₂.trans_le hθ₂.1)⟩
      ⟨j₄, hθ₂.2.trans_lt hb₂a₄, hb₄a₃.trans_le hθ₃.1⟩ hb
  · -- `b j₃ < a j₄`: cut between `θ₁` and `θ₃`.
    exact Side.encard_sigmaJumps_le_of_region hD hP hG hq hL hLp hW hr₀
      ((hW.le_a j₁).trans hθ₁.1) h13 (hθ₃.2.trans (hW.b_le j₃)) hv₁ hv₃ hc₁ hc₃
      (hsep_of_diff hθ₁ hθ₃ (hb₁a₂.trans ((hW.a_le_b j₂).trans_lt hb₂a₃)))
      ⟨j₄, Or.inr (hθ₃.2.trans_lt hb₃a₄)⟩
      ⟨j₂, hθ₁.2.trans_lt hb₁a₂, hb₂a₃.trans_le hθ₃.1⟩ hb

end CuttingSteps

end ThreeSupports
end GM21
end GraphMinor
