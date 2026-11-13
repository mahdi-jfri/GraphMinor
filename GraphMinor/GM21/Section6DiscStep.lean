module

public import GraphMinor.GM21.Section6Cut
public import GraphMinor.GM21.Section6DiscSides
public import GraphMinor.GM21.Section6DiscSetup
import GraphMinor.GM21.Section6DiscLine

/-!
# Graph Minors XXI, proof of (6.7): the step that cuts the disc

The proof of (6.7) in *Graph Minors XXI* (pages 27–28 of the preprint) cuts the disc `Σ` along a
proper line `F` with ends `a, b ∈ V(Γ)` through a region, "such that both of the lines $J_1, J_2
\subseteq bd(\Sigma)$ with ends $a$ and $b$ are disjoint from at least one of $F_1^*, \dots,
F_r^*$". Then "$(\Gamma \cap \Delta_j) \cup \mu(J_i)$ has a presentation in $\Sigma$ with depth $\le
q$ and defect $< r$, and it has an exhaustive vital $(p + 2q)$-linkage", and "every $\Sigma$-jump
belongs to one of $\Delta_1, \Delta_2$". The print's $\mu(J_i)$ is a misprint for $\mu(J_j)$, and
Lean uses $\mu(J_j)$ (see the correction to the proof of (6.7) in `corrections/GM21.md`).

This file proves that step (`encard_sigmaJumps_le_of_region`). We read `bd(Σ)` by angles through a
window (`DiscCut.Window`): the support `F_j*` is the set of points with angles in `[a j, b j]`, and
the ends of `F` have angles `θx < θy` in the window. The first disc meets `bd(Σ)` in the angles
`[θx, θy]`, and the second in the other angles (`exists_disc_sides`). The supports of the two discs
are the nonempty sets `F_j* ∩ Δ_i` (`window_inter_left`, `window_inter_right`). They are supports
because no `F_j*` contains both ends of `F`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Side

open Set Function GraphMinor.Surface Hypergraph GraphMinor.GM21.Supports

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-! ## Listing the supports that meet a side -/

/-- The indices `j` with `P j` can be listed without repetition by `Fin r₁`, where `r₁` is their
number. -/
theorem exists_enum {r : ℕ} (P : Fin r → Prop) [DecidablePred P] :
    ∃ σ : Fin (Finset.univ.filter P).card → Fin r, Injective σ ∧ (∀ i, P (σ i)) ∧
      ∀ j, P j → ∃ i, σ i = j := by
  let T := Finset.univ.filter P
  refine ⟨fun i => (T.equivFin.symm i).1, ?_, ?_, ?_⟩
  · intro i i' h
    exact T.equivFin.symm.injective (Subtype.ext h)
  · intro i
    exact (Finset.mem_filter.mp (T.equivFin.symm i).2).2
  · intro j hj
    refine ⟨T.equivFin ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩, ?_⟩
    simp

/-- If some index fails `P`, fewer than `r` indices satisfy `P`. -/
theorem card_filter_lt {r : ℕ} (P : Fin r → Prop) [DecidablePred P] (h : ∃ j, ¬ P j) :
    (Finset.univ.filter P).card < r := by
  obtain ⟨j, hj⟩ := h
  calc (Finset.univ.filter P).card < Finset.univ.card :=
        Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨j, Finset.mem_univ _, hj⟩)
    _ = r := by simp

/-! ## Supports and angles -/

section window

variable {r : ℕ} {Γ : Surface.Drawing S} {F_star : Fin r → Set S} {f : Circle ≃ₜ bd S}
  {w₀ w₁ : ℝ} {a b : Fin r → ℝ}

set_option hygiene false in
local notation "cp" => GM19.cuffPoint f

/-- A nonempty set of points with angles in `[s, e]` in the window, where `s` and `e` are angles of
vertices, is a support. -/
theorem isSupport_of_Icc (hS : IsSurface S) (hC : bd S ∈ cuffs S)
    (hW : DiscCut.Window Γ F_star f w₀ w₁ a b) {s e : ℝ} (hs : w₀ ≤ s) (he : e ≤ w₁)
    (hsV : cp s ∈ Γ.V) (heV : cp e ∈ Γ.V) (hne : (cp '' Icc s e).Nonempty) :
    IsSupportOfDrawing Γ (cp '' Icc s e) := by
  have hse : s ≤ e := by
    obtain ⟨_, ⟨t, ht, -⟩⟩ := hne
    exact ht.1.trans ht.2
  exact ⟨_, _, supportHasEnds_cuffPoint_Icc hS hC f hs hse he hW.lt_add hsV heV⟩

/-- The part of `F_j*` with angles in `[θx, θy]`. -/
theorem window_inter_left (hW : DiscCut.Window Γ F_star f w₀ w₁ a b) (j : Fin r) {θx θy : ℝ}
    (hx : w₀ ≤ θx) (hy : θy ≤ w₁) :
    F_star j ∩ cp '' Icc θx θy = cp '' Icc (max (a j) θx) (min (b j) θy) := by
  rw [hW.F_eq j, ← (DiscCut.angle_injOn f hW.lt_add).image_inter (hW.Icc_subset j)
    (Icc_subset_Icc hx hy), Icc_inter_Icc]

/-- A point of the window has an angle in `[θy, θx + 2π]` exactly when its angle is at most `θx`
or at least `θy`. -/
theorem mem_image_right_iff (hlt : w₁ < w₀ + 2 * Real.pi) {θx θy t : ℝ} (hx : w₀ ≤ θx)
    (hxy : θx < θy) (hy : θy ≤ w₁) (ht : t ∈ Icc w₀ w₁) :
    cp t ∈ cp '' Icc θy (θx + 2 * Real.pi) ↔ t ≤ θx ∨ θy ≤ t := by
  have hpi := Real.pi_pos
  have hinj := GM17.cuffPoint_injOn_Ico f θy
  constructor
  · rintro ⟨s, hs, heq⟩
    have hsI : s ∈ Ico θy (θy + 2 * Real.pi) := ⟨hs.1, by linarith [hs.2]⟩
    by_cases hty : θy ≤ t
    · exact Or.inr hty
    · push Not at hty
      left
      have h2 : t + 2 * Real.pi ∈ Ico θy (θy + 2 * Real.pi) := ⟨by linarith [ht.1], by linarith⟩
      have := hinj hsI h2 (heq.trans (GM17.cuffPoint_add_two_pi f t).symm)
      linarith [hs.2]
  · rintro (h | h)
    · exact ⟨t + 2 * Real.pi, ⟨by linarith [ht.1], by linarith⟩, GM17.cuffPoint_add_two_pi f t⟩
    · exact ⟨t, ⟨h, by linarith [ht.2]⟩, rfl⟩

/-- The part of `F_j*` with angles in `[θy, θx + 2π]`, when `F_j*` does not contain both points of
angles `θx` and `θy`, is the set of points with angles in an interval whose ends are among
`a j, b j, θx, θy`. -/
theorem window_inter_right (hW : DiscCut.Window Γ F_star f w₀ w₁ a b) (j : Fin r) {θx θy : ℝ}
    (hx : w₀ ≤ θx) (hxy : θx < θy) (hy : θy ≤ w₁) (hj : ¬ (a j ≤ θx ∧ θy ≤ b j)) :
    ∃ s e : ℝ, (s = a j ∨ s = θy) ∧ (e = b j ∨ e = θx) ∧
      F_star j ∩ cp '' Icc θy (θx + 2 * Real.pi) = cp '' Icc s e := by
  have hiff : ∀ t ∈ Icc (a j) (b j),
      cp t ∈ cp '' Icc θy (θx + 2 * Real.pi) ↔ t ≤ θx ∨ θy ≤ t := fun t ht =>
    mem_image_right_iff hW.lt_add hx hxy hy (hW.Icc_subset j ht)
  have key : ∀ s e : ℝ, (∀ t ∈ Icc (a j) (b j), (t ≤ θx ∨ θy ≤ t) ↔ t ∈ Icc s e) →
      Icc s e ⊆ Icc (a j) (b j) →
      F_star j ∩ cp '' Icc θy (θx + 2 * Real.pi) = cp '' Icc s e := by
    intro s e hse hsub
    rw [hW.F_eq j]
    ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hz⟩
      exact ⟨t, (hse t ht).mp ((hiff t ht).mp hz), rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, hsub ht, rfl⟩, (hiff t (hsub ht)).mpr ((hse t (hsub ht)).mpr ht)⟩
  by_cases ha : a j ≤ θx
  · have hb : b j < θy := by
      by_contra h
      exact hj ⟨ha, not_lt.mp h⟩
    refine ⟨a j, min (b j) θx, Or.inl rfl, min_choice _ _, key _ _ ?_ ?_⟩
    · intro t ht
      constructor
      · rintro (h | h)
        · exact ⟨ht.1, le_min ht.2 h⟩
        · exact absurd (h.trans ht.2) (not_le.mpr hb)
      · intro h
        exact Or.inl (h.2.trans (min_le_right _ _))
    · exact Icc_subset_Icc le_rfl (min_le_left _ _)
  · push Not at ha
    refine ⟨max (a j) θy, b j, max_choice _ _, Or.inl rfl, key _ _ ?_ ?_⟩
    · intro t ht
      constructor
      · rintro (h | h)
        · exact absurd (ht.1.trans h) (not_le.mpr ha)
        · exact ⟨max_le ht.1 h, ht.2⟩
      · intro h
        exact Or.inr ((le_max_right _ _).trans h.1)
    · exact Icc_subset_Icc (le_max_left _ _) le_rfl

end window

/-! ## The step -/

section step

variable [T2Space S] {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {f : Circle ≃ₜ bd S} {w₀ w₁ : ℝ}
  {a b : Fin r → ℝ}

set_option hygiene false in
local notation "cp" => GM19.cuffPoint f

/-- **The cutting step of (6.7)** (Graph Minors XXI, pages 27–28 of the preprint). Let
`Γ, F_1*, …, F_r*, H_1, …, H_r, μ` be a presentation of `G` in a disc, of depth `≤ d`, with an
exhaustive vital `p`-linkage, and read `bd(Σ)` through a window. Let `x, y` be vertices of `Γ` at
angles `θx < θy` of the window, both in the closure of a region `r₀`. Suppose that no support
contains both, that some support has no angle in `[θx, θy]`, and that some support has all its
angles in `(θx, θy)`. If every presentation in a disc with fewer than `r` supports, of depth `≤ d`,
with an exhaustive vital `(p + 2d)`-linkage, has at most `λ` jumps, then `Γ` has at most `2λ` jumps.
-/
theorem encard_sigmaJumps_le_of_region (hD : GM06.IsClosedDiscSpace S)
    (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (hG : G.IsGraph) {d p lam : ℕ}
    (hq : ∀ j, q j ≤ d) {L : Hypergraph α β} (hL : IsExhaustiveLinkage G Γ_sub r H L)
    (hLp : IsPLinkage G L p) (hW : DiscCut.Window Γ F_star f w₀ w₁ a b)
    {r₀ : Set S} (hr₀ : r₀ ∈ Γ.R) {θx θy : ℝ} (hx : w₀ ≤ θx) (hxy : θx < θy) (hy : θy ≤ w₁)
    (hxV : cp θx ∈ Γ.V) (hyV : cp θy ∈ Γ.V) (hxr : cp θx ∈ closure r₀)
    (hyr : cp θy ∈ closure r₀) (hsep : ∀ j, ¬ (a j ≤ θx ∧ θy ≤ b j))
    (h₁ : ∃ j, b j < θx ∨ θy < a j) (h₂ : ∃ j, θx < a j ∧ b j < θy)
    (hb : ∀ {S' : Type w} [TopologicalSpace S'] {r' : ℕ} (G' : Hypergraph α β)
      (Γ' : Surface.Drawing S') (Γ_sub' : Hypergraph α β) (ιV' : S' → α) (ιE' : Set S' → β)
      (F' : Fin r' → Set S') (H' : Fin r' → Hypergraph α β) (μ' : BoundaryUnit S' → Hypergraph α β)
      (L' : Hypergraph α β), r' < r → GM06.IsClosedDiscSpace S' → G'.IsGraph →
      PresentationHasDepthLe G' Γ' Γ_sub' ιV' ιE' r' F' H' μ' d →
      IsExhaustiveLinkage G' Γ_sub' r' H' L' → IsPLinkage G' L' (p + 2 * d) →
      (sigmaJumps Γ' Γ_sub' ιV').encard ≤ lam) :
    (sigmaJumps Γ Γ_sub ιV).encard ≤ lam + lam := by
  classical
  have hS := hP.is_surface
  have hC := DiscCut.bd_mem_cuffs hD
  have hpi := Real.pi_pos
  have hlt := hW.lt_add
  have hne : cp θx ≠ cp θy := fun h =>
    hxy.ne (DiscCut.angle_injOn f hlt ⟨hx, hxy.le.trans hy⟩ ⟨hx.trans hxy.le, hy⟩ h)
  -- The line through `r₀`.
  obtain ⟨F, hF, hFsub⟩ :=
    DiscLine.exists_line_in_region hD hP.is_proper_drawing hr₀ hxV hyV hne hxr hyr
  obtain ⟨hFbd', hFU⟩ := DiscLine.inter_eq_of_subset_region hr₀ hFsub
  have hFbd : F ∩ bd S = {cp θx, cp θy} := by
    refine Subset.antisymm hFbd' ?_
    obtain ⟨g, hg0, hg1⟩ := hF
    rintro z (rfl | rfl)
    · exact ⟨hg0 ▸ (g 0).2, GM17.cuffPoint_mem f θx⟩
    · exact ⟨hg1 ▸ (g 1).2, GM17.cuffPoint_mem f θy⟩
  -- The two discs.
  obtain ⟨Δ₁, Δ₂, h, hD₁, hD₂, hbd₁, hbd₂⟩ :=
    exists_disc_sides hD f hxy (by linarith) hF hFbd hxV hyV hFU
  have hinter : ∀ j D, F_star j ∩ D = F_star j ∩ (D ∩ bd S) := fun j D => by
    rw [← inter_assoc, inter_right_comm, inter_eq_left.mpr
      (subset_bd_of_isSupportOfDrawing (hP.supports_isSupport j))]
  have hleft : ∀ j, F_star j ∩ Δ₁ = cp '' Icc (max (a j) θx) (min (b j) θy) := fun j => by
    rw [hinter, hbd₁, window_inter_left hW j hx hy]
  -- The supports of the two discs.
  obtain ⟨σ₁, hσ₁, hP₁, hall₁⟩ := exists_enum (fun j => (F_star j ∩ Δ₁).Nonempty)
  obtain ⟨σ₂, hσ₂, hP₂, hall₂⟩ := exists_enum (fun j => (F_star j ∩ Δ₂).Nonempty)
  have hsup₁ : ∀ i, IsSupportOfDrawing Γ (F_star (σ₁ i) ∩ Δ₁) := by
    intro i
    have hne₁ := hP₁ i
    rw [hleft] at hne₁ ⊢
    refine isSupport_of_Icc hS hC hW (le_max_of_le_left (hW.le_a _))
      (min_le_of_left_le (hW.b_le _)) ?_ ?_ hne₁
    · rcases max_choice (a (σ₁ i)) θx with h' | h' <;> rw [h']
      exacts [hW.a_mem _, hxV]
    · rcases min_choice (b (σ₁ i)) θy with h' | h' <;> rw [h']
      exacts [hW.b_mem _, hyV]
  have hsup₂ : ∀ i, IsSupportOfDrawing Γ (F_star (σ₂ i) ∩ Δ₂) := by
    intro i
    have hne₂ := hP₂ i
    obtain ⟨s, e, hs, he, heq⟩ := window_inter_right hW (σ₂ i) hx hxy hy (hsep _)
    rw [hinter, hbd₂, heq] at hne₂ ⊢
    refine isSupport_of_Icc hS hC hW ?_ ?_ ?_ ?_ hne₂
    · rcases hs with rfl | rfl
      exacts [hW.le_a _, hx.trans hxy.le]
    · rcases he with rfl | rfl
      exacts [hW.b_le _, hxy.le.trans hy]
    · rcases hs with rfl | rfl
      exacts [hW.a_mem _, hyV]
    · rcases he with rfl | rfl
      exacts [hW.b_mem _, hxV]
  -- Each disc misses a support, so it has fewer than `r` supports.
  have hlt₁ : (Finset.univ.filter fun j => (F_star j ∩ Δ₁).Nonempty).card < r := by
    refine card_filter_lt _ ?_
    obtain ⟨j, hj⟩ := h₁
    refine ⟨j, ?_⟩
    rw [hleft, not_nonempty_iff_eq_empty, Icc_eq_empty, image_empty]
    rw [not_le]
    rcases hj with hj | hj
    · exact (min_le_left _ _).trans_lt (hj.trans_le (le_max_right _ _))
    · exact (min_le_right _ _).trans_lt (hj.trans_le (le_max_left _ _))
  have hlt₂ : (Finset.univ.filter fun j => (F_star j ∩ Δ₂).Nonempty).card < r := by
    refine card_filter_lt _ ?_
    obtain ⟨j, hja, hjb⟩ := h₂
    refine ⟨j, ?_⟩
    rw [hinter, hbd₂, hW.F_eq j]
    rintro ⟨_, ⟨t, ht, rfl⟩, hz⟩
    rcases (mem_image_right_iff hlt hx hxy hy (hW.Icc_subset j ht)).mp hz with h' | h'
    · exact absurd (hja.trans_le (ht.1.trans h')) (lt_irrefl _)
    · exact absurd ((h'.trans ht.2).trans_lt hjb) (lt_irrefl _)
  exact encard_sigmaJumps_le_of_sides hP h hG hq hL hLp
    (connectedSpace_of_isClosedDiscSpace hD₁) (connectedSpace_of_isClosedDiscSpace hD₂)
    hσ₁ hsup₁ hall₁ hσ₂ hsup₂ hall₂
    (fun G' Γ' Γs ιV' ιE' F' H' μ' L' => hb G' Γ' Γs ιV' ιE' F' H' μ' L' hlt₁ hD₁)
    (fun G' Γ' Γs ιV' ιE' F' H' μ' L' => hb G' Γ' Γs ιV' ιE' F' H' μ' L' hlt₂ hD₂)

end step

end Side
end GM21
end GraphMinor
