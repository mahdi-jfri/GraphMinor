module

public import GraphMinor.GM21.Section6Induction
public import GraphMinor.GM21.Section4
public import GraphMinor.GM21.Section6Cut
public import GraphMinor.GM21.Section6DiscStep
import GraphMinor.Surface.ChartCells
import GraphMinor.GM21.CuffSpaces
import GraphMinor.Surface.ArcTools
import GraphMinor.GM19.CapExists

/-!
# Graph Minors XXI, (6.3), claim (4): the sides of a separating line are smaller

Claim (4) of the proof of (6.3) (page 29 of the preprint) cuts `Σ` along a separating proper
line `F` into surfaces `Σ₁, Σ₂` and says: "If both $\Sigma_1$ and $\Sigma_2$ are not discs, then by
(4.2)(i) and (4.2)(ii), either $\hat{\Sigma}_i$ is simpler than $\hat{\Sigma}$, or
$\hat{\Sigma}_i$ is homeomorphic to $\hat{\Sigma}$ and $c(\Sigma_i) < c(\Sigma)$ for $i = 1, 2$."

This file proves the topological part of that sentence, in the form the claim uses
(`sides_typeLt_or_disc`): either there is a closed disc `Δ ⊆ Σ` with
`F ⊆ bd(Δ) ⊆ F ∪ bd(Σ)`, which is the conclusion of claim (4), or both sides come before `Σ` in the
order of the induction (`Induction.TypeLt`). We apply (4.2) twice, once with the roles of `Σ₁` and
`Σ₂` exchanged. The case "one of $\Sigma_1, \Sigma_2$ is a disc" of the paper is covered by the
first alternative: (4.2)(ii) gives the disc `Δ` exactly when it does not give `c(Σ_i) < c(Σ)`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace ClaimFour

open Set Topology GraphMinor.Surface GraphMinor.GM21.Induction GraphMinor.GM21.Side

/-- One side of (4.2): either the disc of claim (4) exists, or `Σ₂` comes before `Σ`. -/
theorem side_typeLt_or_disc {S : Type} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    {S₁ S₂ F : Set S} (hS₁ : IsSurface S₁) [ConnectedSpace S₁] (hS₂ : IsSurface S₂)
    [ConnectedSpace S₂] (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F) {s t : S}
    (hF : IsProperLineInSurface F s t) {C : Set S} (hC : C ∈ cuffs S) (hs : s ∈ C) (ht : t ∈ C)
    {n c n₂ c₂ : ℕ} (hT : HasType S n c) (hT₂ : HasType S₂ n₂ c₂) :
    (∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S) ∨ TypeLt n₂ c₂ n c := by
  obtain ⟨Shat, _, ⟨cap⟩⟩ := GM19.exists_cappedSurface _ S hS inferInstance rfl
  obtain ⟨Shat₁, _, ⟨cap₁⟩⟩ := GM19.exists_cappedSurface _ S₁ hS₁ inferInstance rfl
  obtain ⟨Shat₂, _, ⟨cap₂⟩⟩ := GM19.exists_cappedSurface _ S₂ hS₂ inferInstance rfl
  have h42 := theorem_4_2_proof hS hS₁ hS₂ hun hint cap cap₁ cap₂
  have hTc := hT.cap cap
  have hT₂c := hT₂.cap cap₂
  rcases h42.1 s t C hC hs ht hF with hsimp | hsph
  · exact Or.inr (Or.inl (hT₂c.lt_of_isSimplerThan hTc hsimp))
  · obtain ⟨⟨e⟩, hc | ⟨-, hΔ⟩⟩ := h42.2.1 s t C hC hs ht hF hsph
    · refine Or.inr (Or.inr ⟨(hT₂c.eq_of_homeomorph hTc e).1, ?_⟩)
      rw [← hT₂.ncard_cuffs, ← hT.ncard_cuffs]
      exact hc
    · exact Or.inl hΔ

/-- **Graph Minors XXI, proof of (6.3), claim (4), the use of (4.2)** (page 29 of the preprint): "If
both $\Sigma_1$ and $\Sigma_2$ are not discs, then by (4.2)(i) and (4.2)(ii), either
$\hat{\Sigma}_i$ is simpler than $\hat{\Sigma}$, or $\hat{\Sigma}_i$ is homeomorphic to
$\hat{\Sigma}$ and $c(\Sigma_i) < c(\Sigma)$ for $i = 1, 2$."

Here `F` is a proper line with both ends in one cuff `C`, and `Σ₁, Σ₂` are the two sides. Either
there is a closed disc `Δ ⊆ Σ` with `F ⊆ bd(Δ) ⊆ F ∪ bd(Σ)`, or both sides come before `Σ` in the
order of the induction. -/
theorem sides_typeLt_or_disc {S : Type} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    {S₁ S₂ F : Set S} (hS₁ : IsSurface S₁) [ConnectedSpace S₁] (hS₂ : IsSurface S₂)
    [ConnectedSpace S₂] (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F) {s t : S}
    (hF : IsProperLineInSurface F s t) {C : Set S} (hC : C ∈ cuffs S) (hs : s ∈ C) (ht : t ∈ C)
    {n c n₁ c₁ n₂ c₂ : ℕ} (hT : HasType S n c) (hT₁ : HasType S₁ n₁ c₁)
    (hT₂ : HasType S₂ n₂ c₂) :
    (∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S) ∨
      (TypeLt n₁ c₁ n c ∧ TypeLt n₂ c₂ n c) := by
  rcases side_typeLt_or_disc hS hS₁ hS₂ hun hint hF hC hs ht hT hT₂ with hΔ | h₂
  · exact Or.inl hΔ
  rcases side_typeLt_or_disc hS hS₂ hS₁ (by rw [union_comm, hun]) (by rw [inter_comm, hint]) hF
    hC hs ht hT hT₁ with hΔ | h₁
  · exact Or.inl hΔ
  · exact Or.inr ⟨h₁, h₂⟩

/-! ## The supports of a side -/

section supports

variable {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {S₁ S₂ F : Set S} {a b : S}

private theorem isPreconnected_diff_left' {L : Set S} {u v : S}
    (h : IsLineWithEnds L u v) : IsPreconnected (L \ {u}) :=
  h.isPreconnected_diff.subset_closure (fun _ hx => ⟨hx.1, fun h' => hx.2 (.inl h')⟩)
    fun _ hx => h.subset_closure_diff hx.1

omit [TopologicalSpace S] [T2Space S] in
/-- Half of a support at an end `x`: if `K \ {x}` lies in `S₁` or misses it, then `K ∩ S₁` is `K`
or `{x}`. -/
private theorem inter_eq_of_diff {x : S} (hx₁ : x ∈ S₁) {K : Set S} (hxK : x ∈ K)
    (h : K \ {x} ⊆ S₁ ∨ Disjoint (K \ {x}) S₁) : K ∩ S₁ = K ∨ K ∩ S₁ = {x} := by
  rcases h with h | h
  · left
    refine inter_eq_left.mpr fun y hy => ?_
    by_cases hyx : y = x
    · exact hyx ▸ hx₁
    · exact h ⟨hy, hyx⟩
  · right
    ext y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · by_contra hyx
      exact disjoint_left.mp h ⟨hy.1, hyx⟩ hy.2
    · rw [mem_singleton_iff.mp hy]
      exact ⟨hxK, hx₁⟩

/-- **Supports of a side.** Let `F` be a line with sides `S₁, S₂`, and let `K` be a support of `Γ`
that meets `F` in at most one point `x ∈ F ∩ V(Γ) ∩ bd(S)`. If `K ∩ S₁` is not empty, it is a
support. The proof splits `K` at `x`: each part of `K \ {x}` is connected and misses `F`, so it
lies on one side. -/
theorem isSupport_inter_side_of_inter_subset (h : IsSideOfLine Γ S₁ S₂ F a b) {K : Set S}
    (hK : IsSupportOfDrawing Γ K) {x : S} (hxF : x ∈ F) (hxV : x ∈ Γ.V ∩ bd S)
    (hKF : K ∩ F ⊆ {x}) (hne : (K ∩ S₁).Nonempty) : IsSupportOfDrawing Γ (K ∩ S₁) := by
  have hc₁ := h.isClosed_left
  have hc₂ := h.isClosed_right
  have hx₁ : x ∈ S₁ := h.line_subset_left hxF
  have hside : ∀ X : Set S, IsPreconnected X → X ⊆ K \ {x} → X ⊆ S₁ ∨ Disjoint X S₁ :=
    fun X hX hXK => Side.subset_or_disjoint_side hc₁ hc₂ h.union_eq h.inter_eq hX
      (disjoint_left.mpr fun y hyX hyF => (hXK hyX).2 (hKF ⟨(hXK hyX).1, hyF⟩))
  have hpt : IsSupportOfDrawing Γ {x} := ⟨x, x, Or.inl ⟨x, hxV, rfl, rfl, rfl⟩⟩
  by_cases hxK : x ∉ K
  · have hdiff : K \ {x} = K := sdiff_singleton_eq_self hxK
    rcases hside K (isConnected_of_isSupportOfDrawing hK).isPreconnected hdiff.ge with h' | h'
    · rwa [inter_eq_left.mpr h']
    · exact absurd hne (not_nonempty_iff_eq_empty.mpr (disjoint_iff_inter_eq_empty.mp h'))
  rw [not_not] at hxK
  obtain ⟨u, w, hKuw⟩ := hK
  have hends := ends_mem_of_supportHasEnds hKuw
  rcases hKuw with ⟨v, -, rfl, -, -⟩ | ⟨hKbd, huw, hu, hw, hline⟩
  · rw [← mem_singleton_iff.mp hxK, inter_eq_left.mpr (singleton_subset_iff.mpr hx₁)]
    exact hpt
  · have hlineSup : ∀ {L : Set S} {y z : S}, L ⊆ K → y ≠ z → y ∈ Γ.V ∩ bd S →
        z ∈ Γ.V ∩ bd S → IsLineWithEnds L y z → IsSupportOfDrawing Γ L :=
      fun hLK hyz hy hz hL => ⟨_, _, Or.inr ⟨hLK.trans hKbd, hyz, hy, hz, hL⟩⟩
    by_cases hxu : x = u
    · subst hxu
      rcases inter_eq_of_diff hx₁ hxK (hside _ (isPreconnected_diff_left' hline) subset_rfl)
        with h' | h' <;> rw [h']
      · exact ⟨_, _, Or.inr ⟨hKbd, huw, hu, hw, hline⟩⟩
      · exact hpt
    by_cases hxw : x = w
    · subst hxw
      rcases inter_eq_of_diff hx₁ hxK (hside _ (isPreconnected_diff_left' hline.symm) subset_rfl)
        with h' | h' <;> rw [h']
      · exact ⟨_, _, Or.inr ⟨hKbd, huw, hu, hw, hline⟩⟩
      · exact hpt
    obtain ⟨L₁, L₂, hL₁, hL₂, hun, hint⟩ := hline.split hxK hxu hxw
    have hL₁K : L₁ ⊆ K := hun ▸ subset_union_left
    have hL₂K : L₂ ⊆ K := hun ▸ subset_union_right
    have hsplit : K ∩ S₁ = L₁ ∩ S₁ ∪ L₂ ∩ S₁ := by rw [← union_inter_distrib_right, hun]
    have h₁ := inter_eq_of_diff hx₁ hL₁.right_mem (hside _
      (isPreconnected_diff_left' hL₁.symm) (sdiff_subset_sdiff_left hL₁K))
    have h₂ := inter_eq_of_diff hx₁ hL₂.left_mem (hside _
      (isPreconnected_diff_left' hL₂) (sdiff_subset_sdiff_left hL₂K))
    have hS₁ : IsSupportOfDrawing Γ L₁ := hlineSup hL₁K (Ne.symm hxu) hu hxV hL₁
    have hS₂ : IsSupportOfDrawing Γ L₂ := hlineSup hL₂K hxw hxV hw hL₂
    rw [hsplit]
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> rw [h₁, h₂]
    · rw [hun]; exact ⟨_, _, Or.inr ⟨hKbd, huw, hu, hw, hline⟩⟩
    · rwa [union_eq_left.mpr (singleton_subset_iff.mpr hL₁.right_mem)]
    · rwa [union_eq_right.mpr (singleton_subset_iff.mpr hL₂.left_mem)]
    · rw [union_self]; exact hpt

/-- **Supports of a side**, the case used in claim (4) of (6.3). A support `K` of `Γ` that does not
contain both ends of `F` meets the side `S₁` in a support or not at all. -/
theorem isSupport_inter_side (h : IsSideOfLine Γ S₁ S₂ F a b) {K : Set S}
    (hK : IsSupportOfDrawing Γ K) (hab : ¬ (a ∈ K ∧ b ∈ K)) (hne : (K ∩ S₁).Nonempty) :
    IsSupportOfDrawing Γ (K ∩ S₁) := by
  have hKbd := subset_bd_of_isSupportOfDrawing hK
  have hFbd : F ∩ bd S = {a, b} := h.inter_bd
  have hKF : ∀ y ∈ K ∩ F, y = a ∨ y = b := fun y hy => by
    have : y ∈ F ∩ bd S := ⟨hy.2, hKbd hy.1⟩
    rw [hFbd] at this
    exact this
  have haF : a ∈ F := h.proper.1.left_mem
  have hbF : b ∈ F := h.proper.1.right_mem
  have hab' := h.ends_mem_bd
  by_cases ha : a ∈ K
  · have hb : b ∉ K := fun hb => hab ⟨ha, hb⟩
    refine isSupport_inter_side_of_inter_subset h hK haF ⟨h.left_mem, hab'.1⟩ (fun y hy => ?_) hne
    rcases hKF y hy with rfl | rfl
    · rfl
    · exact absurd hy.1 hb
  · refine isSupport_inter_side_of_inter_subset h hK hbF ⟨h.right_mem, hab'.2⟩ (fun y hy => ?_) hne
    rcases hKF y hy with rfl | rfl
    · exact absurd hy.1 ha
    · rfl

end supports

/-! ## Claim (4) when no support holds both ends of the line -/

section claim

universe u v

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S] [ConnectedSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}
  {r' : ℕ} {F_star : Fin r' → Set S} {H : Fin r' → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {L : Hypergraph α β}

/-- **Graph Minors XXI, proof of (6.3), claim (4)** (page 29 of the preprint), when no support
contains both ends of `F`: "Now for $i = 1, 2$, there is a presentation of $G_i$ in $\Sigma_i$ of
depth $\le q$ ... using $\Gamma_i$; and $L \cap G_i$ is an exhaustive vital $(p + 2q)$-linkage. If
both $\Sigma_1$ and $\Sigma_2$ are not discs, then by (4.2)(i) and (4.2)(ii), either
$\hat{\Sigma}_i$ is simpler than $\hat{\Sigma}$, or $\hat{\Sigma}_i$ is homeomorphic to
$\hat{\Sigma}$ and $c(\Sigma_i) < c(\Sigma)$ for $i = 1, 2$. But then from (1), there are
$\le \lambda(p + 2q, q, r + 1)$ $\Sigma_i$-jumps in $\Gamma_i$ for $i = 1, 2$, and hence
$\le 2\lambda(p + 2q, q, r + 1) \le \lambda$ $\Sigma$-jumps in $\Gamma$, as required."

Here `hlam` is the inductive hypothesis (1). Either there is a closed disc `Δ ⊆ Σ` with
`F ⊆ bd(Δ) ⊆ F ∪ bd(Σ)`, or there are at most `2λ` jumps. When no support contains both ends of
`F`, every support meets each side in a support or not at all (`isSupport_inter_side`), so each side
has defect at most `r`. -/
theorem claim_4_of_not_mem_both (hS : IsSurface S) {n c : ℕ} (hT : HasType S n c)
    {p q r lam : ℕ} (hlam : BoundBelow.{u, v} n c (p + 2 * q) q r lam) (hG : G.IsGraph)
    (hr : r' ≤ r) (hd : PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r' H L) (hLp : IsPLinkage G L p)
    {S₁ S₂ F : Set S} {a b : S} (h : IsSideOfLine Γ S₁ S₂ F a b) [ConnectedSpace S₁]
    [ConnectedSpace S₂] {C : Set S} (hC : C ∈ cuffs S) (haC : a ∈ C) (hbC : b ∈ C)
    (hab : ∀ j, ¬ (a ∈ F_star j ∧ b ∈ F_star j)) :
    (∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S) ∨
      (sigmaJumps Γ Γ_sub ιV).encard ≤ lam + lam := by
  classical
  have : T2Space S := hS.2.1
  obtain ⟨n₁, c₁, hT₁⟩ := exists_hasType h.surface_left
  obtain ⟨n₂, c₂, hT₂⟩ := exists_hasType h.surface_right
  rcases sides_typeLt_or_disc hS h.surface_left h.surface_right h.union_eq h.inter_eq h.proper
    hC haC hbC hT hT₁ hT₂ with hΔ | ⟨hlt₁, hlt₂⟩
  · exact Or.inl hΔ
  right
  obtain ⟨qf, hP, hqf, -⟩ := hd
  obtain ⟨σ₁, hσ₁, hP₁, hall₁⟩ := exists_enum (fun j => (F_star j ∩ S₁).Nonempty)
  obtain ⟨σ₂, hσ₂, hP₂, hall₂⟩ := exists_enum (fun j => (F_star j ∩ S₂).Nonempty)
  have hcard : ∀ P : Fin r' → Prop, [DecidablePred P] → (Finset.univ.filter P).card ≤ r :=
    fun P _ => (Finset.card_filter_le _ _).trans (by simpa using hr)
  exact encard_sigmaJumps_le_of_sides hP h hG hqf hL hLp inferInstance inferInstance
    hσ₁ (fun i => isSupport_inter_side h (hP.supports_isSupport _) (hab _) (hP₁ i)) hall₁
    hσ₂ (fun i => isSupport_inter_side h.symm (hP.supports_isSupport _)
      (hab _) (hP₂ i)) hall₂
    (fun G' Γ' Γ_sub' ιV' ιE' F' H' μ' L' hG' hd' hL' hLp' =>
      hlam _ h.surface_left n₁ c₁ hT₁ hlt₁ G' Γ' Γ_sub' ιV' ιE' _ F' H' μ' L' hG' (hcard _) hd'
        hL' hLp')
    (fun G' Γ' Γ_sub' ιV' ιE' F' H' μ' L' hG' hd' hL' hLp' =>
      hlam _ h.surface_right n₂ c₂ hT₂ hlt₂ G' Γ' Γ_sub' ιV' ιE' _ F' H' μ' L' hG' (hcard _) hd'
        hL' hLp')

end claim

end ClaimFour
end GM21
end GraphMinor
