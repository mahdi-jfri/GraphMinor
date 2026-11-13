module

public import GraphMinor.GM21.Section6Four
public import GraphMinor.GM21.Section6CutsBlocks
public import GraphMinor.GM21.Section7Three
public import GraphMinor.GM21.Section6RestrictPres
import GraphMinor.GM21.Section6SideSupports
import GraphMinor.GM21.Section6DiscStep
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, proof of (6.5): the defect-1 presentation on an interval of a support

In the proof of (6.5) (page 26 of the preprint), the boundary of the region $R_i$ meets the
two supports $F_1^*, F_2^*$ in sub-supports $I_1, I_2$, and the paper writes:
"For $j = 1, 2$, let $\Gamma_j$ be the drawing in $\Sigma$ formed by all the vertices in
$V(\Gamma) \cap I_j$ and all the $\Sigma$-jumps $J$ with $U(J) \subseteq R_i \cup I_1 \cup I_2$
with both ends in $I_j$. We claim that $\Gamma_j$ includes at most $\lambda'$ $\Sigma$-jumps. For
if $|I_j| = 1$ this is trivial, since $\Gamma_j$ includes no $\Sigma$-jumps. If $|I_j| \ne 1$ then
$\Gamma_j, I_j, \mu(I_j)$, and the restriction of $\mu$ to $I_j$, is a presentation of
$\Gamma_j \cup \mu(I_j)$ in a disc with depth $\le q$ and defect 1; and
$L \cap (\Gamma_j \cup \mu(I_j))$ is an exhaustive vital $(p+2q)$-linkage, and so by (6.4) it has
at most $\lambda'$ $\Sigma$-jumps."

This file formalizes that step (`DiscCut.ncard_insideSet_le_of_theorem_6_4`), together with the
two-block jump count (`Cuts.ncard_le_of_two_blocks`) giving the paper's bound
$\lambda = n(2\lambda' + 1)$.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

namespace Cuts

open Set

universe u

variable {ι : Type u} {lo hi : ι → ℝ} {T : Set ι}

/-- **The two-block jump count of (6.5)** (Graph Minors XXI, page 26 of the preprint).
Let there be two blocks `[a₁, b₁]` and `[a₂, b₂]` with `a₁ ≤ b₁ < a₂ ≤ b₂`, holding all ends of the
jumps in `T`. If there are at most `n - 1` cross jumps between `[a₁, b₁]` and `[a₂, b₂]` (for
`1 ≤ n`), and each interval between consecutive cut points of either block holds at most `lam`
jumps, then `T.ncard ≤ n * (2 * lam + 1)`. -/
theorem ncard_le_of_two_blocks (hlt : ∀ J ∈ T, lo J < hi J)
    (hlam : ∀ J ∈ T, ∀ J' ∈ T, ¬ (lo J < lo J' ∧ lo J' < hi J ∧ hi J < hi J'))
    (hT : T.Finite) {a₁ b₁ a₂ b₂ : ℝ} (hab₁ : a₁ ≤ b₁) (hb₁a₂ : b₁ < a₂) (hab₂ : a₂ ≤ b₂)
    (hlo : ∀ J ∈ T, lo J ∈ Icc a₁ b₁ ∨ lo J ∈ Icc a₂ b₂)
    (hhi : ∀ J ∈ T, hi J ∈ Icc a₁ b₁ ∨ hi J ∈ Icc a₂ b₂)
    {n lam : ℕ} (hn1 : 1 ≤ n)
    (hcross : (blockCross lo hi T a₁ b₁ a₂ b₂).ncard ≤ n - 1)
    (hint₁ : ∀ g h : ℝ, g < h → a₁ ≤ g → h ≤ b₁ → g ∈ cutPoints lo hi T a₁ b₁ →
      (h ∈ cutPoints lo hi T a₁ b₁ ∨ h = b₁) →
      NoCross lo hi T g h → (insideSet lo hi T ⟨g, h, true⟩).ncard ≤ lam)
    (hint₂ : ∀ g h : ℝ, g < h → a₂ ≤ g → h ≤ b₂ → g ∈ cutPoints lo hi T a₂ b₂ →
      (h ∈ cutPoints lo hi T a₂ b₂ ∨ h = b₂) →
      NoCross lo hi T g h → (insideSet lo hi T ⟨g, h, true⟩).ncard ≤ lam) :
    T.ncard ≤ n * (2 * lam + 1) := by
  have hfin : ∀ X ⊆ T, X.Finite := fun X hX => hT.subset hX
  have hbwd₁ : outBwd lo hi T a₁ b₁ = ∅ := by
    refine eq_empty_of_forall_notMem ?_
    rintro P ⟨hP, h1, h2, h3⟩
    rcases hlo P hP with h | h <;> linarith [h.1, h.2]
  have hfwd₁_sub : outFwd lo hi T a₁ b₁ ⊆ blockCross lo hi T a₁ b₁ a₂ b₂ := by
    rintro P ⟨hP, h1, h2, h3⟩
    rcases hhi P hP with h | h
    · linarith [h.2]
    · exact ⟨hP, ⟨h1, h2⟩, h⟩
  have hM₁ : (outFwd lo hi T a₁ b₁).ncard + (outBwd lo hi T a₁ b₁).ncard ≤ n - 1 := by
    rw [hbwd₁, ncard_empty, add_zero]
    exact (ncard_le_ncard hfwd₁_sub (hfin _ fun J hJ => hJ.1)).trans hcross
  have hfwd₂ : outFwd lo hi T a₂ b₂ = ∅ := by
    refine eq_empty_of_forall_notMem ?_
    rintro P ⟨hP, h1, h2, h3⟩
    rcases hhi P hP with h | h <;> linarith [h.1, h.2]
  have hbwd₂_sub : outBwd lo hi T a₂ b₂ ⊆ blockCross lo hi T a₁ b₁ a₂ b₂ := by
    rintro P ⟨hP, h1, h2, h3⟩
    rcases hlo P hP with h | h
    · exact ⟨hP, h, ⟨h2, h3⟩⟩
    · linarith [h.1]
  have hM₂ : (outFwd lo hi T a₂ b₂).ncard + (outBwd lo hi T a₂ b₂).ncard ≤ n - 1 := by
    rw [hfwd₂, ncard_empty, zero_add]
    exact (ncard_le_ncard hbwd₂_sub (hfin _ fun J hJ => hJ.1)).trans hcross
  have hB₁ := ncard_block_le hlt hlam hT hab₁ hM₁ hint₁
  have hB₂ := ncard_block_le hlt hlam hT hab₂ hM₂ hint₂
  have hsub : T ⊆ ({J ∈ T | lo J ∈ Icc a₁ b₁ ∧ hi J ∈ Icc a₁ b₁} ∪
      {J ∈ T | lo J ∈ Icc a₂ b₂ ∧ hi J ∈ Icc a₂ b₂}) ∪ blockCross lo hi T a₁ b₁ a₂ b₂ := by
    intro J hJ
    rcases hlo J hJ with hloJ | hloJ <;> rcases hhi J hJ with hhiJ | hhiJ
    · exact Or.inl (Or.inl ⟨hJ, hloJ, hhiJ⟩)
    · exact Or.inr ⟨hJ, hloJ, hhiJ⟩
    · linarith [hlt J hJ, hloJ.1, hhiJ.2]
    · exact Or.inl (Or.inr ⟨hJ, hloJ, hhiJ⟩)
  have hF₁ : {J ∈ T | lo J ∈ Icc a₁ b₁ ∧ hi J ∈ Icc a₁ b₁}.Finite := hfin _ fun J hJ => hJ.1
  have hF₂ : {J ∈ T | lo J ∈ Icc a₂ b₂ ∧ hi J ∈ Icc a₂ b₂}.Finite := hfin _ fun J hJ => hJ.1
  have hFC : (blockCross lo hi T a₁ b₁ a₂ b₂).Finite := hfin _ fun J hJ => hJ.1
  have h_add : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  rw [h_add] at hB₁ hB₂
  calc T.ncard
      ≤ (({J ∈ T | lo J ∈ Icc a₁ b₁ ∧ hi J ∈ Icc a₁ b₁} ∪
          {J ∈ T | lo J ∈ Icc a₂ b₂ ∧ hi J ∈ Icc a₂ b₂}) ∪
          blockCross lo hi T a₁ b₁ a₂ b₂).ncard :=
        ncard_le_ncard hsub ((hF₁.union hF₂).union hFC)
    _ ≤ ({J ∈ T | lo J ∈ Icc a₁ b₁ ∧ hi J ∈ Icc a₁ b₁} ∪
          {J ∈ T | lo J ∈ Icc a₂ b₂ ∧ hi J ∈ Icc a₂ b₂}).ncard +
          (blockCross lo hi T a₁ b₁ a₂ b₂).ncard :=
        ncard_union_le _ _
    _ ≤ {J ∈ T | lo J ∈ Icc a₁ b₁ ∧ hi J ∈ Icc a₁ b₁}.ncard +
          {J ∈ T | lo J ∈ Icc a₂ b₂ ∧ hi J ∈ Icc a₂ b₂}.ncard +
          (blockCross lo hi T a₁ b₁ a₂ b₂).ncard :=
        Nat.add_le_add_right (ncard_union_le _ _) _
    _ ≤ n * lam + n * lam + (n - 1) :=
        Nat.add_le_add (Nat.add_le_add hB₁ hB₂) hcross
    _ ≤ n * (2 * lam + 1) := by
        have : n * (2 * lam + 1) = n * lam + n * lam + n := by ring
        omega

end Cuts

namespace DiscCut

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM21.Supports
open GraphMinor.GM21.Cuts

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- In a space where `bd S` is a cuff, every cuff is `bd S`. -/
theorem eq_bd_of_mem_cuffs (hC : bd S ∈ cuffs S) {C : Set S} (hC' : C ∈ cuffs S) : C = bd S := by
  by_contra hne
  obtain ⟨x, hx, rfl⟩ := hC'
  exact Set.disjoint_left.mp (cuffs_disjoint ⟨x, hx, rfl⟩ hC hne) (mem_connectedComponentIn hx) hx

section defect_one

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
  (hC : bd S ∈ cuffs S) {f : Circle ≃ₜ bd S} {w₀ w₁ : ℝ} {a b : Fin r → ℝ}
  (hW : Window Γ F_star f w₀ w₁ a b)
  (hK : IsLinkage G Γ_sub)
  (hdeg : ∀ y ∈ Γ_sub.vertexSet, y ∉ ιV '' (Γ.V ∩ bd S) → (incidentEdges Γ_sub y).ncard = 2)

set_option hygiene false in
local notation "𝒯" => jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))
set_option hygiene false in
local notation "LO" => jumpLo f w₀ w₁ Γ.V ιV
set_option hygiene false in
local notation "HI" => jumpHi f w₀ w₁ Γ.V ιV
set_option hygiene false in
local notation "POS" => {t : ℝ | t ∈ Icc w₀ w₁ ∧ GM19.cuffPoint f t ∈ Γ.V}
set_option hygiene false in
local notation "cp" => GM19.cuffPoint f

include h_pres hW in
/-- The blocks of positions of two different supports are disjoint and so one comes before the
other. -/
theorem Window.lt_or_lt {j j' : Fin r} (hjj : j ≠ j') : b j < a j' ∨ b j' < a j := by
  by_contra h
  push Not at h
  have hm : max (a j) (a j') ∈ Icc (a j) (b j) ∩ Icc (a j') (b j') :=
    ⟨⟨le_max_left _ _, max_le (hW.a_le_b j) h.1⟩, ⟨le_max_right _ _, max_le h.2 (hW.a_le_b j')⟩⟩
  have h₁ : cp (max (a j) (a j')) ∈ F_star j := by
    rw [hW.F_eq j]
    exact ⟨_, hm.1, rfl⟩
  have h₂ : cp (max (a j) (a j')) ∈ F_star j' := by
    rw [hW.F_eq j']
    exact ⟨_, hm.2, rfl⟩
  exact Set.disjoint_left.mp (h_pres.supports_disjoint hjj) h₁ h₂

include h_pres hW in
/-- If `[x, y] ⊆ [a j₀, b j₀]`, then for `j ≠ j₀` the piece `piece f a b j x y` is empty. -/
theorem piece_eq_empty_of_ne {j₀ j : Fin r} (hjj : j ≠ j₀) {x y : ℝ}
    (hx : a j₀ ≤ x) (hy : y ≤ b j₀) :
    piece f a b j x y = ∅ := by
  rw [piece, Icc_eq_empty, image_empty]
  rw [not_le]
  rcases hW.lt_or_lt h_pres hjj with hlt | hlt
  · exact (min_le_left _ _).trans_lt (hlt.trans_le (hx.trans (le_max_right _ _)))
  · exact (min_le_right _ _).trans_lt ((hy.trans_lt hlt).trans_le (le_max_left _ _))

include h_pres hC hW hK hdeg in
/-- **Applying (6.4) to an interval of one support in the proof of (6.5)** (Graph Minors XXI,
page 26 of the preprint). Let `c₀` be an admissible cut with `[c₀.x, c₀.y] ⊆ [a j₀, b j₀]`,
and let `I = cp '' Icc c₀.x c₀.y`. Then `G' = cutB ... c₀ = Γ_{j₀} ∪ μ(I)` has a presentation in
the disc `S` with depth `≤ d` and defect 1, and `L ∩ G'` is an exhaustive vital
`(p + 2d)`-linkage in `G'`. Hence if `lam'` satisfies the conclusion of `(6.4)` for `(p + 2d, d)`,
there are at most `lam'` jumps in `insideSet LO HI 𝒯 c₀`. -/
theorem ncard_insideSet_le_of_theorem_6_4 (hD : GM06.IsClosedDiscSpace S) (hG : G.IsGraph)
    {L : Hypergraph α β} {p d lam' : ℕ}
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (hpL : IsPLinkage G L p) (hq : ∀ j, q j ≤ d)
    (hlam' : ∀ {S' : Type w} [TopologicalSpace S'] (G' : Hypergraph α β)
      (Γ' : Drawing S') (Γ_sub' : Hypergraph α β) (ιV' : S' → α)
      (ιE' : Set S' → β) (F_star' : Fin 1 → Set S') (H' : Fin 1 → Hypergraph α β)
      (μ' : BoundaryUnit S' → Hypergraph α β) (L' : Hypergraph α β),
      GM06.IsClosedDiscSpace S' → G'.IsGraph →
      PresentationHasDepthLe G' Γ' Γ_sub' ιV' ιE' 1 F_star' H' μ' d →
      IsExhaustiveLinkage G' Γ_sub' 1 H' L' → IsPLinkage G' L' (p + 2 * d) →
      (sigmaJumps Γ' Γ_sub' ιV').encard ≤ lam')
    {c₀ : Cut} (hc₀ : Admissible LO HI 𝒯 POS c₀) (j₀ : Fin r)
    (hcj : a j₀ ≤ c₀.x ∧ c₀.y ≤ b j₀) :
    (insideSet LO HI 𝒯 c₀).ncard ≤ lam' := by
  have hS := h_pres.is_surface
  have : T2Space S := hS.2.1
  have hiso := h_pres.drawing_iso
  have hb₀ := admissible_bounds' hc₀
  have hxy : c₀.x < c₀.y := hb₀.2.1
  have hx_mem : c₀.x ∈ Icc w₀ w₁ := ⟨hb₀.1, hxy.le.trans hb₀.2.2.1⟩
  have hy_mem : c₀.y ∈ Icc w₀ w₁ := ⟨hb₀.1.trans hxy.le, hb₀.2.2.1⟩
  have hxV : cp c₀.x ∈ Γ.V := hb₀.2.2.2.1
  have hyV : cp c₀.y ∈ Γ.V := hb₀.2.2.2.2
  set I : Set S := cp '' Icc c₀.x c₀.y with hI_def
  have hI_sub : I ⊆ F_star j₀ := by
    rw [hW.F_eq j₀]
    exact image_mono (Icc_subset_Icc hcj.1 hcj.2)
  have hI_bd : I ⊆ bd S := hI_sub.trans (subset_bd_of_isSupportOfDrawing (h_pres.supports_isSupport j₀))
  have hI_closed : IsClosed I := (isCompact_Icc.image (GM17.cuffPoint_continuous f)).isClosed
  set H' : Hypergraph α β := supportGraph G Γ μ I with hH'_def
  set T₀ : Set (Hypergraph α β) := insideSet LO HI 𝒯 c₀ with hT₀_def
  set K_V : Set α := (⋃ J ∈ T₀, J.vertexSet) ∪ ιV '' (Γ.V ∩ I) with hKV_def
  set K_E : Set β := ⋃ J ∈ T₀, J.edgeSet with hKE_def
  set K : Hypergraph α β := subOn Γ_sub K_V K_E with hK_def
  set Γ' : Drawing S := restrictDrawing Γ ιV ιE K with hΓ'_def
  set G' : Hypergraph α β := cutB G Γ μ f a b 𝒯 LO HI c₀ with hG'_def
  -- `K` is a subgraph of `Γ_sub`.
  have hKV_sub : K_V ⊆ Γ_sub.vertexSet := by
    rintro v (hv | ⟨u, hu, rfl⟩)
    · obtain ⟨J, hJ, hvJ⟩ := mem_iUnion₂.mp hv
      exact hJ.1.1.vertexSet_subset hvJ
    · rw [← h_pres.ιV_image]
      exact ⟨u, hu.1, rfl⟩
  have hKE_sub : K_E ⊆ Γ_sub.edgeSet := by
    intro e he
    obtain ⟨J, hJ, heJ⟩ := mem_iUnion₂.mp he
    exact hJ.1.1.edgeSet_subset heJ
  have hK_le_Γ : K ≤ Γ_sub := by
    apply subOn_le
    intro e he _ x hx
    obtain ⟨J, hJ, heJ⟩ := mem_iUnion₂.mp he
    exact Or.inl (mem_biUnion hJ (J.vertex_mem_of_inc ((GM10.inc_iff_of_le hJ.1.1 heJ).2 hx)))
  have hK_V : K.vertexSet = K_V := inter_eq_left.mpr hKV_sub
  have hK_E : K.edgeSet = K_E := inter_eq_left.mpr hKE_sub
  -- `ιV '' (Γ.V ∩ I)` lies in `H'.vertexSet`.
  have hιVI_sub_H' : ιV '' (Γ.V ∩ I) ⊆ H'.vertexSet := by
    rintro _ ⟨u, hu, rfl⟩
    exact (μ_vertex_le_supportGraph_of_subset h_pres j₀ hI_sub hu).vertexSet_subset
      (ιV_mem_μ_vertex h_pres j₀ ⟨hu.1, hI_sub hu.2⟩)
  -- The pieces for `j = j₀` and `j ≠ j₀`.
  have hpiece_j₀ : piece f a b j₀ c₀.x c₀.y = I := piece_eq j₀ hcj.1 hcj.2
  have hUV_eq : (⋃ j, (supportGraph G Γ μ (piece f a b j c₀.x c₀.y)).vertexSet) = H'.vertexSet := by
    apply Subset.antisymm
    · intro v hv
      obtain ⟨j, hj⟩ := mem_iUnion.mp hv
      by_cases hjj : j = j₀
      · subst hjj
        rwa [hpiece_j₀] at hj
      · rw [piece_eq_empty_of_ne h_pres hW hjj hcj.1 hcj.2,
          (Side.supportGraph_of_eq_empty G Γ μ rfl).1] at hj
        exact hj.elim
    · intro v hv
      exact mem_iUnion.mpr ⟨j₀, by rwa [hpiece_j₀]⟩
  have hUE_eq : (⋃ j, (supportGraph G Γ μ (piece f a b j c₀.x c₀.y)).edgeSet) = H'.edgeSet := by
    apply Subset.antisymm
    · intro e he
      obtain ⟨j, hj⟩ := mem_iUnion.mp he
      by_cases hjj : j = j₀
      · subst hjj
        rwa [hpiece_j₀] at hj
      · rw [piece_eq_empty_of_ne h_pres hW hjj hcj.1 hcj.2,
          (Side.supportGraph_of_eq_empty G Γ μ rfl).2] at hj
        exact hj.elim
    · intro e he
      exact mem_iUnion.mpr ⟨j₀, by rwa [hpiece_j₀]⟩
  -- `(cutA, G')` is a separation of `G`, so `G' ≤ G`.
  obtain ⟨hsep, hsepX⟩ := isSeparation_cut h_pres hC hW hK hdeg hc₀
  have hG'_le : G' ≤ G := subOn_le (ends_subset_cutW h_pres hW)
  have hH'_le_G' : H' ≤ G' :=
    supportGraph_le_cutB hW h_pres j₀ (max_le hcj.1 le_rfl) (le_min hcj.2 le_rfl)
  have hG'_V : G'.vertexSet = K.vertexSet ∪ H'.vertexSet := by
    have hW_sub : cutW G Γ μ f a b 𝒯 LO HI c₀ ⊆ G.vertexSet := cutW_subset h_pres
    change cutW G Γ μ f a b 𝒯 LO HI c₀ ∩ G.vertexSet = _
    rw [inter_eq_left.mpr hW_sub, cutW, hUV_eq, hK_V, hKV_def, Set.union_assoc,
      union_eq_self_of_subset_left hιVI_sub_H']
  have hG'_E : G'.edgeSet = K.edgeSet ∪ H'.edgeSet := by
    have hF_sub : cutF G Γ μ f a b 𝒯 LO HI c₀ ⊆ G.edgeSet := by
      rintro e (he | he)
      · exact h_pres.drawing_subgraph.edgeSet_subset (hKE_sub he)
      · rw [hUE_eq] at he
        exact (supportGraph_le h_pres j₀ hI_sub).edgeSet_subset he
    change cutF G Γ μ f a b 𝒯 LO HI c₀ ∩ G.edgeSet = _
    rw [inter_eq_left.mpr hF_sub, cutF, hUE_eq, hK_E]
  have hK_le_G' : K ≤ G' := by
    rw [GM10.le_iff_of_le (hK_le_Γ.trans h_pres.drawing_subgraph) hG'_le, hG'_V, hG'_E]
    exact ⟨subset_union_left, subset_union_left⟩
  -- The vertices of `Γ'` in `bd S` are `Γ.V ∩ I`.
  have hΓ'V : Γ'.V = {x ∈ Γ.V | ιV x ∈ K.vertexSet} := restrictDrawing_V hiso hK_le_Γ
  have hΓ'V_bd : Γ'.V ∩ bd S = Γ.V ∩ I := by
    rw [hΓ'V, hK_V]
    ext u
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨huV, huJ | ⟨u', hu', heq⟩⟩, hubd⟩
      · obtain ⟨J, hJ, huJ'⟩ := mem_iUnion₂.mp huJ
        have hspec := hW.jumpAngles_spec h_pres hJ.1
        rcases hW.eq_end_of_mem_jump h_pres hJ.1 ⟨huV, hubd⟩ huJ' with rfl | rfl
        · exact ⟨huV, LO J, ⟨hJ.2.1, hspec.2.1.le.trans hJ.2.2.1⟩, rfl⟩
        · exact ⟨huV, HI J, ⟨hJ.2.1.trans hspec.2.1.le, hJ.2.2.1⟩, rfl⟩
      · rw [← h_pres.ιV_injOn hu'.1 huV heq]
        exact hu'
    · rintro ⟨huV, huI⟩
      exact ⟨⟨huV, Or.inr ⟨u, ⟨huV, huI⟩, rfl⟩⟩, hI_bd huI⟩
  have hΓ'V_I : Γ'.V ∩ I = Γ.V ∩ I := by
    ext x
    exact ⟨fun hx => ⟨(hΓ'V_bd ▸ ⟨hx.1, hI_bd hx.2⟩ : x ∈ Γ.V ∩ I).1, hx.2⟩,
      fun hx => ⟨(hΓ'V_bd.symm ▸ hx : x ∈ Γ'.V ∩ bd S).1, hx.2⟩⟩
  -- Every cuff of `S` has at least two vertices of `Γ'`.
  have hcuff_ge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ'.V ∩ C).ncard := by
    intro C hC'
    rw [eq_bd_of_mem_cuffs hC hC', hΓ'V_bd]
    have hne : cp c₀.x ≠ cp c₀.y := fun h => hxy.ne (angle_injOn f hW.lt_add hx_mem hy_mem h)
    have hsub : ({cp c₀.x, cp c₀.y} : Set S) ⊆ Γ.V ∩ I := by
      rintro z (rfl | rfl)
      · exact ⟨hxV, c₀.x, ⟨le_rfl, hxy.le⟩, rfl⟩
      · exact ⟨hyV, c₀.y, ⟨hxy.le, le_rfl⟩, rfl⟩
    calc 2 = ({cp c₀.x, cp c₀.y} : Set S).ncard := (ncard_pair hne).symm
      _ ≤ (Γ.V ∩ I).ncard := ncard_le_ncard hsub (Γ.finite_V.subset inter_subset_left)
  -- Spaces of `Γ'` inside `I` are spaces of `Γ` inside `I`.
  have hcomp_eq : ∀ x ∈ I \ Γ.V,
      connectedComponentIn (bd S \ Γ'.V) x = connectedComponentIn (bd S \ Γ.V) x := by
    intro x ⟨hxI, hxV_not⟩
    have hxbd : x ∈ bd S := hI_bd hxI
    have hΓ'V_sub : Γ'.V ⊆ Γ.V := by rw [hΓ'V]; exact fun z hz => hz.1
    have hdiff_sub : bd S \ Γ.V ⊆ bd S \ Γ'.V := fun z hz => ⟨hz.1, fun h => hz.2 (hΓ'V_sub h)⟩
    apply Subset.antisymm
    · set J_arc : Set S := cp '' Icc c₀.y (c₀.x + 2 * Real.pi)
      have hJ_closed : IsClosed J_arc :=
        (isCompact_Icc.image (GM17.cuffPoint_continuous f)).isClosed
      have hcov_bd : bd S ⊆ I ∪ J_arc := by
        intro z hz
        obtain ⟨t, ht, rfl⟩ := GM17.exists_cuffPoint_mem_Ico f c₀.x hz
        rcases le_total t c₀.y with hty | hyt
        · exact Or.inl ⟨t, ⟨ht.1, hty⟩, rfl⟩
        · exact Or.inr ⟨t, ⟨hyt, ht.2.le⟩, rfl⟩
      have hIJ_sub : I ∩ J_arc ⊆ Γ'.V := by
        rintro _ ⟨⟨t, ht, rfl⟩, ⟨t', ht', heq⟩⟩
        have hlt_2pi : c₀.y < c₀.x + 2 * Real.pi := by linarith [hW.lt_add, hb₀.1, hb₀.2.2.1]
        have hmem_bd : cp t ∈ Γ.V ∩ I := by
          rcases eq_or_lt_of_le ht'.2 with htop | hlt'
          · rw [← heq, htop, GM17.cuffPoint_add_two_pi]
            exact ⟨hxV, c₀.x, ⟨le_rfl, hxy.le⟩, rfl⟩
          · have hteq := GM17.cuffPoint_injOn_Ico f c₀.x ⟨ht.1, ht.2.trans_lt hlt_2pi⟩
              ⟨hxy.le.trans ht'.1, hlt'⟩ heq.symm
            have hty : t = c₀.y := le_antisymm ht.2 (hteq ▸ ht'.1)
            rw [hty]
            exact ⟨hyV, c₀.y, ⟨hxy.le, le_rfl⟩, rfl⟩
        have : cp t ∈ Γ'.V ∩ I := hΓ'V_I.symm ▸ hmem_bd
        exact this.1
      set T := connectedComponentIn (bd S \ Γ'.V) x
      have hT_sub_bd : T ⊆ bd S \ Γ'.V := connectedComponentIn_subset _ _
      have hxT : x ∈ T := mem_connectedComponentIn ⟨hxbd, fun h => hxV_not (hΓ'V_sub h)⟩
      have hT_disj : Disjoint T (I ∩ J_arc) := by
        rw [disjoint_left]
        intro z hzT hzIJ
        exact (hT_sub_bd hzT).2 (hIJ_sub hzIJ)
      have hT_I : T ⊆ I := by
        intro z hzT
        by_contra hzI
        have hzJ : z ∈ J_arc := (hcov_bd (hT_sub_bd hzT).1).resolve_left hzI
        obtain ⟨w, hwT, hwI, hwJ⟩ := isPreconnected_closed_iff.mp
          isPreconnected_connectedComponentIn I J_arc hI_closed hJ_closed
          (fun w hw => hcov_bd (hT_sub_bd hw).1) ⟨x, hxT, hxI⟩ ⟨z, hzT, hzJ⟩
        exact disjoint_left.mp hT_disj hwT ⟨hwI, hwJ⟩
      have hT_pre : IsPreconnected T := isPreconnected_connectedComponentIn
      refine hT_pre.subset_connectedComponentIn hxT
        fun z hzT => ?_
      refine ⟨(hT_sub_bd hzT).1, fun hzV => (hT_sub_bd hzT).2 ?_⟩
      have : z ∈ Γ'.V ∩ I := hΓ'V_I.symm ▸ ⟨hzV, hT_I hzT⟩
      exact this.1
    · exact connectedComponentIn_mono x hdiff_sub
  have hsp_iff : ∀ s, (s ∈ drawingSpaces Γ' ∧ s ⊆ I) ↔ (s ∈ drawingSpaces Γ ∧ s ⊆ I) := by
    intro s
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hsI⟩
      have hxI : x ∈ I := hsI (mem_connectedComponentIn hx)
      have hxV : x ∉ Γ.V := fun h => hx.2 ((hΓ'V_I.symm ▸ ⟨h, hxI⟩ : x ∈ Γ'.V ∩ I).1)
      rw [hcomp_eq x ⟨hxI, hxV⟩] at hsI ⊢
      exact ⟨⟨x, ⟨hx.1, hxV⟩, rfl⟩, hsI⟩
    · rintro ⟨⟨x, hx, rfl⟩, hsI⟩
      have hxI : x ∈ I := hsI (mem_connectedComponentIn hx)
      have hxV' : x ∉ Γ'.V := fun h => hx.2 ((hΓ'V_I ▸ ⟨h, hxI⟩ : x ∈ Γ.V ∩ I).1)
      rw [← hcomp_eq x ⟨hxI, hx.2⟩] at hsI ⊢
      exact ⟨⟨x, ⟨hx.1, hxV'⟩, rfl⟩, hsI⟩
  have hmem_V_bd_of_I : ∀ {u : S}, u ∈ I → (u ∈ Γ'.V ∩ bd S ↔ u ∈ Γ.V ∩ bd S) := by
    intro u huI
    rw [hΓ'V_bd]
    exact ⟨fun h => ⟨h.1, hI_bd h.2⟩, fun h => ⟨h.1, huI⟩⟩
  have hspace_ends_iff : ∀ {s : Set S} {u₁ u₂ : S}, s ⊆ I →
      (SpaceHasEnds Γ' s u₁ u₂ ↔ SpaceHasEnds Γ s u₁ u₂) := by
    intro s u₁ u₂ hsI
    have hclI : closure s ⊆ I := closure_minimal hsI hI_closed
    constructor
    · rintro ⟨hsp, hu₁, hu₂, hne, hline, hcl⟩
      have hu₁I : u₁ ∈ I := hclI (hcl ▸ Or.inr (Or.inl rfl))
      have hu₂I : u₂ ∈ I := hclI (hcl ▸ Or.inr (Or.inr rfl))
      exact ⟨(hsp_iff s).mp ⟨hsp, hsI⟩ |>.1, (hmem_V_bd_of_I hu₁I).mp hu₁,
        (hmem_V_bd_of_I hu₂I).mp hu₂, hne, hline, hcl⟩
    · rintro ⟨hsp, hu₁, hu₂, hne, hline, hcl⟩
      have hu₁I : u₁ ∈ I := hclI (hcl ▸ Or.inr (Or.inl rfl))
      have hu₂I : u₂ ∈ I := hclI (hcl ▸ Or.inr (Or.inr rfl))
      exact ⟨(hsp_iff s).mpr ⟨hsp, hsI⟩ |>.1, (hmem_V_bd_of_I hu₁I).mpr hu₁,
        (hmem_V_bd_of_I hu₂I).mpr hu₂, hne, hline, hcl⟩
  have hsupp_ends_iff : ∀ {F : Set S} {u₁ u₂ : S}, F ⊆ I →
      (SupportHasEnds Γ' F u₁ u₂ ↔ SupportHasEnds Γ F u₁ u₂) := by
    intro F u₁ u₂ hFI
    constructor
    · rintro (⟨v, hv, rfl, hu₁, hu₂⟩ | ⟨hFbd, hne, hu₁, hu₂, hline⟩)
      · exact Or.inl ⟨v, (hmem_V_bd_of_I (hFI (mem_singleton v))).mp hv, rfl, hu₁, hu₂⟩
      · exact Or.inr ⟨hFbd, hne, (hmem_V_bd_of_I (hFI hline.left_mem)).mp hu₁,
          (hmem_V_bd_of_I (hFI hline.right_mem)).mp hu₂, hline⟩
    · rintro (⟨v, hv, rfl, hu₁, hu₂⟩ | ⟨hFbd, hne, hu₁, hu₂, hline⟩)
      · exact Or.inl ⟨v, (hmem_V_bd_of_I (hFI (mem_singleton v))).mpr hv, rfl, hu₁, hu₂⟩
      · exact Or.inr ⟨hFbd, hne, (hmem_V_bd_of_I (hFI hline.left_mem)).mpr hu₁,
          (hmem_V_bd_of_I (hFI hline.right_mem)).mpr hu₂, hline⟩
  have hbetween_imp : ∀ {s₁ s₂ : Set S} {u : S},
      LiesBetweenInSupport Γ' I s₁ s₂ u → LiesBetweenInSupport Γ (F_star j₀) s₁ s₂ u := by
    rintro s₁ s₂ u ⟨⟨huI, huV'⟩, hs₁, hs₂, hs₁I, hs₂I, I₁, I₂, ⟨a₁, b₁, hI₁⟩, ⟨a₂, b₂, hI₂⟩,
      hun, hint, hs₁I₁, hs₂I₂⟩
    have huV : u ∈ Γ.V := (hΓ'V_I ▸ ⟨huV', huI⟩ : u ∈ Γ.V ∩ I).1
    have hI₁I : I₁ ⊆ I := hun ▸ subset_union_left
    have hI₂I : I₂ ⊆ I := hun ▸ subset_union_right
    have hbetI : LiesBetweenInSupport Γ I s₁ s₂ u :=
      ⟨⟨huI, huV⟩, (hsp_iff s₁).mp ⟨hs₁, hs₁I⟩ |>.1, (hsp_iff s₂).mp ⟨hs₂, hs₂I⟩ |>.1,
        hs₁I, hs₂I, I₁, I₂, ⟨a₁, b₁, (hsupp_ends_iff hI₁I).mp hI₁⟩,
        ⟨a₂, b₂, (hsupp_ends_iff hI₂I).mp hI₂⟩, hun, hint, hs₁I₁, hs₂I₂⟩
    exact Side.liesBetweenInSupport_mono hS h_pres.cuff_vertices_ge_two
      (h_pres.supports_isSupport j₀) hI_sub hbetI
  have hsuppGraph_eq : supportGraph G' Γ' μ I = H' := by
    have heq₁ : supportGraph G' Γ' μ I = supportGraph G' Γ μ I := by
      apply Side.supportGraph_eq_of_iff
      · intro P
        simp only [← and_assoc, hsp_iff]
      · intro P
        simp only [hΓ'V_I]
    rw [heq₁, Side.supportGraph_eq_of_le' μ hG'_le hH'_le_G']
  -- Build the defect-1 presentation in `S`.
  have hI_supp : IsSupportOfDrawing Γ I :=
    Side.isSupport_of_Icc hS hC hW hx_mem.1 hy_mem.2 hxV hyV
      ⟨cp c₀.x, c₀.x, ⟨le_rfl, hxy.le⟩, rfl⟩
  have hI_supp' : IsSupportOfDrawing Γ' I := by
    obtain ⟨u₁, u₂, h⟩ := hI_supp
    exact ⟨u₁, u₂, (hsupp_ends_iff subset_rfl).mpr h⟩
  have h_pres' : IsPresentation G' Γ' K ιV ιE 1 (fun _ => I) (fun _ => H') μ (fun _ => q j₀) := {
    is_surface := hS
    is_connected_surface := h_pres.is_connected_surface
    is_proper_drawing := restrictDrawing_isProper h_pres.is_proper_drawing
    cuff_vertices_ge_two := hcuff_ge2
    drawing_subgraph := hK_le_G'
    drawing_iso := isDrawingIso_restrictDrawing hiso hK_le_Γ
    supports_isSupport := fun _ => hI_supp'
    supports_disjoint := fun {i j} hij => absurd (Subsingleton.elim i j) hij
    bd_vertices_covered := by
      rw [hΓ'V_bd, iUnion_const]
      exact inter_subset_right
    v1_sub := fun _ => hH'_le_G'
    v1_disjoint := fun {i j} hij => absurd (Subsingleton.elim i j) hij
    v1_union_V := by rw [iUnion_const, hG'_V, Set.union_comm]
    v1_union_E := by rw [iUnion_const, hG'_E, Set.union_comm]
    v1_inter_V := fun _ => by
      rw [hΓ'V_I]
      apply Subset.antisymm
      · intro v ⟨hvH', hvK⟩
        exact supportGraph_vertexSet_inter_subset h_pres j₀ hI_sub hI_closed
          ⟨hvH', hK_le_Γ.vertexSet_subset hvK⟩
      · rintro _ ⟨u, hu, rfl⟩
        exact ⟨hιVI_sub_H' ⟨u, hu, rfl⟩, hK_V.symm ▸ Or.inr ⟨u, hu, rfl⟩⟩
    v1_inter_E := fun _ =>
      (supportGraph_edgeSet_disjoint h_pres j₀ hI_sub).mono_right hK_le_Γ.edgeSet_subset
    μ_vertex_sub := fun _ u hu => by
      rw [hΓ'V_I] at hu
      have huF : u ∈ Γ.V ∩ F_star j₀ := ⟨hu.1, hI_sub hu.2⟩
      obtain ⟨_, he, hcard, hint⟩ := h_pres.μ_vertex_sub j₀ u huF
      refine ⟨μ_vertex_le_supportGraph_of_subset h_pres j₀ hI_sub hu, he, hcard, ?_⟩
      apply Subset.antisymm
      · intro v ⟨hvμ, hvK⟩
        rw [← hint]
        exact ⟨hvμ, hK_le_Γ.vertexSet_subset hvK⟩
      · rintro _ (rfl : _ = ιV u)
        exact ⟨ιV_mem_μ_vertex h_pres j₀ huF, hK_V.symm ▸ Or.inr ⟨u, hu, rfl⟩⟩
    μ_space_sub := fun _ s hs hsI =>
      Side.μ_space_le_supportGraph_of_subset h_pres j₀ hI_sub ((hsp_iff s).mp ⟨hs, hsI⟩).1 hsI
    v2_eq := fun _ => hsuppGraph_eq.symm
    v3_space := fun _ s hs u₁ u₂ hsI hends' => by
      have hends := (hspace_ends_iff hsI).mp hends'
      have hs_Γ := ((hsp_iff s).mp ⟨hs, hsI⟩).1
      obtain ⟨h1, h2, h3⟩ := h_pres.v3_space j₀ s hs_Γ u₁ u₂ (hsI.trans hI_sub) hends
      have hclI : closure s ⊆ I := closure_minimal hsI hI_closed
      have hu₁I : u₁ ∈ Γ.V ∩ I := ⟨hends.2.1.1, hclI (hends.2.2.2.2.2 ▸ Or.inr (Or.inl rfl))⟩
      have hu₂I : u₂ ∈ Γ.V ∩ I := ⟨hends.2.2.1.1, hclI (hends.2.2.2.2.2 ▸ Or.inr (Or.inr rfl))⟩
      refine ⟨?_, h2, h3⟩
      apply Subset.antisymm
      · intro v ⟨hvμ, hvK⟩
        rw [← h1]
        exact ⟨hvμ, hK_le_Γ.vertexSet_subset hvK⟩
      · rintro v (rfl | rfl)
        · have hv : ιV u₁ ∈ (μ (.space s)).vertexSet ∩ Γ_sub.vertexSet := h1 ▸ Or.inl rfl
          exact ⟨hv.1, hK_V.symm ▸ Or.inr ⟨u₁, hu₁I, rfl⟩⟩
        · have hv : ιV u₂ ∈ (μ (.space s)).vertexSet ∩ Γ_sub.vertexSet := h1 ▸ Or.inr rfl
          exact ⟨hv.1, hK_V.symm ▸ Or.inr ⟨u₂, hu₂I, rfl⟩⟩
    v4_between := fun _ s₁ s₂ u hbet =>
      h_pres.v4_between j₀ s₁ s₂ u (hbetween_imp hbet)
    q_pos := fun _ => h_pres.q_pos j₀
  }
  have hdepth' : PresentationHasDepthLe G' Γ' K ιV ιE 1 (fun _ => I) (fun _ => H') μ d :=
    ⟨fun _ => q j₀, h_pres', fun _ => hq j₀, fun h0 => absurd h0 Nat.one_ne_zero⟩
  -- `L ∩ G'` is an exhaustive vital `(p + 2d)`-linkage in `G'`.
  have hLlink : IsLinkage G L := hL.1.1
  obtain ⟨hlink', hterm'⟩ := theorem_2_2_proof hLlink hsep
  have hvital' := (theorem_2_3_proof hLlink hsep).2 hL.1
  rw [hsepX] at hterm'
  have hcutX_sub_H' : cutX μ f c₀ ⊆ H'.vertexSet := by
    have hxI : cp c₀.x ∈ Γ.V ∩ I := ⟨hxV, c₀.x, ⟨le_rfl, hxy.le⟩, rfl⟩
    have hyI : cp c₀.y ∈ Γ.V ∩ I := ⟨hyV, c₀.y, ⟨hxy.le, le_rfl⟩, rfl⟩
    exact union_subset
      (μ_vertex_le_supportGraph_of_subset h_pres j₀ hI_sub hxI).vertexSet_subset
      (μ_vertex_le_supportGraph_of_subset h_pres j₀ hI_sub hyI).vertexSet_subset
  have hL'_exh : IsExhaustiveLinkage G' K 1 (fun _ => H') (L ∩ G') := by
    refine ⟨hvital', le_inter' (hK_le_Γ.trans hL.2.1) hK_le_G', ?_⟩
    rw [iUnion_const]
    intro v hv
    rcases hterm' hv with ⟨hvL, _⟩ | hvX
    · have hvG' : v ∈ G'.vertexSet := hv.1.2
      rw [hG'_V] at hvG'
      rcases hvG' with hvK | hvH'
      · obtain ⟨j, hj⟩ := mem_iUnion.mp (hL.2.2 hvL)
        have hmem : v ∈ (H j).vertexSet ∩ Γ_sub.vertexSet := ⟨hj, hK_le_Γ.vertexSet_subset hvK⟩
        rw [h_pres.v1_inter_V j] at hmem
        obtain ⟨u, ⟨huV, huF⟩, rfl⟩ := hmem
        have hubd : u ∈ Γ.V ∩ bd S :=
          ⟨huV, subset_bd_of_isSupportOfDrawing (h_pres.supports_isSupport j) huF⟩
        have huΓ' : u ∈ Γ'.V ∩ bd S := ⟨by rw [hΓ'V]; exact ⟨huV, hvK⟩, hubd.2⟩
        rw [hΓ'V_bd] at huΓ'
        exact hιVI_sub_H' ⟨u, huΓ', rfl⟩
      · exact hvH'
    · exact hcutX_sub_H' hvX
  have hL'_p : IsPLinkage G' (L ∩ G') (p + 2 * d) := by
    refine ⟨hlink', ?_⟩
    have hfinT : (terminals L).Finite := L.vertexSet_finite.subset fun x hx => hx.1
    have hfinX : (cutX μ f c₀).Finite :=
      (μ (.vertex (cp c₀.x))).vertexSet_finite.union (μ (.vertex (cp c₀.y))).vertexSet_finite
    calc (terminals (L ∩ G')).ncard
        ≤ ((terminals L \ (cutA G Γ μ f a b 𝒯 LO HI c₀).vertexSet) ∪ cutX μ f c₀).ncard :=
          ncard_le_ncard hterm' (hfinT.sdiff.union hfinX)
      _ ≤ (terminals L \ (cutA G Γ μ f a b 𝒯 LO HI c₀).vertexSet).ncard + (cutX μ f c₀).ncard :=
          ncard_union_le _ _
      _ ≤ (terminals L).ncard + (cutX μ f c₀).ncard :=
          Nat.add_le_add_right (ncard_le_ncard sdiff_subset hfinT) _
      _ ≤ p + 2 * d := Nat.add_le_add hpL.2 (ncard_cutX_le h_pres hW hc₀ hq)
  -- Every jump in `T₀` is a `Σ`-jump of `(Γ', K)`.
  have hT₀_sub : T₀ ⊆ sigmaJumps Γ' K ιV := by
    intro J hJ
    have hJ_sigma : IsSigmaJump Γ Γ_sub ιV J := by
      change J ∈ sigmaJumps Γ Γ_sub ιV
      rw [sigmaJumps_eq_jumpSet hiso]
      exact hJ.1
    obtain ⟨hJΓ, hpath, u, hu, v, hv, huv, hterm, hint⟩ := hJ_sigma
    have hspec := hW.jumpAngles_spec h_pres hJ.1
    have hloI : cp (LO J) ∈ Γ.V ∩ I :=
      ⟨hspec.2.2.2.1, LO J, ⟨hJ.2.1, hspec.2.1.le.trans hJ.2.2.1⟩, rfl⟩
    have hhiI : cp (HI J) ∈ Γ.V ∩ I :=
      ⟨hspec.2.2.2.2.1, HI J, ⟨hJ.2.1.trans hspec.2.1.le, hJ.2.2.1⟩, rfl⟩
    have hu_mem : ιV u ∈ terminals J := hterm ▸ Or.inl rfl
    have hv_mem : ιV v ∈ terminals J := hterm ▸ Or.inr rfl
    rw [hspec.2.2.2.2.2] at hu_mem hv_mem
    have hu' : u ∈ Γ'.V ∩ bd S := by
      rw [hΓ'V_bd]
      rcases hu_mem with h | h
      · rwa [h_pres.ιV_injOn hu.1 hspec.2.2.2.1 h]
      · rwa [h_pres.ιV_injOn hu.1 hspec.2.2.2.2.1 h]
    have hv' : v ∈ Γ'.V ∩ bd S := by
      rw [hΓ'V_bd]
      rcases hv_mem with h | h
      · rwa [h_pres.ιV_injOn hv.1 hspec.2.2.2.1 h]
      · rwa [h_pres.ιV_injOn hv.1 hspec.2.2.2.2.1 h]
    have hJK : J ≤ K :=
      le_subOn hJΓ (fun x hx => Or.inl (mem_biUnion hJ hx)) (fun e he => mem_biUnion hJ he)
    refine ⟨hJK, hpath, u, hu', v, hv', huv, hterm, fun w hw hwJ => ?_⟩
    rw [hΓ'V_bd] at hw
    exact hint w ⟨hw.1, hI_bd hw.2⟩ hwJ
  have hG'_graph : G'.IsGraph := isGraph_of_le hG'_le hG
  have h_encard := (encard_le_encard hT₀_sub).trans
    (hlam' G' Γ' K ιV ιE (fun _ => I) (fun _ => H') μ (L ∩ G') hD hG'_graph hdepth' hL'_exh hL'_p)
  have hT₀_fin : T₀.Finite := (jumpSet_finite hdeg).subset fun J hJ => hJ.1
  rw [← hT₀_fin.cast_ncard_eq] at h_encard
  exact_mod_cast h_encard

end defect_one

end DiscCut
end GM21
end GraphMinor
