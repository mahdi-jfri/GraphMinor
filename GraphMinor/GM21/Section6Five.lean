module

public import GraphMinor.GM21.Section6Four
public import GraphMinor.GM21.Section6CutsBlocks
public import GraphMinor.GM21.Section6FiveOne
public import GraphMinor.GM21.Section6ThreeSupports
import GraphMinor.GM21.Section6
import GraphMinor.GM21.Section6PathLinkage
import GraphMinor.GM21.Section6Exhaustive
import GraphMinor.GM21.LinkageLemmas
import GraphMinor.GM21.LinkagePaths
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM10.TangleLemmas
import Mathlib.Data.Finset.Sort

/-!
# Graph Minors XXI, (6.5), (6.6) and (6.7): discs of any defect

"**6.5** *For all integers $p \ge 0$ and $q \ge 1$ there exists $\lambda \ge 0$ such that, if $G$
has a presentation in a disc $\Sigma$ of depth $\le q$ and defect 2, and there is an exhaustive
vital $p$-linkage in $G$, then there are at most $\lambda$ $\Sigma$-jumps.*" (page 25 of the
preprint)

We follow the paper's proofs of (6.5), (6.6) and (6.7), read by angles as in `Section6DiscSep`:

- **(6.5) (`theorem_6_5`):**
  - *The regions between two supports.* "Let $r_1, \ldots, r_t$ be all the regions of $\Gamma$ in
    $\Sigma$ which are incident both with a vertex in $F_1^*$ and with a vertex in $F_2^*$ ...
    For $1 \le i < t$, let $P_i$ be the $\Sigma$-jump with $\bar{r}_i \cap \bar{r}_{i+1} = U(P_i)$".
    The jumps $P_1, \ldots, P_{t-1}$ are the jumps with one end in each support (the *cross* jumps,
    `Cuts.blockCross`); they are nested (`cross_nested`), and the line $F_{i+1}$ of the paper, drawn
    in $r_{i+1}$ next to $P_i$, is described by the cut along $P_i$ (`jumpCut`).
  - *$t \le n$, from (2.5).* "for $1 \le i < t$, there are $q_j$ mutually vertex-disjoint paths of
    $H_j \cap B_i \cap A_{i+1}$ ... it follows that there are $q_1 + q_2$ mutually vertex-disjoint
    paths of $(H_1 \cup H_2) \cap B_i \cap A_{i+1}$" is `exists_cross_transfer_linkage`, and the
    bound on the number of cross jumps is `ncard_crossSet_lt`.
  - *Each region holds at most $2\lambda'$ jumps.* The paper applies (6.4) to the presentation of
    $\Gamma_j \cup \mu(I_j)$ in a disc with defect 1 and exhaustive vital $(p + 2q)$-linkage
    $L \cap (\Gamma_j \cup \mu(I_j))$ (`DiscCut.ncard_insideSet_le_of_theorem_6_4` in
    `Section6FiveOne`).
  - *The count*, "$2\lambda't + t - 1 \le \lambda$" with $\lambda = n(2\lambda' + 1)$, is
    `Cuts.ncard_le_of_two_blocks`.
- **(6.6) (`theorem_6_6`):** A region $r_0$ incident with vertices in all three supports
  (`ThreeSupports.exists_region_three_supports`) cuts the disc $\Sigma$ into three closed discs
  $\Delta_1, \Delta_2, \Delta_3$, each carrying a presentation of defect 2 with an exhaustive vital
  $(p + 2q)$-linkage (`ThreeSupports.encard_sigmaJumps_le_three_of_region`), giving
  $\lambda = 3\lambda'$.
- **(6.7) (`theorem_6_7`):** Proved by induction on $r$. For $r \le 3$ the result follows from
  (6.4), (6.5) and (6.6); for $r \ge 4$, a region $r_0$ incident with vertices in three supports
  provides a line cutting $\Sigma$ into two closed discs of defect $< r$
  (`ThreeSupports.encard_sigmaJumps_le_two_of_region_three`), giving $\lambda = 2\lambda'$.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace DiscCut

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM21.Supports
open GraphMinor.GM21.Cuts

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- Two systems of disjoint paths in vertex-disjoint graphs `K₁, K₂` together form a system of
disjoint paths in `K₁ ∪ K₂`. -/
theorem hasDisjointPaths_union {K₁ K₂ : Hypergraph α β}
    (hd : Disjoint K₁.vertexSet K₂.vertexSet) {X₁ Y₁ X₂ Y₂ : Set α} {k₁ k₂ : ℕ}
    (hX₁ : X₁ ⊆ K₁.vertexSet) (hX₂ : X₂ ⊆ K₂.vertexSet)
    (h₁ : HasDisjointPaths K₁.skeleton X₁ Y₁ k₁) (h₂ : HasDisjointPaths K₂.skeleton X₂ Y₂ k₂) :
    HasDisjointPaths (K₁ ∪ K₂).skeleton (X₁ ∪ X₂) (Y₁ ∪ Y₂) (k₁ + k₂) := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  let Q₁ : Fin k₁ → PathFromTo (K₁ ∪ K₂).skeleton (X₁ ∪ X₂) (Y₁ ∪ Y₂) := fun i =>
    ⟨(P₁ i).first, (P₁ i).last, (P₁ i).walk.mapLe (skeleton_le_union_left K₁ K₂),
      (P₁ i).isPath.mapLe _, Or.inl (P₁ i).first_mem, Or.inl (P₁ i).last_mem⟩
  let Q₂ : Fin k₂ → PathFromTo (K₁ ∪ K₂).skeleton (X₁ ∪ X₂) (Y₁ ∪ Y₂) := fun i =>
    ⟨(P₂ i).first, (P₂ i).last, (P₂ i).walk.mapLe (skeleton_le_union_right K₁ K₂),
      (P₂ i).isPath.mapLe _, Or.inr (P₂ i).first_mem, Or.inr (P₂ i).last_mem⟩
  have hs₁ : ∀ i, {x | x ∈ (Q₁ i).walk.support} ⊆ K₁.vertexSet := fun i x hx => by
    have hx' : x ∈ (P₁ i).walk.support := by
      simpa [Q₁, SimpleGraph.Walk.support_mapLe_eq_support] using hx
    exact mem_vertexSet_of_mem_walk_support (hX₁ (P₁ i).first_mem) _ hx'
  have hs₂ : ∀ i, {x | x ∈ (Q₂ i).walk.support} ⊆ K₂.vertexSet := fun i x hx => by
    have hx' : x ∈ (P₂ i).walk.support := by
      simpa [Q₂, SimpleGraph.Walk.support_mapLe_eq_support] using hx
    exact mem_vertexSet_of_mem_walk_support (hX₂ (P₂ i).first_mem) _ hx'
  refine ⟨Fin.append Q₁ Q₂, ?_⟩
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_left, Fin.append_left]
      have hne : i ≠ j := fun h => hij (by rw [h])
      simpa [Q₁, SimpleGraph.Walk.support_mapLe_eq_support] using hP₁ hne
    | right j =>
      rw [Fin.append_left, Fin.append_right]
      exact hd.mono (hs₁ i) (hs₂ j)
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_right, Fin.append_left]
      exact hd.symm.mono (hs₂ i) (hs₁ j)
    | right j =>
      rw [Fin.append_right, Fin.append_right]
      have hne : i ≠ j := fun h => hij (by rw [h])
      simpa [Q₂, SimpleGraph.Walk.support_mapLe_eq_support] using hP₂ hne

/-- A finite set with an injective real key has, for every `N` at most its size, a sequence of
`N` members with strictly increasing keys. -/
theorem exists_strictMono_seq {ι : Type*} {X : Set ι} (hX : X.Finite) (κ : ι → ℝ)
    (hinj : InjOn κ X) {N : ℕ} (hN : N ≤ X.ncard) :
    ∃ P : Fin N → ι, (∀ i, P i ∈ X) ∧ StrictMono (κ ∘ P) := by
  classical
  set K : Finset ℝ := hX.toFinset.image κ with hK
  have hKcard : K.card = X.ncard := by
    rw [hK, Finset.card_image_of_injOn (by simpa using hinj), ncard_eq_toFinset_card X hX]
  have hNK : N ≤ K.card := hKcard ▸ hN
  set e := K.orderEmbOfFin rfl with he
  have hpre : ∀ i : Fin N, ∃ J ∈ X, κ J = e (Fin.castLE hNK i) := by
    intro i
    have := K.orderEmbOfFin_mem rfl (Fin.castLE hNK i)
    obtain ⟨J, hJ, hJe⟩ := Finset.mem_image.1 this
    exact ⟨J, (Set.Finite.mem_toFinset hX).1 hJ, hJe⟩
  choose P hPX hPκ using hpre
  refine ⟨P, hPX, fun i i' hii' => ?_⟩
  simp only [Function.comp, hPκ]
  exact e.strictMono ((Fin.castLE_lt_castLE_iff hNK).2 hii')

section claims

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
set_option hygiene false in
local notation "AA" => cutA G Γ μ f a b 𝒯 LO HI
set_option hygiene false in
local notation "BB" => cutB G Γ μ f a b 𝒯 LO HI

include h_pres hW

omit hW in
/-- `|X(c)| = q_{j₁} + q_{j₂}` for a cut from `F_{j₁}*` to `F_{j₂}*`: "Since
$\mu(a_i) \cap \mu(b_i) = \emptyset$, it follows that $|V(A_i \cap B_i)| = q_1 + q_2$". -/
theorem ncard_cutX_eq {j₁ j₂ : Fin r} (hjj : j₁ ≠ j₂) {c : Cut}
    (hx : cp c.x ∈ Γ.V ∩ F_star j₁) (hy : cp c.y ∈ Γ.V ∩ F_star j₂) :
    (cutX μ f c).ncard = q j₁ + q j₂ := by
  have h₁ := h_pres.μ_vertex_sub j₁ _ hx
  have h₂ := h_pres.μ_vertex_sub j₂ _ hy
  rw [cutX, ncard_union_eq ((h_pres.v1_disjoint hjj).mono h₁.1.vertexSet_subset
      h₂.1.vertexSet_subset) ((G.vertexSet_finite.subset (μ_vertex_le h_pres j₁ hx).vertexSet_subset))
      ((G.vertexSet_finite.subset (μ_vertex_le h_pres j₂ hy).vertexSet_subset)), h₁.2.2.1, h₂.2.2.1]

include hC hK hdeg

/-- **The linkages of the proof of (6.5)**: for nested cuts `c ⊇ c'` from `F_{j₁}*` to
`F_{j₂}*`, "there are $q_1 + q_2$ mutually vertex-disjoint paths of
$(H_1 \cup H_2) \cap B_i \cap A_{i+1}$ between $V(A_i \cap B_i)$ and
$V(A_{i+1} \cap B_{i+1})$", from (6.2) applied in each support. They form a linkage with
`q_{j₁} + q_{j₂}` components and no edge of `Γ`. -/
theorem exists_cross_transfer_linkage (hG : G.IsGraph) {j₁ j₂ : Fin r} (hjj : j₁ ≠ j₂)
    {c c' : Cut} (hc : Admissible LO HI 𝒯 POS c) (hc' : Admissible LO HI 𝒯 POS c')
    (hx : a j₁ ≤ c.x) (hxx' : c.x ≤ c'.x) (hx' : c'.x ≤ b j₁)
    (hy' : a j₂ ≤ c'.y) (hy'y : c'.y ≤ c.y) (hy : c.y ≤ b j₂) :
    ∃ M : Hypergraph α β,
      IsLinkage (BB c ∩ AA c') M ∧
      (linkagePattern M).ncard = q j₁ + q j₂ ∧
      (∀ P ∈ linkagePattern M, ∃ u ∈ (AA c ∩ BB c).vertexSet,
        ∃ w ∈ (AA c' ∩ BB c').vertexSet, P = {u, w}) ∧
      Disjoint M.edgeSet Γ_sub.edgeSet := by
  have hS := h_pres.is_surface
  have hb := admissible_bounds' hc
  have hb' := admissible_bounds' hc'
  have hlt₁ : b j₁ < a j₁ + 2 * Real.pi := by linarith [hW.lt_add, hW.le_a j₁, hW.b_le j₁]
  have hlt₂ : b j₂ < a j₂ + 2 * Real.pi := by linarith [hW.lt_add, hW.le_a j₂, hW.b_le j₂]
  have hI₁sub := image_Icc_subset j₁ f (hW.F_eq j₁) hx hx'
  have hI₂sub := image_Icc_subset j₂ f (hW.F_eq j₂) hy' hy
  have hI₁ends := supportHasEnds_cuffPoint_Icc hS hC f hx hxx' hx' hlt₁ hb.2.2.2.1 hb'.2.2.2.1
  have hI₂ends := supportHasEnds_cuffPoint_Icc hS hC f hy' hy'y hy hlt₂ hb'.2.2.2.2 hb.2.2.2.2
  have hp₁ := theorem_6_2_proof h_pres j₁ hI₁sub hI₁ends
  have hp₂ := hasDisjointPaths_symm (theorem_6_2_proof h_pres j₂ hI₂sub hI₂ends)
  have hxI : cp c.x ∈ Γ.V ∩ cp '' Icc c.x c'.x := ⟨hb.2.2.2.1, c.x, ⟨le_rfl, hxx'⟩, rfl⟩
  have hyI : cp c.y ∈ Γ.V ∩ cp '' Icc c'.y c.y := ⟨hb.2.2.2.2, c.y, ⟨hy'y, le_rfl⟩, rfl⟩
  have hX₁ := (μ_vertex_le_supportGraph_of_subset h_pres j₁ hI₁sub hxI).vertexSet_subset
  have hX₂ := (μ_vertex_le_supportGraph_of_subset h_pres j₂ hI₂sub hyI).vertexSet_subset
  have hdisj : Disjoint (supportGraph G Γ μ (cp '' Icc c.x c'.x)).vertexSet
      (supportGraph G Γ μ (cp '' Icc c'.y c.y)).vertexSet :=
    (h_pres.v1_disjoint hjj).mono (supportGraph_le_H h_pres hI₁sub).vertexSet_subset
      (supportGraph_le_H h_pres hI₂sub).vertexSet_subset
  have hpaths := hasDisjointPaths_union hdisj hX₁ hX₂ hp₁ hp₂
  have hK₀G := GM10.union_le (supportGraph_le h_pres j₁ hI₁sub) (supportGraph_le h_pres j₂ hI₂sub)
  have hK₀g := isGraph_of_le hK₀G hG
  obtain ⟨M, hML, hMcard, hMP⟩ := exists_linkage_of_hasDisjointPaths hK₀g
    (union_subset_union hX₁ hX₂) hpaths
  have hK₀B : supportGraph G Γ μ (cp '' Icc c.x c'.x) ∪ supportGraph G Γ μ (cp '' Icc c'.y c.y) ≤
      BB c :=
    GM10.union_le (supportGraph_le_cutB hW h_pres j₁ (max_le hx le_rfl)
        (le_min hx' (hb'.2.1.le.trans hy'y)))
      (supportGraph_le_cutB hW h_pres j₂ (max_le hy' (hxx'.trans hb'.2.1.le)) (le_min hy le_rfl))
  have hK₀A : supportGraph G Γ μ (cp '' Icc c.x c'.x) ∪ supportGraph G Γ μ (cp '' Icc c'.y c.y) ≤
      AA c' :=
    GM10.union_le (supportGraph_le_cutA h_pres hC hW hG hc' j₁ hx hxx' hx' hb.2.2.2.1
        hb'.2.2.2.1 (Or.inl le_rfl))
      (supportGraph_le_cutA h_pres hC hW hG hc' j₂ hy' hy'y hy hb'.2.2.2.2 hb.2.2.2.2
        (Or.inr le_rfl))
  have hK₀ := le_inter' hK₀B hK₀A
  have hsep := (isSeparation_cut h_pres hC hW hK hdeg hc).2
  have hsep' := (isSeparation_cut h_pres hC hW hK hdeg hc').2
  refine ⟨M, ⟨hML.1.trans hK₀, hML.2⟩, hMcard, ?_, ?_⟩
  · intro P hP
    obtain ⟨u, hu, w, hw, rfl⟩ := hMP P hP
    refine ⟨u, by rw [hsep]; exact hu, w, ?_, rfl⟩
    rw [hsep']
    exact hw
  · rw [Set.disjoint_left]
    intro e he heΓ
    rcases hML.1.edgeSet_subset he with he' | he'
    · exact Set.disjoint_left.mp (supportGraph_edgeSet_disjoint h_pres j₁ hI₁sub) he' heΓ
    · exact Set.disjoint_left.mp (supportGraph_edgeSet_disjoint h_pres j₂ hI₂sub) he' heΓ

/-- The cut along a jump `J`, with `J` inside: the line $F_{i+1}$ of the proof of (6.5), drawn
next to $P_i$ in $r_{i+1}$. -/
def jumpCut (lo hi : Hypergraph α β → ℝ) (J : Hypergraph α β) : Cut := ⟨lo J, hi J, true⟩

omit hC in
/-- Two cross jumps are nested. -/
theorem cross_nested (hD : GM06.IsClosedDiscSpace S) {x₀ e₁ s₂ y₀ : ℝ} (he : e₁ < s₂)
    {J J' : Hypergraph α β}
    (hJ : J ∈ blockCross LO HI 𝒯 x₀ e₁ s₂ y₀) (hJ' : J' ∈ blockCross LO HI 𝒯 x₀ e₁ s₂ y₀) :
    (LO J ≤ LO J' ∧ HI J' ≤ HI J) ∨ (LO J' ≤ LO J ∧ HI J ≤ HI J') := by
  have h1 := hW.not_cross_of_mem_jumpSet h_pres hD hK hdeg hJ.1 hJ'.1
  have h2 := hW.not_cross_of_mem_jumpSet h_pres hD hK hdeg hJ'.1 hJ.1
  obtain ⟨-, ⟨-, hJe⟩, ⟨hJs, -⟩⟩ := hJ
  obtain ⟨-, ⟨-, hJ'e⟩, ⟨hJ's, -⟩⟩ := hJ'
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  rcases lt_or_ge (LO J) (LO J') with hl | hl
  · have hh : HI J < HI J' := hc1 hl.le
    exact h1 ⟨hl, by linarith, hh⟩
  · rcases eq_or_lt_of_le hl with hl' | hl'
    · rcases lt_or_ge (HI J) (HI J') with hh | hh
      · exact absurd (hc2 hl'.le) (not_lt.2 hh.le)
      · exact absurd (hc1 hl'.ge) (not_lt.2 hh)
    · have hh : HI J' < HI J := hc2 hl'.le
      exact h2 ⟨hl', by linarith, hh⟩

/-- **$t \le n$.** If `n` has the property of (2.6) for `p` and `k ≥ 2 d`, where `d` bounds the
depth, then fewer than `n` jumps have one end in `[a j₁, b j₁]` and the other in `[a j₂, b j₂]`,
when `b j₁ < a j₂`. "Choose $n \ge 0$ as in (2.5) with $k$ replaced by $2q$. ... From (2.5), it
follows that $t \le n$." -/
theorem ncard_crossSet_lt (hD : GM06.IsClosedDiscSpace S) (hG : G.IsGraph)
    {L : Hypergraph α β} {p k n dd : ℕ}
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (hpL : IsPLinkage G L p) (hq : ∀ j, q j ≤ dd)
    (hk : 2 * dd ≤ k)
    (hn : ∀ (A B : Fin n → Hypergraph α β) (M : Fin n → Fin n → Hypergraph α β),
      IsVitalPLinkage G L p →
      (∀ i : Fin n, G.IsSeparation (A i) (B i) ∧ separationOrder (A i) (B i) ≤ k) →
      (∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i) →
      (∀ i i' : Fin n, i < i' →
        separationOrder (A i) (B i) = separationOrder (A i') (B i') →
        (∀ j : Fin n, i < j → j < i' →
          separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
        IsLinkage (B i ∩ A i') (M i i') ∧
        (linkagePattern (M i i')).ncard = separationOrder (A i) (B i) ∧
        ∀ P ∈ linkagePattern (M i i'),
          ∃ u ∈ (A i ∩ B i).vertexSet, ∃ w ∈ (A i' ∩ B i').vertexSet, P = {u, w}) →
      ∃ i i' : Fin n, i < i' ∧
        separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
        (∀ j : Fin n, i < j → j < i' →
          separationOrder (A i) (B i) < separationOrder (A j) (B j)) ∧
        L ∩ B i ∩ A i' = M i i')
    {j₁ j₂ : Fin r} (he : b j₁ < a j₂) :
    (blockCross LO HI 𝒯 (a j₁) (b j₁) (a j₂) (b j₂)).ncard < n := by
  classical
  by_contra hnot
  push Not at hnot
  set X := blockCross LO HI 𝒯 (a j₁) (b j₁) (a j₂) (b j₂) with hX
  have hjj : j₁ ≠ j₂ := by
    rintro rfl
    linarith [hW.a_le_b j₁]
  have hXfin : X.Finite := (jumpSet_finite hdeg).subset fun J hJ => hJ.1
  have hspec := fun {J} (hJ : J ∈ 𝒯) => hW.jumpAngles_spec h_pres hJ
  -- The key `LO - HI` orders the cross jumps from the outside in.
  have hinj : InjOn (fun J => LO J - HI J) X := by
    intro J hJ J' hJ' hκ
    simp only at hκ
    rcases cross_nested h_pres hW hK hdeg hD he hJ hJ' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    · exact hW.jump_eq_of_angles h_pres hK hdeg hJ.1 hJ'.1 (by linarith) (by linarith)
  obtain ⟨P, hPX, hPmono⟩ := exists_strictMono_seq hXfin _ hinj hnot
  have hPlt : ∀ i i' : Fin n, i < i' → LO (P i) ≤ LO (P i') ∧ HI (P i') ≤ HI (P i) ∧
      (LO (P i) < LO (P i') ∨ HI (P i') < HI (P i)) := by
    intro i i' hii'
    have hκ := hPmono hii'
    simp only [Function.comp] at hκ
    rcases cross_nested h_pres hW hK hdeg hD he (hPX i) (hPX i') with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨h1, h2, ?_⟩
      by_contra h
      push Not at h
      linarith [h.1, h.2]
    · exfalso
      linarith
  set d : Fin n → Cut := fun i => jumpCut LO HI (P i) with hd
  have hadm : ∀ i, Admissible LO HI 𝒯 POS (d i) := by
    intro i
    have hPi := (hPX i).1
    refine ⟨⟨hW.jumpLo_mem h_pres hPi, (hspec hPi).2.2.2.1⟩,
      ⟨hW.jumpHi_mem h_pres hPi, (hspec hPi).2.2.2.2.1⟩, (hspec hPi).2.1, fun J hJ => ⟨?_, ?_⟩⟩
    · exact hW.not_cross_of_mem_jumpSet h_pres hD hK hdeg hPi hJ
    · exact hW.not_cross_of_mem_jumpSet h_pres hD hK hdeg hJ hPi
  have hnest : ∀ i i' : Fin n, i < i' → Nested LO HI 𝒯 (d i) (d i') := by
    intro i i' hii'
    obtain ⟨h1, h2, -⟩ := hPlt i i' hii'
    refine ⟨h1, h2, ?_⟩
    rintro J ⟨hJ, hJ1, hJ2, -⟩
    exact ⟨hJ, h1.trans hJ1, hJ2.trans h2, Or.inl rfl⟩
  set A : Fin n → Hypergraph α β := fun i => AA (d i) with hA_def
  set B : Fin n → Hypergraph α β := fun i => BB (d i) with hB_def
  have hsep : ∀ i, G.IsSeparation (A i) (B i) ∧ (A i ∩ B i).vertexSet = cutX μ f (d i) :=
    fun i => isSeparation_cut h_pres hC hW hK hdeg (hadm i)
  have hFx : ∀ i, cp (d i).x ∈ Γ.V ∩ F_star j₁ := fun i =>
    ⟨(hspec (hPX i).1).2.2.2.1, by rw [hW.F_eq j₁]; exact ⟨_, (hPX i).2.1, rfl⟩⟩
  have hFy : ∀ i, cp (d i).y ∈ Γ.V ∩ F_star j₂ := fun i =>
    ⟨(hspec (hPX i).1).2.2.2.2.1,
      by rw [hW.F_eq j₂]; exact ⟨_, (hPX i).2.2, rfl⟩⟩
  have hord : ∀ i, separationOrder (A i) (B i) = q j₁ + q j₂ := fun i => by
    unfold separationOrder
    rw [(hsep i).2]
    exact ncard_cutX_eq h_pres hjj (hFx i) (hFy i)
  let Pm : Fin n → Fin n → Hypergraph α β → Prop := fun i i' M =>
    IsLinkage (B i ∩ A i') M ∧ (linkagePattern M).ncard = separationOrder (A i) (B i) ∧
      (∀ P ∈ linkagePattern M,
        ∃ u ∈ (A i ∩ B i).vertexSet, ∃ w ∈ (A i' ∩ B i').vertexSet, P = {u, w}) ∧
      Disjoint M.edgeSet Γ_sub.edgeSet
  let M : Fin n → Fin n → Hypergraph α β := fun i i' =>
    if h : ∃ M, Pm i i' M then h.choose else G
  have hM : ∀ i i', i < i' → Pm i i' (M i i') := by
    intro i i' hii'
    obtain ⟨h1, h2, -⟩ := hPlt i i' hii'
    have hex : ∃ M, Pm i i' M := by
      obtain ⟨M₀, h₁, h₂, h₃, h₄⟩ := exists_cross_transfer_linkage h_pres hC hW hK hdeg hG hjj
        (hadm i) (hadm i') (hPX i).2.1.1 h1 (hPX i').2.1.2 (hPX i').2.2.1 h2 (hPX i).2.2.2
      exact ⟨M₀, h₁, by rw [hord]; exact h₂, h₃, h₄⟩
    show Pm i i' (if h : ∃ M, Pm i i' M then h.choose else G)
    rw [dite_eq_left hex]
    exact hex.choose_spec
  have hordk : ∀ i, separationOrder (A i) (B i) ≤ k := fun i => by
    rw [hord]
    linarith [hq j₁, hq j₂]
  obtain ⟨i, i', hii', -, -, hLM⟩ := hn A B M ⟨hL.1, hpL⟩ (fun i => ⟨(hsep i).1, hordk i⟩)
    (fun i j hij => cut_nested h_pres hC hW hK hdeg (hadm i) (hadm j) (hnest i j hij))
    (fun i i' h _ _ => ⟨(hM i i' h).1, (hM i i' h).2.1, (hM i i' h).2.2.1⟩)
  -- The jump `P i` is inside the `i`th cut but not inside the `i'`th one.
  have hJi : P i ∈ insideSet LO HI 𝒯 (d i) := ⟨(hPX i).1, le_rfl, le_rfl, Or.inl rfl⟩
  have hJi' : P i ∉ insideSet LO HI 𝒯 (d i') := by
    rintro ⟨-, h1, h2, -⟩
    obtain ⟨h1', h2', h3'⟩ := hPlt i i' hii'
    change LO (P i') ≤ LO (P i) at h1
    change HI (P i) ≤ HI (P i') at h2
    rcases h3' with h | h <;> linarith
  obtain ⟨e, heJ⟩ := edgeSet_nonempty_of_mem_jumpSet hJi.1
  have heΓ : e ∈ Γ_sub.edgeSet := hJi.1.1.edgeSet_subset heJ
  have heG : e ∈ G.edgeSet := h_pres.drawing_subgraph.edgeSet_subset heΓ
  have hnotF : e ∉ cutF G Γ μ f a b 𝒯 LO HI (d i') := by
    rintro (h | h)
    · rw [mem_iUnion₂] at h
      obtain ⟨J', hJ', heJ'⟩ := h
      obtain rfl := jump_eq_of_edge hdeg hJi.1 hJ'.1 heJ heJ'
      exact hJi' hJ'
    · rw [mem_iUnion] at h
      obtain ⟨j', h⟩ := h
      exact Set.disjoint_left.mp
        (supportGraph_edgeSet_disjoint h_pres j' (piece_subset hW j' _ _)) h heΓ
  have heM : e ∈ (M i i').edgeSet := by
    rw [← hLM]
    exact ⟨⟨hL.2.1.edgeSet_subset heΓ, ⟨Or.inl (mem_biUnion hJi heJ), heG⟩⟩,
      ⟨⟨heG, hnotF⟩, heG⟩⟩
  exact Set.disjoint_left.mp (hM i i' hii').2.2.2 heM heΓ

/-- **The count of (6.5) for two supports** (Graph Minors XXI, page 26 of the preprint).
If `n ≥ 1` has the property of (2.6) for `p` and `k ≥ 2 d`, where `d` bounds the depth, and `lam'`
has the property of (6.4) for `(p + 2 d, d)`, then for two supports `j₁, j₂` with `b j₁ < a j₂`
covering all supports, there are at most `n * (2 * lam' + 1)` jumps. -/
theorem ncard_jumpSet_le_two_supports (hD : GM06.IsClosedDiscSpace S) (hG : G.IsGraph)
    {L : Hypergraph α β} {p k n dd lam' : ℕ}
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (hpL : IsPLinkage G L p) (hq : ∀ j, q j ≤ dd)
    (hk : 2 * dd ≤ k) (hn1 : 1 ≤ n)
    (hn : ∀ (A B : Fin n → Hypergraph α β) (M : Fin n → Fin n → Hypergraph α β),
      IsVitalPLinkage G L p →
      (∀ i : Fin n, G.IsSeparation (A i) (B i) ∧ separationOrder (A i) (B i) ≤ k) →
      (∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i) →
      (∀ i i' : Fin n, i < i' →
        separationOrder (A i) (B i) = separationOrder (A i') (B i') →
        (∀ j : Fin n, i < j → j < i' →
          separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
        IsLinkage (B i ∩ A i') (M i i') ∧
        (linkagePattern (M i i')).ncard = separationOrder (A i) (B i) ∧
        ∀ P ∈ linkagePattern (M i i'),
          ∃ u ∈ (A i ∩ B i).vertexSet, ∃ w ∈ (A i' ∩ B i').vertexSet, P = {u, w}) →
      ∃ i i' : Fin n, i < i' ∧
        separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
        (∀ j : Fin n, i < j → j < i' →
          separationOrder (A i) (B i) < separationOrder (A j) (B j)) ∧
        L ∩ B i ∩ A i' = M i i')
    (hlam' : ∀ {S' : Type w} [TopologicalSpace S'] (G' : Hypergraph α β)
      (Γ' : Drawing S') (Γ_sub' : Hypergraph α β) (ιV' : S' → α)
      (ιE' : Set S' → β) (F_star' : Fin 1 → Set S') (H' : Fin 1 → Hypergraph α β)
      (μ' : BoundaryUnit S' → Hypergraph α β) (L' : Hypergraph α β),
      GM06.IsClosedDiscSpace S' → G'.IsGraph →
      PresentationHasDepthLe G' Γ' Γ_sub' ιV' ιE' 1 F_star' H' μ' dd →
      IsExhaustiveLinkage G' Γ_sub' 1 H' L' → IsPLinkage G' L' (p + 2 * dd) →
      (sigmaJumps Γ' Γ_sub' ιV').encard ≤ lam')
    {j₁ j₂ : Fin r} (hb₁a₂ : b j₁ < a j₂) (hcov : ∀ j : Fin r, j = j₁ ∨ j = j₂) :
    (Set.ncard 𝒯) ≤ n * (2 * lam' + 1) := by
  have hspec := fun {J} (hJ : J ∈ 𝒯) => hW.jumpAngles_spec h_pres hJ
  have hint : ∀ (j : Fin r) (g h : ℝ), g < h → a j ≤ g → h ≤ b j →
      g ∈ cutPoints LO HI 𝒯 (a j) (b j) →
      (h ∈ cutPoints LO HI 𝒯 (a j) (b j) ∨ h = b j) →
      NoCross LO HI 𝒯 g h → (insideSet LO HI 𝒯 ⟨g, h, true⟩).ncard ≤ lam' := by
    intro j g h hgh hg hh hgP hhP hgh'
    have hPos : ∀ t, t ∈ cutPoints LO HI 𝒯 (a j) (b j) → t ∈ POS := by
      rintro t (rfl | ⟨P, hP, rfl⟩ | ⟨P, hP, rfl⟩)
      · exact ⟨hW.Icc_subset j ⟨le_rfl, hW.a_le_b j⟩, hW.a_mem j⟩
      · exact ⟨hW.jumpLo_mem h_pres hP.1, (hspec hP.1).2.2.2.1⟩
      · exact ⟨hW.jumpHi_mem h_pres hP.1, (hspec hP.1).2.2.2.2.1⟩
    have hhP' : h ∈ POS := by
      rcases hhP with hhP | rfl
      · exact hPos h hhP
      · exact ⟨hW.Icc_subset j ⟨hW.a_le_b j, le_rfl⟩, hW.b_mem j⟩
    exact ncard_insideSet_le_of_theorem_6_4 h_pres hC hW hK hdeg hD hG hL hpL hq hlam'
      ⟨hPos g hgP, hhP', hgh, hgh'⟩ j ⟨hg, hh⟩
  refine ncard_le_of_two_blocks (lo := LO) (hi := HI) (fun J hJ => (hspec hJ).2.1)
    (fun J hJ J' hJ' => hW.not_cross_of_mem_jumpSet h_pres hD hK hdeg hJ hJ')
    (jumpSet_finite hdeg) (hW.a_le_b j₁) hb₁a₂ (hW.a_le_b j₂)
    (fun J hJ => ?_) (fun J hJ => ?_) hn1 ?_ (hint j₁) (hint j₂)
  · obtain ⟨j, hj⟩ := hW.exists_support h_pres (hW.jumpLo_mem h_pres hJ) (hspec hJ).2.2.2.1
    rcases hcov j with rfl | rfl
    · exact Or.inl hj
    · exact Or.inr hj
  · obtain ⟨j, hj⟩ := hW.exists_support h_pres (hW.jumpHi_mem h_pres hJ) (hspec hJ).2.2.2.2.1
    rcases hcov j with rfl | rfl
    · exact Or.inl hj
    · exact Or.inr hj
  · have := ncard_crossSet_lt h_pres hC hW hK hdeg hD hG hL hpL hq hk hn hb₁a₂
    omega

end claims

end DiscCut
end GM21
end GraphMinor

namespace GraphMinor
namespace GM21

universe u v w

open Set GraphMinor.Surface GraphMinor.GM21.Cuts

/-- **Graph Minors XXI, (6.5)** (page 25 of the preprint): "*For all integers $p \ge 0$ and
$q \ge 1$ there exists $\lambda \ge 0$ such that, if $G$ has a presentation in a disc $\Sigma$ of
depth $\le q$ and defect 2, and there is an exhaustive vital $p$-linkage in $G$, then there are at
most $\lambda$ $\Sigma$-jumps.*"

Follows the paper's proof: choose $n$ from (2.6) for $(p, 2q)$ and $\lambda'$ from (6.4) for
$(p + 2q, q)$, and set $\lambda = n(2\lambda' + 1)$. -/
theorem theorem_6_5_proof (p q : ℕ) (hq : 1 ≤ q) :
    ∃ lam : ℕ, ∀ {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
      (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α)
      (ιE : Set S → β) (F_star : Fin 2 → Set S) (H : Fin 2 → Hypergraph α β)
      (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
      GM06.IsClosedDiscSpace S → G.IsGraph →
      PresentationHasDepthLe G Γ Γ_sub ιV ιE 2 F_star H μ q →
      IsExhaustiveLinkage G Γ_sub 2 H L → IsPLinkage G L p →
      (sigmaJumps Γ Γ_sub ιV).encard ≤ lam := by
  obtain ⟨n, hn2, hn⟩ := theorem_2_6_proof.{u, v} p (2 * q)
  obtain ⟨lam', hlam'⟩ := theorem_6_4_proof.{u, v, w} (p + 2 * q) q hq
  refine ⟨n * (2 * lam' + 1), ?_⟩
  intro S _ α β G Γ Γ_sub ιV ιE F_star H μ L hD hG hdepth hL hpL
  obtain ⟨qf, h_pres, hqf, -⟩ := hdepth
  have hC := DiscCut.bd_mem_cuffs hD
  have hK := IsExhaustiveLinkage.isLinkage h_pres hL
  have hdeg := IsExhaustiveLinkage.ncard_incidentEdges_eq_two h_pres hL
  have hT : (jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))).Finite := jumpSet_finite hdeg
  rw [sigmaJumps_eq_jumpSet h_pres.drawing_iso, ← hT.cast_ncard_eq]
  norm_cast
  obtain ⟨f, w₀, w₁, a, b, hW, -⟩ := DiscCut.exists_window h_pres hD (0 : Fin 2)
  rcases hW.lt_or_lt h_pres (by decide : (0 : Fin 2) ≠ 1) with h01 | h10
  · exact DiscCut.ncard_jumpSet_le_two_supports h_pres hC hW hK hdeg hD hG hL hpL
      (fun j => hqf j) le_rfl (by omega) (hn G L)
      (fun G' Γ' Γ_sub' ιV' ιE' F_star' H' μ' L' =>
        hlam' G' Γ' Γ_sub' ιV' ιE' F_star' H' μ' L')
      h01 (fun j => by fin_cases j <;> simp)
  · exact DiscCut.ncard_jumpSet_le_two_supports h_pres hC hW hK hdeg hD hG hL hpL
      (fun j => hqf j) le_rfl (by omega) (hn G L)
      (fun G' Γ' Γ_sub' ιV' ιE' F_star' H' μ' L' =>
        hlam' G' Γ' Γ_sub' ιV' ιE' F_star' H' μ' L')
      h10 (fun j => by fin_cases j <;> simp)

/-- **Graph Minors XXI, (6.6)** (page 27 of the preprint): "*For all integers $p \ge 0$ and
$q \ge 1$ there exists $\lambda \ge 0$ such that, if $G$ has a presentation in a disc $\Sigma$ of
depth $\le q$ and defect $3$, and there is an exhaustive vital $p$-linkage $G$, then there are at
most $\lambda$ $\Sigma$-jumps.*"

Follows the paper's proof: choose $\lambda'$ from (6.5) for $(p + 2q, q)$, set $\lambda = 3\lambda'$,
and cut $\Sigma$ into three closed discs $\Delta_1, \Delta_2, \Delta_3$ through a region $r_0$
incident with vertices in all three supports (`ThreeSupports.encard_sigmaJumps_le_three_of_region`). -/
theorem theorem_6_6_proof (p q : ℕ) (hq : 1 ≤ q) :
    ∃ lam : ℕ, ∀ {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
      (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α)
      (ιE : Set S → β) (F_star : Fin 3 → Set S) (H : Fin 3 → Hypergraph α β)
      (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
      GM06.IsClosedDiscSpace S → G.IsGraph →
      PresentationHasDepthLe G Γ Γ_sub ιV ιE 3 F_star H μ q →
      IsExhaustiveLinkage G Γ_sub 3 H L → IsPLinkage G L p →
      (sigmaJumps Γ Γ_sub ιV).encard ≤ lam := by
  obtain ⟨lam', hlam'⟩ := theorem_6_5_proof.{u, v, w} (p + 2 * q) q hq
  refine ⟨3 * lam', ?_⟩
  intro S _ α β G Γ Γ_sub ιV ιE F_star H μ L hD hG hdepth hL hpL
  obtain ⟨qf, h_pres, hqf, -⟩ := hdepth
  have : T2Space S := h_pres.is_surface.2.1
  obtain ⟨f, w₀, w₁, a, b, hW, -⟩ := DiscCut.exists_window h_pres hD (0 : Fin 3)
  have h := ThreeSupports.encard_sigmaJumps_le_three_of_region hD h_pres hG (fun j => hqf j)
    hL hpL hW (fun G' Γ' Γ_sub' ιV' ιE' F' H' μ' L' =>
      hlam' G' Γ' Γ_sub' ιV' ιE' F' H' μ' L')
  exact h.trans_eq (Nat.cast_mul 3 lam').symm

/-- **Graph Minors XXI, (6.7)** (page 27 of the preprint): "*For all integers $p, r \ge 0$
and $q \ge 1$ there exists $\lambda \ge 0$ such that, if $G$ has a presentation in a disc
$\Sigma$ of depth $\le q$ and defect $\le r$, and there is an exhaustive vital $p$-linkage in
$G$, then there are at most $\lambda$ $\Sigma$-jumps.*"

Follows the paper's proof by induction on $r$: for $r \le 3$ the result follows from (6.4), (6.5)
and (6.6); for $r \ge 4$, set $\lambda = 2\lambda'$ where $\lambda'$ is from the induction
hypothesis for $(p + 2q, r - 1, q)$, and cut $\Sigma$ along a proper line in a region incident with
three supports (`ThreeSupports.encard_sigmaJumps_le_two_of_region_three`). -/
theorem theorem_6_7_proof (p r q : ℕ) (hq : 1 ≤ q) :
    ∃ lam : ℕ, ∀ {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v} {r' : ℕ}
      (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α)
      (ιE : Set S → β) (F_star : Fin r' → Set S) (H : Fin r' → Hypergraph α β)
      (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
      r' ≤ r → GM06.IsClosedDiscSpace S → G.IsGraph →
      PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q →
      IsExhaustiveLinkage G Γ_sub r' H L → IsPLinkage G L p →
      (sigmaJumps Γ Γ_sub ιV).encard ≤ lam := by
  induction r generalizing p with
  | zero =>
    refine ⟨0, ?_⟩
    intro S _ α β r' G Γ Γ_sub ιV ιE F_star H μ L hr hD _ hdepth _ _
    obtain ⟨qf, h_pres, -⟩ := hdepth
    have hC := DiscCut.bd_mem_cuffs hD
    obtain ⟨u, hu⟩ := nonempty_of_ncard_ne_zero
      (by have := h_pres.cuff_vertices_ge_two (bd S) hC; omega : (Γ.V ∩ bd S).ncard ≠ 0)
    have h := h_pres.bd_vertices_covered hu
    rw [mem_iUnion] at h
    obtain ⟨j, -⟩ := h
    have := j.2
    omega
  | succ r_prev ih =>
    rcases le_or_gt (r_prev + 1) 3 with hr3 | hr4
    · -- Base cases `r ≤ 3`: use (6.4), (6.5) and (6.6).
      obtain ⟨lam₁, hlam₁⟩ := theorem_6_4_proof.{u, v, w} p q hq
      obtain ⟨lam₂, hlam₂⟩ := theorem_6_5_proof.{u, v, w} p q hq
      obtain ⟨lam₃, hlam₃⟩ := theorem_6_6_proof.{u, v, w} p q hq
      refine ⟨max lam₁ (max lam₂ lam₃), ?_⟩
      intro S _ α β r' G Γ Γ_sub ιV ιE F_star H μ L hr hD hG hdepth hL hpL
      have hr0 : 0 < r' := by
        obtain ⟨qf, h_pres, -⟩ := hdepth
        have hC := DiscCut.bd_mem_cuffs hD
        obtain ⟨u, hu⟩ := nonempty_of_ncard_ne_zero
          (by have := h_pres.cuff_vertices_ge_two (bd S) hC; omega : (Γ.V ∩ bd S).ncard ≠ 0)
        have h := h_pres.bd_vertices_covered hu
        rw [mem_iUnion] at h
        obtain ⟨j, -⟩ := h
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) j.2
      rcases (by omega : r' = 1 ∨ r' = 2 ∨ r' = 3) with rfl | rfl | rfl
      · exact (hlam₁ G Γ Γ_sub ιV ιE F_star H μ L hD hG hdepth hL hpL).trans
          (Nat.cast_le.mpr (le_max_left _ _))
      · exact (hlam₂ G Γ Γ_sub ιV ιE F_star H μ L hD hG hdepth hL hpL).trans
          (Nat.cast_le.mpr ((le_max_left _ _).trans (le_max_right _ _)))
      · exact (hlam₃ G Γ Γ_sub ιV ιE F_star H μ L hD hG hdepth hL hpL).trans
          (Nat.cast_le.mpr ((le_max_right _ _).trans (le_max_right _ _)))
    · -- Inductive step `4 ≤ r_prev + 1`: set `lam = 2 * lam'`.
      obtain ⟨lam', hlam'⟩ := ih (p + 2 * q)
      refine ⟨2 * lam', ?_⟩
      intro S _ α β r' G Γ Γ_sub ιV ιE F_star H μ L hr hD hG hdepth hL hpL
      rcases (by omega : r' ≤ r_prev ∨ r' = r_prev + 1) with hr' | rfl
      · have hpL' : IsPLinkage G L (p + 2 * q) :=
          ⟨hpL.1, hpL.2.trans (Nat.le_add_right p (2 * q))⟩
        exact (hlam' G Γ Γ_sub ιV ιE F_star H μ L hr' hD hG hdepth hL hpL').trans
          (Nat.cast_le.mpr (by omega))
      · obtain ⟨qf, h_pres, hqf, -⟩ := hdepth
        have : T2Space S := h_pres.is_surface.2.1
        obtain ⟨f, w₀, w₁, a, b, hW, -⟩ := DiscCut.exists_window h_pres hD ⟨0, by omega⟩
        have h := ThreeSupports.encard_sigmaJumps_le_two_of_region_three hD h_pres hG
          (fun j => hqf j) hL hpL hW (by omega : 4 ≤ r_prev + 1)
          (fun G' Γ' Γ_sub' ιV' ιE' F' H' μ' L' hlt =>
            hlam' G' Γ' Γ_sub' ιV' ιE' F' H' μ' L' (Nat.lt_succ_iff.mp hlt))
        exact h.trans_eq (by rw [← two_mul]; exact (Nat.cast_mul 2 lam').symm)

end GM21
end GraphMinor
