module

public import GraphMinor.GM21.Section6DiscSep
public import GraphMinor.GM21.Section2
import GraphMinor.GM21.Section6
import GraphMinor.GM21.Section6PathLinkage
import GraphMinor.GM21.Section6Exhaustive
import GraphMinor.GM21.LinkageLemmas
import GraphMinor.GM06.DiscRegions
import GraphMinor.GM10.TangleLemmas
import GraphMinor.GM21.Section6FourPaths

/-!
# Graph Minors XXI, (6.4): a disc with defect 1

"**6.4** *For all integers $p \ge 0$ and $q \ge 1$ there exists $\lambda \ge 0$ such that, if $G$
has a presentation in a disc $\Sigma$ of depth $\le q$ and defect 1, and there is an exhaustive
vital $p$-linkage in $G$, then there are at most $\lambda$ $\Sigma$-jumps.*" (page 24 of the
preprint)

We follow the paper's proof. Choose `n` by (2.6) with `k = 2q`, and `λ = n^n`. Good lines `F`
and their discs `Δ(F)` are described by cuts (`Section6Cuts`, `Section6DiscSep`).

Then (6.4) is `theorem_6_4`.

- Claims (1) and (2) are `isSeparation_cut` and `cut_nested` (`Section6DiscSep`).
- Claim (3), "If $|X(F)| = |X(F')|$ there are $|X(F)|$ mutually vertex-disjoint paths of
  $B(F) \cap A(F')$ between $X(F)$ and $X(F')$, each using no edge of $\Gamma$", is
  `exists_transfer_linkage`; it comes from (6.1)(iii) and (6.2), as in the paper.
- Claim (4), that in a sequence of `n` nested good lines some step loses no edge of `Γ`, is
  `not_isStrictChain`; it comes from (2.6), as in the paper.
- The last step: the regions of `Γ` form a tree `T` when two regions are joined if they touch
  along an edge of `Γ`, and the edges of `T` are in one-to-one correspondence with the jumps
  (`RegionTree.ncard_jumpSet_eq_ncard_edgeSet`). Every vertex of `T` has degree at most `n`, and
  "every path of $T$ has at most $n$ vertices. Hence $|E(T)| \le n^n = \lambda$" is
  `RegionTree.ncard_jumpSet_le`. As the paper says it, the path bound is shown only for paths
  that start at the region outside `F*`. This is still enough for the count (see the correction
  to the proof of (6.4) in `corrections/GM21.md`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace DiscCut

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM21.Supports
open GraphMinor.GM21.Cuts

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- A subgraph of two graphs is a subgraph of their intersection. -/
theorem le_inter' {M A B : Hypergraph α β} (hA : M ≤ A) (hB : M ≤ B) : M ≤ A ∩ B where
  vertexSet_subset := subset_inter hA.vertexSet_subset hB.vertexSet_subset
  edgeSet_subset := subset_inter hA.edgeSet_subset hB.edgeSet_subset
  ends_eq e he := by
    ext x
    simp only [Hypergraph.ends, mem_ofPred_eq]
    show A.Inc e x ∧ B.Inc e x ↔ M.Inc e x
    rw [← GM10.inc_iff_of_le hA he, ← GM10.inc_iff_of_le hB he, and_self]

/-- Two vertex-disjoint subgraphs of a graph have no common edge. -/
theorem edgeSet_disjoint_of_vertexSet_disjoint {G A B : Hypergraph α β} (hG : G.IsGraph)
    (hA : A ≤ G) (hB : B ≤ G) (hAB : Disjoint A.vertexSet B.vertexSet) :
    Disjoint A.edgeSet B.edgeSet := by
  rw [Set.disjoint_left]
  intro e heA heB
  obtain ⟨x, hx⟩ := (hG e (hA.edgeSet_subset heA)).1
  have hxA : A.Inc e x := (GM10.inc_iff_of_le hA heA).2 hx
  have hxB : B.Inc e x := (GM10.inc_iff_of_le hB heB).2 hx
  exact Set.disjoint_left.mp hAB (A.vertex_mem_of_inc hxA) (B.vertex_mem_of_inc hxB)

private theorem nonempty_of_mem_drawingSpaces'' {Γ : Drawing S} {s : Set S}
    (hs : s ∈ drawingSpaces Γ) : s.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hs
  exact ⟨x, mem_connectedComponentIn hx⟩

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
/-- `μ` of a part of `F_j*` has no edge of `μ` of a part of another support. -/
theorem supportGraph_edgeSet_disjoint_of_ne (hG : G.IsGraph) {j j' : Fin r} (hjj : j ≠ j')
    {I I' : Set S} (hI : I ⊆ F_star j) (hI' : I' ⊆ F_star j') :
    Disjoint (supportGraph G Γ μ I).edgeSet (supportGraph G Γ μ I').edgeSet := by
  refine edgeSet_disjoint_of_vertexSet_disjoint hG (supportGraph_le h_pres j hI)
    (supportGraph_le h_pres j' hI') ?_
  exact (h_pres.v1_disjoint hjj).mono
    (supportGraph_le_H h_pres hI).vertexSet_subset (supportGraph_le_H h_pres hI').vertexSet_subset

/-- `|X(c)| ≤ 2 q` when every support has depth at most `q`. -/
theorem ncard_cutX_le {c : Cut} (hc : Admissible LO HI 𝒯 POS c) {d : ℕ} (hd : ∀ j, q j ≤ d) :
    (cutX μ f c).ncard ≤ 2 * d := by
  have hb := admissible_bounds' hc
  obtain ⟨j, -, hx⟩ := exists_piece_of_pos h_pres hW ⟨hb.1, hb.2.1.le.trans hb.2.2.1⟩
    hb.2.2.2.1 le_rfl le_rfl
  obtain ⟨j', -, hy⟩ := exists_piece_of_pos h_pres hW ⟨hb.1.trans hb.2.1.le, hb.2.2.1⟩
    hb.2.2.2.2 le_rfl le_rfl
  have hxF : cp c.x ∈ Γ.V ∩ F_star j := ⟨hx.1, piece_subset hW j _ _ hx.2⟩
  have hyF : cp c.y ∈ Γ.V ∩ F_star j' := ⟨hy.1, piece_subset hW j' _ _ hy.2⟩
  calc (cutX μ f c).ncard
      ≤ (μ (.vertex (cp c.x))).vertexSet.ncard + (μ (.vertex (cp c.y))).vertexSet.ncard :=
        ncard_union_le _ _
    _ = q j + q j' := by
        rw [(h_pres.μ_vertex_sub j _ hxF).2.2.1, (h_pres.μ_vertex_sub j' _ hyF).2.2.1]
    _ ≤ 2 * d := by linarith [hd j, hd j']

omit h_pres in
/-- The part of `F_j*` between the angles `x ≤ y` of two vertices lies in `B(c)` when
`c.x ≤ x` and `y ≤ c.y`. -/
theorem supportGraph_le_cutB (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) {c : Cut}
    (j : Fin r) {x y : ℝ} (hx : max (a j) c.x ≤ x)
    (hy : y ≤ min (b j) c.y) : supportGraph G Γ μ (cp '' Icc x y) ≤ BB c := by
  have hsub : cp '' Icc x y ⊆ piece f a b j c.x c.y := image_mono (Icc_subset_Icc hx hy)
  have hmI := supportGraph_mono h_pres j (piece_subset hW j c.x c.y) hsub
  have hle := supportGraph_le h_pres j ((hsub.trans (piece_subset hW j c.x c.y)))
  apply le_subOn hle
  · exact fun v hv => Or.inr (mem_iUnion.2 ⟨j, hmI.vertexSet_subset hv⟩)
  · exact fun e he => Or.inr (mem_iUnion.2 ⟨j, hmI.edgeSet_subset he⟩)

include hC in
/-- The part of `F_j*` between the angles `x ≤ y` of two vertices lies in `A(c)` when `[x, y]`
is outside the cut `c` (`y ≤ c.x` or `c.y ≤ x`). -/
theorem supportGraph_le_cutA (hG : G.IsGraph) {c : Cut} (hc : Admissible LO HI 𝒯 POS c)
    (j : Fin r) {x y : ℝ} (hxj : a j ≤ x) (hxy : x ≤ y) (hyj : y ≤ b j) (hxV : cp x ∈ Γ.V)
    (hyV : cp y ∈ Γ.V) (hout : y ≤ c.x ∨ c.y ≤ x) :
    supportGraph G Γ μ (cp '' Icc x y) ≤ AA c := by
  have hb := admissible_bounds' hc
  have hsub : cp '' Icc x y ⊆ F_star j := by
    rw [hW.F_eq j]
    exact image_mono (Icc_subset_Icc hxj hyj)
  have hle := supportGraph_le h_pres j hsub
  have hlt : b j < a j + 2 * Real.pi := by linarith [hW.lt_add, hW.le_a j, hW.b_le j]
  have haj : cp (a j) ∈ Γ.V ∩ bd S := ⟨hW.a_mem j, GM17.cuffPoint_mem f _⟩
  apply le_subOn hle
  · intro v hv
    refine ⟨hle.vertexSet_subset hv, fun ⟨hvW, hvX⟩ => hvX ?_⟩
    have hvH : v ∈ (H j).vertexSet := (supportGraph_le_H h_pres hsub).vertexSet_subset hv
    obtain ⟨p, p', hp, hpp, hp', hvp⟩ := exists_part_of_mem_cutW h_pres hW hvW hvH
    exact mem_cutX_of_outside h_pres hC hW hc hxj hxy hyj hout hp hpp hp' hv hvp
  · intro e he
    refine ⟨hle.edgeSet_subset he, ?_⟩
    rintro (hej | hec)
    · rw [mem_iUnion₂] at hej
      obtain ⟨J, hJ, heJ⟩ := hej
      exact Set.disjoint_left.mp (supportGraph_edgeSet_disjoint h_pres j hsub) he
        (hJ.1.1.edgeSet_subset heJ)
    · rw [mem_iUnion] at hec
      obtain ⟨j', hec⟩ := hec
      by_cases hjj : j = j'
      · subst hjj
        -- The two parts of `F_j*` meet in at most the vertex at `c.x` or `c.y`, by (V4).
        have hP : cp (max (a j) c.x) ∈ Γ.V := by
          rcases max_cases (a j) c.x with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
          exacts [hW.a_mem j, hb.2.2.2.1]
        rcases le_or_gt (max (a j) c.x) (min (b j) c.y) with hle' | hgt
        · rcases hout with h | h
          · have hyP : y ≤ max (a j) c.x := h.trans (le_max_right _ _)
            have hmono := supportGraph_mono (G := G) (μ := μ) h_pres j
              (image_Icc_subset j f (hW.F_eq j) (hxj.trans hxy) (min_le_left _ _))
              (image_mono (Icc_subset_Icc hyP le_rfl) :
                piece f a b j c.x c.y ⊆ cp '' Icc y (min (b j) c.y))
            exact Set.disjoint_left.mp (supportGraph_edgeSet_disjoint_of_angles h_pres j hC f hlt
              haj (hW.b_mem j) (hW.F_eq j) hxj hxy (hyP.trans hle') (min_le_left _ _) hxV hyV)
              he (hmono.edgeSet_subset hec)
          · have hPx : min (b j) c.y ≤ x := (min_le_right _ _).trans h
            have hmono := supportGraph_mono (G := G) (μ := μ) h_pres j
              (image_Icc_subset j f (hW.F_eq j) (le_max_left _ _) (hxy.trans hyj))
              (image_mono (Icc_subset_Icc le_rfl hPx) :
                piece f a b j c.x c.y ⊆ cp '' Icc (max (a j) c.x) x)
            exact Set.disjoint_left.mp (supportGraph_edgeSet_disjoint_of_angles h_pres j hC f hlt
              haj (hW.b_mem j) (hW.F_eq j) (le_max_left _ _) (hle'.trans hPx) hxy hyj hP hxV)
              (hmono.edgeSet_subset hec) he
        · have hempty : piece f a b j c.x c.y = ∅ := by
            rw [piece, Icc_eq_empty (not_le.2 hgt), image_empty]
          rw [hempty] at hec
          obtain ⟨s, hs, hs0, -⟩ := exists_space_of_mem_edgeSet h_pres j (empty_subset _) hec
          obtain ⟨z, hz⟩ := nonempty_of_mem_drawingSpaces'' hs
          exact hs0 hz
      · exact Set.disjoint_left.mp (supportGraph_edgeSet_disjoint_of_ne h_pres hG hjj hsub
          (piece_subset hW j' c.x c.y)) he hec

include hC hK hdeg

/-- **Claim (3) of the proof of (6.4)**: if `c'` is nested in `c`, both lie in one support
`F_j*`, and `|X(c)| = |X(c')|`, there is a linkage in `B(c) ∩ A(c')` with `|X(c)|` components,
each with one end in `X(c)` and the other in `X(c')`, which uses no edge of `Γ`. As in the paper,
the paths come from (6.2) and (6.1)(iii). -/
theorem exists_transfer_linkage (hG : G.IsGraph) {j : Fin r} {c c' : Cut}
    (hc : Admissible LO HI 𝒯 POS c) (hc' : Admissible LO HI 𝒯 POS c')
    (hn : Nested LO HI 𝒯 c c') (hcj : a j ≤ c.x ∧ c.y ≤ b j)
    (hord : (cutX μ f c).ncard = (cutX μ f c').ncard) :
    ∃ M : Hypergraph α β,
      IsLinkage (BB c ∩ AA c') M ∧
      (linkagePattern M).ncard = (cutX μ f c).ncard ∧
      (∀ P ∈ linkagePattern M, ∃ u ∈ (AA c ∩ BB c).vertexSet,
        ∃ w ∈ (AA c' ∩ BB c').vertexSet, P = {u, w}) ∧
      Disjoint M.edgeSet Γ_sub.edgeSet := by
  have hS := h_pres.is_surface
  have hb := admissible_bounds' hc
  have hb' := admissible_bounds' hc'
  have hlt : b j < a j + 2 * Real.pi := by linarith [hW.lt_add, hW.le_a j, hW.b_le j]
  have hF := hW.F_eq j
  obtain ⟨hx, hxx', hx'y', hy'y, hy⟩ : a j ≤ c.x ∧ c.x ≤ c'.x ∧ c'.x < c'.y ∧ c'.y ≤ c.y ∧
      c.y ≤ b j := ⟨hcj.1, hn.1, hb'.2.1, hn.2.1, hcj.2⟩
  have hxV := hb.2.2.2.1
  have hyV := hb.2.2.2.2
  have hx'V := hb'.2.2.2.1
  have hy'V := hb'.2.2.2.2
  have hx' : c'.x ≤ b j := (hx'y'.le.trans hy'y).trans hy
  -- The supports `I`, `I'` and `J` of (6.1)(iii).
  have hIsub := image_Icc_subset j f hF hx hx'
  have hI'sub := image_Icc_subset j f hF (hx.trans (hxx'.trans hx'y'.le)) hy
  have hJsub := image_Icc_subset j f hF (hx.trans hxx') hy
  have hIends := supportHasEnds_cuffPoint_Icc hS hC f hx hxx' hx' hlt hxV hx'V
  have hI'ends := supportHasEnds_cuffPoint_Icc hS hC f (hx.trans (hxx'.trans hx'y'.le)) hy'y hy
    hlt hy'V hyV
  have hJends := supportHasEnds_cuffPoint_Icc hS hC f (hx.trans hxx') (hx'y'.le.trans hy'y) hy
    hlt hx'V hyV
  have hIJ := (cuffPoint_Icc_split f hx hxx' (hx'y'.le.trans hy'y) hy hlt).2
  have hI'J : cp '' Icc c'.y c.y ⊆ cp '' Icc c'.x c.y := image_mono (Icc_subset_Icc hx'y'.le le_rfl)
  have hk₂ : ((μ (.vertex (cp c'.y))).vertexSet ∪ (μ (.vertex (cp c'.x))).vertexSet).ncard =
      (cutX μ f c).ncard := by
    rw [Set.union_comm]
    exact hord.symm
  have hpaths := theorem_6_1_iii_exists h_pres j hIsub hIends hI'sub hI'ends hJsub hJends hIJ hI'J rfl
    hk₂ (theorem_6_2_proof h_pres j hIsub hIends) (theorem_6_2_proof h_pres j hI'sub hI'ends)
  -- The graph `K₀ = μ(I) ∪ μ(I')` in which the paths lie.
  have hμI := supportGraph_le h_pres j hIsub
  have hμI' := supportGraph_le h_pres j hI'sub
  have hK₀G := GM10.union_le hμI hμI'
  have hK₀g := isGraph_of_le hK₀G hG
  have hxI : cp c.x ∈ Γ.V ∩ cp '' Icc c.x c'.x := ⟨hxV, c.x, ⟨le_rfl, hxx'⟩, rfl⟩
  have hyI' : cp c.y ∈ Γ.V ∩ cp '' Icc c'.y c.y := ⟨hyV, c.y, ⟨hy'y, le_rfl⟩, rfl⟩
  have hX : cutX μ f c ⊆ (supportGraph G Γ μ (cp '' Icc c.x c'.x) ∪
      supportGraph G Γ μ (cp '' Icc c'.y c.y)).vertexSet := by
    rintro v (hv | hv)
    · exact Or.inl ((μ_vertex_le_supportGraph_of_subset h_pres j hIsub hxI).vertexSet_subset hv)
    · exact Or.inr ((μ_vertex_le_supportGraph_of_subset h_pres j hI'sub hyI').vertexSet_subset hv)
  obtain ⟨M, hML, hMcard, hMP⟩ := exists_linkage_of_hasDisjointPaths hK₀g hX hpaths
  -- `K₀ ≤ B(c) ∩ A(c')`.
  have hK₀B : supportGraph G Γ μ (cp '' Icc c.x c'.x) ∪ supportGraph G Γ μ (cp '' Icc c'.y c.y) ≤
      BB c :=
    GM10.union_le
      (supportGraph_le_cutB hW h_pres j (max_le hx le_rfl) (le_min hx' (hx'y'.le.trans hy'y)))
      (supportGraph_le_cutB hW h_pres j (max_le (hx.trans (hxx'.trans hx'y'.le))
        (hxx'.trans hx'y'.le)) (le_min hy le_rfl))
  have hK₀A : supportGraph G Γ μ (cp '' Icc c.x c'.x) ∪ supportGraph G Γ μ (cp '' Icc c'.y c.y) ≤
      AA c' :=
    GM10.union_le (supportGraph_le_cutA h_pres hC hW hG hc' j hx hxx' hx' hxV hx'V (Or.inl le_rfl))
      (supportGraph_le_cutA h_pres hC hW hG hc' j (hx.trans (hxx'.trans hx'y'.le)) hy'y hy hy'V
        hyV (Or.inr le_rfl))
  have hK₀ := le_inter' hK₀B hK₀A
  have hsep := (isSeparation_cut h_pres hC hW hK hdeg hc).2
  have hsep' := (isSeparation_cut h_pres hC hW hK hdeg hc').2
  refine ⟨M, ⟨hML.1.trans hK₀, hML.2⟩, hMcard, ?_, ?_⟩
  · intro P hP
    obtain ⟨u, hu, w, hw, rfl⟩ := hMP P hP
    refine ⟨u, by rw [hsep]; exact hu, w, ?_, rfl⟩
    rw [hsep', cutX]
    exact hw
  · rw [Set.disjoint_left]
    intro e he heΓ
    rcases hML.1.edgeSet_subset he with he' | he'
    · exact Set.disjoint_left.mp (supportGraph_edgeSet_disjoint h_pres j hIsub) he' heΓ
    · exact Set.disjoint_left.mp (supportGraph_edgeSet_disjoint h_pres j hI'sub) he' heΓ

/-- **Claim (4) of the proof of (6.4)**: "If $F_1, \ldots, F_n$ is a sequence of good lines such
that $\Delta(F_{i+1}) \subseteq \Delta(F_i)$ for $1 \le i < n$, there exists $i$ with
$1 \le i < n$ such that every edge of $\Gamma \cap \Delta(F_i)$ is an edge of
$\Gamma \cap \Delta(F_{i+1})$." In terms of cuts in one support `F_j*`: there is no strict chain
of `n` cuts, where `n` has the property of (2.6) for `p` and some `k ≥ 2 d`, `d` a bound of the
depth (hypothesis `hn`). As in the paper, (2.6) gives `i < i'` with `L ∩ B_i ∩ A_{i'} = M_{ii'}`,
which uses no edge of `Γ`, while a jump inside the `i`th cut and not inside the `(i+1)`th gives an
edge of `Γ ∩ B_i ∩ A_{i'}` in `L`. -/
theorem not_isStrictChain (hG : G.IsGraph) {L : Hypergraph α β} {p k n dd : ℕ}
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
    (j : Fin r) (d : Fin n → Cut) (hdj : ∀ i, a j ≤ (d i).x ∧ (d i).y ≤ b j) :
    ¬ IsStrictChain LO HI 𝒯 POS d := by
  classical
  intro hd
  set A : Fin n → Hypergraph α β := fun i => AA (d i) with hA_def
  set B : Fin n → Hypergraph α β := fun i => BB (d i) with hB_def
  have hsep : ∀ i, G.IsSeparation (A i) (B i) ∧ (A i ∩ B i).vertexSet = cutX μ f (d i) :=
    fun i => isSeparation_cut h_pres hC hW hK hdeg (hd.1 i)
  have hord : ∀ i, separationOrder (A i) (B i) = (cutX μ f (d i)).ncard := fun i => by
    unfold separationOrder
    rw [(hsep i).2]
  let Pm : Fin n → Fin n → Hypergraph α β → Prop := fun i i' M =>
    IsLinkage (B i ∩ A i') M ∧ (linkagePattern M).ncard = separationOrder (A i) (B i) ∧
      (∀ P ∈ linkagePattern M,
        ∃ u ∈ (A i ∩ B i).vertexSet, ∃ w ∈ (A i' ∩ B i').vertexSet, P = {u, w}) ∧
      Disjoint M.edgeSet Γ_sub.edgeSet
  let M : Fin n → Fin n → Hypergraph α β := fun i i' =>
    if h : ∃ M, Pm i i' M then h.choose else G
  have hM : ∀ i i', i < i' → separationOrder (A i) (B i) = separationOrder (A i') (B i') →
      Pm i i' (M i i') := by
    intro i i' hii' heq
    have hex : ∃ M, Pm i i' M := by
      obtain ⟨M₀, h₁, h₂, h₃, h₄⟩ := exists_transfer_linkage h_pres hC hW hK hdeg hG (hd.1 i)
        (hd.1 i') (hd.2.1 i i' hii') (hdj i) (by rw [← hord, ← hord]; exact heq)
      exact ⟨M₀, h₁, by rw [hord]; exact h₂, h₃, h₄⟩
    show Pm i i' (if h : ∃ M, Pm i i' M then h.choose else G)
    rw [dite_eq_left hex]
    exact hex.choose_spec
  have hordk : ∀ i, separationOrder (A i) (B i) ≤ k := fun i => by
    rw [hord]
    exact (ncard_cutX_le h_pres hW (hd.1 i) hq).trans hk
  obtain ⟨i, i', hii', heq, -, hLM⟩ := hn A B M ⟨hL.1, hpL⟩ (fun i => ⟨(hsep i).1, hordk i⟩)
    (fun i j hij => cut_nested h_pres hC hW hK hdeg (hd.1 i) (hd.1 j) (hd.2.1 i j hij))
    (fun i i' h heq _ => ⟨(hM i i' h heq).1, (hM i i' h heq).2.1, (hM i i' h heq).2.2.1⟩)
  -- The step from `i` to `i + 1` loses a jump `J`, which is then not inside the `i'`th cut.
  have hi1 : i.1 + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt hii') i'.2
  obtain ⟨J, hJi, hJn⟩ := not_subset.1 (hd.2.2 i hi1)
  have hJi' : J ∉ insideSet LO HI 𝒯 (d i') := by
    intro h
    have hle' : i.1 + 1 ≤ i'.1 := hii'
    rcases eq_or_lt_of_le hle' with h' | h'
    · have : (⟨i.1 + 1, hi1⟩ : Fin n) = i' := Fin.ext h'
      rw [this] at hJn
      exact hJn h
    · exact hJn ((hd.2.1 ⟨i.1 + 1, hi1⟩ i' h').2.2 h)
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
  exact Set.disjoint_left.mp (hM i i' hii' heq).2.2.2 heM heΓ

end claims

end DiscCut

universe u v w

open Set GraphMinor.Surface GraphMinor.GM21.Cuts

/-- **Graph Minors XXI, (6.4)** (page 24 of the preprint): "*For all integers $p \ge 0$ and
$q \ge 1$ there exists $\lambda \ge 0$ such that, if $G$ has a presentation in a disc $\Sigma$ of
depth $\le q$ and defect 1, and there is an exhaustive vital $p$-linkage in $G$, then there are at
most $\lambda$ $\Sigma$-jumps.*"

A disc is a space homeomorphic to the closed unit disc (`GM06.IsClosedDiscSpace`). As in the paper,
`n` comes from (2.6) with `k = 2q`, and `λ = n^n`. Claim (4) (`DiscCut.not_isStrictChain`) says that
there is no strict chain of `n` cuts, and the tree of regions gives at most `n^n` jumps
(`RegionTree.ncard_jumpSet_le`). -/
theorem theorem_6_4_proof (p q : ℕ) (_hq : 1 ≤ q) :
    ∃ lam : ℕ, ∀ {S : Type w} [TopologicalSpace S] {α : Type u} {β : Type v}
      (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α)
      (ιE : Set S → β) (F_star : Fin 1 → Set S) (H : Fin 1 → Hypergraph α β)
      (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
      GM06.IsClosedDiscSpace S → G.IsGraph →
      PresentationHasDepthLe G Γ Γ_sub ιV ιE 1 F_star H μ q →
      IsExhaustiveLinkage G Γ_sub 1 H L → IsPLinkage G L p →
      (sigmaJumps Γ Γ_sub ιV).encard ≤ lam := by
  obtain ⟨n, hn2, hn⟩ := theorem_2_6_proof.{u, v} p (2 * q)
  refine ⟨n ^ n, ?_⟩
  intro S _ α β G Γ Γ_sub ιV ιE F_star H μ L hD hG hdepth hL hpL
  obtain ⟨qf, h_pres, hqf, -⟩ := hdepth
  obtain ⟨f, w₀, w₁, a, b, hW, -⟩ := DiscCut.exists_window h_pres hD 0
  have hC := DiscCut.bd_mem_cuffs hD
  have hK := IsExhaustiveLinkage.isLinkage h_pres hL
  have hdeg := IsExhaustiveLinkage.ncard_incidentEdges_eq_two h_pres hL
  have hT : (jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S))).Finite := jumpSet_finite hdeg
  rw [sigmaJumps_eq_jumpSet h_pres.drawing_iso, ← hT.cast_ncard_eq]
  norm_cast
  -- Every vertex of `Γ` in `bd(Σ)` lies in `F* = [a 0, b 0]`.
  have hin : ∀ {t : ℝ}, t ∈ Icc w₀ w₁ → GM19.cuffPoint f t ∈ Γ.V → t ∈ Icc (a 0) (b 0) := by
    intro t ht htV
    obtain ⟨j, hj⟩ := hW.exists_support h_pres ht htV
    rwa [Fin.fin_one_eq_zero j] at hj
  refine RegionTree.ncard_jumpSet_le h_pres hW hK hdeg hD (by omega) fun d hd => ?_
  exact DiscCut.not_isStrictChain h_pres hC hW hK hdeg hG hL hpL (fun j => hqf j) le_rfl (hn G L)
    0 d (fun i => ⟨(hin (hd.1 i).1.1 (hd.1 i).1.2).1, (hin (hd.1 i).2.1.1 (hd.1 i).2.1.2).2⟩) hd

end GM21
end GraphMinor
