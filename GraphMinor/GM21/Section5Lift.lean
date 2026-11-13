module

public import GraphMinor.GM21.Section5Puncture
public import GraphMinor.GM19.PullLift
public import GraphMinor.GM19.ThinPainting
public import GraphMinor.GM11.Theorem61
public import GraphMinor.GM12.Section3PuncturedSurface
public import GraphMinor.GM12.Section3PuncturedCuffs
public import GraphMinor.GM12.Section3PuncturedBoundary
public import GraphMinor.GM12.Section3PuncturedModel
public import GraphMinor.GM12.Section3SubspaceDrawing
public import GraphMinor.GM12.Section4MetricExistence
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Graph Minors XXI, Section 5: Lifting Drawings Across Cuts and Claims (4)–(9), (11) of `(5.2)`

Formalizes the combinatorial and topological reductions for `(5.2)` (pages 18–21 of the preprint) of
N. Robertson and P. D. Seymour, *Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616:

1. Multi-step vertex splitting (`ObtainedBySplittingLe`, `ObtainedBySplittingOutsideLe`) and
   loop deletion (`isTangle_deleteLoop`, `isVitalLinkage_deleteLoop`).
2. Claims (4), (5), and (6) (`claim_5_2_4`, `claim_5_2_5`, `claim_5_2_6`), together with their
   drawing-transport specializations (`apply_claim_5_2_5_of_drawing`,
   `apply_claim_5_2_6_of_drawing`).
3. Zero-split subspace drawing restriction (`exists_subspace_drawing_of_closed`) and lifting a
   loopless drawing across `IsCutting ψ F` with at most `|F ∩ V(B)|` vertex splits
   (`exists_lifted_drawing_of_isCutting`).
4. Claim (7) (`claim_5_2_7`) and Claim (8) (`claim_5_2_8`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function Hypergraph
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM12 GraphMinor.GM17 GraphMinor.GM19

universe u v w

/-! ## 1. Multi-step vertex splitting (`ObtainedBySplittingLe`) -/

section MultiSplit

variable {α : Type u} {β : Type v}

/-- Splitting a vertex preserves `IsGraph`. -/
theorem isGraph_of_isVertexSplit {G G' : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hG : G.IsGraph) :
    G'.IsGraph := by
  intro e heG'
  have heG : e ∈ G.edgeSet := hs.edgeSet_eq ▸ heG'
  have hcard : (G'.ends e).ncard = (G.ends e).ncard := isVertexSplit_ends_ncard_eq hs e
  obtain ⟨hne, hle2⟩ := hG e heG
  have hpos : 0 < (G.ends e).ncard :=
    (ncard_pos (G.vertexSet_finite.subset fun _ hv => G.vertex_mem_of_inc hv)).mpr hne
  exact ⟨nonempty_of_ncard_ne_zero (by omega), hcard ▸ hle2⟩

/-- Splitting at most `k` vertices preserves `IsGraph`. -/
theorem isGraph_of_obtainedBySplittingLe {k : ℕ} {G G' : Hypergraph α β}
    (hsplit : ObtainedBySplittingLe k G G') (hG : G.IsGraph) :
    G'.IsGraph := by
  induction hsplit with
  | refl _ _ => exact hG
  | step hs _ ih =>
    rcases hs with ⟨_, _, _, _, _, hs'⟩
    exact ih (isGraph_of_isVertexSplit hs' hG)

/-- Iterated **Graph Minors XXI, (3.6)**: if `G'` is obtained from a graph `G` by splitting at most
`k` vertices (`ObtainedBySplittingLe k G G'`), and `G` has a tangle of order `θ` with `k + 1 ≤ θ`,
then `G'` has a tangle of order `θ - k`. -/
theorem tangle_of_obtainedBySplittingLe {k : ℕ} {G G' : Hypergraph α β}
    (hG : G.IsGraph) (hsplit : ObtainedBySplittingLe k G G')
    {θ : ℕ} (hθ : k + 1 ≤ θ)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    ∃ 𝒯' : Set (Hypergraph α β × Hypergraph α β), IsTangle G' (θ - k) 𝒯' := by
  induction hsplit generalizing θ 𝒯 with
  | refl k G =>
    exact ⟨truncation 𝒯 (θ - k), h𝒯.truncation (by omega) (by omega)⟩
  | @step k G G₁ G' hs hrest ih =>
    have hG₁ : G₁.IsGraph := by
      rcases hs with ⟨_, _, _, _, _, hs'⟩
      exact isGraph_of_isVertexSplit hs' hG
    obtain ⟨𝒯₁, h𝒯₁⟩ := GM21.theorem_3_6_proof hG hs (by omega) h𝒯
    obtain ⟨𝒯', h𝒯'⟩ := ih hG₁ (θ := θ - 1) (by omega) h𝒯₁
    have h_eq : θ - 1 - k = θ - (k + 1) := by omega
    exact ⟨𝒯', h_eq ▸ h𝒯'⟩

/-- Iterated **Graph Minors XXI, (2.4)**: if `G'` is obtained from `G` by splitting at most `k`
vertices (`ObtainedBySplittingLe k G G'`) and `G` has a vital `p`-linkage, then `G'` has a vital
`(p + 2 * k)`-linkage. -/
theorem hasVitalPLinkage_of_obtainedBySplittingLe {k : ℕ} {G G' : Hypergraph α β} {p : ℕ}
    (hsplit : ObtainedBySplittingLe k G G') (hL : HasVitalPLinkage G p) :
    HasVitalPLinkage G' (p + 2 * k) := by
  induction hsplit generalizing p with
  | refl k G =>
    rcases hL with ⟨L, hLp⟩
    exact ⟨L, hLp.1, hLp.2.1, hLp.2.2.trans (by omega)⟩
  | @step k G G₁ G' hs hrest ih =>
    have hL₁ : HasVitalPLinkage G₁ (p + 2) := GM21.theorem_2_4_proof hs hL
    have hL' : HasVitalPLinkage G' ((p + 2) + 2 * k) := ih hL₁
    have h_eq : (p + 2) + 2 * k = p + 2 * (k + 1) := by omega
    exact h_eq ▸ hL'

/-- Under a single vertex split `IsVertexSplit G G' v v₁ v₂ δ₁ δ₂`, the terminals of
`splitSpanningSubgraph G' L` are contained in `terminals L ∪ {v₁, v₂}`. -/
lemma terminals_splitSpanningSubgraph_subset_insert {G G' L : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hL : IsVitalLinkage G L) :
    terminals (splitSpanningSubgraph G' L) ⊆ insert v₁ (insert v₂ (terminals L)) := by
  let L' := splitSpanningSubgraph G' L
  have hL'_link : IsLinkage G' L' := isLinkage_splitSpanningSubgraph hs hL.1
  have hE_L' : L.edgeSet = L'.edgeSet := by
    simp only [L', splitSpanningSubgraph, hs.edgeSet_eq,
      inter_eq_self_of_subset_right hL.1.1.edgeSet_subset]
  obtain ⟨hinc_other, _, _, _⟩ :=
    isVertexSplit_incidentEdges_props hs hL.1.1 (splitSpanningSubgraph_le G' L) hE_L'
  obtain ⟨_, _, _, _, hv_notG', hV_other, _, _, _, _, _⟩ := isVertexSplit_basic_props hs
  intro x hx
  by_cases hxv₁ : x = v₁
  · exact Or.inl hxv₁
  · by_cases hxv₂ : x = v₂
    · exact Or.inr (Or.inl hxv₂)
    · right; right
      have hxv : x ≠ v := fun h => hv_notG' (h ▸ hx.1)
      have hxG : x ∈ G.vertexSet := (hV_other x hxv hxv₁ hxv₂).mp hx.1
      have hxL : x ∈ L.vertexSet := by rwa [hL.2.1]
      have hnot2 : (incidentEdges L x).ncard ≠ 2 := by
        rw [hinc_other x hxv hxv₁ hxv₂]
        exact fun h2 => (hL'_link.notMem_terminals_iff hx.1).mpr h2 hx
      by_contra hx_not_term
      exact hnot2 ((hL.1.notMem_terminals_iff hxL).mp hx_not_term)

/-- For any reference vertex set `S : Set α`, a single vertex split increases `(vertexSet \ S).ncard`
by at most `2`. -/
lemma vertexSet_sdiff_ncard_le_of_isVertexSplit {G G' : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (S : Set α) :
    (G'.vertexSet \ S).ncard ≤ (G.vertexSet \ S).ncard + 2 := by
  have hsub : G'.vertexSet \ S ⊆ insert v₁ (insert v₂ (G.vertexSet \ S)) := by
    intro x ⟨hxG', hxS⟩
    rw [hs.vertexSet_eq] at hxG'
    rcases hxG' with ⟨hxG, _⟩ | rfl | rfl
    · exact Or.inr (Or.inr ⟨hxG, hxS⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hfin : (insert v₁ (insert v₂ (G.vertexSet \ S))).Finite :=
    ((G.vertexSet_finite.subset sdiff_subset).insert v₂).insert v₁
  calc
    (G'.vertexSet \ S).ncard ≤ (insert v₁ (insert v₂ (G.vertexSet \ S))).ncard :=
      ncard_le_ncard hsub hfin
    _ ≤ (insert v₂ (G.vertexSet \ S)).ncard + 1 := ncard_insert_le v₁ _
    _ ≤ ((G.vertexSet \ S).ncard + 1) + 1 := Nat.add_le_add_right (ncard_insert_le v₂ _) 1
    _ = (G.vertexSet \ S).ncard + 2 := by omega

/-- For any reference vertex set `S : Set α`, splitting at most `k` vertices increases
`(vertexSet \ S).ncard` by at most `2 * k`. -/
theorem vertexSet_sdiff_ncard_le_of_obtainedBySplittingLe {k : ℕ} {G G' : Hypergraph α β}
    (hsplit : ObtainedBySplittingLe k G G') (S : Set α) :
    (G'.vertexSet \ S).ncard ≤ (G.vertexSet \ S).ncard + 2 * k := by
  induction hsplit with
  | refl k G => omega
  | @step k G G₁ G' hs hrest ih =>
    rcases hs with ⟨_, _, _, _, _, hs'⟩
    have h₁ := vertexSet_sdiff_ncard_le_of_isVertexSplit hs' S
    have h₂ := ih
    omega

/-- If `G'` is obtained from `G` by splitting at most `k` vertices and `G.vertexSet ⊆ S`, then at
most `2 * k` vertices of `G'` lie outside `S`. -/
theorem vertexSet_sdiff_ncard_le_two_mul_of_obtainedBySplittingLe {k : ℕ} {G G' : Hypergraph α β}
    (hsplit : ObtainedBySplittingLe k G G') {S : Set α} (hGS : G.vertexSet ⊆ S) :
    (G'.vertexSet \ S).ncard ≤ 2 * k := by
  have h := vertexSet_sdiff_ncard_le_of_obtainedBySplittingLe hsplit S
  have hemp : G.vertexSet \ S = ∅ := Set.sdiff_eq_empty.mpr hGS
  rw [hemp, ncard_empty, zero_add] at h
  exact h

/-- `G'` can be obtained from `G` by splitting at most `k` vertices, with all newly produced
vertices chosen outside an ambient vertex set `U` (in `(5.2)`, `U = V(Γ)` when splitting vertices
of `B ⊆ Γ`). -/
inductive ObtainedBySplittingOutsideLe (U : Set α) :
    ℕ → Hypergraph α β → Hypergraph α β → Prop
  | refl (k : ℕ) (G : Hypergraph α β) : ObtainedBySplittingOutsideLe U k G G
  | step {k : ℕ} {G G₁ G' : Hypergraph α β} {v v₁ v₂ : α} {δ₁ δ₂ : Set β} :
      IsVertexSplit G G₁ v v₁ v₂ δ₁ δ₂ →
      v₁ ∉ U → v₂ ∉ U →
      ObtainedBySplittingOutsideLe U k G₁ G' →
      ObtainedBySplittingOutsideLe U (k + 1) G G'

/-- `ObtainedBySplittingOutsideLe U k G G'` implies `ObtainedBySplittingLe k G G'`. -/
theorem ObtainedBySplittingOutsideLe.toObtainedBySplittingLe {U : Set α} {k : ℕ}
    {G G' : Hypergraph α β} (h : ObtainedBySplittingOutsideLe U k G G') :
    ObtainedBySplittingLe k G G' := by
  induction h with
  | refl k G => exact ObtainedBySplittingLe.refl k G
  | step hs _ _ _ ih => exact ObtainedBySplittingLe.step ⟨_, _, _, _, _, hs⟩ ih

/-- Monotonicity of `ObtainedBySplittingOutsideLe` in the split bound `k`. -/
theorem ObtainedBySplittingOutsideLe.mono {U : Set α} {k k' : ℕ}
    {G G' : Hypergraph α β} (h : ObtainedBySplittingOutsideLe U k G G') (hle : k ≤ k') :
    ObtainedBySplittingOutsideLe U k' G G' := by
  induction h generalizing k' with
  | refl k G => exact ObtainedBySplittingOutsideLe.refl k' G
  | @step k G G₁ G' v v₁ v₂ δ₁ δ₂ hs hv₁ hv₂ hrest ih =>
    rcases k' with _ | k'
    · omega
    · exact ObtainedBySplittingOutsideLe.step hs hv₁ hv₂ (ih (by omega))

/-- If `G'` is obtained from `G` by splitting at most `k` vertices with new vertices outside `U`
and `L` is a vital linkage in `G`, then `G'` has a vital linkage `L'` whose terminals lie in
`terminals L ∪ (G'.vertexSet \ U)`. -/
theorem exists_vitalLinkage_of_obtainedBySplittingOutsideLe {U : Set α} {k : ℕ}
    {G G' L : Hypergraph α β}
    (hsplit : ObtainedBySplittingOutsideLe U k G G') (hL : IsVitalLinkage G L) :
    ∃ L' : Hypergraph α β,
      IsVitalLinkage G' L' ∧
      terminals L' ⊆ (terminals L ∩ G'.vertexSet) ∪ (G'.vertexSet \ U) := by
  induction hsplit generalizing L with
  | refl k G =>
    refine ⟨L, hL, ?_⟩
    intro x hx
    exact Or.inl ⟨hx, hL.1.1.vertexSet_subset hx.1⟩
  | @step k G G₁ G' v v₁ v₂ δ₁ δ₂ hs hv₁U hv₂U hrest ih =>
    let L₁ := splitSpanningSubgraph G₁ L
    have hL₁_vital : IsVitalLinkage G₁ L₁ :=
      (isVitalPLinkage_splitSpanningSubgraph hs ⟨hL, hL.1, le_rfl⟩).1
    have hterm₁ : terminals L₁ ⊆ insert v₁ (insert v₂ (terminals L)) :=
      terminals_splitSpanningSubgraph_subset_insert hs hL
    obtain ⟨L', hL'_vital, hterm'⟩ := ih hL₁_vital
    refine ⟨L', hL'_vital, ?_⟩
    intro x hx
    rcases hterm' hx with ⟨hx₁, hxG'⟩ | hx_diff
    · rcases hterm₁ hx₁ with rfl | rfl | hxL
      · exact Or.inr ⟨hxG', hv₁U⟩
      · exact Or.inr ⟨hxG', hv₂U⟩
      · exact Or.inl ⟨hxL, hxG'⟩
    · exact Or.inr hx_diff

end MultiSplit

/-! ## 2. Loop deletion in tangles and vital linkages (for Claim (4) of `(5.2)`) -/

section LoopDeletion

variable {α : Type u} {β : Type v}

/-- When `e ∈ G.edgeSet` has at most one end (`(G.ends e).ncard ≤ 1`), any separation `(A', B')` of
`G.deleteEdges {e}` has `G.ends e ⊆ A'.vertexSet` or `G.ends e ⊆ B'.vertexSet`. -/
private lemma ends_subset_left_or_right_of_ncard_le_one {G A' B' : Hypergraph α β} {e : β}
    (hsize : (G.ends e).ncard ≤ 1)
    (hsep' : (G.deleteEdges {e}).IsSeparation A' B') :
    G.ends e ⊆ A'.vertexSet ∨ G.ends e ⊆ B'.vertexSet := by
  have hfin : (G.ends e).Finite :=
    G.vertexSet_finite.subset fun _ hv => G.vertex_mem_of_inc hv
  have hsub : (G.ends e).Subsingleton :=
    (Set.ncard_le_one_iff_eq hfin).mp hsize |>.elim
      (fun hemp => hemp ▸ subsingleton_empty)
      (fun ⟨a, ha⟩ => ha ▸ subsingleton_singleton)
  rcases eq_empty_or_nonempty (G.ends e) with hemp | ⟨v, hv⟩
  · left; rw [hemp]; exact empty_subset _
  · have hvG : v ∈ (G.deleteEdges {e}).vertexSet := G.vertex_mem_of_inc hv
    rw [← hsep'.vertexSet_union] at hvG
    rcases hvG with hvA' | hvB'
    · left
      intro u hu
      exact (hsub hu hv) ▸ hvA'
    · right
      intro u hu
      exact (hsub hu hv) ▸ hvB'

/-- Adding a loop edge `e` whose ends lie in `A'.vertexSet` to `A' ≤ G.deleteEdges {e}`. -/
def addLoopSubhypergraph (G A' : Hypergraph α β) (e : β)
    (he : e ∈ G.edgeSet) (hA' : A' ≤ G.deleteEdges {e})
    (hends : G.ends e ⊆ A'.vertexSet) : Hypergraph α β where
  vertexSet := A'.vertexSet
  edgeSet := insert e A'.edgeSet
  Inc f v := (f = e ∧ G.Inc e v) ∨ A'.Inc f v
  vertex_mem_of_inc f v h := by
    rcases h with ⟨rfl, hinc⟩ | hinc
    · exact hends hinc
    · exact A'.vertex_mem_of_inc hinc
  edge_mem_of_inc f v h := by
    rcases h with ⟨rfl, _⟩ | hinc
    · exact Or.inl rfl
    · exact Or.inr (A'.edge_mem_of_inc hinc)
  vertexSet_finite := A'.vertexSet_finite
  edgeSet_finite := A'.edgeSet_finite.insert e

private lemma addLoopSubhypergraph_le {G A' : Hypergraph α β} {e : β}
    (he : e ∈ G.edgeSet) (hA' : A' ≤ G.deleteEdges {e})
    (hends : G.ends e ⊆ A'.vertexSet) :
    addLoopSubhypergraph G A' e he hA' hends ≤ G where
  vertexSet_subset := hA'.vertexSet_subset
  edgeSet_subset f hf := by
    rcases hf with rfl | hfA'
    · exact he
    · exact (hA'.edgeSet_subset hfA').1
  ends_eq f hf := by
    ext v
    change G.Inc f v ↔ (f = e ∧ G.Inc e v) ∨ A'.Inc f v
    rcases hf with rfl | hfA'
    · constructor
      · intro hinc
        exact Or.inl ⟨rfl, hinc⟩
      · rintro (⟨_, hinc⟩ | hinc)
        · exact hinc
        · have hf_del := hA'.edgeSet_subset (A'.edge_mem_of_inc hinc)
          exact (hf_del.2 rfl).elim
    · have hf_ne : f ≠ e := (hA'.edgeSet_subset hfA').2
      have hA'G : A' ≤ G := hA'.trans (GM10.deleteEdges_le G {e})
      constructor
      · intro hinc
        exact Or.inr ((GM10.inc_iff_of_le hA'G hfA').2 hinc)
      · rintro (⟨rfl, _⟩ | hinc)
        · exact (hf_ne rfl).elim
        · exact (GM10.inc_iff_of_le hA'G hfA').1 hinc

private lemma isSeparation_addLoopSubhypergraph_left {G A' B' : Hypergraph α β} {e : β}
    (he : e ∈ G.edgeSet) (hsep' : (G.deleteEdges {e}).IsSeparation A' B')
    (hends : G.ends e ⊆ A'.vertexSet) :
    G.IsSeparation (addLoopSubhypergraph G A' e he hsep'.left_le hends) B' := by
  have hleA := addLoopSubhypergraph_le he hsep'.left_le hends
  have hleB : B' ≤ G := hsep'.right_le.trans (GM10.deleteEdges_le G {e})
  rw [GM10.isSeparation_iff_of_le hleA hleB]
  refine ⟨hsep'.vertexSet_union, ?_, ?_⟩
  · ext f
    change f ∈ insert e A'.edgeSet ∪ B'.edgeSet ↔ f ∈ G.edgeSet
    rw [insert_union, hsep'.edgeSet_union]
    simp only [deleteEdges, mem_insert_iff, mem_sdiff, mem_singleton_iff]
    exact ⟨by rintro (rfl | ⟨hf, _⟩); exacts [he, hf],
      fun hf => by by_cases hfe : f = e; exacts [Or.inl hfe, Or.inr ⟨hf, hfe⟩]⟩
  · ext f
    change f ∈ insert e A'.edgeSet ∩ B'.edgeSet ↔ f ∈ (∅ : Set β)
    simp only [mem_inter_iff, mem_insert_iff, mem_empty_iff_false, iff_false]
    rintro ⟨rfl | hfA', hfB'⟩
    · exact (hsep'.right_le.edgeSet_subset hfB').2 rfl
    · exact hsep'.notMem_edgeSet_right hfA' hfB'

/-- Tangle in `G.deleteEdges {e}` obtained from a tangle `𝒯` in `G` by deleting an edge `e` with at
most one end. -/
def deleteLoopTangle (G : Hypergraph α β) (e : β)
    (𝒯 : Set (Hypergraph α β × Hypergraph α β)) (θ : ℕ) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | (G.deleteEdges {e}).IsSeparation p.1 p.2 ∧
    separationOrder p.1 p.2 < θ ∧
    ∃ q ∈ 𝒯, q.1.vertexSet = p.1.vertexSet ∧ q.2.vertexSet = p.2.vertexSet}

/-- **Graph Minors X, (8.4)** (direct vertex-set form without `Theorem45Statement`):
if `𝒯` is a tangle of order `θ` in `G` and `e ∈ G.edgeSet` has at most one end
(`(G.ends e).ncard ≤ 1`), then `deleteLoopTangle G e 𝒯 θ` is a tangle of order `θ` in
`G.deleteEdges {e}`. -/
theorem isTangle_deleteLoop {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {e : β} (he : e ∈ G.edgeSet) (hsize : (G.ends e).ncard ≤ 1) :
    IsTangle (G.deleteEdges {e}) θ (deleteLoopTangle G e 𝒯 θ) where
  one_le := h𝒯.one_le
  isSeparation _ _ h := h.1
  order_lt _ _ h := h.2.1
  axiom1 A' B' hsep' hord' := by
    rcases ends_subset_left_or_right_of_ncard_le_one hsize hsep' with hA' | hB'
    · let A := addLoopSubhypergraph G A' e he hsep'.left_le hA'
      have hsep : G.IsSeparation A B' := isSeparation_addLoopSubhypergraph_left he hsep' hA'
      have hord : separationOrder A B' < θ := hord'
      rcases h𝒯.axiom1 hsep hord with hm | hm
      · exact Or.inl ⟨hsep', hord', ⟨(A, B'), hm, rfl, rfl⟩⟩
      · exact Or.inr ⟨hsep'.symm, by rwa [GM10.separationOrder_comm],
          ⟨(B', A), hm, rfl, rfl⟩⟩
    · let B := addLoopSubhypergraph G B' e he hsep'.symm.left_le hB'
      have hsep : G.IsSeparation B A' :=
        isSeparation_addLoopSubhypergraph_left he hsep'.symm hB'
      have hord : separationOrder B A' < θ := by
        unfold separationOrder
        change (B'.vertexSet ∩ A'.vertexSet).ncard < θ
        rw [Set.inter_comm]
        exact hord'
      rcases h𝒯.axiom1 hsep hord with hm | hm
      · exact Or.inr ⟨hsep'.symm, by rwa [GM10.separationOrder_comm],
          ⟨(B, A'), hm, rfl, rfl⟩⟩
      · exact Or.inl ⟨hsep', hord', ⟨(A', B), hm, rfl, rfl⟩⟩
  axiom2 A₁' B₁' A₂' B₂' A₃' B₃' h₁ h₂ h₃ hU' := by
    have hVU' : A₁'.vertexSet ∪ A₂'.vertexSet ∪ A₃'.vertexSet = G.vertexSet :=
      congrArg Hypergraph.vertexSet hU'
    have hEU' : A₁'.edgeSet ∪ A₂'.edgeSet ∪ A₃'.edgeSet = G.edgeSet \ {e} :=
      congrArg Hypergraph.edgeSet hU'
    have hfin : (G.ends e).Finite :=
      G.vertexSet_finite.subset fun _ hv => G.vertex_mem_of_inc hv
    have hsub : (G.ends e).Subsingleton :=
      (Set.ncard_le_one_iff_eq hfin).mp hsize |>.elim
        (fun hemp => hemp ▸ subsingleton_empty)
        (fun ⟨a, ha⟩ => ha ▸ subsingleton_singleton)
    have hends_123 :
        G.ends e ⊆ A₁'.vertexSet ∨ G.ends e ⊆ A₂'.vertexSet ∨ G.ends e ⊆ A₃'.vertexSet := by
      rcases eq_empty_or_nonempty (G.ends e) with hemp | ⟨v, hv⟩
      · left; rw [hemp]; exact empty_subset _
      · have hvG : v ∈ A₁'.vertexSet ∪ A₂'.vertexSet ∪ A₃'.vertexSet :=
          hVU'.symm ▸ G.vertex_mem_of_inc hv
        rcases hvG with (hv₁ | hv₂) | hv₃
        · exact Or.inl fun u hu => (hsub hu hv) ▸ hv₁
        · exact Or.inr (Or.inl fun u hu => (hsub hu hv) ▸ hv₂)
        · exact Or.inr (Or.inr fun u hu => (hsub hu hv) ▸ hv₃)
    have mem_of_same_V : ∀ {A' B' A B : Hypergraph α β}
        (h : (A', B') ∈ deleteLoopTangle G e 𝒯 θ)
        (hsep : G.IsSeparation A B)
        (hVA : A.vertexSet = A'.vertexSet) (hVB : B.vertexSet = B'.vertexSet),
        (A, B) ∈ 𝒯 := by
      intro A' B' A B h hsep hVA hVB
      rcases h.2.2 with ⟨⟨A₀, B₀⟩, hm₀, hVA₀, hVB₀⟩
      dsimp only at hm₀ hVA₀ hVB₀
      have hord : separationOrder A B < θ := by
        unfold separationOrder
        change (A.vertexSet ∩ B.vertexSet).ncard < θ
        rw [hVA, hVB]
        exact h.2.1
      have hVB_sub : B₀.vertexSet ⊆ B.vertexSet := by rw [hVB₀, hVB]
      exact GM10.theorem_2_9_case_1 h𝒯 hm₀ hsep hord hVB_sub
    have exists_lift : ∀ {A' B' : Hypergraph α β}
        (h : (A', B') ∈ deleteLoopTangle G e 𝒯 θ),
        ∃ A B : Hypergraph α β, (A, B) ∈ 𝒯 ∧ A.vertexSet = A'.vertexSet ∧ A' ≤ A := by
      intro A' B' h
      rcases ends_subset_left_or_right_of_ncard_le_one hsize h.1 with hA' | hB'
      · let A := addLoopSubhypergraph G A' e he h.1.left_le hA'
        have hsep : G.IsSeparation A B' := isSeparation_addLoopSubhypergraph_left he h.1 hA'
        have hm : (A, B') ∈ 𝒯 := mem_of_same_V h hsep rfl rfl
        have hle : A' ≤ A :=
          (GM10.le_iff_of_le (h.1.left_le.trans (GM10.deleteEdges_le G {e})) hsep.left_le).2
            ⟨Subset.rfl, subset_insert e _⟩
        exact ⟨A, B', hm, rfl, hle⟩
      · let B := addLoopSubhypergraph G B' e he h.1.symm.left_le hB'
        have hsep : G.IsSeparation A' B :=
          (isSeparation_addLoopSubhypergraph_left he h.1.symm hB').symm
        have hm : (A', B) ∈ 𝒯 := mem_of_same_V h hsep rfl rfl
        exact ⟨A', B, hm, rfl, le_rfl⟩
    rcases hends_123 with hends₁ | hends₂ | hends₃
    · let A₁ := addLoopSubhypergraph G A₁' e he h₁.1.left_le hends₁
      have hsep₁ : G.IsSeparation A₁ B₁' := isSeparation_addLoopSubhypergraph_left he h₁.1 hends₁
      have hm₁ : (A₁, B₁') ∈ 𝒯 := mem_of_same_V h₁ hsep₁ rfl rfl
      obtain ⟨A₂, B₂, hm₂, hVA₂, hle₂⟩ := exists_lift h₂
      obtain ⟨A₃, B₃, hm₃, hVA₃, hle₃⟩ := exists_lift h₃
      apply h𝒯.axiom2 hm₁ hm₂ hm₃
      have hU_le : A₁ ∪ A₂ ∪ A₃ ≤ G :=
        GM10.union_le (GM10.union_le hsep₁.left_le (h𝒯.isSeparation hm₂).left_le)
          (h𝒯.isSeparation hm₃).left_le
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl ?_ ?_
      · change A₁'.vertexSet ∪ A₂.vertexSet ∪ A₃.vertexSet = G.vertexSet
        rw [hVA₂, hVA₃, hVU']
      · ext f
        refine ⟨fun hf => hU_le.edgeSet_subset hf, fun hfG => ?_⟩
        by_cases hfe : f = e
        · subst hfe
          exact Or.inl (Or.inl (Or.inl rfl))
        · have hf_del : f ∈ G.edgeSet \ {e} := ⟨hfG, hfe⟩
          rcases (hEU'.symm ▸ hf_del) with (hf₁ | hf₂) | hf₃
          · exact Or.inl (Or.inl (Or.inr hf₁))
          · exact Or.inl (Or.inr (hle₂.edgeSet_subset hf₂))
          · exact Or.inr (hle₃.edgeSet_subset hf₃)
    · obtain ⟨A₁, B₁, hm₁, hVA₁, hle₁⟩ := exists_lift h₁
      let A₂ := addLoopSubhypergraph G A₂' e he h₂.1.left_le hends₂
      have hsep₂ : G.IsSeparation A₂ B₂' := isSeparation_addLoopSubhypergraph_left he h₂.1 hends₂
      have hm₂ : (A₂, B₂') ∈ 𝒯 := mem_of_same_V h₂ hsep₂ rfl rfl
      obtain ⟨A₃, B₃, hm₃, hVA₃, hle₃⟩ := exists_lift h₃
      apply h𝒯.axiom2 hm₁ hm₂ hm₃
      have hU_le : A₁ ∪ A₂ ∪ A₃ ≤ G :=
        GM10.union_le (GM10.union_le (h𝒯.isSeparation hm₁).left_le hsep₂.left_le)
          (h𝒯.isSeparation hm₃).left_le
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl ?_ ?_
      · change A₁.vertexSet ∪ A₂'.vertexSet ∪ A₃.vertexSet = G.vertexSet
        rw [hVA₁, hVA₃, hVU']
      · ext f
        refine ⟨fun hf => hU_le.edgeSet_subset hf, fun hfG => ?_⟩
        by_cases hfe : f = e
        · subst hfe
          exact Or.inl (Or.inr (Or.inl rfl))
        · have hf_del : f ∈ G.edgeSet \ {e} := ⟨hfG, hfe⟩
          rcases (hEU'.symm ▸ hf_del) with (hf₁ | hf₂) | hf₃
          · exact Or.inl (Or.inl (hle₁.edgeSet_subset hf₁))
          · exact Or.inl (Or.inr (Or.inr hf₂))
          · exact Or.inr (hle₃.edgeSet_subset hf₃)
    · obtain ⟨A₁, B₁, hm₁, hVA₁, hle₁⟩ := exists_lift h₁
      obtain ⟨A₂, B₂, hm₂, hVA₂, hle₂⟩ := exists_lift h₂
      let A₃ := addLoopSubhypergraph G A₃' e he h₃.1.left_le hends₃
      have hsep₃ : G.IsSeparation A₃ B₃' := isSeparation_addLoopSubhypergraph_left he h₃.1 hends₃
      have hm₃ : (A₃, B₃') ∈ 𝒯 := mem_of_same_V h₃ hsep₃ rfl rfl
      apply h𝒯.axiom2 hm₁ hm₂ hm₃
      have hU_le : A₁ ∪ A₂ ∪ A₃ ≤ G :=
        GM10.union_le (GM10.union_le (h𝒯.isSeparation hm₁).left_le (h𝒯.isSeparation hm₂).left_le)
          hsep₃.left_le
      refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hU_le le_rfl ?_ ?_
      · change A₁.vertexSet ∪ A₂.vertexSet ∪ A₃'.vertexSet = G.vertexSet
        rw [hVA₁, hVA₂, hVU']
      · ext f
        refine ⟨fun hf => hU_le.edgeSet_subset hf, fun hfG => ?_⟩
        by_cases hfe : f = e
        · subst hfe
          exact Or.inr (Or.inl rfl)
        · have hf_del : f ∈ G.edgeSet \ {e} := ⟨hfG, hfe⟩
          rcases (hEU'.symm ▸ hf_del) with (hf₁ | hf₂) | hf₃
          · exact Or.inl (Or.inl (hle₁.edgeSet_subset hf₁))
          · exact Or.inl (Or.inr (hle₂.edgeSet_subset hf₂))
          · exact Or.inr (Or.inr hf₃)
  axiom3 A' B' h hVA' := by
    rcases h.2.2 with ⟨⟨A, B⟩, hm, hVA, _⟩
    dsimp only at hm hVA
    exact h𝒯.axiom3 hm (hVA.trans hVA')

/-- Deleting an edge `e` with at most one end preserves any vital linkage `L` in `G`. -/
theorem isVitalLinkage_deleteLoop {G L : Hypergraph α β} {e : β}
    (hL : IsVitalLinkage G L) (hsize : (G.ends e).ncard ≤ 1) :
    IsVitalLinkage (G.deleteEdges {e}) L := by
  have he_notL : e ∉ L.edgeSet := by
    intro heL
    have h2 : (L.ends e).ncard = 2 := hL.1.ends_ncard_eq_two heL
    rw [← hL.1.1.ends_eq e heL] at h2
    omega
  have hL_le : L ≤ G.deleteEdges {e} :=
    { vertexSet_subset := hL.1.1.vertexSet_subset
      edgeSet_subset := fun f hf => ⟨hL.1.1.edgeSet_subset hf, fun hfe => he_notL (hfe ▸ hf)⟩
      ends_eq := fun f hf =>
        ((GM10.deleteEdges_le G {e}).ends_eq f
          ⟨hL.1.1.edgeSet_subset hf, fun hfe => he_notL (hfe ▸ hf)⟩).symm.trans
          (hL.1.1.ends_eq f hf) }
  have hL_link : IsLinkage (G.deleteEdges {e}) L :=
    isLinkage_of_le hL.1 le_rfl hL_le
  refine ⟨hL_link, hL.2.1, fun L' hL' hpat => ?_⟩
  have hL'_G : IsLinkage G L' :=
    isLinkage_of_le hL' le_rfl (hL'.1.trans (GM10.deleteEdges_le G {e}))
  exact hL.2.2 L' hL'_G hpat

end LoopDeletion

/-! ## 3. Surface classification with boundary (for Claim (6) of `(5.2)`) -/

/-- Two connected surfaces with homeomorphic cappings and the same number of cuffs are
homeomorphic. -/
theorem homeo_of_capped_homeo_and_cuffs_ncard_eq
    {S Shat S' Shat' : Type}
    [TopologicalSpace S] [TopologicalSpace Shat]
    [TopologicalSpace S'] [TopologicalSpace Shat']
    (hS : IsSurface S) [ConnectedSpace S]
    (hS' : IsSurface S') [ConnectedSpace S']
    (cap : GM19.IsCappedSurface S Shat) (cap' : GM19.IsCappedSurface S' Shat')
    (hhat : Nonempty (Shat' ≃ₜ Shat))
    (hcuffs : (cuffs S').ncard = (cuffs S).ncard) :
    Nonempty (S' ≃ₜ S) := by
  obtain ⟨a, b, c, ⟨eS⟩⟩ := classification S hS inferInstance
  obtain ⟨a', b', c', ⟨eS'⟩⟩ := classification S' hS' inferInstance
  obtain ⟨e_SM⟩ := GM19.capModel a b c Shat (GM19.IsCappedSurface.ofHomeo eS.symm cap)
  obtain ⟨e_S'M⟩ := GM19.capModel a' b' c' Shat' (GM19.IsCappedSurface.ofHomeo eS'.symm cap')
  obtain ⟨e_hat⟩ := hhat
  have hM0 : Nonempty (SurfaceModel a' b' 0 ≃ₜ SurfaceModel a b 0) :=
    ⟨e_S'M.symm.trans (e_hat.trans e_SM)⟩
  obtain ⟨-, hab, hb0⟩ := (modelCriterion.2 a' b' 0 a b 0).mp hM0
  have hcS : (cuffs S).ncard = c := by
    have h := GM19.numCuffs_eq eS
    rw [numCuffs_model] at h
    exact h
  have hcS' : (cuffs S').ncard = c' := by
    have h := GM19.numCuffs_eq eS'
    rw [numCuffs_model] at h
    exact h
  have hcc' : c' = c := by omega
  obtain ⟨e_M⟩ := (modelCriterion.2 a' b' c' a b c).mpr ⟨hcc', hab, hb0⟩
  exact ⟨eS'.trans (e_M.trans eS.symm)⟩

/-! ## 4. Subclaims (4), (5), and (6) of Graph Minors XXI, (5.2) -/

/-- **Graph Minors XXI, (5.2), Claim (4)** (page 18 of the preprint):
"(4) $\Gamma$ *is connected and loopless.*" -/
theorem claim_5_2_4 {α : Type u} {β : Type v}
    {G L : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (hL : IsVitalLinkage G L) :
    (∀ Γ₁ Γ₂ : Hypergraph α β, (Γ₁, Γ₂) ∈ 𝒯 → separationOrder Γ₁ Γ₂ = 0 →
      IsTangle Γ₂ θ (restrictOrderZeroTangle Γ₂ 𝒯) ∧
      IsVitalLinkage Γ₂ (L ∩ Γ₂) ∧
      terminals (L ∩ Γ₂) ⊆ terminals L ∧
      Γ₂.vertexSet ⊆ G.vertexSet) ∧
    (∀ e ∈ G.edgeSet, (G.ends e).ncard ≤ 1 →
      IsTangle (G.deleteEdges {e}) θ (deleteLoopTangle G e 𝒯 θ) ∧
      IsVitalLinkage (G.deleteEdges {e}) L ∧
      (G.deleteEdges {e}).vertexSet = G.vertexSet ∧
      (G.deleteEdges {e}).edgeSet.ncard < G.edgeSet.ncard) := by
  refine ⟨?_, ?_⟩
  · intro Γ₁ Γ₂ hmem hord0
    have hsep : G.IsSeparation Γ₁ Γ₂ := h𝒯.isSeparation hmem
    have h𝒯₂ : IsTangle Γ₂ θ (restrictOrderZeroTangle Γ₂ 𝒯) :=
      GM21.theorem_3_3_proof h𝒯 hmem hord0
    have hL₂_vital : IsVitalLinkage Γ₂ (L ∩ Γ₂) :=
      (GM21.theorem_2_3_proof hL.1 hsep).2 hL
    have hterm_sub : terminals (L ∩ Γ₂) ⊆ terminals L := by
      have h22 := (GM21.theorem_2_2_proof hL.1 hsep).2
      have hemp : (Γ₁ ∩ Γ₂).vertexSet = ∅ :=
        (ncard_eq_zero (Γ₁ ∩ Γ₂).vertexSet_finite).1 hord0
      rw [hemp, union_empty] at h22
      exact h22.trans sdiff_subset
    exact ⟨h𝒯₂, hL₂_vital, hterm_sub, hsep.right_le.vertexSet_subset⟩
  · intro e he hsize
    refine ⟨isTangle_deleteLoop h𝒯 he hsize,
      isVitalLinkage_deleteLoop hL hsize, rfl, ?_⟩
    exact ncard_lt_ncard (sdiff_singleton_ssubset.2 he) G.edgeSet_finite

/-- **Graph Minors XXI, (5.2), Claim (5)** (page 18 of the preprint):
"(5) *Suppose that* $(A, B) \in \mathcal{T}$ *has order* $\le \theta_4$, *and* $\Gamma'$ *is a
drawing in a surface* $\Sigma'$, *such that* $\Gamma'$ *can be obtained from* $B$ *by splitting*
$\le \theta_4$ *vertices of* $B$. *Then* $\hat{\Sigma}'$ *is not simpler than* $\Sigma_0$." -/
theorem claim_5_2_5 {α : Type u} {β : Type v}
    {S₀ S' Shat' : Type}
    [TopologicalSpace S₀] [TopologicalSpace S'] [TopologicalSpace Shat']
    {G L A B G' : Hypergraph α β}
    {p θ θ₄ θ₁ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hG : G.IsGraph)
    (h𝒯 : IsTangle G θ 𝒯)
    (hL : IsVitalPLinkage G L p)
    (hAB : (A, B) ∈ 𝒯)
    (hord : separationOrder A B ≤ θ₄)
    (hsplit : ObtainedBySplittingLe θ₄ B G')
    (hθ_ge : 2 * θ₄ + θ₁ ≤ θ)
    (hθ₁_pos : 1 ≤ θ₁)
    (h_ind1 : ∀ (T' : Set (Hypergraph α β × Hypergraph α β)),
      IsSimplerThan Shat' S₀ →
      IsTangle G' θ₁ T' →
      ¬ HasVitalPLinkage G' (p + 3 * θ₄)) :
    ¬ IsSimplerThan Shat' S₀ := by
  intro hsimpler
  have hsep : G.IsSeparation A B := h𝒯.isSeparation hAB
  obtain ⟨𝒯_B, h𝒯_B, -⟩ := GM21.theorem_3_5_proof hG h𝒯 hAB
  have h𝒯_B' : IsTangle B (θ - θ₄) (truncation 𝒯_B (θ - θ₄)) :=
    h𝒯_B.truncation (by omega) (by omega)
  have hB_graph : B.IsGraph :=
    fun e he => (hsep.right_le.ends_eq e he).symm ▸ hG e (hsep.right_le.edgeSet_subset he)
  obtain ⟨𝒯_G', h𝒯_G'⟩ :=
    tangle_of_obtainedBySplittingLe hB_graph hsplit (by omega) h𝒯_B'
  have h𝒯_θ₁ : IsTangle G' θ₁ (truncation 𝒯_G' θ₁) :=
    h𝒯_G'.truncation hθ₁_pos (by omega)
  have hLB_vital : IsVitalLinkage B (L ∩ B) := (GM21.theorem_2_3_proof hL.1.1 hsep).2 hL.1
  have hLB_term : (terminals (L ∩ B)).ncard ≤ p + θ₄ := by
    have hsub := (GM21.theorem_2_2_proof hL.1.1 hsep).2
    have hfin₁ : (terminals L \ A.vertexSet).Finite :=
      (L.vertexSet_finite.subset fun _ h => h.1).subset sdiff_subset
    have hfin₂ : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
    calc
      (terminals (L ∩ B)).ncard
        ≤ ((terminals L \ A.vertexSet) ∪ (A ∩ B).vertexSet).ncard :=
          ncard_le_ncard hsub (hfin₁.union hfin₂)
      _ ≤ (terminals L \ A.vertexSet).ncard + (A ∩ B).vertexSet.ncard :=
          ncard_union_le _ _
      _ ≤ (terminals L).ncard + separationOrder A B := by
          refine Nat.add_le_add ?_ le_rfl
          exact ncard_le_ncard sdiff_subset (L.vertexSet_finite.subset fun _ h => h.1)
      _ ≤ p + θ₄ := Nat.add_le_add hL.2.2 hord
  have hB_vital : HasVitalPLinkage B (p + θ₄) :=
    ⟨L ∩ B, hLB_vital, hLB_vital.1, hLB_term⟩
  have hG'_vital : HasVitalPLinkage G' ((p + θ₄) + 2 * θ₄) :=
    hasVitalPLinkage_of_obtainedBySplittingLe hsplit hB_vital
  have h_eq : (p + θ₄) + 2 * θ₄ = p + 3 * θ₄ := by omega
  exact h_ind1 (truncation 𝒯_G' θ₁) hsimpler h𝒯_θ₁ (h_eq ▸ hG'_vital)

/-- **Graph Minors XXI, (5.2), Claim (6)** (pages 18–19 of the preprint):
"(6) *Suppose that* $(A, B) \in \mathcal{T}$ *has order* $\le \theta_4$, *and* $\Gamma'$ *is a
drawing in a surface* $\Sigma'$, *such that* $\Gamma'$ *can be obtained from* $B$ *by splitting*
$\le \theta_4$ *vertices of* $B$. *Suppose, moreover, that* ...
(a) $\hat{\Sigma}'$ *is homeomorphic to* $\Sigma_0$*, and*
(b) *for* $v \in V(\Gamma')$, $v \in bd(\Sigma')$ *if and only if either* $v \in V(A \cap B)$,
*or* $v \in V(\Gamma) \cap bd(\Sigma)$, *or* $v \notin V(\Gamma)$ *(that is,* $v$ *is a new vertex
produced by splitting).*
*Then* $c(\Sigma') \ge c(\Sigma)$*, and if equality holds then* $|V(\Gamma') \cap bd(\Sigma')| \ge p$." -/
theorem claim_5_2_6 {S S₀ S' Shat' : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    [TopologicalSpace S'] [TopologicalSpace Shat']
    (hS : IsSurface S) [ConnectedSpace S]
    (hS' : IsSurface S') [ConnectedSpace S']
    (cap : GM19.IsCappedSurface S S₀) (cap' : GM19.IsCappedSurface S' Shat')
    {Γ : Surface.Drawing S}
    {L A B G' : Hypergraph S (Set S)}
    {bd_V' : Set S}
    {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hAB : (A, B) ∈ 𝒯)
    (hord : separationOrder A B ≤ θ₄)
    (hsplit : ObtainedBySplittingOutsideLe Γ.V θ₄ B G')
    (h6a : Nonempty (Shat' ≃ₜ S₀))
    (h6b : ∀ v ∈ G'.vertexSet,
      v ∈ bd_V' ↔ v ∈ (A ∩ B).vertexSet ∨ v ∈ Γ.V ∩ bd S ∨ v ∉ Γ.V)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (h_ind2 : (cuffs S').ncard < (cuffs S).ncard →
      (G'.vertexSet ∩ bd_V').ncard ≤ p + 3 * θ₄ →
      ∀ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (L' : Hypergraph S (Set S)),
        IsTangle G' θ₂ T' →
        IsVitalLinkage G' L' →
        ¬ (terminals L' ⊆ bd_V'))
    (h_ind3 : Nonempty (S' ≃ₜ S) →
      (G'.vertexSet ∩ bd_V').ncard < p →
      ∀ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (L' : Hypergraph S (Set S)),
        IsTangle G' θ₃ T' →
        IsVitalLinkage G' L' →
        ¬ (terminals L' ⊆ bd_V')) :
    (cuffs S).ncard ≤ (cuffs S').ncard ∧
      ((cuffs S').ncard = (cuffs S).ncard → p ≤ (G'.vertexSet ∩ bd_V').ncard) := by
  have hG : Γ.toHypergraph.IsGraph := drawing_toHypergraph_isGraph Γ
  have hsep : Γ.toHypergraph.IsSeparation A B := h𝒯.isSeparation hAB
  obtain ⟨𝒯_B, h𝒯_B, -⟩ := GM21.theorem_3_5_proof hG h𝒯 hAB
  have h𝒯_B' : IsTangle B (θ - θ₄) (truncation 𝒯_B (θ - θ₄)) :=
    h𝒯_B.truncation (by omega) (by omega)
  have hB_graph : B.IsGraph :=
    fun e he => (hsep.right_le.ends_eq e he).symm ▸ hG e (hsep.right_le.edgeSet_subset he)
  obtain ⟨𝒯_G', h𝒯_G'⟩ :=
    tangle_of_obtainedBySplittingLe hB_graph hsplit.toObtainedBySplittingLe (by omega) h𝒯_B'
  have hLB_vital : IsVitalLinkage B (L ∩ B) := (GM21.theorem_2_3_proof hL.1 hsep).2 hL
  have hLB_term : terminals (L ∩ B) ⊆ (Γ.V ∩ bd S) ∪ (A ∩ B).vertexSet := by
    intro v hv
    rcases (GM21.theorem_2_2_proof hL.1 hsep).2 hv with ⟨hvL, _⟩ | hvAB
    · exact Or.inl ⟨hL.1.1.vertexSet_subset hvL.1, hL_bd hvL⟩
    · exact Or.inr hvAB
  obtain ⟨L', hL'_vital, hL'_term⟩ :=
    exists_vitalLinkage_of_obtainedBySplittingOutsideLe hsplit hLB_vital
  have hL'_bd : terminals L' ⊆ bd_V' := by
    intro v hv
    have hvG' : v ∈ G'.vertexSet := hL'_vital.1.1.vertexSet_subset hv.1
    rw [h6b v hvG']
    rcases hL'_term hv with ⟨hvLB, _⟩ | ⟨_, hv_notΓ⟩
    · rcases hLB_term hvLB with hv_bd | hvAB
      · exact Or.inr (Or.inl hv_bd)
      · exact Or.inl hvAB
    · exact Or.inr (Or.inr hv_notΓ)
  have hG'_bd_sub :
      G'.vertexSet ∩ bd_V' ⊆ ((A ∩ B).vertexSet ∪ (Γ.V ∩ bd S)) ∪ (G'.vertexSet \ Γ.V) := by
    intro v ⟨hvG', hvbd⟩
    rcases (h6b v hvG').mp hvbd with hvAB | hv_bd | hv_notΓ
    · exact Or.inl (Or.inl hvAB)
    · exact Or.inl (Or.inr hv_bd)
    · exact Or.inr ⟨hvG', hv_notΓ⟩
  have hfin_AB : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
  have hfin_Γbd : (Γ.V ∩ bd S).Finite := Γ.toHypergraph.vertexSet_finite.subset inter_subset_left
  have hfin_diff : (G'.vertexSet \ Γ.V).Finite := G'.vertexSet_finite.subset sdiff_subset
  have hdiff_card : (G'.vertexSet \ Γ.V).ncard ≤ 2 * θ₄ :=
    vertexSet_sdiff_ncard_le_two_mul_of_obtainedBySplittingLe
      hsplit.toObtainedBySplittingLe hsep.right_le.vertexSet_subset
  have hG'_bd_le : (G'.vertexSet ∩ bd_V').ncard ≤ p + 3 * θ₄ := by
    calc
      (G'.vertexSet ∩ bd_V').ncard
        ≤ (((A ∩ B).vertexSet ∪ (Γ.V ∩ bd S)) ∪ (G'.vertexSet \ Γ.V)).ncard :=
          ncard_le_ncard hG'_bd_sub ((hfin_AB.union hfin_Γbd).union hfin_diff)
      _ ≤ ((A ∩ B).vertexSet ∪ (Γ.V ∩ bd S)).ncard + (G'.vertexSet \ Γ.V).ncard :=
          ncard_union_le _ _
      _ ≤ (A ∩ B).vertexSet.ncard + (Γ.V ∩ bd S).ncard + (G'.vertexSet \ Γ.V).ncard :=
          Nat.add_le_add_right (ncard_union_le _ _) _
      _ ≤ θ₄ + p + 2 * θ₄ :=
          Nat.add_le_add (Nat.add_le_add hord hΓ_bd) hdiff_card
      _ = p + 3 * θ₄ := by omega
  refine ⟨?_, ?_⟩
  · by_contra! hlt
    have h𝒯_θ₂ : IsTangle G' θ₂ (truncation 𝒯_G' θ₂) :=
      h𝒯_G'.truncation hθ₂_pos (by omega)
    exact h_ind2 hlt hG'_bd_le (truncation 𝒯_G' θ₂) L' h𝒯_θ₂ hL'_vital hL'_bd
  · intro hcuffs_eq
    by_contra! hlt
    have hhomeo : Nonempty (S' ≃ₜ S) :=
      homeo_of_capped_homeo_and_cuffs_ncard_eq hS hS' cap cap' h6a hcuffs_eq
    have h𝒯_θ₃ : IsTangle G' θ₃ (truncation 𝒯_G' θ₃) :=
      h𝒯_G'.truncation hθ₃_pos (by omega)
    exact h_ind3 hhomeo hlt (truncation 𝒯_G' θ₃) L' h𝒯_θ₃ hL'_vital hL'_bd

/-- Cardinality deduction in **Graph Minors XXI, (5.2), Claim (11)** (page 21 of the preprint):
if `C ⊆ bd S`, `bd_V' ⊆ ((Γ.V ∩ bd S) \ C) ∪ (F ∩ Γ.V)`, and
`(Γ.V ∩ bd S).ncard ≤ bd_V'.ncard`, then `(C ∩ Γ.V).ncard ≤ (F ∩ Γ.V).ncard`. -/
theorem claim_5_2_11_card {S : Type*} [TopologicalSpace S]
    {Γ : Surface.Drawing S} {F C bd_V' : Set S}
    (hC_bd : C ⊆ bd S)
    (hbd_V' : bd_V' ⊆ ((Γ.V ∩ bd S) \ C) ∪ (F ∩ Γ.V))
    (hle : (Γ.V ∩ bd S).ncard ≤ bd_V'.ncard) :
    (C ∩ Γ.V).ncard ≤ (F ∩ Γ.V).ncard := by
  have hfin_V : Γ.V.Finite := Γ.toHypergraph.vertexSet_finite
  have hfin_bd : (Γ.V ∩ bd S).Finite := hfin_V.subset inter_subset_left
  have hfin_diff : ((Γ.V ∩ bd S) \ C).Finite := hfin_bd.subset sdiff_subset
  have hfin_C : (C ∩ Γ.V).Finite := hfin_V.subset inter_subset_right
  have hfin_F : (F ∩ Γ.V).Finite := hfin_V.subset inter_subset_right
  have h_decomp : Γ.V ∩ bd S = ((Γ.V ∩ bd S) \ C) ∪ (C ∩ Γ.V) := by
    ext v
    simp only [mem_inter_iff, mem_union, mem_sdiff]
    constructor
    · intro ⟨hvΓ, hvbd⟩
      by_cases hvC : v ∈ C
      · exact Or.inr ⟨hvC, hvΓ⟩
      · exact Or.inl ⟨⟨hvΓ, hvbd⟩, hvC⟩
    · rintro (⟨⟨hvΓ, hvbd⟩, _⟩ | ⟨hvC, hvΓ⟩)
      · exact ⟨hvΓ, hvbd⟩
      · exact ⟨hvΓ, hC_bd hvC⟩
  have h_disj : Disjoint ((Γ.V ∩ bd S) \ C) (C ∩ Γ.V) :=
    disjoint_left.mpr fun _ h₁ h₂ => h₁.2 h₂.1
  have h_eq : (Γ.V ∩ bd S).ncard = ((Γ.V ∩ bd S) \ C).ncard + (C ∩ Γ.V).ncard := by
    conv_lhs => rw [h_decomp]
    exact ncard_union_eq h_disj hfin_diff hfin_C
  have h_upper : bd_V'.ncard ≤ ((Γ.V ∩ bd S) \ C).ncard + (F ∩ Γ.V).ncard :=
    (ncard_le_ncard hbd_V' (hfin_diff.union hfin_F)).trans (ncard_union_le _ _)
  omega

/-- Drawing-transport specialization of `claim_5_2_5`: given a drawing `Γ' : Drawing S'` in a
surface `S'` with capping `cap' : IsCappedSurface S' Shat'` and injective maps `(π, fE)` on
`Γ'.V` and `Γ'.E` such that `mapHypergraph π fE Γ'.toHypergraph` is obtained from `B` by splitting
at most `θ₄` vertices, `Shat'` is not simpler than `S₀`. -/
theorem apply_claim_5_2_5_of_drawing {α : Type} {β : Type}
    {S₀ S' Shat' : Type}
    [TopologicalSpace S₀] [TopologicalSpace S'] [TopologicalSpace Shat']
    {G L A B : Hypergraph α β}
    {Γ' : Surface.Drawing S'}
    {π : S' → α} {fE : Set S' → β}
    {p θ θ₄ θ₁ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hG : G.IsGraph)
    (h𝒯 : IsTangle G θ 𝒯)
    (hL : IsVitalPLinkage G L p)
    (hAB : (A, B) ∈ 𝒯)
    (hord : separationOrder A B ≤ θ₄)
    (hπ : InjOn π Γ'.V)
    (hfE : InjOn fE Γ'.E)
    (hsplit : ObtainedBySplittingLe θ₄ B (mapHypergraph π fE Γ'.toHypergraph))
    (hθ_ge : 2 * θ₄ + θ₁ ≤ θ)
    (hθ₁_pos : 1 ≤ θ₁)
    (h_ind1 : IsSimplerThan Shat' S₀ →
      ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        IsTangle Γ'.toHypergraph θ₁ T' →
        ¬ HasVitalPLinkage Γ'.toHypergraph (p + 3 * θ₄)) :
    ¬ IsSimplerThan Shat' S₀ := by
  refine claim_5_2_5 (S' := S') hG h𝒯 hL hAB hord hsplit hθ_ge hθ₁_pos ?_
  intro T_G' hsimpler hT_G' hvit_G'
  have hT' : IsTangle Γ'.toHypergraph θ₁ (comapTangle π fE Γ'.toHypergraph T_G') :=
    isTangle_comapHypergraph hπ hfE hT_G'
  have hvit' : HasVitalPLinkage Γ'.toHypergraph (p + 3 * θ₄) :=
    (hasVitalPLinkage_mapHypergraph hπ hfE).mp hvit_G'
  exact h_ind1 hsimpler _ hT' hvit'

/-- Drawing-transport specialization of `claim_5_2_6`: given a drawing `Γ' : Drawing S'` in a
surface `S'` with capping `cap' : IsCappedSurface S' Shat'` and injective maps `(π, fE)` on
`Γ'.V` and `Γ'.E` such that `G' = mapHypergraph π fE Γ'.toHypergraph` is obtained from `B` by
splitting at most `θ₄` vertices with new vertices outside `Γ.V`, and `bd_V' = π '' (Γ'.V ∩ bd S')`
satisfies (6b), we have `(cuffs S).ncard ≤ (cuffs S').ncard` and on equality
`p ≤ (Γ'.V ∩ bd S').ncard`. -/
theorem apply_claim_5_2_6_of_drawing {S S₀ S' Shat' : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    [TopologicalSpace S'] [TopologicalSpace Shat']
    (hS : IsSurface S) [ConnectedSpace S]
    (hS' : IsSurface S') [ConnectedSpace S']
    (cap : GM19.IsCappedSurface S S₀) (cap' : GM19.IsCappedSurface S' Shat')
    {Γ : Surface.Drawing S}
    {L A B : Hypergraph S (Set S)}
    {Γ' : Surface.Drawing S'}
    {π : S' → S} {fE : Set S' → Set S}
    {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hAB : (A, B) ∈ 𝒯)
    (hord : separationOrder A B ≤ θ₄)
    (hπ : InjOn π Γ'.V)
    (hfE : InjOn fE Γ'.E)
    (hsplit : ObtainedBySplittingOutsideLe Γ.V θ₄ B (mapHypergraph π fE Γ'.toHypergraph))
    (h6a : Nonempty (Shat' ≃ₜ S₀))
    (h6b : ∀ y ∈ Γ'.V,
      y ∈ bd S' ↔ π y ∈ (A ∩ B).vertexSet ∨ π y ∈ Γ.V ∩ bd S ∨ π y ∉ Γ.V)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (h_ind2 : (cuffs S').ncard < (cuffs S).ncard →
      (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
      ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
        (L' : Hypergraph S' (Set S')),
        IsTangle Γ'.toHypergraph θ₂ T' →
        IsVitalLinkage Γ'.toHypergraph L' →
        ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : Nonempty (S' ≃ₜ S) →
      (Γ'.V ∩ bd S').ncard < p →
      ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
        (L' : Hypergraph S' (Set S')),
        IsTangle Γ'.toHypergraph θ₃ T' →
        IsVitalLinkage Γ'.toHypergraph L' →
        ¬ (terminals L' ⊆ bd S')) :
    (cuffs S).ncard ≤ (cuffs S').ncard ∧
      ((cuffs S').ncard = (cuffs S).ncard → p ≤ (Γ'.V ∩ bd S').ncard) := by
  let G' := mapHypergraph π fE Γ'.toHypergraph
  let bd_V' := π '' (Γ'.V ∩ bd S')
  have hG'_bd_eq : G'.vertexSet ∩ bd_V' = π '' (Γ'.V ∩ bd S') := by
    ext v
    change (v ∈ π '' Γ'.V ∧ v ∈ π '' (Γ'.V ∩ bd S')) ↔ v ∈ π '' (Γ'.V ∩ bd S')
    simp only [mem_image, mem_inter_iff]
    constructor
    · rintro ⟨_, y, ⟨hyV, hybd⟩, rfl⟩
      exact ⟨y, ⟨hyV, hybd⟩, rfl⟩
    · rintro ⟨y, ⟨hyV, hybd⟩, rfl⟩
      exact ⟨⟨y, hyV, rfl⟩, y, ⟨hyV, hybd⟩, rfl⟩
  have hbd_card : (G'.vertexSet ∩ bd_V').ncard = (Γ'.V ∩ bd S').ncard := by
    rw [hG'_bd_eq]
    exact (hπ.mono inter_subset_left).ncard_image
  have h6b' : ∀ v ∈ G'.vertexSet,
      v ∈ bd_V' ↔ v ∈ (A ∩ B).vertexSet ∨ v ∈ Γ.V ∩ bd S ∨ v ∉ Γ.V := by
    rintro _ ⟨y, hyV, rfl⟩
    constructor
    · rintro ⟨y', ⟨hy'V, hy'bd⟩, hy'eq⟩
      have hyy' : y = y' := hπ hyV hy'V hy'eq.symm
      subst hyy'
      exact (h6b y hyV).mp hy'bd
    · intro h
      exact ⟨y, ⟨hyV, (h6b y hyV).mpr h⟩, rfl⟩
  have hres := claim_5_2_6 hS hS' cap cap' hΓ_bd h𝒯 hL hL_bd hAB hord hsplit h6a h6b'
    hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos
    (fun hlt hle T_G' L_G' hT_G' hL_G' hterm_G' => by
      rw [hbd_card] at hle
      have hT' : IsTangle Γ'.toHypergraph θ₂ (comapTangle π fE Γ'.toHypergraph T_G') :=
        isTangle_comapHypergraph hπ hfE hT_G'
      let L' := comapHypergraph π fE Γ'.toHypergraph L_G'
      have hL'_le : L' ≤ Γ'.toHypergraph := comapHypergraph_le_self hL_G'.1.1
      have hmapL' : mapHypergraph π fE L' = L_G' := mapHypergraph_comapHypergraph hL_G'.1.1
      have hL' : IsVitalLinkage Γ'.toHypergraph L' := by
        rw [← isVitalLinkage_mapHypergraph hL'_le hπ hfE, hmapL']
        exact hL_G'
      have hterm' : terminals L' ⊆ bd S' := by
        intro y hy
        have hy_map : π y ∈ terminals (mapHypergraph π fE L') := by
          rw [terminals_mapHypergraph hL'_le hπ hfE]
          exact mem_image_of_mem π hy
        rw [hmapL'] at hy_map
        rcases hterm_G' hy_map with ⟨y', ⟨hy'V, hy'bd⟩, hy'eq⟩
        have hyV : y ∈ Γ'.V := hL'_le.vertexSet_subset hy.1
        have hyy' : y = y' := hπ hyV hy'V hy'eq.symm
        exact hyy' ▸ hy'bd
      exact h_ind2 hlt hle _ L' hT' hL' hterm')
    (fun hhomeo hlt T_G' L_G' hT_G' hL_G' hterm_G' => by
      rw [hbd_card] at hlt
      have hT' : IsTangle Γ'.toHypergraph θ₃ (comapTangle π fE Γ'.toHypergraph T_G') :=
        isTangle_comapHypergraph hπ hfE hT_G'
      let L' := comapHypergraph π fE Γ'.toHypergraph L_G'
      have hL'_le : L' ≤ Γ'.toHypergraph := comapHypergraph_le_self hL_G'.1.1
      have hmapL' : mapHypergraph π fE L' = L_G' := mapHypergraph_comapHypergraph hL_G'.1.1
      have hL' : IsVitalLinkage Γ'.toHypergraph L' := by
        rw [← isVitalLinkage_mapHypergraph hL'_le hπ hfE, hmapL']
        exact hL_G'
      have hterm' : terminals L' ⊆ bd S' := by
        intro y hy
        have hy_map : π y ∈ terminals (mapHypergraph π fE L') := by
          rw [terminals_mapHypergraph hL'_le hπ hfE]
          exact mem_image_of_mem π hy
        rw [hmapL'] at hy_map
        rcases hterm_G' hy_map with ⟨y', ⟨hy'V, hy'bd⟩, hy'eq⟩
        have hyV : y ∈ Γ'.V := hL'_le.vertexSet_subset hy.1
        have hyy' : y = y' := hπ hyV hy'V hy'eq.symm
        exact hyy' ▸ hy'bd
      exact h_ind3 hhomeo hlt _ L' hT' hL' hterm')
  rw [hbd_card] at hres
  exact hres

/-! ## 5. Zero-split subspace drawing restriction and `capDrawing` tangle transport -/

/-- For any drawing `H : Drawing S` and closed set `W : Set S`, the hypergraph of `H.interSet W`
equals `(PaintingOrDrawing.drawing H).inter W`. -/
theorem interSet_toHypergraph_eq_inter {S : Type*} [TopologicalSpace S] [T1Space S]
    (H : Surface.Drawing S) {W : Set S} (hW : IsClosed W) :
    (H.interSet W).toHypergraph = (PaintingOrDrawing.drawing H).inter W := by
  have hV_eq : (H.interSet W).V = H.V ∩ W := by
    apply Subset.antisymm
    · refine union_subset inter_subset_left ?_
      refine iUnion₂_subset fun e he x hx => ⟨hx.2, ?_⟩
      exact hW.closure_subset_iff.mpr he.1.2 hx.1
    · intro x ⟨hxV, hxW⟩
      exact Or.inl ⟨⟨hxV, hxW⟩, hxV⟩
  have hE_eq : (H.interSet W).E = {e | e ∈ H.E ∧ e ⊆ W} := by
    rw [Drawing.interSet, Drawing.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq]
    tauto
  refine Hypergraph.ext (Set.ext fun x => ?_) (Set.ext fun e => ?_)
    (funext fun e => funext fun x => propext ?_)
  · change x ∈ (H.interSet W).V ↔ x ∈ H.V ∩ W
    rw [hV_eq]
  · change e ∈ (H.interSet W).E ↔ e ∈ {e | e ∈ H.E ∧ e ⊆ W}
    rw [hE_eq]
  · change (e ∈ (H.interSet W).E ∧ x ∈ (H.interSet W).V ∧ x ∈ closure e) ↔
      (e ∈ H.E ∧ x ∈ H.V ∧ x ∈ closure e) ∧ e ⊆ W ∧ x ∈ W
    rw [hV_eq, hE_eq]
    simp only [mem_ofPred_eq, mem_inter_iff]
    tauto

/-- For any drawing `H : Drawing S` and closed set `W : Set S`, the support of `H.interSet W` is
contained in `W`. -/
theorem interSet_U_subset {S : Type*} [TopologicalSpace S] [T1Space S]
    (H : Surface.Drawing S) {W : Set S} (hW : IsClosed W) :
    (H.interSet W).U ⊆ W := by
  refine union_subset ?_ ?_
  · refine union_subset (inter_subset_left.trans inter_subset_right) ?_
    exact iUnion₂_subset fun e he x hx => hW.closure_subset_iff.mpr he.1.2 hx.1
  · exact iUnion₂_subset fun e he => hW.closure_subset_iff.mpr he.1.2

/-- For any drawing `H : Drawing S` and set `W : Set S`, `(H.interSet W).U ⊆ H.U`. -/
theorem interSet_U_subset_self {S : Type*} [TopologicalSpace S] [T1Space S]
    (H : Surface.Drawing S) (W : Set S) :
    (H.interSet W).U ⊆ H.U := by
  refine union_subset ?_ ?_
  · refine union_subset (inter_subset_right.trans H.V_subset_U) ?_
    exact iUnion₂_subset fun e _ x hx => H.V_subset_U hx.2
  · exact iUnion₂_subset fun e he => (H.closure_subset_U he.1.1).trans Subset.rfl

/-- Transporting `GM12.drawingInSubspace B W hUC` to `S` via `(Subtype.val, image Subtype.val)`
gives `B.toHypergraph`. -/
theorem mapHypergraph_drawingInSubspace_eq {S : Type*} [TopologicalSpace S]
    (B : Surface.Drawing S) (W : Set S) (hUC : B.U ⊆ W) :
    mapHypergraph (Subtype.val : W → S) (image (Subtype.val : W → S))
      (GM12.drawingInSubspace B W hUC).toHypergraph = B.toHypergraph := by
  let B' := GM12.drawingInSubspace B W hUC
  have hVW : B.V ⊆ W := B.V_subset_U.trans hUC
  have hV_eq : (Subtype.val : W → S) '' B'.V = B.V := by
    rw [GM12.drawingInSubspace_V, Subtype.image_preimage_coe]
    exact inter_eq_self_of_subset_right hVW
  have hE_eq : (image (Subtype.val : W → S)) '' B'.E = B.E := by
    rw [GM12.drawingInSubspace_E]
    ext e
    simp only [mem_image]
    constructor
    · rintro ⟨_, ⟨e₀, he₀, rfl⟩, rfl⟩
      have he₀W : e₀ ⊆ W := fun x hx => hUC (he₀.2.1 hx).1
      rw [Subtype.image_preimage_coe, inter_eq_self_of_subset_right he₀W]
      exact he₀
    · intro he
      have heW : e ⊆ W := fun x hx => hUC (he.2.1 hx).1
      refine ⟨(Subtype.val : W → S) ⁻¹' e, ⟨e, he, rfl⟩, ?_⟩
      rw [Subtype.image_preimage_coe, inter_eq_self_of_subset_right heW]
  refine Hypergraph.ext (Set.ext fun x => ?_) (Set.ext fun e => ?_)
    (funext fun e => funext fun x => propext ?_)
  · change x ∈ (Subtype.val : W → S) '' B'.V ↔ x ∈ B.V
    rw [hV_eq]
  · change e ∈ (image (Subtype.val : W → S)) '' B'.E ↔ e ∈ B.E
    rw [hE_eq]
  · change (∃ e' y, (e' ∈ B'.E ∧ y ∈ B'.V ∧ y ∈ closure e') ∧
        (Subtype.val : W → S) '' e' = e ∧ y.1 = x) ↔
      e ∈ B.E ∧ x ∈ B.V ∧ x ∈ closure e
    constructor
    · rintro ⟨e', y, ⟨he', hyV, hycl⟩, rfl, rfl⟩
      rw [GM12.drawingInSubspace_E] at he'
      rcases he' with ⟨e₀, he₀, rfl⟩
      have he₀W : e₀ ⊆ W := fun z hz => hUC (he₀.2.1 hz).1
      have h_im : (Subtype.val : W → S) '' ((Subtype.val : W → S) ⁻¹' e₀) = e₀ := by
        rw [Subtype.image_preimage_coe, inter_eq_self_of_subset_right he₀W]
      rw [h_im]
      rw [GM12.drawingInSubspace_V] at hyV
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
        mem_preimage, h_im] at hycl
      exact ⟨he₀, hyV, hycl⟩
    · rintro ⟨he, hxV, hxcl⟩
      have heW : e ⊆ W := fun z hz => hUC (he.2.1 hz).1
      let y : W := ⟨x, hVW hxV⟩
      refine ⟨(Subtype.val : W → S) ⁻¹' e, y, ⟨?_, ?_, ?_⟩, ?_, rfl⟩
      · rw [GM12.drawingInSubspace_E]
        exact ⟨e, he, rfl⟩
      · rw [GM12.drawingInSubspace_V]
        exact hxV
      · rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
          mem_preimage, Subtype.image_preimage_coe, inter_eq_self_of_subset_right heW]
        exact hxcl
      · rw [Subtype.image_preimage_coe, inter_eq_self_of_subset_right heW]

/-- Under `cap.emb : S → Shat`, `mapHypergraph cap.emb (image cap.emb)` maps
`(PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' W)` to
`(PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter W`. -/
theorem mapHypergraph_cap_inter_eq {S Shat : Type}
    [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : GM19.IsCappedSurface S Shat)
    (Γ : Surface.Drawing S) (W : Set Shat) :
    mapHypergraph cap.emb (image cap.emb)
      ((PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' W)) =
      (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter W := by
  have hinj := cap.isEmbedding.injective
  refine Hypergraph.ext (Set.ext fun x => ?_) (Set.ext fun e => ?_)
    (funext fun e => funext fun x => propext ?_)
  · change x ∈ cap.emb '' (Γ.V ∩ cap.emb ⁻¹' W) ↔ x ∈ (capDrawing hS cap Γ).V ∩ W
    rw [capDrawing_V, image_inter_preimage]
  · change e ∈ (image cap.emb) '' {e₀ ∈ Γ.E | e₀ ⊆ cap.emb ⁻¹' W} ↔
      e ∈ {e' ∈ (capDrawing hS cap Γ).E | e' ⊆ W}
    rw [capDrawing_E]
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨e₀, ⟨he₀, he₀W⟩, rfl⟩
      exact ⟨⟨e₀, he₀, rfl⟩, image_subset_iff.mpr he₀W⟩
    · rintro ⟨⟨e₀, he₀, rfl⟩, heW⟩
      exact ⟨e₀, ⟨he₀, image_subset_iff.mp heW⟩, rfl⟩
  · change (∃ e₀ v₀, ((e₀ ∈ Γ.E ∧ v₀ ∈ Γ.V ∧ v₀ ∈ closure e₀) ∧
        e₀ ⊆ cap.emb ⁻¹' W ∧ v₀ ∈ cap.emb ⁻¹' W) ∧ cap.emb '' e₀ = e ∧ cap.emb v₀ = x) ↔
      ((e ∈ (capDrawing hS cap Γ).E ∧ x ∈ (capDrawing hS cap Γ).V ∧ x ∈ closure e) ∧
        e ⊆ W ∧ x ∈ W)
    have : CompactSpace S := hS.1
    have : T2Space S := hS.2.1
    have : T2Space Shat := cap.isSurface.2.1
    have hcl_map : ∀ e₀ : Set S, closure (cap.emb '' e₀) = cap.emb '' closure e₀ :=
      fun e₀ => Subset.antisymm
        (closure_minimal (image_mono subset_closure)
          ((IsClosed.isCompact isClosed_closure).image cap.isEmbedding.continuous).isClosed)
        (image_closure_subset_closure_image cap.isEmbedding.continuous)
    rw [capDrawing_E, capDrawing_V]
    constructor
    · rintro ⟨e₀, v₀, ⟨⟨he₀, hv₀, hv₀cl⟩, he₀W, hv₀W⟩, rfl, rfl⟩
      refine ⟨⟨⟨e₀, he₀, rfl⟩, ⟨v₀, hv₀, rfl⟩, ?_⟩, image_subset_iff.mpr he₀W, hv₀W⟩
      rw [hcl_map]
      exact mem_image_of_mem cap.emb hv₀cl
    · rintro ⟨⟨⟨e₀, he₀, rfl⟩, ⟨v₀, hv₀, hxv₀⟩, hxcl⟩, heW, hxW⟩
      rw [hcl_map] at hxcl
      rcases hxcl with ⟨v₁, hv₁cl, hv₁x⟩
      have hv₀₁ : v₀ = v₁ := hinj (hxv₀.trans hv₁x.symm)
      subst hv₀₁
      refine ⟨e₀, v₀, ⟨⟨he₀, hv₀, hv₁cl⟩, image_subset_iff.mp heW,
        show v₀ ∈ cap.emb ⁻¹' W by rw [mem_preimage, hxv₀]; exact hxW⟩, rfl, hxv₀⟩

/-- Zero-split subspace drawing restriction for a closed subsurface `W ⊆ Shat`:
restricting `capDrawing hS cap Γ` to `W` via `GM12.drawingInSubspace` produces a drawing
`Γ' : Drawing W` and injective maps `(π, fE)` on `Γ'.V` and `Γ'.E` such that
`mapHypergraph π fE Γ'.toHypergraph = (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' W)`. -/
theorem exists_subspace_drawing_of_closed {S Shat : Type}
    [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : GM19.IsCappedSurface S Shat)
    (Γ : Surface.Drawing S) {W : Set Shat} (hW : IsClosed W) :
    ∃ (Γ' : Surface.Drawing W) (π : W → S) (fE : Set W → Set S),
      InjOn π Γ'.V ∧
      InjOn fE Γ'.E ∧
      mapHypergraph π fE Γ'.toHypergraph =
        (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' W) ∧
      (∀ y ∈ Γ'.V, cap.emb (π y) = y.1 ∧ π y ∈ Γ.V ∧ y.1 ∈ W) ∧
      (∀ y ∈ Γ'.U, y.1 ∈ cap.emb '' Γ.U ∧ (y.1 ∈ cap.emb '' Γ.V → y ∈ Γ'.V)) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have : T2Space Shat := cap.isSurface.2.1
  let Γ_hat := capDrawing hS cap Γ
  let B_hat := Γ_hat.interSet W
  have hUC : B_hat.U ⊆ W := interSet_U_subset Γ_hat hW
  let Γ' : Surface.Drawing W := GM12.drawingInSubspace B_hat W hUC
  have hU_spec : ∀ y ∈ Γ'.U, y.1 ∈ cap.emb '' Γ.U ∧ (y.1 ∈ cap.emb '' Γ.V → y ∈ Γ'.V) := by
    intro y hyU
    have hyB : y.1 ∈ B_hat.U := by rwa [GM12.drawingInSubspace_U] at hyU
    have hy_hatU : y.1 ∈ Γ_hat.U := interSet_U_subset_self Γ_hat W hyB
    rw [capDrawing_U] at hy_hatU
    refine ⟨hy_hatU, fun hy_hatV => ?_⟩
    rw [GM12.drawingInSubspace_V]
    have hV_eq : B_hat.V = Γ_hat.V ∩ W :=
      congrArg Hypergraph.vertexSet (interSet_toHypergraph_eq_inter Γ_hat hW)
    change y.1 ∈ B_hat.V
    rw [hV_eq, capDrawing_V]
    exact ⟨hy_hatV, y.2⟩
  have h_sub_map :
      mapHypergraph (Subtype.val : W → Shat) (image (Subtype.val : W → Shat)) Γ'.toHypergraph =
        (PaintingOrDrawing.drawing Γ_hat).inter W :=
    (mapHypergraph_drawingInSubspace_eq B_hat W hUC).trans (interSet_toHypergraph_eq_inter Γ_hat hW)
  have h_cap_map := mapHypergraph_cap_inter_eq hS cap Γ W
  have hinj := cap.isEmbedding.injective
  have hV_range : ∀ y ∈ Γ'.V, y.1 ∈ cap.emb '' Γ.V ∧ y.1 ∈ W := by
    intro y hy
    have hyB : y.1 ∈ B_hat.V := by rwa [GM12.drawingInSubspace_V] at hy
    have hV_eq : B_hat.V = Γ_hat.V ∩ W :=
      congrArg Hypergraph.vertexSet (interSet_toHypergraph_eq_inter Γ_hat hW)
    rw [hV_eq, capDrawing_V] at hyB
    exact hyB
  have hE_range : ∀ e' ∈ Γ'.E, (Subtype.val : W → Shat) '' e' ∈ (image cap.emb) '' Γ.E := by
    intro e' he'
    have he'B : (Subtype.val : W → Shat) '' e' ∈ B_hat.E := by
      change (Subtype.val : W → Shat) '' e' ∈ B_hat.toHypergraph.edgeSet
      rw [← mapHypergraph_drawingInSubspace_eq B_hat W hUC]
      exact mem_image_of_mem _ he'
    have hE_eq : B_hat.E = {e ∈ Γ_hat.E | e ⊆ W} :=
      congrArg Hypergraph.edgeSet (interSet_toHypergraph_eq_inter Γ_hat hW)
    rw [hE_eq, capDrawing_E] at he'B
    exact he'B.1
  let fE : Set W → Set S := fun e' => cap.emb ⁻¹' ((Subtype.val : W → Shat) '' e')
  by_cases hS_ne : Nonempty S
  · haveI := hS_ne
    let π₀ : W → S := fun y => Function.invFun cap.emb y.1
    have hπ₀_spec : ∀ y ∈ Γ'.V, cap.emb (π₀ y) = y.1 ∧ π₀ y ∈ Γ.V ∧ y.1 ∈ W := by
      intro y hy
      rcases hV_range y hy with ⟨⟨v, hv, hvy⟩, hyW⟩
      have hinv : π₀ y = v := by
        dsimp [π₀]
        rw [← hvy]
        exact Function.leftInverse_invFun hinj v
      exact ⟨hinv ▸ hvy, hinv ▸ hv, hyW⟩
    have hπ₀_inj : InjOn π₀ Γ'.V := by
      intro y₁ hy₁ y₂ hy₂ h_eq
      apply Subtype.ext
      rw [← (hπ₀_spec y₁ hy₁).1, ← (hπ₀_spec y₂ hy₂).1, h_eq]
    have hfE_spec : ∀ e' ∈ Γ'.E,
        cap.emb '' (fE e') = (Subtype.val : W → Shat) '' e' ∧ fE e' ∈ Γ.E := by
      intro e' he'
      rcases hE_range e' he' with ⟨e₀, he₀, he₀_eq⟩
      have hfE_eq : fE e' = e₀ := by
        dsimp [fE]
        rw [← he₀_eq, preimage_image_eq _ hinj]
      exact ⟨hfE_eq ▸ he₀_eq, hfE_eq ▸ he₀⟩
    have hfE_inj : InjOn fE Γ'.E := by
      intro e₁ he₁ e₂ he₂ h_eq
      have himg : (Subtype.val : W → Shat) '' e₁ = (Subtype.val : W → Shat) '' e₂ := by
        rw [← (hfE_spec e₁ he₁).1, ← (hfE_spec e₂ he₂).1, h_eq]
      exact Set.image_injective.mpr Subtype.val_injective himg
    refine ⟨Γ', π₀, fE, hπ₀_inj, hfE_inj, ?_, hπ₀_spec, hU_spec⟩
    have h_comp : mapHypergraph cap.emb (image cap.emb)
        (mapHypergraph π₀ fE Γ'.toHypergraph) =
        mapHypergraph cap.emb (image cap.emb)
          ((PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' W)) := by
      rw [h_cap_map, ← h_sub_map]
      refine Hypergraph.ext (Set.ext fun x => ?_) (Set.ext fun e => ?_)
        (funext fun e => funext fun x => propext ?_)
      · change x ∈ cap.emb '' (π₀ '' Γ'.V) ↔ x ∈ (Subtype.val : W → Shat) '' Γ'.V
        simp only [mem_image]
        constructor
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
          exact ⟨y, hy, (hπ₀_spec y hy).1.symm⟩
        · rintro ⟨y, hy, rfl⟩
          exact ⟨π₀ y, ⟨y, hy, rfl⟩, (hπ₀_spec y hy).1⟩
      · change e ∈ (image cap.emb) '' (fE '' Γ'.E) ↔
          e ∈ (image (Subtype.val : W → Shat)) '' Γ'.E
        simp only [mem_image]
        constructor
        · rintro ⟨_, ⟨e', he', rfl⟩, rfl⟩
          exact ⟨e', he', (hfE_spec e' he').1.symm⟩
        · rintro ⟨e', he', rfl⟩
          exact ⟨fE e', ⟨e', he', rfl⟩, (hfE_spec e' he').1⟩
      · change (∃ e₁ v₁, (∃ e' y, (e' ∈ Γ'.E ∧ y ∈ Γ'.V ∧ y ∈ closure e') ∧ fE e' = e₁ ∧ π₀ y = v₁) ∧
            cap.emb '' e₁ = e ∧ cap.emb v₁ = x) ↔
          ∃ e' y, (e' ∈ Γ'.E ∧ y ∈ Γ'.V ∧ y ∈ closure e') ∧
            (Subtype.val : W → Shat) '' e' = e ∧ y.1 = x
        constructor
        · rintro ⟨_, _, ⟨e', y, ⟨he', hy, hycl⟩, rfl, rfl⟩, rfl, rfl⟩
          exact ⟨e', y, ⟨he', hy, hycl⟩, (hfE_spec e' he').1.symm, (hπ₀_spec y hy).1.symm⟩
        · rintro ⟨e', y, ⟨he', hy, hycl⟩, rfl, rfl⟩
          exact ⟨fE e', π₀ y, ⟨e', y, ⟨he', hy, hycl⟩, rfl, rfl⟩,
            (hfE_spec e' he').1, (hπ₀_spec y hy).1⟩
    refine Hypergraph.ext (Set.ext fun v => ?_) (Set.ext fun e => ?_)
      (funext fun e => funext fun v => propext ?_)
    · have hv := congrArg (fun H => cap.emb v ∈ H.vertexSet) h_comp
      dsimp [mapHypergraph] at hv
      rw [hinj.mem_set_image, hinj.mem_set_image] at hv
      exact Eq.to_iff hv
    · have he := congrArg (fun H => cap.emb '' e ∈ H.edgeSet) h_comp
      dsimp [mapHypergraph] at he
      rw [(Set.image_injective.mpr hinj).mem_set_image,
        (Set.image_injective.mpr hinj).mem_set_image] at he
      exact Eq.to_iff he
    · have hinc := congrArg (fun H => H.Inc (cap.emb '' e) (cap.emb v)) h_comp
      change (∃ e₀ v₀, (mapHypergraph π₀ fE Γ'.toHypergraph).Inc e₀ v₀ ∧
          cap.emb '' e₀ = cap.emb '' e ∧ cap.emb v₀ = cap.emb v) =
        (∃ e₀ v₀, ((PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' W)).Inc e₀ v₀ ∧
          cap.emb '' e₀ = cap.emb '' e ∧ cap.emb v₀ = cap.emb v) at hinc
      constructor
      · intro h
        have h' : ∃ e₀ v₀, (mapHypergraph π₀ fE Γ'.toHypergraph).Inc e₀ v₀ ∧
            cap.emb '' e₀ = cap.emb '' e ∧ cap.emb v₀ = cap.emb v := ⟨e, v, h, rfl, rfl⟩
        rw [hinc] at h'
        rcases h' with ⟨e₀, v₀, h₀, he₀, hv₀⟩
        rwa [Set.image_injective.mpr hinj he₀, hinj hv₀] at h₀
      · intro h
        have h' : ∃ e₀ v₀, ((PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' W)).Inc e₀ v₀ ∧
            cap.emb '' e₀ = cap.emb '' e ∧ cap.emb v₀ = cap.emb v := ⟨e, v, h, rfl, rfl⟩
        rw [← hinc] at h'
        rcases h' with ⟨e₀, v₀, h₀, he₀, hv₀⟩
        rwa [Set.image_injective.mpr hinj he₀, hinj hv₀] at h₀
  · haveI : IsEmpty S := not_nonempty_iff.mp hS_ne
    have hV_emp : Γ.V = ∅ := eq_empty_of_forall_notMem fun x => isEmptyElim x
    have hE_emp : Γ.E = ∅ := by
      refine eq_empty_of_forall_notMem fun e he => ?_
      rcases he.1 with ⟨x, _⟩
      exact isEmptyElim x
    have hV'_emp : Γ'.V = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => ?_
      rcases (hV_range y hy).1 with ⟨v, _, _⟩
      exact isEmptyElim v
    have hE'_emp : Γ'.E = ∅ := by
      refine eq_empty_of_forall_notMem fun e' he' => ?_
      rcases hE_range e' he' with ⟨e₀, he₀, _⟩
      rw [hE_emp] at he₀
      exact he₀
    have h_univ : (range cap.emb)ᶜ = ∅ := by
      rw [cap.compl_eq]
      ext z
      simp only [mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
      rintro C ⟨x, _⟩
      exact isEmptyElim x
    have h_range : range cap.emb = univ := compl_empty_iff.mp h_univ
    haveI : IsEmpty W := ⟨fun y => by
      have hy : y.1 ∈ range cap.emb := h_range.symm ▸ mem_univ y.1
      rcases hy with ⟨x, _⟩
      exact isEmptyElim x⟩
    refine ⟨Γ', isEmptyElim, fE, ?_, ?_, ?_, fun y => isEmptyElim y, fun y => isEmptyElim y⟩
    · intro y; exact isEmptyElim y
    · intro e' he'; rw [hE'_emp] at he'; exact False.elim he'
    · refine Hypergraph.ext (Set.ext fun x => isEmptyElim x) (Set.ext fun e => ?_)
        (funext fun e => funext fun x => propext (isEmptyElim x))
      change e ∈ fE '' Γ'.E ↔ e ∈ {e₀ ∈ Γ.E | e₀ ⊆ cap.emb ⁻¹' W}
      rw [hE'_emp, hE_emp]
      simp

/-! ## 6. Lifting a loopless drawing across `IsCutting ψ F` (`exists_lifted_drawing_of_isCutting`) -/

section LiftDrawing

/-- A surface containing a line is infinite. -/
theorem infinite_of_isLine {S : Type*} [TopologicalSpace S] {F : Set S} (hF : IsLine F) :
    Infinite S := by
  rcases hF with ⟨f⟩
  haveI : Infinite (Icc (0 : ℝ) 1) := Set.Icc.infinite zero_lt_one
  exact Infinite.of_injective (fun t : Icc (0 : ℝ) 1 => (f t).1)
    (Subtype.val_injective.comp f.injective)

/-- A surface containing an `O`-arc is infinite. -/
theorem infinite_of_isOArc {S : Type*} [TopologicalSpace S] {F : Set S} (hF : IsOArc F) :
    Infinite S := by
  rcases hF with ⟨e⟩
  haveI : Infinite (Icc (0 : ℝ) 1) := Set.Icc.infinite zero_lt_one
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc 0 Real.pi :=
    Icc_subset_Icc_right (by linarith [Real.two_le_pi])
  have hinj_cos : InjOn Real.cos (Icc (0 : ℝ) 1) :=
    (Real.strictAntiOn_cos.mono hsub).injOn
  have hinj_exp : Function.Injective (fun t : Icc (0 : ℝ) 1 => Circle.exp t.1) := by
    intro t₁ t₂ h
    have hre : (Circle.exp t₁.1 : ℂ).re = (Circle.exp t₂.1 : ℂ).re :=
      congrArg Complex.re (congrArg Subtype.val h)
    simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] at hre
    exact Subtype.ext (hinj_cos t₁.2 t₂.2 hre)
  exact Infinite.of_injective (fun t : Icc (0 : ℝ) 1 => (e (Circle.exp t.1)).1)
    (Subtype.val_injective.comp (e.injective.comp hinj_exp))

/-- For a line `closure e` with distinct ends `u ≠ v` (`closure e \ {u, v} = e`), `e` is connected
near each point of `tilde e = {u, v}`. -/
private lemma isConnectedNear_of_isLineWithEnds {S : Type} [TopologicalSpace S] [T2Space S]
    {e : Set S} {u v : S} (he_diff : closure e \ {u, v} = e)
    (hL : IsLineWithEnds (closure e) u v) {w : S} (hw : w ∈ tilde e) :
    GM19.IsConnectedNear e w := by
  obtain ⟨f, hf0, hf1⟩ := hL
  let T : Set (Icc (0 : ℝ) 1) := {(0 : Icc (0 : ℝ) 1), (1 : Icc (0 : ℝ) 1)}
  have hT_fin : T.Finite := (finite_singleton _).insert _
  have himg : (fun t : Icc (0 : ℝ) 1 => (f t).1) '' Tᶜ = e := by
    apply Eq.trans _ he_diff
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(f t).2, ?_⟩
      rintro (hxu | hxv)
      · apply ht; left
        exact f.injective (Subtype.ext (hxu.trans hf0.symm))
      · apply ht; right
        exact f.injective (Subtype.ext (hxv.trans hf1.symm))
    · rintro ⟨hxcl, hxuv⟩
      refine ⟨f.symm ⟨x, hxcl⟩, ?_, by simp⟩
      rintro (h0 | h1)
      · apply hxuv; left
        have := congrArg (fun t => (f t).1) h0
        simpa [hf0] using this
      · apply hxuv; right
        have := congrArg (fun t => (f t).1) (mem_singleton_iff.mp h1)
        simpa [hf1] using this
  have hw_uv : w = u ∨ w = v := by
    by_contra hnot
    have hwe : w ∈ e := by
      rw [← he_diff]
      exact ⟨hw.1, hnot⟩
    exact hw.2 hwe
  rcases hw_uv with rfl | rfl
  · have h0 : ∀ W ∈ 𝓝 (0 : Icc (0 : ℝ) 1),
        ∃ B ⊆ Tᶜ ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 (0 : Icc (0 : ℝ) 1), Tᶜ ∩ W' ⊆ B := by
      refine GM19.connected_near_extreme (convex_Icc (0 : ℝ) 1) ?_ hT_fin (Or.inl rfl)
      have h_eq : Icc (0 : ℝ) 1 \ {((0 : Icc (0 : ℝ) 1) : ℝ)} = Ioc (0 : ℝ) 1 := Icc_sdiff_left
      rw [h_eq]
      exact convex_Ioc (0 : ℝ) 1
    have h := GM19.isConnectedNear_of_homeo f h0
    rwa [himg, hf0] at h
  · have h1 : ∀ W ∈ 𝓝 (1 : Icc (0 : ℝ) 1),
        ∃ B ⊆ Tᶜ ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 (1 : Icc (0 : ℝ) 1), Tᶜ ∩ W' ⊆ B := by
      refine GM19.connected_near_extreme (convex_Icc (0 : ℝ) 1) ?_ hT_fin (Or.inr rfl)
      have h_eq : Icc (0 : ℝ) 1 \ {((1 : Icc (0 : ℝ) 1) : ℝ)} = Ico (0 : ℝ) 1 := Icc_sdiff_right
      rw [h_eq]
      exact convex_Ico (0 : ℝ) 1
    have h := GM19.isConnectedNear_of_homeo f h1
    rwa [himg, hf1] at h

/-- Under a cutting map `hcm : GM19.IsCutMap ψ F` with `IsClosed F`, if `A ⊆ Fᶜ` is connected near
`v`, then `closure (ψ ⁻¹' A)` has at most one point over `v`. -/
private lemma eq_of_mem_closure_preimage_of_isCutMap {Y S : Type}
    [TopologicalSpace Y] [TopologicalSpace S] [CompactSpace Y] [T2Space Y] [T2Space S]
    {ψ : Y → S} {F : Set S} (hcm : GM19.IsCutMap ψ F) (hF : IsClosed F)
    {A : Set S} {v : S} (hA : A ⊆ Fᶜ) (hloc : GM19.IsConnectedNear A v)
    {y₁ y₂ : Y} (h₁ : ψ y₁ = v) (h₂ : ψ y₂ = v)
    (hc₁ : y₁ ∈ closure (ψ ⁻¹' A)) (hc₂ : y₂ ∈ closure (ψ ⁻¹' A)) :
    y₁ = y₂ := by
  by_contra hne
  have hfin : (ψ ⁻¹' {v}).Finite := hcm.2.2.2.1 v
  have hcomp : IsCompact (ψ ⁻¹' {v} \ {y₁}) := (hfin.subset sdiff_subset).isCompact
  obtain ⟨U₁, U₂, hU₁, hU₂, hy₁, hy₂, hdis⟩ :=
    SeparatedNhds.of_isCompact_isCompact (isCompact_singleton (x := y₁)) hcomp
      (by rw [disjoint_singleton_left]; exact fun hx => hx.2 rfl)
  have hy₁U : y₁ ∈ U₁ := hy₁ rfl
  have hcl_map : IsClosedMap ψ := GM19.isClosedMap_of_isCutMap hcm
  have hWo : IsOpen (ψ '' (U₁ ∪ U₂)ᶜ)ᶜ :=
    (hcl_map _ (hU₁.union hU₂).isClosed_compl).isOpen_compl
  have hvW : v ∈ (ψ '' (U₁ ∪ U₂)ᶜ)ᶜ := by
    rintro ⟨y, hy, hyv⟩
    by_cases hyy₁ : y = y₁
    · exact hy (Or.inl (hyy₁ ▸ hy₁U))
    · exact hy (Or.inr (hy₂ ⟨hyv, hyy₁⟩))
  obtain ⟨B, hBsub, hBc, W', hW', hsub⟩ := hloc _ (hWo.mem_nhds hvW)
  have hBF : B ⊆ Fᶜ := fun z hz => hA (hBsub hz).1
  have hcov : ψ ⁻¹' B ⊆ U₁ ∪ U₂ := by
    intro y hy
    by_contra hny
    exact (hBsub hy).2 ⟨y, hny, rfl⟩
  have hpt : ∀ {w : Y} {U : Set Y}, ψ w = v → IsOpen U → w ∈ U → w ∈ closure (ψ ⁻¹' A) →
      (ψ ⁻¹' B ∩ U).Nonempty := by
    intro w U hw hU hwU hc
    have hn : U ∩ ψ ⁻¹' W' ∈ 𝓝 w :=
      Filter.inter_mem (hU.mem_nhds hwU)
        (hcm.1.continuousAt.preimage_mem_nhds (hw.symm ▸ hW'))
    obtain ⟨p, ⟨hpU, hpW⟩, hpA⟩ := mem_closure_iff_nhds.mp hc _ hn
    exact ⟨p, hsub ⟨hpA, hpW⟩, hpU⟩
  have hy₂U : y₂ ∈ U₂ := hy₂ ⟨h₂, fun hx => hne hx.symm⟩
  obtain ⟨p, -, hp₁, hp₂⟩ :=
    GM19.isPreconnected_preimage_of_isCutMap hcm hF hBF hBc U₁ U₂ hU₁ hU₂ hcov
      (hpt h₁ hU₁ hy₁U hc₁) (hpt h₂ hU₂ hy₂U hc₂)
  exact disjoint_left.mp hdis hp₁ hp₂

/-- Under `hcm : GM19.IsCutMap ψ F` with `IsClosed F`, for any non-loop edge `e ∈ B.E` with
`e ⊆ Fᶜ`, `ψ` maps `closure (ψ ⁻¹' e)` homeomorphically onto `closure e`. -/
private noncomputable def homeoClosureEdgeOfCutMap {Y S : Type}
    [TopologicalSpace Y] [TopologicalSpace S] [CompactSpace Y] [T2Space Y] [T2Space S]
    {ψ : Y → S} {F : Set S} (hcm : GM19.IsCutMap ψ F) (hF : IsClosed F)
    (B : Surface.Drawing S) {e : Set S} (he : e ∈ B.E) (heF : e ⊆ Fᶜ)
    {u v : S} (huv : u ≠ v) (hcap : closure e ∩ B.V = {u, v})
    (hL : IsLineWithEnds (closure e) u v) :
    ↥(closure (ψ ⁻¹' e)) ≃ₜ ↥(closure e) := by
  have hcl_map : IsClosedMap ψ := GM19.isClosedMap_of_isCutMap hcm
  have h_im_cl : ψ '' closure (ψ ⁻¹' e) = closure e := by
    have hsur : ψ '' (ψ ⁻¹' e) = e := hcm.2.1.image_preimage e
    refine Subset.antisymm ?_ ?_
    · exact (image_closure_subset_closure_image hcm.1).trans (closure_mono hsur.subset)
    · conv_lhs => rw [← hsur]
      exact hcl_map.closure_image_subset _
  have he_diff : closure e \ {u, v} = e := by
    rw [← hcap, sdiff_self_inter]
    exact B.closure_diff_V he
  have hbij : Function.Bijective (fun x : ↥(closure (ψ ⁻¹' e)) =>
      (⟨ψ x.1, h_im_cl ▸ mem_image_of_mem ψ x.2⟩ : ↥(closure e))) := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have hxy' : ψ x = ψ y := congrArg Subtype.val hxy
      apply Subtype.ext
      by_cases hxe : ψ x ∈ e
      · exact hcm.2.2.1 (heF hxe) (heF (hxy' ▸ hxe)) hxy'
      · have hxcl : ψ x ∈ closure e := h_im_cl ▸ mem_image_of_mem ψ hx
        have hloc := isConnectedNear_of_isLineWithEnds he_diff hL ⟨hxcl, hxe⟩
        exact eq_of_mem_closure_preimage_of_isCutMap hcm hF heF hloc rfl hxy'.symm hx hy
    · rintro ⟨z, hz⟩
      rw [← h_im_cl] at hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  haveI : CompactSpace ↥(closure (ψ ⁻¹' e)) :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ hbij)
    ((hcm.1.comp continuous_subtype_val).subtype_mk _)

/-- Given a loopless drawing `B : Drawing S` (`∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard`), a
closed set `F ⊆ S` with `F ∩ B.U ⊆ B.V`, and a cutting `hcut : IsCutting ψ F` (`ψ : Y → S`), every
edge `e ∈ B.E` has distinct ends `u ≠ v` and `closure e` is a line with ends `u` and `v`. -/
private lemma edge_isLineWithEnds_of_loopless {S : Type} [TopologicalSpace S]
    (B : Surface.Drawing S) (hB_loopless : ∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard)
    {e : Set S} (he : e ∈ B.E) :
    ∃ u v : S, u ≠ v ∧ closure e ∩ B.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
  rcases B.edge_cond e he with ⟨u, v, huv, hcap, hL⟩ | ⟨u, hcap, _⟩
  · exact ⟨u, v, huv, hcap, hL⟩
  · exfalso
    have hends : B.toHypergraph.ends e = {u} := by
      ext x
      change (e ∈ B.E ∧ x ∈ B.V ∧ x ∈ closure e) ↔ x ∈ {u}
      rw [and_iff_right he, and_comm, ← mem_inter_iff, hcap]
    have h1 : (B.toHypergraph.ends e).ncard = 1 := by rw [hends, ncard_singleton]
    have h2 := hB_loopless e he
    omega

/-- Under a cutting map `hcm : GM19.IsCutMap ψ F` with `IsClosed F` and `F ∩ B.U ⊆ B.V`, the
preimage `ψ ⁻¹' e` of any non-loop edge `e ∈ B.E` is nonempty and path-connected, and `ψ` is
injective on `closure (ψ ⁻¹' e)` with `ψ '' (closure (ψ ⁻¹' e)) = closure e`. -/
private lemma lift_edge_props_of_isCutMap {Y S : Type}
    [TopologicalSpace Y] [TopologicalSpace S] [CompactSpace Y] [T2Space Y] [T2Space S]
    {ψ : Y → S} {F : Set S} (hcm : GM19.IsCutMap ψ F) (hF : IsClosed F)
    (B : Surface.Drawing S) (hB_loopless : ∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard)
    (hFB : F ∩ B.U ⊆ B.V) {e : Set S} (he : e ∈ B.E) :
    (ψ ⁻¹' e).Nonempty ∧
    IsPathConnected (ψ ⁻¹' e) ∧
    InjOn ψ (closure (ψ ⁻¹' e)) ∧
    ψ '' (closure (ψ ⁻¹' e)) = closure e ∧
    (∃ u' v' : Y, u' ≠ v' ∧ closure (ψ ⁻¹' e) ∩ ψ ⁻¹' B.V = {u', v'} ∧
      IsLineWithEnds (closure (ψ ⁻¹' e)) u' v') := by
  have heF : e ⊆ Fᶜ := fun x hxe hxF => (he.2.1 hxe).2 (hFB ⟨hxF, (he.2.1 hxe).1⟩)
  obtain ⟨u, v, huv, hcap, hL⟩ := edge_isLineWithEnds_of_loopless B hB_loopless he
  let he_homeo := homeoClosureEdgeOfCutMap hcm hF B he heF huv hcap hL
  have h_apply : ∀ y : ↥(closure (ψ ⁻¹' e)), (he_homeo y).1 = ψ y.1 := fun _ => rfl
  have h_symm_ψ : ∀ z : ↥(closure e), ψ (he_homeo.symm z).1 = z.1 := by
    intro z
    have := h_apply (he_homeo.symm z)
    rw [Homeomorph.apply_symm_apply] at this
    exact this.symm
  have h_inj : InjOn ψ (closure (ψ ⁻¹' e)) := by
    intro y₁ hy₁ y₂ hy₂ h_eq
    have hsub : he_homeo ⟨y₁, hy₁⟩ = he_homeo ⟨y₂, hy₂⟩ := Subtype.ext h_eq
    exact congrArg Subtype.val (he_homeo.injective hsub)
  have h_im_cl : ψ '' (closure (ψ ⁻¹' e)) = closure e := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (he_homeo ⟨y, hy⟩).2
    · intro hx
      exact ⟨(he_homeo.symm ⟨x, hx⟩).1, (he_homeo.symm ⟨x, hx⟩).2, h_symm_ψ ⟨x, hx⟩⟩
  obtain ⟨x₀, hx₀⟩ := he.1
  obtain ⟨y₀, rfl⟩ := hcm.2.1 x₀
  have hne : (ψ ⁻¹' e).Nonempty := ⟨y₀, hx₀⟩
  have hpc : IsPathConnected (ψ ⁻¹' e) := by
    refine ⟨y₀, hx₀, fun {y} hy => ?_⟩
    obtain ⟨γ, hγ⟩ := he.2.2.1.joinedIn (ψ y₀) hx₀ (ψ y) hy
    let γ_cl : unitInterval → ↥(closure e) := fun t => ⟨γ t, subset_closure (hγ t)⟩
    have hγ_cl_cont : Continuous γ_cl := γ.continuous.subtype_mk _
    let γ' : unitInterval → Y := fun t => (he_homeo.symm (γ_cl t)).1
    have hγ'_cont : Continuous γ' :=
      continuous_subtype_val.comp (he_homeo.symm.continuous.comp hγ_cl_cont)
    have hγ'_0 : γ' 0 = y₀ := by
      have hψ0 : ψ (γ' 0) = ψ y₀ := by
        change ψ (he_homeo.symm (γ_cl 0)).1 = ψ y₀
        rw [h_symm_ψ]
        exact γ.source
      exact h_inj (he_homeo.symm (γ_cl 0)).2 (subset_closure hx₀) hψ0
    have hγ'_1 : γ' 1 = y := by
      have hψ1 : ψ (γ' 1) = ψ y := by
        change ψ (he_homeo.symm (γ_cl 1)).1 = ψ y
        rw [h_symm_ψ]
        exact γ.target
      exact h_inj (he_homeo.symm (γ_cl 1)).2 (subset_closure hy) hψ1
    refine ⟨{ toFun := γ', continuous_toFun := hγ'_cont, source' := hγ'_0, target' := hγ'_1 },
      fun t => ?_⟩
    change ψ (γ' t) ∈ e
    dsimp [γ', γ_cl]
    rw [h_symm_ψ]
    exact hγ t
  have hu_cl : u ∈ closure e := (hcap.symm ▸ Or.inl rfl : u ∈ closure e ∩ B.V).1
  have hv_cl : v ∈ closure e := (hcap.symm ▸ Or.inr rfl : v ∈ closure e ∩ B.V).1
  let u' : Y := (he_homeo.symm ⟨u, hu_cl⟩).1
  let v' : Y := (he_homeo.symm ⟨v, hv_cl⟩).1
  have hu'_ψ : ψ u' = u := h_symm_ψ ⟨u, hu_cl⟩
  have hv'_ψ : ψ v' = v := h_symm_ψ ⟨v, hv_cl⟩
  have hu'v' : u' ≠ v' := fun h => huv (hu'_ψ.symm.trans (congrArg ψ h |>.trans hv'_ψ))
  have hcap' : closure (ψ ⁻¹' e) ∩ ψ ⁻¹' B.V = {u', v'} := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hycl, hyV⟩
      have hψy : ψ y ∈ closure e ∩ B.V := ⟨h_im_cl ▸ mem_image_of_mem ψ hycl, hyV⟩
      rw [hcap] at hψy
      rcases hψy with hψu | hψv
      · left
        exact h_inj hycl (he_homeo.symm ⟨u, hu_cl⟩).2 (hψu.trans hu'_ψ.symm)
      · right
        exact h_inj hycl (he_homeo.symm ⟨v, hv_cl⟩).2 (mem_singleton_iff.mp hψv |>.trans hv'_ψ.symm)
    · rintro (rfl | rfl)
      · exact ⟨(he_homeo.symm ⟨u, hu_cl⟩).2, hu'_ψ.symm ▸ (hcap.symm ▸ Or.inl rfl : u ∈ closure e ∩ B.V).2⟩
      · exact ⟨(he_homeo.symm ⟨v, hv_cl⟩).2, hv'_ψ.symm ▸ (hcap.symm ▸ Or.inr rfl : v ∈ closure e ∩ B.V).2⟩
  obtain ⟨f, hf0, hf1⟩ := hL
  have hL' : IsLineWithEnds (closure (ψ ⁻¹' e)) u' v' := by
    refine ⟨f.trans he_homeo.symm, ?_, ?_⟩
    · change (he_homeo.symm (f 0)).1 = u'
      have hf0' : f 0 = ⟨u, hu_cl⟩ := Subtype.ext hf0
      rw [hf0']
    · change (he_homeo.symm (f 1)).1 = v'
      have hf1' : f 1 = ⟨v, hv_cl⟩ := Subtype.ext hf1
      rw [hf1']
  exact ⟨hne, hpc, h_inj, h_im_cl, u', v', hu'v', hcap', hL'⟩

/-- Under `hcm : GM19.IsCutMap ψ F` with `IsClosed F` and `F ∩ B.U ⊆ B.V`, the arc components of
`ψ ⁻¹' B.U \ ψ ⁻¹' B.V` are `(preimage ψ) '' B.E`. -/
private lemma arcComponentsIn_preimage_cutMap {Y S : Type}
    [TopologicalSpace Y] [TopologicalSpace S] [CompactSpace Y] [T2Space Y] [T2Space S]
    {ψ : Y → S} {F : Set S} (hcm : GM19.IsCutMap ψ F) (hF : IsClosed F)
    (B : Surface.Drawing S) (hB_loopless : ∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard)
    (hFB : F ∩ B.U ⊆ B.V) :
    arcComponentsIn (ψ ⁻¹' B.U \ ψ ⁻¹' B.V) = (preimage ψ) '' B.E := by
  refine GM19.arcComponentsIn_of_pieces (B.finite_edges.image _) ?_ ?_ ?_ ?_
  · rintro _ ⟨e, he, rfl⟩
    exact (lift_edge_props_of_isCutMap hcm hF B hB_loopless hFB he).2.1
  · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ hne
    refine disjoint_left.mpr fun y hy₁ hy₂ => hne ?_
    rw [B.edge_eq_of_mem he₁ he₂ hy₁ hy₂]
  · rintro _ ⟨e, he, rfl⟩ y ⟨hycl, hyU, hyV⟩
    have h_im := (lift_edge_props_of_isCutMap hcm hF B hB_loopless hFB he).2.2.2.1
    have hψy : ψ y ∈ closure e \ B.V := ⟨h_im ▸ mem_image_of_mem ψ hycl, hyV⟩
    rwa [B.closure_diff_V he] at hψy
  · ext y
    constructor
    · rintro ⟨hyU, hyV⟩
      obtain ⟨e, he, hye⟩ := GM19.exists_arcComp_superset (F := B.U \ B.V)
        (isPathConnected_singleton (ψ y)) (singleton_subset_iff.mpr ⟨hyU, hyV⟩)
      exact ⟨ψ ⁻¹' e, ⟨e, he, rfl⟩, hye rfl⟩
    · rintro ⟨_, ⟨e, he, rfl⟩, hye⟩
      exact he.2.1 hye

/-- Given a loopless drawing `B : Drawing S` (`∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard`), a
closed set `F ⊆ S` with `F ∩ B.U ⊆ B.V`, and a cutting `hcut : IsCutting ψ F` (`ψ : Y → S`), the
preimage `(ψ ⁻¹' B.U, ψ ⁻¹' B.V)` is a drawing `B' : Drawing Y` with `B'.E = (preimage ψ) '' B.E`. -/
def liftDrawing {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (hS : IsSurface S)
    {ψ : Y → S} {F : Set S} (hcut : IsCutting ψ F) (hF : IsClosed F)
    (B : Surface.Drawing S) (hB_loopless : ∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard)
    (hFB : F ∩ B.U ⊆ B.V) :
    Surface.Drawing Y where
  U := ψ ⁻¹' B.U
  V := ψ ⁻¹' B.V
  V_subset_U := preimage_mono B.V_subset_U
  isClosed_U := B.isClosed_U.preimage hcut.1
  finite_V := B.finite_V.preimage' fun y _ => (GM19.IsCutting.isCutMap hcut).2.2.2.1 y
  finite_edges := by
    haveI : CompactSpace Y := hY.1
    haveI : T2Space Y := hY.2.1
    haveI : T2Space S := hS.2.1
    rw [arcComponentsIn_preimage_cutMap (GM19.IsCutting.isCutMap hcut) hF B hB_loopless hFB]
    exact B.finite_edges.image _
  edge_cond := by
    haveI : CompactSpace Y := hY.1
    haveI : T2Space Y := hY.2.1
    haveI : T2Space S := hS.2.1
    intro e' he'
    rw [arcComponentsIn_preimage_cutMap (GM19.IsCutting.isCutMap hcut) hF B hB_loopless hFB] at he'
    rcases he' with ⟨e, he, rfl⟩
    exact Or.inl
      (lift_edge_props_of_isCutMap (GM19.IsCutting.isCutMap hcut) hF B hB_loopless hFB he).2.2.2.2

theorem liftDrawing_V {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (hS : IsSurface S)
    {ψ : Y → S} {F : Set S} (hcut : IsCutting ψ F) (hF : IsClosed F)
    (B : Surface.Drawing S) (hB_loopless : ∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard)
    (hFB : F ∩ B.U ⊆ B.V) :
    (liftDrawing hY hS hcut hF B hB_loopless hFB).V = ψ ⁻¹' B.V := rfl

theorem liftDrawing_E {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (hS : IsSurface S)
    {ψ : Y → S} {F : Set S} (hcut : IsCutting ψ F) (hF : IsClosed F)
    (B : Surface.Drawing S) (hB_loopless : ∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard)
    (hFB : F ∩ B.U ⊆ B.V) :
    (liftDrawing hY hS hcut hF B hB_loopless hFB).E = (preimage ψ) '' B.E := by
  haveI : CompactSpace Y := hY.1
  haveI : T2Space Y := hY.2.1
  haveI : T2Space S := hS.2.1
  exact arcComponentsIn_preimage_cutMap (GM19.IsCutting.isCutMap hcut) hF B hB_loopless hFB

/-- Right-append step for `ObtainedBySplittingOutsideLe`: if `G₁` is obtained from `G` in `≤ k`
splits outside `U` and `G₂` is obtained from `G₁` by a single vertex split with new vertices
outside `U`, then `G₂` is obtained from `G` in `≤ k + 1` splits outside `U`. -/
theorem ObtainedBySplittingOutsideLe.snoc {α : Type u} {β : Type v}
    {U : Set α} {k : ℕ} {G G₁ G₂ : Hypergraph α β}
    (h : ObtainedBySplittingOutsideLe U k G G₁)
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G₁ G₂ v v₁ v₂ δ₁ δ₂) (hv₁ : v₁ ∉ U) (hv₂ : v₂ ∉ U) :
    ObtainedBySplittingOutsideLe U (k + 1) G G₂ := by
  induction h with
  | refl k G =>
    exact ObtainedBySplittingOutsideLe.step hs hv₁ hv₂ (ObtainedBySplittingOutsideLe.refl k G₂)
  | step hs₀ hv₁₀ hv₂₀ _ ih =>
    exact ObtainedBySplittingOutsideLe.step hs₀ hv₁₀ hv₂₀ (ih hs)

/-- Intermediate hypergraph in `S` associated with a vertex projection `π : Y → S` during the
vertex-by-vertex splitting of `B` along `F ∩ B.V`. -/
def splitLiftHypergraph {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (B : Surface.Drawing S) (ψ : Y → S) (hψ : Continuous ψ)
    (hfib : ∀ x, (ψ ⁻¹' {x}).Finite) (π : Y → S) : Hypergraph S (Set S) where
  vertexSet := π '' (ψ ⁻¹' B.V)
  edgeSet := B.E
  Inc e w := e ∈ B.E ∧ ∃ y ∈ closure (ψ ⁻¹' e) ∩ ψ ⁻¹' B.V, π y = w
  vertex_mem_of_inc _ _ h := by
    rcases h.2 with ⟨y, ⟨_, hyV⟩, rfl⟩
    exact mem_image_of_mem π hyV
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := (B.finite_V.preimage' fun x _ => hfib x).image π
  edgeSet_finite := B.finite_edges

/-- At `π = ψ`, `splitLiftHypergraph` is `B.toHypergraph`. -/
private lemma splitLiftHypergraph_self {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (hS : IsSurface S)
    {ψ : Y → S} {F : Set S} (hcut : IsCutting ψ F) (hF : IsClosed F)
    (B : Surface.Drawing S) (hB_loopless : ∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard)
    (hFB : F ∩ B.U ⊆ B.V) :
    splitLiftHypergraph hY B ψ hcut.1 (GM19.IsCutting.isCutMap hcut).2.2.2.1 ψ = B.toHypergraph := by
  haveI : CompactSpace Y := hY.1
  haveI : T2Space Y := hY.2.1
  haveI : T2Space S := hS.2.1
  refine Hypergraph.ext (Set.ext fun x => ?_) (Set.ext fun e => Iff.rfl)
    (funext fun e => funext fun x => propext ?_)
  · change x ∈ ψ '' (ψ ⁻¹' B.V) ↔ x ∈ B.V
    rw [hcut.2.1.image_preimage]
  · change (e ∈ B.E ∧ ∃ y ∈ closure (ψ ⁻¹' e) ∩ ψ ⁻¹' B.V, ψ y = x) ↔
      e ∈ B.E ∧ x ∈ B.V ∧ x ∈ closure e
    constructor
    · rintro ⟨he, y, ⟨hycl, hyV⟩, rfl⟩
      have h_im :=
        (lift_edge_props_of_isCutMap (GM19.IsCutting.isCutMap hcut) hF B hB_loopless hFB he).2.2.2.1
      exact ⟨he, hyV, h_im ▸ mem_image_of_mem ψ hycl⟩
    · rintro ⟨he, hxV, hxcl⟩
      have h_im :=
        (lift_edge_props_of_isCutMap (GM19.IsCutting.isCutMap hcut) hF B hB_loopless hFB he).2.2.2.1
      rw [← h_im] at hxcl
      rcases hxcl with ⟨y, hycl, rfl⟩
      exact ⟨he, y, ⟨hycl, hxV⟩, rfl⟩

/-- When `π : Y → S` is injective on `ψ ⁻¹' B.V`, `mapHypergraph π (image ψ) B'.toHypergraph`
equals `splitLiftHypergraph hY B ψ hcut.1 (GM19.IsCutting.isCutMap hcut).2.2.2.1 π`. -/
private lemma mapHypergraph_liftDrawing_eq_splitLiftHypergraph {Y S : Type}
    [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (hS : IsSurface S)
    {ψ : Y → S} {F : Set S} (hcut : IsCutting ψ F) (hF : IsClosed F)
    (B : Surface.Drawing S) (hB_loopless : ∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard)
    (hFB : F ∩ B.U ⊆ B.V) (π : Y → S) :
    mapHypergraph π (image ψ) (liftDrawing hY hS hcut hF B hB_loopless hFB).toHypergraph =
      splitLiftHypergraph hY B ψ hcut.1 (GM19.IsCutting.isCutMap hcut).2.2.2.1 π := by
  let B' := liftDrawing hY hS hcut hF B hB_loopless hFB
  have hE_eq : (image ψ) '' B'.E = B.E := by
    rw [liftDrawing_E]
    ext e
    simp only [mem_image]
    constructor
    · rintro ⟨_, ⟨e₀, he₀, rfl⟩, rfl⟩
      rw [hcut.2.1.image_preimage]
      exact he₀
    · intro he
      exact ⟨ψ ⁻¹' e, ⟨e, he, rfl⟩, hcut.2.1.image_preimage e⟩
  refine Hypergraph.ext (Set.ext fun x => Iff.rfl) (Set.ext fun e => ?_)
    (funext fun e => funext fun x => propext ?_)
  · change e ∈ (image ψ) '' B'.E ↔ e ∈ B.E
    rw [hE_eq]
  · change (∃ e' y, (e' ∈ B'.E ∧ y ∈ B'.V ∧ y ∈ closure e') ∧ ψ '' e' = e ∧ π y = x) ↔
      e ∈ B.E ∧ ∃ y ∈ closure (ψ ⁻¹' e) ∩ ψ ⁻¹' B.V, π y = x
    rw [liftDrawing_E, liftDrawing_V]
    constructor
    · rintro ⟨_, y, ⟨⟨e₀, he₀, rfl⟩, hyV, hycl⟩, rfl, rfl⟩
      rw [hcut.2.1.image_preimage]
      exact ⟨he₀, y, ⟨hycl, hyV⟩, rfl⟩
    · rintro ⟨he, y, ⟨hycl, hyV⟩, rfl⟩
      exact ⟨ψ ⁻¹' e, y, ⟨⟨e, he, rfl⟩, hyV, hycl⟩, hcut.2.1.image_preimage e, rfl⟩

/-- Lifting a loopless drawing `B : Drawing S` across a cutting `hcut : IsCutting ψ F` (`ψ : Y → S`)
produces `B' = liftDrawing hY hS hcut hF B hB_loopless hFB : Drawing Y` and a vertex map `π : Y → S`
such that `InjOn π B'.V`, `InjOn (image ψ) B'.E`, and `mapHypergraph π (image ψ) B'.toHypergraph`
is obtained from `B.toHypergraph` by splitting at most `(F ∩ B.V).ncard` vertices with all newly
produced vertices outside `U₀`. -/
theorem exists_lifted_drawing_of_isCutting {Y S : Type}
    [TopologicalSpace Y] [TopologicalSpace S] [Infinite S]
    (hY : IsSurface Y) (hS : IsSurface S)
    {ψ : Y → S} {F : Set S} (hcut : IsCutting ψ F) (hF : IsClosed F)
    (B : Surface.Drawing S) (hB_loopless : ∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard)
    (hFB : F ∩ B.U ⊆ B.V) {U₀ : Set S} (hU₀_fin : U₀.Finite) :
    ∃ (B' : Surface.Drawing Y) (π : Y → S) (fE : Set Y → Set S),
      B' = liftDrawing hY hS hcut hF B hB_loopless hFB ∧
      InjOn π B'.V ∧
      InjOn fE B'.E ∧
      ObtainedBySplittingOutsideLe U₀ (F ∩ B.V).ncard B.toHypergraph
        (mapHypergraph π fE B'.toHypergraph) ∧
      (∀ y ∈ B'.V, ψ y ∉ F → π y = ψ y) ∧
      (∀ y ∈ B'.V, ψ y ∈ F → π y ∉ U₀ ∪ B.V) := by
  haveI : CompactSpace Y := hY.1
  haveI : T2Space Y := hY.2.1
  haveI : T2Space S := hS.2.1
  classical
  let B' := liftDrawing hY hS hcut hF B hB_loopless hFB
  have hfib : ∀ x, (ψ ⁻¹' {x}).Finite := (GM19.IsCutting.isCutMap hcut).2.2.2.1
  have hV'_fin : (ψ ⁻¹' B.V).Finite := B.finite_V.preimage' fun x _ => hfib x
  have hFB_fin : (F ∩ B.V).Finite := B.finite_V.subset inter_subset_right
  have h_ind : ∀ (K : Finset S), (K : Set S) ⊆ F ∩ B.V →
      ∃ π : Y → S,
        (∀ y ∈ ψ ⁻¹' B.V, ψ y ∉ (K : Set S) → π y = ψ y) ∧
        (∀ y ∈ ψ ⁻¹' B.V, ψ y ∈ (K : Set S) → π y ∉ U₀ ∪ B.V) ∧
        (∀ y₁ ∈ ψ ⁻¹' B.V, ∀ y₂ ∈ ψ ⁻¹' B.V,
          (ψ y₁ ∈ (K : Set S) ∨ ψ y₁ ∉ F) →
          (ψ y₂ ∈ (K : Set S) ∨ ψ y₂ ∉ F) →
          π y₁ = π y₂ → y₁ = y₂) ∧
        ObtainedBySplittingOutsideLe U₀ K.card B.toHypergraph
          (splitLiftHypergraph hY B ψ hcut.1 hfib π) := by
    intro K
    induction K using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨ψ, fun _ _ _ => rfl, ?_, ?_, ?_⟩
      · intro y _ hy
        simp at hy
      · intro y₁ _ y₂ _ h₁ h₂ h_eq
        simp only [Finset.coe_empty, mem_empty_iff_false, false_or] at h₁ h₂
        exact hcut.2.2.1 h₁ h₂ h_eq
      · rw [Finset.card_empty, splitLiftHypergraph_self hY hS hcut hF B hB_loopless hFB]
        exact ObtainedBySplittingOutsideLe.refl 0 B.toHypergraph
    | @insert v K hvK ih =>
      intro hK_sub
      have hv_mem : v ∈ F ∩ B.V := hK_sub (Finset.mem_coe.mpr (Finset.mem_insert_self v K))
      have hK_sub' : (K : Set S) ⊆ F ∩ B.V :=
        fun x hx => hK_sub (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx)))
      obtain ⟨π, hπ_out, hπ_in, hπ_inj, hπ_split⟩ := ih hK_sub'
      have hfib2 : (ψ ⁻¹' {v}).ncard = 2 := hcut.2.2.2.1 v hv_mem.1
      obtain ⟨y₁, y₂, hy₁₂, hfib_eq⟩ := Set.ncard_eq_two.mp hfib2
      have hy₁_ψ : ψ y₁ = v := by
        have : y₁ ∈ ψ ⁻¹' {v} := hfib_eq ▸ Or.inl rfl
        exact this
      have hy₂_ψ : ψ y₂ = v := by
        have : y₂ ∈ ψ ⁻¹' {v} := hfib_eq ▸ Or.inr rfl
        exact this
      have hy₁_V : y₁ ∈ ψ ⁻¹' B.V := by change ψ y₁ ∈ B.V; rw [hy₁_ψ]; exact hv_mem.2
      have hy₂_V : y₂ ∈ ψ ⁻¹' B.V := by change ψ y₂ ∈ B.V; rw [hy₂_ψ]; exact hv_mem.2
      let Avoid₁ : Set S := U₀ ∪ B.V ∪ π '' (ψ ⁻¹' B.V)
      have hAvoid₁_fin : Avoid₁.Finite :=
        (hU₀_fin.union B.finite_V).union (hV'_fin.image π)
      obtain ⟨v₁, hv₁_not⟩ := Infinite.exists_notMem_finset hAvoid₁_fin.toFinset
      have hv₁_avoid : v₁ ∉ Avoid₁ := by rwa [Set.Finite.mem_toFinset] at hv₁_not
      have hAvoid₂_fin : (insert v₁ Avoid₁).Finite := hAvoid₁_fin.insert v₁
      obtain ⟨v₂, hv₂_not⟩ := Infinite.exists_notMem_finset hAvoid₂_fin.toFinset
      have hv₂_avoid' : v₂ ∉ insert v₁ Avoid₁ := by rwa [Set.Finite.mem_toFinset] at hv₂_not
      have hv₁₂ : v₁ ≠ v₂ := fun h => hv₂_avoid' (Or.inl h.symm)
      have hv₂_avoid : v₂ ∉ Avoid₁ := fun h => hv₂_avoid' (Or.inr h)
      let π' : Y → S := fun y => if y = y₁ then v₁ else if y = y₂ then v₂ else π y
      have hπ'_y₁ : π' y₁ = v₁ := by simp [π']
      have hπ'_y₂ : π' y₂ = v₂ := by simp [π', hy₁₂.symm]
      have hπ'_other : ∀ y : Y, ψ y ≠ v → π' y = π y := by
        intro y hy
        have hy₁' : y ≠ y₁ := fun h => hy (h ▸ hy₁_ψ)
        have hy₂' : y ≠ y₂ := fun h => hy (h ▸ hy₂_ψ)
        simp [π', hy₁', hy₂']
      have hπ'_on_v : ∀ y : Y, ψ y = v → (y = y₁ ∧ π' y = v₁) ∨ (y = y₂ ∧ π' y = v₂) := by
        intro y hy
        have hy_mem : y ∈ ψ ⁻¹' {v} := hy
        rw [hfib_eq] at hy_mem
        rcases hy_mem with rfl | rfl
        · exact Or.inl ⟨rfl, hπ'_y₁⟩
        · exact Or.inr ⟨rfl, hπ'_y₂⟩
      refine ⟨π', ?_, ?_, ?_, ?_⟩
      · intro y hyV hy_not
        rw [Finset.coe_insert, mem_insert_iff, not_or] at hy_not
        rw [hπ'_other y hy_not.1]
        exact hπ_out y hyV hy_not.2
      · intro y hyV hy_in
        rw [Finset.coe_insert, mem_insert_iff] at hy_in
        rcases hy_in with hy_v | hy_K
        · rcases hπ'_on_v y hy_v with ⟨_, h_eq⟩ | ⟨_, h_eq⟩
          · rw [h_eq]; exact fun h => hv₁_avoid (Or.inl h)
          · rw [h_eq]; exact fun h => hv₂_avoid (Or.inl h)
        · have hyv : ψ y ≠ v := fun h => hvK (Finset.mem_coe.mp (h ▸ hy_K))
          rw [hπ'_other y hyv]
          exact hπ_in y hyV hy_K
      · intro z₁ hz₁ z₂ hz₂ h₁ h₂ h_eq
        rw [Finset.coe_insert, mem_insert_iff] at h₁ h₂
        by_cases hz₁v : ψ z₁ = v
        · by_cases hz₂v : ψ z₂ = v
          · rcases hπ'_on_v z₁ hz₁v with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;>
              rcases hπ'_on_v z₂ hz₂v with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
            · rfl
            · exfalso; rw [h1, h2] at h_eq; exact hv₁₂ h_eq
            · exfalso; rw [h1, h2] at h_eq; exact hv₁₂ h_eq.symm
            · rfl
          · exfalso
            rw [hπ'_other z₂ hz₂v] at h_eq
            rcases hπ'_on_v z₁ hz₁v with ⟨_, h1⟩ | ⟨_, h1⟩
            · rw [h1] at h_eq
              exact hv₁_avoid (Or.inr ⟨z₂, hz₂, h_eq.symm⟩)
            · rw [h1] at h_eq
              exact hv₂_avoid (Or.inr ⟨z₂, hz₂, h_eq.symm⟩)
        · by_cases hz₂v : ψ z₂ = v
          · exfalso
            rw [hπ'_other z₁ hz₁v] at h_eq
            rcases hπ'_on_v z₂ hz₂v with ⟨_, h2⟩ | ⟨_, h2⟩
            · rw [h2] at h_eq
              exact hv₁_avoid (Or.inr ⟨z₁, hz₁, h_eq⟩)
            · rw [h2] at h_eq
              exact hv₂_avoid (Or.inr ⟨z₁, hz₁, h_eq⟩)
          · rw [hπ'_other z₁ hz₁v, hπ'_other z₂ hz₂v] at h_eq
            have h₁' : ψ z₁ ∈ (K : Set S) ∨ ψ z₁ ∉ F :=
              h₁.imp_left fun h => h.resolve_left hz₁v
            have h₂' : ψ z₂ ∈ (K : Set S) ∨ ψ z₂ ∉ F :=
              h₂.imp_left fun h => h.resolve_left hz₂v
            exact hπ_inj z₁ hz₁ z₂ hz₂ h₁' h₂' h_eq
      · let G₁ := splitLiftHypergraph hY B ψ hcut.1 hfib π
        let G₂ := splitLiftHypergraph hY B ψ hcut.1 hfib π'
        let δ₁ : Set (Set S) := {e ∈ B.E | y₁ ∈ closure (ψ ⁻¹' e)}
        let δ₂ : Set (Set S) := {e ∈ B.E | y₂ ∈ closure (ψ ⁻¹' e)}
        have hπ_eq_v_iff : ∀ y ∈ ψ ⁻¹' B.V, π y = v ↔ ψ y = v := by
          intro y hyV
          constructor
          · intro hπy
            by_cases hyK : ψ y ∈ (K : Set S)
            · exfalso
              exact hπ_in y hyV hyK (Or.inr (hπy ▸ hv_mem.2))
            · rw [← hπ_out y hyV hyK, hπy]
          · intro hψy
            rw [hπ_out y hyV (hψy ▸ fun h => hvK (Finset.mem_coe.mp h)), hψy]
        have hs : IsVertexSplit G₁ G₂ v v₁ v₂ δ₁ δ₂ := by
          refine
            { v_mem := ⟨y₁, hy₁_V, (hπ_eq_v_iff y₁ hy₁_V).mpr hy₁_ψ⟩
              v₁_not_mem := fun h => hv₁_avoid (Or.inr h)
              v₂_not_mem := fun h => hv₂_avoid (Or.inr h)
              v₁_ne_v₂ := hv₁₂
              δ_disjoint := ?_
              δ_union := ?_
              vertexSet_eq := ?_
              edgeSet_eq := rfl
              inc_iff := ?_ }
          · refine disjoint_left.mpr fun e ⟨he, hy₁cl⟩ ⟨_, hy₂cl⟩ => hy₁₂ ?_
            have h_inj :=
              (lift_edge_props_of_isCutMap (GM19.IsCutting.isCutMap hcut) hF B hB_loopless hFB he).2.2.1
            exact h_inj hy₁cl hy₂cl (hy₁_ψ.trans hy₂_ψ.symm)
          · ext e
            change (e ∈ B.E ∧ y₁ ∈ closure (ψ ⁻¹' e)) ∨ (e ∈ B.E ∧ y₂ ∈ closure (ψ ⁻¹' e)) ↔
              e ∈ B.E ∧ (e ∈ B.E ∧ ∃ y ∈ closure (ψ ⁻¹' e) ∩ ψ ⁻¹' B.V, π y = v)
            constructor
            · rintro (⟨he, hy₁cl⟩ | ⟨he, hy₂cl⟩)
              · exact ⟨he, he, y₁, ⟨hy₁cl, hy₁_V⟩, (hπ_eq_v_iff y₁ hy₁_V).mpr hy₁_ψ⟩
              · exact ⟨he, he, y₂, ⟨hy₂cl, hy₂_V⟩, (hπ_eq_v_iff y₂ hy₂_V).mpr hy₂_ψ⟩
            · rintro ⟨_, he, y, ⟨hycl, hyV⟩, hπy⟩
              have hψy : ψ y = v := (hπ_eq_v_iff y hyV).mp hπy
              rcases hπ'_on_v y hψy with ⟨rfl, _⟩ | ⟨rfl, _⟩
              · exact Or.inl ⟨he, hycl⟩
              · exact Or.inr ⟨he, hycl⟩
          · ext w
            simp only [G₁, G₂, splitLiftHypergraph, mem_image, mem_union, mem_sdiff,
              mem_singleton_iff, mem_insert_iff]
            constructor
            · rintro ⟨y, hyV, rfl⟩
              by_cases hψy : ψ y = v
              · rcases hπ'_on_v y hψy with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
                · exact Or.inr (Or.inl h1)
                · exact Or.inr (Or.inr h1)
              · rw [hπ'_other y hψy]
                exact Or.inl ⟨⟨y, hyV, rfl⟩, fun h => hψy ((hπ_eq_v_iff y hyV).mp h)⟩
            · rintro (⟨⟨y, hyV, rfl⟩, hne⟩ | rfl | rfl)
              · have hψy : ψ y ≠ v := fun h => hne ((hπ_eq_v_iff y hyV).mpr h)
                exact ⟨y, hyV, hπ'_other y hψy⟩
              · exact ⟨y₁, hy₁_V, hπ'_y₁⟩
              · exact ⟨y₂, hy₂_V, hπ'_y₂⟩
          · intro e _ w hw
            change (e ∈ B.E ∧ ∃ y ∈ closure (ψ ⁻¹' e) ∩ ψ ⁻¹' B.V, π' y = w) ↔
              (w ≠ v₁ ∧ w ≠ v₂ ∧ (e ∈ B.E ∧ ∃ y ∈ closure (ψ ⁻¹' e) ∩ ψ ⁻¹' B.V, π y = w)) ∨
              (w = v₁ ∧ e ∈ B.E ∧ y₁ ∈ closure (ψ ⁻¹' e)) ∨
              (w = v₂ ∧ e ∈ B.E ∧ y₂ ∈ closure (ψ ⁻¹' e))
            constructor
            · rintro ⟨he, y, ⟨hycl, hyV⟩, rfl⟩
              by_cases hψy : ψ y = v
              · rcases hπ'_on_v y hψy with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
                · rw [h1]; exact Or.inr (Or.inl ⟨rfl, he, hycl⟩)
                · rw [h1]; exact Or.inr (Or.inr ⟨rfl, he, hycl⟩)
              · rw [hπ'_other y hψy]
                have h_ne_v₁ : π y ≠ v₁ := fun h => hv₁_avoid (Or.inr ⟨y, hyV, h⟩)
                have h_ne_v₂ : π y ≠ v₂ := fun h => hv₂_avoid (Or.inr ⟨y, hyV, h⟩)
                exact Or.inl ⟨h_ne_v₁, h_ne_v₂, he, y, ⟨hycl, hyV⟩, rfl⟩
            · rintro (⟨hw_ne_v₁, hw_ne_v₂, he, y, ⟨hycl, hyV⟩, rfl⟩ |
                ⟨rfl, he, hy₁cl⟩ | ⟨rfl, he, hy₂cl⟩)
              · have hψy : ψ y ≠ v := by
                  intro h
                  have hπv : π y = v := (hπ_eq_v_iff y hyV).mpr h
                  rcases hw with ⟨z, hzV, hπ'z⟩
                  rw [hπv] at hπ'z
                  by_cases hψz : ψ z = v
                  · rcases hπ'_on_v z hψz with ⟨_, h1⟩ | ⟨_, h1⟩
                    · exact hw_ne_v₁ (hπv.trans (hπ'z.symm.trans h1))
                    · exact hw_ne_v₂ (hπv.trans (hπ'z.symm.trans h1))
                  · rw [hπ'_other z hψz] at hπ'z
                    exact hψz ((hπ_eq_v_iff z hzV).mp hπ'z)
                exact ⟨he, y, ⟨hycl, hyV⟩, hπ'_other y hψy⟩
              · exact ⟨he, y₁, ⟨hy₁cl, hy₁_V⟩, hπ'_y₁⟩
              · exact ⟨he, y₂, ⟨hy₂cl, hy₂_V⟩, hπ'_y₂⟩
        rw [Finset.card_insert_of_notMem hvK]
        exact hπ_split.snoc hs
          (fun h => hv₁_avoid (Or.inl (Or.inl h)))
          (fun h => hv₂_avoid (Or.inl (Or.inl h)))
  let K₀ : Finset S := hFB_fin.toFinset
  have hK₀_coe : (K₀ : Set S) = F ∩ B.V := Set.Finite.coe_toFinset hFB_fin
  have hK₀_card : K₀.card = (F ∩ B.V).ncard := by
    rw [← Set.ncard_coe_finset, hK₀_coe]
  obtain ⟨π, hπ_out, hπ_in, hπ_inj, hπ_split⟩ := h_ind K₀ hK₀_coe.subset
  rw [hK₀_coe] at hπ_out hπ_in hπ_inj
  rw [hK₀_card, ← mapHypergraph_liftDrawing_eq_splitLiftHypergraph hY hS hcut hF B hB_loopless hFB π]
    at hπ_split
  have hπ_injOn : InjOn π B'.V := by
    intro y₁ hy₁ y₂ hy₂ h_eq
    have h₁ : ψ y₁ ∈ F ∩ B.V ∨ ψ y₁ ∉ F := by
      by_cases h : ψ y₁ ∈ F
      · exact Or.inl ⟨h, hy₁⟩
      · exact Or.inr h
    have h₂ : ψ y₂ ∈ F ∩ B.V ∨ ψ y₂ ∉ F := by
      by_cases h : ψ y₂ ∈ F
      · exact Or.inl ⟨h, hy₂⟩
      · exact Or.inr h
    exact hπ_inj y₁ hy₁ y₂ hy₂ h₁ h₂ h_eq
  have hfE_injOn : InjOn (image ψ) B'.E := by
    rw [liftDrawing_E]
    rintro _ ⟨e₁, _, rfl⟩ _ ⟨e₂, _, rfl⟩ h_eq
    rw [hcut.2.1.image_preimage, hcut.2.1.image_preimage] at h_eq
    rw [h_eq]
  refine ⟨B', π, image ψ, rfl, hπ_injOn, hfE_injOn, hπ_split, ?_, ?_⟩
  · intro y hyV hyF
    exact hπ_out y hyV fun h => hyF h.1
  · intro y hyV hyF
    exact hπ_in y hyV ⟨hyF, hyV⟩

/-- Boundary characterization for a lifted drawing `B' = liftDrawing hY hS hcut hF B hB_loopless hFB`:
every vertex `y ∈ B'.V` satisfies `y ∈ bd Y ↔ π y ∈ Γ.V ∩ bd S ∨ π y ∉ Γ.V` when `U₀ = Γ.V` and
`B.V ⊆ Γ.V`. -/
theorem bd_iff_of_lifted_drawing {Y S : Type}
    [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (hS : IsSurface S)
    {ψ : Y → S} {F : Set S} (hcut : IsCutting ψ F) (hF : IsClosed F)
    {Γ B : Surface.Drawing S} (hBV : B.V ⊆ Γ.V)
    {B' : Surface.Drawing Y} {π : Y → S}
    (hB'_V : B'.V = ψ ⁻¹' B.V)
    (hπ_out : ∀ y ∈ B'.V, ψ y ∉ F → π y = ψ y)
    (hπ_in : ∀ y ∈ B'.V, ψ y ∈ F → π y ∉ Γ.V ∪ B.V) :
    ∀ y ∈ B'.V, y ∈ bd Y ↔ π y ∈ Γ.V ∩ bd S ∨ π y ∉ Γ.V := by
  haveI : CompactSpace Y := hY.1
  haveI : T2Space Y := hY.2.1
  haveI : T2Space S := hS.2.1
  have hcm : GM19.IsCutMap ψ F := GM19.IsCutting.isCutMap hcut
  intro y hyV
  have hyBV : ψ y ∈ B.V := by
    change y ∈ ψ ⁻¹' B.V
    rwa [← hB'_V]
  by_cases hyF : ψ y ∈ F
  · have hy_bd : y ∈ bd Y := hcut.2.2.2.2 hyF
    have hπ_not : π y ∉ Γ.V := fun h => hπ_in y hyV hyF (Or.inl h)
    exact ⟨fun _ => Or.inr hπ_not, fun _ => hy_bd⟩
  · rw [hπ_out y hyV hyF]
    have hψ_Γ : ψ y ∈ Γ.V := hBV hyBV
    constructor
    · intro hy_bd
      exact Or.inl ⟨hψ_Γ, GM19.bd_of_bd_cutMap hcm hF hy_bd hyF⟩
    · rintro (⟨_, hψ_bd⟩ | h_not)
      · intro hint
        exact hψ_bd (GM19.isInteriorPoint_image hcm hF hint hyF)
      · exact (h_not hψ_Γ).elim

/-- If `B : Drawing S` is proper (`B.IsProper`) and `F ∩ B.U ⊆ B.V`, then the lifted drawing
`liftDrawing hY hS hcut hF B hB_loopless hFB` is also proper. -/
theorem liftDrawing_isProper {Y S : Type}
    [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (hS : IsSurface S)
    {ψ : Y → S} {F : Set S} (hcut : IsCutting ψ F) (hF : IsClosed F)
    (B : Surface.Drawing S) (hB_loopless : ∀ e ∈ B.E, 2 ≤ (B.toHypergraph.ends e).ncard)
    (hFB : F ∩ B.U ⊆ B.V) (hB_prop : B.IsProper) :
    (liftDrawing hY hS hcut hF B hB_loopless hFB).IsProper := by
  haveI : CompactSpace Y := hY.1
  haveI : T2Space Y := hY.2.1
  haveI : T2Space S := hS.2.1
  have hcm : GM19.IsCutMap ψ F := GM19.IsCutting.isCutMap hcut
  rintro y ⟨hy_bd, hy_U⟩
  change ψ y ∈ B.U at hy_U
  change ψ y ∈ B.V
  by_cases hyF : ψ y ∈ F
  · exact hFB ⟨hyF, hy_U⟩
  · exact hB_prop ⟨GM19.bd_of_bd_cutMap hcm hF hy_bd hyF, hy_U⟩

end LiftDrawing

/-! ## 7. Claims (7) and (8) of Graph Minors XXI, (5.2) -/

/-- For any tangle `𝒯` of order `θ ≥ 1` in `G`, the trivial separation `(⊥, G)` belongs to `𝒯`. -/
theorem bot_self_mem_tangle {α : Type u} {β : Type v}
    {G : Hypergraph α β} {θ : ℕ} {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) : (⊥, G) ∈ 𝒯 := by
  have hsep : G.IsSeparation ⊥ G := by
    rw [GM10.isSeparation_iff_of_le bot_le le_rfl]
    exact ⟨empty_union _, empty_union _, empty_inter _⟩
  have hord : separationOrder (⊥ : Hypergraph α β) G < θ := by
    have h0 : separationOrder (⊥ : Hypergraph α β) G = 0 := by
      unfold separationOrder
      change ((∅ : Set α) ∩ G.vertexSet).ncard = 0
      simp
    rw [h0]
    exact h𝒯.one_le
  rcases h𝒯.axiom1 hsep hord with hm | hm
  · exact hm
  · exfalso
    exact h𝒯.axiom3 hm rfl

/-- **Graph Minors XXI, (5.2), Claim (7)** (page 19 of the preprint):
"(7) *There is no* $\Gamma$*-normal proper line* $F \subseteq \Sigma$ *with ends in different cuffs
such that* $|F \cap V(\Gamma)| \le \theta_4$." -/
theorem claim_5_2_7 {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L : Hypergraph S (Set S)}
    {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ_prop : Γ.IsProper)
    (hΓ_loopless : ∀ e ∈ Γ.E, 2 ≤ (Γ.toHypergraph.ends e).ncard)
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (h_ind2 : ∀ (S' Shat' : Type) [TopologicalSpace S'] [TopologicalSpace Shat'],
      IsSurface S' → [ConnectedSpace S'] →
      GM19.IsCappedSurface S' Shat' →
      Nonempty (Shat' ≃ₜ S₀) →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₂ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → [ConnectedSpace S'] →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S'),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L' : Hypergraph S' (Set S')),
          IsTangle Γ'.toHypergraph θ₃ T' →
          IsVitalLinkage Γ'.toHypergraph L' →
          ¬ (terminals L' ⊆ bd S'))
    {F : Set S} {s t : S} {C₁ C₂ : Set S}
    (hC₁ : C₁ ∈ cuffs S) (hC₂ : C₂ ∈ cuffs S) (hC_ne : C₁ ≠ C₂)
    (hs : s ∈ C₁) (ht : t ∈ C₂)
    (hF_line : IsProperLineInSurface F s t)
    (hF_norm : (PaintingOrDrawing.drawing Γ).IsNormal F) :
    θ₄ < (F ∩ Γ.V).ncard := by
  by_contra! hle
  haveI : T2Space S := hS.2.1
  obtain ⟨f_line, _, _⟩ := hF_line.1
  haveI : Infinite S := infinite_of_isLine ⟨f_line⟩
  have hcomp_s : connectedComponentIn (bd S) s = C₁ := by
    rcases hC₁ with ⟨z, _, rfl⟩
    exact (connectedComponentIn_eq hs).symm
  have hcomp_t : connectedComponentIn (bd S) t = C₂ := by
    rcases hC₂ with ⟨z, _, rfl⟩
    exact (connectedComponentIn_eq ht).symm
  have hdiff : connectedComponentIn (bd S) s ≠ connectedComponentIn (bd S) t := by
    rw [hcomp_s, hcomp_t]
    exact hC_ne
  obtain ⟨Y, tY, ψ, hY, hcut, h_iarc, -, -⟩ :=
    cutIArc S F s t hS inferInstance hF_line.ne hF_line.inter_bd_eq hF_line.1
  letI := tY
  obtain ⟨hY_conn, -⟩ := h_iarc hdiff
  letI := hY_conn
  haveI : T2Space Y := hY.2.1
  obtain ⟨Yhat, tYhat, ⟨capY⟩⟩ := exists_cappedSurface _ Y hY inferInstance rfl
  letI := tYhat
  obtain ⟨hhat, hcuffs⟩ :=
    (theorem_4_1_proof hS hY hcut cap capY).1 s t C₁ C₂ hC₁ hC₂ hC_ne hs ht hF_line
  have hFc : IsClosed F := hF_line.1.isCompact.isClosed
  obtain ⟨Γ', π, fE, rfl, hπ_inj, hfE_inj, hsplit, hπ_out, hπ_in⟩ :=
    exists_lifted_drawing_of_isCutting hY hS hcut hFc Γ hΓ_loopless hF_norm Γ.finite_V
  have hΓ'_prop : (liftDrawing hY hS hcut hFc Γ hΓ_loopless hF_norm).IsProper :=
    liftDrawing_isProper hY hS hcut hFc Γ hΓ_loopless hF_norm hΓ_prop
  have hsplit_θ₄ : ObtainedBySplittingOutsideLe Γ.V θ₄ Γ.toHypergraph
      (mapHypergraph π fE (liftDrawing hY hS hcut hFc Γ hΓ_loopless hF_norm).toHypergraph) :=
    hsplit.mono hle
  have hAB : ((⊥ : Hypergraph S (Set S)), Γ.toHypergraph) ∈ 𝒯 := bot_self_mem_tangle h𝒯
  have hord0 : separationOrder (⊥ : Hypergraph S (Set S)) Γ.toHypergraph ≤ θ₄ := by
    unfold separationOrder
    change ((∅ : Set S) ∩ Γ.V).ncard ≤ θ₄
    simp
  have h6b : ∀ y ∈ (liftDrawing hY hS hcut hFc Γ hΓ_loopless hF_norm).V,
      y ∈ bd Y ↔
        π y ∈ ((⊥ : Hypergraph S (Set S)) ∩ Γ.toHypergraph).vertexSet ∨
          π y ∈ Γ.V ∩ bd S ∨ π y ∉ Γ.V := by
    intro y hyV
    have hbd_iff := bd_iff_of_lifted_drawing hY hS hcut hFc Subset.rfl rfl hπ_out hπ_in y hyV
    change y ∈ bd Y ↔ π y ∈ (∅ : Set S) ∩ Γ.V ∨ π y ∈ Γ.V ∩ bd S ∨ π y ∉ Γ.V
    rw [empty_inter, mem_empty_iff_false, false_or]
    exact hbd_iff
  have h6 := apply_claim_5_2_6_of_drawing hS hY cap capY hΓ_bd h𝒯 hL hL_bd hAB hord0
    hπ_inj hfE_inj hsplit_θ₄ hhat h6b hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos
    (fun hlt_c hle_bd T' L' hT' hL' => h_ind2 Y Yhat hY capY hhat hlt_c _ hΓ'_prop hle_bd T' L' hT' hL')
    (fun hhomeo hlt_bd T' L' hT' hL' => h_ind3 Y hY hhomeo _ hΓ'_prop hlt_bd T' L' hT' hL')
  have h_le := h6.1
  omega

/-- Properties of the two sides `S₁ = ψ '' W₁` and `S₂ = ψ '' W₂` of a separating `O`-arc cut
`T : TwoSides ψ F W₁ W₂ X X'` in a surface `S` with `bd S = ∅`. -/
private theorem twoSides_subsurfaces' {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y]
    [T2Space S] [T2Space Y] [ConnectedSpace S]
    (hbd : bd S = ∅) (hY : IsSurface Y)
    {F : Set S} {ψ : Y → S} {W₁ W₂ X X' : Set Y}
    (T : TwoSides ψ F W₁ W₂ X X') (hF : IsOArc F)
    (hc₁ : ConnectedSpace W₁) (hc₂ : ConnectedSpace W₂) :
    let S₁ := ψ '' W₁
    let S₂ := ψ '' W₂
    IsSurface S₁ ∧ ConnectedSpace S₁ ∧ IsClosed S₁ ∧
    IsSurface S₂ ∧ ConnectedSpace S₂ ∧ IsClosed S₂ ∧
    S₁ ∪ S₂ = univ ∧ S₁ ∩ S₂ = F ∧
    closure (univ \ S₁) = S₂ ∧ frontier S₁ = F ∧
    bd S₂ = Subtype.val ⁻¹' F ∧ IsOArc (bd S₂) := by
  haveI : CompactSpace Y := hY.1
  let S₁ := ψ '' W₁
  let S₂ := ψ '' W₂
  haveI hcW₁ : CompactSpace W₁ := isCompact_iff_compactSpace.mp T.c₁.1.isCompact
  haveI hcW₂ : CompactSpace W₂ := isCompact_iff_compactSpace.mp T.c₂.1.isCompact
  let j₁ : W₁ → S₁ := fun y ↦ ⟨ψ y.1, mem_image_of_mem _ y.2⟩
  have cj₁ : Continuous j₁ := (T.hψ.1.comp continuous_subtype_val).subtype_mk _
  have bj₁ : Function.Bijective j₁ :=
    ⟨fun a b he ↦ T.inj (congrArg Subtype.val he), fun ⟨_, y, hy, rfl⟩ ↦ ⟨⟨y, hy⟩, rfl⟩⟩
  let eW₁ : W₁ ≃ₜ S₁ := cj₁.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j₁ bj₁)
  let j₂ : W₂ → S₂ := fun y ↦ ⟨ψ y.1, mem_image_of_mem _ y.2⟩
  have cj₂ : Continuous j₂ := (T.hψ.1.comp continuous_subtype_val).subtype_mk _
  have bj₂ : Function.Bijective j₂ :=
    ⟨fun a b he ↦ T.symm.inj (congrArg Subtype.val he), fun ⟨_, y, hy, rfl⟩ ↦ ⟨⟨y, hy⟩, rfl⟩⟩
  let eW₂ : W₂ ≃ₜ S₂ := cj₂.homeoOfEquivCompactToT2 (f := Equiv.ofBijective j₂ bj₂)
  have hS₁ : IsSurface S₁ := isSurface_of_homeo eW₁ (isSurface_sub hY T.c₁)
  have hS₂ : IsSurface S₂ := isSurface_of_homeo eW₂ (isSurface_sub hY T.c₂)
  have hconn₁ : ConnectedSpace S₁ := eW₁.surjective.connectedSpace eW₁.continuous
  have hconn₂ : ConnectedSpace S₂ := eW₂.surjective.connectedSpace eW₂.continuous
  have hcl₁ : IsClosed S₁ := (T.c₁.1.isCompact.image T.hψ.1).isClosed
  have hcl₂ : IsClosed S₂ := (T.c₂.1.isCompact.image T.hψ.1).isClosed
  have hun : S₁ ∪ S₂ = univ := by
    rw [← image_union, T.hU, image_univ_of_surjective T.hψ.2.1]
  have hint : S₁ ∩ S₂ = F := by
    apply Subset.antisymm
    · rintro _ ⟨⟨y₁, hy₁, rfl⟩, ⟨y₂, hy₂, he⟩⟩
      exact T.b.mapsTo (T.mem_cross hy₁ hy₂ he.symm)
    · intro x hxF
      obtain ⟨y₁, hy₁, rfl⟩ := T.b.surjOn hxF
      obtain ⟨y₂, hy₂, he₂⟩ := T.b'.surjOn hxF
      exact ⟨⟨y₁, T.hX hy₁, rfl⟩, ⟨y₂, T.hX' hy₂, he₂⟩⟩
  have hFc : IsClosed F := (isCompact_of_isOArc hF).isClosed
  have hbdY_eq : bd Y = ψ ⁻¹' F := by
    apply Subset.antisymm _ T.hψ.2.2.2.2
    intro y hy
    by_contra hyF
    have h_in_bd : ψ y ∈ bd S := bd_of_bd_cutMap (IsCutting.isCutMap T.hψ) hFc hy hyF
    rw [hbd] at h_in_bd
    exact h_in_bd
  have hbd_W₂ : ∀ y : W₂, y ∈ bd W₂ ↔ ψ y.1 ∈ F := by
    intro y
    rw [mem_bd_sub T.c₂.2, hbdY_eq]
    rfl
  have hbd_S₂ : bd S₂ = Subtype.val ⁻¹' F := by
    ext z
    obtain ⟨y, rfl⟩ := eW₂.surjective z
    have h_img := image_bd_homeomorph eW₂
    have hy_iff : eW₂ y ∈ bd S₂ ↔ y ∈ bd W₂ := by
      rw [← h_img]
      exact ⟨fun ⟨w, hw, he⟩ ↦ eW₂.injective he ▸ hw, fun hy ↦ ⟨y, hy, rfl⟩⟩
    rw [hy_iff, hbd_W₂]
    rfl
  have hF_sub₂ : F ⊆ S₂ := hint ▸ inter_subset_right
  have himg_bd₂ : Subtype.val '' bd S₂ = F := by
    rw [hbd_S₂, Subtype.image_preimage_coe, inter_eq_right.mpr hF_sub₂]
  have hO_bd₂ : IsOArc (bd S₂) := by
    obtain ⟨φ⟩ := hF
    let e_sub : (bd S₂ : Set S₂) ≃ₜ F :=
      (IsEmbedding.subtypeVal.homeomorphImage (bd S₂)).trans (Homeomorph.setCongr himg_bd₂)
    exact ⟨φ.trans e_sub.symm⟩
  have hcl_compl₁ : closure (univ \ S₁) = S₂ := by
    have hdiff_eq : univ \ S₁ = S₂ \ F := by
      ext x
      simp only [mem_sdiff, mem_univ, true_and]
      constructor
      · intro hx₁
        exact ⟨(hun ▸ mem_univ x).resolve_left hx₁, fun hxF ↦ hx₁ (hint ▸ hxF).1⟩
      · rintro ⟨hx₂, hxF⟩ hx₁
        exact hxF (hint ▸ ⟨hx₁, hx₂⟩)
    rw [hdiff_eq]
    apply Subset.antisymm (hcl₂.closure_subset_iff.mpr sdiff_subset)
    intro x hx₂
    have hdense := (dense_interior' hS₂).closure_eq
    have hx_cl : (⟨x, hx₂⟩ : S₂) ∈ closure (bd S₂)ᶜ := hdense.symm ▸ mem_univ _
    have h_img_compl : Subtype.val '' (bd S₂ : Set S₂)ᶜ = S₂ \ F := by
      rw [hbd_S₂, ← preimage_compl, Subtype.image_preimage_coe]
      rfl
    rw [← h_img_compl]
    exact image_closure_subset_closure_image continuous_subtype_val
      (mem_image_of_mem Subtype.val hx_cl)
  have hfr₁ : frontier S₁ = F := by
    rw [frontier_eq_closure_inter_closure, hcl₁.closure_eq, compl_eq_univ_sdiff, hcl_compl₁, hint]
  exact ⟨hS₁, hconn₁, hcl₁, hS₂, hconn₂, hcl₂, hun, hint, hcl_compl₁, hfr₁, hbd_S₂, hO_bd₂⟩

/-- Identity capping of a connected surface `S` with `bd S = ∅`. -/
private def isCappedSurface_self {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (hbd : bd S = ∅) :
    IsCappedSurface S S :=
  have hcuffs : cuffs S = ∅ := by
    refine eq_empty_of_forall_notMem ?_
    rintro _ ⟨x, hx, -⟩
    rw [hbd] at hx
    exact hx
  { isSurface := hS
    connected := inferInstance
    bd_empty := hbd
    emb := id
    isEmbedding := IsEmbedding.id
    cuffDisc := fun _ ↦ ∅
    cuffDisc_closedDisc := fun Θ hΘ ↦ by simp [hcuffs] at hΘ
    cuffDisc_bd := fun Θ hΘ ↦ by simp [hcuffs] at hΘ
    cuffDisc_disjoint := fun Θ hΘ ↦ by simp [hcuffs] at hΘ
    compl_eq := by simp [hcuffs] }

/-- **Graph Minors XXI, (5.2), Claim (8)** (pages 19–20 of the preprint):
"(8) $\mathcal{T}_1$ *is respectful.* ... Let $d_1$ be the metric of $\mathcal{T}_1$." -/
theorem claim_5_2_8 {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L : Hypergraph S (Set S)}
    {p θ θ₄ θ₁ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ_conn : IsPreconnected Γ.U)
    (hΓ_loopless : ∀ e ∈ Γ.E, 2 ≤ (Γ.toHypergraph.ends e).ncard)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalPLinkage Γ.toHypergraph L p)
    (hθ₄_pos : 1 ≤ θ₄)
    (hθ_θ₁ : 2 * θ₄ + θ₁ ≤ θ)
    (hθ₁_pos : 1 ≤ θ₁)
    (h_ind1 : ∀ (Shat' : Type) [TopologicalSpace Shat'],
      IsSurface Shat' → bd Shat' = ∅ → [ConnectedSpace Shat'] →
      IsSimplerThan Shat' S₀ →
      ∀ (S' : Type) [TopologicalSpace S'],
        IsSurface S' → [ConnectedSpace S'] →
        GM19.IsCappedSurface S' Shat' →
        ∀ (Γ' : Surface.Drawing S')
          (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
          IsTangle Γ'.toHypergraph θ₁ T' →
          ¬ HasVitalPLinkage Γ'.toHypergraph (p + 3 * θ₄)) :
    haveI : T2Space S₀ := cap.isSurface.2.1
    let T₁ := mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)
    ∃ d₁ : Set S₀ → Set S₀ → ℕ,
      GM14.HasTangleMetric (capDrawing hS cap Γ) θ₄ T₁ d₁ := by
  have hS₀ : IsSurface S₀ := cap.isSurface
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  haveI : CompactSpace S₀ := hS₀.1
  haveI : T2Space S₀ := hS₀.2.1
  haveI : ConnectedSpace S₀ := cap.connected
  have hbd₀ : bd S₀ = ∅ := cap.bd_empty
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  let Γ_hat := capDrawing hS cap Γ
  let T_hat := mapTangle cap.emb (image cap.emb) 𝒯
  let T₁ := mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)
  have hinj_V : InjOn cap.emb Γ.V := cap.isEmbedding.injective.injOn
  have hinj_E : InjOn (image cap.emb) Γ.E :=
    (Set.image_injective.mpr cap.isEmbedding.injective).injOn
  have h_toH : Γ_hat.toHypergraph = mapHypergraph cap.emb (image cap.emb) Γ.toHypergraph :=
    toHypergraph_mapDrawingInjOn Γ cap.emb
      cap.isEmbedding.continuous.continuousOn cap.isEmbedding.injective.injOn
  have hT_hat : IsTangle Γ_hat.toHypergraph θ T_hat := by
    rw [h_toH]
    exact isTangle_mapHypergraph hinj_V hinj_E h𝒯
  have h𝒯_θ₄ : IsTangle Γ.toHypergraph θ₄ (truncation 𝒯 θ₄) :=
    h𝒯.truncation hθ₄_pos (by omega)
  have hT₁ : IsTangle Γ_hat.toHypergraph θ₄ T₁ := by
    rw [h_toH]
    exact isTangle_mapHypergraph hinj_V hinj_E h𝒯_θ₄
  have hL_hat : IsVitalPLinkage Γ_hat.toHypergraph
      (mapHypergraph cap.emb (image cap.emb) L) p := by
    rw [h_toH]
    exact (isVitalPLinkage_mapHypergraph hL.1.1.1 hinj_V hinj_E).mpr hL
  have hΓ_hat_loopless : ∀ e ∈ Γ_hat.E, 2 ≤ (Γ_hat.toHypergraph.ends e).ncard := by
    intro e he
    rw [capDrawing_E] at he
    rcases he with ⟨e₀, he₀, rfl⟩
    have h_ends : Γ_hat.toHypergraph.ends (cap.emb '' e₀) =
        cap.emb '' (Γ.toHypergraph.ends e₀) := by
      rw [h_toH]
      exact ends_mapHypergraph (le_refl Γ.toHypergraph) hinj_E he₀
    rw [h_ends, Set.ncard_image_of_injective _ cap.isEmbedding.injective]
    exact hΓ_loopless e₀ he₀
  -- Step 1: Prove `(PaintingOrDrawing.drawing Γ_hat).IsRespectful θ₄ T₁`.
  have h_resp : (PaintingOrDrawing.drawing Γ_hat).IsRespectful θ₄ T₁ := by
    refine ⟨inferInstance, fun F hF hnorm hcard => ?_⟩
    haveI : Infinite S₀ := infinite_of_isOArc hF
    have hFc : IsClosed F := (isCompact_of_isOArc hF).isClosed
    have h_nonsep : ∀ (Y : Type) [TopologicalSpace Y],
        IsSurface Y → ConnectedSpace Y → ∀ ψ : Y → S₀, IsCutting ψ F → False := by
      intro Y tY hY hYc ψ hψ
      letI := tY
      letI := hYc
      haveI : T2Space Y := hY.2.1
      obtain ⟨Z', tZ', ⟨capY⟩⟩ := exists_cappedSurface _ Y hY inferInstance rfl
      letI := tZ'
      have hZ'_surf : IsSurface Z' := capY.isSurface
      haveI : ConnectedSpace Z' := capY.connected
      have hsimp : IsSimplerThan Z' S₀ :=
        (theorem_4_1_proof hS₀ hY hψ (isCappedSurface_self hS₀ hbd₀) capY).2.2 hbd₀ hF inferInstance
      obtain ⟨Γ', π, fE, rfl, hπ_inj, hfE_inj, hsplit, -, -⟩ :=
        exists_lifted_drawing_of_isCutting hY hS₀ hψ hFc Γ_hat hΓ_hat_loopless hnorm Γ_hat.finite_V
      have hcard' : (F ∩ Γ_hat.V).ncard < θ₄ := hcard
      have hsplit_θ₄ : ObtainedBySplittingLe θ₄ Γ_hat.toHypergraph
          (mapHypergraph π fE (liftDrawing hY hS₀ hψ hFc Γ_hat hΓ_hat_loopless hnorm).toHypergraph) :=
        (hsplit.mono hcard'.le).toObtainedBySplittingLe
      have hAB : ((⊥ : Hypergraph S₀ (Set S₀)), Γ_hat.toHypergraph) ∈ T_hat :=
        bot_self_mem_tangle hT_hat
      have hord0 : separationOrder (⊥ : Hypergraph S₀ (Set S₀)) Γ_hat.toHypergraph ≤ θ₄ := by
        unfold separationOrder
        change ((∅ : Set S₀) ∩ Γ_hat.V).ncard ≤ θ₄
        simp
      exact apply_claim_5_2_5_of_drawing (Shat' := Z')
        (drawing_toHypergraph_isGraph Γ_hat) hT_hat hL_hat hAB hord0 hπ_inj hfE_inj
        hsplit_θ₄ hθ_θ₁ hθ₁_pos
        (fun hsimp' T' hT' => h_ind1 Z' hZ'_surf capY.bd_empty hsimp' Y hY capY _ T' hT')
        hsimp
    have h_sep_side : ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] (hY : IsSurface Y)
        {ψ : Y → S₀} {W₁ W₂ X X' : Set Y} (T_s : TwoSides ψ F W₁ W₂ X X')
        (hc₁ : ConnectedSpace W₁) (hc₂ : ConnectedSpace W₂),
        ((PaintingOrDrawing.drawing Γ_hat).inter (ψ '' W₁),
          (PaintingOrDrawing.drawing Γ_hat).inter (ψ '' W₂)) ∈ T₁ →
        ∃ Δ : Set S₀, IsClosedDisc Δ ∧ subBd Δ = F ∧
          ((PaintingOrDrawing.drawing Γ_hat).inter Δ,
            (PaintingOrDrawing.drawing Γ_hat).interOutside Δ) ∈ T₁ := by
      intro Y tY t2Y hY ψ W₁ W₂ X X' T_s hc₁ hc₂ h_mem
      letI := tY; letI := t2Y
      obtain ⟨hS₁, hconn₁, hcl₁, hS₂, hconn₂, hcl₂, hun, hint, hcl_compl₁, hfr₁, -, -⟩ :=
        twoSides_subsurfaces' hbd₀ hY T_s hF hc₁ hc₂
      let S₁ := ψ '' W₁
      let S₂ := ψ '' W₂
      letI := hconn₁; letI := hconn₂
      obtain ⟨Z₁', tZ₁', ⟨cap₁⟩⟩ := exists_cappedSurface _ S₁ hS₁ hconn₁ rfl
      obtain ⟨Z₂', tZ₂', ⟨cap₂⟩⟩ := exists_cappedSurface _ S₂ hS₂ hconn₂ rfl
      letI := tZ₁'; letI := tZ₂'
      have hZ₂'_surf : IsSurface Z₂' := cap₂.isSurface
      haveI : ConnectedSpace Z₂' := cap₂.connected
      have hnot_simp : ¬ IsSimplerThan Z₂' S₀ := by
        let B_hat_d := Γ_hat.interSet S₂
        have hUC : B_hat_d.U ⊆ S₂ := interSet_U_subset Γ_hat hcl₂
        let Γ' : Surface.Drawing S₂ := GM12.drawingInSubspace B_hat_d S₂ hUC
        have h_map : mapHypergraph (Subtype.val : S₂ → S₀) (image (Subtype.val : S₂ → S₀))
            Γ'.toHypergraph = (PaintingOrDrawing.drawing Γ_hat).inter S₂ :=
          (mapHypergraph_drawingInSubspace_eq B_hat_d S₂ hUC).trans
            (interSet_toHypergraph_eq_inter Γ_hat hcl₂)
        have hπ_inj : InjOn (Subtype.val : S₂ → S₀) Γ'.V := Subtype.val_injective.injOn
        have hfE_inj : InjOn (image (Subtype.val : S₂ → S₀)) Γ'.E :=
          (Set.image_injective.mpr Subtype.val_injective).injOn
        have hsplit : ObtainedBySplittingLe θ₄ ((PaintingOrDrawing.drawing Γ_hat).inter S₂)
            (mapHypergraph (Subtype.val : S₂ → S₀) (image (Subtype.val : S₂ → S₀)) Γ'.toHypergraph) := by
          rw [h_map]
          exact ObtainedBySplittingLe.refl θ₄ _
        have hAB : ((PaintingOrDrawing.drawing Γ_hat).inter S₁,
            (PaintingOrDrawing.drawing Γ_hat).inter S₂) ∈ T_hat := by
          rcases h_mem with ⟨p_orig, hp_trunc, hp_eq⟩
          exact ⟨p_orig, hp_trunc.1, hp_eq⟩
        have hord : separationOrder ((PaintingOrDrawing.drawing Γ_hat).inter S₁)
            ((PaintingOrDrawing.drawing Γ_hat).inter S₂) ≤ θ₄ :=
          (hT₁.order_lt h_mem).le
        exact apply_claim_5_2_5_of_drawing (Shat' := Z₂')
          (drawing_toHypergraph_isGraph Γ_hat) hT_hat hL_hat hAB hord hπ_inj hfE_inj
          hsplit hθ_θ₁ hθ₁_pos
          (fun hsimp' T' hT' => h_ind1 Z₂' hZ₂'_surf cap₂.bd_empty hsimp' S₂ hS₂ cap₂ _ T' hT')
      have hdisc₁ : IsClosedDisc S₁ :=
        ((theorem_4_2_proof hS₀ hS₁ hS₂ hun hint (isCappedSurface_self hS₀ hbd₀) cap₁ cap₂).2.2 hbd₀ hF).resolve_left
          hnot_simp
      have hsubBd₁ : subBd S₁ = F := (GM11.subBd_eq_frontier S₁).trans hfr₁
      have hout_eq : (PaintingOrDrawing.drawing Γ_hat).interOutside S₁ =
          (PaintingOrDrawing.drawing Γ_hat).inter S₂ := by
        change (PaintingOrDrawing.drawing Γ_hat).inter (closure (univ \ S₁)) = _
        rw [hcl_compl₁]
      exact ⟨S₁, hdisc₁, hsubBd₁, hout_eq.symm ▸ h_mem⟩
    obtain ⟨Y, tY, t2Y, ψ, hY, hψ, hcase, -⟩ :=
      exists_cut_loop hS₀ hF (by rw [hbd₀]; exact disjoint_empty F)
    letI := tY; letI := t2Y
    haveI : CompactSpace Y := hY.1
    rcases hcase with ⟨X, X', hdX, hunX, hOX, hOX', b1, b2⟩ | hQ
    · obtain ⟨eX_homeo⟩ := id hOX
      obtain ⟨eX'_homeo⟩ := id hOX'
      have hx : (eX_homeo 1).1 ∈ X := (eX_homeo 1).2
      have hy : (eX'_homeo 1).1 ∈ X' := (eX'_homeo 1).2
      rcases cut_comps hψ hY hOX.isPreconnected hOX'.isPreconnected hunX hx hy with
        hYc | ⟨W₁, W₂, -, -, hX₁, hX₂, hW₁, hW₂, hU, hdW, hc₁, hc₂⟩
      · exact False.elim (h_nonsep Y hY hYc ψ hψ)
      · have hXb : X ⊆ bd Y := fun z hz ↦ hψ.2.2.2.2 (hunX ▸ Or.inl hz)
        have hXb' : X' ⊆ bd Y := fun z hz ↦ hψ.2.2.2.2 (hunX ▸ Or.inr hz)
        let T_s : TwoSides ψ F W₁ W₂ X X' :=
          ⟨hψ, hW₁, hW₂, hU, hdW, hX₁, hX₂, hunX, b1, b2, hXb, hXb'⟩
        obtain ⟨-, -, hcl₁, -, -, -, -, -, hcl_compl₁, hfr₁, -, -⟩ :=
          twoSides_subsurfaces' hbd₀ hY T_s hF hc₁ hc₂
        let S₁ := ψ '' W₁
        let S₂ := ψ '' W₂
        have hout_eq : (PaintingOrDrawing.drawing Γ_hat).interOutside S₁ =
            (PaintingOrDrawing.drawing Γ_hat).inter S₂ := by
          change (PaintingOrDrawing.drawing Γ_hat).inter (closure (univ \ S₁)) = _
          rw [hcl_compl₁]
        have hnorm' : F ∩ Γ_hat.U ⊆ Γ_hat.V := hnorm
        have hsep : Γ_hat.toHypergraph.IsSeparation
            ((PaintingOrDrawing.drawing Γ_hat).inter S₁)
            ((PaintingOrDrawing.drawing Γ_hat).inter S₂) := by
          rw [← hout_eq]
          exact GM11.isSeparation_inter (Γ := PaintingOrDrawing.drawing Γ_hat) hcl₁
            (hfr₁.symm ▸ hnorm')
        have hord_lt : separationOrder
            ((PaintingOrDrawing.drawing Γ_hat).inter S₁)
            ((PaintingOrDrawing.drawing Γ_hat).inter S₂) < θ₄ := by
          rw [← hout_eq]
          have hsub_v : (((PaintingOrDrawing.drawing Γ_hat).inter S₁) ∩
              ((PaintingOrDrawing.drawing Γ_hat).interOutside S₁)).vertexSet ⊆ F ∩ Γ_hat.V := by
            intro v hv
            rw [← hfr₁]
            exact GM11.inter_outside_subset hv
          exact (ncard_le_ncard hsub_v (Γ_hat.finite_V.subset inter_subset_right)).trans_lt hcard
        rcases hT₁.axiom1 hsep hord_lt with h_mem | h_mem
        · exact h_sep_side Y hY T_s hc₁ hc₂ h_mem
        · exact h_sep_side Y hY T_s.symm hc₂ hc₁ h_mem
    · obtain ⟨eQ_homeo⟩ := id hQ
      have ne₀ : (ψ ⁻¹' F).Nonempty := ⟨_, (eQ_homeo 1).2⟩
      have hYc : ConnectedSpace Y := connected_of_cut hψ hY hQ.isPreconnected rfl ne₀
      exact False.elim (h_nonsep Y hY hYc ψ hψ)
  -- Step 2: Deduce `Γ_hat.IsTwoCell` from `theorem_4_3_proof` and `h_resp`.
  have h_twocell : Γ_hat.IsTwoCell := by
    rw [theorem_4_3_proof hS₀ hbd₀ Γ_hat]
    have hV_ne : Γ_hat.V.Nonempty := by
      by_contra h_emp
      rw [not_nonempty_iff_eq_empty] at h_emp
      have h_self_emp : Γ_hat.toHypergraph.vertexSet = (⊥ : Hypergraph S₀ (Set S₀)).vertexSet :=
        h_emp
      exact hT₁.axiom3 (bot_self_mem_tangle hT₁) h_self_emp.symm
    have hU_conn : IsPreconnected Γ_hat.U := by
      rw [capDrawing_U]
      exact hΓ_conn.image cap.emb cap.isEmbedding.continuous.continuousOn
    refine ⟨hV_ne, hU_conn, fun F hF hdis => ?_⟩
    have hnormF : (PaintingOrDrawing.drawing Γ_hat).IsNormal F := by
      intro x ⟨hxF, hxU⟩
      exact (disjoint_left.mp hdis hxF hxU).elim
    have hcardF : (F ∩ Γ_hat.V).ncard < θ₄ := by
      have hemp : F ∩ Γ_hat.V = ∅ :=
        (disjoint_of_subset_right Γ_hat.V_subset_U hdis).inter_eq
      rw [hemp, ncard_empty]
      exact hθ₄_pos
    obtain ⟨Δ, hΔ, hbdΔ, -⟩ := h_resp.2 F hF hnormF hcardF
    have hdiscBdΔ : discBd Δ = F := by
      rw [← GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hΔ, ← GM11.subBd_eq_frontier, hbdΔ]
    exact ⟨Δ, hΔ, hdiscBdΔ⟩
  -- Step 3: Apply `GM12.exists_metric_of_respectful_drawing_tangle`.
  exact GM12.exists_metric_of_respectful_drawing_tangle hcl₀ ⟨h_twocell, hT₁, h_resp⟩

/-! ## 7. Radial cuff-disc shrinking and Claims (9) and (11) of Graph Minors XXI, (5.2) -/

/-- Radial shrinking of `closedBall (0 : ℂ) 1` fixing a finite subset `F ⊆ sphere (0 : ℂ) 1`:
there exists a closed disc `K ⊆ closedBall (0 : ℂ) 1` such that `K ⊆ ball (0 : ℂ) 1 ∪ F` and
`F ⊆ discBd K`. -/
theorem exists_shrunk_closedUnitDisc_fixing_sphere_subset
    {F : Set ℂ} (hF_fin : F.Finite) (hF_sub : F ⊆ Metric.sphere (0 : ℂ) 1) :
    ∃ K : Set ℂ,
      K ⊆ Metric.closedBall (0 : ℂ) 1 ∧
      IsClosedDisc K ∧
      K ⊆ Metric.ball (0 : ℂ) 1 ∪ F ∧
      F ⊆ discBd K := by
  let S₀' : Set ℂ := insert (0 : ℂ) F
  have hS₀'_fin : S₀'.Finite := hF_fin.insert 0
  have hS₀'_closed : IsClosed S₀' := hS₀'_fin.isClosed
  have hS₀'_ne : S₀'.Nonempty := insert_nonempty 0 F
  let c_rad : ℂ → ℝ := fun z => 1 - (1 / 3 : ℝ) * min 1 (Metric.infDist z S₀')
  let Φ₀ : ℂ → ℂ := fun z => c_rad z • z
  have hc_cont : Continuous c_rad :=
    continuous_const.sub
      (continuous_const.mul (continuous_const.min (Metric.continuous_infDist_pt S₀')))
  have hΦ_cont : Continuous Φ₀ := hc_cont.smul continuous_id
  have hc_bounds : ∀ z : ℂ, (2 / 3 : ℝ) ≤ c_rad z ∧ c_rad z ≤ 1 := by
    intro z
    have h1 : 0 ≤ min 1 (Metric.infDist z S₀') := le_min zero_le_one Metric.infDist_nonneg
    have h2 : min 1 (Metric.infDist z S₀') ≤ 1 := min_le_left 1 _
    dsimp [c_rad]
    constructor <;> linarith
  have hc_pos : ∀ z : ℂ, 0 < c_rad z := fun z => by linarith [(hc_bounds z).1]
  have hc_lip : ∀ x y : ℂ, |c_rad x - c_rad y| ≤ (1 / 3 : ℝ) * ‖y - x‖ := by
    intro x y
    have hd1 : Metric.infDist x S₀' ≤ Metric.infDist y S₀' + dist x y :=
      Metric.infDist_le_infDist_add_dist
    have hd2 : Metric.infDist y S₀' ≤ Metric.infDist x S₀' + dist y x :=
      Metric.infDist_le_infDist_add_dist
    rw [dist_comm, dist_eq_norm] at hd1
    rw [dist_eq_norm] at hd2
    have h_diff : c_rad x - c_rad y =
        (1 / 3 : ℝ) * (min 1 (Metric.infDist y S₀') - min 1 (Metric.infDist x S₀')) := by
      dsimp [c_rad]
      ring
    rw [h_diff, abs_le]
    rcases le_total 1 (Metric.infDist x S₀') with hx1 | hx1 <;>
      rcases le_total 1 (Metric.infDist y S₀') with hy1 | hy1 <;>
      simp only [min_eq_left, min_eq_right, hx1, hy1] <;>
      constructor <;> linarith [norm_nonneg (y - x)]
  have hΦ_inj : InjOn Φ₀ (Metric.closedBall (0 : ℂ) 1) := by
    intro x hx y hy hxy
    have hy_norm : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
    have h_id : c_rad x • (y - x) = (c_rad x - c_rad y) • y := by
      rw [smul_sub, sub_smul (c_rad x) (c_rad y) y]
      exact congrArg (c_rad x • y - ·) hxy
    have h_norm := congrArg norm h_id
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h_norm
    have hcx : (2 / 3 : ℝ) ≤ |c_rad x| := (hc_bounds x).1.trans (le_abs_self _)
    have hlip : |c_rad x - c_rad y| ≤ (1 / 3 : ℝ) * ‖y - x‖ := hc_lip x y
    have h_diff_nonneg : 0 ≤ ‖y - x‖ := norm_nonneg _
    have h_y_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
    have h_zero : ‖y - x‖ = 0 := by nlinarith
    exact (sub_eq_zero.mp (norm_eq_zero.mp h_zero)).symm
  have hΦ_fix : ∀ z ∈ F, Φ₀ z = z := by
    intro z hz
    have h_inf : Metric.infDist z S₀' = 0 := Metric.infDist_zero_of_mem (Or.inr hz)
    have hc1 : c_rad z = 1 := by simp [c_rad, h_inf]
    simp [Φ₀, hc1]
  have hΦ_ball : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, z ∉ F → Φ₀ z ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz hzF
    rw [Metric.mem_ball, dist_zero_right]
    change ‖c_rad z • z‖ < 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hc_pos z)]
    have hz_le : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    rcases lt_or_eq_of_le hz_le with hz_lt | hz_eq
    · have hc1 : c_rad z ≤ 1 := (hc_bounds z).2
      have hz_nn : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith
    · have hz_ne0 : z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hz_eq
        norm_num at hz_eq
      have hz_not_S₀' : z ∉ S₀' := by
        rintro (rfl | hzF')
        · exact hz_ne0 rfl
        · exact hzF hzF'
      have h_inf_pos : 0 < Metric.infDist z S₀' :=
        (hS₀'_closed.notMem_iff_infDist_pos hS₀'_ne).mp hz_not_S₀'
      have h_min_pos : 0 < min 1 (Metric.infDist z S₀') := lt_min zero_lt_one h_inf_pos
      have hc_lt : c_rad z < 1 := by
        dsimp [c_rad]
        linarith
      rw [hz_eq, mul_one]
      exact hc_lt
  obtain ⟨Φinv, hΦinv, hΦl⟩ :=
    Surface.exists_inv_of_compactOn (isCompact_closedBall (0 : ℂ) 1) hΦ_cont.continuousOn hΦ_inj
  obtain ⟨hK_disc, hK_bd⟩ :=
    Surface.isClosedDisc_closedBall.1.image hΦ_cont.continuousOn hΦinv hΦl
  rw [Surface.isClosedDisc_closedBall.2] at hK_bd
  have hK_sub_ball_F : Φ₀ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 ∪ F := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzF : z ∈ F
    · rw [hΦ_fix z hzF]
      exact Or.inr hzF
    · exact Or.inl (hΦ_ball z hz hzF)
  have hK_sub_cb : Φ₀ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro w hw
    rcases hK_sub_ball_F hw with hw_ball | hwF
    · exact Metric.ball_subset_closedBall hw_ball
    · exact Metric.sphere_subset_closedBall (hF_sub hwF)
  refine ⟨Φ₀ '' Metric.closedBall (0 : ℂ) 1, hK_sub_cb, hK_disc, hK_sub_ball_F, ?_⟩
  rw [hK_bd]
  intro z hzF
  exact ⟨z, hF_sub hzF, hΦ_fix z hzF⟩

/-- Given a closed disc `E` in a topological space `Z` and a finite subset `A ⊆ discBd E`, there is
a closed subdisc `D ⊆ E` such that `D ⊆ discInt E ∪ A`, `discInt D ⊆ discInt E`, and
`A ⊆ discBd D`. -/
theorem exists_subdisc_fixing_bd_subset {Z : Type*} [TopologicalSpace Z]
    {E : Set Z} (hE : IsClosedDisc E) {A : Set Z} (hA_fin : A.Finite) (hA_sub : A ⊆ discBd E) :
    ∃ D : Set Z,
      D ⊆ E ∧
      IsClosedDisc D ∧
      D ⊆ discInt E ∪ A ∧
      discInt D ⊆ discInt E ∧
      A ⊆ discBd D := by
  obtain ⟨h, g, c⟩ := hE.exists_isChart
  let F : Set ℂ := h '' A
  have hF_fin : F.Finite := hA_fin.image h
  have hF_sub : F ⊆ Metric.sphere (0 : ℂ) 1 := by
    rintro _ ⟨u, huA, rfl⟩
    exact c.bd ▸ mem_image_of_mem h (hA_sub huA)
  obtain ⟨K, hK_sub, hK_disc, hK_ball_F, hF_bd⟩ :=
    exists_shrunk_closedUnitDisc_fixing_sphere_subset hF_fin hF_sub
  obtain ⟨hD_disc, hD_bd⟩ := c.disc_g hK_sub hK_disc
  have hA_E : A ⊆ E := hA_sub.trans (Surface.discBd_subset E)
  have hgF : g '' F = A := c.g_h hA_E
  have hD_sub_int_A : g '' K ⊆ discInt E ∪ A := by
    calc g '' K ⊆ g '' (Metric.ball (0 : ℂ) 1 ∪ F) := image_mono hK_ball_F
      _ = g '' Metric.ball (0 : ℂ) 1 ∪ g '' F := image_union g _ _
      _ = discInt E ∪ A := by rw [c.discInt_eq, hgF]
  have hA_sub_bdD : A ⊆ discBd (g '' K) := by
    rw [hD_bd, ← hgF]
    exact image_mono hF_bd
  have hD_int_sub : discInt (g '' K) ⊆ discInt E := by
    intro x hx
    rcases hD_sub_int_A hx.1 with hx_int | hx_A
    · exact hx_int
    · exact (hx.2 (hA_sub_bdD hx_A)).elim
  exact ⟨g '' K, c.g_subset hK_sub, hD_disc, hD_sub_int_A, hD_int_sub, hA_sub_bdD⟩

/-- Radial shrinking of `closedBall (0 : ℂ) 1` fixing both a compact subset
`K₀ ⊆ ball (0 : ℂ) 1` and a finite subset `F ⊆ sphere (0 : ℂ) 1`, together with radial lines from
each `z₀ ∈ sphere (0 : ℂ) 1 \ F` to `discBd K`. -/
theorem exists_shrunk_closedUnitDisc_fixing_sphere_and_int
    {K₀ F : Set ℂ} (hK₀_comp : IsCompact K₀) (hK₀_sub : K₀ ⊆ Metric.ball (0 : ℂ) 1)
    (hF_fin : F.Finite) (hF_sub : F ⊆ Metric.sphere (0 : ℂ) 1) :
    ∃ K : Set ℂ,
      K ⊆ Metric.closedBall (0 : ℂ) 1 ∧
      IsClosedDisc K ∧
      K ⊆ Metric.ball (0 : ℂ) 1 ∪ F ∧
      F ⊆ discBd K ∧
      K₀ ⊆ discInt K ∧
      (∀ z₀ ∈ Metric.sphere (0 : ℂ) 1 \ F,
        ∃ w₀ ∈ discBd K, ∃ L_ℂ : Set ℂ,
          IsLineWithEnds L_ℂ z₀ w₀ ∧
          L_ℂ ⊆ Metric.ball (0 : ℂ) 1 ∪ {z₀} ∧
          L_ℂ ∩ K = {w₀}) := by
  let S₀' : Set ℂ := insert (0 : ℂ) (K₀ ∪ F)
  have hS₀'_comp : IsCompact S₀' := (hK₀_comp.union hF_fin.isCompact).insert 0
  have hS₀'_closed : IsClosed S₀' := hS₀'_comp.isClosed
  have hS₀'_ne : S₀'.Nonempty := insert_nonempty 0 (K₀ ∪ F)
  let c_rad : ℂ → ℝ := fun z => 1 - (1 / 3 : ℝ) * min 1 (Metric.infDist z S₀')
  let Φ₀ : ℂ → ℂ := fun z => c_rad z • z
  have hc_cont : Continuous c_rad :=
    continuous_const.sub
      (continuous_const.mul (continuous_const.min (Metric.continuous_infDist_pt S₀')))
  have hΦ_cont : Continuous Φ₀ := hc_cont.smul continuous_id
  have hc_bounds : ∀ z : ℂ, (2 / 3 : ℝ) ≤ c_rad z ∧ c_rad z ≤ 1 := by
    intro z
    have h1 : 0 ≤ min 1 (Metric.infDist z S₀') := le_min zero_le_one Metric.infDist_nonneg
    have h2 : min 1 (Metric.infDist z S₀') ≤ 1 := min_le_left 1 _
    dsimp [c_rad]
    constructor <;> linarith
  have hc_pos : ∀ z : ℂ, 0 < c_rad z := fun z => by linarith [(hc_bounds z).1]
  have hc_lip : ∀ x y : ℂ, |c_rad x - c_rad y| ≤ (1 / 3 : ℝ) * ‖y - x‖ := by
    intro x y
    have hd1 : Metric.infDist x S₀' ≤ Metric.infDist y S₀' + dist x y :=
      Metric.infDist_le_infDist_add_dist
    have hd2 : Metric.infDist y S₀' ≤ Metric.infDist x S₀' + dist y x :=
      Metric.infDist_le_infDist_add_dist
    rw [dist_comm, dist_eq_norm] at hd1
    rw [dist_eq_norm] at hd2
    have h_diff : c_rad x - c_rad y =
        (1 / 3 : ℝ) * (min 1 (Metric.infDist y S₀') - min 1 (Metric.infDist x S₀')) := by
      dsimp [c_rad]
      ring
    rw [h_diff, abs_le]
    rcases le_total 1 (Metric.infDist x S₀') with hx1 | hx1 <;>
      rcases le_total 1 (Metric.infDist y S₀') with hy1 | hy1 <;>
      simp only [min_eq_left, min_eq_right, hx1, hy1] <;>
      constructor <;> linarith [norm_nonneg (y - x)]
  have hΦ_inj : InjOn Φ₀ (Metric.closedBall (0 : ℂ) 1) := by
    intro x hx y hy hxy
    have hy_norm : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
    have h_id : c_rad x • (y - x) = (c_rad x - c_rad y) • y := by
      rw [smul_sub, sub_smul (c_rad x) (c_rad y) y]
      exact congrArg (c_rad x • y - ·) hxy
    have h_norm := congrArg norm h_id
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h_norm
    have hcx : (2 / 3 : ℝ) ≤ |c_rad x| := (hc_bounds x).1.trans (le_abs_self _)
    have hlip : |c_rad x - c_rad y| ≤ (1 / 3 : ℝ) * ‖y - x‖ := hc_lip x y
    have h_diff_nonneg : 0 ≤ ‖y - x‖ := norm_nonneg _
    have h_y_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
    have h_zero : ‖y - x‖ = 0 := by nlinarith
    exact (sub_eq_zero.mp (norm_eq_zero.mp h_zero)).symm
  have hΦ_fix_S₀' : ∀ z ∈ S₀', Φ₀ z = z := by
    intro z hz
    have h_inf : Metric.infDist z S₀' = 0 := Metric.infDist_zero_of_mem hz
    have hc1 : c_rad z = 1 := by simp [c_rad, h_inf]
    simp [Φ₀, hc1]
  have hΦ_fix : ∀ z ∈ F, Φ₀ z = z := fun z hz => hΦ_fix_S₀' z (Or.inr (Or.inr hz))
  have hΦ_fix_K₀ : ∀ z ∈ K₀, Φ₀ z = z := fun z hz => hΦ_fix_S₀' z (Or.inr (Or.inl hz))
  have hc_lt_of_sphere_diff : ∀ z₀ ∈ Metric.sphere (0 : ℂ) 1 \ F, c_rad z₀ < 1 := by
    intro z₀ ⟨hz₀_sph, hz₀_F⟩
    have hz₀_norm : ‖z₀‖ = 1 := mem_sphere_zero_iff_norm.mp hz₀_sph
    have hz₀_ne0 : z₀ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hz₀_norm
      norm_num at hz₀_norm
    have hz₀_not_K₀ : z₀ ∉ K₀ := by
      intro hzK₀
      have hlt : ‖z₀‖ < 1 := mem_ball_zero_iff.mp (hK₀_sub hzK₀)
      linarith
    have hz₀_not_S₀' : z₀ ∉ S₀' := by
      rintro (rfl | hzK₀ | hzF')
      · exact hz₀_ne0 rfl
      · exact hz₀_not_K₀ hzK₀
      · exact hz₀_F hzF'
    have h_inf_pos : 0 < Metric.infDist z₀ S₀' :=
      (hS₀'_closed.notMem_iff_infDist_pos hS₀'_ne).mp hz₀_not_S₀'
    have h_min_pos : 0 < min 1 (Metric.infDist z₀ S₀') := lt_min zero_lt_one h_inf_pos
    dsimp [c_rad]
    linarith
  have hΦ_ball : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, z ∉ F → Φ₀ z ∈ Metric.ball (0 : ℂ) 1 := by
    intro z hz hzF
    rw [Metric.mem_ball, dist_zero_right]
    change ‖c_rad z • z‖ < 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hc_pos z)]
    have hz_le : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    rcases lt_or_eq_of_le hz_le with hz_lt | hz_eq
    · have hc1 : c_rad z ≤ 1 := (hc_bounds z).2
      have hz_nn : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith
    · have hz_sph : z ∈ Metric.sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr hz_eq
      have hc_lt : c_rad z < 1 := hc_lt_of_sphere_diff z ⟨hz_sph, hzF⟩
      rw [hz_eq, mul_one]
      exact hc_lt
  obtain ⟨Φinv, hΦinv, hΦl⟩ :=
    Surface.exists_inv_of_compactOn (isCompact_closedBall (0 : ℂ) 1) hΦ_cont.continuousOn hΦ_inj
  obtain ⟨hK_disc, hK_bd⟩ :=
    Surface.isClosedDisc_closedBall.1.image hΦ_cont.continuousOn hΦinv hΦl
  rw [Surface.isClosedDisc_closedBall.2] at hK_bd
  have hK_sub_ball_F : Φ₀ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 ∪ F := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hzF : z ∈ F
    · rw [hΦ_fix z hzF]
      exact Or.inr hzF
    · exact Or.inl (hΦ_ball z hz hzF)
  have hK_sub_cb : Φ₀ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro w hw
    rcases hK_sub_ball_F hw with hw_ball | hwF
    · exact Metric.ball_subset_closedBall hw_ball
    · exact Metric.sphere_subset_closedBall (hF_sub hwF)
  have hK₀_int : K₀ ⊆ discInt (Φ₀ '' Metric.closedBall (0 : ℂ) 1) := by
    intro z hzK₀
    have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := hK₀_sub hzK₀
    have hz_cb : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz_ball
    refine ⟨⟨z, hz_cb, hΦ_fix_K₀ z hzK₀⟩, ?_⟩
    rw [hK_bd]
    rintro ⟨w, hw_sph, hw_eq⟩
    have hw_cb : w ∈ Metric.closedBall (0 : ℂ) 1 := Metric.sphere_subset_closedBall hw_sph
    have hwz : w = z := hΦ_inj hw_cb hz_cb (hw_eq.trans (hΦ_fix_K₀ z hzK₀).symm)
    subst hwz
    have hlt : ‖w‖ < 1 := mem_ball_zero_iff.mp hz_ball
    have heq : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw_sph
    linarith
  refine ⟨Φ₀ '' Metric.closedBall (0 : ℂ) 1, hK_sub_cb, hK_disc, hK_sub_ball_F, ?_, hK₀_int, ?_⟩
  · rw [hK_bd]
    intro z hzF
    exact ⟨z, hF_sub hzF, hΦ_fix z hzF⟩
  · intro z₀ hz₀
    have hz₀_sph : z₀ ∈ Metric.sphere (0 : ℂ) 1 := hz₀.1
    have hz₀_norm : ‖z₀‖ = 1 := mem_sphere_zero_iff_norm.mp hz₀_sph
    have hc_lt : c_rad z₀ < 1 := hc_lt_of_sphere_diff z₀ hz₀
    let w₀ : ℂ := Φ₀ z₀
    have hw₀_bd : w₀ ∈ discBd (Φ₀ '' Metric.closedBall (0 : ℂ) 1) := by
      rw [hK_bd]
      exact ⟨z₀, hz₀_sph, rfl⟩
    let γ : unitInterval → ℂ := fun t => (1 - (t : ℝ) * (1 - c_rad z₀)) • z₀
    let L_ℂ : Set ℂ := range γ
    have hγ_cont : Continuous γ :=
      (continuous_const.sub (continuous_subtype_val.mul continuous_const)).smul continuous_const
    have hγ_inj : Function.Injective γ := by
      intro t₁ t₂ ht
      have h_sub : (((t₂ : ℝ) - (t₁ : ℝ)) * (1 - c_rad z₀)) • z₀ = 0 := by
        have h1 : (1 - (t₁ : ℝ) * (1 - c_rad z₀)) - (1 - (t₂ : ℝ) * (1 - c_rad z₀)) =
            ((t₂ : ℝ) - (t₁ : ℝ)) * (1 - c_rad z₀) := by ring
        rw [← h1, sub_smul]
        exact sub_eq_zero.mpr ht
      have h_norm := congrArg norm h_sub
      rw [norm_smul, norm_zero, hz₀_norm, mul_one, Real.norm_eq_abs, abs_eq_zero] at h_norm
      rcases mul_eq_zero.mp h_norm with h_eq | h_eq
      · exact Subtype.ext (by linarith)
      · linarith
    have hγ0 : γ 0 = z₀ := by simp [γ]
    have hγ1 : γ 1 = w₀ := by
      dsimp [γ, w₀, Φ₀]
      congr 1
      simp
    have hγ_arc : IsArcMap γ := ⟨hγ_cont, hγ_inj⟩
    have hL_line : IsLineWithEnds L_ℂ z₀ w₀ := by
      have h := hγ_arc.isLineWithEnds
      rwa [hγ0, hγ1] at h
    have hL_sub : L_ℂ ⊆ Metric.ball (0 : ℂ) 1 ∪ {z₀} := by
      rintro _ ⟨t, rfl⟩
      have ht0 : 0 ≤ (t : ℝ) := t.2.1
      have ht1 : (t : ℝ) ≤ 1 := t.2.2
      rcases eq_or_lt_of_le ht0 with ht_zero | ht_pos
      · have ht_eq : t = 0 := Subtype.ext ht_zero.symm
        rw [ht_eq, hγ0]
        exact Or.inr rfl
      · left
        rw [Metric.mem_ball, dist_zero_right]
        change ‖(1 - (t : ℝ) * (1 - c_rad z₀)) • z₀‖ < 1
        rw [norm_smul, hz₀_norm, mul_one, Real.norm_eq_abs]
        have hr_pos : 0 < 1 - (t : ℝ) * (1 - c_rad z₀) := by
          have hc_ge : (2 / 3 : ℝ) ≤ c_rad z₀ := (hc_bounds z₀).1
          nlinarith
        rw [abs_of_pos hr_pos]
        nlinarith
    have hL_inter : L_ℂ ∩ (Φ₀ '' Metric.closedBall (0 : ℂ) 1) = {w₀} := by
      ext u
      simp only [mem_inter_iff, mem_singleton_iff]
      constructor
      · rintro ⟨⟨t, rfl⟩, ⟨z, hz_cb, hz_eq⟩⟩
        have ht0 : 0 ≤ (t : ℝ) := t.2.1
        have ht1 : (t : ℝ) ≤ 1 := t.2.2
        let r : ℝ := 1 - (t : ℝ) * (1 - c_rad z₀)
        have hr_ge : c_rad z₀ ≤ r := by
          dsimp [r]
          nlinarith
        have hr_pos : 0 < r := lt_of_lt_of_le (hc_pos z₀) hr_ge
        let s : ℝ := r / c_rad z
        have hs_pos : 0 < s := div_pos hr_pos (hc_pos z)
        have hrs : r = c_rad z * s := (mul_div_cancel₀ r (ne_of_gt (hc_pos z))).symm
        have hz_eq_s : z = s • z₀ := by
          have h1 : c_rad z • z = c_rad z • (s • z₀) := by
            rw [← mul_smul, ← hrs]
            exact hz_eq
          exact smul_right_injective ℂ (ne_of_gt (hc_pos z)) h1
        have hz_norm_le : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz_cb
        have hs_le_one : s ≤ 1 := by
          rw [hz_eq_s, norm_smul, hz₀_norm, mul_one, Real.norm_eq_abs, abs_of_pos hs_pos] at hz_norm_le
          exact hz_norm_le
        have hdiff_norm : ‖z₀ - z‖ = 1 - s := by
          have h1 : z₀ - z = (1 - s) • z₀ := by
            rw [hz_eq_s, sub_smul, one_smul]
          rw [h1, norm_smul, hz₀_norm, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        have hlip := hc_lip z z₀
        rw [hdiff_norm] at hlip
        have hcz_le : c_rad z ≤ c_rad z₀ + (1 / 3 : ℝ) * (1 - s) := by
          linarith [(le_abs_self (c_rad z - c_rad z₀)).trans hlip]
        have hc0_ge : (2 / 3 : ℝ) ≤ c_rad z₀ := (hc_bounds z₀).1
        have hr_le : r ≤ (c_rad z₀ + (1 / 3 : ℝ) * (1 - s)) * s := by
          rw [hrs]
          exact mul_le_mul_of_nonneg_right hcz_le (le_of_lt hs_pos)
        have hs_eq_one : s = 1 := by nlinarith
        have hzz₀ : z = z₀ := by rw [hz_eq_s, hs_eq_one, one_smul]
        have hr_eq : 1 - (t : ℝ) * (1 - c_rad z₀) = c_rad z₀ := by
          change r = c_rad z₀
          rw [hrs, hs_eq_one, mul_one, hzz₀]
        have ht_coe : (t : ℝ) = 1 := by nlinarith
        have ht_eq_one : t = 1 := Subtype.ext ht_coe
        rw [ht_eq_one, hγ1]
      · rintro rfl
        exact ⟨⟨1, hγ1⟩, ⟨z₀, Metric.sphere_subset_closedBall hz₀_sph, rfl⟩⟩
    exact ⟨w₀, hw₀_bd, L_ℂ, hL_line, hL_sub, hL_inter⟩

/-- Given a closed disc `E` in a T2 space `Z`, a compact subset `E₀ ⊆ discInt E`, and a finite
subset `A ⊆ discBd E`, there is a closed subdisc `D ⊆ E` such that `D ⊆ discInt E ∪ A`,
`discInt D ⊆ discInt E`, `A ⊆ discBd D`, `E₀ ⊆ discInt D`, and every `p ∈ discBd E \ A` is joined
to some `q ∈ discBd D` by a line `L₀ ⊆ discInt E ∪ {p}` with `L₀ ∩ D = {q}`. -/
theorem exists_subdisc_fixing_bd_subset_and_int {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    {E E₀ : Set Z} (hE : IsClosedDisc E) (hE₀_comp : IsCompact E₀) (hE₀_sub : E₀ ⊆ discInt E)
    {A : Set Z} (hA_fin : A.Finite) (hA_sub : A ⊆ discBd E) :
    ∃ D : Set Z,
      D ⊆ E ∧
      IsClosedDisc D ∧
      D ⊆ discInt E ∪ A ∧
      discInt D ⊆ discInt E ∧
      A ⊆ discBd D ∧
      E₀ ⊆ discInt D ∧
      (∀ p ∈ discBd E \ A,
        ∃ q ∈ discBd D, ∃ L₀ : Set Z,
          IsLineWithEnds L₀ p q ∧
          L₀ ⊆ discInt E ∪ {p} ∧
          L₀ ∩ D = {q}) := by
  obtain ⟨h, g, c⟩ := hE.exists_isChart
  let K₀ : Set ℂ := h '' E₀
  let F : Set ℂ := h '' A
  have hE₀_E : E₀ ⊆ E := hE₀_sub.trans (fun _ hx => hx.1)
  have hK₀_comp : IsCompact K₀ := hE₀_comp.image_of_continuousOn (c.hc.mono hE₀_E)
  have hK₀_sub : K₀ ⊆ Metric.ball (0 : ℂ) 1 := by
    rintro _ ⟨u, huE₀, rfl⟩
    have hu_int : u ∈ g '' Metric.ball (0 : ℂ) 1 := by
      rw [← c.discInt_eq]
      exact hE₀_sub huE₀
    rcases hu_int with ⟨z, hz_ball, rfl⟩
    rw [c.hg (Metric.ball_subset_closedBall hz_ball)]
    exact hz_ball
  have hF_fin : F.Finite := hA_fin.image h
  have hF_sub : F ⊆ Metric.sphere (0 : ℂ) 1 := by
    rintro _ ⟨u, huA, rfl⟩
    exact c.bd ▸ mem_image_of_mem h (hA_sub huA)
  obtain ⟨K, hK_sub, hK_disc, hK_ball_F, hF_bd, hK₀_int, h_rad⟩ :=
    exists_shrunk_closedUnitDisc_fixing_sphere_and_int hK₀_comp hK₀_sub hF_fin hF_sub
  obtain ⟨hD_disc, hD_bd⟩ := c.disc_g hK_sub hK_disc
  have hA_E : A ⊆ E := hA_sub.trans (Surface.discBd_subset E)
  have hgF : g '' F = A := c.g_h hA_E
  have hgK₀ : g '' K₀ = E₀ := c.g_h hE₀_E
  have hD_sub_int_A : g '' K ⊆ discInt E ∪ A := by
    calc g '' K ⊆ g '' (Metric.ball (0 : ℂ) 1 ∪ F) := image_mono hK_ball_F
      _ = g '' Metric.ball (0 : ℂ) 1 ∪ g '' F := image_union g _ _
      _ = discInt E ∪ A := by rw [c.discInt_eq, hgF]
  have hA_sub_bdD : A ⊆ discBd (g '' K) := by
    rw [hD_bd, ← hgF]
    exact image_mono hF_bd
  have hD_int_sub : discInt (g '' K) ⊆ discInt E := by
    intro x hx
    rcases hD_sub_int_A hx.1 with hx_int | hx_A
    · exact hx_int
    · exact (hx.2 (hA_sub_bdD hx_A)).elim
  have hE₀_sub_intD : E₀ ⊆ discInt (g '' K) := by
    rw [← hgK₀]
    rintro _ ⟨z, hzK₀, rfl⟩
    have hz_intK : z ∈ discInt K := hK₀_int hzK₀
    refine ⟨mem_image_of_mem g hz_intK.1, ?_⟩
    rw [hD_bd]
    rintro ⟨w, hw_bdK, hw_eq⟩
    have hwz : w = z :=
      c.injOn (hK_sub (Surface.discBd_subset K hw_bdK)) (hK_sub hz_intK.1) hw_eq
    subst hwz
    exact hz_intK.2 hw_bdK
  refine ⟨g '' K, c.g_subset hK_sub, hD_disc, hD_sub_int_A, hD_int_sub, hA_sub_bdD, hE₀_sub_intD, ?_⟩
  intro p ⟨hp_bd, hp_notA⟩
  let z₀ : ℂ := h p
  have hp_E : p ∈ E := Surface.discBd_subset E hp_bd
  have hgz₀ : g z₀ = p := c.gh hp_E
  have hz₀_sph : z₀ ∈ Metric.sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hp_bd
  have hz₀_notF : z₀ ∉ F := by
    rintro ⟨u, huA, hu_eq⟩
    have hup : u = p := c.gh.injOn (hA_E huA) hp_E hu_eq
    subst hup
    exact hp_notA huA
  obtain ⟨w₀, hw₀_bdK, L_ℂ, hL_line, hL_sub, hL_inter⟩ := h_rad z₀ ⟨hz₀_sph, hz₀_notF⟩
  let q : Z := g w₀
  have hq_bdD : q ∈ discBd (g '' K) := by
    rw [hD_bd]
    exact mem_image_of_mem g hw₀_bdK
  let L₀ : Set Z := g '' L_ℂ
  have hL_ℂ_cb : L_ℂ ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro w hw
    rcases hL_sub hw with hw_ball | rfl
    · exact Metric.ball_subset_closedBall hw_ball
    · exact Metric.sphere_subset_closedBall hz₀_sph
  obtain ⟨u, hu, hL_range, hu0, hu1⟩ := hL_line.exists_arc
  have hu_cb : ∀ t, u t ∈ Metric.closedBall (0 : ℂ) 1 :=
    fun t => hL_ℂ_cb (hL_range ▸ mem_range_self t)
  have hgu_arc : IsArcMap (g ∘ u) :=
    ⟨c.gc.comp_continuous hu.1 hu_cb,
      fun s t hst => hu.2 (c.injOn (hu_cb s) (hu_cb t) hst)⟩
  have hL₀_line : IsLineWithEnds L₀ p q := by
    have h := hgu_arc.isLineWithEnds
    dsimp [L₀]
    rw [← hL_range, ← range_comp]
    rwa [Function.comp_apply, hu0, hgz₀, Function.comp_apply, hu1] at h
  have hL₀_sub : L₀ ⊆ discInt E ∪ {p} := by
    calc L₀ = g '' L_ℂ := rfl
      _ ⊆ g '' (Metric.ball (0 : ℂ) 1 ∪ {z₀}) := image_mono hL_sub
      _ = g '' Metric.ball (0 : ℂ) 1 ∪ {g z₀} := by rw [image_union, image_singleton]
      _ = discInt E ∪ {p} := by rw [c.discInt_eq, hgz₀]
  have hL₀_inter : L₀ ∩ (g '' K) = {q} := by
    rw [← c.g_inter hL_ℂ_cb hK_sub, hL_inter, image_singleton]
  exact ⟨q, hq_bdD, L₀, hL₀_line, hL₀_sub, hL₀_inter⟩

/-- Core punctured-surface reduction for **Claims (9) and (11)** of **Graph Minors XXI, (5.2)**
(pages 20–21 of the preprint):
for any `Γ`-normal `O`-arc `F ⊆ S` and closed disc `D ⊆ S₀` with `subBd D = cap.emb '' F` and
`((PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter D,
  (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).interOutside D) ∈ T₁`,
1. at most one cuff `C ∈ cuffs S` has `¬ Disjoint (cap.cuffDisc C) D` (equivalently
   `cap.cuffDisc C ⊆ discInt D`), and
2. for every cuff `C ∈ cuffs S` with `cap.emb '' C ⊆ D`, `(C ∩ Γ.V).ncard ≤ (F ∩ Γ.V).ncard`. -/
theorem claim_5_2_9_and_11_core {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L : Hypergraph S (Set S)}
    {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (h_ind2 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → ConnectedSpace S' →
      GM19.IsCappedSurface S' S₀ →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S')
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
        (L' : Hypergraph S' (Set S')),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        IsTangle Γ'.toHypergraph θ₂ T' →
        IsVitalLinkage Γ'.toHypergraph L' →
        ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → ConnectedSpace S' →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S')
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
        (L' : Hypergraph S' (Set S')),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        IsTangle Γ'.toHypergraph θ₃ T' →
        IsVitalLinkage Γ'.toHypergraph L' →
        ¬ (terminals L' ⊆ bd S'))
    {F : Set S} {D : Set S₀}
    (hnF : (PaintingOrDrawing.drawing Γ).IsNormal F) (hF : IsOArc F)
    (hD : IsClosedDisc D) (hbdD : subBd D = cap.emb '' F)
    (hmD : ((PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter D,
      (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).interOutside D) ∈
        mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)) :
    (∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S,
      ¬ Disjoint (cap.cuffDisc C₁) D → ¬ Disjoint (cap.cuffDisc C₂) D → C₁ = C₂) ∧
    (∀ C ∈ cuffs S, cap.emb '' C ⊆ D → (C ∩ Γ.V).ncard ≤ (F ∩ Γ.V).ncard) := by
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : CompactSpace S₀ := hS₀.1
  haveI : T2Space S₀ := hS₀.2.1
  haveI : ConnectedSpace S₀ := cap.connected
  have hinj_emb : Function.Injective cap.emb := cap.isEmbedding.injective
  have hfrD : frontier D = cap.emb '' F := (GM11.subBd_eq_frontier D).symm.trans hbdD
  have hdiscBd_D : discBd D = cap.emb '' F :=
    (GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hD).symm.trans hfrD
  have hdiscInt_D_open : IsOpen (discInt D) := hD.isOpen_discInt hS₀.2.2
  have hdiscInt_D_eq : discInt D = interior D := by
    rw [Surface.discInt, hdiscBd_D, ← hfrD, frontier, hD.isClosed.closure_eq,
      sdiff_sdiff_right_self, inter_eq_right.mpr interior_subset]
  have hcompl_discInt_D : (discInt D)ᶜ = closure (univ \ D) := by
    rw [hdiscInt_D_eq, ← closure_compl, compl_eq_univ_sdiff]
  -- Every cuff disc is either inside `discInt D` or disjoint from `D`.
  have h_cuff_side : ∀ C' ∈ cuffs S,
      cap.cuffDisc C' ⊆ discInt D ∨ Disjoint (cap.cuffDisc C') D := by
    intro C' hC'
    have h_pre : IsPreconnected (cap.cuffDisc C') := by
      rw [cap.cuffDisc_eq_discInt hS hC']
      exact (cap.cuffDisc_closedDisc C' hC').isPreconnected_discInt
    have h_disj_bd : Disjoint (cap.cuffDisc C') (discBd D) := by
      rw [hdiscBd_D]
      refine disjoint_left.mpr fun x hx_disc ⟨s, _, hsx⟩ => ?_
      have hx_compl : x ∈ (range cap.emb)ᶜ := by
        rw [cap.compl_eq]
        exact mem_iUnion₂.mpr ⟨C', hC', hx_disc⟩
      exact hx_compl ⟨s, hsx⟩
    exact hD.side hS₀.2.2 h_pre h_disj_bd
  -- Build the family of shrunk cuff discs for `CuffsOut`.
  classical
  let CuffsOut : Set (Set S) := {C' ∈ cuffs S | Disjoint (cap.cuffDisc C') D}
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hCuffsOut_fin : CuffsOut.Finite := hcuffs_fin.subset (sep_subset _ _)
  haveI : Finite CuffsOut := hCuffsOut_fin.to_subtype
  have h_shrunk : ∀ c : CuffsOut, ∃ P_c : Set S₀,
      P_c ⊆ closure (cap.cuffDisc c.1) ∧
      IsClosedDisc P_c ∧
      P_c ⊆ cap.cuffDisc c.1 ∪ cap.emb '' ((c.1 ∩ Γ.V) \ F) ∧
      discInt P_c ⊆ cap.cuffDisc c.1 ∧
      cap.emb '' ((c.1 ∩ Γ.V) \ F) ⊆ discBd P_c := by
    intro c
    have hE_disc : IsClosedDisc (closure (cap.cuffDisc c.1)) :=
      cap.cuffDisc_closedDisc c.1 c.2.1
    have hE_bd : discBd (closure (cap.cuffDisc c.1)) = cap.emb '' c.1 :=
      cap.cuffDisc_bd c.1 c.2.1
    have hE_int : discInt (closure (cap.cuffDisc c.1)) = cap.cuffDisc c.1 :=
      (cap.cuffDisc_eq_discInt hS c.2.1).symm
    have hA_fin : (cap.emb '' ((c.1 ∩ Γ.V) \ F)).Finite :=
      ((Γ.finite_V.subset inter_subset_right).sdiff).image cap.emb
    have hA_sub : cap.emb '' ((c.1 ∩ Γ.V) \ F) ⊆ discBd (closure (cap.cuffDisc c.1)) := by
      rw [hE_bd]
      exact image_mono (sdiff_subset.trans inter_subset_left)
    obtain ⟨P_c, hP_sub, hP_disc, hP_int_A, hP_int, hP_bd⟩ :=
      exists_subdisc_fixing_bd_subset hE_disc hA_fin hA_sub
    rw [hE_int] at hP_int_A hP_int
    exact ⟨P_c, hP_sub, hP_disc, hP_int_A, hP_int, hP_bd⟩
  choose P_c hP_c_sub_cl hP_c_disc hP_c_sub_union hP_c_int hP_c_bd using h_shrunk
  let P : Option CuffsOut → Set S₀ := fun i =>
    match i with
    | none => D
    | some c => P_c c
  have hP_disc : ∀ i : Option CuffsOut, IsClosedDisc (P i) := by
    rintro (_ | c)
    · exact hD
    · exact hP_c_disc c
  have hP_disj_none : ∀ c : CuffsOut, Disjoint (P_c c) D := by
    intro c
    refine disjoint_left.mpr fun x hxP hxD => ?_
    rcases hP_c_sub_union c hxP with hx_open | ⟨u, ⟨⟨hu_c, _⟩, hu_notF⟩, rfl⟩
    · exact disjoint_left.mp c.2.2 hx_open hxD
    · have h_cl_disj : Disjoint (closure (cap.cuffDisc c.1)) (discInt D) :=
        (c.2.2.mono_right (Surface.discInt_subset D)).closure_left hdiscInt_D_open
      have hu_cl : cap.emb u ∈ closure (cap.cuffDisc c.1) := by
        rw [cap.closure_cuffDisc hS c.2.1]
        exact Or.inr (mem_image_of_mem cap.emb hu_c)
      have hu_not_int : cap.emb u ∉ discInt D := disjoint_left.mp h_cl_disj hu_cl
      have hu_bdD : cap.emb u ∈ discBd D := by
        by_contra hu_not_bd
        exact hu_not_int ⟨hxD, hu_not_bd⟩
      rw [hdiscBd_D, hinj_emb.mem_set_image] at hu_bdD
      exact hu_notF hu_bdD
  have hP_disj : Pairwise fun i j : Option CuffsOut => Disjoint (P i) (P j) := by
    rintro (_ | c₁) (_ | c₂) hij
    · exact (hij rfl).elim
    · exact (hP_disj_none c₂).symm
    · exact hP_disj_none c₁
    · have hne : c₁.1 ≠ c₂.1 := fun h => hij (congrArg some (Subtype.ext h))
      exact (cap.cuffDisc_disjoint c₁.1 c₁.2.1 c₂.1 c₂.2.1 hne).mono
        (hP_c_sub_cl c₁) (hP_c_sub_cl c₂)
  obtain ⟨_, hW_surf, hW_bd, hW_conn, hW_cuffs⟩ :=
    Surface.remove_discs hS₀ hcl₀.2.2 hP_disc hP_disj
  obtain ⟨capW⟩ := GM19.nonempty_capped_of_removal hcl₀ hP_disc hP_disj
  let W : Set S₀ := (⋃ i : Option CuffsOut, discInt (P i))ᶜ
  haveI : ConnectedSpace ↥W := hW_conn
  have hW_closed : IsClosed W :=
    (isOpen_iUnion fun i => (hP_disc i).isOpen_discInt hS₀.2.2).isClosed_compl
  have hbW : ∀ i : Option CuffsOut, ∀ x ∈ discBd (P i), x ∈ W := fun i x hx hu => by
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    by_cases hij : i = j
    · subst hij
      exact hj.2 hx
    · exact Set.disjoint_left.mp (hP_disj hij) (Surface.discBd_subset _ hx) hj.1
  have hinj_cuff : Function.Injective
      (fun i : Option CuffsOut => (Subtype.val ⁻¹' discBd (P i) : Set ↥W)) := by
    intro i j he
    by_contra hij
    obtain ⟨y, hy⟩ := (IsOArc.isConnected' (hP_disc i).isOArc_discBd).nonempty
    have h1 : (⟨y, hbW i y hy⟩ : ↥W) ∈ (Subtype.val ⁻¹' discBd (P j) : Set ↥W) := by
      dsimp only at he
      have hmem : (⟨y, hbW i y hy⟩ : ↥W) ∈ (Subtype.val ⁻¹' discBd (P i) : Set ↥W) := hy
      rwa [he] at hmem
    exact Set.disjoint_left.mp (hP_disj hij)
      (Surface.discBd_subset _ hy) (Surface.discBd_subset _ h1)
  have hcuffs_W : (cuffs ↥W).ncard = CuffsOut.ncard + 1 := by
    haveI : Fintype CuffsOut := hCuffsOut_fin.fintype
    rw [hW_cuffs, ← image_univ, Set.ncard_image_of_injective univ hinj_cuff,
      ncard_univ, Nat.card_eq_fintype_card, Fintype.card_option,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have h_pre_W : cap.emb ⁻¹' W = cap.emb ⁻¹' (closure (univ \ D)) := by
    ext s
    rw [mem_preimage, mem_preimage, ← hcompl_discInt_D]
    change (cap.emb s ∉ ⋃ i : Option CuffsOut, discInt (P i)) ↔ cap.emb s ∉ discInt D
    rw [mem_iUnion, not_exists]
    constructor
    · intro h
      exact h none
    · rintro h (_ | c)
      · exact h
      · intro hs_int
        have hs_open : cap.emb s ∈ cap.cuffDisc c.1 := hP_c_int c hs_int
        have hs_compl : cap.emb s ∈ (range cap.emb)ᶜ := by
          rw [cap.compl_eq]
          exact mem_iUnion₂.mpr ⟨c.1, c.2.1, hs_open⟩
        exact hs_compl (mem_range_self s)
  -- Identify the separation `(A, B)` of `Γ` pulled back from `(D, closure (univ \ D))`.
  let A : Hypergraph S (Set S) := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' D)
  let B : Hypergraph S (Set S) := (PaintingOrDrawing.drawing Γ).inter (cap.emb ⁻¹' W)
  have hinj_V : InjOn cap.emb Γ.toHypergraph.vertexSet := hinj_emb.injOn
  have hinj_E : InjOn (image cap.emb) Γ.toHypergraph.edgeSet :=
    (Set.image_injective.mpr hinj_emb).injOn
  have h_mapA : mapHypergraph cap.emb (image cap.emb) A =
      (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter D :=
    mapHypergraph_cap_inter_eq hS cap Γ D
  have h_mapB : mapHypergraph cap.emb (image cap.emb) B =
      (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).interOutside D := by
    dsimp [B]
    rw [h_pre_W]
    exact mapHypergraph_cap_inter_eq hS cap Γ (closure (univ \ D))
  have hA_le : A ≤ Γ.toHypergraph :=
    GM11.inter_le (Γ := PaintingOrDrawing.drawing Γ)
      (hD.isClosed.preimage cap.isEmbedding.continuous)
  have hB_le : B ≤ Γ.toHypergraph :=
    GM11.inter_le (Γ := PaintingOrDrawing.drawing Γ)
      (hW_closed.preimage cap.isEmbedding.continuous)
  have hmD_orig : (A, B) ∈ truncation 𝒯 θ₄ := by
    rcases hmD with ⟨⟨A₀, B₀⟩, hm₀, heq⟩
    obtain ⟨hA₀, hB₀⟩ := Prod.ext_iff.mp heq
    dsimp only at hm₀ hA₀ hB₀
    have hsep₀ := h𝒯.isSeparation hm₀.1
    have hA_eq : A₀ = A := by
      rw [← comapHypergraph_mapHypergraph hsep₀.left_le hinj_V hinj_E,
        ← comapHypergraph_mapHypergraph hA_le hinj_V hinj_E, hA₀, h_mapA]
    have hB_eq : B₀ = B := by
      rw [← comapHypergraph_mapHypergraph hsep₀.right_le hinj_V hinj_E,
        ← comapHypergraph_mapHypergraph hB_le hinj_V hinj_E, hB₀, h_mapB]
    rwa [← hA_eq, ← hB_eq]
  have hAB : (A, B) ∈ 𝒯 := hmD_orig.1
  have hord : separationOrder A B ≤ θ₄ := hmD_orig.2.le
  have hAB_V : (A ∩ B).vertexSet = F ∩ Γ.V := by
    ext v
    change (v ∈ Γ.V ∧ cap.emb v ∈ D) ∧ (v ∈ Γ.V ∧ cap.emb v ∈ W) ↔ v ∈ F ∧ v ∈ Γ.V
    rw [show (cap.emb v ∈ W) ↔ cap.emb v ∈ closure (univ \ D) from
      Set.ext_iff.mp h_pre_W v]
    have h_inter_D : D ∩ closure (univ \ D) = cap.emb '' F := by
      rw [← compl_eq_univ_sdiff]
      nth_rw 1 [← hD.isClosed.closure_eq]
      rw [← frontier_eq_closure_inter_closure, hfrD]
    constructor
    · rintro ⟨⟨hvΓ, hvD⟩, ⟨_, hvW⟩⟩
      have hvF : cap.emb v ∈ cap.emb '' F := h_inter_D ▸ ⟨hvD, hvW⟩
      exact ⟨(hinj_emb.mem_set_image).mp hvF, hvΓ⟩
    · rintro ⟨hvF, hvΓ⟩
      have hv_in : cap.emb v ∈ D ∩ closure (univ \ D) :=
        h_inter_D.symm ▸ mem_image_of_mem cap.emb hvF
      exact ⟨⟨hvΓ, hv_in.1⟩, ⟨hvΓ, hv_in.2⟩⟩
  -- Obtain the zero-split subspace drawing `Γ'` on `W`.
  obtain ⟨Γ', π, fE, hπ_inj, hfE_inj, h_map, hπ_spec, hU_spec⟩ :=
    exists_subspace_drawing_of_closed hS cap Γ hW_closed
  have hΓ'_prop : Γ'.IsProper := by
    rintro y ⟨hy_bd, hy_U⟩
    obtain ⟨⟨s, hs_U, hs_eq⟩, h_to_V⟩ := hU_spec y hy_U
    apply h_to_V
    rw [hW_bd, mem_preimage, mem_iUnion] at hy_bd
    rcases hy_bd with ⟨_ | c, hy_bdP⟩
    · change y.1 ∈ discBd D at hy_bdP
      rw [← hs_eq, hdiscBd_D, hinj_emb.mem_set_image] at hy_bdP
      rw [← hs_eq]
      exact mem_image_of_mem cap.emb (hnF ⟨hy_bdP, hs_U⟩)
    · change y.1 ∈ discBd (P_c c) at hy_bdP
      have hy_P : y.1 ∈ P_c c := Surface.discBd_subset (P_c c) hy_bdP
      rw [← hs_eq] at hy_P
      rcases hP_c_sub_union c hy_P with h_open | h_A
      · exfalso
        have h_compl : cap.emb s ∈ (range cap.emb)ᶜ := by
          rw [cap.compl_eq]
          exact mem_iUnion₂.mpr ⟨c.1, c.2.1, h_open⟩
        exact h_compl (mem_range_self s)
      · rw [hinj_emb.mem_set_image] at h_A
        rw [← hs_eq]
        exact mem_image_of_mem cap.emb h_A.1.2
  have hsplit : ObtainedBySplittingOutsideLe Γ.V θ₄ B
      (mapHypergraph π fE Γ'.toHypergraph) := by
    rw [h_map]
    exact ObtainedBySplittingOutsideLe.refl θ₄ B
  -- Characterize `y ∈ bd ↥W` for `y ∈ Γ'.V` for `(6)(b)` and for Claim (11).
  have h_bd_iff : ∀ y ∈ Γ'.V,
      y ∈ bd ↥W ↔
        π y ∈ F ∩ Γ.V ∨ ∃ c : CuffsOut, π y ∈ (c.1 ∩ Γ.V) \ F := by
    intro y hyV
    obtain ⟨h_emb_π, hπ_V, hyW⟩ := hπ_spec y hyV
    rw [hW_bd, mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨_ | c, hy_bdP⟩
      · change y.1 ∈ discBd D at hy_bdP
        rw [← h_emb_π, hdiscBd_D, hinj_emb.mem_set_image] at hy_bdP
        exact Or.inl ⟨hy_bdP, hπ_V⟩
      · change y.1 ∈ discBd (P_c c) at hy_bdP
        have hy_P : y.1 ∈ P_c c := Surface.discBd_subset (P_c c) hy_bdP
        rw [← h_emb_π] at hy_P
        rcases hP_c_sub_union c hy_P with h_open | h_A
        · exfalso
          have h_compl : cap.emb (π y) ∈ (range cap.emb)ᶜ := by
            rw [cap.compl_eq]
            exact mem_iUnion₂.mpr ⟨c.1, c.2.1, h_open⟩
          exact h_compl (mem_range_self (π y))
        · rw [hinj_emb.mem_set_image] at h_A
          exact Or.inr ⟨c, h_A⟩
    · rintro (⟨hvF, _⟩ | ⟨c, hv_c⟩)
      · refine ⟨none, ?_⟩
        change y.1 ∈ discBd D
        rw [← h_emb_π, hdiscBd_D]
        exact mem_image_of_mem cap.emb hvF
      · refine ⟨some c, ?_⟩
        change y.1 ∈ discBd (P_c c)
        rw [← h_emb_π]
        exact hP_c_bd c (mem_image_of_mem cap.emb hv_c)
  have h6b : ∀ y ∈ Γ'.V,
      y ∈ bd ↥W ↔
        π y ∈ (A ∩ B).vertexSet ∨ π y ∈ Γ.V ∩ bd S ∨ π y ∉ Γ.V := by
    intro y hyV
    obtain ⟨h_emb_π, hπ_V, hyW⟩ := hπ_spec y hyV
    rw [h_bd_iff y hyV, hAB_V]
    constructor
    · rintro (hvF | ⟨c, ⟨⟨hvc, hvΓ⟩, _⟩⟩)
      · exact Or.inl hvF
      · have hc_bd : c.1 ⊆ bd S := by
          rcases c.2.1 with ⟨x, _, hxc⟩
          rw [← hxc]
          exact connectedComponentIn_subset (bd S) x
        exact Or.inr (Or.inl ⟨hvΓ, hc_bd hvc⟩)
    · rintro (hvF | ⟨hvΓ, hv_bdS⟩ | hv_notΓ)
      · exact Or.inl hvF
      · by_cases hvF : π y ∈ F
        · exact Or.inl ⟨hvF, hvΓ⟩
        · rw [← sUnion_cuffs] at hv_bdS
          rcases hv_bdS with ⟨C', hC', hvC'⟩
          rcases h_cuff_side C' hC' with h_in | h_disj
          · exfalso
            have hv_cl : cap.emb (π y) ∈ closure (cap.cuffDisc C') := by
              rw [cap.closure_cuffDisc hS hC']
              exact Or.inr (mem_image_of_mem cap.emb hvC')
            have hv_D : cap.emb (π y) ∈ D :=
              (closure_mono (h_in.trans (Surface.discInt_subset D))).trans
                hD.isClosed.closure_eq.subset hv_cl
            have hv_W : cap.emb (π y) ∈ W := h_emb_π.symm ▸ hyW
            have hv_not_int : cap.emb (π y) ∉ discInt D :=
              fun h => hv_W (mem_iUnion.mpr ⟨none, h⟩)
            have hv_bdD : cap.emb (π y) ∈ discBd D := by
              by_contra h_not_bd
              exact hv_not_int ⟨hv_D, h_not_bd⟩
            rw [hdiscBd_D, hinj_emb.mem_set_image] at hv_bdD
            exact hvF hv_bdD
          · exact Or.inr ⟨⟨C', hC', h_disj⟩, ⟨hvC', hvΓ⟩, hvF⟩
      · exact (hv_notΓ hπ_V).elim
  -- Apply `apply_claim_5_2_6_of_drawing` to `W` and `Γ'`.
  obtain ⟨hcuffs_le, hcuffs_eq_imp⟩ :=
    apply_claim_5_2_6_of_drawing hS hW_surf cap capW hΓ_bd h𝒯 hL hL_bd hAB hord
      hπ_inj hfE_inj hsplit ⟨Homeomorph.refl S₀⟩ h6b hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos
      (fun hlt hle T' L' => h_ind2 ↥W hW_surf hW_conn capW hlt Γ' T' L' hΓ'_prop hle)
      (fun hhomeo hlt T' L' => h_ind3 ↥W hW_surf hW_conn hhomeo Γ' T' L' hΓ'_prop hlt)
  rw [hcuffs_W] at hcuffs_le hcuffs_eq_imp
  -- Deduce Claim (9) and Claim (11).
  have h_decomp_cuffs : (cuffs S \ CuffsOut).ncard + CuffsOut.ncard = (cuffs S).ncard :=
    ncard_sdiff_add_ncard_of_subset (sep_subset _ _) hcuffs_fin
  have h_in_le_one : (cuffs S \ CuffsOut).ncard ≤ 1 := by omega
  refine ⟨?_, ?_⟩
  · intro C₁ hC₁ C₂ hC₂ hnd₁ hnd₂
    have h₁ : C₁ ∈ cuffs S \ CuffsOut := ⟨hC₁, fun h => hnd₁ h.2⟩
    have h₂ : C₂ ∈ cuffs S \ CuffsOut := ⟨hC₂, fun h => hnd₂ h.2⟩
    have hsub : (cuffs S \ CuffsOut).Subsingleton :=
      (Set.ncard_le_one_iff_eq (hcuffs_fin.subset sdiff_subset)).mp h_in_le_one |>.elim
        (fun hemp => hemp ▸ subsingleton_empty)
        (fun ⟨a, ha⟩ => ha ▸ subsingleton_singleton)
    exact hsub h₁ h₂
  · intro C hC hC_sub_D
    rcases h_cuff_side C hC with hC_in | hC_disj
    · have hC_mem_diff : C ∈ cuffs S \ CuffsOut :=
        ⟨hC, fun h => by
          have h_ne : (cap.cuffDisc C).Nonempty := by
            rw [cap.cuffDisc_eq_discInt hS hC]
            exact (cap.cuffDisc_closedDisc C hC).nonempty_discInt
          obtain ⟨x₀, hx₀⟩ := h_ne
          exact disjoint_left.mp h.2 hx₀ (Surface.discInt_subset D (hC_in hx₀))⟩
      have h_pos_diff : 1 ≤ (cuffs S \ CuffsOut).ncard :=
        (ncard_pos (hcuffs_fin.subset sdiff_subset)).mpr ⟨C, hC_mem_diff⟩
      have h_eq_cuffs : CuffsOut.ncard + 1 = (cuffs S).ncard := by omega
      have hp_le : p ≤ (π '' (Γ'.V ∩ bd ↥W)).ncard := by
        rw [(hπ_inj.mono inter_subset_left).ncard_image]
        exact hcuffs_eq_imp h_eq_cuffs
      have hC_bd : C ⊆ bd S := by
        rcases hC with ⟨x, _, hxC⟩
        rw [← hxC]
        exact connectedComponentIn_subset (bd S) x
      have h_bd_V'_sub : π '' (Γ'.V ∩ bd ↥W) ⊆ ((Γ.V ∩ bd S) \ C) ∪ (F ∩ Γ.V) := by
        rintro _ ⟨y, ⟨hyV, hybd⟩, rfl⟩
        rcases (h_bd_iff y hyV).mp hybd with hvF | ⟨c, ⟨⟨hvc, hvΓ⟩, _⟩⟩
        · exact Or.inr hvF
        · left
          have hc_bd : c.1 ⊆ bd S := by
            rcases c.2.1 with ⟨x, _, hxc⟩
            rw [← hxc]
            exact connectedComponentIn_subset (bd S) x
          refine ⟨⟨hvΓ, hc_bd hvc⟩, fun hvC => ?_⟩
          have hc_ne_C : c.1 ≠ C := fun h_eq => hC_mem_diff.2 (h_eq ▸ c.2)
          have hdisj_cC := cap.cuffDisc_disjoint c.1 c.2.1 C hC hc_ne_C
          have hv_cl_c : cap.emb (π y) ∈ closure (cap.cuffDisc c.1) := by
            rw [cap.closure_cuffDisc hS c.2.1]
            exact Or.inr (mem_image_of_mem cap.emb hvc)
          have hv_cl_C : cap.emb (π y) ∈ closure (cap.cuffDisc C) := by
            rw [cap.closure_cuffDisc hS hC]
            exact Or.inr (mem_image_of_mem cap.emb hvC)
          exact disjoint_left.mp hdisj_cC hv_cl_c hv_cl_C
      exact claim_5_2_11_card hC_bd h_bd_V'_sub (hΓ_bd.trans hp_le)
    · have h_cl_disj : Disjoint (closure (cap.cuffDisc C)) (discInt D) :=
        (hC_disj.mono_right (Surface.discInt_subset D)).closure_left hdiscInt_D_open
      have hC_sub_F : C ⊆ F := by
        intro u huC
        have hu_cl : cap.emb u ∈ closure (cap.cuffDisc C) := by
          rw [cap.closure_cuffDisc hS hC]
          exact Or.inr (mem_image_of_mem cap.emb huC)
        have hu_D : cap.emb u ∈ D := hC_sub_D (mem_image_of_mem cap.emb huC)
        have hu_not_int : cap.emb u ∉ discInt D := disjoint_left.mp h_cl_disj hu_cl
        have hu_bdD : cap.emb u ∈ discBd D := by
          by_contra hu_not_bd
          exact hu_not_int ⟨hu_D, hu_not_bd⟩
        rwa [hdiscBd_D, hinj_emb.mem_set_image] at hu_bdD
      exact ncard_le_ncard (inter_subset_inter_left Γ.V hC_sub_F)
        (Γ.finite_V.subset inter_subset_right)

/-- **Graph Minors XXI, (5.2), Claim (9)** (page 20 of the preprint):
"(9) *If* $F \subseteq \hat{\Sigma}$ *is a* $\Gamma$*-normal* $O$*-arc with*
$|F \cap V(\Gamma)| < \theta_4$*, then* $C \cap ins(F) \ne \emptyset$ *for at most one cuff* $C$."

For any `Γ`-normal `O`-arc `F ⊆ S` disjoint from `bd S` (as in Claim (10)) and closed disc
`D ⊆ S₀` with `subBd D = cap.emb '' F` and
`((PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter D,
  (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).interOutside D) ∈ T₁`:
1. every cuff `C ∈ cuffs S` with `(cap.emb '' C ∩ D).Nonempty` has
   `closure (cap.cuffDisc C) ⊆ discInt D` and `cap.emb '' C ⊆ discInt D`,
2. at most one cuff `C ∈ cuffs S` satisfies `(cap.emb '' C ∩ D).Nonempty`, and
3. if `C ∈ cuffs S` satisfies `(cap.emb '' C ∩ D).Nonempty`, then `cap.emb ⁻¹' D ∩ bd S = C`. -/
theorem claim_5_2_9 {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L : Hypergraph S (Set S)}
    {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (h_ind2 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → ConnectedSpace S' →
      GM19.IsCappedSurface S' S₀ →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S')
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
        (L' : Hypergraph S' (Set S')),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        IsTangle Γ'.toHypergraph θ₂ T' →
        IsVitalLinkage Γ'.toHypergraph L' →
        ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → ConnectedSpace S' →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S')
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
        (L' : Hypergraph S' (Set S')),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        IsTangle Γ'.toHypergraph θ₃ T' →
        IsVitalLinkage Γ'.toHypergraph L' →
        ¬ (terminals L' ⊆ bd S'))
    {F : Set S} {D : Set S₀}
    (hnF : (PaintingOrDrawing.drawing Γ).IsNormal F) (hF : IsOArc F)
    (hF_disj_bd : Disjoint F (bd S))
    (hD : IsClosedDisc D) (hbdD : subBd D = cap.emb '' F)
    (hmD : ((PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter D,
      (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).interOutside D) ∈
        mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)) :
    (∀ C ∈ cuffs S, (cap.emb '' C ∩ D).Nonempty →
      closure (cap.cuffDisc C) ⊆ discInt D ∧ cap.emb '' C ⊆ discInt D) ∧
    (∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S,
      (cap.emb '' C₁ ∩ D).Nonempty → (cap.emb '' C₂ ∩ D).Nonempty → C₁ = C₂) ∧
    (∀ C ∈ cuffs S, (cap.emb '' C ∩ D).Nonempty → cap.emb ⁻¹' D ∩ bd S = C) := by
  haveI : T2Space S := hS.2.1
  have hS₀ : IsSurface S₀ := cap.isSurface
  have hcl₀ : IsClosedSurface S₀ := cap.isClosedSurface
  haveI : T2Space S₀ := hS₀.2.1
  have hfrD : frontier D = cap.emb '' F := (GM11.subBd_eq_frontier D).symm.trans hbdD
  have hdiscBd_D : discBd D = cap.emb '' F :=
    (GM11.IsClosedDisc.frontier_eq_discBd hcl₀ hD).symm.trans hfrD
  obtain ⟨h9_core, -⟩ :=
    claim_5_2_9_and_11_core hS cap hΓ_bd h𝒯 hL hL_bd hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos
      h_ind2 h_ind3 hnF hF hD hbdD hmD
  have h_cl_sub : ∀ C ∈ cuffs S, (cap.emb '' C ∩ D).Nonempty →
      closure (cap.cuffDisc C) ⊆ discInt D ∧ cap.emb '' C ⊆ discInt D := by
    intro C hC ⟨x, ⟨hxC, hxD⟩⟩
    have hC_bd : C ⊆ bd S := by
      rcases hC with ⟨y, _, hyC⟩
      rw [← hyC]
      exact connectedComponentIn_subset (bd S) y
    have h_open_pre : IsPreconnected (cap.cuffDisc C) := by
      rw [cap.cuffDisc_eq_discInt hS hC]
      exact (cap.cuffDisc_closedDisc C hC).isPreconnected_discInt
    have h_cl_pre : IsPreconnected (closure (cap.cuffDisc C)) := h_open_pre.closure
    have h_disj_bd : Disjoint (closure (cap.cuffDisc C)) (discBd D) := by
      rw [cap.closure_cuffDisc hS hC, hdiscBd_D]
      refine disjoint_left.mpr fun z hz ⟨s, hsF, hsz⟩ => ?_
      rcases hz with hz_open | ⟨u, huC, huz⟩
      · have hz_compl : z ∈ (range cap.emb)ᶜ := by
          rw [cap.compl_eq]
          exact mem_iUnion₂.mpr ⟨C, hC, hz_open⟩
        exact hz_compl ⟨s, hsz⟩
      · have hus : u = s := cap.isEmbedding.injective (huz.trans hsz.symm)
        exact disjoint_left.mp hF_disj_bd hsF (hus ▸ hC_bd huC)
    have hC_sub_cl : cap.emb '' C ⊆ closure (cap.cuffDisc C) := by
      rw [cap.closure_cuffDisc hS hC]
      exact subset_union_right
    rcases hD.side hS₀.2.2 h_cl_pre h_disj_bd with h_in | h_disj
    · exact ⟨h_in, hC_sub_cl.trans h_in⟩
    · exact (disjoint_left.mp h_disj (hC_sub_cl hxC) hxD).elim
  have h_unique : ∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S,
      (cap.emb '' C₁ ∩ D).Nonempty → (cap.emb '' C₂ ∩ D).Nonempty → C₁ = C₂ := by
    intro C₁ hC₁ C₂ hC₂ hne₁ hne₂
    have h₁ := (h_cl_sub C₁ hC₁ hne₁).1
    have h₂ := (h_cl_sub C₂ hC₂ hne₂).1
    have hne_open₁ : (cap.cuffDisc C₁).Nonempty := by
      rw [cap.cuffDisc_eq_discInt hS hC₁]
      exact (cap.cuffDisc_closedDisc C₁ hC₁).nonempty_discInt
    have hne_open₂ : (cap.cuffDisc C₂).Nonempty := by
      rw [cap.cuffDisc_eq_discInt hS hC₂]
      exact (cap.cuffDisc_closedDisc C₂ hC₂).nonempty_discInt
    obtain ⟨z₁, hz₁⟩ := hne_open₁
    obtain ⟨z₂, hz₂⟩ := hne_open₂
    exact h9_core C₁ hC₁ C₂ hC₂
      (fun hd₁ => disjoint_left.mp hd₁ hz₁ (Surface.discInt_subset D (h₁ (subset_closure hz₁))))
      (fun hd₂ => disjoint_left.mp hd₂ hz₂ (Surface.discInt_subset D (h₂ (subset_closure hz₂))))
  refine ⟨h_cl_sub, h_unique, ?_⟩
  intro C hC hne
  have hC_in : cap.emb '' C ⊆ D :=
    (h_cl_sub C hC hne).2.trans (Surface.discInt_subset D)
  have hC_bd : C ⊆ bd S := by
    rcases hC with ⟨y, _, hyC⟩
    rw [← hyC]
    exact connectedComponentIn_subset (bd S) y
  apply Subset.antisymm
  · rintro u ⟨huD, hu_bd⟩
    rw [← sUnion_cuffs] at hu_bd
    rcases hu_bd with ⟨C', hC', huC'⟩
    have hne' : (cap.emb '' C' ∩ D).Nonempty := ⟨cap.emb u, mem_image_of_mem cap.emb huC', huD⟩
    rwa [← h_unique C hC C' hC' hne hne'] at huC'
  · intro u huC
    exact ⟨hC_in (mem_image_of_mem cap.emb huC), hC_bd huC⟩

/-- **Graph Minors XXI, (5.2), Claim (11)** (page 21 of the preprint):
"(11) *If* $F \subseteq \Sigma$ *is a* $\Gamma$*-normal* $O$*-arc with* $|F \cap V(\Gamma)| < \theta_4$*,
and* $ins(F)$ *includes a unique cuff* $C$*, then* $|F \cap V(\Gamma)| \ge |C \cap V(\Gamma)|$." -/
theorem claim_5_2_11 {S S₀ : Type}
    [TopologicalSpace S] [TopologicalSpace S₀]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S S₀)
    {Γ : Surface.Drawing S}
    {L : Hypergraph S (Set S)}
    {p θ θ₄ θ₂ θ₃ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ)
    (hθ₂_pos : 1 ≤ θ₂)
    (hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ)
    (hθ₃_pos : 1 ≤ θ₃)
    (h_ind2 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → ConnectedSpace S' →
      GM19.IsCappedSurface S' S₀ →
      (cuffs S').ncard < (cuffs S).ncard →
      ∀ (Γ' : Surface.Drawing S')
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
        (L' : Hypergraph S' (Set S')),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
        IsTangle Γ'.toHypergraph θ₂ T' →
        IsVitalLinkage Γ'.toHypergraph L' →
        ¬ (terminals L' ⊆ bd S'))
    (h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
      IsSurface S' → ConnectedSpace S' →
      Nonempty (S' ≃ₜ S) →
      ∀ (Γ' : Surface.Drawing S')
        (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
        (L' : Hypergraph S' (Set S')),
        Γ'.IsProper →
        (Γ'.V ∩ bd S').ncard < p →
        IsTangle Γ'.toHypergraph θ₃ T' →
        IsVitalLinkage Γ'.toHypergraph L' →
        ¬ (terminals L' ⊆ bd S')) :
    ∀ (F : Set S) (D : Set S₀) (C : Set S),
      (PaintingOrDrawing.drawing Γ).IsNormal F → IsOArc F →
      C ∈ cuffs S →
      IsClosedDisc D → subBd D = cap.emb '' F →
      ((PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter D,
        (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).interOutside D) ∈
          mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄) →
      cap.emb '' C ⊆ D →
      (C ∩ Γ.V).ncard ≤ (F ∩ Γ.V).ncard := by
  intro F D C hnF hF hC hD hbdD hmD hCD
  exact (claim_5_2_9_and_11_core hS cap hΓ_bd h𝒯 hL hL_bd hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos
    h_ind2 h_ind3 hnF hF hD hbdD hmD).2 C hC hCD

end GM21
end GraphMinor
