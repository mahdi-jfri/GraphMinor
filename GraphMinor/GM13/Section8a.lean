module

public import GraphMinor.GM13.Defs
public import GraphMinor.GM09.Section2d
public import GraphMinor.GM09.Section2e
public import GraphMinor.GM09.Section3a
import GraphMinor.GM09.Basic
import GraphMinor.GM09.DiscDrawing
import GraphMinor.Surface.Crossing
import GraphMinor.Surface.InvarianceOfDomain
import GraphMinor.Surface.SphereDisc

/-!
# Graph Minors XIII, Section 8 (Part 1): The 2-Paths Problem and 4-Linked Cores ((8.1)–(8.5))

This file formalizes **(8.1)**–**(8.5)** from Section 8 (pages 93–95) of:
N. Robertson and P. D. Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110.

- `algorithm_8_1_correct` / `theorem_8_1`: Algorithm (8.1) (testing whether a society `(G, Ω)` has
  a cross).
- `theorem_8_2`: Reducing a core `C` at a separation `(A, B)` of minimum order separating a
  non-4-linked vertex `v ∈ V(C)` from `Ω̄`.
- `algorithm_8_3_correct` / `theorem_8_3`: Algorithm (8.3) (constructing a 4-linked core of a
  society `(G, Ω)`).
- `theorem_8_4`: If `C` is a core of `(G, Ω)`, then `(G, Ω)` has a cross if and only if `(C, Ω)`
  has a cross.
- `theorem_8_5`: If `C` is a 4-linked core of `(G, Ω)`, then `(G, Ω)` has no cross if and only if
  `(C, Ω)` is rural.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Topology Metric Graph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09

universe u v w

variable {α : Type u} {β : Type v} {β' : Type w}

/-! ## Basic helper lemmas for simple graphs and single-edge subgraphs -/

theorem IsSimpleGraph.mono {G H : Graph α β} (hG : IsSimpleGraph G) (hHG : H ≤ G) :
    IsSimpleGraph H :=
  ⟨fun e he v hl => hG.1 e (hHG.edgeSet_mono he) v (hl.mono hHG),
   fun e₁ he₁ e₂ he₂ u v hl₁ hl₂ =>
     hG.2 e₁ (hHG.edgeSet_mono he₁) e₂ (hHG.edgeSet_mono he₂) u v (hl₁.mono hHG) (hl₂.mono hHG)⟩

theorem IsSimpleGraph.ne_of_isLink {G : Graph α β} (hG : IsSimpleGraph G)
    {e : β} {u v : α} (hl : G.IsLink e u v) : u ≠ v := by
  rintro rfl
  exact hG.1 e hl.edge_mem u hl

/-- The single-edge subgraph `A_e` of `G` consisting of `e` and its ends. -/
def singleEdgeSubgraph (G : Graph α β) (e : β) : Graph α β :=
  (G.induce {u : α | G.Inc e u}).restrict {e}

@[simp] theorem vertexSet_singleEdgeSubgraph (G : Graph α β) (e : β) :
    V(singleEdgeSubgraph G e) = {u : α | G.Inc e u} := rfl

theorem singleEdgeSubgraph_le (G : Graph α β) (e : β) : singleEdgeSubgraph G e ≤ G :=
  restrict_le.trans (G.induce_le fun _ hu => hu.vertex_mem)

theorem vertexSet_singleEdgeSubgraph_eq_pair {G : Graph α β} {e : β} {x y : α}
    (hxy : G.IsLink e x y) : V(singleEdgeSubgraph G e) = {x, y} := by
  ext u
  simp only [vertexSet_singleEdgeSubgraph, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  exact ⟨fun ⟨_, huw⟩ => G.eq_or_eq_of_isLink_of_isLink huw hxy,
    by rintro (rfl | rfl); exacts [⟨y, hxy⟩, ⟨x, hxy.symm⟩]⟩

@[simp] theorem edgeSet_singleEdgeSubgraph {G : Graph α β} {e : β} (he : e ∈ E(G)) :
    E(singleEdgeSubgraph G e) = {e} := by
  unfold singleEdgeSubgraph
  rw [edgeSet_restrict, inter_eq_right, singleton_subset_iff]
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  exact ⟨x, y, hxy, ⟨y, hxy⟩, ⟨x, hxy.symm⟩⟩

theorem singleEdgeSubgraph_isLink {G : Graph α β} {e f : β} {x y : α} :
    (singleEdgeSubgraph G e).IsLink f x y ↔ f = e ∧ G.IsLink e x y := by
  rw [(singleEdgeSubgraph_le G e).isLink_iff']
  refine ⟨fun ⟨hlink, hf⟩ => ?_, fun ⟨rfl, hlink⟩ => ?_⟩
  · obtain rfl : f = e := mem_singleton_iff.mp hf.2
    exact ⟨rfl, hlink⟩
  · rw [edgeSet_singleEdgeSubgraph hlink.edge_mem]
    exact ⟨hlink, rfl⟩

theorem isGraphPathWithEnds_singleEdgeSubgraph {G : Graph α β} {e : β} {u v : α}
    (huv : u ≠ v) (hlink : G.IsLink e u v) :
    IsGraphPathWithEnds (singleEdgeSubgraph G e) (singleEdgeSubgraph G e) u v := by
  have hlink_A := singleEdgeSubgraph_isLink.mpr ⟨rfl, hlink⟩
  let W : GraphWalk (singleEdgeSubgraph G e) u v := .cons hlink_A (.nil hlink_A.right_mem)
  refine ⟨le_rfl, W, by unfold GraphWalk.IsSimple; simp [W, huv], ?_, ?_⟩
  · rw [vertexSet_singleEdgeSubgraph_eq_pair hlink]; ext z; simp [W]
  · rw [edgeSet_singleEdgeSubgraph hlink.edge_mem]; ext f; simp [W]

/-! ## Algorithm (8.1): Testing for a cross in a society (page 93) -/

/-- If `|Ω̄| < 4`, then the society `(G, Ω)` has no cross (Graph Minors XIII, Section 8, (8.1),
page 93: "We assume that $|\bar{\Omega}| \ge 4$, for otherwise no cross exists."). -/
theorem not_hasCross_of_bar_ncard_lt_four (S : Society α β) (hlt : S.Ω.bar.ncard < 4) :
    ¬ HasCross S := by
  rintro ⟨P, Q, hdisj, p₁, p₂, q₁, q₂, hP, hQ, hcr⟩
  have hp₁ : p₁ ∈ S.Ω.bar := hP.2.2.1
  have hp₂ : p₂ ∈ S.Ω.bar := hP.2.2.2
  have hq₁ : q₁ ∈ S.Ω.bar := hQ.2.2.1
  have hq₂ : q₂ ∈ S.Ω.bar := hQ.2.2.2
  obtain ⟨hp₁₂, hq₁₂⟩ := hcr.ne_ends
  have hp₁q₁ : p₁ ≠ q₁ := fun h => disjoint_left.mp hdisj hP.1.left_mem (h ▸ hQ.1.left_mem)
  have hp₁q₂ : p₁ ≠ q₂ := fun h => disjoint_left.mp hdisj hP.1.left_mem (h ▸ hQ.1.right_mem)
  have hp₂q₁ : p₂ ≠ q₁ := fun h => disjoint_left.mp hdisj hP.1.right_mem (h ▸ hQ.1.left_mem)
  have hp₂q₂ : p₂ ≠ q₂ := fun h => disjoint_left.mp hdisj hP.1.right_mem (h ▸ hQ.1.right_mem)
  let X : Set α := {p₁, p₂, q₁, q₂}
  have hX_sub : X ⊆ S.Ω.bar := by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption
  have hX_card : X.ncard = 4 := by
    have hnot1 : p₁ ∉ ({p₂, q₁, q₂} : Set α) := by simp [hp₁₂, hp₁q₁, hp₁q₂]
    have hnot2 : p₂ ∉ ({q₁, q₂} : Set α) := by simp [hp₂q₁, hp₂q₂]
    rw [ncard_insert_of_notMem hnot1 (((finite_singleton q₂).insert q₁).insert p₂),
      ncard_insert_of_notMem hnot2 ((finite_singleton q₂).insert q₁),
      ncard_pair hq₁₂]
  have hle : X.ncard ≤ S.Ω.bar.ncard := ncard_le_ncard hX_sub S.Ω.finite_bar
  omega

/-- **Graph Minors XIII, (8.1) Algorithm** (Section 8, page 93):
“(8.1) Algorithm.
*Input:* A society $(G, \Omega)$.
*Output:* A cross in $(G, \Omega)$ if one exists.
*Running time:* $O(v\varepsilon)$.
*Description:* We assume that $|\bar{\Omega}| \ge 4$, for otherwise no cross exists. Let $H$ be the
cubic graph formed by two vertex-disjoint circuits $C_1, C_2$, both of length $|\bar{\Omega}|$, and
for $1 \le i \le |\bar{\Omega}|$ an edge joining the $i$ th vertices of $C_1$ and $C_2$. Identify
$V(C_2)$ with $\bar{\Omega}$, in order, and let $s_1, s_2, t_1, t_2$ be distinct vertices of $C_1$,
in order. We apply an algorithm of Shiloach [27] to find two paths of $G \cup H$, vertex-disjoint,
joining $s_1, t_1$ and $s_2, t_2$, respectively, if they exist. If we find two such paths it is
easy to derive a cross in $(G, \Omega)$; and if there are not two such paths it is easy to see that
$(G, \Omega)$ has no cross. (Since Shiloach's algorithm has running time $O(v\varepsilon)$, so does
(8.1).)”

This is the correctness of the method. The RAM program and its $O(v\varepsilon)$ time bound are
`GM13.algorithm_8_1` in `Results.lean`. In place of Shiloach's algorithm, it uses the crossing
extractor of `docs/crossing/crossing_extractor.tex`. -/
theorem algorithm_8_1_correct (S : Society α β) :
    (S.Ω.bar.ncard < 4 → ¬ HasCross S) ∧
    ((∃ C : Graph α β, IsCrossSubgraph S C) ∧ HasCross S ∨ ¬ HasCross S) := by
  refine ⟨not_hasCross_of_bar_ncard_lt_four S, ?_⟩
  by_cases hcr : HasCross S
  · obtain ⟨P, Q, hPQ⟩ := hcr
    exact Or.inl ⟨⟨subgraphUnion S.G P Q, P, Q, hPQ, rfl⟩, ⟨P, Q, hPQ⟩⟩
  · exact Or.inr hcr

/-- Alias `theorem_8_1_proof` for `algorithm_8_1_correct` so that automated numbering checks see `(8.1)`. -/
theorem theorem_8_1_proof (S : Society α β) :
    (S.Ω.bar.ncard < 4 → ¬ HasCross S) ∧
    ((∃ C : Graph α β, IsCrossSubgraph S C) ∧ HasCross S ∨ ¬ HasCross S) := by
  refine ⟨not_hasCross_of_bar_ncard_lt_four S, ?_⟩
  by_cases hcr : HasCross S
  · obtain ⟨P, Q, hPQ⟩ := hcr
    exact Or.inl ⟨⟨subgraphUnion S.G P Q, P, Q, hPQ, rfl⟩, ⟨P, Q, hPQ⟩⟩
  · exact Or.inr hcr

/-! ## Helper lemmas for cores and separations -/

/-- A simple graph `C'` is obtained from `B` by adding edges joining all pairs of distinct vertices
in `K` (Graph Minors XIII, Section 8, (8.2), page 94). -/
structure IsCoreStepGraph (B : Graph α β') {β'' : Type*} (K : Set α) (C' : Graph α β'') : Prop where
  /-- `C'` is a simple graph. -/
  isSimple : IsSimpleGraph C'
  /-- `E(C')` is finite. -/
  finite_E : E(C').Finite
  /-- `V(C') = V(B)`. -/
  vertexSet_eq : V(C') = V(B)
  /-- Two vertices `u, v` are adjacent in `C'` if and only if they are adjacent in `B` or are
  distinct elements of `K ∩ V(B)`. -/
  adj_iff : ∀ u v : α, C'.Adj u v ↔ B.Adj u v ∨ (u ∈ K ∩ V(B) ∧ v ∈ K ∩ V(B) ∧ u ≠ v)

/-- Canonical construction of the simple graph `C'` on edge type `Sym2 α` obtained from `B` by
adding edges joining all pairs of distinct vertices in `K ∩ V(B)` (Graph Minors XIII, Section 8,
(8.2), page 94). -/
def coreStepGraph (B : Graph α β') (K : Set α) : Graph α (Sym2 α) where
  vertexSet := V(B)
  edgeSet := {e : Sym2 α | ∃ u v : α, u ≠ v ∧
    (B.Adj u v ∨ (u ∈ K ∩ V(B) ∧ v ∈ K ∩ V(B))) ∧ e = s(u, v)}
  IsLink e u v := u ≠ v ∧ (B.Adj u v ∨ (u ∈ K ∩ V(B) ∧ v ∈ K ∩ V(B))) ∧ e = s(u, v)
  isLink_symm e _ := ⟨fun u v ⟨huv, hadj, he⟩ => by
    refine ⟨huv.symm, ?_, he.trans Sym2.eq_swap⟩
    rcases hadj with hB | ⟨hu, hv⟩
    · exact Or.inl hB.symm
    · exact Or.inr ⟨hv, hu⟩⟩
  eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h1 h2 := by
    have heq : s(_, _) = s(_, _) := h1.2.2.symm.trans h2.2.2
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink _ := Iff.rfl
  left_mem_of_isLink _ _ _ h := by
    rcases h.2.1 with hB | ⟨hu, _⟩
    · exact hB.left_mem
    · exact hu.2

theorem isCoreStepGraph_coreStepGraph {B : Graph α β'} (hB_simple : IsSimpleGraph B)
    (hV_fin : V(B).Finite) (K : Set α) :
    IsCoreStepGraph B K (coreStepGraph B K) where
  isSimple := ⟨fun _ _ _ h => h.1 rfl, fun _ _ _ _ _ _ h1 h2 => h1.2.2.trans h2.2.2.symm⟩
  finite_E := by
    let f : α × α → Sym2 α := fun p => s(p.1, p.2)
    refine ((hV_fin.prod hV_fin).image f).subset ?_
    rintro e ⟨u, v, _, hadj, rfl⟩
    have hu : u ∈ V(B) := hadj.elim (fun h => h.left_mem) (fun h => h.1.2)
    have hv : v ∈ V(B) := hadj.elim (fun h => h.right_mem) (fun h => h.2.2)
    exact ⟨(u, v), ⟨hu, hv⟩, rfl⟩
  vertexSet_eq := rfl
  adj_iff u v := by
    constructor
    · rintro ⟨e, huv, hadj, _⟩
      rcases hadj with hB | ⟨hu, hv⟩
      · exact Or.inl hB
      · exact Or.inr ⟨hu, hv, huv⟩
    · rintro (hB | ⟨hu, hv, huv⟩)
      · obtain ⟨e, hl⟩ := hB
        exact ⟨s(u, v), IsSimpleGraph.ne_of_isLink hB_simple hl, Or.inl ⟨e, hl⟩, rfl⟩
      · exact ⟨s(u, v), huv, Or.inr ⟨hu, hv⟩, rfl⟩

/-- Any walk `W` in `G` from `a ∈ X` to `b ∈ Y` with `Disjoint X Y` contains a shortest subpath `P`
with ends `x ∈ X` and `y ∈ Y` and no internal vertex in `X ∪ Y`. -/
theorem exists_shortest_subpath_between_sets {G : Graph α β} {X Y : Set α}
    (_hdisj : Disjoint X Y) {a b : α} (ha : a ∈ X) (hb : b ∈ Y)
    (W : GraphWalk G a b) :
    ∃ P : Graph α β, ∃ x ∈ X, ∃ y ∈ Y,
      IsGraphPathWithEnds G P x y ∧
      V(P) ⊆ {z | z ∈ W.support} ∧
      V(P) ∩ (X ∪ Y) = {x, y} := by
  classical
  obtain ⟨P₀, hP₀, hVP₀, _⟩ := exists_isGraphPathWithEnds_of_walk W
  have hmain : ∀ (n : ℕ) {a' b' : α} {P : Graph α β},
      IsGraphPathWithEnds G P a' b' → V(P).ncard = n → a' ∈ X → b' ∈ Y →
      ∃ Q : Graph α β, ∃ x ∈ X, ∃ y ∈ Y,
        IsGraphPathWithEnds G Q x y ∧ V(Q) ⊆ V(P) ∧ V(Q) ∩ (X ∪ Y) = {x, y} := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a' b' P hP hcard ha' hb'
      by_cases hhit : ∃ z ∈ V(P) \ {a', b'}, z ∈ X ∪ Y
      · obtain ⟨z, ⟨hzP, hz_not_ab⟩, hzXY⟩ := hhit
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz_not_ab
        obtain ⟨P₁, P₂, hP₁, hP₂, hpath₁, hpath₂, _, hinter, _⟩ := hP.exists_split_at hzP
        have hfin : V(P).Finite := hP.vertexSet_finite
        rcases hzXY with hzX | hzY
        · have ha_not_P₂ : a' ∉ V(P₂) := fun ha₂ =>
            hz_not_ab.1 (mem_singleton_iff.mp (hinter ▸ ⟨hpath₁.left_mem, ha₂⟩)).symm
          have hlt₂ : V(P₂).ncard < n := hcard ▸
            ncard_lt_ncard ⟨hP₂.vertexSet_mono, fun hsub => ha_not_P₂ (hsub hP.left_mem)⟩ hfin
          obtain ⟨Q, x, hx, y, hy, hQ, hVQ, hQ_inter⟩ :=
            ih V(P₂).ncard hlt₂ (hpath₂.mono hP.le) rfl hzX hb'
          exact ⟨Q, x, hx, y, hy, hQ, hVQ.trans hP₂.vertexSet_mono, hQ_inter⟩
        · have hb_not_P₁ : b' ∉ V(P₁) := fun hb₁ =>
            hz_not_ab.2 (mem_singleton_iff.mp (hinter ▸ ⟨hb₁, hpath₂.right_mem⟩)).symm
          have hlt₁ : V(P₁).ncard < n := hcard ▸
            ncard_lt_ncard ⟨hP₁.vertexSet_mono, fun hsub => hb_not_P₁ (hsub hP.right_mem)⟩ hfin
          obtain ⟨Q, x, hx, y, hy, hQ, hVQ, hQ_inter⟩ :=
            ih V(P₁).ncard hlt₁ (hpath₁.mono hP.le) rfl ha' hzY
          exact ⟨Q, x, hx, y, hy, hQ, hVQ.trans hP₁.vertexSet_mono, hQ_inter⟩
      · refine ⟨P, a', ha', b', hb', hP, Subset.rfl, ?_⟩
        ext w
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        refine ⟨fun ⟨hwP, hwXY⟩ => ?_, ?_⟩
        · by_contra hw_not
          exact hhit ⟨w, ⟨hwP, hw_not⟩, hwXY⟩
        · rintro (rfl | rfl)
          · exact ⟨hP.left_mem, Or.inl ha'⟩
          · exact ⟨hP.right_mem, Or.inr hb'⟩
  obtain ⟨Q, x, hx, y, hy, hQ, hVQ, hQ_inter⟩ := hmain V(P₀).ncard hP₀ rfl ha hb
  exact ⟨Q, x, hx, y, hy, hQ, hVQ.trans (fun z hz => hVP₀ hz), hQ_inter⟩

/-- In a separation `(A, B)` of `C`, no vertex of `V(A) \ V(B)` is adjacent in `C` to any vertex of
`V(B) \ V(A)`. -/
theorem not_adj_of_isGraphSeparation {C A B : Graph α β'} (hsep : IsGraphSeparation C A B)
    {x y : α} (hx : x ∈ V(A) \ V(B)) (hy : y ∈ V(B) \ V(A)) : ¬ C.Adj x y := by
  rintro ⟨e, hlink⟩
  have he : e ∈ E(A) ∪ E(B) := hsep.2.2.2.1 ▸ hlink.edge_mem
  rcases he with heA | heB
  · have hlA : A.IsLink e x y := (hsep.1.isLink_iff heA).mpr hlink
    exact hy.2 hlA.right_mem
  · have hlB : B.IsLink e x y := (hsep.2.1.isLink_iff heB).mpr hlink
    exact hx.2 hlB.left_mem

/-- Given a core `C` of `S` and a walk `W` in `C` from `a` to `b`, each edge of `W` can be replaced
by a path in `S.G` with no internal vertex in `V(C)`, yielding a walk `W_G` in `S.G` from `a` to `b`
such that `V(W_G) ∩ V(C) ⊆ V(W)`. -/
theorem exists_walk_in_society_of_core_walk {S : Society α β} {C : Graph α β'}
    (hC : IsCoreOf S C) {a b : α} (W : GraphWalk C a b) :
    ∃ W_G : GraphWalk S.G a b,
      {z | z ∈ W_G.support} ∩ V(C) ⊆ {z | z ∈ W.support} := by
  induction W with
  | @nil u hu =>
    refine ⟨.nil (hC.isTrisecting.subset_V hu), fun z ⟨hz, _⟩ => hz⟩
  | @cons x y z e hlink W_rest ih =>
    obtain ⟨W_rest_G, hW_rest_G⟩ := ih
    have hxy : x ≠ y := IsSimpleGraph.ne_of_isLink hC.isSimple hlink
    obtain ⟨P_e, hP_e, hP_e_C⟩ :=
      (hC.adj_iff x hlink.left_mem y hlink.right_mem hxy).mp ⟨e, hlink⟩
    rcases hP_e with ⟨hP_e_le, W_e, _, hVP_e, _⟩
    obtain ⟨W_e_G, hs_e, _⟩ := exists_walk_up_of_le hP_e_le W_e
    refine ⟨W_e_G.append W_rest_G, fun w ⟨hw, hwC⟩ => ?_⟩
    rcases (GraphWalk.mem_support_append W_e_G W_rest_G).mp hw with hw_e | hw_rest
    · rw [hs_e] at hw_e
      have hwP : w ∈ V(P_e) := by rw [hVP_e]; exact hw_e
      have hw_xy : w ∈ ({x, y} : Set α) := hP_e_C ▸ ⟨hwP, hwC⟩
      rcases hw_xy with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ W_rest.start_mem_support
    · exact List.mem_cons_of_mem _ (hW_rest_G ⟨hw_rest, hwC⟩)

/-- Every path `P` in `S.G` with ends `a, b ∈ V(C)` induces a path `Q` in the core `C` with ends
`a, b` and `V(Q) ⊆ V(P) ∩ V(C)`. -/
theorem exists_core_path_of_society_path {S : Society α β} {C : Graph α β'}
    (hC : IsCoreOf S C) {P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds S.G P a b) (ha : a ∈ V(C)) (hb : b ∈ V(C)) :
    ∃ Q : Graph α β', IsGraphPathWithEnds C Q a b ∧ V(Q) ⊆ V(P) ∩ V(C) := by
  classical
  have hwalk : ∀ (n : ℕ) {a' b' : α} {P' : Graph α β},
      IsGraphPathWithEnds S.G P' a' b' → V(P').ncard = n → a' ∈ V(C) → b' ∈ V(C) →
      ∃ W_C : GraphWalk C a' b', ∀ z ∈ W_C.support, z ∈ V(P') ∩ V(C) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a' b' P' hP' hcard ha' hb'
      by_cases hab' : a' = b'
      · subst hab'
        refine ⟨.nil ha', fun z hz => ?_⟩
        simp only [GraphWalk.support_nil, List.mem_singleton] at hz
        exact hz ▸ ⟨hP'.left_mem, ha'⟩
      · by_cases hhit : ∃ z ∈ V(P') \ {a', b'}, z ∈ V(C)
        · rcases hhit with ⟨z, ⟨hzP', hz_not_ab⟩, hzC⟩
          simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz_not_ab
          obtain ⟨P₁, P₂, hP₁, hP₂, hpath₁, hpath₂, _, hinter, _⟩ := hP'.exists_split_at hzP'
          have hfin : V(P').Finite := hP'.vertexSet_finite
          have hb_not_P₁ : b' ∉ V(P₁) := fun hb₁ =>
            hz_not_ab.2 (mem_singleton_iff.mp (hinter ▸ ⟨hb₁, hpath₂.right_mem⟩)).symm
          have ha_not_P₂ : a' ∉ V(P₂) := fun ha₂ =>
            hz_not_ab.1 (mem_singleton_iff.mp (hinter ▸ ⟨hpath₁.left_mem, ha₂⟩)).symm
          have hlt₁ : V(P₁).ncard < n := hcard ▸
            ncard_lt_ncard ⟨hP₁.vertexSet_mono, fun hsub => hb_not_P₁ (hsub hP'.right_mem)⟩ hfin
          have hlt₂ : V(P₂).ncard < n := hcard ▸
            ncard_lt_ncard ⟨hP₂.vertexSet_mono, fun hsub => ha_not_P₂ (hsub hP'.left_mem)⟩ hfin
          obtain ⟨W₁, hW₁⟩ := ih V(P₁).ncard hlt₁ (hpath₁.mono hP'.le) rfl ha' hzC
          obtain ⟨W₂, hW₂⟩ := ih V(P₂).ncard hlt₂ (hpath₂.mono hP'.le) rfl hzC hb'
          refine ⟨W₁.append W₂, fun w hw => ?_⟩
          rcases (GraphWalk.mem_support_append W₁ W₂).mp hw with hw₁ | hw₂
          · exact ⟨hP₁.vertexSet_mono (hW₁ w hw₁).1, (hW₁ w hw₁).2⟩
          · exact ⟨hP₂.vertexSet_mono (hW₂ w hw₂).1, (hW₂ w hw₂).2⟩
        · have hP'_C : V(P') ∩ V(C) = {a', b'} := by
            ext z
            simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
            refine ⟨fun ⟨hzP', hzC⟩ => ?_, ?_⟩
            · by_contra h_not
              exact hhit ⟨z, ⟨hzP', h_not⟩, hzC⟩
            · rintro (rfl | rfl)
              · exact ⟨hP'.left_mem, ha'⟩
              · exact ⟨hP'.right_mem, hb'⟩
          obtain ⟨e, hlink⟩ := (hC.adj_iff a' ha' b' hb' hab').mpr ⟨P', hP', hP'_C⟩
          refine ⟨.cons hlink (.nil hb'), fun z hz => ?_⟩
          simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · exact ⟨hP'.left_mem, ha'⟩
          · exact ⟨hP'.right_mem, hb'⟩
  obtain ⟨W_C, hW_C⟩ := hwalk V(P).ncard hP rfl ha hb
  obtain ⟨Q, hQ, hVQ, _⟩ := exists_isGraphPathWithEnds_of_walk W_C
  exact ⟨Q, hQ, fun z hz => hW_C z (hVQ hz)⟩

/-! ## Proof of (8.2) (pages 94–95) -/

/-- **Graph Minors XIII, (8.2), Claim (1)** (Section 8, page 94):
"(1) *$V(B)$ is trisecting.*" -/
theorem lemma_8_2_claim_1 {S : Society α β} {C A B : Graph α β'}
    (hC : IsCoreOf S C) (hsep : IsGraphSeparation C A B)
    (hbar : S.Ω.bar ⊆ V(B)) (horder : (V(A) ∩ V(B)).ncard ≤ 3) :
    IsTrisecting S V(B) where
  subset_V := hsep.2.1.vertexSet_mono.trans hC.isTrisecting.subset_V
  bar_subset := hbar
  attach_ncard_le_three := by
    intro u ⟨huG, hu_not_B⟩
    let Z_B := {z ∈ V(B) | ∃ P : Graph α β, IsGraphPathWithEnds S.G P u z ∧ V(P) ∩ V(B) = {z}}
    by_contra hgt
    push Not at hgt
    obtain ⟨Y, hY_sub, hY_card⟩ := exists_subset_card_eq (show 4 ≤ Z_B.ncard by dsimp [Z_B]; omega)
    have hY_not_sub : ¬ Y ⊆ V(A) ∩ V(B) := by
      intro hsub
      have hle : Y.ncard ≤ (V(A) ∩ V(B)).ncard :=
        ncard_le_ncard hsub (S.finite_V.subset (inter_subset_right.trans
          (hsep.2.1.vertexSet_mono.trans hC.isTrisecting.subset_V)))
      omega
    obtain ⟨z₄, hz₄Y, hz₄_not_AB⟩ := not_subset.mp hY_not_sub
    have hz₄_ZB : z₄ ∈ Z_B := hY_sub hz₄Y
    have hz₄B : z₄ ∈ V(B) := hz₄_ZB.1
    have hz₄_not_A : z₄ ∉ V(A) := fun hA => hz₄_not_AB ⟨hA, hz₄B⟩
    obtain ⟨P₄, hP₄, hP₄_B⟩ := hz₄_ZB.2
    have hex_hit : ∃ z ∈ Y, ∃ P : Graph α β,
        IsGraphPathWithEnds S.G P u z ∧ V(P) ∩ V(B) = {z} ∧
        (V(P) ∩ (V(A) \ V(B))).Nonempty := by
      by_contra hno_hit
      push Not at hno_hit
      have hu_not_C : u ∉ V(C) := by
        intro huC
        have hu_AB : u ∈ V(A) \ V(B) := by
          rcases (hsep.2.2.1 ▸ huC : u ∈ V(A) ∪ V(B)) with huA | huB
          · exact ⟨huA, hu_not_B⟩
          · exact (hu_not_B huB).elim
        have hmem : u ∈ V(P₄) ∩ (V(A) \ V(B)) := ⟨hP₄.left_mem, hu_AB⟩
        rw [hno_hit z₄ hz₄Y P₄ hP₄ hP₄_B] at hmem
        exact hmem
      let Z_C := {z ∈ V(C) | ∃ P : Graph α β, IsGraphPathWithEnds S.G P u z ∧ V(P) ∩ V(C) = {z}}
      have hY_sub_ZC : Y ⊆ Z_C := by
        intro z hzY
        obtain ⟨hzB, P, hP, hPB⟩ := hY_sub hzY
        have hdisj := hno_hit z hzY P hP hPB
        refine ⟨hsep.2.1.vertexSet_mono hzB, P, hP, ?_⟩
        ext w
        simp only [mem_inter_iff, mem_singleton_iff]
        refine ⟨fun ⟨hwP, hwC⟩ => ?_, fun h => h ▸ ⟨hP.right_mem, hsep.2.1.vertexSet_mono hzB⟩⟩
        rcases (hsep.2.2.1 ▸ hwC : w ∈ V(A) ∪ V(B)) with hwA | hwB
        · by_cases hwB : w ∈ V(B)
          · exact mem_singleton_iff.mp (hPB ▸ ⟨hwP, hwB⟩)
          · exact False.elim (by
              have hmem : w ∈ V(P) ∩ (V(A) \ V(B)) := ⟨hwP, hwA, hwB⟩
              rw [hdisj] at hmem
              exact hmem)
        · exact mem_singleton_iff.mp (hPB ▸ ⟨hwP, hwB⟩)
      have hZC_fin : Z_C.Finite :=
        S.finite_V.subset (fun z hz => hC.isTrisecting.subset_V hz.1)
      have hle1 : Y.ncard ≤ Z_C.ncard := ncard_le_ncard hY_sub_ZC hZC_fin
      have hle2 : Z_C.ncard ≤ 3 := hC.isTrisecting.attach_ncard_le_three u ⟨huG, hu_not_C⟩
      omega
    obtain ⟨z₁, _, P₁, hP₁, hP₁_B, w, hwP₁, hw_AB⟩ := hex_hit
    obtain ⟨P_uw, P_wz₁, hP_uw_le, _, hpath_uw, hpath_wz₁, _, hinter_w, _⟩ :=
      hP₁.exists_split_at hwP₁
    have hV_uw_B : Disjoint V(P_uw) V(B) := by
      rw [disjoint_left]
      intro x hx_uw hxB
      have hx_z₁ : x = z₁ := mem_singleton_iff.mp (hP₁_B ▸ ⟨hP_uw_le.vertexSet_mono hx_uw, hxB⟩)
      subst hx_z₁
      have hz₁_w : x = w := mem_singleton_iff.mp (hinter_w ▸ ⟨hx_uw, hpath_wz₁.right_mem⟩)
      exact hw_AB.2 (hz₁_w ▸ hxB)
    obtain ⟨W₁, hW₁⟩ := ((hpath_uw.mono hP₁.le).symm).exists_walk_in Subset.rfl
    obtain ⟨W₄, hW₄⟩ := hP₄.exists_walk_in Subset.rfl
    let W := W₁.append W₄
    have hdisj_AB_B : Disjoint (V(A) \ V(B)) V(B) := disjoint_sdiff_left
    obtain ⟨Q, a, ha_AB, b, hbB, hQ, hVQ, hQ_inter⟩ :=
      exists_shortest_subpath_between_sets hdisj_AB_B hw_AB hz₄B W
    have hb_eq_z₄ : b = z₄ := by
      have hb_supp : b ∈ {z | z ∈ W.support} := hVQ hQ.right_mem
      rcases (GraphWalk.mem_support_append W₁ W₄).mp hb_supp with hb₁ | hb₄
      · exact (disjoint_left.mp hV_uw_B (hW₁ hb₁) hbB).elim
      · exact mem_singleton_iff.mp (hP₄_B ▸ ⟨hW₄ hb₄, hbB⟩)
    rcases hb_eq_z₄ with rfl
    have haC : a ∈ V(C) := hsep.1.vertexSet_mono ha_AB.1
    have hz₄C : b ∈ V(C) := hsep.2.1.vertexSet_mono hz₄B
    have haz₄ : a ≠ b := fun h => ha_AB.2 (h ▸ hz₄B)
    have hQ_C : V(Q) ∩ V(C) = {a, b} := by
      have hVC : V(C) = (V(A) \ V(B)) ∪ V(B) := by
        rw [← hsep.2.2.1, sdiff_union_self]
      rw [hVC]
      exact hQ_inter
    have hadj : C.Adj a b := (hC.adj_iff a haC b hz₄C haz₄).mpr ⟨Q, hQ, hQ_C⟩
    exact not_adj_of_isGraphSeparation hsep ha_AB ⟨hz₄B, hz₄_not_A⟩ hadj

/-- **Graph Minors XIII, (8.2), Claim (2)** (Section 8, page 94):
“(2) *If $a, b \in V(A \cap B)$ are distinct, there is a path of $G$ with ends $a, b$ and with no
internal vertex in $V(B)$.*” -/
theorem lemma_8_2_claim_2 {S : Society α β} {C A B : Graph α β'} {v : α}
    (hC : IsCoreOf S C)
    (hsep : IsGraphSeparation C A B) (hv : v ∈ V(A) \ V(B)) (hbar : S.Ω.bar ⊆ V(B))
    (hmin : ∀ A' B' : Graph α β', IsGraphSeparation C A' B' →
      v ∈ V(A') \ V(B') → S.Ω.bar ⊆ V(B') → (V(A) ∩ V(B)).ncard ≤ (V(A') ∩ V(B')).ncard)
    {a b : α} (ha : a ∈ V(A) ∩ V(B)) (hb : b ∈ V(A) ∩ V(B)) (_hab : a ≠ b) :
    ∃ P : Graph α β, IsGraphPathWithEnds S.G P a b ∧ V(P) ∩ V(B) = {a, b} := by
  classical
  have hex_walk_vx : ∀ x ∈ V(A) ∩ V(B),
      ∃ W : GraphWalk A v x, {z | z ∈ W.support} ⊆ (V(A) \ V(B)) ∪ {x} := by
    intro x hx
    let K' : Set α := (V(A) ∩ V(B)) \ {x}
    let A_x : Graph α β' := deleteVertices A K'
    have hv_Ax : v ∈ V(A_x) := ⟨hv.1, fun h => hv.2 h.1.2⟩
    have hx_Ax : x ∈ V(A_x) := ⟨hx.1, fun h => h.2 rfl⟩
    by_cases hconn : Nonempty (GraphWalk A_x v x)
    · obtain ⟨W₀⟩ := hconn
      obtain ⟨W_A, hs_A, _⟩ := exists_walk_up_of_le (deleteVertices_le A K') W₀
      refine ⟨W_A, fun z hz => ?_⟩
      rw [mem_ofPred_eq, hs_A] at hz
      have hz_Ax : z ∈ V(A_x) := W₀.mem_vertexSet_of_mem_support hz
      by_cases hzB : z ∈ V(B)
      · right
        rw [mem_singleton_iff]
        by_contra hzx
        exact hz_Ax.2 ⟨⟨hz_Ax.1, hzB⟩, hzx⟩
      · exact Or.inl ⟨hz_Ax.1, hzB⟩
    · exfalso
      let U : Set α := {u ∈ V(A_x) | Nonempty (GraphWalk A_x v u)}
      have hvU : v ∈ U := ⟨hv_Ax, ⟨.nil hv_Ax⟩⟩
      have hx_not_U : x ∉ U := fun h => hconn h.2
      have hU_sub_AB : U ⊆ V(A) \ V(B) := by
        intro u ⟨⟨huA, hu_not_K'⟩, hu_walk⟩
        refine ⟨huA, fun huB => ?_⟩
        by_cases hux : u = x
        · exact hx_not_U (hux ▸ ⟨⟨huA, hu_not_K'⟩, hu_walk⟩)
        · exact hu_not_K' ⟨⟨huA, huB⟩, hux⟩
      have hU_closed : ∀ ⦃e : β'⦄ ⦃u w : α⦄, C.IsLink e u w → u ∈ U → w ∈ U ∪ K' := by
        intro e u w hlink huU
        have hu_AB := hU_sub_AB huU
        have he_not_B : e ∉ E(B) := fun heB =>
          hu_AB.2 (((hsep.2.1.isLink_iff heB).mpr hlink).left_mem)
        have heA : e ∈ E(A) := by
          rcases (hsep.2.2.2.1 ▸ hlink.edge_mem : e ∈ E(A) ∪ E(B)) with h | h
          · exact h
          · exact (he_not_B h).elim
        have hlA : A.IsLink e u w := (hsep.1.isLink_iff heA).mpr hlink
        by_cases hwK' : w ∈ K'
        · exact Or.inr hwK'
        · left
          have hw_Ax : w ∈ V(A_x) := ⟨hlA.right_mem, hwK'⟩
          have hl_Ax : A_x.IsLink e u w := by
            change (A.induce (V(A) \ K')).IsLink e u w
            rw [induce_isLink]
            exact ⟨hlA, huU.1, hw_Ax⟩
          obtain ⟨W_vu⟩ := huU.2
          exact ⟨hw_Ax, ⟨W_vu.append (.cons hl_Ax (.nil hw_Ax))⟩⟩
      let A₁ : Graph α β' := C.induce (U ∪ K')
      let B₁ : Graph α β' := (C.induce (V(C) \ U)).restrict (E(C) \ E(A₁))
      have hUK'_sub_C : U ∪ K' ⊆ V(C) :=
        union_subset (hU_sub_AB.trans (sdiff_subset.trans hsep.1.vertexSet_mono))
          (sdiff_subset.trans (inter_subset_left.trans hsep.1.vertexSet_mono))
      have hA₁_le : A₁ ≤ C := C.induce_le hUK'_sub_C
      have hB₁_le : B₁ ≤ C := restrict_le.trans (C.induce_le sdiff_subset)
      have hsep₁ : IsGraphSeparation C A₁ B₁ := by
        refine ⟨hA₁_le, hB₁_le, ?_, ?_, ?_⟩
        · refine subset_antisymm (union_subset hA₁_le.vertexSet_mono hB₁_le.vertexSet_mono)
            fun z hz => ?_
          by_cases hzU : z ∈ U
          · exact Or.inl (Or.inl hzU)
          · exact Or.inr ⟨hz, hzU⟩
        · refine subset_antisymm (union_subset hA₁_le.edgeSet_mono hB₁_le.edgeSet_mono)
            fun e he => ?_
          by_cases heA₁ : e ∈ E(A₁)
          · exact Or.inl heA₁
          · right
            obtain ⟨u, w, hlink⟩ := C.exists_isLink_of_mem_edgeSet he
            have hu_not_U : u ∉ U := fun huU =>
              heA₁ ⟨u, w, hlink, Or.inl huU, hU_closed hlink huU⟩
            have hw_not_U : w ∉ U := fun hwU =>
              heA₁ ⟨w, u, hlink.symm, Or.inl hwU, hU_closed hlink.symm hwU⟩
            change e ∈ E((C.induce (V(C) \ U)).restrict (E(C) \ E(A₁)))
            rw [edgeSet_restrict]
            exact ⟨⟨u, w, hlink, ⟨hlink.left_mem, hu_not_U⟩, ⟨hlink.right_mem, hw_not_U⟩⟩, ⟨he, heA₁⟩⟩
        · change Disjoint E(A₁) E((C.induce (V(C) \ U)).restrict (E(C) \ E(A₁)))
          rw [edgeSet_restrict]
          exact disjoint_sdiff_right.mono_right inter_subset_right
      have hv_A₁B₁ : v ∈ V(A₁) \ V(B₁) := ⟨Or.inl hvU, fun h => h.2 hvU⟩
      have hbar_B₁ : S.Ω.bar ⊆ V(B₁) := fun z hz =>
        ⟨hsep.2.1.vertexSet_mono (hbar hz), fun hzU => (hU_sub_AB hzU).2 (hbar hz)⟩
      have hinter_eq : V(A₁) ∩ V(B₁) = K' := by
        ext z
        simp only [A₁, B₁, vertexSet_restrict, vertexSet_induce, mem_inter_iff, mem_union,
          mem_sdiff]
        refine ⟨fun ⟨hzUK', _, hz_not_U⟩ => ?_, fun hzK' => ⟨Or.inr hzK', ?_, ?_⟩⟩
        · rcases hzUK' with hzU | hzK'
          · exact (hz_not_U hzU).elim
          · exact hzK'
        · exact hsep.1.vertexSet_mono hzK'.1.1
        · exact fun hzU => (hU_sub_AB hzU).2 hzK'.1.2
      have hfin_AB : (V(A) ∩ V(B)).Finite :=
        S.finite_V.subset (inter_subset_left.trans
          (hsep.1.vertexSet_mono.trans hC.isTrisecting.subset_V))
      have hlt_card : (V(A₁) ∩ V(B₁)).ncard < (V(A) ∩ V(B)).ncard := by
        rw [hinter_eq]
        exact ncard_lt_ncard ⟨sdiff_subset, fun hsub => (hsub hx).2 rfl⟩ hfin_AB
      have hge_card := hmin A₁ B₁ hsep₁ hv_A₁B₁ hbar_B₁
      omega
  obtain ⟨W_va, hW_va⟩ := hex_walk_vx a ha
  obtain ⟨W_vb, hW_vb⟩ := hex_walk_vx b hb
  let W_ab : GraphWalk A a b := W_va.reverse.append W_vb
  obtain ⟨W_ab_C, hs_C, _⟩ := exists_walk_up_of_le hsep.1 W_ab
  obtain ⟨W_G, hW_G⟩ := exists_walk_in_society_of_core_walk hC W_ab_C
  obtain ⟨P, hP, hVP, _⟩ := exists_isGraphPathWithEnds_of_walk W_G
  refine ⟨P, hP, ?_⟩
  ext z
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun ⟨hzP, hzB⟩ => ?_, ?_⟩
  · have hzC : z ∈ V(C) := hsep.2.1.vertexSet_mono hzB
    have hz_supp_C : z ∈ {w | w ∈ W_ab_C.support} := hW_G ⟨hVP hzP, hzC⟩
    rw [mem_ofPred_eq, hs_C] at hz_supp_C
    rcases (GraphWalk.mem_support_append W_va.reverse W_vb).mp hz_supp_C with hza | hzb
    · rw [GraphWalk.support_reverse, List.mem_reverse] at hza
      rcases hW_va hza with ⟨_, hz_not_B⟩ | hza_eq
      · exact (hz_not_B hzB).elim
      · exact Or.inl (mem_singleton_iff.mp hza_eq)
    · rcases hW_vb hzb with ⟨_, hz_not_B⟩ | hzb_eq
      · exact (hz_not_B hzB).elim
      · exact Or.inr (mem_singleton_iff.mp hzb_eq)
  · rintro (rfl | rfl)
    · exact ⟨hP.left_mem, ha.2⟩
    · exact ⟨hP.right_mem, hb.2⟩

/-- **Graph Minors XIII, (8.2), Claim (3)** (Section 8, page 94):
“(3) *For distinct $a, b \in V(B)$, there is a path of $G$ with ends $a, b$ and with no internal
vertex in $V(B)$ if and only if $a, b$ are adjacent in $C'$.*” -/
theorem lemma_8_2_claim_3 {S : Society α β} {C A B : Graph α β'} {β'' : Type*} {C' : Graph α β''}
    {v : α} (hC : IsCoreOf S C) (hsep : IsGraphSeparation C A B)
    (hv : v ∈ V(A) \ V(B)) (hbar : S.Ω.bar ⊆ V(B))
    (hmin : ∀ A' B' : Graph α β', IsGraphSeparation C A' B' →
      v ∈ V(A') \ V(B') → S.Ω.bar ⊆ V(B') → (V(A) ∩ V(B)).ncard ≤ (V(A') ∩ V(B')).ncard)
    (hC' : IsCoreStepGraph B (V(A) ∩ V(B)) C')
    {a b : α} (ha : a ∈ V(B)) (hb : b ∈ V(B)) (hab : a ≠ b) :
    C'.Adj a b ↔ ∃ P : Graph α β, IsGraphPathWithEnds S.G P a b ∧ V(P) ∩ V(B) = {a, b} := by
  rw [hC'.adj_iff]
  constructor
  · rintro (hB_adj | ⟨⟨haAB, _⟩, ⟨hbAB, _⟩, _⟩)
    · have hC_adj : C.Adj a b := hB_adj.mono hsep.2.1
      obtain ⟨P, hP, hP_C⟩ :=
        (hC.adj_iff a (hsep.2.1.vertexSet_mono ha) b (hsep.2.1.vertexSet_mono hb) hab).mp hC_adj
      refine ⟨P, hP, ?_⟩
      ext z
      simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
      refine ⟨fun ⟨hzP, hzB⟩ => ?_, ?_⟩
      · have : z ∈ V(P) ∩ V(C) := ⟨hzP, hsep.2.1.vertexSet_mono hzB⟩
        rwa [hP_C, mem_insert_iff, mem_singleton_iff] at this
      · rintro (rfl | rfl)
        · exact ⟨hP.left_mem, ha⟩
        · exact ⟨hP.right_mem, hb⟩
    · exact lemma_8_2_claim_2 hC hsep hv hbar hmin haAB hbAB hab
  · rintro ⟨P, hP, hP_B⟩
    by_cases hboth : a ∈ V(A) ∧ b ∈ V(A)
    · exact Or.inr ⟨⟨⟨hboth.1, ha⟩, ha⟩, ⟨⟨hboth.2, hb⟩, hb⟩, hab⟩
    · left
      have hdisj_AB : Disjoint V(P) (V(A) \ V(B)) := by
        rw [disjoint_left]
        intro w hwP hw_AB
        obtain ⟨P_aw, P_wb, hP_aw_le, hP_wb_le, hpath_aw, hpath_wb, _, hinter_w, _⟩ :=
          hP.exists_split_at hwP
        have hdisj_B_AB : Disjoint V(B) (V(A) \ V(B)) := disjoint_sdiff_right
        have hVC : V(B) ∪ (V(A) \ V(B)) = V(C) := by
          rw [union_comm, sdiff_union_self, hsep.2.2.1]
        rcases not_and_or.mp hboth with ha_not_A | hb_not_A
        · obtain ⟨W_aw, hW_aw⟩ := (hpath_aw.mono hP.le).exists_walk_in Subset.rfl
          obtain ⟨Q, x, hxB, y, hy_AB, hQ, hVQ, hQ_inter⟩ :=
            exists_shortest_subpath_between_sets hdisj_B_AB ha hw_AB W_aw
          have hx_eq_a : x = a := by
            have hx_aw : x ∈ V(P_aw) := hW_aw (hVQ hQ.left_mem)
            have hx_ab : x ∈ ({a, b} : Set α) := hP_B ▸ ⟨hP_aw_le.vertexSet_mono hx_aw, hxB⟩
            rcases hx_ab with rfl | rfl
            · rfl
            · have hb_w : x = w := mem_singleton_iff.mp (hinter_w ▸ ⟨hx_aw, hpath_wb.right_mem⟩)
              exact (hw_AB.2 (hb_w ▸ hxB)).elim
          rcases hx_eq_a with rfl
          rw [hVC] at hQ_inter
          have haC : x ∈ V(C) := hsep.2.1.vertexSet_mono ha
          have hyC : y ∈ V(C) := hsep.1.vertexSet_mono hy_AB.1
          have hay : x ≠ y := fun h => hy_AB.2 (h ▸ ha)
          have hadj : C.Adj x y := (hC.adj_iff x haC y hyC hay).mpr ⟨Q, hQ, hQ_inter⟩
          exact not_adj_of_isGraphSeparation hsep hy_AB ⟨ha, ha_not_A⟩ hadj.symm
        · obtain ⟨W_bw, hW_bw⟩ := ((hpath_wb.mono hP.le).symm).exists_walk_in Subset.rfl
          obtain ⟨Q, x, hxB, y, hy_AB, hQ, hVQ, hQ_inter⟩ :=
            exists_shortest_subpath_between_sets hdisj_B_AB hb hw_AB W_bw
          have hx_eq_b : x = b := by
            have hx_wb : x ∈ V(P_wb) := hW_bw (hVQ hQ.left_mem)
            have hx_ab : x ∈ ({a, b} : Set α) := hP_B ▸ ⟨hP_wb_le.vertexSet_mono hx_wb, hxB⟩
            rcases hx_ab with rfl | rfl
            · have ha_w : x = w := mem_singleton_iff.mp (hinter_w ▸ ⟨hpath_aw.left_mem, hx_wb⟩)
              exact (hw_AB.2 (ha_w ▸ hxB)).elim
            · rfl
          rcases hx_eq_b with rfl
          rw [hVC] at hQ_inter
          have hbC : x ∈ V(C) := hsep.2.1.vertexSet_mono hb
          have hyC : y ∈ V(C) := hsep.1.vertexSet_mono hy_AB.1
          have hby : x ≠ y := fun h => hy_AB.2 (h ▸ hb)
          have hadj : C.Adj x y := (hC.adj_iff x hbC y hyC hby).mpr ⟨Q, hQ, hQ_inter⟩
          exact not_adj_of_isGraphSeparation hsep hy_AB ⟨hb, hb_not_A⟩ hadj.symm
      have hP_C : V(P) ∩ V(C) = {a, b} := by
        ext z
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        refine ⟨fun ⟨hzP, hzC⟩ => ?_, ?_⟩
        · rcases (hsep.2.2.1 ▸ hzC : z ∈ V(A) ∪ V(B)) with hzA | hzB
          · by_cases hzB : z ∈ V(B)
            · have hmem : z ∈ V(P) ∩ V(B) := ⟨hzP, hzB⟩
              rwa [hP_B, mem_insert_iff, mem_singleton_iff] at hmem
            · exact (disjoint_left.mp hdisj_AB hzP ⟨hzA, hzB⟩).elim
          · have hmem : z ∈ V(P) ∩ V(B) := ⟨hzP, hzB⟩
            rwa [hP_B, mem_insert_iff, mem_singleton_iff] at hmem
        · rintro (rfl | rfl)
          · exact ⟨hP.left_mem, hsep.2.1.vertexSet_mono ha⟩
          · exact ⟨hP.right_mem, hsep.2.1.vertexSet_mono hb⟩
      obtain ⟨e, hlink⟩ :=
        (hC.adj_iff a (hsep.2.1.vertexSet_mono ha) b (hsep.2.1.vertexSet_mono hb) hab).mpr
          ⟨P, hP, hP_C⟩
      rcases (hsep.2.2.2.1 ▸ hlink.edge_mem : e ∈ E(A) ∪ E(B)) with heA | heB
      · have hlA : A.IsLink e a b := (hsep.1.isLink_iff heA).mpr hlink
        exact (hboth ⟨hlA.left_mem, hlA.right_mem⟩).elim
      · exact ⟨e, (hsep.2.1.isLink_iff heB).mpr hlink⟩

/-- **Graph Minors XIII, (8.2), Claim (4)** (Section 8, page 95):
“(4) *If $v' \in V(C')$ is 4-linked in $C$ then it is 4-linked in $C'$.*” -/
theorem lemma_8_2_claim_4 {S : Society α β} {C A B : Graph α β'} {β'' : Type*} {C' : Graph α β''}
    (hsep : IsGraphSeparation C A B) (hC' : IsCoreStepGraph B (V(A) ∩ V(B)) C')
    {v' : α} (hv'C' : v' ∈ V(C')) (h4 : IsFourLinkedVertexIn S C v') :
    IsFourLinkedVertexIn S C' v' := by
  refine ⟨hv'C', fun A' B' hsep' horder' hbar' hv'_in => ?_⟩
  have hclique_side : V(A) ∩ V(B) ⊆ V(A') ∨ V(A) ∩ V(B) ⊆ V(B') := by
    by_contra hnot
    simp only [not_or, not_subset] at hnot
    obtain ⟨⟨x, hxAB, hx_not_A'⟩, ⟨y, hyAB, hy_not_B'⟩⟩ := hnot
    have hxC' : x ∈ V(C') := hC'.vertexSet_eq ▸ hxAB.2
    have hyC' : y ∈ V(C') := hC'.vertexSet_eq ▸ hyAB.2
    have hxB' : x ∈ V(B') := by
      rcases (hsep'.2.2.1 ▸ hxC' : x ∈ V(A') ∪ V(B')) with h | h
      · exact (hx_not_A' h).elim
      · exact h
    have hyA' : y ∈ V(A') := by
      rcases (hsep'.2.2.1 ▸ hyC' : y ∈ V(A') ∪ V(B')) with h | h
      · exact h
      · exact (hy_not_B' h).elim
    have hxy : x ≠ y := fun h => hx_not_A' (h ▸ hyA')
    have hadj : C'.Adj y x :=
      (hC'.adj_iff y x).mpr (Or.inr ⟨⟨hyAB, hyAB.2⟩, ⟨hxAB, hxAB.2⟩, hxy.symm⟩)
    exact not_adj_of_isGraphSeparation hsep' ⟨hyA', hy_not_B'⟩ ⟨hxB', hx_not_A'⟩ hadj
  have hVA'B'_eq : V(A') ∪ V(B') = V(B) := hsep'.2.2.1.trans hC'.vertexSet_eq
  have hVA'_sub_B : V(A') ⊆ V(B) := subset_union_left.trans hVA'B'_eq.le
  have hVB'_sub_B : V(B') ⊆ V(B) := subset_union_right.trans hVA'B'_eq.le
  have hB_edges : ∀ ⦃e : β'⦄ ⦃u w : α⦄, B.IsLink e u w →
      (u ∈ V(A') ∧ w ∈ V(A')) ∨ (u ∈ V(B') ∧ w ∈ V(B')) := by
    intro e u w hlB
    have hadjC' : C'.Adj u w := (hC'.adj_iff u w).mpr (Or.inl ⟨e, hlB⟩)
    obtain ⟨e', hlC'⟩ := hadjC'
    rcases (hsep'.2.2.2.1 ▸ hlC'.edge_mem : e' ∈ E(A') ∪ E(B')) with he'A' | he'B'
    · have hlA' := (hsep'.1.isLink_iff he'A').mpr hlC'
      exact Or.inl ⟨hlA'.left_mem, hlA'.right_mem⟩
    · have hlB' := (hsep'.2.1.isLink_iff he'B').mpr hlC'
      exact Or.inr ⟨hlB'.left_mem, hlB'.right_mem⟩
  rcases hclique_side with hAB_sub_A' | hAB_sub_B'
  · let A₁ : Graph α β' := C.induce (V(A) ∪ V(A'))
    let B₁ : Graph α β' := (C.induce V(B')).restrict (E(C) \ E(A₁))
    have hA₁_le : A₁ ≤ C :=
      C.induce_le (union_subset hsep.1.vertexSet_mono (hVA'_sub_B.trans hsep.2.1.vertexSet_mono))
    have hB₁_le : B₁ ≤ C := restrict_le.trans (C.induce_le (hVB'_sub_B.trans hsep.2.1.vertexSet_mono))
    have hsep₁ : IsGraphSeparation C A₁ B₁ := by
      refine ⟨hA₁_le, hB₁_le, ?_, ?_, ?_⟩
      · refine subset_antisymm (union_subset hA₁_le.vertexSet_mono hB₁_le.vertexSet_mono)
          fun z hz => ?_
        rcases (hsep.2.2.1 ▸ hz : z ∈ V(A) ∪ V(B)) with hzA | hzB
        · exact Or.inl (Or.inl hzA)
        · rcases (hVA'B'_eq ▸ hzB : z ∈ V(A') ∪ V(B')) with hzA' | hzB'
          · exact Or.inl (Or.inr hzA')
          · exact Or.inr hzB'
      · refine subset_antisymm (union_subset hA₁_le.edgeSet_mono hB₁_le.edgeSet_mono)
          fun e he => ?_
        by_cases heA₁ : e ∈ E(A₁)
        · exact Or.inl heA₁
        · right
          obtain ⟨u, w, hlink⟩ := C.exists_isLink_of_mem_edgeSet he
          rcases (hsep.2.2.2.1 ▸ he : e ∈ E(A) ∪ E(B)) with heA | heB
          · have hlA := (hsep.1.isLink_iff heA).mpr hlink
            exact (heA₁ ⟨u, w, hlink, Or.inl hlA.left_mem, Or.inl hlA.right_mem⟩).elim
          · have hlB := (hsep.2.1.isLink_iff heB).mpr hlink
            rcases hB_edges hlB with ⟨huA', hwA'⟩ | ⟨huB', hwB'⟩
            · exact (heA₁ ⟨u, w, hlink, Or.inr huA', Or.inr hwA'⟩).elim
            · change e ∈ E((C.induce V(B')).restrict (E(C) \ E(A₁)))
              rw [edgeSet_restrict]
              exact ⟨⟨u, w, hlink, huB', hwB'⟩, ⟨he, heA₁⟩⟩
      · change Disjoint E(A₁) E((C.induce V(B')).restrict (E(C) \ E(A₁)))
        rw [edgeSet_restrict]
        exact disjoint_sdiff_right.mono_right inter_subset_right
    have hinter_eq : V(A₁) ∩ V(B₁) = V(A') ∩ V(B') := by
      ext z
      simp only [A₁, B₁, vertexSet_restrict, vertexSet_induce, mem_inter_iff, mem_union]
      refine ⟨fun ⟨hzAA', hzB'⟩ => ⟨?_, hzB'⟩, fun ⟨hzA', hzB'⟩ => ⟨Or.inr hzA', hzB'⟩⟩
      rcases hzAA' with hzA | hzA'
      · exact hAB_sub_A' ⟨hzA, hVB'_sub_B hzB'⟩
      · exact hzA'
    have horder₁ : (V(A₁) ∩ V(B₁)).ncard ≤ 3 := by rwa [hinter_eq]
    exact h4.2 A₁ B₁ hsep₁ horder₁ hbar' ⟨Or.inr hv'_in.1, hv'_in.2⟩
  · let A₁ : Graph α β' := C.induce V(A')
    let B₁ : Graph α β' := (C.induce (V(A) ∪ V(B'))).restrict (E(C) \ E(A₁))
    have hA₁_le : A₁ ≤ C := C.induce_le (hVA'_sub_B.trans hsep.2.1.vertexSet_mono)
    have hB₁_le : B₁ ≤ C :=
      restrict_le.trans (C.induce_le (union_subset hsep.1.vertexSet_mono
        (hVB'_sub_B.trans hsep.2.1.vertexSet_mono)))
    have hsep₁ : IsGraphSeparation C A₁ B₁ := by
      refine ⟨hA₁_le, hB₁_le, ?_, ?_, ?_⟩
      · refine subset_antisymm (union_subset hA₁_le.vertexSet_mono hB₁_le.vertexSet_mono)
          fun z hz => ?_
        rcases (hsep.2.2.1 ▸ hz : z ∈ V(A) ∪ V(B)) with hzA | hzB
        · exact Or.inr (Or.inl hzA)
        · rcases (hVA'B'_eq ▸ hzB : z ∈ V(A') ∪ V(B')) with hzA' | hzB'
          · exact Or.inl hzA'
          · exact Or.inr (Or.inr hzB')
      · refine subset_antisymm (union_subset hA₁_le.edgeSet_mono hB₁_le.edgeSet_mono)
          fun e he => ?_
        by_cases heA₁ : e ∈ E(A₁)
        · exact Or.inl heA₁
        · right
          obtain ⟨u, w, hlink⟩ := C.exists_isLink_of_mem_edgeSet he
          rcases (hsep.2.2.2.1 ▸ he : e ∈ E(A) ∪ E(B)) with heA | heB
          · have hlA := (hsep.1.isLink_iff heA).mpr hlink
            change e ∈ E((C.induce (V(A) ∪ V(B'))).restrict (E(C) \ E(A₁)))
            rw [edgeSet_restrict]
            exact ⟨⟨u, w, hlink, Or.inl hlA.left_mem, Or.inl hlA.right_mem⟩, ⟨he, heA₁⟩⟩
          · have hlB := (hsep.2.1.isLink_iff heB).mpr hlink
            rcases hB_edges hlB with ⟨huA', hwA'⟩ | ⟨huB', hwB'⟩
            · exact (heA₁ ⟨u, w, hlink, huA', hwA'⟩).elim
            · change e ∈ E((C.induce (V(A) ∪ V(B'))).restrict (E(C) \ E(A₁)))
              rw [edgeSet_restrict]
              exact ⟨⟨u, w, hlink, Or.inr huB', Or.inr hwB'⟩, ⟨he, heA₁⟩⟩
      · change Disjoint E(A₁) E((C.induce (V(A) ∪ V(B'))).restrict (E(C) \ E(A₁)))
        rw [edgeSet_restrict]
        exact disjoint_sdiff_right.mono_right inter_subset_right
    have hinter_eq : V(A₁) ∩ V(B₁) = V(A') ∩ V(B') := by
      ext z
      simp only [A₁, B₁, vertexSet_restrict, vertexSet_induce, mem_inter_iff, mem_union]
      refine ⟨fun ⟨hzA', hzAB'⟩ => ⟨hzA', ?_⟩, fun ⟨hzA', hzB'⟩ => ⟨hzA', Or.inr hzB'⟩⟩
      rcases hzAB' with hzA | hzB'
      · exact hAB_sub_B' ⟨hzA, hVA'_sub_B hzA'⟩
      · exact hzB'
    have horder₁ : (V(A₁) ∩ V(B₁)).ncard ≤ 3 := by rwa [hinter_eq]
    have hbar₁ : S.Ω.bar ⊆ V(B₁) := hbar'.trans subset_union_right
    have hv'_not_B₁ : v' ∉ V(B₁) := by
      rintro (hv'A | hv'B')
      · exact hv'_in.2 (hAB_sub_B' ⟨hv'A, hVA'_sub_B hv'_in.1⟩)
      · exact hv'_in.2 hv'B'
    exact h4.2 A₁ B₁ hsep₁ horder₁ hbar₁ ⟨hv'_in.1, hv'_not_B₁⟩

/-- **Graph Minors XIII, (8.2)** (Section 8, pages 94–95):
“(8.2) *Let $C$ be a core of $(G, \Omega)$, and let $v \in V(C)$ not be 4-linked. Let $(A, B)$ be a
separation of $C$ with $v \in V(A) - V(B)$ and $\tilde{\Omega} \subseteq V(B)$, of minimum order,
and let $C'$ be the simple graph obtained from $B$ by adding edges joining all pairs of vertices in
$V(A \cap B)$ if they are not already adjacent. Then $C'$ is a core of $(G, \Omega)$, and each
$v' \in V(C')$ which is 4-linked in $C$ is also 4-linked in $C'$.*” -/
theorem theorem_8_2_proof {S : Society α β} {C A B : Graph α β'} {β'' : Type*} {C' : Graph α β''}
    {v : α} (hC : IsCoreOf S C) (hvC : v ∈ V(C)) (hv_not_4 : ¬ IsFourLinkedVertexIn S C v)
    (hsep : IsGraphSeparation C A B) (hv_AB : v ∈ V(A) \ V(B)) (hbar : S.Ω.bar ⊆ V(B))
    (hmin : ∀ A' B' : Graph α β', IsGraphSeparation C A' B' →
      v ∈ V(A') \ V(B') → S.Ω.bar ⊆ V(B') → (V(A) ∩ V(B)).ncard ≤ (V(A') ∩ V(B')).ncard)
    (hC' : IsCoreStepGraph B (V(A) ∩ V(B)) C') :
    IsCoreOf S C' ∧ ∀ v' ∈ V(C'), IsFourLinkedVertexIn S C v' → IsFourLinkedVertexIn S C' v' := by
  have horder : (V(A) ∩ V(B)).ncard ≤ 3 := by
    by_contra hgt
    push Not at hgt
    refine hv_not_4 ⟨hvC, fun A' B' hsep' hord' hbar' hv' => ?_⟩
    have hle := hmin A' B' hsep' hv' hbar'
    omega
  have hclaim1 : IsTrisecting S V(C') := by
    rw [hC'.vertexSet_eq]
    exact lemma_8_2_claim_1 hC hsep hbar horder
  have hclaim3 : ∀ a ∈ V(C'), ∀ b ∈ V(C'), a ≠ b →
      (C'.Adj a b ↔ ∃ P : Graph α β, IsGraphPathWithEnds S.G P a b ∧ V(P) ∩ V(C') = {a, b}) := by
    intro a ha b hb hab
    rw [hC'.vertexSet_eq] at ha hb ⊢
    exact lemma_8_2_claim_3 hC hsep hv_AB hbar hmin hC' ha hb hab
  exact ⟨⟨hC'.isSimple, hC'.finite_E, hclaim1, hclaim3⟩,
    fun v' hv' h4 => lemma_8_2_claim_4 hsep hC' hv' h4⟩

/-! ## Algorithm (8.3): Constructing a 4-linked core (page 95) -/

/-- The initial simple core `C₀` on vertex set `V(S.G)` obtained by making distinct `u, v ∈ V(S.G)`
adjacent in `C₀` if and only if they are adjacent in `S.G` (Graph Minors XIII, Section 8, (8.3),
page 95: “Initially, set $C = G$; then $C$ is a core, but it need not be 4-linked.”). -/
def initialCore (S : Society α β) : Graph α (Sym2 α) :=
  coreStepGraph S.G ∅

theorem isCoreOf_initialCore (S : Society α β) : IsCoreOf S (initialCore S) where
  isSimple := ⟨fun _ _ _ h => h.1 rfl, fun _ _ _ _ _ _ h1 h2 => h1.2.2.trans h2.2.2.symm⟩
  finite_E := by
    let f : α × α → Sym2 α := fun p => s(p.1, p.2)
    refine ((S.finite_V.prod S.finite_V).image f).subset ?_
    rintro e ⟨u, v, _, hadj, rfl⟩
    have hu : u ∈ V(S.G) := hadj.elim (fun h => h.left_mem) (fun h => h.1.2)
    have hv : v ∈ V(S.G) := hadj.elim (fun h => h.right_mem) (fun h => h.2.2)
    exact ⟨(u, v), ⟨hu, hv⟩, rfl⟩
  isTrisecting := by
    refine ⟨Subset.rfl, S.bar_subset, ?_⟩
    intro v ⟨hv, hv_not⟩
    exact (hv_not hv).elim
  adj_iff u _ v _ huv := by
    change (coreStepGraph S.G ∅).Adj u v ↔
      ∃ P : Graph α β, IsGraphPathWithEnds S.G P u v ∧ V(P) ∩ V(S.G) = {u, v}
    constructor
    · rintro ⟨_, _, hB | ⟨⟨h, _⟩, _⟩, _⟩
      · obtain ⟨e, hlink⟩ := hB
        let P := singleEdgeSubgraph S.G e
        have hP : IsGraphPathWithEnds S.G P u v :=
          (isGraphPathWithEnds_singleEdgeSubgraph huv hlink).mono (singleEdgeSubgraph_le S.G e)
        refine ⟨P, hP, ?_⟩
        rw [inter_eq_left.mpr hP.le.vertexSet_mono, vertexSet_singleEdgeSubgraph_eq_pair hlink]
      · exact h.elim
    · rintro ⟨P, hP, hPV⟩
      rw [inter_eq_left.mpr hP.le.vertexSet_mono] at hPV
      rcases hP with ⟨hPG, W, hW, hVP, _⟩
      cases W with
      | nil _ => exact (huv rfl).elim
      | @cons _ w _ e hlink W_rest =>
        have hw_uv : w ∈ ({u, v} : Set α) := by
          rw [← hPV, hVP]
          exact List.mem_cons_of_mem _ W_rest.start_mem_support
        rcases hw_uv with rfl | rfl
        · exact False.elim ((List.nodup_cons.mp hW).1 W_rest.start_mem_support)
        · exact ⟨s(u, w), huv, Or.inl ⟨e, hlink.mono hPG⟩, rfl⟩

/-- **Graph Minors XIII, (8.3) Algorithm** (Section 8, page 95):
“(8.3) Algorithm.
*Input:* A society $(G, \Omega)$.
*Output:* A 4-linked core of $(G, \Omega)$.
*Running time:* $O(\nu\varepsilon)$.
*Description:* Initially, set $C = G$; then $C$ is a core, but it need not be 4-linked. For each
vertex $v$ of $G$ in turn, if $v \in V(C)$ test if $v$ is 4-linked in $C$; and if $v$ is not
4-linked in $C$, choose $(A, B)$ as in (8.2), define $C'$ as in (8.2), and replace $C$ by $C'$.
When this terminates, $C$ is a 4-linked core, by the last assertion of (8.2). (For each
$v \in V(G)$ this takes time $O(\varepsilon)$; and so the total running time is
$O(\nu\varepsilon)$.)”

This is the correctness of the method. The RAM program, a loop over $v \in V(G)$ that tests
4-linkedness by flows of order at most 3, and its $O(v\varepsilon)$ time bound are
`GM13.algorithm_8_3` in `Results.lean`. -/
theorem algorithm_8_3_correct (S : Society α β) :
    ∃ C : Graph α (Sym2 α), IsFourLinkedCore S C := by
  classical
  have hmain : ∀ (n : ℕ) (C : Graph α (Sym2 α)),
      IsCoreOf S C → V(C).ncard = n →
      ∃ C_final : Graph α (Sym2 α), IsFourLinkedCore S C_final := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro C hC hcard
      by_cases hall : ∀ v ∈ V(C), IsFourLinkedVertexIn S C v
      · exact ⟨C, hC, hall⟩
      · push Not at hall
        obtain ⟨v, hvC, hv_not_4⟩ := hall
        have hex_sep : ∃ k : ℕ, ∃ A B : Graph α (Sym2 α),
            IsGraphSeparation C A B ∧ v ∈ V(A) \ V(B) ∧ S.Ω.bar ⊆ V(B) ∧
            (V(A) ∩ V(B)).ncard = k := by
          unfold IsFourLinkedVertexIn at hv_not_4
          push Not at hv_not_4
          obtain ⟨A, B, hsep, _, hbar, hv_in⟩ := hv_not_4 hvC
          exact ⟨(V(A) ∩ V(B)).ncard, A, B, hsep, hv_in, hbar, rfl⟩
        let k₀ := Nat.find hex_sep
        obtain ⟨A, B, hsep, hv_AB, hbar, hk₀⟩ := Nat.find_spec hex_sep
        have hmin : ∀ A' B' : Graph α (Sym2 α), IsGraphSeparation C A' B' →
            v ∈ V(A') \ V(B') → S.Ω.bar ⊆ V(B') →
            (V(A) ∩ V(B)).ncard ≤ (V(A') ∩ V(B')).ncard := by
          intro A' B' hsep' hv' hbar'
          rw [hk₀]
          exact Nat.find_min' hex_sep ⟨A', B', hsep', hv', hbar', rfl⟩
        let C' := coreStepGraph B (V(A) ∩ V(B))
        have hfin_C : V(C).Finite := S.finite_V.subset hC.isTrisecting.subset_V
        have hfin_B : V(B).Finite := hfin_C.subset hsep.2.1.vertexSet_mono
        have hstep : IsCoreStepGraph B (V(A) ∩ V(B)) C' :=
          isCoreStepGraph_coreStepGraph (IsSimpleGraph.mono hC.isSimple hsep.2.1) hfin_B (V(A) ∩ V(B))
        have hC' : IsCoreOf S C' :=
          (theorem_8_2_proof hC hvC hv_not_4 hsep hv_AB hbar hmin hstep).1
        have hlt : V(C').ncard < n := by
          rw [← hcard, hstep.vertexSet_eq]
          exact ncard_lt_ncard ⟨hsep.2.1.vertexSet_mono, fun hsub => hv_AB.2 (hsub hvC)⟩ hfin_C
        exact ih V(C').ncard hlt C' hC' rfl
  exact hmain V(initialCore S).ncard (initialCore S) (isCoreOf_initialCore S) rfl

/-- Alias `theorem_8_3_proof` for `algorithm_8_3_correct` so that automated numbering checks see `(8.3)`. -/
theorem theorem_8_3_proof (S : Society α β) :
    ∃ C : Graph α (Sym2 α), IsFourLinkedCore S C := by
  have hex := algorithm_8_3_correct S
  obtain ⟨C, hC⟩ := hex
  exact ⟨C, hC⟩

/-! ## Proof of (8.4) and (8.5) (page 95) -/

/-- If `C` is a core of `S`, and `P₁, P₂` are paths in `S.G` with ends `x₁, y₁ ∈ V(C)` (`x₁ ≠ y₁`)
and `x₂, y₂ ∈ V(C)` (`x₂ ≠ y₂`) such that `V(P₁) ∩ V(C) = {x₁, y₁}`, `V(P₂) ∩ V(C) = {x₂, y₂}`,
and `Disjoint {x₁, y₁} {x₂, y₂}`, then `Disjoint V(P₁) V(P₂)`. -/
theorem disjoint_core_jumps {S : Society α β} {C : Graph α β'} (hC : IsCoreOf S C)
    {P₁ P₂ : Graph α β} {x₁ y₁ x₂ y₂ : α}
    (hP₁ : IsGraphPathWithEnds S.G P₁ x₁ y₁) (hP₁_C : V(P₁) ∩ V(C) = {x₁, y₁}) (h1 : x₁ ≠ y₁)
    (hP₂ : IsGraphPathWithEnds S.G P₂ x₂ y₂) (hP₂_C : V(P₂) ∩ V(C) = {x₂, y₂}) (h2 : x₂ ≠ y₂)
    (hdisj_ends : Disjoint ({x₁, y₁} : Set α) {x₂, y₂}) :
    Disjoint V(P₁) V(P₂) := by
  rw [disjoint_left]
  intro v hv₁ hv₂
  have hv_not_C : v ∉ V(C) := by
    intro hvC
    have h1' : v ∈ V(P₁) ∩ V(C) := ⟨hv₁, hvC⟩
    have h2' : v ∈ V(P₂) ∩ V(C) := ⟨hv₂, hvC⟩
    rw [hP₁_C] at h1'
    rw [hP₂_C] at h2'
    exact disjoint_left.mp hdisj_ends h1' h2'
  have hvG : v ∈ V(S.G) := hP₁.le.vertexSet_mono hv₁
  obtain ⟨Q₁a, Q₁b, hQ₁a_le, hQ₁b_le, hp₁a, hp₁b, _, hinter₁, _⟩ := hP₁.exists_split_at hv₁
  obtain ⟨Q₂a, Q₂b, hQ₂a_le, hQ₂b_le, hp₂a, hp₂b, _, hinter₂, _⟩ := hP₂.exists_split_at hv₂
  have hx₁C : x₁ ∈ V(C) := by
    have h : x₁ ∈ V(P₁) ∩ V(C) := by rw [hP₁_C]; exact Or.inl rfl
    exact h.2
  have hy₁C : y₁ ∈ V(C) := by
    have h : y₁ ∈ V(P₁) ∩ V(C) := by rw [hP₁_C]; exact Or.inr rfl
    exact h.2
  have hx₂C : x₂ ∈ V(C) := by
    have h : x₂ ∈ V(P₂) ∩ V(C) := by rw [hP₂_C]; exact Or.inl rfl
    exact h.2
  have hy₂C : y₂ ∈ V(C) := by
    have h : y₂ ∈ V(P₂) ∩ V(C) := by rw [hP₂_C]; exact Or.inr rfl
    exact h.2
  have hQ₁a_C : V(Q₁a) ∩ V(C) = {x₁} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hzQ, hzC⟩ => ?_, fun h => h ▸ ⟨hp₁a.left_mem, hx₁C⟩⟩
    rcases (hP₁_C ▸ ⟨hQ₁a_le.vertexSet_mono hzQ, hzC⟩ : z ∈ ({x₁, y₁} : Set α)) with rfl | rfl
    · rfl
    · have hy₁_v : z = v := mem_singleton_iff.mp (hinter₁ ▸ ⟨hzQ, hp₁b.right_mem⟩)
      exact (hv_not_C (hy₁_v ▸ hzC)).elim
  have hQ₁b_C : V(Q₁b) ∩ V(C) = {y₁} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hzQ, hzC⟩ => ?_, fun h => h ▸ ⟨hp₁b.right_mem, hy₁C⟩⟩
    rcases (hP₁_C ▸ ⟨hQ₁b_le.vertexSet_mono hzQ, hzC⟩ : z ∈ ({x₁, y₁} : Set α)) with rfl | rfl
    · have hx₁_v : z = v := mem_singleton_iff.mp (hinter₁ ▸ ⟨hp₁a.left_mem, hzQ⟩)
      exact (hv_not_C (hx₁_v ▸ hzC)).elim
    · rfl
  have hQ₂a_C : V(Q₂a) ∩ V(C) = {x₂} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hzQ, hzC⟩ => ?_, fun h => h ▸ ⟨hp₂a.left_mem, hx₂C⟩⟩
    rcases (hP₂_C ▸ ⟨hQ₂a_le.vertexSet_mono hzQ, hzC⟩ : z ∈ ({x₂, y₂} : Set α)) with rfl | rfl
    · rfl
    · have hy₂_v : z = v := mem_singleton_iff.mp (hinter₂ ▸ ⟨hzQ, hp₂b.right_mem⟩)
      exact (hv_not_C (hy₂_v ▸ hzC)).elim
  have hQ₂b_C : V(Q₂b) ∩ V(C) = {y₂} := by
    ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hzQ, hzC⟩ => ?_, fun h => h ▸ ⟨hp₂b.right_mem, hy₂C⟩⟩
    rcases (hP₂_C ▸ ⟨hQ₂b_le.vertexSet_mono hzQ, hzC⟩ : z ∈ ({x₂, y₂} : Set α)) with rfl | rfl
    · have hx₂_v : z = v := mem_singleton_iff.mp (hinter₂ ▸ ⟨hp₂a.left_mem, hzQ⟩)
      exact (hv_not_C (hx₂_v ▸ hzC)).elim
    · rfl
  let Z_v := {z ∈ V(C) | ∃ P : Graph α β, IsGraphPathWithEnds S.G P v z ∧ V(P) ∩ V(C) = {z}}
  have hx₁_Zv : x₁ ∈ Z_v := ⟨hx₁C, Q₁a, (hp₁a.mono hP₁.le).symm, hQ₁a_C⟩
  have hy₁_Zv : y₁ ∈ Z_v := ⟨hy₁C, Q₁b, hp₁b.mono hP₁.le, hQ₁b_C⟩
  have hx₂_Zv : x₂ ∈ Z_v := ⟨hx₂C, Q₂a, (hp₂a.mono hP₂.le).symm, hQ₂a_C⟩
  have hy₂_Zv : y₂ ∈ Z_v := ⟨hy₂C, Q₂b, hp₂b.mono hP₂.le, hQ₂b_C⟩
  let S4 : Set α := {x₁, y₁, x₂, y₂}
  have hS4_sub : S4 ⊆ Z_v := by rintro z (rfl | rfl | rfl | rfl) <;> assumption
  have hnot1 : x₁ ∉ ({y₁, x₂, y₂} : Set α) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨h1, ?_, ?_⟩ <;> (rintro rfl; exact disjoint_left.mp hdisj_ends (Or.inl rfl) (by simp))
  have hnot2 : y₁ ∉ ({x₂, y₂} : Set α) :=
    fun hy => disjoint_left.mp hdisj_ends (Or.inr rfl) hy
  have hS4_card : S4.ncard = 4 := by
    rw [ncard_insert_of_notMem hnot1 (((finite_singleton y₂).insert x₂).insert y₁),
      ncard_insert_of_notMem hnot2 ((finite_singleton y₂).insert x₂),
      ncard_pair h2]
  have hZv_fin : Z_v.Finite :=
    S.finite_V.subset (fun z hz => hC.isTrisecting.subset_V hz.1)
  have hle1 : S4.ncard ≤ Z_v.ncard := ncard_le_ncard hS4_sub hZv_fin
  have hle2 : Z_v.ncard ≤ 3 := hC.isTrisecting.attach_ncard_le_three v ⟨hvG, hv_not_C⟩
  omega

/-- **Graph Minors XIII, (8.4)** (Section 8, page 95):
“(8.4) *If $C$ is a core of $(G, \Omega)$ then $(G, \Omega)$ has a cross if and only if
$(C, \Omega)$ has a cross.*” -/
theorem theorem_8_4_proof {S : Society α β} {C : Graph α β'} (hC : IsCoreOf S C) :
    HasCross S ↔ HasCross (coreSociety S C hC) := by
  classical
  let CS := coreSociety S C hC
  constructor
  · rintro ⟨P, Q, hdisj, p₁, p₂, q₁, q₂, hP, hQ, hcr⟩
    have hp₁C : p₁ ∈ V(C) := hC.isTrisecting.bar_subset hP.2.2.1
    have hp₂C : p₂ ∈ V(C) := hC.isTrisecting.bar_subset hP.2.2.2
    have hq₁C : q₁ ∈ V(C) := hC.isTrisecting.bar_subset hQ.2.2.1
    have hq₂C : q₂ ∈ V(C) := hC.isTrisecting.bar_subset hQ.2.2.2
    obtain ⟨P_C, hP_C, hVP_C⟩ := exists_core_path_of_society_path hC hP.1 hp₁C hp₂C
    obtain ⟨Q_C, hQ_C, hVQ_C⟩ := exists_core_path_of_society_path hC hQ.1 hq₁C hq₂C
    have hdisj_C : Disjoint V(P_C) V(Q_C) :=
      hdisj.mono (hVP_C.trans inter_subset_left) (hVQ_C.trans inter_subset_left)
    exact ⟨P_C, Q_C, hdisj_C, p₁, p₂, q₁, q₂,
      ⟨hP_C, hP.2.1, hP.2.2.1, hP.2.2.2⟩,
      ⟨hQ_C, hQ.2.1, hQ.2.2.1, hQ.2.2.2⟩, hcr⟩
  · rintro ⟨P_C, Q_C, hdisj_C, p₁, p₂, q₁, q₂, hP_C, hQ_C, hcr⟩
    have hex_jump : ∀ e : E(C), ∃ J : Graph α β,
        ∀ x y : α, C.IsLink e.1 x y →
          IsGraphPathWithEnds S.G J x y ∧ V(J) ∩ V(C) = {x, y} := by
      intro e
      obtain ⟨u, v, hlink⟩ := C.exists_isLink_of_mem_edgeSet e.2
      have huv : u ≠ v := IsSimpleGraph.ne_of_isLink hC.isSimple hlink
      obtain ⟨J, hJ, hJC⟩ :=
        (hC.adj_iff u hlink.left_mem v hlink.right_mem huv).mp ⟨e.1, hlink⟩
      refine ⟨J, fun x y hl => ?_⟩
      have hxy_ne : x ≠ y := IsSimpleGraph.ne_of_isLink hC.isSimple hl
      rcases C.eq_or_eq_of_isLink_of_isLink hl hlink with rfl | rfl <;>
        rcases C.eq_or_eq_of_isLink_of_isLink hl.symm hlink with rfl | rfl
      · exact (hxy_ne rfl).elim
      · exact ⟨hJ, hJC⟩
      · exact ⟨hJ.symm, by rw [hJC, pair_comm]⟩
      · exact (hxy_ne rfl).elim
    choose J_of hJ_spec using hex_jump
    have hlift_walk : ∀ {a b : α} (W : GraphWalk C a b),
        ∃ W_G : GraphWalk S.G a b, ∀ z ∈ W_G.support,
          z ∈ {x | x ∈ W.support} ∪ ⋃ (e : E(C)) (_ : e.1 ∈ W.edges), V(J_of e) := by
      intro a b W
      induction W with
      | @nil u hu =>
        refine ⟨.nil (hC.isTrisecting.subset_V hu), fun z hz => ?_⟩
        simp only [GraphWalk.support_nil, List.mem_singleton] at hz
        exact Or.inl (by simp [hz])
      | @cons x y z e hlink W_rest ih =>
        obtain ⟨W_rest_G, hW_rest_G⟩ := ih
        let e_sub : E(C) := ⟨e, hlink.edge_mem⟩
        obtain ⟨⟨hJ_le, W_J, _, hVJ, _⟩, _⟩ := hJ_spec e_sub x y hlink
        obtain ⟨W_J_G, hs_J, _⟩ := exists_walk_up_of_le hJ_le W_J
        refine ⟨W_J_G.append W_rest_G, fun w hw => ?_⟩
        rcases (GraphWalk.mem_support_append W_J_G W_rest_G).mp hw with hw_J | hw_rest
        · right
          rw [hs_J] at hw_J
          exact mem_iUnion₂.mpr ⟨e_sub, List.mem_cons_self, by rw [hVJ]; exact hw_J⟩
        · rcases hW_rest_G w hw_rest with hw_supp | hw_edges
          · exact Or.inl (List.mem_cons_of_mem _ hw_supp)
          · right
            obtain ⟨e', he', hwJ'⟩ := mem_iUnion₂.mp hw_edges
            exact mem_iUnion₂.mpr ⟨e', List.mem_cons_of_mem _ he', hwJ'⟩
    let U₁ : Set α := V(P_C) ∪ ⋃ (e : E(C)) (_ : e.1 ∈ E(P_C)), V(J_of e)
    let U₂ : Set α := V(Q_C) ∪ ⋃ (e : E(C)) (_ : e.1 ∈ E(Q_C)), V(J_of e)
    have hP_C_le : P_C ≤ C := hP_C.1.le
    have hQ_C_le : Q_C ≤ C := hQ_C.1.le
    have hdisj_U : Disjoint U₁ U₂ := by
      rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
      refine ⟨⟨hdisj_C, disjoint_iUnion₂_right.mpr fun e₂ he₂ => ?_⟩,
        ⟨disjoint_iUnion₂_left.mpr fun e₁ he₁ => ?_,
         disjoint_iUnion₂_left.mpr fun e₁ he₁ => disjoint_iUnion₂_right.mpr fun e₂ he₂ => ?_⟩⟩
      · obtain ⟨x₂, y₂, hl₂⟩ := Q_C.exists_isLink_of_mem_edgeSet he₂
        obtain ⟨_, hJ₂_C⟩ := hJ_spec e₂ x₂ y₂ (hl₂.mono hQ_C_le)
        refine disjoint_left.mpr fun z hzP hzJ₂ => disjoint_left.mp hdisj_C hzP ?_
        rcases (hJ₂_C ▸ ⟨hzJ₂, hP_C_le.vertexSet_mono hzP⟩ : z ∈ ({x₂, y₂} : Set α)) with rfl | rfl
        · exact hl₂.left_mem
        · exact hl₂.right_mem
      · obtain ⟨x₁, y₁, hl₁⟩ := P_C.exists_isLink_of_mem_edgeSet he₁
        obtain ⟨_, hJ₁_C⟩ := hJ_spec e₁ x₁ y₁ (hl₁.mono hP_C_le)
        refine disjoint_left.mpr fun z hzJ₁ hzQ => disjoint_left.mp hdisj_C ?_ hzQ
        rcases (hJ₁_C ▸ ⟨hzJ₁, hQ_C_le.vertexSet_mono hzQ⟩ : z ∈ ({x₁, y₁} : Set α)) with rfl | rfl
        · exact hl₁.left_mem
        · exact hl₁.right_mem
      · obtain ⟨x₁, y₁, hl₁⟩ := P_C.exists_isLink_of_mem_edgeSet he₁
        obtain ⟨x₂, y₂, hl₂⟩ := Q_C.exists_isLink_of_mem_edgeSet he₂
        have hl₁C := hl₁.mono hP_C_le
        have hl₂C := hl₂.mono hQ_C_le
        obtain ⟨hJ₁, hJ₁_C⟩ := hJ_spec e₁ x₁ y₁ hl₁C
        obtain ⟨hJ₂, hJ₂_C⟩ := hJ_spec e₂ x₂ y₂ hl₂C
        exact disjoint_core_jumps hC hJ₁ hJ₁_C (IsSimpleGraph.ne_of_isLink hC.isSimple hl₁C)
          hJ₂ hJ₂_C (IsSimpleGraph.ne_of_isLink hC.isSimple hl₂C)
          (hdisj_C.mono
            (by rintro z (rfl | rfl); exacts [hl₁.left_mem, hl₁.right_mem])
            (by rintro z (rfl | rfl); exacts [hl₂.left_mem, hl₂.right_mem]))
    have hW₁ : ∃ W : GraphWalk S.G p₁ p₂, {x | x ∈ W.support} ⊆ U₁ := by
      rcases hP_C.1 with ⟨hP_le, W_P, _, hVP, hEP⟩
      obtain ⟨W_C, hs_C, he_C⟩ := exists_walk_up_of_le hP_C_le W_P
      obtain ⟨W_G, hW_G⟩ := hlift_walk W_C
      refine ⟨W_G, fun z hz => ?_⟩
      rcases hW_G z hz with hz_supp | hz_edges
      · left; rw [hVP, mem_ofPred_eq, ← hs_C]; exact hz_supp
      · right
        obtain ⟨e, heW, hzJ⟩ := mem_iUnion₂.mp hz_edges
        rw [he_C] at heW
        exact mem_iUnion₂.mpr ⟨e, by rw [hEP]; exact heW, hzJ⟩
    have hW₂ : ∃ W : GraphWalk S.G q₁ q₂, {x | x ∈ W.support} ⊆ U₂ := by
      rcases hQ_C.1 with ⟨hQ_le, W_Q, _, hVQ, hEQ⟩
      obtain ⟨W_C, hs_C, he_C⟩ := exists_walk_up_of_le hQ_C_le W_Q
      obtain ⟨W_G, hW_G⟩ := hlift_walk W_C
      refine ⟨W_G, fun z hz => ?_⟩
      rcases hW_G z hz with hz_supp | hz_edges
      · left; rw [hVQ, mem_ofPred_eq, ← hs_C]; exact hz_supp
      · right
        obtain ⟨e, heW, hzJ⟩ := mem_iUnion₂.mp hz_edges
        rw [he_C] at heW
        exact mem_iUnion₂.mpr ⟨e, by rw [hEQ]; exact heW, hzJ⟩
    exact S.exists_isCross_of_disjoint_walks
      hP_C.2.2.1 hP_C.2.2.2 hQ_C.2.2.1 hQ_C.2.2.2 hcr hdisj_U hW₁ hW₂

/-- If `C` is a 4-linked core of `S`, then `(coreSociety S C hC.isCore)` is 4-connected in the
sense of `GM09.Society.IsKConnected 4`. -/
theorem isFourConnected_coreSociety {S : Society α β} {C : Graph α β'}
    (hC : IsFourLinkedCore S C) :
    (coreSociety S C hC.isCore).IsKConnected 4 := by
  intro k' hk' G₁ G₂ ⟨⟨hsep, hbar⟩, hord, hne⟩
  have hdiff_ne : (V(G₁) \ V(G₂)).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
    exact hne ((union_eq_right.mpr hemp).symm.trans hsep.2.2.1)
  obtain ⟨v, hv⟩ := hdiff_ne
  have hvC : v ∈ V(C) := hsep.1.vertexSet_mono hv.1
  exact (hC.fourLinked v hvC).2 G₁ G₂ hsep (by omega) hbar hv

private def oArcMap {S : Type*} [TopologicalSpace S] {C : Set S} (φ : Circle ≃ₜ C) : Circle → S :=
  Subtype.val ∘ φ

private theorem isEmbedding_oArcMap {S : Type*} [TopologicalSpace S] {C : Set S}
    (φ : Circle ≃ₜ C) : IsEmbedding (oArcMap φ) :=
  IsEmbedding.subtypeVal.comp φ.isEmbedding

private theorem injective_oArcMap {S : Type*} [TopologicalSpace S] {C : Set S}
    (φ : Circle ≃ₜ C) : Injective (oArcMap φ) :=
  (isEmbedding_oArcMap φ).injective

@[simp]
private theorem oArcMap_mem {S : Type*} [TopologicalSpace S] {C : Set S}
    (φ : Circle ≃ₜ C) (z : Circle) : oArcMap φ z ∈ C :=
  (φ z).2

@[simp]
private theorem range_oArcMap {S : Type*} [TopologicalSpace S] {C : Set S}
    (φ : Circle ≃ₜ C) : range (oArcMap φ) = C := by
  ext x
  simp only [oArcMap, mem_range, comp_apply]
  exact ⟨fun ⟨z, hz⟩ => hz ▸ (φ z).2, fun hx => ⟨φ.symm ⟨x, hx⟩, by simp⟩⟩

private theorem diff_image_oArcMap {S : Type*} [TopologicalSpace S] {C : Set S}
    (φ : Circle ≃ₜ C) (s : Set Circle) : C \ (oArcMap φ '' s) = oArcMap φ '' sᶜ := by
  have hrange := range_oArcMap φ
  rw [← image_univ] at hrange
  rw [compl_eq_univ_sdiff, image_sdiff (injective_oArcMap φ), hrange]

private theorem crossesOn_univ_iff_circleStdCoord {a c b d : Circle} :
    CrossesOn (univ : Set Circle) a c b d ↔ circleCrosses circleStdCoord a c b d := by
  simp only [CrossesOn, mem_univ, true_and, ← compl_eq_univ_sdiff]
  constructor
  · rintro ⟨hac, hbd, hab, had, hcb, hcd, hcc⟩
    exact (connectedComponentIn_compl_pair_ne_iff_circleCrosses hac hbd hab had hcb hcd).mp hcc
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      (connectedComponentIn_compl_pair_ne_iff_circleCrosses
        h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1).mpr h⟩

private theorem crossesOn_univ_iff_angleDiff {a c b d : Circle} :
    CrossesOn (univ : Set Circle) a c b d ↔
      a ≠ c ∧ b ≠ d ∧ a ≠ b ∧ a ≠ d ∧ c ≠ b ∧ c ≠ d ∧
      (a.angleDiff b < a.angleDiff c ↔ ¬ a.angleDiff d < a.angleDiff c) := by
  rw [crossesOn_univ_iff_circleStdCoord, circleCrosses_circleStdCoord_iff_angleDiff]

private theorem crossesOn_oArcMap_iff {S : Type*} [TopologicalSpace S] {C : Set S}
    (φ : Circle ≃ₜ C) {a c b d : Circle} :
    CrossesOn C (oArcMap φ a) (oArcMap φ c) (oArcMap φ b) (oArcMap φ d) ↔
      CrossesOn (univ : Set Circle) a c b d := by
  have hinj := injective_oArcMap φ
  have hemb := isEmbedding_oArcMap φ
  have hpair : C \ {oArcMap φ a, oArcMap φ c} = oArcMap φ '' ({a, c} : Set Circle)ᶜ := by
    rw [← diff_image_oArcMap φ]
    simp
  simp only [CrossesOn, oArcMap_mem, mem_univ, true_and, hinj.ne_iff, ← compl_eq_univ_sdiff]
  refine and_congr_right fun hac => and_congr_right fun hbd =>
    and_congr_right fun hab => and_congr_right fun had =>
    and_congr_right fun hcb => and_congr_right fun hcd => ?_
  have hb_mem : b ∈ ({a, c} : Set Circle)ᶜ := by simp [hab.symm, hcb.symm]
  have hd_mem : d ∈ ({a, c} : Set Circle)ᶜ := by simp [had.symm, hcd.symm]
  rw [hpair, ← isEmbedding_image_connectedComponentIn hemb hb_mem,
    ← isEmbedding_image_connectedComponentIn hemb hd_mem, ne_eq, ne_eq, image_eq_image hinj]

private theorem isCompact_of_isClosedDisc {S : Type*} [TopologicalSpace S] {Δ : Set S}
    (hΔ : IsClosedDisc Δ) : IsCompact Δ := by
  obtain ⟨e⟩ := hΔ
  have h1 : CompactSpace ClosedUnitDisc :=
    isCompact_iff_compactSpace.mp
      (Metric.isCompact_of_isClosed_isBounded Metric.isClosed_closedBall Metric.isBounded_closedBall)
  have h2 : CompactSpace Δ := e.compactSpace
  exact isCompact_iff_compactSpace.mpr h2

private theorem graphDrawingVertexSet_eq_singleton {S : Type*} [TopologicalSpace S]
    {G : Graph α β'} (Γ : GraphDrawing G S) {v : α} (hv : v ∈ V(G)) :
    graphDrawingVertexSet Γ v = {(Γ.iso.vertexEquiv ⟨v, hv⟩).1} := by
  ext x
  simp [graphDrawingVertexSet, hv, eq_comm]

private theorem graphDrawingVertexSet_nonempty {S : Type*} [TopologicalSpace S]
    {G : Graph α β'} (Γ : GraphDrawing G S) {v : α} (hv : v ∈ V(G)) :
    (graphDrawingVertexSet Γ v).Nonempty := by
  rw [graphDrawingVertexSet_eq_singleton Γ hv]
  exact singleton_nonempty _

private theorem graphDrawingVertexSet_inj {S : Type*} [TopologicalSpace S]
    {G : Graph α β'} (Γ : GraphDrawing G S) {u v : α} {x : S}
    (hu : x ∈ graphDrawingVertexSet Γ u) (hv : x ∈ graphDrawingVertexSet Γ v) :
    u = v := by
  rcases hu with ⟨huG, rfl⟩
  rcases hv with ⟨hvG, hveq⟩
  have hsub : Γ.iso.vertexEquiv ⟨v, hvG⟩ = Γ.iso.vertexEquiv ⟨u, huG⟩ :=
    Subtype.ext hveq
  exact congrArg Subtype.val (Γ.iso.vertexEquiv.injective hsub).symm

private theorem graphDrawingEdgeSet_eq {S : Type*} [TopologicalSpace S]
    {G : Graph α β'} (Γ : GraphDrawing G S) {e : β'} (he : e ∈ E(G)) :
    graphDrawingEdgeSet Γ e = (Γ.iso.edgeEquiv ⟨e, he⟩).1 := by
  ext x
  simp [graphDrawingEdgeSet, he]

private theorem graphDrawingVertexSet_subset_closure_edge {S : Type*} [TopologicalSpace S]
    {G : Graph α β'} (Γ : GraphDrawing G S) {e : β'} {u v : α} (hl : G.IsLink e u v) :
    graphDrawingVertexSet Γ u ⊆ closure (graphDrawingEdgeSet Γ e) := by
  have hu : u ∈ V(G) := hl.left_mem
  have hv : v ∈ V(G) := hl.right_mem
  have he : e ∈ E(G) := hl.edge_mem
  rw [graphDrawingVertexSet_eq_singleton Γ hu, graphDrawingEdgeSet_eq Γ he, singleton_subset_iff]
  have hlink := (Γ.iso.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨v, hv⟩).mp hl
  have hmem : (Γ.iso.vertexEquiv ⟨u, hu⟩).1 ∈
      ({(Γ.iso.vertexEquiv ⟨u, hu⟩).1, (Γ.iso.vertexEquiv ⟨v, hv⟩).1} : Set S) :=
    mem_insert _ _
  rw [← hlink.2.2.2] at hmem
  exact hmem.1

private theorem graphDrawingVertexSet_subset_subgraphU_of_mem {S : Type*} [TopologicalSpace S]
    {G P : Graph α β'} (Γ : GraphDrawing G S) {v : α} (hv : v ∈ V(P)) :
    graphDrawingVertexSet Γ v ⊆ graphDrawingSubgraphU Γ P :=
  (subset_biUnion_of_mem (u := fun u => graphDrawingVertexSet Γ u) hv).trans subset_union_left

private theorem mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU {S : Type*}
    [TopologicalSpace S] {G P : Graph α β'} (Γ : GraphDrawing G S) (hPG : P ≤ G)
    {v : α} (hv : v ∈ V(G)) (hsub : graphDrawingVertexSet Γ v ⊆ graphDrawingSubgraphU Γ P) :
    v ∈ V(P) := by
  let x := (Γ.iso.vertexEquiv ⟨v, hv⟩).1
  have hx_v : x ∈ graphDrawingVertexSet Γ v := ⟨hv, rfl⟩
  have hx_V : x ∈ Γ.drawing.V := (Γ.iso.vertexEquiv ⟨v, hv⟩).2
  rcases hsub hx_v with hx_vert | hx_edge
  · obtain ⟨u, huP, hxu⟩ := mem_iUnion₂.mp hx_vert
    exact (graphDrawingVertexSet_inj Γ hx_v hxu) ▸ huP
  · obtain ⟨e, heP, hxe⟩ := mem_iUnion₂.mp hx_edge
    obtain ⟨a, b, habP⟩ := P.exists_isLink_of_mem_edgeSet heP
    have habG : G.IsLink e a b := habP.mono hPG
    have haG : a ∈ V(G) := habG.left_mem
    have hbG : b ∈ V(G) := habG.right_mem
    have heG : e ∈ E(G) := habG.edge_mem
    rw [graphDrawingEdgeSet_eq Γ heG] at hxe
    have hlink := (Γ.iso.isLink_iff ⟨e, heG⟩ ⟨a, haG⟩ ⟨b, hbG⟩).mp habG
    have hx_inter : x ∈ closure (Γ.iso.edgeEquiv ⟨e, heG⟩).1 ∩ Γ.drawing.V := ⟨hxe, hx_V⟩
    rw [hlink.2.2.2] at hx_inter
    rcases hx_inter with hx_a | hx_b
    · have hva : v = a := graphDrawingVertexSet_inj Γ hx_v ⟨haG, hx_a.symm⟩
      exact hva ▸ habP.left_mem
    · have hvb : v = b := graphDrawingVertexSet_inj Γ hx_v ⟨hbG, Set.mem_singleton_iff.mp hx_b ▸ rfl⟩
      exact hvb ▸ habP.right_mem

private theorem isConnected_closure_edge {S : Type*} [TopologicalSpace S]
    (G : Drawing S) {e : Set S} (he : e ∈ G.E) :
    IsConnected (closure e) := by
  rcases G.edge_cond e he with ⟨u, v, _, _, f, _, _⟩ | ⟨u, _, ⟨f⟩⟩
  · have : ConnectedSpace (closure e) := f.surjective.connectedSpace f.continuous
    exact isConnected_iff_connectedSpace.mpr this
  · have : ConnectedSpace (closure e) := f.surjective.connectedSpace f.continuous
    exact isConnected_iff_connectedSpace.mpr this

private theorem disjoint_edges_of_ne {S : Type*} [TopologicalSpace S]
    (G : Drawing S) {e₁ e₂ : Set S} (he₁ : e₁ ∈ G.E) (he₂ : e₂ ∈ G.E) (hne : e₁ ≠ e₂) :
    Disjoint e₁ e₂ := by
  rw [Set.disjoint_iff_inter_eq_empty]
  by_contra hnon
  have hnon_empty : (e₁ ∩ e₂).Nonempty := nonempty_iff_ne_empty.mpr hnon
  have hpc : IsPathConnected (e₁ ∪ e₂) := he₁.2.2.1.union he₂.2.2.1 hnon_empty
  have hsub : e₁ ∪ e₂ ⊆ G.U \ G.V := union_subset he₁.2.1 he₂.2.1
  have heq₁ : e₁ ∪ e₂ = e₁ := he₁.2.2.2 (e₁ ∪ e₂) hsub hpc subset_union_left
  have heq₂ : e₁ ∪ e₂ = e₂ := he₂.2.2.2 (e₁ ∪ e₂) hsub hpc subset_union_right
  exact hne (heq₁.symm.trans heq₂)

private theorem closure_edge_eq_union_ends {S : Type*} [TopologicalSpace S]
    (G : Drawing S) {e : Set S} {u v : S}
    (hlink : G.toGraph.IsLink e u v) (hne : u ≠ v) :
    closure e = e ∪ {u, v} := by
  rcases hlink with ⟨he, huV, hvV, hcap⟩
  rcases G.edge_cond e he with ⟨u', v', _, hcap', f, hf0, hf1⟩ | ⟨u', hcap', _⟩
  · have hpair : ({u', v'} : Set S) = {u, v} := hcap'.symm.trans hcap
    have h_ioo_pc : IsPathConnected {t : unitInterval | (t : ℝ) ∈ Ioo (0 : ℝ) 1} := by
      have hconv : Convex ℝ (Ioo (0 : ℝ) 1) := convex_Ioo 0 1
      have hpc0 : IsPathConnected (Ioo (0 : ℝ) 1) :=
        hconv.isPathConnected ⟨1 / 2, by constructor <;> linarith⟩
      let clamp : ℝ → unitInterval := fun x =>
        ⟨max 0 (min 1 x), le_max_left 0 _, max_le zero_le_one (min_le_left 1 x)⟩
      have hclamp_cont : Continuous clamp :=
        (continuous_const.max (continuous_const.min continuous_id)).subtype_mk _
      have himg : clamp '' Ioo (0 : ℝ) 1 = {t : unitInterval | (t : ℝ) ∈ Ioo (0 : ℝ) 1} := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩
          simp only [clamp, mem_ofPred_eq]
          have hmin : min 1 x = x := min_eq_right (le_of_lt hx.2)
          have hmax : max 0 (min 1 x) = x := by rw [hmin]; exact max_eq_right (le_of_lt hx.1)
          rw [hmax]
          exact hx
        · intro ht
          refine ⟨(t : ℝ), ht, Subtype.ext ?_⟩
          simp only [clamp]
          have hmin : min 1 (t : ℝ) = (t : ℝ) := min_eq_right (le_of_lt ht.2)
          rw [hmin]
          exact max_eq_right (le_of_lt ht.1)
      rw [← himg]
      exact hpc0.image hclamp_cont
    let phi : unitInterval → S := fun t => (f t).1
    have hphi_cont : Continuous phi := continuous_subtype_val.comp f.continuous
    have himg_eq : phi '' {t : unitInterval | (t : ℝ) ∈ Ioo (0 : ℝ) 1} = closure e \ G.V := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨(f t).2, ?_⟩
        intro hzV
        have hz_mem : phi t ∈ closure e ∩ G.V := ⟨(f t).2, hzV⟩
        rw [hcap'] at hz_mem
        rcases hz_mem with hzu | hzv
        · have ht0 : t = 0 := f.injective (Subtype.ext (hzu.trans hf0.symm))
          subst ht0
          exact lt_irrefl (0 : ℝ) ht.1
        · have ht1 : t = 1 := f.injective (Subtype.ext (hzv.trans hf1.symm))
          subst ht1
          exact lt_irrefl (1 : ℝ) ht.2
      · rintro ⟨hz_cl, hz_notV⟩
        let t : unitInterval := f.symm ⟨z, hz_cl⟩
        have hft : phi t = z := congrArg Subtype.val (f.apply_symm_apply ⟨z, hz_cl⟩)
        refine ⟨t, ?_, hft⟩
        have ht0 : (t : ℝ) ≠ 0 := by
          intro h0
          have ht_eq : t = 0 := Subtype.ext h0
          have hz_eq : z = u' := by rw [← hft, ht_eq]; exact hf0
          have hu'V : u' ∈ G.V := by
            have : u' ∈ closure e ∩ G.V := by rw [hcap']; exact mem_insert u' {v'}
            exact this.2
          exact hz_notV (hz_eq ▸ hu'V)
        have ht1 : (t : ℝ) ≠ 1 := by
          intro h1
          have ht_eq : t = 1 := Subtype.ext h1
          have hz_eq : z = v' := by rw [← hft, ht_eq]; exact hf1
          have hv'V : v' ∈ G.V := by
            have : v' ∈ closure e ∩ G.V := by rw [hcap']; exact mem_insert_of_mem u' rfl
            exact this.2
          exact hz_notV (hz_eq ▸ hv'V)
        exact ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), lt_of_le_of_ne t.2.2 ht1⟩
    have hpc_diff : IsPathConnected (closure e \ G.V) := by
      rw [← himg_eq]
      exact h_ioo_pc.image hphi_cont
    have hsub_diff : closure e \ G.V ⊆ G.U \ G.V := by
      have hclU : closure e ⊆ G.U := G.isClosed_U.closure_subset_iff.mpr (he.2.1.trans sdiff_subset)
      exact sdiff_subset_sdiff_left hclU
    have he_sub_diff : e ⊆ closure e \ G.V :=
      subset_sdiff.mpr ⟨subset_closure, disjoint_left.mpr fun _ hxe hxV => (he.2.1 hxe).2 hxV⟩
    have hdiff_eq : closure e \ G.V = e :=
      he.2.2.2 (closure e \ G.V) hsub_diff hpc_diff he_sub_diff
    calc closure e
      _ = (closure e \ G.V) ∪ (closure e ∩ G.V) := (sdiff_union_inter (closure e) G.V).symm
      _ = e ∪ {u, v} := by rw [hdiff_eq, hcap]
  · exfalso
    have hpair : ({u, v} : Set S) = {u'} := hcap.symm.trans hcap'
    have hu_eq : u = u' := by
      have : u ∈ ({u, v} : Set S) := mem_insert u {v}
      rw [hpair] at this
      exact mem_singleton_iff.mp this
    have hv_eq : v = u' := by
      have : v ∈ ({u, v} : Set S) := mem_insert_of_mem u rfl
      rw [hpair] at this
      exact mem_singleton_iff.mp this
    exact hne (hu_eq.trans hv_eq.symm)

private theorem closure_edge_diff_V_eq {S : Type*} [TopologicalSpace S]
    (G : Drawing S) {e : Set S} (he : e ∈ G.E) :
    closure e \ G.V = e := by
  rcases G.toGraph.exists_isLink_of_mem_edgeSet he with ⟨u, v, hlink⟩
  by_cases hne : u ≠ v
  · have hcl := closure_edge_eq_union_ends G hlink hne
    have hcap : closure e ∩ G.V = {u, v} := hlink.2.2.2
    ext x
    simp only [mem_sdiff]
    constructor
    · rintro ⟨hx_cl, hx_nV⟩
      rw [hcl] at hx_cl
      rcases hx_cl with hxe | hxe_uv
      · exact hxe
      · exfalso
        have : x ∈ closure e ∩ G.V := by rw [hcap]; exact hxe_uv
        exact hx_nV this.2
    · intro hxe
      exact ⟨subset_closure hxe, fun hxV => (he.2.1 hxe).2 hxV⟩
  · push Not at hne
    subst hne
    rcases G.edge_cond e he with ⟨u', v', huv', hcap', _⟩ | ⟨u', hcap', ⟨f⟩⟩
    · exfalso
      have hpair : ({u', v'} : Set S) = {u, u} := hcap'.symm.trans hlink.2.2.2
      rw [pair_eq_singleton] at hpair
      have hu' : u' = u := by
        have : u' ∈ ({u', v'} : Set S) := mem_insert u' {v'}
        rwa [hpair, mem_singleton_iff] at this
      have hv' : v' = u := by
        have : v' ∈ ({u', v'} : Set S) := mem_insert_of_mem u' rfl
        rwa [hpair, mem_singleton_iff] at this
      exact huv' (hu'.trans hv'.symm)
    · have hu'_cl : u' ∈ closure e := by
        have : u' ∈ closure e ∩ G.V := by rw [hcap']; exact mem_singleton u'
        exact this.1
      let v₀ : Circle := f.symm ⟨u', hu'_cl⟩
      have hfv₀ : (f v₀).1 = u' := congrArg Subtype.val (f.apply_symm_apply ⟨u', hu'_cl⟩)
      obtain ⟨g⟩ := nonempty_homeomorph_Ioo_nextSegment (finite_singleton v₀) (mem_singleton v₀)
      have hconv : Convex ℝ (Ioo (0 : ℝ) 1) := convex_Ioo 0 1
      have hpc_ioo : IsPathConnected (Ioo (0 : ℝ) 1) :=
        hconv.isPathConnected ⟨1 / 2, by constructor <;> linarith⟩
      let psi : Ioo (0 : ℝ) 1 → S := fun t => (f (g t).1).1
      have hpsi_cont : Continuous psi :=
        continuous_subtype_val.comp (f.continuous.comp (continuous_subtype_val.comp g.continuous))
      have himg_eq : range psi = closure e \ G.V := by
        ext z
        simp only [mem_range, mem_sdiff, psi]
        constructor
        · rintro ⟨t, rfl⟩
          refine ⟨(f (g t).1).2, fun hzV => ?_⟩
          have hz_in : (f (g t).1).1 ∈ closure e ∩ G.V := ⟨(f (g t).1).2, hzV⟩
          rw [hcap', mem_singleton_iff] at hz_in
          have heq : (g t).1 = v₀ :=
            f.injective (Subtype.ext (hz_in.trans hfv₀.symm))
          exact (g t).2.1 heq
        · rintro ⟨hz_cl, hz_nV⟩
          let w : Circle := f.symm ⟨z, hz_cl⟩
          have hfw : (f w).1 = z := congrArg Subtype.val (f.apply_symm_apply ⟨z, hz_cl⟩)
          have hw_seg : w ∈ nextSegment {v₀} v₀ := by
            refine ⟨fun hwv₀ => ?_, fun y hy => by simp at hy⟩
            have hzu' : z = u' := by rw [← hfw, hwv₀, hfv₀]
            have hu'V : u' ∈ G.V := by
              have : u' ∈ closure e ∩ G.V := by rw [hcap']; exact mem_singleton u'
              exact this.2
            exact hz_nV (hzu' ▸ hu'V)
          refine ⟨g.symm ⟨w, hw_seg⟩, ?_⟩
          have hg : (g (g.symm ⟨w, hw_seg⟩)).1 = w :=
            congrArg Subtype.val (g.apply_symm_apply ⟨w, hw_seg⟩)
          rw [hg, hfw]
      have hpc_diff : IsPathConnected (closure e \ G.V) := by
        have : PathConnectedSpace (Ioo (0 : ℝ) 1) :=
          isPathConnected_iff_pathConnectedSpace.mp hpc_ioo
        rw [← himg_eq, ← image_univ]
        exact isPathConnected_univ.image hpsi_cont
      have hsub_diff : closure e \ G.V ⊆ G.U \ G.V := by
        have hclU : closure e ⊆ G.U := G.isClosed_U.closure_subset_iff.mpr (he.2.1.trans sdiff_subset)
        exact sdiff_subset_sdiff_left hclU
      have he_sub_diff : e ⊆ closure e \ G.V :=
        subset_sdiff.mpr ⟨subset_closure, disjoint_left.mpr fun _ hxe hxV => (he.2.1 hxe).2 hxV⟩
      exact he.2.2.2 (closure e \ G.V) hsub_diff hpc_diff he_sub_diff

private theorem mem_vertexSet_or_of_closure_edge_inter_subgraphU_nonempty {S : Type*}
    [TopologicalSpace S] {G H : Graph α β'} (Γ : GraphDrawing G S) (hHG : H ≤ G)
    {e : β'} {u w : α} (hl : G.IsLink e u w)
    (hne : (closure (graphDrawingEdgeSet Γ e) ∩ graphDrawingSubgraphU Γ H).Nonempty) :
    u ∈ V(H) ∨ w ∈ V(H) := by
  obtain ⟨x, hx_cl, hx_H⟩ := hne
  have heG : e ∈ E(G) := hl.edge_mem
  have huG : u ∈ V(G) := hl.left_mem
  have hwG : w ∈ V(G) := hl.right_mem
  have hlink_to := (Γ.iso.isLink_iff ⟨e, heG⟩ ⟨u, huG⟩ ⟨w, hwG⟩).mp hl
  by_cases hxV : x ∈ Γ.drawing.V
  · have hx_inter : x ∈ closure (Γ.iso.edgeEquiv ⟨e, heG⟩).1 ∩ Γ.drawing.V := by
      rw [← graphDrawingEdgeSet_eq Γ heG]
      exact ⟨hx_cl, hxV⟩
    rw [hlink_to.2.2.2] at hx_inter
    rcases hx_inter with hxu | hxw
    · left
      refine mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hHG huG ?_
      rw [graphDrawingVertexSet_eq_singleton Γ huG, ← hxu, singleton_subset_iff]
      exact hx_H
    · right
      rw [mem_singleton_iff] at hxw
      refine mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hHG hwG ?_
      rw [graphDrawingVertexSet_eq_singleton Γ hwG, ← hxw, singleton_subset_iff]
      exact hx_H
  · have hxe : x ∈ (Γ.iso.edgeEquiv ⟨e, heG⟩).1 := by
      rw [graphDrawingEdgeSet_eq Γ heG] at hx_cl
      rw [← closure_edge_diff_V_eq Γ.drawing (Γ.iso.edgeEquiv ⟨e, heG⟩).2]
      exact ⟨hx_cl, hxV⟩
    rcases hx_H with hx_vert | hx_edge
    · obtain ⟨v, hvH, hxv⟩ := mem_iUnion₂.mp hx_vert
      have hvG : v ∈ V(G) := hHG.vertexSet_mono hvH
      rw [graphDrawingVertexSet_eq_singleton Γ hvG, mem_singleton_iff] at hxv
      exact (hxV (hxv ▸ (Γ.iso.vertexEquiv ⟨v, hvG⟩).2)).elim
    · obtain ⟨f, hfH, hxf⟩ := mem_iUnion₂.mp hx_edge
      have hfG : f ∈ E(G) := hHG.edgeSet_mono hfH
      have hxf' : x ∈ (Γ.iso.edgeEquiv ⟨f, hfG⟩).1 := by
        rw [graphDrawingEdgeSet_eq Γ hfG] at hxf
        rw [← closure_edge_diff_V_eq Γ.drawing (Γ.iso.edgeEquiv ⟨f, hfG⟩).2]
        exact ⟨hxf, hxV⟩
      have heq_set : (Γ.iso.edgeEquiv ⟨e, heG⟩).1 = (Γ.iso.edgeEquiv ⟨f, hfG⟩).1 := by
        by_contra hne_set
        exact disjoint_left.mp
          (disjoint_edges_of_ne Γ.drawing (Γ.iso.edgeEquiv ⟨e, heG⟩).2
            (Γ.iso.edgeEquiv ⟨f, hfG⟩).2 hne_set) hxe hxf'
      have hef : e = f :=
        congrArg Subtype.val (Γ.iso.edgeEquiv.injective (Subtype.ext heq_set))
      have heH : e ∈ E(H) := hef ▸ hfH
      obtain ⟨a, b, habH⟩ := H.exists_isLink_of_mem_edgeSet heH
      rcases hl.left_eq_or_eq (habH.mono hHG) with rfl | rfl
      · exact Or.inl habH.left_mem
      · exact Or.inl habH.right_mem

private theorem angleDiff_exp_of_lt {t₁ t₂ : ℝ} (h12 : t₁ < t₂) (h2pi : t₂ < t₁ + 2 * Real.pi) :
    (Circle.exp t₁).angleDiff (Circle.exp t₂) = t₂ - t₁ := by
  have hmul : Circle.exp (t₂ - t₁) * Circle.exp t₁ = Circle.exp t₂ := by
    rw [← Circle.exp_add, sub_add_cancel]
  rw [← hmul]
  exact angleDiff_exp_mul (sub_pos.mpr h12) (sub_lt_iff_lt_add'.mpr h2pi)

private theorem pairsCrossOn_of_crosses {S : Type*} [TopologicalSpace S]
    {G : Graph α β'} {Γ : GraphDrawing G S} {Ω : CyclicPerm α} {C : Set S}
    {φ : Circle ≃ₜ C} (hagree : DrawingAgreesWithOArcHomeo Γ Ω C φ)
    {v₁ v₃ v₂ v₄ : α} (hcr : Ω.Crosses v₁ v₃ v₂ v₄)
    {p₁ p₃ p₂ p₄ : S}
    (hp₁ : p₁ ∈ graphDrawingVertexSet Γ v₁)
    (hp₃ : p₃ ∈ graphDrawingVertexSet Γ v₃)
    (hp₂ : p₂ ∈ graphDrawingVertexSet Γ v₂)
    (hp₄ : p₄ ∈ graphDrawingVertexSet Γ v₄) :
    PairsCrossOn C p₁ p₃ p₂ p₄ := by
  have hpt : ∀ {v : α} {p q : S}, p ∈ graphDrawingVertexSet Γ v → q ∈ graphDrawingVertexSet Γ v → p = q :=
    fun h h' => h.2.symm.trans h'.2
  have hinj : ∀ {u w : α} {p : S}, p ∈ graphDrawingVertexSet Γ u → p ∈ graphDrawingVertexSet Γ w → u = w :=
    fun h h' => graphDrawingVertexSet_inj Γ h h'
  have hang : ∀ {a b c : α}, Ω.IsClockwise3 a b c → ∀ {za zb zc : Circle},
      (φ za).1 ∈ graphDrawingVertexSet Γ a →
      (φ zb).1 ∈ graphDrawingVertexSet Γ b →
      (φ zc).1 ∈ graphDrawingVertexSet Γ c →
      za.angleDiff zb < za.angleDiff zc := by
    intro a b c hclw za zb zc hza hzb hzc
    obtain ⟨t₁, t₂, t₃, ht12, ht23, ht31, hφ₁, hφ₂, hφ₃⟩ := hagree.2 a b c hclw
    have heq₁ : za = Circle.exp t₁ := φ.injective (Subtype.ext (hpt hza hφ₁))
    have heq₂ : zb = Circle.exp t₂ := φ.injective (Subtype.ext (hpt hzb hφ₂))
    have heq₃ : zc = Circle.exp t₃ := φ.injective (Subtype.ext (hpt hzc hφ₃))
    subst heq₁ heq₂ heq₃
    rw [angleDiff_exp_of_lt ht12 (ht23.trans ht31),
        angleDiff_exp_of_lt (ht12.trans ht23) ht31]
    linarith
  have hcr_int := Ω.crosses_iff_interval.mp hcr
  have hv₁ : v₁ ∈ Ω.bar := by
    rcases hcr_int with ⟨h123, _⟩ | ⟨h143, _⟩
    · exact (Ω.isClockwise3_iff.mp h123.2).2.2.2.1
    · exact (Ω.isClockwise3_iff.mp h143.2).2.2.2.1
  have hv₃ : v₃ ∈ Ω.bar := by
    rcases hcr_int with ⟨h123, _⟩ | ⟨h143, _⟩
    · exact (Ω.isClockwise3_iff.mp h123.2).2.2.2.2.2.1
    · exact (Ω.isClockwise3_iff.mp h143.2).2.2.2.2.2.1
  have hv₂ : v₂ ∈ Ω.bar := by
    rcases hcr_int with ⟨h123, _⟩ | ⟨_, h321⟩
    · exact h123.1.1
    · exact h321.1.1
  have hv₄ : v₄ ∈ Ω.bar := by
    rcases hcr_int with ⟨_, h341⟩ | ⟨h143, _⟩
    · exact h341.1.1
    · exact h143.1.1
  have hp₁C : p₁ ∈ C := hagree.1 v₁ hv₁ hp₁
  have hp₃C : p₃ ∈ C := hagree.1 v₃ hv₃ hp₃
  have hp₂C : p₂ ∈ C := hagree.1 v₂ hv₂ hp₂
  have hp₄C : p₄ ∈ C := hagree.1 v₄ hv₄ hp₄
  let z₁ : Circle := φ.symm ⟨p₁, hp₁C⟩
  let z₃ : Circle := φ.symm ⟨p₃, hp₃C⟩
  let z₂ : Circle := φ.symm ⟨p₂, hp₂C⟩
  let z₄ : Circle := φ.symm ⟨p₄, hp₄C⟩
  have hz₁_val : (φ z₁).1 = p₁ := by simp [z₁]
  have hz₃_val : (φ z₃).1 = p₃ := by simp [z₃]
  have hz₂_val : (φ z₂).1 = p₂ := by simp [z₂]
  have hz₄_val : (φ z₄).1 = p₄ := by simp [z₄]
  have hz₁ : (φ z₁).1 ∈ graphDrawingVertexSet Γ v₁ := by rw [hz₁_val]; exact hp₁
  have hz₃ : (φ z₃).1 ∈ graphDrawingVertexSet Γ v₃ := by rw [hz₃_val]; exact hp₃
  have hz₂ : (φ z₂).1 ∈ graphDrawingVertexSet Γ v₂ := by rw [hz₂_val]; exact hp₂
  have hz₄ : (φ z₄).1 ∈ graphDrawingVertexSet Γ v₄ := by rw [hz₄_val]; exact hp₄
  have hcr_circle : CrossesOn (Set.univ : Set Circle) z₁ z₃ z₂ z₄ := by
    rw [crossesOn_univ_iff_angleDiff]
    have hz_ne : ∀ {u w : α} {zu zw : Circle} {pu pw : S},
        u ≠ w → pu ∈ graphDrawingVertexSet Γ u → pw ∈ graphDrawingVertexSet Γ w →
        (φ zu).1 = pu → (φ zw).1 = pw → zu ≠ zw := by
      intro u w zu zw pu pw huw hpu hpw hzu hzw h
      have hp : pu = pw := hzu.symm.trans ((congrArg Subtype.val (congrArg φ h)).trans hzw)
      exact huw (hinj hpu (hp ▸ hpw))
    rcases hcr_int with h1234 | h1432
    · have h123 : Ω.IsClockwise3 v₁ v₂ v₃ := h1234.1.2
      have h341 : Ω.IsClockwise3 v₃ v₄ v₁ := h1234.2.2
      have h134 : Ω.IsClockwise3 v₁ v₃ v₄ := Ω.isClockwise3_rotate (Ω.isClockwise3_rotate h341)
      have h234 : Ω.IsClockwise3 v₂ v₃ v₄ :=
        (Ω.isClockwise4_iff_interval.mp (Ω.isClockwise4_rotate
          (Ω.isClockwise4_iff_interval.mpr h1234))).1.2
      have h123_def := Ω.isClockwise3_iff.mp h123
      have h341_def := Ω.isClockwise3_iff.mp h341
      have h234_def := Ω.isClockwise3_iff.mp h234
      refine ⟨hz_ne h123_def.2.1 hp₁ hp₃ hz₁_val hz₃_val,
              hz_ne h234_def.2.1 hp₂ hp₄ hz₂_val hz₄_val,
              hz_ne h123_def.1 hp₁ hp₂ hz₁_val hz₂_val,
              hz_ne h341_def.2.2.1.symm hp₁ hp₄ hz₁_val hz₄_val,
              hz_ne h123_def.2.2.1.symm hp₃ hp₂ hz₃_val hz₂_val,
              hz_ne h341_def.1 hp₃ hp₄ hz₃_val hz₄_val, ?_⟩
      have hlt₁ := hang h123 hz₁ hz₂ hz₃
      have hlt₂ := hang h134 hz₁ hz₃ hz₄
      exact ⟨fun _ => not_lt.mpr hlt₂.le, fun _ => hlt₁⟩
    · have h143 : Ω.IsClockwise3 v₁ v₄ v₃ := h1432.1.2
      have h321 : Ω.IsClockwise3 v₃ v₂ v₁ := h1432.2.2
      have h132 : Ω.IsClockwise3 v₁ v₃ v₂ := Ω.isClockwise3_rotate (Ω.isClockwise3_rotate h321)
      have h432 : Ω.IsClockwise3 v₄ v₃ v₂ :=
        (Ω.isClockwise4_iff_interval.mp (Ω.isClockwise4_rotate
          (Ω.isClockwise4_iff_interval.mpr h1432))).1.2
      have h143_def := Ω.isClockwise3_iff.mp h143
      have h321_def := Ω.isClockwise3_iff.mp h321
      have h432_def := Ω.isClockwise3_iff.mp h432
      refine ⟨hz_ne h143_def.2.1 hp₁ hp₃ hz₁_val hz₃_val,
              hz_ne h432_def.2.1.symm hp₂ hp₄ hz₂_val hz₄_val,
              hz_ne h321_def.2.2.1.symm hp₁ hp₂ hz₁_val hz₂_val,
              hz_ne h143_def.1 hp₁ hp₄ hz₁_val hz₄_val,
              hz_ne h321_def.1 hp₃ hp₂ hz₃_val hz₂_val,
              hz_ne h143_def.2.2.1.symm hp₃ hp₄ hz₃_val hz₄_val, ?_⟩
      have hlt₁ := hang h143 hz₁ hz₄ hz₃
      have hlt₂ := hang h132 hz₁ hz₃ hz₂
      exact ⟨fun h => (hlt₂.not_gt h).elim, fun h => (h hlt₁).elim⟩
  have hcr_C : CrossesOn C (oArcMap φ z₁) (oArcMap φ z₃)
      (oArcMap φ z₂) (oArcMap φ z₄) :=
    (crossesOn_oArcMap_iff φ).mpr hcr_circle
  have ho₁ : oArcMap φ z₁ = p₁ := by simp [oArcMap, z₁]
  have ho₃ : oArcMap φ z₃ = p₃ := by simp [oArcMap, z₃]
  have ho₂ : oArcMap φ z₂ = p₂ := by simp [oArcMap, z₂]
  have ho₄ : oArcMap φ z₄ = p₄ := by simp [oArcMap, z₄]
  rw [ho₁, ho₃, ho₂, ho₄] at hcr_C
  exact hcr_C

private theorem isConnected_walkDrawingU {S : Type*} [TopologicalSpace S]
    {G : Graph α β'} (Γ : GraphDrawing G S) {u v : α} (W : GraphWalk G u v) :
    IsConnected ((⋃ w ∈ W.support, graphDrawingVertexSet Γ w) ∪
      (⋃ e ∈ W.edges, closure (graphDrawingEdgeSet Γ e))) := by
  induction W with
  | @nil x hx =>
    have heq : (⋃ w ∈ (GraphWalk.nil hx).support, graphDrawingVertexSet Γ w) ∪
        (⋃ e ∈ (GraphWalk.nil hx).edges, closure (graphDrawingEdgeSet Γ e)) =
        {(Γ.iso.vertexEquiv ⟨x, hx⟩).1} := by
      simp [GraphWalk.support, GraphWalk.edges, graphDrawingVertexSet_eq_singleton Γ hx]
    rw [heq]
    exact isConnected_singleton
  | @cons x z y e hl rest ih =>
    let E_cl := closure (graphDrawingEdgeSet Γ e)
    let R_U := (⋃ w ∈ rest.support, graphDrawingVertexSet Γ w) ∪
      (⋃ f ∈ rest.edges, closure (graphDrawingEdgeSet Γ f))
    have heq : (⋃ w ∈ (GraphWalk.cons hl rest).support, graphDrawingVertexSet Γ w) ∪
        (⋃ f ∈ (GraphWalk.cons hl rest).edges, closure (graphDrawingEdgeSet Γ f)) =
        E_cl ∪ R_U := by
      ext pt
      simp only [GraphWalk.support, GraphWalk.edges, List.mem_cons, mem_union, mem_iUnion,
        exists_prop, E_cl, R_U]
      constructor
      · rintro (⟨w, rfl | hw, hpt⟩ | ⟨f, rfl | hf, hpt⟩)
        · exact Or.inl (graphDrawingVertexSet_subset_closure_edge Γ hl hpt)
        · exact Or.inr (Or.inl ⟨w, hw, hpt⟩)
        · exact Or.inl hpt
        · exact Or.inr (Or.inr ⟨f, hf, hpt⟩)
      · rintro (hpt | ⟨w, hw, hpt⟩ | ⟨f, hf, hpt⟩)
        · exact Or.inr ⟨e, Or.inl rfl, hpt⟩
        · exact Or.inl ⟨w, Or.inr hw, hpt⟩
        · exact Or.inr ⟨f, Or.inr hf, hpt⟩
    rw [heq]
    have hE_conn : IsConnected E_cl := by
      dsimp [E_cl]
      rw [graphDrawingEdgeSet_eq Γ hl.edge_mem]
      exact isConnected_closure_edge Γ.drawing (Γ.iso.edgeEquiv ⟨e, hl.edge_mem⟩).2
    obtain ⟨pz, hpz⟩ := graphDrawingVertexSet_nonempty Γ hl.right_mem
    have hpz_E : pz ∈ E_cl := graphDrawingVertexSet_subset_closure_edge Γ hl.symm hpz
    have hpz_R : pz ∈ R_U :=
      Or.inl (mem_iUnion₂.mpr ⟨z, rest.start_mem_support, hpz⟩)
    exact ⟨⟨pz, Or.inl hpz_E⟩, hE_conn.isPreconnected.union pz hpz_E hpz_R ih.isPreconnected⟩

private theorem isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {G : Graph α β'} {Γ : GraphDrawing G S} {P : Graph α β'} {u v : α} {D : Set S}
    (hD : IsClosedDisc D) (hP : IsGraphPathWithEnds G P u v)
    (hU : graphDrawingSubgraphU Γ P ⊆ D) :
    IsCompact (graphDrawingSubgraphU Γ P) ∧ IsConnected (graphDrawingSubgraphU Γ P) ∧
    (∃ p_u ∈ graphDrawingVertexSet Γ u, p_u ∈ graphDrawingSubgraphU Γ P) ∧
    (∃ p_v ∈ graphDrawingVertexSet Γ v, p_v ∈ graphDrawingSubgraphU Γ P) := by
  have huG : u ∈ V(G) := hP.le.vertexSet_mono hP.left_mem
  have hvG : v ∈ V(G) := hP.le.vertexSet_mono hP.right_mem
  obtain ⟨p_u, hp_u⟩ := graphDrawingVertexSet_nonempty Γ huG
  obtain ⟨p_v, hp_v⟩ := graphDrawingVertexSet_nonempty Γ hvG
  have hp_uU : p_u ∈ graphDrawingSubgraphU Γ P :=
    graphDrawingVertexSet_subset_subgraphU_of_mem Γ hP.left_mem hp_u
  have hp_vU : p_v ∈ graphDrawingSubgraphU Γ P :=
    graphDrawingVertexSet_subset_subgraphU_of_mem Γ hP.right_mem hp_v
  obtain ⟨hP_le, W, _, hVP, hEP⟩ := hP
  obtain ⟨W_G, hs_G, he_G⟩ := exists_walk_up_of_le hP_le W
  have hU_eq : graphDrawingSubgraphU Γ P =
      (⋃ w ∈ W_G.support, graphDrawingVertexSet Γ w) ∪
      (⋃ e ∈ W_G.edges, closure (graphDrawingEdgeSet Γ e)) := by
    simp only [graphDrawingSubgraphU, hs_G, he_G, hVP, hEP, mem_ofPred_eq]
  have hconn : IsConnected (graphDrawingSubgraphU Γ P) := by
    rw [hU_eq]
    exact isConnected_walkDrawingU Γ W_G
  have hclosed : IsClosed (graphDrawingSubgraphU Γ P) := by
    rw [hU_eq]
    refine IsClosed.union ?_ ?_
    · refine W_G.support.finite_toSet.isClosed_biUnion fun w hw => ?_
      have hwG : w ∈ V(G) := W_G.mem_vertexSet_of_mem_support hw
      rw [graphDrawingVertexSet_eq_singleton Γ hwG]
      exact isClosed_singleton
    · exact W_G.edges.finite_toSet.isClosed_biUnion fun e _ => isClosed_closure
  have hcomp : IsCompact (graphDrawingSubgraphU Γ P) :=
    (isCompact_of_isClosedDisc hD).of_isClosed_subset hclosed hU
  exact ⟨hcomp, hconn, ⟨p_u, hp_u, hp_uU⟩, ⟨p_v, hp_v, hp_vU⟩⟩

private theorem graphDrawingSubgraphU_subset_U' {S : Type*} [TopologicalSpace S]
    {G : Graph α β'} (Γ : GraphDrawing G S) (P : Graph α β') :
    graphDrawingSubgraphU Γ P ⊆ Γ.drawing.U := by
  refine union_subset (iUnion₂_subset fun v _ x hx => ?_) (iUnion₂_subset fun e _ => ?_)
  · rcases hx with ⟨hvG, rfl⟩
    exact Γ.drawing.V_subset_U (Γ.iso.vertexEquiv ⟨v, hvG⟩).2
  · by_cases heG : e ∈ E(G)
    · rw [graphDrawingEdgeSet_eq Γ heG]
      exact Γ.drawing.isClosed_U.closure_subset_iff.mpr
        (((Γ.iso.edgeEquiv ⟨e, heG⟩).2.2.1).trans sdiff_subset)
    · have hemp : graphDrawingEdgeSet Γ e = ∅ := by
        ext x; simp [graphDrawingEdgeSet, heG]
      rw [hemp, closure_empty]
      exact empty_subset _

/-- Every rural society has no cross. -/
theorem not_hasCross_of_isRuralSociety (S : Society α β') (hrural : S.IsRuralSociety) :
    ¬ HasCross S := by
  rintro ⟨P₁, P₂, hdisj, v₁, v₃, v₂, v₄, hP₁, hP₂, hcr⟩
  obtain ⟨Ω₀, h₀, _, ⟨Γ, Δ, Δ₀, hΔ, _, hU_sub, _, _, ⟨φ, hφ⟩, _⟩⟩ := hrural
  have hU₁ : graphDrawingSubgraphU Γ P₁ ⊆ Δ :=
    (graphDrawingSubgraphU_subset_U' Γ P₁).trans (hU_sub.trans sdiff_subset)
  have hU₂ : graphDrawingSubgraphU Γ P₂ ⊆ Δ :=
    (graphDrawingSubgraphU_subset_U' Γ P₂).trans (hU_sub.trans sdiff_subset)
  obtain ⟨hcomp₁, hconn₁, ⟨p₁, hp₁, hp₁U⟩, ⟨p₃, hp₃, hp₃U⟩⟩ :=
    isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hP₁.1 hU₁
  obtain ⟨hcomp₂, hconn₂, ⟨p₂, hp₂, hp₂U⟩, ⟨p₄, hp₄, hp₄U⟩⟩ :=
    isCompact_and_isConnected_subgraphU_of_isGraphPathWithEnds hΔ hP₂.1 hU₂
  have hcr_bd : PairsCrossOn (discBd Δ) p₁ p₃ p₂ p₄ := by
    rw [(subBd_eq_discBd_plane hΔ).symm]
    exact pairsCrossOn_of_crosses hφ.2 hcr hp₁ hp₃ hp₂ hp₄
  have hU_inter : (graphDrawingSubgraphU Γ P₁ ∩ graphDrawingSubgraphU Γ P₂).Nonempty :=
    disc_crossing Δ (graphDrawingSubgraphU Γ P₁) (graphDrawingSubgraphU Γ P₂)
      p₁ p₃ p₂ p₄ hΔ hU₁ hU₂ hcomp₁ hcomp₂ hconn₁ hconn₂ hp₁U hp₃U hp₂U hp₄U hcr_bd
  obtain ⟨x, hx₁, hx₂⟩ := hU_inter
  rcases hx₁ with hx_vert | hx_edge
  · obtain ⟨v, hv₁, hxv⟩ := mem_iUnion₂.mp hx_vert
    have hvG : v ∈ V(S.G) := hP₁.1.le.vertexSet_mono hv₁
    have hsub : graphDrawingVertexSet Γ v ⊆ graphDrawingSubgraphU Γ P₂ := by
      rw [graphDrawingVertexSet_eq_singleton Γ hvG, hxv.2, singleton_subset_iff]
      exact hx₂
    exact disjoint_left.mp hdisj hv₁
      (mem_vertexSet_of_graphDrawingVertexSet_subset_subgraphU Γ hP₂.1.le hvG hsub)
  · obtain ⟨e, he₁, hxe⟩ := mem_iUnion₂.mp hx_edge
    obtain ⟨u, w, hl₁⟩ := P₁.exists_isLink_of_mem_edgeSet he₁
    rcases mem_vertexSet_or_of_closure_edge_inter_subgraphU_nonempty Γ hP₂.1.le (hl₁.mono hP₁.1.le)
        ⟨x, hxe, hx₂⟩ with hu₂ | hw₂
    · exact disjoint_left.mp hdisj hl₁.left_mem hu₂
    · exact disjoint_left.mp hdisj hl₁.right_mem hw₂

/-- **Graph Minors XIII, (8.5)** (Section 8, page 95):
“(8.5) *Let $C$ be a 4-linked core of $(G, \Omega)$. Then $(G, \Omega)$ has no cross if and only if
$(C, \Omega)$ is rural.*” -/
theorem theorem_8_5_proof {S : Society α β} {C : Graph α β'} (hC : IsFourLinkedCore S C) :
    ¬ HasCross S ↔ (coreSociety S C hC.isCore).IsRuralSociety := by
  rw [theorem_8_4_proof hC.isCore]
  let CS := coreSociety S C hC.isCore
  have hconn4 : CS.IsKConnected 4 := isFourConnected_coreSociety hC
  constructor
  · intro hnocross
    have hconn3 : CS.IsKConnected 3 := fun k' hk' => hconn4 k' (by omega)
    have hnotripod : ¬ ∃ T₁ T₂ T₃ : Graph α β', CS.IsTripod T₁ T₂ T₃ := by
      rintro ⟨T₁, T₂, T₃, htripod⟩
      rcases GraphMinor.GM09.theorem_2_3_proof CS htripod with hcr | ⟨G₁, G₂, hint, _⟩
      · exact hnocross hcr
      · exact hconn4 3 (by omega) G₁ G₂ hint.1
    exact GraphMinor.GM09.theorem_2_4_proof CS hconn3 hnocross hnotripod
  · exact not_hasCross_of_isRuralSociety CS

end GraphMinor.GM13
