module

public import GraphMinor.GM21.Cited
public import GraphMinor.GM21.Parallel
public import GraphMinor.GM14.Defs
public import GraphMinor.GM16.Section7
public import GraphMinor.GM17.Subdivide
public import GraphMinor.GM19.Defs2
import GraphMinor.GM09.Basic
import GraphMinor.GM12.Section4BranchUnions
import GraphMinor.GM21.Section10

/-!
# Graph Minors XXI: Main Theorem (1.1)

This file formalizes the main theorem **(1.1)** of N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616 (Section 1, page 1 of the preprint):
- `GM21Theorem11Statement` and `theorem_1_1`: for every integer `p ≥ 0` there exists `w ≥ 0` such
  that every finite graph `G : Graph α β` with a vital `p`-linkage has tree-width at most `w`.

The `Graph`-level definitions `IsLinkage`, `IsTerminal`, `terminals`, `IsPLinkage`,
`linkagePattern`, `IsVitalLinkage`, `IsVitalPLinkage`, `IsGraphTreeDecomposition`,
`graphTreeDecompWidthPlusOne`, `graphTreeDecompWidth`, `graphTreeWidthPlusOne`, `graphTreeWidth`,
and `TreeWidthLE` match those of Graph Minors XXII (`GraphMinor/GM22/Defs.lean`).

Proved from **(10.4)** (`theorem_10_4`) and **(3.1)** (`theorem_3_1`), via the equivalence between
`Graph`-level and `Hypergraph`-level vital `p`-linkages and tree-decompositions
(`Hypergraph.ofGraph` and `GM17.toGraph`).
-/

@[expose] public section

namespace GraphMinor.GM21

open Set Function Topology
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM14

universe u v w

namespace Final

/-! ## 1. `Graph`-level definitions of linkages and tree-width (matching `GM22`) -/

/-- A *linkage* in a graph $G$ is a subgraph of $G$, every component of which is a path.
Graph Minors XXI, Section 1 (page 1 of the preprint); Graph Minors XXII, Section 1 (page 530). -/
def IsLinkage {α : Type u} {β : Type v} (G L : Graph α β) : Prop :=
  L ≤ G ∧ ∀ P ∈ graphComponents L, IsGraphPath L P

/-- A vertex $v \in V(G)$ is a *terminal* of a linkage $L$ if $v \in V(L)$ and $v$ has degree at
most one in $L$.
Graph Minors XXI, Section 1 (page 1 of the preprint); Graph Minors XXII, Section 1 (page 530). -/
def IsTerminal {α : Type u} {β : Type v} (L : Graph α β) (v : α) : Prop :=
  v ∈ V(L) ∧ vertexValency L v ≤ 1

/-- The set of all terminals of a linkage $L$.
Graph Minors XXI, Section 1 (page 1 of the preprint); Graph Minors XXII, Section 1 (page 530). -/
def terminals {α : Type u} {β : Type v} (L : Graph α β) : Set α :=
  {v ∈ V(L) | vertexValency L v ≤ 1}

/-- A linkage $L$ in $G$ is a *$p$-linkage* if it has at most $p$ terminals.
Graph Minors XXI, Section 1 (page 1 of the preprint); Graph Minors XXII, Section 1 (page 530). -/
def IsPLinkage {α : Type u} {β : Type v} (G L : Graph α β) (p : ℕ) : Prop :=
  IsLinkage G L ∧ (terminals L).ncard ≤ p

/-- The *pattern* of a linkage $L$ is the partition of its set of terminals determined by the
components of $L$.
Graph Minors XXI, Section 1 (page 1 of the preprint); Graph Minors XXII, Section 1 (pages 530–531).
-/
def linkagePattern {α : Type u} {β : Type v} (L : Graph α β) : Set (Set α) :=
  {B : Set α | B.Nonempty ∧ ∃ P ∈ graphComponents L, B = V(P) ∩ terminals L}

/-- A linkage $L$ in $G$ is *vital* if $V(L) = V(G)$ and there is no linkage $L' \ne L$ in $G$ with
the same pattern as $L$.
Graph Minors XXI, Section 1 (page 1 of the preprint); Graph Minors XXII, Section 1 (page 531). -/
def IsVitalLinkage {α : Type u} {β : Type v} (G L : Graph α β) : Prop :=
  IsLinkage G L ∧ V(L) = V(G) ∧
    ∀ L' : Graph α β, IsLinkage G L' → linkagePattern L' = linkagePattern L → L' = L

/-- A linkage $L$ in $G$ is a *vital $p$-linkage* if it is both a $p$-linkage and vital in $G$.
Graph Minors XXI, Section 1 (page 1 of the preprint); Graph Minors XXII, Section 1 (pages 530–531).
-/
def IsVitalPLinkage {α : Type u} {β : Type v} (G L : Graph α β) (p : ℕ) : Prop :=
  IsPLinkage G L p ∧ IsVitalLinkage G L

/-- A *tree-decomposition* of a graph $G$ is a pair $(T, W)$, where $T$ is a tree and
$W = (W_t : t \in V(T))$ is a family of subgraphs of $G$ satisfying conditions 1 and 2.
Graph Minors XXII, Section 1 (page 531). -/
structure IsGraphTreeDecomposition {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    (G : Graph α β) (T : SimpleGraph ι) (W : ι → Graph α β) : Prop where
  /-- $T$ is a tree. -/
  isTree : T.IsTree
  /-- Each $W_t$ is a subgraph of $G$. -/
  le : ∀ t : ι, W t ≤ G
  /-- 1. $\bigcup(W_t : t \in V(T)) = G$. -/
  sUnion_eq : subgraphSUnion G (Set.range W) = G
  /-- 2. If $t'$ lies on the path of $T$ between $t$ and $t''$ then
  $W_t \cap W_{t''} \subseteq W_{t'}$. -/
  inter_le : ∀ ⦃t t' t'' : ι⦄, OnTreePath T t t'' t' → subgraphInter G (W t) (W t'') ≤ W t'

/-- One plus the width of a graph tree-decomposition $(T, W)$: $\max_{t \in V(T)} |V(W_t)|$.
Graph Minors XXII, Section 1 (page 531). -/
noncomputable def graphTreeDecompWidthPlusOne {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    (W : ι → Graph α β) : ℕ :=
  sSup (Set.range fun t : ι ↦ V(W t).ncard)

/-- The *width* $\max (|V(W_t)| - 1 : t \in V(T))$ of a tree-decomposition $(T, W)$ of $G$.
Graph Minors XXII, Section 1 (page 531). -/
noncomputable def graphTreeDecompWidth {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    (W : ι → Graph α β) : ℤ :=
  (graphTreeDecompWidthPlusOne W : ℤ) - 1

/-- One plus the *tree-width* of a graph $G$, as a natural number.
Graph Minors XXII, Section 1 (page 531). -/
noncomputable def graphTreeWidthPlusOne {α : Type u} {β : Type v} (G : Graph α β) : ℕ :=
  sInf {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (W : ι → Graph α β),
    IsGraphTreeDecomposition G T W ∧ graphTreeDecompWidthPlusOne W = w}

/-- The *tree-width* of a graph $G$, as an integer ($\ge -1$).
Graph Minors XXII, Section 1 (page 531). -/
noncomputable def graphTreeWidth {α : Type u} {β : Type v} (G : Graph α β) : ℤ :=
  (graphTreeWidthPlusOne G : ℤ) - 1

/-- A graph $G$ has *tree-width $\le w$* if it admits a tree-decomposition $(T, W)$ of width at
most $w$, that is, with $|V(W_t)| \le w + 1$ for every $t \in V(T)$.
Graph Minors XXII, Section 1 (page 531). -/
def TreeWidthLE {α : Type u} {β : Type v} (G : Graph α β) (w : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (W : ι → Graph α β),
    IsGraphTreeDecomposition G T W ∧ ∀ t : ι, V(W t).ncard ≤ w + 1

/-- **Graph Minors XXI, (1.1)** (*Graphs with unique linkages*, Section 1, page 1 of the preprint;
stated as **1.1** in Graph Minors XXII, Section 1, page 531):
"**1.1** *For every integer $p \ge 0$ there exists $w \ge 0$ such that every graph with a vital
$p$-linkage has tree-width $\le w$.*" -/
def GM21Theorem11Statement : Prop :=
  ∀ p : ℕ, ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G L : Graph α β),
    V(G).Finite → E(G).Finite → IsVitalPLinkage G L p → TreeWidthLE G w

/-! ## 2. Combining `(10.4)` and `(3.1)` on `Hypergraph α β` -/

/-- Graph Minors XXI, (10.4) combined with (3.1) for any `Hypergraph α β`:
every graph with a vital `p`-linkage has `treeWidthPlusOne G ≤ w + 1`. -/
theorem hypergraph_treeWidthPlusOne_le_of_hasVitalPLinkage
    (p : ℕ) :
    ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G : Hypergraph α β),
      G.IsGraph → GM21.HasVitalPLinkage G p → treeWidthPlusOne G ≤ w + 1 := by
  obtain ⟨θ, hθ_pos, h104⟩ := theorem_10_4_proof p
  refine ⟨(3 * θ) / 2, ?_⟩
  intro α β G hG hvit
  by_cases htw0 : treeWidthPlusOne G = 0
  · omega
  · have htw_pos : 1 ≤ treeWidthPlusOne G := Nat.pos_of_ne_zero htw0
    let w_G := treeWidthPlusOne G - 1
    have hw_G : treeWidthPlusOne G = w_G + 1 := by omega
    obtain ⟨⟨θ_G, 𝒯, h𝒯, hge⟩, _⟩ := theorem_3_1_proof G w_G hw_G
    have hlt : θ_G < θ := by
      by_contra hge_θ
      exact h104 G θ_G 𝒯 hG (Nat.le_of_not_lt hge_θ) h𝒯 hvit
    omega

/-! ## 3. Bridge between `Graph α β` and `Hypergraph α β` -/

lemma ofGraph_ends_eq_of_isLink {α : Type u} {β : Type v}
    {H : Graph α β} (hVH : V(H).Finite) (hEH : E(H).Finite)
    {e : β} {x y : α} (hl : H.IsLink e x y) :
    (Hypergraph.ofGraph H hVH hEH).ends e = {x, y} := by
  ext z
  simp only [Hypergraph.ends, Hypergraph.ofGraph, Graph.Inc, mem_ofPred_eq,
    mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨w, hzw⟩
    exact hzw.left_eq_or_eq hl
  · rintro (rfl | rfl)
    · exact ⟨y, hl⟩
    · exact ⟨x, hl.symm⟩

lemma toGraph_ofGraph {α : Type u} {β : Type v}
    (H : Graph α β) (hVH : V(H).Finite) (hEH : E(H).Finite) :
    GM17.toGraph (Hypergraph.ofGraph H hVH hEH) (GM16.isGraph_ofGraph H hVH hEH) = H := by
  refine Graph.ext rfl fun e x y => ?_
  simp only [GM17.toGraph]
  constructor
  · rintro ⟨he, hx, hy, hsub⟩
    obtain ⟨u, w, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
    have hends := ofGraph_ends_eq_of_isLink hVH hEH hl
    rw [hends] at hx hy hsub
    rcases hx with hx_eq | hx_eq <;> rcases hy with hy_eq | hy_eq
    · rw [hx_eq, hy_eq] at hsub ⊢
      have hw : w = u := by simpa using hsub (Or.inr rfl)
      rwa [hw] at hl
    · rw [hx_eq, hy_eq]; exact hl
    · rw [hx_eq, hy_eq]; exact hl.symm
    · rw [hx_eq, hy_eq] at hsub ⊢
      have hu : u = w := by simpa using hsub (Or.inl rfl)
      rwa [hu] at hl
  · intro hl
    have hends := ofGraph_ends_eq_of_isLink hVH hEH hl
    rw [hends]
    exact ⟨hl.edge_mem, Or.inl rfl, Or.inr rfl, Subset.rfl⟩

lemma toGraph_le_iff {α : Type u} {β : Type v}
    {H₁ H₂ : Hypergraph α β} (h₁ : H₁.IsGraph) (h₂ : H₂.IsGraph) :
    GM17.toGraph H₁ h₁ ≤ GM17.toGraph H₂ h₂ ↔ H₁ ≤ H₂ := by
  constructor
  · intro h
    have hV₁ : V(GM17.toGraph H₁ h₁).Finite := H₁.vertexSet_finite
    have hE₁ : E(GM17.toGraph H₁ h₁).Finite := H₁.edgeSet_finite
    have hV₂ : V(GM17.toGraph H₂ h₂).Finite := H₂.vertexSet_finite
    have hE₂ : E(GM17.toGraph H₂ h₂).Finite := H₂.edgeSet_finite
    have hle := GM17.ofGraph_le h hV₁ hE₁ hV₂ hE₂
    rwa [GM17.ofGraph_toGraph H₁ h₁ hV₁ hE₁, GM17.ofGraph_toGraph H₂ h₂ hV₂ hE₂] at hle
  · intro h
    refine ⟨h.vertexSet_subset, fun e x y hl => ?_⟩
    rcases hl with ⟨he, hx, hy, hsub⟩
    have he₂ : e ∈ H₂.edgeSet := h.edgeSet_subset he
    have hends := h.ends_eq e he
    rw [← hends] at hx hy hsub
    exact ⟨he₂, hx, hy, hsub⟩

lemma graphWalk_iff_skeleton_reachable {α : Type u} {β : Type v}
    {H : Graph α β} (hVH : V(H).Finite) (hEH : E(H).Finite)
    {x y : α} (hx : x ∈ V(H)) (hy : y ∈ V(H)) :
    Nonempty (GraphWalk H x y) ↔ (Hypergraph.ofGraph H hVH hEH).skeleton.Reachable x y := by
  constructor
  · rintro ⟨W⟩
    exact GM12.graphWalk_skeleton_reachable hVH hEH W
  · rintro ⟨p⟩
    have hwalk : ∀ {a b : α} (w : (Hypergraph.ofGraph H hVH hEH).skeleton.Walk a b),
        a ∈ V(H) → b ∈ V(H) → Nonempty (GraphWalk H a b) := by
      intro a b w
      induction w with
      | nil =>
        intro ha _
        exact ⟨GraphWalk.nil ha⟩
      | @cons a c b hadj w' ih =>
        intro ha hb
        rcases hadj with ⟨hne, e, ⟨u₁, hl₁⟩, ⟨u₂, hl₂⟩⟩
        have hl_ac : H.IsLink e a c := by
          rcases hl₂.left_eq_or_eq hl₁ with h_eq | rfl
          · exact (hne h_eq.symm).elim
          · exact hl₁
        obtain ⟨W'⟩ := ih hl_ac.right_mem hb
        exact ⟨GraphWalk.cons hl_ac W'⟩
    exact hwalk p hx hy

lemma isGraphConnected_iff {α : Type u} {β : Type v}
    {C : Graph α β} (hVC : V(C).Finite) (hEC : E(C).Finite) :
    IsGraphConnected C ↔
      (Hypergraph.ofGraph C hVC hEC).vertexSet.Nonempty ∧
      ∀ x ∈ (Hypergraph.ofGraph C hVC hEC).vertexSet,
        ∀ y ∈ (Hypergraph.ofGraph C hVC hEC).vertexSet,
          (Hypergraph.ofGraph C hVC hEC).skeleton.Reachable x y := by
  refine and_congr_right fun _ => forall₂_congr fun x hx => forall₂_congr fun y hy => ?_
  exact graphWalk_iff_skeleton_reachable hVC hEC hx hy

lemma isGraphComponent_iff_isComponentOf {α : Type u} {β : Type v}
    {L C : Graph α β} (hVL : V(L).Finite) (hEL : E(L).Finite)
    (hVC : V(C).Finite) (hEC : E(C).Finite) :
    IsGraphComponent C L ↔
      GM21.IsComponentOf (Hypergraph.ofGraph L hVL hEL) (Hypergraph.ofGraph C hVC hEC) := by
  let L_H := Hypergraph.ofGraph L hVL hEL
  let C_H := Hypergraph.ofGraph C hVC hEC
  have hL_graph : L_H.IsGraph := GM16.isGraph_ofGraph L hVL hEL
  have hC_graph : C_H.IsGraph := GM16.isGraph_ofGraph C hVC hEC
  constructor
  · rintro ⟨hCL, ⟨hne, hconn⟩, hmax⟩
    refine ⟨GM17.ofGraph_le hCL hVC hEC hVL hEL, hne,
      fun x hx y hy => (graphWalk_iff_skeleton_reachable hVC hEC hx hy).mp (hconn x hx y hy), ?_⟩
    intro C' hC'_le hne' hconn' hle'
    have hC'_graph : C'.IsGraph := fun e he => by
      rw [← hC'_le.ends_eq e he]
      exact hL_graph e (hC'_le.edgeSet_subset he)
    let C'_G := GM17.toGraph C' hC'_graph
    have hVC' : V(C'_G).Finite := C'.vertexSet_finite
    have hEC' : E(C'_G).Finite := C'.edgeSet_finite
    have h_of_C' : Hypergraph.ofGraph C'_G hVC' hEC' = C' :=
      GM17.ofGraph_toGraph C' hC'_graph hVC' hEC'
    have hC'_le_L : C'_G ≤ L := by
      rw [← toGraph_ofGraph L hVL hEL]
      exact (toGraph_le_iff hC'_graph hL_graph).mpr hC'_le
    have hC_le_C' : C ≤ C'_G := by
      rw [← toGraph_ofGraph C hVC hEC]
      exact (toGraph_le_iff hC_graph hC'_graph).mpr hle'
    have hC'_conn : IsGraphConnected C'_G := by
      refine ⟨hne', fun x hx y hy => ?_⟩
      rw [graphWalk_iff_skeleton_reachable hVC' hEC' hx hy, h_of_C']
      exact hconn' x hx y hy
    have heq : C'_G = C := hmax C'_G hC_le_C' hC'_le_L hC'_conn
    rw [← h_of_C']
    exact Hypergraph.ext (congrArg Graph.vertexSet heq) (congrArg Graph.edgeSet heq)
      (by change C'_G.Inc = C.Inc; rw [heq])
  · rintro ⟨hCL, hne, hconn, hmax⟩
    have hCL_G : C ≤ L := by
      rw [← toGraph_ofGraph C hVC hEC, ← toGraph_ofGraph L hVL hEL]
      exact (toGraph_le_iff hC_graph hL_graph).mpr hCL
    refine ⟨hCL_G, ⟨hne, fun x hx y hy =>
      (graphWalk_iff_skeleton_reachable hVC hEC hx hy).mpr (hconn x hx y hy)⟩, ?_⟩
    intro C' hC_le_C' hC'_le_L ⟨hne', hconn'⟩
    have hVC' : V(C').Finite := hVL.subset hC'_le_L.vertexSet_mono
    have hEC' : E(C').Finite := hEL.subset hC'_le_L.edgeSet_mono
    have hconn'_H : ∀ x ∈ (Hypergraph.ofGraph C' hVC' hEC').vertexSet,
        ∀ y ∈ (Hypergraph.ofGraph C' hVC' hEC').vertexSet,
          (Hypergraph.ofGraph C' hVC' hEC').skeleton.Reachable x y :=
      fun x hx y hy => (graphWalk_iff_skeleton_reachable hVC' hEC' hx hy).mp (hconn' x hx y hy)
    have heq := hmax (Hypergraph.ofGraph C' hVC' hEC')
      (GM17.ofGraph_le hC'_le_L hVC' hEC' hVL hEL) hne' hconn'_H
      (GM17.ofGraph_le hC_le_C' hVC hEC hVC' hEC')
    exact (Compatible.of_le_le hC'_le_L hCL_G).ext
      (congrArg Hypergraph.vertexSet heq) (congrArg Hypergraph.edgeSet heq)

/-! ### Helper lemmas on `GraphWalk` for `isGraphPath_iff_isPathGraph` -/

lemma graphWalk_support_length {α : Type u} {β : Type v} {P : Graph α β}
    {u v : α} (W : GraphWalk P u v) :
    W.support.length = W.length + 1 := by
  induction W with
  | nil => rfl
  | cons _ rest ih => simp [GraphWalk.support, GraphWalk.length, GraphWalk.edges, ih]

lemma graphWalk_support_zero {α : Type u} {β : Type v} {P : Graph α β}
    {u v : α} (W : GraphWalk P u v) :
    W.support[0]'(by rw [graphWalk_support_length]; omega) = u := by
  cases W <;> rfl

lemma graphWalk_support_last {α : Type u} {β : Type v} {P : Graph α β}
    {u v : α} (W : GraphWalk P u v) :
    W.support[W.length]'(by rw [graphWalk_support_length]; omega) = v := by
  induction W with
  | nil => rfl
  | cons _ rest ih =>
    simp only [GraphWalk.support, GraphWalk.length, GraphWalk.edges, List.length_cons,
      List.getElem_cons_succ]
    exact ih

lemma graphWalk_isLink_getElem {α : Type u} {β : Type v} {P : Graph α β}
    {u v : α} (W : GraphWalk P u v) (k : ℕ) (hk : k < W.length) :
    P.IsLink (W.edges[k]'hk)
      (W.support[k]'(by rw [graphWalk_support_length]; omega))
      (W.support[k + 1]'(by rw [graphWalk_support_length]; omega)) := by
  induction W generalizing k with
  | nil => simp [GraphWalk.length, GraphWalk.edges] at hk
  | cons hl rest ih =>
    cases k with
    | zero =>
      simp only [GraphWalk.edges, GraphWalk.support, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.zero_add]
      rwa [graphWalk_support_zero]
    | succ k' =>
      simp only [GraphWalk.edges, GraphWalk.support, List.getElem_cons_succ]
      exact ih k' (Nat.lt_of_succ_lt_succ hk)

lemma isGraphPath_iff_isPathGraph {α : Type u} {β : Type v}
    {L P : Graph α β} (hPL : P ≤ L) (hVP : V(P).Finite) (hEP : E(P).Finite) :
    IsGraphPath L P ↔ GM21.IsPathGraph (Hypergraph.ofGraph P hVP hEP) := by
  let P_H := Hypergraph.ofGraph P hVP hEP
  have hP_graph : P_H.IsGraph := GM16.isGraph_ofGraph P hVP hEP
  constructor
  · rintro ⟨a, b, _, W, hW_simp, hVP_eq, hEP_eq⟩
    by_cases hlen0 : W.length = 0
    · cases W with
      | nil ha =>
        have hV_sing : P_H.vertexSet = {a} := by
          change V(P) = {a}
          rw [hVP_eq]
          ext x; simp [GraphWalk.support]
        have hE_emp : P_H.edgeSet = ∅ := by
          change E(P) = ∅
          rw [hEP_eq]
          ext e; simp [GraphWalk.edges]
        refine ⟨hP_graph, ⟨a, hV_sing ▸ rfl⟩, ?_, fun e he => (hE_emp ▸ he).elim,
          fun e he => (hE_emp ▸ he).elim, ?_, fun _ hHP ⟨e, he⟩ => (hE_emp ▸ hHP.edgeSet_subset he).elim⟩
        · intro x hx y hy
          rw [hV_sing] at hx hy
          rw [mem_singleton_iff.mp hx, mem_singleton_iff.mp hy]
        · intro x _
          have hemp : GM21.incidentEdges P_H x = ∅ := by
            ext e; simp [GM21.incidentEdges, hE_emp]
          rw [hemp, ncard_empty]; omega
      | cons _ _ => simp [GraphWalk.length, GraphWalk.edges] at hlen0
    · have hm_pos : 1 ≤ W.length := Nat.pos_of_ne_zero hlen0
      let m := W.length
      let v : Fin (m + 1) → α := fun i =>
        W.support[i.1]'(by rw [graphWalk_support_length]; exact i.2)
      have hv_inj : Function.Injective v := by
        intro i j hij
        ext
        exact (List.Nodup.getElem_inj_iff hW_simp).mp hij
      have hv0 : v 0 = a := graphWalk_support_zero W
      have hvm : v ⟨m, Nat.lt_succ_self m⟩ = b := graphWalk_support_last W
      have hV_range : P_H.vertexSet = Set.range v := by
        change V(P) = Set.range v
        rw [hVP_eq]
        ext x
        simp only [mem_ofPred_eq, List.mem_iff_getElem, mem_range, v]
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨⟨i, by rw [graphWalk_support_length] at hi; exact hi⟩, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨i.1, by rw [graphWalk_support_length]; exact i.2, rfl⟩
      have hends_step : ∀ k : ℕ, (hk : k < m) →
          P_H.ends (W.edges[k]'hk) = {v ⟨k, by omega⟩, v ⟨k + 1, by omega⟩} := by
        intro k hk
        exact ofGraph_ends_eq_of_isLink hVP hEP (graphWalk_isLink_getElem W k hk)
      have h2 : ∀ e ∈ P_H.edgeSet, (P_H.ends e).ncard = 2 := by
        intro e he
        change e ∈ E(P) at he
        rw [hEP_eq, mem_ofPred_eq, List.mem_iff_getElem] at he
        rcases he with ⟨k, hk, rfl⟩
        rw [hends_step k hk, ncard_pair]
        intro h_eq
        have := congrArg Fin.val (hv_inj h_eq)
        dsimp at this; omega
      have hpair_inj : ∀ k₁ k₂ : ℕ, (hk₁ : k₁ < m) → (hk₂ : k₂ < m) →
          ({v ⟨k₁, by omega⟩, v ⟨k₁ + 1, by omega⟩} : Set α) =
            {v ⟨k₂, by omega⟩, v ⟨k₂ + 1, by omega⟩} → k₁ = k₂ := by
        intro k₁ k₂ hk₁ hk₂ heq
        have h1 : v ⟨k₁, by omega⟩ ∈ ({v ⟨k₂, by omega⟩, v ⟨k₂ + 1, by omega⟩} : Set α) := by
          rw [← heq]; exact Or.inl rfl
        have h2' : v ⟨k₁ + 1, by omega⟩ ∈ ({v ⟨k₂, by omega⟩, v ⟨k₂ + 1, by omega⟩} : Set α) := by
          rw [← heq]; exact Or.inr rfl
        rcases h1 with h1 | h1 <;> rcases h2' with h2' | h2'
        · have c1 := congrArg Fin.val (hv_inj h1)
          have c2 := congrArg Fin.val (hv_inj h2')
          dsimp at c1 c2; omega
        · have c1 := congrArg Fin.val (hv_inj h1)
          dsimp at c1; exact c1
        · have c1 := congrArg Fin.val (hv_inj h1)
          have c2 := congrArg Fin.val (hv_inj h2')
          dsimp at c1 c2; omega
        · have c1 := congrArg Fin.val (hv_inj h1)
          have c2 := congrArg Fin.val (hv_inj h2')
          dsimp at c1 c2; omega
      have hinj_E : ∀ e₁ ∈ P_H.edgeSet, ∀ e₂ ∈ P_H.edgeSet,
          P_H.ends e₁ = P_H.ends e₂ → e₁ = e₂ := by
        intro e₁ he₁ e₂ he₂ hends
        change e₁ ∈ E(P) at he₁
        change e₂ ∈ E(P) at he₂
        rw [hEP_eq, mem_ofPred_eq, List.mem_iff_getElem] at he₁ he₂
        rcases he₁ with ⟨k₁, hk₁, rfl⟩
        rcases he₂ with ⟨k₂, hk₂, rfl⟩
        rw [hends_step k₁ hk₁, hends_step k₂ hk₂] at hends
        have hk_eq := hpair_inj k₁ k₂ hk₁ hk₂ hends
        subst hk_eq; rfl
      have hadj_iff : ∀ i j : Fin (m + 1),
          P_H.skeleton.Adj (v i) (v j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
        intro i j
        constructor
        · rintro ⟨hne_ij, e, hi_inc, hj_inc⟩
          have heP : e ∈ E(P) := P_H.edge_mem_of_inc hi_inc
          rw [hEP_eq, mem_ofPred_eq, List.mem_iff_getElem] at heP
          rcases heP with ⟨k, hk, rfl⟩
          have hi_ends : v i ∈ P_H.ends (W.edges[k]'hk) := hi_inc
          have hj_ends : v j ∈ P_H.ends (W.edges[k]'hk) := hj_inc
          rw [hends_step k hk] at hi_ends hj_ends
          rcases hi_ends with hi_eq | hi_eq <;> rcases hj_ends with hj_eq | hj_eq
          · exact (hne_ij (hi_eq.trans hj_eq.symm)).elim
          · left
            have c1 := congrArg Fin.val (hv_inj hi_eq)
            have c2 := congrArg Fin.val (hv_inj hj_eq)
            dsimp at c1 c2; omega
          · right
            have c1 := congrArg Fin.val (hv_inj hi_eq)
            have c2 := congrArg Fin.val (hv_inj hj_eq)
            dsimp at c1 c2; omega
          · exact (hne_ij (hi_eq.trans hj_eq.symm)).elim
        · rintro (h_eq | h_eq)
          · have hk : i.1 < m := by omega
            have hl := graphWalk_isLink_getElem W i.1 hk
            have hj_eq : j = ⟨i.1 + 1, by omega⟩ := Fin.ext h_eq.symm
            rw [hj_eq]
            refine ⟨fun h => by have := congrArg Fin.val (hv_inj h); dsimp at this; omega,
              W.edges[i.1]'hk, hl.inc_left, hl.inc_right⟩
          · have hk : j.1 < m := by omega
            have hl := graphWalk_isLink_getElem W j.1 hk
            have hi_eq : i = ⟨j.1 + 1, by omega⟩ := Fin.ext h_eq.symm
            rw [hi_eq]
            refine ⟨fun h => by have := congrArg Fin.val (hv_inj h); dsimp at this; omega,
              W.edges[j.1]'hk, hl.inc_right, hl.inc_left⟩
      exact (isPathGraph_of_isIndexedPath hP_graph h2 hinj_E
        ⟨m, hm_pos, v, hv_inj, hv0, hvm, hV_range, hadj_iff⟩).1
  · intro hP
    by_cases hE_emp : P_H.edgeSet = ∅
    · obtain ⟨v, hv_eq, _⟩ := isPathGraph_empty_edgeSet hP hE_emp
      have hv_P : v ∈ V(P) := by change v ∈ P_H.vertexSet; rw [hv_eq]; rfl
      refine ⟨v, v, hPL, GraphWalk.nil hv_P, by simp [GraphWalk.IsSimple, GraphWalk.support],
        ?_, ?_⟩
      · change P_H.vertexSet = _
        rw [hv_eq]; ext x; simp [GraphWalk.support]
      · change P_H.edgeSet = _
        rw [hE_emp]; ext e; simp [GraphWalk.edges]
    · obtain ⟨x₁, _, x₂, _, _, hpath, _⟩ :=
        exists_isIndexedPath_of_isPathGraph hP (nonempty_iff_ne_empty.mpr hE_emp)
      rcases hpath with ⟨m, _, v, hv_inj, _, _, hV_range, hadj_iff⟩
      have hex_edge : ∀ k : ℕ, (hk : k < m) →
          ∃ e : β, P.IsLink e (v ⟨k, by omega⟩) (v ⟨k + 1, by omega⟩) := by
        intro k hk
        have hadj : P_H.skeleton.Adj (v ⟨k, by omega⟩) (v ⟨k + 1, by omega⟩) :=
          (hadj_iff ⟨k, by omega⟩ ⟨k + 1, by omega⟩).mpr (Or.inl rfl)
        rcases hadj with ⟨hne, e, ⟨u₁, hl₁⟩, ⟨u₂, hl₂⟩⟩
        rcases hl₂.left_eq_or_eq hl₁ with h_eq | rfl
        · exact (hne h_eq.symm).elim
        · exact ⟨e, hl₁⟩
      choose e_fn he_fn using hex_edge
      have hwalk_build : ∀ k : ℕ, (hk : k ≤ m) →
          ∃ W : GraphWalk P (v ⟨k, by omega⟩) (v ⟨m, Nat.lt_succ_self m⟩),
            (∀ x, x ∈ W.support ↔ ∃ i : Fin (m + 1), k ≤ i.1 ∧ v i = x) ∧
            W.support.Nodup ∧
            (∀ e, e ∈ W.edges ↔ ∃ j : ℕ, ∃ hj : j < m, k ≤ j ∧ e_fn j hj = e) := by
        intro k hk
        induction hdiff : m - k generalizing k with
        | zero =>
          have hk_eq : k = m := by omega
          have hfin_eq : (⟨k, by omega⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext hk_eq
          have hvm_P : v ⟨m, Nat.lt_succ_self m⟩ ∈ V(P) := by
            change v ⟨m, Nat.lt_succ_self m⟩ ∈ P_H.vertexSet
            rw [hV_range]; exact mem_range_self _
          rw [hfin_eq]
          refine ⟨GraphWalk.nil hvm_P, ?_, by simp [GraphWalk.support], ?_⟩
          · intro x
            simp only [GraphWalk.support, List.mem_singleton]
            constructor
            · rintro rfl; exact ⟨⟨m, Nat.lt_succ_self m⟩, by omega, rfl⟩
            · rintro ⟨i, hi, rfl⟩
              congr 1; ext; dsimp; omega
          · intro e
            simp only [GraphWalk.edges, List.not_mem_nil, false_iff, not_exists, not_and]
            intro j hj hmj _; omega
        | succ d ih =>
          have hk_lt : k < m := by omega
          obtain ⟨W', hW'_supp, hW'_nodup, hW'_edges⟩ := ih (k + 1) (by omega) (by omega)
          let W := GraphWalk.cons (he_fn k hk_lt) W'
          refine ⟨W, ?_, ?_, ?_⟩
          · intro x
            simp only [W, GraphWalk.support, List.mem_cons, hW'_supp]
            constructor
            · rintro (rfl | ⟨i, hi, rfl⟩)
              · exact ⟨⟨k, by omega⟩, le_rfl, rfl⟩
              · exact ⟨i, by omega, rfl⟩
            · rintro ⟨i, hi, rfl⟩
              rcases eq_or_lt_of_le hi with h_eq | h_lt
              · left; congr 1; ext; exact h_eq.symm
              · right; exact ⟨i, h_lt, rfl⟩
          · simp only [W, GraphWalk.support, List.nodup_cons, hW'_supp]
            refine ⟨?_, hW'_nodup⟩
            rintro ⟨i, hi, h_eq⟩
            have := congrArg Fin.val (hv_inj h_eq)
            dsimp at this; omega
          · intro e
            simp only [W, GraphWalk.edges, List.mem_cons, hW'_edges]
            constructor
            · rintro (rfl | ⟨j, hj, hkj, rfl⟩)
              · exact ⟨k, hk_lt, le_rfl, rfl⟩
              · exact ⟨j, hj, by omega, rfl⟩
            · rintro ⟨j, hj, hkj, rfl⟩
              rcases eq_or_lt_of_le hkj with rfl | h_lt
              · exact Or.inl rfl
              · exact Or.inr ⟨j, hj, h_lt, rfl⟩
      obtain ⟨W, hW_supp, hW_nodup, hW_edges⟩ := hwalk_build 0 (Nat.zero_le m)
      refine ⟨v ⟨0, Nat.zero_lt_succ m⟩, v ⟨m, Nat.lt_succ_self m⟩, hPL, W, hW_nodup, ?_, ?_⟩
      · change P_H.vertexSet = _
        rw [hV_range]
        ext x
        rw [mem_range, mem_ofPred_eq, hW_supp]
        exact ⟨fun ⟨i, hi⟩ => ⟨i, Nat.zero_le _, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩
      · ext e
        rw [mem_ofPred_eq, hW_edges]
        constructor
        · intro he
          have hcard2 : (P_H.ends e).ncard = 2 := hP.2.2.2.1 e he
          obtain ⟨u, w, hl⟩ := Graph.exists_isLink_of_mem_edgeSet he
          have hends := ofGraph_ends_eq_of_isLink hVP hEP hl
          have huw_ne : u ≠ w := by
            intro rfl
            rw [hends, pair_eq_singleton, ncard_singleton] at hcard2
            omega
          have hu_V : u ∈ P_H.vertexSet := hl.left_mem
          have hw_V : w ∈ P_H.vertexSet := hl.right_mem
          rw [hV_range] at hu_V hw_V
          rcases hu_V with ⟨i, rfl⟩
          rcases hw_V with ⟨j, rfl⟩
          have hadj_ij : P_H.skeleton.Adj (v i) (v j) :=
            ⟨huw_ne, e, hl.inc_left, hl.inc_right⟩
          rcases (hadj_iff i j).mp hadj_ij with hij | hji
          · have hi_lt : i.1 < m := by omega
            refine ⟨i.1, hi_lt, Nat.zero_le _, ?_⟩
            apply hP.2.2.2.2.1 _ (he_fn i.1 hi_lt).edge_mem e he
            rw [ofGraph_ends_eq_of_isLink hVP hEP (he_fn i.1 hi_lt), hends]
            have hj_eq : j = ⟨i.1 + 1, by omega⟩ := Fin.ext hij.symm
            rw [hj_eq]
          · have hj_lt : j.1 < m := by omega
            refine ⟨j.1, hj_lt, Nat.zero_le _, ?_⟩
            apply hP.2.2.2.2.1 _ (he_fn j.1 hj_lt).edge_mem e he
            rw [ofGraph_ends_eq_of_isLink hVP hEP (he_fn j.1 hj_lt), hends, Set.pair_comm]
            have hi_eq : i = ⟨j.1 + 1, by omega⟩ := Fin.ext hji.symm
            rw [hi_eq]
        · rintro ⟨j, hj, _, rfl⟩
          exact (he_fn j hj).edge_mem

lemma isLinkage_iff {α : Type u} {β : Type v}
    {G L : Graph α β} (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hVL : V(L).Finite) (hEL : E(L).Finite) :
    IsLinkage G L ↔
      GM21.IsLinkage (Hypergraph.ofGraph G hVG hEG) (Hypergraph.ofGraph L hVL hEL) := by
  let G_H := Hypergraph.ofGraph G hVG hEG
  let L_H := Hypergraph.ofGraph L hVL hEL
  have hG_graph : G_H.IsGraph := GM16.isGraph_ofGraph G hVG hEG
  have hL_graph : L_H.IsGraph := GM16.isGraph_ofGraph L hVL hEL
  constructor
  · rintro ⟨hLG, hcomp⟩
    refine ⟨GM17.ofGraph_le hLG hVL hEL hVG hEG, hL_graph, fun C_H hC_H => ?_⟩
    have hC_graph : C_H.IsGraph := fun e he => by
      rw [← hC_H.1.ends_eq e he]
      exact hL_graph e (hC_H.1.edgeSet_subset he)
    let C := GM17.toGraph C_H hC_graph
    have hVC : V(C).Finite := C_H.vertexSet_finite
    have hEC : E(C).Finite := C_H.edgeSet_finite
    have h_of_C : Hypergraph.ofGraph C hVC hEC = C_H :=
      GM17.ofGraph_toGraph C_H hC_graph hVC hEC
    rw [← h_of_C] at hC_H ⊢
    have hC_comp : IsGraphComponent C L :=
      (isGraphComponent_iff_isComponentOf hVL hEL hVC hEC).mpr hC_H
    exact (isGraphPath_iff_isPathGraph hC_comp.1 hVC hEC).mp (hcomp C hC_comp)
  · rintro ⟨hLG, _, hcomp⟩
    have hLG_G : L ≤ G := by
      rw [← toGraph_ofGraph L hVL hEL, ← toGraph_ofGraph G hVG hEG]
      exact (toGraph_le_iff hL_graph hG_graph).mpr hLG
    refine ⟨hLG_G, fun P hP => ?_⟩
    have hVP : V(P).Finite := hVL.subset hP.1.vertexSet_mono
    have hEP : E(P).Finite := hEL.subset hP.1.edgeSet_mono
    have hP_H : GM21.IsComponentOf L_H (Hypergraph.ofGraph P hVP hEP) :=
      (isGraphComponent_iff_isComponentOf hVL hEL hVP hEP).mp hP
    exact (isGraphPath_iff_isPathGraph hP.1 hVP hEP).mpr (hcomp _ hP_H)

lemma vertexValency_eq_vertexDegree {α : Type u} {β : Type v}
    (L : Graph α β) (hVL : V(L).Finite) (hEL : E(L).Finite) (v : α) :
    vertexValency L v = GM21.vertexDegree (Hypergraph.ofGraph L hVL hEL) v := by
  let L_H := Hypergraph.ofGraph L hVL hEL
  let A : Set β := {e ∈ E(L) | ∃ w ≠ v, L.IsLink e v w}
  let B : Set β := {e ∈ E(L) | L.IsLink e v v}
  have hA_fin : A.Finite := hEL.subset fun _ h => h.1
  have hB_fin : B.Finite := hEL.subset fun _ h => h.1
  have hdisj : Disjoint A B := by
    refine Set.disjoint_left.mpr fun e ⟨_, w, hne, hvw⟩ ⟨_, hvv⟩ => ?_
    rcases hvw.symm.left_eq_or_eq hvv with h_eq | h_eq <;> exact hne h_eq
  have hinc_eq : GM21.incidentEdges L_H v = A ∪ B := by
    ext e
    simp only [GM21.incidentEdges, L_H, Hypergraph.ofGraph, Graph.Inc, A, B,
      mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨he, w, hl⟩
      by_cases hwv : w = v
      · subst hwv; exact Or.inr ⟨he, hl⟩
      · exact Or.inl ⟨he, w, hwv, hl⟩
    · rintro (⟨he, w, _, hl⟩ | ⟨he, hl⟩)
      · exact ⟨he, w, hl⟩
      · exact ⟨he, v, hl⟩
  have hloop_eq : {e ∈ GM21.incidentEdges L_H v | (L_H.ends e).Subsingleton} = B := by
    ext e
    simp only [GM21.incidentEdges, B, mem_ofPred_eq]
    change (e ∈ E(L) ∧ ∃ w, L.IsLink e v w) ∧ (L_H.ends e).Subsingleton ↔
      e ∈ E(L) ∧ L.IsLink e v v
    constructor
    · rintro ⟨⟨he, w, hl⟩, hsub⟩
      have hends := ofGraph_ends_eq_of_isLink hVL hEL hl
      have hvw : v = w := hsub (by rw [hends]; exact Or.inl rfl) (by rw [hends]; exact Or.inr rfl)
      subst hvw
      exact ⟨he, hl⟩
    · rintro ⟨he, hl⟩
      have hends := ofGraph_ends_eq_of_isLink hVL hEL hl
      refine ⟨⟨he, v, hl⟩, ?_⟩
      rw [hends, pair_eq_singleton]
      exact subsingleton_singleton
  unfold vertexValency GM21.vertexDegree
  change A.ncard + 2 * B.ncard = _
  rw [hloop_eq, hinc_eq, ncard_union_eq hdisj hA_fin hB_fin]
  omega

lemma terminals_eq {α : Type u} {β : Type v}
    (L : Graph α β) (hVL : V(L).Finite) (hEL : E(L).Finite) :
    terminals L = GM21.terminals (Hypergraph.ofGraph L hVL hEL) := by
  ext v
  simp only [terminals, GM21.terminals, GM21.IsTerminal, mem_ofPred_eq]
  rw [vertexValency_eq_vertexDegree L hVL hEL v]
  rfl

lemma linkagePattern_eq_of_isLinkage {α : Type u} {β : Type v}
    {G L : Graph α β} (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hVL : V(L).Finite) (hEL : E(L).Finite) (hlink : IsLinkage G L) :
    linkagePattern L = GM21.linkagePattern (Hypergraph.ofGraph L hVL hEL) := by
  let L_H := Hypergraph.ofGraph L hVL hEL
  have hL_graph : L_H.IsGraph := GM16.isGraph_ofGraph L hVL hEL
  have hlink_H : GM21.IsLinkage (Hypergraph.ofGraph G hVG hEG) L_H :=
    (isLinkage_iff hVG hEG hVL hEL).mp hlink
  ext B
  simp only [linkagePattern, GM21.linkagePattern, mem_ofPred_eq, terminals_eq L hVL hEL]
  constructor
  · rintro ⟨_, P, hP, rfl⟩
    have hVP : V(P).Finite := hVL.subset hP.1.vertexSet_mono
    have hEP : E(P).Finite := hEL.subset hP.1.edgeSet_mono
    refine ⟨Hypergraph.ofGraph P hVP hEP,
      (isGraphComponent_iff_isComponentOf hVL hEL hVP hEP).mp hP, Set.inter_comm _ _⟩
  · rintro ⟨C_H, hC_H, rfl⟩
    have hP_C : GM21.IsPathGraph C_H := hlink_H.2.2 C_H hC_H
    obtain ⟨z, hzC, hz_deg⟩ := exists_deg_le_one_of_isPathGraph hP_C
    have hz_term : z ∈ GM21.terminals L_H :=
      (mem_terminals_iff_of_isComponentOf hL_graph hC_H hP_C hzC).mpr hz_deg
    have hC_graph : C_H.IsGraph := hP_C.1
    let P := GM17.toGraph C_H hC_graph
    have hVP : V(P).Finite := C_H.vertexSet_finite
    have hEP : E(P).Finite := C_H.edgeSet_finite
    have h_of_P : Hypergraph.ofGraph P hVP hEP = C_H :=
      GM17.ofGraph_toGraph C_H hC_graph hVP hEP
    refine ⟨⟨z, hz_term, hzC⟩, P, ?_, Set.inter_comm _ _⟩
    change IsGraphComponent P L
    rw [isGraphComponent_iff_isComponentOf hVL hEL hVP hEP, h_of_P]
    exact hC_H

lemma hasVitalPLinkage_ofGraph {α : Type u} {β : Type v}
    {G L : Graph α β} (hVG : V(G).Finite) (hEG : E(G).Finite)
    {p : ℕ} (h : IsVitalPLinkage G L p) :
    GM21.HasVitalPLinkage (Hypergraph.ofGraph G hVG hEG) p := by
  rcases h with ⟨⟨hlink, hcard⟩, ⟨_, hV_eq, huniq⟩⟩
  have hVL : V(L).Finite := hVG.subset hlink.1.vertexSet_mono
  have hEL : E(L).Finite := hEG.subset hlink.1.edgeSet_mono
  let G_H := Hypergraph.ofGraph G hVG hEG
  let L_H := Hypergraph.ofGraph L hVL hEL
  have hG_graph : G_H.IsGraph := GM16.isGraph_ofGraph G hVG hEG
  have hL_graph : L_H.IsGraph := GM16.isGraph_ofGraph L hVL hEL
  have hlink_H : GM21.IsLinkage G_H L_H := (isLinkage_iff hVG hEG hVL hEL).mp hlink
  refine ⟨L_H, ⟨hlink_H, hV_eq, ?_⟩, hlink_H, ?_⟩
  · intro L'_H hL'_H hpat
    have hL'_graph : L'_H.IsGraph := fun e he => by
      rw [← hL'_H.1.ends_eq e he]
      exact hG_graph e (hL'_H.1.edgeSet_subset he)
    let L' := GM17.toGraph L'_H hL'_graph
    have hVL' : V(L').Finite := L'_H.vertexSet_finite
    have hEL' : E(L').Finite := L'_H.edgeSet_finite
    have h_of_L' : Hypergraph.ofGraph L' hVL' hEL' = L'_H :=
      GM17.ofGraph_toGraph L'_H hL'_graph hVL' hEL'
    have hL'_link : IsLinkage G L' := by
      rw [isLinkage_iff hVG hEG hVL' hEL', h_of_L']
      exact hL'_H
    have hpat_G : linkagePattern L' = linkagePattern L := by
      rw [linkagePattern_eq_of_isLinkage hVG hEG hVL' hEL' hL'_link,
          linkagePattern_eq_of_isLinkage hVG hEG hVL hEL hlink, h_of_L', hpat]
    have heq : L' = L := huniq L' hL'_link hpat_G
    rw [← h_of_L']
    exact Hypergraph.ext (congrArg Graph.vertexSet heq) (congrArg Graph.edgeSet heq)
      (by change L'.Inc = L.Inc; rw [heq])
  · rwa [← terminals_eq L hVL hEL]

/-! ### From `treeWidthPlusOne (Hypergraph.ofGraph G hVG hEG) ≤ w + 1` to `TreeWidthLE G w` -/

lemma treeWidthLE_of_treeWidthPlusOne_le {α : Type u} {β : Type v}
    {G : Graph α β} (hVG : V(G).Finite) (hEG : E(G).Finite) {w : ℕ}
    (htw : treeWidthPlusOne (Hypergraph.ofGraph G hVG hEG) ≤ w + 1) :
    TreeWidthLE G w := by
  let G_H := Hypergraph.ofGraph G hVG hEG
  have hG_graph : G_H.IsGraph := GM16.isGraph_ofGraph G hVG hEG
  obtain ⟨ι, _, T, τ, htd, hw_eq⟩ := exists_treeDecomposition_eq_treeWidthPlusOne G_H
  have hτ_graph : ∀ t : ι, (τ t).IsGraph := fun t e he => by
    rw [← (htd.le t).ends_eq e he]
    exact hG_graph e ((htd.le t).edgeSet_subset he)
  let W : ι → Graph α β := fun t => GM17.toGraph (τ t) (hτ_graph t)
  have hW_le : ∀ t : ι, W t ≤ G := fun t => by
    rw [← toGraph_ofGraph G hVG hEG]
    exact (toGraph_le_iff (hτ_graph t) hG_graph).mpr (htd.le t)
  have hW_mem : ∀ P ∈ Set.range W, P ≤ G := by
    rintro _ ⟨t, rfl⟩
    exact hW_le t
  refine ⟨ι, inferInstance, T, W, ⟨htd.isTree, hW_le, ?_, ?_⟩, ?_⟩
  · refine (Compatible.of_le_le (subgraphSUnion_le hW_mem) le_rfl).ext ?_ ?_
    · rw [vertexSet_subgraphSUnion]
      ext v
      rw [mem_iUnion₂]
      refine ⟨?_, ?_⟩
      · rintro ⟨_, ⟨t, rfl⟩, hv⟩
        exact htd.vertex_mem_iff.mpr ⟨t, hv⟩
      · intro hv
        obtain ⟨t, ht⟩ := htd.vertex_mem_iff.mp hv
        exact ⟨W t, ⟨t, rfl⟩, ht⟩
    · rw [edgeSet_subgraphSUnion hW_mem]
      ext e
      rw [mem_iUnion₂]
      refine ⟨?_, ?_⟩
      · rintro ⟨_, ⟨t, rfl⟩, he⟩
        exact (hW_le t).edgeSet_mono he
      · intro he
        obtain ⟨t, ht⟩ := htd.edge_mem_iff.mp he
        exact ⟨W t, ⟨t, rfl⟩, ht⟩
  · intro t t' t'' hp
    have hle_inter := htd.inter_le hp
    refine (Compatible.of_le_le (subgraphInter_le (hW_le t)) (hW_le t')).le_iff.mpr ⟨?_, ?_⟩
    · rw [vertexSet_subgraphInter]
      exact hle_inter.vertexSet_subset
    · rw [edgeSet_subgraphInter (hW_le t) (hW_le t'')]
      exact hle_inter.edgeSet_subset
  · intro t
    change (τ t).vertexSet.ncard ≤ w + 1
    exact (ncard_vertexSet_le_treeDecompWidthPlusOne τ t).trans (hw_eq.trans_le htw)

/-! ## 4. Proof of Graph Minors XXI, (1.1) -/

/-- **Graph Minors XXI, (1.1)** (Section 1, page 1 of the preprint):
"**1.1** *For every integer $p \ge 0$ there exists $w \ge 0$ such that every graph with a vital
$p$-linkage has tree-width $\le w$.*" -/
theorem theorem_1_1_proof :
    GM21Theorem11Statement.{u, v} := by
  intro p
  obtain ⟨w, hw⟩ :=
    hypergraph_treeWidthPlusOne_le_of_hasVitalPLinkage p
  refine ⟨w, ?_⟩
  intro α β G L hVG hEG hvit
  apply treeWidthLE_of_treeWidthPlusOne_le hVG hEG
  exact hw (Hypergraph.ofGraph G hVG hEG) (GM16.isGraph_ofGraph G hVG hEG)
    (hasVitalPLinkage_ofGraph hVG hEG hvit)

end Final

export Final (IsGraphTreeDecomposition graphTreeDecompWidthPlusOne graphTreeDecompWidth
  graphTreeWidthPlusOne graphTreeWidth TreeWidthLE GM21Theorem11Statement theorem_1_1_proof)

end GraphMinor.GM21
