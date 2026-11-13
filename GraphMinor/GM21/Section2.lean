module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.LinkageLemmas
public import GraphMinor.GM21.SeparationGluing
public import GraphMinor.GM21.VertexSplitting
public import GraphMinor.GM21.NestedSeparations

/-!
# Graph Minors XXI, Section 2: Some basic lemmas

Formalization of Section 2 (pages 2–8 of the preprint) of
N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616.

Proves:
- `theorem_2_1` (Graph Minors XXI, (2.1)): deleting `X ⊆ V(G)` turns a vital `p`-linkage into a
  vital `(p + 2|X|)`-linkage.
- `theorem_2_2` (Graph Minors XXI, (2.2)): restricting a linkage `L` to one side `B` of a
  separation `(A, B)` of `G` yields a linkage in `B` with terminals in `(X \ V(A)) ∪ V(A ∩ B)`.
- `theorem_2_3` (Graph Minors XXI, (2.3)): replacing `L ∩ B` by a linkage `L'` in `B` with the
  same pattern gives a linkage `prunedLeft L A B ∪ L'` in `G` with the same pattern as `L`; in
  particular, if `L` is vital in `G` then `L ∩ B` is vital in `B`.
- `theorem_2_4` (Graph Minors XXI, (2.4)): splitting a vertex of a graph with a vital `p`-linkage
  yields a graph with a vital `(p + 2)`-linkage.
- `theorem_2_5` (Graph Minors XXI, (2.5)): nested separations of constant order `k` linked by
  `k`-component linkages `M_i` agree with a vital `p`-linkage `L` on some interval.
- `theorem_2_6` (Graph Minors XXI, (2.6)): strengthening of `(2.5)` to separations of order `≤ k`.
- `theorem_2_7` (Graph Minors XXI, (2.7)): simultaneous version of `(2.6)` for two vital
  `p`-linkages `L, L'`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.GM10 GraphMinor.GM17

universe u v

/-! ## (2.1): Deleting a vertex set `X` from a vital `p`-linkage -/

/-- **Graph Minors XXI, (2.1)** (page 2 of the preprint):
"If $L$ is a vital $p$-linkage in $G$, and $X \subseteq V(G)$, then $L \setminus X$ is a vital
$(p + 2|X|)$-linkage in $G \setminus X$." -/
theorem theorem_2_1_proof {α : Type u} {β : Type v}
    {G L : Hypergraph α β} {p : ℕ} {X : Set α}
    (hL : IsVitalPLinkage G L p) (hX : X ⊆ G.vertexSet) :
    IsVitalPLinkage (G.deleteVertices X) (L.deleteVertices X) (p + 2 * X.ncard) := by
  have hsep : G.IsSeparation (deleteVerticesComplement G X) (G.deleteVertices X) :=
    isSeparation_deleteVertices G X
  have hvital_inter : IsVitalLinkage (G.deleteVertices X) (L ∩ G.deleteVertices X) :=
    isVitalLinkage_inter_right_of_isSeparation hL.1 hsep
  rw [inter_deleteVertices_eq hL.1.1.1 X] at hvital_inter
  exact ⟨hvital_inter, hvital_inter.1, terminals_deleteVertices_ncard_le hL.2 hX⟩

/-! ## (2.2): Restricting a linkage to one side of a separation -/

/-- If `L ≤ G`, `(A, B)` is a separation of `G`, and `v ∈ V(L ∩ B) \ V(A)`, then the edges
incident with `v` in `L ∩ B` are exactly the edges incident with `v` in `L`. -/
lemma incidentEdges_inter_eq_of_not_mem_left {α : Type u} {β : Type v}
    {G L A B : Hypergraph α β} (hLG : L ≤ G) (hsep : G.IsSeparation A B)
    {v : α} (hvA : v ∉ A.vertexSet) :
    incidentEdges (L ∩ B) v = incidentEdges L v := by
  ext e
  simp only [incidentEdges, mem_ofPred_eq, inter_edgeSet]
  constructor
  · rintro ⟨⟨heL, _⟩, hinc⟩
    exact ⟨heL, hinc.1⟩
  · rintro ⟨heL, hincL⟩
    have heG : e ∈ G.edgeSet := hLG.edgeSet_subset heL
    have hincG : G.Inc e v := (inc_iff_of_le hLG heL).1 hincL
    have heAB : e ∈ A.edgeSet ∪ B.edgeSet := by rwa [hsep.edgeSet_union]
    have henotA : e ∉ A.edgeSet := by
      intro heA
      have hincA : A.Inc e v := (inc_iff_of_le hsep.left_le heA).2 hincG
      exact hvA (A.vertex_mem_of_inc hincA)
    have heB : e ∈ B.edgeSet := heAB.resolve_left henotA
    have hincB : B.Inc e v := (inc_iff_of_le hsep.right_le heB).2 hincG
    exact ⟨⟨heL, heB⟩, ⟨hincL, hincB⟩⟩

/-- If `L ≤ G`, `(A, B)` is a separation of `G`, and `v ∈ V(L ∩ B) \ V(A)`, then the degree of
`v` in `L ∩ B` equals the degree of `v` in `L`. -/
lemma vertexDegree_inter_eq_of_not_mem_left {α : Type u} {β : Type v}
    {G L A B : Hypergraph α β} (hLG : L ≤ G) (hsep : G.IsSeparation A B)
    {v : α} (hvA : v ∉ A.vertexSet) :
    vertexDegree (L ∩ B) v = vertexDegree L v := by
  have hinc_eq := incidentEdges_inter_eq_of_not_mem_left hLG hsep hvA
  have hsub : L ∩ B ≤ L := inter_le_left hLG hsep.right_le
  unfold vertexDegree
  rw [hinc_eq]
  congr 2
  ext e
  simp only [mem_ofPred_eq]
  refine and_congr_right fun he => ?_
  have hends : L.ends e = (L ∩ B).ends e := by
    have heLB : e ∈ (L ∩ B).edgeSet := by
      have : e ∈ incidentEdges (L ∩ B) v := by rwa [hinc_eq]
      exact this.1
    exact hsub.ends_eq e heLB
  rw [hends]

/-- Every terminal of `L ∩ B` belongs to `(terminals L \ V(A)) ∪ V(A ∩ B)` whenever `L ≤ G` and
`(A, B)` is a separation of `G`. -/
lemma terminals_inter_subset_of_isSeparation {α : Type u} {β : Type v}
    {G L A B : Hypergraph α β} (hLG : L ≤ G) (hsep : G.IsSeparation A B) :
    terminals (L ∩ B) ⊆ (terminals L \ A.vertexSet) ∪ (A ∩ B).vertexSet := by
  rintro v ⟨hvLB, hdeg⟩
  have hvL : v ∈ L.vertexSet := hvLB.1
  have hvB : v ∈ B.vertexSet := hvLB.2
  by_cases hvA : v ∈ A.vertexSet
  · exact Or.inr ⟨hvA, hvB⟩
  · left
    refine ⟨⟨hvL, ?_⟩, hvA⟩
    rwa [← vertexDegree_inter_eq_of_not_mem_left hLG hsep hvA]

/-- **Graph Minors XXI, (2.2)** (page 2 of the preprint):
"If $L$ is a linkage in $G$ with set of terminals $X$, and $(A, B)$ is a separation of $G$, then
$L \cap B$ is a linkage in $B$ with set of terminals a subset of
$(X \setminus V(A)) \cup V(A \cap B)$." -/
theorem theorem_2_2_proof {α : Type u} {β : Type v}
    {G L A B : Hypergraph α β}
    (hL : IsLinkage G L) (hsep : G.IsSeparation A B) :
    IsLinkage B (L ∩ B) ∧
      terminals (L ∩ B) ⊆ (terminals L \ A.vertexSet) ∪ (A ∩ B).vertexSet :=
  ⟨isLinkage_of_le hL (inter_le_left hL.1 hsep.right_le) (inter_le_right hL.1 hsep.right_le),
    terminals_inter_subset_of_isSeparation hL.1 hsep⟩

/-! ## (2.3): Replacing a linkage on one side of a separation -/

/-- **Graph Minors XXI, (2.3)** (page 2 of the preprint):
"If $L$ is a linkage in $G$, and $(A, B)$ is a separation of $G$, and $L'$ is a linkage in $B$
with the same pattern as $L \cap B$, then $(L \cap A) \cup L'$ is a linkage in $G$ with the same
pattern as $L$. In particular, if $L$ is a vital linkage in $G$ then $L \cap B$ is a vital linkage
in $B$."

In the first conclusion, `(L ∩ A)` is formalized as `prunedLeft L A B`, which removes
vertices of `V(L ∩ A ∩ B)` that are internal (degree `2`) in `L ∩ B` so that routing `L'` away
from such a separator vertex does not leave an uncancelled degree-`0` terminal in the union. As
printed, the first claim is false. See the correction to (2.3) in `corrections/GM21.md`. -/
theorem theorem_2_3_proof {α : Type u} {β : Type v}
    {G L A B : Hypergraph α β}
    (hL : IsLinkage G L) (hsep : G.IsSeparation A B) :
    (∀ L' : Hypergraph α β,
      IsLinkage B L' →
      linkagePattern L' = linkagePattern (L ∩ B) →
      IsLinkage G (prunedLeft L A B ∪ L') ∧
        linkagePattern (prunedLeft L A B ∪ L') = linkagePattern L) ∧
    (IsVitalLinkage G L → IsVitalLinkage B (L ∩ B)) :=
  ⟨fun _ hL' hpat =>
    ⟨(prunedLeft_union_isLinkage_and_pattern hL hsep hL' hpat).1,
      (prunedLeft_union_isLinkage_and_pattern hL hsep hL' hpat).2.2⟩,
    fun hvital => isVitalLinkage_inter_right_of_isSeparation hvital hsep⟩

/-! ## (2.4): Splitting a vertex of a graph with a vital `p`-linkage -/

/-- **Graph Minors XXI, (2.4)** (page 3 of the preprint):
"If $G'$ is obtained from $G$ by splitting a vertex $v$, and $G$ has a vital $p$-linkage, then
$G'$ has a vital $(p+2)$-linkage." -/
theorem theorem_2_4_proof {α : Type u} {β : Type v}
    {G G' : Hypergraph α β} {p : ℕ}
    (hsplit : ObtainedBySplittingVertex G G')
    (hL : HasVitalPLinkage G p) :
    HasVitalPLinkage G' (p + 2) := by
  rcases hsplit with ⟨_, _, _, _, _, hsplit'⟩
  rcases hL with ⟨L, hLp⟩
  exact ⟨splitSpanningSubgraph G' L, isVitalPLinkage_splitSpanningSubgraph hsplit' hLp⟩

/-! ## (2.5), (2.6), and (2.7): Nested separations and vital linkages -/

/-- **Graph Minors XXI, (2.5)** (page 3 of the preprint):
"Let $p, k \ge 0$ and let $n = (2p + 1)(p + k + 1)^{2(p+k)} + 1$. Let $L$ be a vital $p$-linkage
in a graph $G$, and for $1 \le i \le n$ let $(A_i, B_i)$ be a separation of $G$ of order $k$, such
that
1. $A_i \subseteq A_j$ and $B_j \subseteq B_i$ for $1 \le i < j \le n$, and
2. for $1 \le i < n$, there is a linkage $M_i$ in $B_i \cap A_{i+1}$ with $k$ components, each with
one end in $V(A_i \cap B_i)$ and the other in $V(A_{i+1} \cap B_{i+1})$.
Then there exists $i$ with $1 \le i < n$ such that $L \cap B_i \cap A_{i+1} = M_i$." -/
theorem theorem_2_5_proof {α : Type u} {β : Type v} (p k : ℕ)
    (G L : Hypergraph α β)
    (A B : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k)) + 1) → Hypergraph α β)
    (M : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k))) → Hypergraph α β)
    (hL : IsVitalPLinkage G L p)
    (hsep : ∀ r : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k)) + 1),
      G.IsSeparation (A r) (B r) ∧ separationOrder (A r) (B r) = k)
    (hmono : ∀ r₁ r₂ : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k)) + 1),
      r₁ < r₂ → A r₁ ≤ A r₂ ∧ B r₂ ≤ B r₁)
    (hM : ∀ r : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k))),
      IsLinkage (B r.castSucc ∩ A r.succ) (M r) ∧
      (linkagePattern (M r)).ncard = k ∧
      ∀ P ∈ linkagePattern (M r),
        ∃ u ∈ (A r.castSucc ∩ B r.castSucc).vertexSet,
          ∃ w ∈ (A r.succ ∩ B r.succ).vertexSet, P = {u, w}) :
    ∃ r : Fin ((2 * p + 1) * (p + k + 1) ^ (2 * (p + k))),
      L ∩ B r.castSucc ∩ A r.succ = M r :=
  vital_linkage_constant_order_nested_separations hL hsep hmono hM

/-- **Graph Minors XXI, (2.6)** (pages 6–7 of the preprint):
"For all integers $p, k \ge 0$ there exists $n \ge 0$ with the following property. Let $L$ be a
vital $p$-linkage in a graph $G$, and for $1 \le i \le n$ let $(A_i, B_i)$ be a separation of $G$
of order $\le k$, such that ...
1. $A_i \subseteq A_j$ and $B_j \subseteq B_i$, for $1 \le i < j \le n$
2. if $1 \le i < i' \le n$, and $|V(A_i \cap B_i)| = |V(A_{i'} \cap B_{i'})| = k'$ say, and
$|V(A_j \cap B_j)| > k'$ for all $j$ with $i < j < i'$, then there is a linkage $M_{ii'}$ in
$B_i \cap A_{i'}$ with $k'$ components, each with one end in $V(A_i \cap B_i)$ and the other in
$V(A_{i'} \cap B_{i'})$.
Then there exist $i, i'$ as in (ii) such that $L \cap B_i \cap A_{i'} = M_{ii'}$." -/
theorem theorem_2_6_proof (p k : ℕ) :
    ∃ n : ℕ, 2 ≤ n ∧
      ∀ {α : Type u} {β : Type v} (G L : Hypergraph α β)
        (A B : Fin n → Hypergraph α β)
        (M : Fin n → Fin n → Hypergraph α β),
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
            ∃ u ∈ (A i ∩ B i).vertexSet,
              ∃ w ∈ (A i' ∩ B i').vertexSet, P = {u, w}) →
        ∃ i i' : Fin n, i < i' ∧
          separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
          (∀ j : Fin n, i < j → j < i' →
            separationOrder (A i) (B i) < separationOrder (A j) (B j)) ∧
          L ∩ B i ∩ A i' = M i i' :=
  vital_linkage_bounded_order_nested_separations p k

/-- **Graph Minors XXI, (2.7)** (page 8 of the preprint):
"For all integers $p, k \ge 0$ there exists $n \ge 0$ with the following property. Let $L, L'$ be
vital $p$-linkages in a graph $G$, and for $1 \le i \le n$ let $(A_i, B_i)$ be as in (2.6),
satisfying (2.6)(i) and (ii). Then there exist $i, i'$ as in (ii) such that
$L \cap B_i \cap A_{i'} = L' \cap B_i \cap A_{i'} = M_{ii'}$." -/
theorem theorem_2_7_proof {α : Type u} {β : Type v} (p k : ℕ) :
    ∃ n : ℕ, 2 ≤ n ∧
      ∀ (G L L' : Hypergraph α β)
        (A B : Fin n → Hypergraph α β)
        (M : Fin n → Fin n → Hypergraph α β),
        IsVitalPLinkage G L p →
        IsVitalPLinkage G L' p →
        (∀ i : Fin n, G.IsSeparation (A i) (B i) ∧ separationOrder (A i) (B i) ≤ k) →
        (∀ i j : Fin n, i < j → A i ≤ A j ∧ B j ≤ B i) →
        (∀ i i' : Fin n, i < i' →
          separationOrder (A i) (B i) = separationOrder (A i') (B i') →
          (∀ j : Fin n, i < j → j < i' →
            separationOrder (A i) (B i) < separationOrder (A j) (B j)) →
          IsLinkage (B i ∩ A i') (M i i') ∧
          (linkagePattern (M i i')).ncard = separationOrder (A i) (B i) ∧
          ∀ P ∈ linkagePattern (M i i'),
            ∃ u ∈ (A i ∩ B i).vertexSet,
              ∃ w ∈ (A i' ∩ B i').vertexSet, P = {u, w}) →
        ∃ i i' : Fin n, i < i' ∧
          separationOrder (A i) (B i) = separationOrder (A i') (B i') ∧
          (∀ j : Fin n, i < j → j < i' →
            separationOrder (A i) (B i) < separationOrder (A j) (B j)) ∧
          L ∩ B i ∩ A i' = M i i' ∧
          L' ∩ B i ∩ A i' = M i i' :=
  vital_linkages_bounded_order_nested_separations p k

end GM21
end GraphMinor
