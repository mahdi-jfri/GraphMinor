module

public import GraphMinor.Compute.Menger
public import GraphMinor.Compute.Restrict
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Linarith

/-!
# Branch-Decompositions, Graph Separations, and Combinatorics of GM XIII (3.3)

This file develops the plain combinatorial definitions and step-preservation lemmas for
Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, Section 3 (pages 70–75):

1. **Graph separations (`GraphSeparation`):** Plain definition of a separation `(A, B)` of a simple
   graph `G : SimpleGraph (Fin n)` and its order `|V(A ∩ B)|`, following GM XIII Section 2, page 70.
2. **Branch-decompositions (`IsBranchDecompOfWidthLe`) and partial branch-decompositions
   (`IsPartialBranchDecomp`):** Plain definitions of cubic/leaf trees, tree leaves, the order of a
   tree edge `f ∈ E(T)`, and branch-decompositions of width `≤ 3ω`, following GM XIII Section 3,
   pages 70 and 73.
3. **Parent-array trees (`parentTree`):** Concrete representation of trees on `Fin t` via a parent
   map `p : ℕ → ℕ` with `p x < x` for `1 ≤ x < t`, characterization of reachability in `T \ {f}` via
   subtree membership `inSubtree`, and leaf-splitting lemmas.
4. **Correctness of Steps (1)–(6) of Algorithm (3.3):** Preservation of the recursion invariants
   (i)–(iii) and the Menger bridge showing that when Step (4) finds no separation of `R` across all
   valid partitions `(Z₁, Z₂, Z₃)` of `Z`, `G_i` has no separation `(A, B)` of order `≤ ω`
   satisfying `|Z - V(A)|, |Z - V(B)| ≤ (2/3)|Z| - (1/2)|Z ∩ V(A ∩ B)|`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: Graph Separations and the Balance Condition of GM XIII (3.1) & (3.3) -/

/-- A separation `(A, B)` of a simple graph `G : SimpleGraph (Fin n)` on vertex set `V(G) = Fin n`,
as defined in Graph Minors XIII, Section 2, page 69:
"A separation of a graph or digraph $G$ is a pair $(A, B)$ of subgraphs such that $A \cup B = G$ and
$E(A \cap B) = \emptyset$, where for subgraphs $G_1 = (V_1, E_1)$, $G_2 = (V_2, E_2)$ of $G$, $G_1 \cup G_2$ and
$G_1 \cap G_2$ are the subgraphs $(V_1 \cup V_2, E_1 \cup E_2)$ and $(V_1 \cap V_2, E_1 \cap E_2)$, respectively.
The order of the separation $(A, B)$ is $|V(A \cap B)|$." -/
structure GraphSeparation {n : ℕ} (G : SimpleGraph (Fin n)) where
  /-- Vertex set `V(A)` of the first subgraph `A`. -/
  VA : Finset (Fin n)
  /-- Vertex set `V(B)` of the second subgraph `B`. -/
  VB : Finset (Fin n)
  /-- Edge graph `E(A)` of the first subgraph `A`. -/
  EA : SimpleGraph (Fin n)
  /-- Edge graph `E(B)` of the second subgraph `B`. -/
  EB : SimpleGraph (Fin n)
  /-- `V(A) ∪ V(B) = V(G)`. -/
  union_verts : VA ∪ VB = Finset.univ
  /-- `E(A) ⊆ E(G)`. -/
  EA_le : EA ≤ G
  /-- `E(B) ⊆ E(G)`. -/
  EB_le : EB ≤ G
  /-- `E(A) ∪ E(B) = E(G)`. -/
  union_edges : EA ⊔ EB = G
  /-- `E(A ∩ B) = ∅`. -/
  disj_edges : EA ⊓ EB = ⊥
  /-- Every edge of `A` has both endpoints in `V(A)`. -/
  EA_verts : ∀ ⦃u v : Fin n⦄, EA.Adj u v → u ∈ VA ∧ v ∈ VA
  /-- Every edge of `B` has both endpoints in `V(B)`. -/
  EB_verts : ∀ ⦃u v : Fin n⦄, EB.Adj u v → u ∈ VB ∧ v ∈ VB

/-- The order `|V(A ∩ B)|` of a separation `(A, B)` of `G` (GM XIII, Section 2, page 70). -/
def GraphSeparation.order {n : ℕ} {G : SimpleGraph (Fin n)} (sep : GraphSeparation G) : ℕ :=
  (sep.VA ∩ sep.VB).card

/-- The balance condition on a separation `(A, B)` relative to `Z ⊆ V(G)` from GM XIII (3.1) and
(3.3) Step (4) (pages 71 and 73):
`|Z - V(A)|, |Z - V(B)| ≤ (2/3)|Z| - (1/2)|Z ∩ V(A ∩ B)|`, stated over `ℚ`. -/
def GraphSeparation.IsBalancedQ {n : ℕ} {G : SimpleGraph (Fin n)}
    (sep : GraphSeparation G) (Z : Finset (Fin n)) : Prop :=
  ((Z \ sep.VA).card : ℚ) ≤
    (2 / 3 : ℚ) * (Z.card : ℚ) - (1 / 2 : ℚ) * ((Z ∩ (sep.VA ∩ sep.VB)).card : ℚ) ∧
  ((Z \ sep.VB).card : ℚ) ≤
    (2 / 3 : ℚ) * (Z.card : ℚ) - (1 / 2 : ℚ) * ((Z ∩ (sep.VA ∩ sep.VB)).card : ℚ)

/-- Equivalent natural-number formulation of `IsBalancedQ` obtained by clearing denominators (`× 6`). -/
def GraphSeparation.IsBalancedNat {n : ℕ} {G : SimpleGraph (Fin n)}
    (sep : GraphSeparation G) (Z : Finset (Fin n)) : Prop :=
  6 * (Z \ sep.VA).card + 3 * (Z ∩ (sep.VA ∩ sep.VB)).card ≤ 4 * Z.card ∧
  6 * (Z \ sep.VB).card + 3 * (Z ∩ (sep.VA ∩ sep.VB)).card ≤ 4 * Z.card

theorem GraphSeparation.isBalancedQ_iff_isBalancedNat {n : ℕ} {G : SimpleGraph (Fin n)}
    (sep : GraphSeparation G) (Z : Finset (Fin n)) :
    sep.IsBalancedQ Z ↔ sep.IsBalancedNat Z := by
  unfold IsBalancedQ IsBalancedNat
  constructor
  · rintro ⟨hA, hB⟩
    constructor
    · have hA6 : (6 : ℚ) * ((Z \ sep.VA).card : ℚ) +
          (3 : ℚ) * ((Z ∩ (sep.VA ∩ sep.VB)).card : ℚ) ≤ (4 : ℚ) * (Z.card : ℚ) := by
        linarith
      exact_mod_cast hA6
    · have hB6 : (6 : ℚ) * ((Z \ sep.VB).card : ℚ) +
          (3 : ℚ) * ((Z ∩ (sep.VA ∩ sep.VB)).card : ℚ) ≤ (4 : ℚ) * (Z.card : ℚ) := by
        linarith
      exact_mod_cast hB6
  · rintro ⟨hA, hB⟩
    have hAq : (6 : ℚ) * ((Z \ sep.VA).card : ℚ) +
        (3 : ℚ) * ((Z ∩ (sep.VA ∩ sep.VB)).card : ℚ) ≤ (4 : ℚ) * (Z.card : ℚ) := by
      exact_mod_cast hA
    have hBq : (6 : ℚ) * ((Z \ sep.VB).card : ℚ) +
        (3 : ℚ) * ((Z ∩ (sep.VA ∩ sep.VB)).card : ℚ) ≤ (4 : ℚ) * (Z.card : ℚ) := by
      exact_mod_cast hB
    constructor <;> linarith

/-- Every edge of `G` has both endpoints in `V(A)` or both endpoints in `V(B)`. -/
theorem GraphSeparation.adj_endpoints {n : ℕ} {G : SimpleGraph (Fin n)}
    (sep : GraphSeparation G) {u v : Fin n} (hadj : G.Adj u v) :
    (u ∈ sep.VA ∧ v ∈ sep.VA) ∨ (u ∈ sep.VB ∧ v ∈ sep.VB) := by
  rw [← sep.union_edges, sup_adj] at hadj
  rcases hadj with hA | hB
  · exact Or.inl (sep.EA_verts hA)
  · exact Or.inr (sep.EB_verts hB)

/-- No edge of `G` joins a vertex outside `V(B)` to a vertex outside `V(A)`. -/
theorem GraphSeparation.not_adj_sdiff {n : ℕ} {G : SimpleGraph (Fin n)}
    (sep : GraphSeparation G) {u v : Fin n} (hu : u ∉ sep.VB) (hv : v ∉ sep.VA) :
    ¬G.Adj u v := by
  intro hadj
  rcases sep.adj_endpoints hadj with ⟨_, hvA⟩ | ⟨huB, _⟩
  · exact hv hvA
  · exact hu huB

/-- Every walk in `G` starting in `V(A)` and ending in `V(B)` contains a vertex of `V(A) ∩ V(B)`. -/
theorem GraphSeparation.walk_hits_inter {n : ℕ} {G : SimpleGraph (Fin n)}
    (sep : GraphSeparation G) {u v : Fin n} (w : G.Walk u v)
    (hu : u ∈ sep.VA) (hv : v ∈ sep.VB) :
    ∃ z ∈ sep.VA ∩ sep.VB, z ∈ w.support := by
  induction w with
  | nil =>
    rename_i u
    exact ⟨u, Finset.mem_inter.mpr ⟨hu, hv⟩, by simp⟩
  | @cons x y v hadj tail ih =>
    by_cases hxB : x ∈ sep.VB
    · exact ⟨x, Finset.mem_inter.mpr ⟨hu, hxB⟩, by simp⟩
    · have hyA : y ∈ sep.VA := by
        rcases sep.adj_endpoints hadj with ⟨_, hyA⟩ | ⟨hxB', _⟩
        · exact hyA
        · exact False.elim (hxB hxB')
      rcases ih hyA hv with ⟨z, hz_inter, hz_supp⟩
      exact ⟨z, hz_inter, by simp [hz_supp]⟩

/-! ### Section 2: Plain Definitions of Branch-Decomposition and Partial Branch-Decomposition -/

/-- The set of leaves (vertices of degree `1`) of a simple graph `T : SimpleGraph (Fin t)`.
In GM XIII, Section 3, page 70: "(The *leaves* of $T$ are the vertices with valency 1.)" -/
def treeLeaves {t : ℕ} (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] : Finset (Fin t) :=
  Finset.univ.filter (fun v : Fin t => T.degree v = 1)

@[simp]
theorem mem_treeLeaves {t : ℕ} (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (v : Fin t) :
    v ∈ treeLeaves T ↔ T.degree v = 1 := by
  simp [treeLeaves]

/-- Condition (i) of a branch-decomposition (GM XIII, Section 3, page 70):
"$T$ is a tree and every vertex of $T$ has valency 1 or 3". -/
def IsCubicOrLeafTree {t : ℕ} (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] : Prop :=
  T.IsTree ∧ ∀ v : Fin t, T.degree v = 1 ∨ T.degree v = 3

/-- The set of vertices of `G` that contribute to the order of an edge `f` of `T` under `τ`:
vertices `w` of `G` incident with an edge `e₁ ∈ E(G)` and an edge `e₂ ∈ E(G)` such that `τ(e₁)`
and `τ(e₂)` lie in different connected components of `T \ f`
(GM XIII, Section 3, page 70 and page 73). -/
noncomputable def treeEdgeCutVerts {n t : ℕ} (G : SimpleGraph (Fin n))
    (T : SimpleGraph (Fin t)) (τ : Sym2 (Fin n) → Fin t) (f : Sym2 (Fin t)) :
    Finset (Fin n) :=
  open Classical in
  Finset.univ.filter (fun w : Fin n =>
    ∃ e₁ ∈ G.edgeFinset, ∃ e₂ ∈ G.edgeFinset,
      w ∈ e₁ ∧ w ∈ e₂ ∧ ¬(T.deleteEdges {f}).Reachable (τ e₁) (τ e₂))

@[simp]
theorem mem_treeEdgeCutVerts {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : SimpleGraph (Fin t)) (τ : Sym2 (Fin n) → Fin t) (f : Sym2 (Fin t)) (w : Fin n) :
    w ∈ treeEdgeCutVerts G T τ f ↔
      ∃ e₁ ∈ G.edgeFinset, ∃ e₂ ∈ G.edgeFinset,
        w ∈ e₁ ∧ w ∈ e₂ ∧ ¬(T.deleteEdges {f}).Reachable (τ e₁) (τ e₂) := by
  classical
  unfold treeEdgeCutVerts
  convert Finset.mem_filter.trans (and_iff_right (Finset.mem_univ w))

/-- The order of an edge `f ∈ E(T)` in `(T, τ)` (GM XIII, Section 3, pages 70 and 73). -/
noncomputable def treeEdgeOrder {n t : ℕ} (G : SimpleGraph (Fin n))
    (T : SimpleGraph (Fin t)) (τ : Sym2 (Fin n) → Fin t) (f : Sym2 (Fin t)) : ℕ :=
  (treeEdgeCutVerts G T τ f).card

/-- A branch-decomposition `(T, τ)` of `G` in which every edge of `T` has order `≤ B`, as defined
in Graph Minors XIII, Section 3, page 70:
(i) `T` is a tree and every vertex of `T` has valency 1 or 3;
(ii) `τ` is a bijection from `E(G)` to the set of leaves of `T`;
and every edge `f ∈ E(T)` has order `≤ B`. -/
def IsBranchDecompOfWidthLe {n t : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (τ : Sym2 (Fin n) → Fin t) : Prop :=
  IsCubicOrLeafTree T ∧
  Set.BijOn τ (G.edgeFinset : Set (Sym2 (Fin n))) (treeLeaves T : Set (Fin t)) ∧
  ∀ f ∈ T.edgeFinset, treeEdgeOrder G T τ f ≤ B

/-- The recursion invariant (ii)–(iii) of Algorithm (3.3) (GM XIII, Section 3, page 73):
(ii) a tree `T_i` each vertex of which has valency 1 or 3;
(iii) a surjection `τ_i` from `E(G_i)` to the set of leaves of `T_i`, such that each edge of `T_i`
has order `≤ 3ω`. -/
def IsPartialBranchDecomp {n t : ℕ} (ω : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj] (τ : Sym2 (Fin n) → Fin t) : Prop :=
  IsCubicOrLeafTree T ∧
  (∀ e ∈ G.edgeFinset, τ e ∈ treeLeaves T) ∧
  (∀ v ∈ treeLeaves T, ∃ e ∈ G.edgeFinset, τ e = v) ∧
  (∀ f ∈ T.edgeFinset, treeEdgeOrder G T τ f ≤ 3 * ω)

/-- Step (1) of Algorithm (3.3): when `|E(G_i)| ≤ |Leaves(T_i)|`, any partial branch-decomposition
`(T_i, τ_i)` of `G_i` has `τ_i` a bijection from `E(G_i)` to the leaves of `T_i`, hence is a
branch-decomposition of `G_i` of width `≤ 3ω`. -/
theorem IsPartialBranchDecomp.to_isBranchDecompOfWidthLe {n t : ℕ} {ω : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Sym2 (Fin n) → Fin t}
    (hpart : IsPartialBranchDecomp ω G T τ)
    (hcard : G.edgeFinset.card ≤ (treeLeaves T).card) :
    IsBranchDecompOfWidthLe (3 * ω) G T τ := by
  classical
  rcases hpart with ⟨htree, hmaps, hsurj, hord⟩
  have hmaps_set : Set.MapsTo τ (G.edgeFinset : Set (Sym2 (Fin n))) (treeLeaves T : Set (Fin t)) :=
    fun e he => hmaps e he
  have hsurj_set : Set.SurjOn τ (G.edgeFinset : Set (Sym2 (Fin n))) (treeLeaves T : Set (Fin t)) :=
    fun v hv => hsurj v hv
  have hsub : treeLeaves T ⊆ G.edgeFinset.image τ := by
    intro v hv
    rcases hsurj v hv with ⟨e, he, rfl⟩
    exact Finset.mem_image_of_mem τ he
  have hcard_im : (G.edgeFinset.image τ).card = G.edgeFinset.card := by
    have h1 : (treeLeaves T).card ≤ (G.edgeFinset.image τ).card := Finset.card_le_card hsub
    have h2 : (G.edgeFinset.image τ).card ≤ G.edgeFinset.card := Finset.card_image_le
    omega
  have hinj_set : Set.InjOn τ (G.edgeFinset : Set (Sym2 (Fin n))) :=
    Finset.injOn_of_card_image_eq hcard_im
  exact ⟨htree, ⟨hmaps_set, hinj_set, hsurj_set⟩, hord⟩

/-- Deleting an edge from `G` can only shrink `treeEdgeCutVerts`. -/
theorem treeEdgeOrder_mono_subgraph {n t : ℕ} {G₁ G₂ : SimpleGraph (Fin n)}
    (hle : G₁ ≤ G₂) (T : SimpleGraph (Fin t)) (τ : Sym2 (Fin n) → Fin t) (f : Sym2 (Fin t)) :
    treeEdgeOrder G₁ T τ f ≤ treeEdgeOrder G₂ T τ f := by
  classical
  apply Finset.card_le_card
  intro w hw
  rw [mem_treeEdgeCutVerts] at hw ⊢
  rcases hw with ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
  exact ⟨e₁, edgeFinset_mono hle he₁, e₂, edgeFinset_mono hle he₂, hw₁, hw₂, hnr⟩

/-! ### Section 3: Parent-Array Trees (`parentTree`) and Subtree Reachability -/

/-- A simple graph on `Fin t` defined by a parent function `p : ℕ → ℕ`: vertices `u` and `v` are
adjacent if and only if `u > 0` and `v = p u` (with `p u ≠ u`), or `v > 0` and `u = p v` (with
`p v ≠ v`). When `p x < x` for all `1 ≤ x < t`, this defines a tree rooted at `0`. -/
def parentTree (t : ℕ) (p : ℕ → ℕ) : SimpleGraph (Fin t) where
  Adj u v := u ≠ v ∧ ((0 < u.1 ∧ v.1 = p u.1) ∨ (0 < v.1 ∧ u.1 = p v.1))
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

instance instDecidableRelParentTreeAdj (t : ℕ) (p : ℕ → ℕ) :
    DecidableRel (parentTree t p).Adj :=
  fun u v => inferInstanceAs
    (Decidable (u ≠ v ∧ ((0 < u.1 ∧ v.1 = p u.1) ∨ (0 < v.1 ∧ u.1 = p v.1))))

theorem parentTree_adj_of_lt {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ x, 0 < x → x < t → p x < x) {u v : Fin t} :
    (parentTree t p).Adj u v ↔
      (0 < u.1 ∧ v.1 = p u.1) ∨ (0 < v.1 ∧ u.1 = p v.1) := by
  unfold parentTree
  simp only [ne_eq, Fin.ext_iff]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rcases h with ⟨hu, hvp⟩ | ⟨hv, hup⟩
    · have := hp u.1 hu u.2; omega
    · have := hp v.1 hv v.2; omega

/-- Every vertex in `parentTree t p` is reachable from vertex `0` when `p x < x` for all `x > 0`. -/
theorem parentTree_reachable_zero {t : ℕ} {p : ℕ → ℕ} (ht : 0 < t)
    (hp : ∀ x, 0 < x → x < t → p x < x) (u : Fin t) :
    (parentTree t p).Reachable ⟨0, ht⟩ u := by
  suffices ∀ k (u : Fin t), u.1 < k → (parentTree t p).Reachable ⟨0, ht⟩ u from
    this (u.1 + 1) u (by omega)
  intro k
  induction k with
  | zero => intro u hu; omega
  | succ k ih =>
    intro u hu_lt
    by_cases hu0 : u.1 = 0
    · have heq : u = ⟨0, ht⟩ := Fin.ext hu0
      rw [heq]
    · have hu_pos : 0 < u.1 := by omega
      have hpu_lt : p u.1 < u.1 := hp u.1 hu_pos u.2
      let pu : Fin t := ⟨p u.1, by omega⟩
      have hadj : (parentTree t p).Adj pu u := by
        rw [parentTree_adj_of_lt hp]
        exact Or.inr ⟨hu_pos, rfl⟩
      exact (ih pu (by dsimp [pu]; omega)).trans hadj.reachable

theorem parentTree_connected {t : ℕ} {p : ℕ → ℕ} (ht : 0 < t)
    (hp : ∀ x, 0 < x → x < t → p x < x) :
    (parentTree t p).Connected := by
  have : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  refine Connected.mk fun u v => ?_
  exact (parentTree_reachable_zero ht hp u).symm.trans (parentTree_reachable_zero ht hp v)

/-- The edges of `parentTree t p` are in bijection with `{x : Fin t | 0 < x.1}` via
`x ↦ s(⟨p x.1, _⟩, x)`. -/
theorem parentTree_card_edgeFinset {t : ℕ} {p : ℕ → ℕ} (ht : 0 < t)
    (hp : ∀ x, 0 < x → x < t → p x < x) :
    (parentTree t p).edgeFinset.card + 1 = t := by
  have hpos_card : (Finset.univ.filter (fun x : Fin t => 0 < x.1)).card + 1 = t := by
    have hcomp :
        (Finset.univ.filter (fun x : Fin t => 0 < x.1)).card +
          (Finset.univ.filter (fun x : Fin t => ¬0 < x.1)).card = t := by
      have h1 := Finset.card_filter_add_card_filter_not (fun x : Fin t => 0 < x.1)
        (s := (Finset.univ : Finset (Fin t)))
      simpa using h1
    have hzero :
        Finset.univ.filter (fun x : Fin t => ¬0 < x.1) = ({⟨0, ht⟩} : Finset (Fin t)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Nat.le_zero,
        Finset.mem_singleton, Fin.ext_iff]
    rw [hzero, Finset.card_singleton] at hcomp
    exact hcomp
  suffices hbij :
      (parentTree t p).edgeFinset.card =
        (Finset.univ.filter (fun x : Fin t => 0 < x.1)).card by
    omega
  symm
  refine Finset.card_bij
    (fun (x : Fin t) (hx : x ∈ Finset.univ.filter (fun x : Fin t => 0 < x.1)) =>
      have hx_pos : 0 < x.1 := (Finset.mem_filter.mp hx).2
      have hpx_lt : p x.1 < t := Nat.lt_trans (hp x.1 hx_pos x.2) x.2
      s(⟨p x.1, hpx_lt⟩, x))
    ?_ ?_ ?_
  · intro x hx
    have hx_pos : 0 < x.1 := (Finset.mem_filter.mp hx).2
    rw [mem_edgeFinset, mem_edgeSet, parentTree_adj_of_lt hp]
    exact Or.inr ⟨hx_pos, rfl⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    have hx₁_pos : 0 < x₁.1 := (Finset.mem_filter.mp hx₁).2
    have hx₂_pos : 0 < x₂.1 := (Finset.mem_filter.mp hx₂).2
    have hp₁ : p x₁.1 < x₁.1 := hp x₁.1 hx₁_pos x₁.2
    have hp₂ : p x₂.1 < x₂.1 := hp x₂.1 hx₂_pos x₂.2
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · have h1' : p x₁.1 = x₂.1 := congrArg Fin.val h1
      have h2' : x₁.1 = p x₂.1 := congrArg Fin.val h2
      omega
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeFinset, mem_edgeSet, parentTree_adj_of_lt hp] at he
      rcases he with ⟨hu_pos, hvp⟩ | ⟨hv_pos, hup⟩
      · refine ⟨u, by simp [hu_pos], ?_⟩
        dsimp
        have hv_eq : (⟨p u.1, Nat.lt_trans (hp u.1 hu_pos u.2) u.2⟩ : Fin t) = v :=
          Fin.ext hvp.symm
        rw [hv_eq, Sym2.eq_swap]
      · refine ⟨v, by simp [hv_pos], ?_⟩
        dsimp
        have hu_eq : (⟨p v.1, Nat.lt_trans (hp v.1 hv_pos v.2) v.2⟩ : Fin t) = u :=
          Fin.ext hup.symm
        rw [hu_eq]

/-- Whenever `0 < t` and `p x < x` for all `0 < x < t`, `parentTree t p` is a tree. -/
theorem parentTree_isTree {t : ℕ} {p : ℕ → ℕ} (ht : 0 < t)
    (hp : ∀ x, 0 < x → x < t → p x < x) :
    (parentTree t p).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨parentTree_connected ht hp, ?_⟩
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact parentTree_card_edgeFinset ht hp

/-- Subtree membership test in a parent-array tree `p` (where `p y < y` for `y > 0`):
`inSubtree p x y` returns `true` if and only if `y` lies in the subtree rooted at `x > 0` (that is,
ascending parent pointers from `y` visits `x`). -/
def inSubtree (p : ℕ → ℕ) (x : ℕ) : ℕ → Bool
  | 0 => x == 0
  | y + 1 =>
    if y + 1 == x then true
    else if p (y + 1) < y + 1 then inSubtree p x (p (y + 1))
    else false
termination_by y => y

theorem inSubtree_self (p : ℕ → ℕ) (x : ℕ) : inSubtree p x x = true := by
  cases x with
  | zero => simp [inSubtree]
  | succ x' => simp [inSubtree]

theorem inSubtree_zero_of_pos (p : ℕ → ℕ) {x : ℕ} (hx : 0 < x) :
    inSubtree p x 0 = false := by
  unfold inSubtree
  simp [Nat.ne_of_gt hx]

theorem inSubtree_step {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z)
    {x y : ℕ} (hy_pos : 0 < y) (hy_lt : y < t) (hyx : y ≠ x) :
    inSubtree p x y = inSubtree p x (p y) := by
  obtain ⟨y', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hy_pos)
  have hpy : p (y' + 1) < y' + 1 := hp (y' + 1) hy_pos hy_lt
  conv_lhs => unfold inSubtree
  simp [hyx, hpy]

/-- For `x > 0`, deleting the tree edge `e_x = s(⟨p x, _⟩, ⟨x, _⟩)` from `parentTree t p` preserves
`inSubtree p x` along all remaining edges. -/
theorem inSubtree_eq_of_adj_deleteEdge {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z)
    {x : Fin t} (hx_pos : 0 < x.1) :
    let px : Fin t := ⟨p x.1, Nat.lt_trans (hp x.1 hx_pos x.2) x.2⟩
    ∀ {u v : Fin t},
      ((parentTree t p).deleteEdges {s(px, x)}).Adj u v →
      inSubtree p x.1 u.1 = inSubtree p x.1 v.1 := by
  intro px u v hadj
  rw [deleteEdges_adj, Set.mem_singleton_iff] at hadj
  rcases hadj with ⟨hadj_T, hne_edge⟩
  rw [parentTree_adj_of_lt hp] at hadj_T
  rcases hadj_T with ⟨hu_pos, hvp⟩ | ⟨hv_pos, hup⟩
  · have hux : u.1 ≠ x.1 := by
      intro hux_eq
      apply hne_edge
      have hu_eq : u = x := Fin.ext hux_eq
      have hv_eq : v = px := Fin.ext (hvp.trans (congrArg p hux_eq))
      rw [hu_eq, hv_eq, Sym2.eq_swap]
    rw [inSubtree_step hp hu_pos u.2 hux, hvp]
  · have hvx : v.1 ≠ x.1 := by
      intro hvx_eq
      apply hne_edge
      have hv_eq : v = x := Fin.ext hvx_eq
      have hu_eq : u = px := Fin.ext (hup.trans (congrArg p hvx_eq))
      rw [hu_eq, hv_eq]
    rw [inSubtree_step hp hv_pos v.2 hvx, hup]

theorem inSubtree_eq_of_reachable_deleteEdge {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z)
    {x : Fin t} (hx_pos : 0 < x.1) :
    let px : Fin t := ⟨p x.1, Nat.lt_trans (hp x.1 hx_pos x.2) x.2⟩
    ∀ {u v : Fin t},
      ((parentTree t p).deleteEdges {s(px, x)}).Reachable u v →
      inSubtree p x.1 u.1 = inSubtree p x.1 v.1 := by
  intro px u v hreach
  rcases hreach with ⟨w⟩
  induction w with
  | nil => rfl
  | @cons a b c hadj tail ih =>
    exact (inSubtree_eq_of_adj_deleteEdge hp hx_pos hadj).trans ih

/-- Every vertex `y` with `inSubtree p x.1 y.1 = true` reaches `x` in
`(parentTree t p).deleteEdges {s(px, x)}`. -/
theorem reachable_root_of_inSubtree_true {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z)
    {x : Fin t} (hx_pos : 0 < x.1) (y : Fin t) (hy : inSubtree p x.1 y.1 = true) :
    let px : Fin t := ⟨p x.1, Nat.lt_trans (hp x.1 hx_pos x.2) x.2⟩
    ((parentTree t p).deleteEdges {s(px, x)}).Reachable x y := by
  intro px
  suffices ∀ k (y : Fin t), y.1 < k → inSubtree p x.1 y.1 = true →
      ((parentTree t p).deleteEdges {s(px, x)}).Reachable x y from
    this (y.1 + 1) y (by omega) hy
  intro k
  induction k with
  | zero => intro y hy_lt _; omega
  | succ k ih =>
    intro y hy_lt hy_sub
    by_cases hyx : y.1 = x.1
    · have heq : y = x := Fin.ext hyx
      rw [heq]
    · by_cases hy0 : y.1 = 0
      · rw [hy0, inSubtree_zero_of_pos p hx_pos] at hy_sub
        cases hy_sub
      · have hy_pos : 0 < y.1 := by omega
        have hpy_lt : p y.1 < y.1 := hp y.1 hy_pos y.2
        have hy_step := inSubtree_step hp hy_pos y.2 hyx
        rw [hy_sub] at hy_step
        let py : Fin t := ⟨p y.1, by omega⟩
        have hreach_py := ih py (by dsimp [py]; omega) hy_step.symm
        have hadj_del : ((parentTree t p).deleteEdges {s(px, x)}).Adj py y := by
          rw [deleteEdges_adj, Set.mem_singleton_iff, parentTree_adj_of_lt hp]
          refine ⟨Or.inr ⟨hy_pos, rfl⟩, ?_⟩
          intro heq
          rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
          · exact hyx (congrArg Fin.val h)
          · have : p y.1 = x.1 := congrArg Fin.val h1
            have : y.1 = p x.1 := congrArg Fin.val h2
            have := hp x.1 hx_pos x.2
            omega
        exact hreach_py.trans hadj_del.reachable

/-- Every vertex `y` with `inSubtree p x.1 y.1 = false` reaches `0` in
`(parentTree t p).deleteEdges {s(px, x)}`. -/
theorem reachable_zero_of_inSubtree_false {t : ℕ} {p : ℕ → ℕ} (ht : 0 < t)
    (hp : ∀ z, 0 < z → z < t → p z < z)
    {x : Fin t} (hx_pos : 0 < x.1) (y : Fin t) (hy : inSubtree p x.1 y.1 = false) :
    let px : Fin t := ⟨p x.1, Nat.lt_trans (hp x.1 hx_pos x.2) x.2⟩
    ((parentTree t p).deleteEdges {s(px, x)}).Reachable ⟨0, ht⟩ y := by
  intro px
  suffices ∀ k (y : Fin t), y.1 < k → inSubtree p x.1 y.1 = false →
      ((parentTree t p).deleteEdges {s(px, x)}).Reachable ⟨0, ht⟩ y from
    this (y.1 + 1) y (by omega) hy
  intro k
  induction k with
  | zero => intro y hy_lt _; omega
  | succ k ih =>
    intro y hy_lt hy_sub
    by_cases hy0 : y.1 = 0
    · have heq : y = ⟨0, ht⟩ := Fin.ext hy0
      rw [heq]
    · have hy_pos : 0 < y.1 := by omega
      have hyx : y.1 ≠ x.1 := by
        intro h
        rw [h, inSubtree_self] at hy_sub
        cases hy_sub
      have hpy_lt : p y.1 < y.1 := hp y.1 hy_pos y.2
      have hy_step := inSubtree_step hp hy_pos y.2 hyx
      rw [hy_sub] at hy_step
      let py : Fin t := ⟨p y.1, by omega⟩
      have hreach_py := ih py (by dsimp [py]; omega) hy_step.symm
      have hadj_del : ((parentTree t p).deleteEdges {s(px, x)}).Adj py y := by
        rw [deleteEdges_adj, Set.mem_singleton_iff, parentTree_adj_of_lt hp]
        refine ⟨Or.inr ⟨hy_pos, rfl⟩, ?_⟩
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact hyx (congrArg Fin.val h)
        · have : p y.1 = x.1 := congrArg Fin.val h1
          have : y.1 = p x.1 := congrArg Fin.val h2
          have := hp x.1 hx_pos x.2
          omega
      exact hreach_py.trans hadj_del.reachable

/-- Exact characterization of reachability after deleting tree edge `s(px, x)` from `parentTree t p`:
two vertices `u, v` are in the same component of `(parentTree t p) \ s(px, x)` if and only if
`inSubtree p x.1 u.1 = inSubtree p x.1 v.1`. -/
theorem parentTree_deleteEdge_reachable_iff {t : ℕ} {p : ℕ → ℕ} (ht : 0 < t)
    (hp : ∀ z, 0 < z → z < t → p z < z)
    {x : Fin t} (hx_pos : 0 < x.1) (u v : Fin t) :
    ((parentTree t p).deleteEdges
      {s(⟨p x.1, Nat.lt_trans (hp x.1 hx_pos x.2) x.2⟩, x)}).Reachable u v ↔
      inSubtree p x.1 u.1 = inSubtree p x.1 v.1 := by
  constructor
  · exact inSubtree_eq_of_reachable_deleteEdge hp hx_pos
  · intro heq
    cases hu : inSubtree p x.1 u.1
    · have hv : inSubtree p x.1 v.1 = false := by rw [← heq, hu]
      exact (reachable_zero_of_inSubtree_false ht hp hx_pos u hu).symm.trans
        (reachable_zero_of_inSubtree_false ht hp hx_pos v hv)
    · have hv : inSubtree p x.1 v.1 = true := by rw [← heq, hu]
      exact (reachable_root_of_inSubtree_true hp hx_pos u hu).symm.trans
        (reachable_root_of_inSubtree_true hp hx_pos v hv)

/-! ### Section 4: Initial 2-Vertex Tree and Splitting a Leaf in `parentTree` -/

/-- Every edge of `parentTree t p` has the form `s(⟨p x.1, _⟩, x)` for some `x : Fin t` with `0 < x.1`. -/
theorem exists_pos_of_mem_edgeFinset_parentTree {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z)
    {f : Sym2 (Fin t)} (hf : f ∈ (parentTree t p).edgeFinset) :
    ∃ (x : Fin t) (hx_pos : 0 < x.1),
      f = s(⟨p x.1, Nat.lt_trans (hp x.1 hx_pos x.2) x.2⟩, x) := by
  induction f using Sym2.ind with
  | _ u v =>
    rw [mem_edgeFinset, mem_edgeSet, parentTree_adj_of_lt hp] at hf
    rcases hf with ⟨hu_pos, hvp⟩ | ⟨hv_pos, hup⟩
    · refine ⟨u, hu_pos, ?_⟩
      have hv_eq : (⟨p u.1, Nat.lt_trans (hp u.1 hu_pos u.2) u.2⟩ : Fin t) = v := Fin.ext hvp.symm
      rw [hv_eq, Sym2.eq_swap]
    · refine ⟨v, hv_pos, ?_⟩
      have hu_eq : (⟨p v.1, Nat.lt_trans (hp v.1 hv_pos v.2) v.2⟩ : Fin t) = u := Fin.ext hup.symm
      rw [hu_eq]

/-- If `x : Fin t` has `0 < x.1` and no child in `parentTree t p` (that is, `p z ≠ x.1` for all
`0 < z < t`), then `inSubtree p x.1 y = (y == x.1)` for all `y < t`. -/
theorem inSubtree_of_no_children {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z)
    {x : ℕ} (hx_pos : 0 < x) (hx_lt : x < t)
    (hno_child : ∀ z, 0 < z → z < t → p z ≠ x) :
    ∀ y < t, inSubtree p x y = (y == x) := by
  suffices ∀ k y, y < k → y < t → inSubtree p x y = (y == x) from
    fun y hy => this (y + 1) y (by omega) hy
  intro k
  induction k with
  | zero => intro y hy _; omega
  | succ k ih =>
    intro y hy_k hy_t
    by_cases hyx : y = x
    · subst hyx
      simp [inSubtree_self]
    · by_cases hy0 : y = 0
      · subst hy0
        rw [inSubtree_zero_of_pos p hx_pos]
        simp [Nat.ne_of_lt hx_pos]
      · have hy_pos : 0 < y := by omega
        have hpy_lt : p y < y := hp y hy_pos hy_t
        have hpy_ne : p y ≠ x := hno_child y hy_pos hy_t
        rw [inSubtree_step hp hy_pos hy_t hyx]
        rw [ih (p y) (by omega) (by omega)]
        simp [hyx, hpy_ne]

/-- Extending parent function `p` when splitting leaf `v < t` into two new leaves `t` and `t + 1`. -/
def splitLeafParent (p : ℕ → ℕ) (t v : ℕ) (x : ℕ) : ℕ :=
  if x = t ∨ x = t + 1 then v else p x

theorem splitLeafParent_lt {t v : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (hv_lt : v < t) :
    ∀ z, 0 < z → z < t + 2 → splitLeafParent p t v z < z := by
  intro z hz_pos hz_lt
  unfold splitLeafParent
  split_ifs with h
  · omega
  · exact hp z hz_pos (by omega)

theorem inSubtree_splitLeafParent_of_lt {t v : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (hv_lt : v < t)
    {x : ℕ} (hx_lt : x < t) :
    ∀ y < t, inSubtree (splitLeafParent p t v) x y = inSubtree p x y := by
  suffices ∀ k y, y < k → y < t → inSubtree (splitLeafParent p t v) x y = inSubtree p x y from
    fun y hy => this (y + 1) y (by omega) hy
  intro k
  induction k with
  | zero => intro y hy _; omega
  | succ k ih =>
    intro y hy_k hy_t
    by_cases hyx : y = x
    · subst hyx
      simp [inSubtree_self]
    · by_cases hy0 : y = 0
      · subst hy0
        simp [inSubtree]
      · have hy_pos : 0 < y := by omega
        have hp' : ∀ z, 0 < z → z < t + 2 → splitLeafParent p t v z < z :=
          splitLeafParent_lt hp hv_lt
        rw [inSubtree_step hp' hy_pos (by omega) hyx, inSubtree_step hp hy_pos hy_t hyx]
        have hsplit_y : splitLeafParent p t v y = p y := by
          simp [splitLeafParent, show y ≠ t by omega, show y ≠ t + 1 by omega]
        rw [hsplit_y]
        have hpy_lt : p y < y := hp y hy_pos hy_t
        exact ih (p y) (by omega) (by omega)

theorem inSubtree_splitLeafParent_left {t v : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (ht : 0 < t) (hv_lt : v < t)
    {x : ℕ} (hx_lt : x < t) :
    inSubtree (splitLeafParent p t v) x t = inSubtree p x v := by
  have hp' := splitLeafParent_lt hp hv_lt
  rw [inSubtree_step hp' ht (by omega) (by omega)]
  have hsplit_t : splitLeafParent p t v t = v := by simp [splitLeafParent]
  rw [hsplit_t]
  exact inSubtree_splitLeafParent_of_lt hp hv_lt hx_lt v hv_lt

theorem inSubtree_splitLeafParent_right {t v : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (hv_lt : v < t)
    {x : ℕ} (hx_lt : x < t) :
    inSubtree (splitLeafParent p t v) x (t + 1) = inSubtree p x v := by
  have hp' := splitLeafParent_lt hp hv_lt
  rw [inSubtree_step hp' (by omega) (by omega) (by omega)]
  have hsplit_t1 : splitLeafParent p t v (t + 1) = v := by simp [splitLeafParent]
  rw [hsplit_t1]
  exact inSubtree_splitLeafParent_of_lt hp hv_lt hx_lt v hv_lt

theorem inSubtree_splitLeafParent_new_left {t v : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (ht : 0 < t) (hv_lt : v < t) :
    ∀ y < t + 2, inSubtree (splitLeafParent p t v) t y = (y == t) := by
  apply inSubtree_of_no_children (splitLeafParent_lt hp hv_lt) ht (by omega)
  intro z hz_pos hz_lt
  unfold splitLeafParent
  split_ifs with h
  · omega
  · have := hp z hz_pos (by omega)
    omega

theorem inSubtree_splitLeafParent_new_right {t v : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (hv_lt : v < t) :
    ∀ y < t + 2, inSubtree (splitLeafParent p t v) (t + 1) y = (y == t + 1) := by
  apply inSubtree_of_no_children (splitLeafParent_lt hp hv_lt) (by omega) (by omega)
  intro z hz_pos hz_lt
  unfold splitLeafParent
  split_ifs with h
  · omega
  · have := hp z hz_pos (by omega)
    omega

/-- In the initial 2-vertex tree `parentTree 2 (fun _ => 0)`, both vertices `0` and `1` have
degree `1`. -/
theorem degree_parentTree_two (v : Fin 2) :
    (parentTree 2 (fun _ => 0)).degree v = 1 := by
  fin_cases v <;> decide

theorem isCubicOrLeafTree_parentTree_two :
    IsCubicOrLeafTree (parentTree 2 (fun _ => 0)) := by
  refine ⟨parentTree_isTree (by omega) (fun x hx hlt => by omega), fun v => ?_⟩
  exact Or.inl (degree_parentTree_two v)

theorem treeLeaves_parentTree_two :
    treeLeaves (parentTree 2 (fun _ => 0)) = Finset.univ := by
  ext v
  simp [treeLeaves, degree_parentTree_two]

/-- Embedding `Fin t ↪ Fin (t + 2)` for comparing neighbor finsets when splitting a leaf. -/
def finCastAddTwo (t : ℕ) : Fin t ↪ Fin (t + 2) where
  toFun u := ⟨u.1, by omega⟩
  inj' _ _ h := Fin.ext (Fin.mk.inj h)

@[simp]
theorem finCastAddTwo_val (t : ℕ) (u : Fin t) : (finCastAddTwo t u).1 = u.1 := rfl

/-- Neighbor finset of `⟨u.1, _⟩` (`u ≠ v`) in `parentTree (t + 2) (splitLeafParent p t v.1)`. -/
theorem neighborFinset_splitLeafParent_of_ne {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) {v u : Fin t} (hne : u ≠ v) :
    (parentTree (t + 2) (splitLeafParent p t v.1)).neighborFinset ⟨u.1, by omega⟩ =
      ((parentTree t p).neighborFinset u).map (finCastAddTwo t) := by
  have hp' := splitLeafParent_lt hp v.2
  have hne_val : u.1 ≠ v.1 := fun h => hne (Fin.ext h)
  ext w
  simp only [mem_neighborFinset, Finset.mem_map, Fin.ext_iff, finCastAddTwo_val]
  rw [parentTree_adj_of_lt hp']
  dsimp only
  constructor
  · rintro (⟨hu_pos, hwp⟩ | ⟨hw_pos, hup⟩)
    · have hsplit_u : splitLeafParent p t v.1 u.1 = p u.1 := by
        simp [splitLeafParent, show u.1 ≠ t by omega, show u.1 ≠ t + 1 by omega]
      rw [hsplit_u] at hwp
      have hw_lt : w.1 < t := by
        have := hp u.1 hu_pos u.2; omega
      refine ⟨⟨w.1, hw_lt⟩, ?_, rfl⟩
      rw [parentTree_adj_of_lt hp]
      exact Or.inl ⟨hu_pos, hwp⟩
    · have hw_lt : w.1 < t := by
        by_contra hge
        have hsplit_w : splitLeafParent p t v.1 w.1 = v.1 := by
          unfold splitLeafParent; split_ifs with h <;> omega
        rw [hsplit_w] at hup
        exact hne_val hup
      have hsplit_w : splitLeafParent p t v.1 w.1 = p w.1 := by
        simp [splitLeafParent, show w.1 ≠ t by omega, show w.1 ≠ t + 1 by omega]
      rw [hsplit_w] at hup
      refine ⟨⟨w.1, hw_lt⟩, ?_, rfl⟩
      rw [parentTree_adj_of_lt hp]
      exact Or.inr ⟨hw_pos, hup⟩
  · rintro ⟨w₀, hw₀, hw_eq⟩
    rw [parentTree_adj_of_lt hp] at hw₀
    rcases hw₀ with ⟨hu_pos, hwp⟩ | ⟨hw_pos, hup⟩
    · left
      refine ⟨hu_pos, ?_⟩
      have hsplit_u : splitLeafParent p t v.1 u.1 = p u.1 := by
        simp [splitLeafParent, show u.1 ≠ t by omega, show u.1 ≠ t + 1 by omega]
      rw [hsplit_u, ← hw_eq, hwp]
    · right
      refine ⟨by omega, ?_⟩
      have hsplit_w : splitLeafParent p t v.1 w.1 = p w₀.1 := by
        rw [← hw_eq]
        simp [splitLeafParent, show w₀.1 ≠ t by omega, show w₀.1 ≠ t + 1 by omega]
      rw [hsplit_w, hup]

/-- Neighbor finset of `⟨v.1, _⟩` in `parentTree (t + 2) (splitLeafParent p t v.1)`. -/
theorem neighborFinset_splitLeafParent_self {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (v : Fin t) :
    (parentTree (t + 2) (splitLeafParent p t v.1)).neighborFinset ⟨v.1, by omega⟩ =
      insert ⟨t, by omega⟩ (insert ⟨t + 1, by omega⟩
        (((parentTree t p).neighborFinset v).map (finCastAddTwo t))) := by
  have ht : 0 < t := Nat.zero_lt_of_lt v.2
  have hp' := splitLeafParent_lt hp v.2
  ext w
  simp only [mem_neighborFinset, Finset.mem_insert, Finset.mem_map, Fin.ext_iff, finCastAddTwo_val]
  rw [parentTree_adj_of_lt hp']
  dsimp only
  constructor
  · rintro (⟨hv_pos, hwp⟩ | ⟨hw_pos, hvp⟩)
    · have hsplit_v : splitLeafParent p t v.1 v.1 = p v.1 := by
        simp [splitLeafParent, show v.1 ≠ t by omega, show v.1 ≠ t + 1 by omega]
      rw [hsplit_v] at hwp
      have hw_lt : w.1 < t := by have := hp v.1 hv_pos v.2; omega
      right; right
      refine ⟨⟨w.1, hw_lt⟩, ?_, rfl⟩
      rw [parentTree_adj_of_lt hp]
      exact Or.inl ⟨hv_pos, hwp⟩
    · by_cases hw_lt : w.1 < t
      · have hsplit_w : splitLeafParent p t v.1 w.1 = p w.1 := by
          simp [splitLeafParent, show w.1 ≠ t by omega, show w.1 ≠ t + 1 by omega]
        rw [hsplit_w] at hvp
        right; right
        refine ⟨⟨w.1, hw_lt⟩, ?_, rfl⟩
        rw [parentTree_adj_of_lt hp]
        exact Or.inr ⟨hw_pos, hvp⟩
      · have : w.1 = t ∨ w.1 = t + 1 := by omega
        rcases this with hwt | hwt1
        · exact Or.inl hwt
        · exact Or.inr (Or.inl hwt1)
  · rintro (hwt | hwt1 | ⟨w₀, hw₀, hw_eq⟩)
    · right
      refine ⟨by omega, ?_⟩
      simp [splitLeafParent, hwt]
    · right
      refine ⟨by omega, ?_⟩
      simp [splitLeafParent, hwt1]
    · rw [parentTree_adj_of_lt hp] at hw₀
      rcases hw₀ with ⟨hv_pos, hwp⟩ | ⟨hw_pos, hvp⟩
      · left
        refine ⟨hv_pos, ?_⟩
        have hsplit_v : splitLeafParent p t v.1 v.1 = p v.1 := by
          simp [splitLeafParent, show v.1 ≠ t by omega, show v.1 ≠ t + 1 by omega]
        rw [hsplit_v, ← hw_eq, hwp]
      · right
        refine ⟨by omega, ?_⟩
        have hsplit_w : splitLeafParent p t v.1 w.1 = p w₀.1 := by
          rw [← hw_eq]
          simp [splitLeafParent, show w₀.1 ≠ t by omega, show w₀.1 ≠ t + 1 by omega]
        rw [hsplit_w, hvp]

/-- Neighbor finset of `⟨t, _⟩` in `parentTree (t + 2) (splitLeafParent p t v.1)`. -/
theorem neighborFinset_splitLeafParent_left {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (ht : 0 < t) (v : Fin t) :
    (parentTree (t + 2) (splitLeafParent p t v.1)).neighborFinset ⟨t, by omega⟩ =
      {⟨v.1, by omega⟩} := by
  have hp' := splitLeafParent_lt hp v.2
  ext w
  simp only [mem_neighborFinset, Finset.mem_singleton, Fin.ext_iff]
  rw [parentTree_adj_of_lt hp']
  dsimp only
  constructor
  · rintro (⟨_, hwp⟩ | ⟨hw_pos, htp⟩)
    · simp [splitLeafParent] at hwp
      exact hwp
    · unfold splitLeafParent at htp
      split_ifs at htp with h
      · have := v.2; omega
      · have := hp w.1 hw_pos (by omega)
        omega
  · intro hwv
    left
    refine ⟨ht, ?_⟩
    simp [splitLeafParent, hwv]

/-- Neighbor finset of `⟨t + 1, _⟩` in `parentTree (t + 2) (splitLeafParent p t v.1)`. -/
theorem neighborFinset_splitLeafParent_right {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (v : Fin t) :
    (parentTree (t + 2) (splitLeafParent p t v.1)).neighborFinset ⟨t + 1, by omega⟩ =
      {⟨v.1, by omega⟩} := by
  have hp' := splitLeafParent_lt hp v.2
  ext w
  simp only [mem_neighborFinset, Finset.mem_singleton, Fin.ext_iff]
  rw [parentTree_adj_of_lt hp']
  dsimp only
  constructor
  · rintro (⟨_, hwp⟩ | ⟨hw_pos, htp⟩)
    · simp [splitLeafParent] at hwp
      exact hwp
    · unfold splitLeafParent at htp
      split_ifs at htp with h
      · have := v.2; omega
      · have := hp w.1 hw_pos (by omega)
        omega
  · intro hwv
    left
    refine ⟨by omega, ?_⟩
    simp [splitLeafParent, hwv]

theorem degree_splitLeafParent_of_ne {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) {v u : Fin t} (hne : u ≠ v) :
    (parentTree (t + 2) (splitLeafParent p t v.1)).degree ⟨u.1, by omega⟩ =
      (parentTree t p).degree u := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    neighborFinset_splitLeafParent_of_ne hp hne, Finset.card_map]

theorem degree_splitLeafParent_self {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (v : Fin t) :
    (parentTree (t + 2) (splitLeafParent p t v.1)).degree ⟨v.1, by omega⟩ =
      (parentTree t p).degree v + 2 := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
    neighborFinset_splitLeafParent_self hp v]
  have hnot1 : (⟨t, by omega⟩ : Fin (t + 2)) ∉
      insert ⟨t + 1, by omega⟩ (((parentTree t p).neighborFinset v).map (finCastAddTwo t)) := by
    simp only [Finset.mem_insert, Finset.mem_map, Fin.ext_iff, finCastAddTwo_val,
      not_or, not_exists, not_and]
    refine ⟨by omega, fun w _ => by omega⟩
  have hnot2 : (⟨t + 1, by omega⟩ : Fin (t + 2)) ∉
      ((parentTree t p).neighborFinset v).map (finCastAddTwo t) := by
    simp only [Finset.mem_map, Fin.ext_iff, finCastAddTwo_val, not_exists, not_and]
    intro w _
    omega
  rw [Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem hnot2, Finset.card_map]

theorem degree_splitLeafParent_left {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (ht : 0 < t) (v : Fin t) :
    (parentTree (t + 2) (splitLeafParent p t v.1)).degree ⟨t, by omega⟩ = 1 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_splitLeafParent_left hp ht v,
    Finset.card_singleton]

theorem degree_splitLeafParent_right {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (v : Fin t) :
    (parentTree (t + 2) (splitLeafParent p t v.1)).degree ⟨t + 1, by omega⟩ = 1 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_splitLeafParent_right hp v,
    Finset.card_singleton]

/-- Splitting a leaf `v` of a cubic-or-leaf tree `parentTree t p` produces a cubic-or-leaf tree
`parentTree (t + 2) (splitLeafParent p t v.1)`. -/
theorem isCubicOrLeafTree_splitLeafParent {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (ht : 0 < t)
    (hcub : IsCubicOrLeafTree (parentTree t p))
    {v : Fin t} (hv : v ∈ treeLeaves (parentTree t p)) :
    IsCubicOrLeafTree (parentTree (t + 2) (splitLeafParent p t v.1)) := by
  have hp' := splitLeafParent_lt hp v.2
  refine ⟨parentTree_isTree (by omega) hp', fun w => ?_⟩
  by_cases hw_lt : w.1 < t
  · let w₀ : Fin t := ⟨w.1, hw_lt⟩
    have hw_eq : w = ⟨w₀.1, by omega⟩ := Fin.ext rfl
    rw [hw_eq]
    by_cases hwv : w₀ = v
    · subst hwv
      rw [degree_splitLeafParent_self hp w₀]
      have hdeg1 : (parentTree t p).degree w₀ = 1 := (mem_treeLeaves _ _).mp hv
      exact Or.inr (by omega)
    · rw [degree_splitLeafParent_of_ne hp hwv]
      exact hcub.2 w₀
  · rcases (by omega : w.1 = t ∨ w.1 = t + 1) with h1 | h2
    · have hw_eq : w = ⟨t, by omega⟩ := Fin.ext h1
      rw [hw_eq]
      exact Or.inl (degree_splitLeafParent_left hp ht v)
    · have hw_eq : w = ⟨t + 1, by omega⟩ := Fin.ext h2
      rw [hw_eq]
      exact Or.inl (degree_splitLeafParent_right hp v)

/-- Exact characterization of the leaves of `parentTree (t + 2) (splitLeafParent p t v.1)`:
they are the leaves of `parentTree t p` other than `v`, together with `⟨t, _⟩` and `⟨t + 1, _⟩`. -/
theorem mem_treeLeaves_splitLeafParent_iff {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (ht : 0 < t)
    {v : Fin t} (hv : v ∈ treeLeaves (parentTree t p)) (w : Fin (t + 2)) :
    w ∈ treeLeaves (parentTree (t + 2) (splitLeafParent p t v.1)) ↔
      w.1 = t ∨ w.1 = t + 1 ∨
        ∃ (hw_lt : w.1 < t), ⟨w.1, hw_lt⟩ ∈ treeLeaves (parentTree t p) ∧ w.1 ≠ v.1 := by
  rw [mem_treeLeaves]
  by_cases hw_lt : w.1 < t
  · let w₀ : Fin t := ⟨w.1, hw_lt⟩
    have hw_eq : w = ⟨w₀.1, by omega⟩ := Fin.ext rfl
    rw [hw_eq]
    by_cases hwv : w₀ = v
    · subst hwv
      rw [degree_splitLeafParent_self hp w₀]
      have hdeg1 : (parentTree t p).degree w₀ = 1 := (mem_treeLeaves _ _).mp hv
      simp [hdeg1, show ¬w₀.1 = t by omega, show ¬w₀.1 = t + 1 by omega]
    · rw [degree_splitLeafParent_of_ne hp hwv, ← mem_treeLeaves]
      have hwv_val : w₀.1 ≠ v.1 := fun h => hwv (Fin.ext h)
      simp [hwv_val, show ¬w₀.1 = t by omega, show ¬w₀.1 = t + 1 by omega]
  · rcases (by omega : w.1 = t ∨ w.1 = t + 1) with hwt | hwt1
    · have hw_eq : w = ⟨t, by omega⟩ := Fin.ext hwt
      rw [hw_eq, degree_splitLeafParent_left hp ht v]
      simp
    · have hw_eq : w = ⟨t + 1, by omega⟩ := Fin.ext hwt1
      rw [hw_eq, degree_splitLeafParent_right hp v]
      simp

/-- Cardinality of `treeLeaves` increases by `1` when splitting a leaf `v`. -/
theorem card_treeLeaves_splitLeafParent {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z) (ht : 0 < t)
    {v : Fin t} (hv : v ∈ treeLeaves (parentTree t p)) :
    (treeLeaves (parentTree (t + 2) (splitLeafParent p t v.1))).card =
      (treeLeaves (parentTree t p)).card + 1 := by
  have heq :
      treeLeaves (parentTree (t + 2) (splitLeafParent p t v.1)) =
        insert ⟨t, by omega⟩ (insert ⟨t + 1, by omega⟩
          (((treeLeaves (parentTree t p)).erase v).map (finCastAddTwo t))) := by
    ext w
    rw [mem_treeLeaves_splitLeafParent_iff hp ht hv]
    simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_erase, Fin.ext_iff, finCastAddTwo_val]
    constructor
    · rintro (hwt | hwt1 | ⟨hw_lt, hw_leaf, hw_ne⟩)
      · exact Or.inl hwt
      · exact Or.inr (Or.inl hwt1)
      · right; right
        exact ⟨⟨w.1, hw_lt⟩, ⟨fun h => hw_ne (congrArg Fin.val h), hw_leaf⟩, rfl⟩
    · rintro (hwt | hwt1 | ⟨w₀, ⟨hw_ne, hw_leaf⟩, hw_eq⟩)
      · exact Or.inl hwt
      · exact Or.inr (Or.inl hwt1)
      · right; right
        have hw_ne_val : w₀.1 ≠ v.1 := fun h => hw_ne (Fin.ext h)
        refine ⟨by omega, ?_, by omega⟩
        have h : (⟨w.1, by omega⟩ : Fin t) = w₀ := Fin.ext hw_eq.symm
        rwa [h]
  rw [heq]
  have hnot1 : (⟨t, by omega⟩ : Fin (t + 2)) ∉
      insert ⟨t + 1, by omega⟩ (((treeLeaves (parentTree t p)).erase v).map (finCastAddTwo t)) := by
    simp only [Finset.mem_insert, Finset.mem_map, Fin.ext_iff, finCastAddTwo_val,
      not_or, not_exists, not_and]
    exact ⟨by omega, fun w _ => by omega⟩
  have hnot2 : (⟨t + 1, by omega⟩ : Fin (t + 2)) ∉
      ((treeLeaves (parentTree t p)).erase v).map (finCastAddTwo t) := by
    simp only [Finset.mem_map, Fin.ext_iff, finCastAddTwo_val, not_exists, not_and]
    intro w _; omega
  rw [Finset.card_insert_of_notMem hnot1, Finset.card_insert_of_notMem hnot2,
    Finset.card_map, Finset.card_erase_of_mem hv]
  have hpos : 1 ≤ (treeLeaves (parentTree t p)).card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

/-- Every leaf `v` of `parentTree t p` has no children: if `v.1 > 0`, its unique neighbor is its
parent `p v.1 < v.1`, so no `z > 0` can have `p z = v.1`. -/
theorem no_children_of_mem_treeLeaves_pos {t : ℕ} {p : ℕ → ℕ}
    (hp : ∀ z, 0 < z → z < t → p z < z)
    {v : Fin t} (hv : v ∈ treeLeaves (parentTree t p)) (hv_pos : 0 < v.1) :
    ∀ z, 0 < z → z < t → p z ≠ v.1 := by
  intro z hz_pos hz_lt hpz
  have hdeg1 : (parentTree t p).degree v = 1 := (mem_treeLeaves _ _).mp hv
  rw [degree_eq_one_iff_existsUnique_adj] at hdeg1
  rcases hdeg1 with ⟨w, _, hw_uniq⟩
  let pv : Fin t := ⟨p v.1, Nat.lt_trans (hp v.1 hv_pos v.2) v.2⟩
  let zFin : Fin t := ⟨z, hz_lt⟩
  have hadj_pv : (parentTree t p).Adj v pv := by
    rw [parentTree_adj_of_lt hp]
    exact Or.inl ⟨hv_pos, rfl⟩
  have hadj_z : (parentTree t p).Adj v zFin := by
    rw [parentTree_adj_of_lt hp]
    exact Or.inr ⟨hz_pos, hpz.symm⟩
  have hpv_eq_w : pv = w := hw_uniq pv hadj_pv
  have hz_eq_w : zFin = w := hw_uniq zFin hadj_z
  have hpv_eq_z : (p v.1 : ℕ) = z := congrArg Fin.val (hpv_eq_w.trans hz_eq_w.symm)
  have hpv_lt : p v.1 < v.1 := hp v.1 hv_pos v.2
  have hpz_lt : p z < z := hp z hz_pos hz_lt
  omega

/-! ### Section 5: Leaf Cut Sets (`Z = V(R ∩ R')`) and Preservation of Invariants in Steps (1)–(6) -/

/-- For a leaf `v` (`T.degree v = 1`) and its unique neighbor `u` (`T.Adj u v`), vertex `v` is
isolated in `T.deleteEdges {s(u, v)}`. -/
theorem not_adj_deleteEdges_of_degree_eq_one {t : ℕ} {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {u v w : Fin t} (hdeg : T.degree v = 1) (hadj_uv : T.Adj u v) :
    ¬(T.deleteEdges {s(u, v)}).Adj v w := by
  rw [deleteEdges_adj, Set.mem_singleton_iff]
  rintro ⟨hadj_vw, hne⟩
  rw [degree_eq_one_iff_existsUnique_adj] at hdeg
  rcases hdeg with ⟨z, _, hz_uniq⟩
  have hu_z : u = z := hz_uniq u hadj_uv.symm
  have hw_z : w = z := hz_uniq w hadj_vw
  have hw_u : w = u := hw_z.trans hu_z.symm
  subst hw_u
  exact hne Sym2.eq_swap

theorem reachable_deleteEdges_leaf_self_iff {t : ℕ} {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {u v y : Fin t} (hdeg : T.degree v = 1) (hadj_uv : T.Adj u v) :
    (T.deleteEdges {s(u, v)}).Reachable v y ↔ y = v := by
  constructor
  · rintro ⟨w⟩
    cases w with
    | nil => rfl
    | @cons _ z _ hadj _ =>
      exact False.elim (not_adj_deleteEdges_of_degree_eq_one hdeg hadj_uv hadj)
  · rintro rfl
    exact Reachable.refl _

/-- Removing the unique edge `s(u, v)` incident with a leaf `v` of a connected graph `T` splits `T`
into `{v}` and `{v}ᶜ`: two vertices `y, z` are reachable in `T.deleteEdges {s(u, v)}` if and only if
`(y = v ↔ z = v)`. -/
theorem deleteEdges_leaf_reachable_iff {t : ℕ} {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    (hconn : T.Connected) {u v : Fin t} (hdeg : T.degree v = 1) (hadj_uv : T.Adj u v)
    (y z : Fin t) :
    (T.deleteEdges {s(u, v)}).Reachable y z ↔ (y = v ↔ z = v) := by
  by_cases hyv : y = v
  · subst hyv
    rw [reachable_deleteEdges_leaf_self_iff hdeg hadj_uv]
    simp
  · by_cases hzv : z = v
    · subst hzv
      rw [reachable_comm, reachable_deleteEdges_leaf_self_iff hdeg hadj_uv]
      simp [hyv]
    · simp only [hyv, hzv, iff_self, iff_true]
      have hconn_compl : (T.induce ({v}ᶜ : Set (Fin t))).Connected :=
        hconn.induce_compl_singleton_of_degree_eq_one hdeg
      rcases hconn_compl ⟨y, hyv⟩ ⟨z, hzv⟩ with ⟨w⟩
      have lift_walk : ∀ {a b : ({v}ᶜ : Set (Fin t))},
          (T.induce ({v}ᶜ : Set (Fin t))).Walk a b →
          (T.deleteEdges {s(u, v)}).Reachable a.1 b.1 := by
        intro a b w₀
        induction w₀ with
        | nil => exact Reachable.refl _
        | @cons x₁ x₂ x₃ hadj tail ih =>
          have hadj_del : (T.deleteEdges {s(u, v)}).Adj x₁.1 x₂.1 := by
            rw [deleteEdges_adj, Set.mem_singleton_iff]
            refine ⟨hadj, ?_⟩
            intro heq
            rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h, _⟩
            · exact x₂.2 h
            · exact x₁.2 h
          exact hadj_del.reachable.trans ih
      exact lift_walk w

/-- The vertex set `Z = V(R ∩ R')` in Step (2) of Algorithm (3.3) for a leaf `v`:
vertices `w` of `G` incident with an edge `e₁ ∈ E(G)` having `τ(e₁) = v` and an edge
`e₂ ∈ E(G)` having `τ(e₂) ≠ v`. -/
noncomputable def leafCutVerts {n t : ℕ} (G : SimpleGraph (Fin n))
    (τ : Sym2 (Fin n) → Fin t) (v : Fin t) : Finset (Fin n) :=
  open Classical in
  Finset.univ.filter (fun w : Fin n =>
    (∃ e₁ ∈ G.edgeFinset, w ∈ e₁ ∧ τ e₁ = v) ∧
    (∃ e₂ ∈ G.edgeFinset, w ∈ e₂ ∧ τ e₂ ≠ v))

@[simp]
theorem mem_leafCutVerts {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Sym2 (Fin n) → Fin t) (v : Fin t) (w : Fin n) :
    w ∈ leafCutVerts G τ v ↔
      (∃ e₁ ∈ G.edgeFinset, w ∈ e₁ ∧ τ e₁ = v) ∧
      (∃ e₂ ∈ G.edgeFinset, w ∈ e₂ ∧ τ e₂ ≠ v) := by
  classical
  unfold leafCutVerts
  convert Finset.mem_filter.trans (and_iff_right (Finset.mem_univ w))

/-- For any leaf `v` of a connected graph `T` and its incident edge `s(u, v)`,
`treeEdgeCutVerts G T τ s(u, v) = leafCutVerts G τ v`. -/
theorem treeEdgeCutVerts_leaf_eq {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj] (hconn : T.Connected)
    (τ : Sym2 (Fin n) → Fin t) {u v : Fin t} (hdeg : T.degree v = 1) (hadj_uv : T.Adj u v) :
    treeEdgeCutVerts G T τ s(u, v) = leafCutVerts G τ v := by
  ext w
  rw [mem_treeEdgeCutVerts, mem_leafCutVerts]
  constructor
  · rintro ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
    rw [deleteEdges_leaf_reachable_iff hconn hdeg hadj_uv] at hnr
    by_cases h1 : τ e₁ = v
    · have h2 : τ e₂ ≠ v := fun h => hnr ⟨fun _ => h, fun _ => h1⟩
      exact ⟨⟨e₁, he₁, hw₁, h1⟩, ⟨e₂, he₂, hw₂, h2⟩⟩
    · have h2 : τ e₂ = v := by
        by_contra h2'
        exact hnr ⟨fun h => False.elim (h1 h), fun h => False.elim (h2' h)⟩
      exact ⟨⟨e₂, he₂, hw₂, h2⟩, ⟨e₁, he₁, hw₁, h1⟩⟩
  · rintro ⟨⟨e₁, he₁, hw₁, h1⟩, ⟨e₂, he₂, hw₂, h2⟩⟩
    refine ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, ?_⟩
    rw [deleteEdges_leaf_reachable_iff hconn hdeg hadj_uv]
    intro hiff
    exact h2 (hiff.mp h1)

/-- In any partial branch-decomposition `(T, τ)` of `G`, every leaf `v ∈ treeLeaves T` has
`|leafCutVerts G τ v| ≤ 3ω` (GM XIII (3.3) Step (2), page 73: "`|V(R ∩ R')| ≤ 3ω`"). -/
theorem card_leafCutVerts_le_three_mul_omega {n t : ℕ} {ω : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Sym2 (Fin n) → Fin t}
    (hpart : IsPartialBranchDecomp ω G T τ)
    {v : Fin t} (hv : v ∈ treeLeaves T) :
    (leafCutVerts G τ v).card ≤ 3 * ω := by
  have hdeg : T.degree v = 1 := (mem_treeLeaves T v).mp hv
  have hdeg_rw := hdeg
  rw [degree_eq_one_iff_existsUnique_adj] at hdeg_rw
  rcases hdeg_rw with ⟨u, hadj_vu, _⟩
  have hadj_uv : T.Adj u v := hadj_vu.symm
  have hf_mem : s(u, v) ∈ T.edgeFinset := by
    rw [mem_edgeFinset, mem_edgeSet]; exact hadj_uv
  have hord := hpart.2.2.2 s(u, v) hf_mem
  unfold treeEdgeOrder at hord
  rwa [treeEdgeCutVerts_leaf_eq G hpart.1.1.connected τ hdeg hadj_uv] at hord

/-- Every edge `e ∈ G.edgeFinset` has at most `2` incident vertices in `Fin n`. -/
theorem card_incident_edge_le_two {n : ℕ} (e : Sym2 (Fin n)) :
    (Finset.univ.filter (fun w : Fin n => w ∈ e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | _ u v =>
    have hsub : Finset.univ.filter (fun w : Fin n => w ∈ s(u, v)) ⊆ {u, v} := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
        Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      exact hw
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

/-- Initialization of Algorithm (3.3) (page 73):
Given `G₁` with an edge `e₀ ∈ G₁.edgeFinset` and another edge `e₁ ∈ G₁.edgeFinset` (`e₁ ≠ e₀`),
setting `T₁ = parentTree 2 (fun _ => 0)` and `τ₁(e) = 0` if `e = e₀` else `1` yields a valid
`IsPartialBranchDecomp ω G₁ T₁ τ₁` for any `ω ≥ 2`. -/
theorem isPartialBranchDecomp_init {n : ℕ} {ω : ℕ} (hω : 2 ≤ ω)
    (G₁ : SimpleGraph (Fin n)) [DecidableRel G₁.Adj]
    {e₀ e₁ : Sym2 (Fin n)} (he₀ : e₀ ∈ G₁.edgeFinset) (he₁ : e₁ ∈ G₁.edgeFinset)
    (hne : e₁ ≠ e₀)
    (τ₁ : Sym2 (Fin n) → Fin 2)
    (hτ₀ : τ₁ e₀ = ⟨0, by omega⟩)
    (hτ_other : ∀ e ∈ G₁.edgeFinset, e ≠ e₀ → τ₁ e = ⟨1, by omega⟩) :
    IsPartialBranchDecomp ω G₁ (parentTree 2 (fun _ => 0)) τ₁ := by
  refine ⟨isCubicOrLeafTree_parentTree_two, ?_, ?_, ?_⟩
  · intro e _
    rw [treeLeaves_parentTree_two]
    exact Finset.mem_univ _
  · intro v _
    fin_cases v
    · exact ⟨e₀, he₀, hτ₀⟩
    · exact ⟨e₁, he₁, hτ_other e₁ he₁ hne⟩
  · intro f hf
    have hp : ∀ z, 0 < z → z < 2 → (fun _ => 0) z < z := fun z hz _ => hz
    rcases exists_pos_of_mem_edgeFinset_parentTree hp hf with ⟨x, hx_pos, hf_eq⟩
    have hx_lt2 : x.1 < 2 := x.2
    have hx1 : x = ⟨1, by decide⟩ := Fin.ext (by change x.1 = 1; omega)
    have hf_eq01 : f = s(⟨0, by decide⟩, ⟨1, by decide⟩) := by
      rw [hf_eq]
      exact congrArg₂ (fun a b => s(a, b)) (Fin.ext rfl) hx1
    rw [hf_eq01]
    have hdeg1 : (parentTree 2 (fun _ => 0)).degree ⟨1, by decide⟩ = 1 :=
      degree_parentTree_two ⟨1, by decide⟩
    have hadj01 : (parentTree 2 (fun _ => 0)).Adj ⟨0, by decide⟩ ⟨1, by decide⟩ := by
      rw [parentTree_adj_of_lt hp]
      exact Or.inr ⟨by decide, rfl⟩
    have hconn : (parentTree 2 (fun _ => 0)).Connected :=
      parentTree_connected (by omega) hp
    unfold treeEdgeOrder
    rw [treeEdgeCutVerts_leaf_eq G₁ hconn τ₁ hdeg1 hadj01]
    have hsub : leafCutVerts G₁ τ₁ ⟨1, by omega⟩ ⊆ Finset.univ.filter (fun w : Fin n => w ∈ e₀) := by
      intro w hw
      rw [mem_leafCutVerts] at hw
      rcases hw with ⟨_, ⟨e₂, he₂, hw₂, hne1⟩⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases he₂_eq : e₂ = e₀
      · rwa [← he₂_eq]
      · exact False.elim (hne1 (hτ_other e₂ he₂ he₂_eq))
    have hcard := (Finset.card_le_card hsub).trans (card_incident_edge_le_two e₀)
    omega

/-- Key invariance lemma for splitting a leaf `v` of `parentTree t p` into `⟨t, _⟩` and
`⟨t + 1, _⟩` (used in both Step (3) and Step (5) of Algorithm (3.3)):
Suppose `(parentTree t p, τ)` is a partial branch-decomposition of `G`, `v` is a leaf of
`parentTree t p`, and `τ' : Sym2 (Fin n) → Fin (t + 2)` maps:
- every `e` with `τ e ≠ v` to `⟨(τ e).1, _⟩`, and
- every `e` with `τ e = v` to either `⟨t, _⟩` or `⟨t + 1, _⟩`,
such that both `⟨t, _⟩` and `⟨t + 1, _⟩` are hit by at least one edge of `G`, and both
`|leafCutVerts G τ' ⟨t, _⟩| ≤ 3ω` and `|leafCutVerts G τ' ⟨t + 1, _⟩| ≤ 3ω`.
Then `(parentTree (t + 2) (splitLeafParent p t v.1), τ')` is a partial branch-decomposition of `G`. -/
theorem isPartialBranchDecomp_splitLeaf {n t : ℕ} {ω : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {p : ℕ → ℕ} (ht : 0 < t) (hp : ∀ z, 0 < z → z < t → p z < z)
    {τ : Sym2 (Fin n) → Fin t}
    (hpart : IsPartialBranchDecomp ω G (parentTree t p) τ)
    {v : Fin t} (hv : v ∈ treeLeaves (parentTree t p))
    {τ' : Sym2 (Fin n) → Fin (t + 2)}
    (hτ'_ne : ∀ e ∈ G.edgeFinset, τ e ≠ v → (τ' e).1 = (τ e).1)
    (hτ'_eq : ∀ e ∈ G.edgeFinset, τ e = v → (τ' e).1 = t ∨ (τ' e).1 = t + 1)
    (hsurj_left : ∃ e ∈ G.edgeFinset, τ' e = ⟨t, by omega⟩)
    (hsurj_right : ∃ e ∈ G.edgeFinset, τ' e = ⟨t + 1, by omega⟩)
    (hord_left : (leafCutVerts G τ' ⟨t, by omega⟩).card ≤ 3 * ω)
    (hord_right : (leafCutVerts G τ' ⟨t + 1, by omega⟩).card ≤ 3 * ω) :
    IsPartialBranchDecomp ω G (parentTree (t + 2) (splitLeafParent p t v.1)) τ' := by
  let p' := splitLeafParent p t v.1
  have hp' : ∀ z, 0 < z → z < t + 2 → p' z < z := splitLeafParent_lt hp v.2
  have hcub' : IsCubicOrLeafTree (parentTree (t + 2) p') :=
    isCubicOrLeafTree_splitLeafParent hp ht hpart.1 hv
  refine ⟨hcub', ?_, ?_, ?_⟩
  · -- Maps into `treeLeaves`
    intro e he
    rw [mem_treeLeaves_splitLeafParent_iff hp ht hv]
    by_cases hev : τ e = v
    · rcases hτ'_eq e he hev with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    · right; right
      have hval := hτ'_ne e he hev
      refine ⟨by rw [hval]; exact (τ e).2, ?_, ?_⟩
      · have h_eq : (⟨(τ' e).1, by rw [hval]; exact (τ e).2⟩ : Fin t) = τ e := Fin.ext hval
        rw [h_eq]
        exact hpart.2.1 e he
      · rw [hval]
        exact fun h => hev (Fin.ext h)
  · -- Surjective onto `treeLeaves`
    intro w hw
    rw [mem_treeLeaves_splitLeafParent_iff hp ht hv] at hw
    rcases hw with hwt | hwt1 | ⟨hw_lt, hw_leaf, hw_ne⟩
    · rcases hsurj_left with ⟨e, he, he_eq⟩
      exact ⟨e, he, he_eq.trans (Fin.ext hwt.symm)⟩
    · rcases hsurj_right with ⟨e, he, he_eq⟩
      exact ⟨e, he, he_eq.trans (Fin.ext hwt1.symm)⟩
    · rcases hpart.2.2.1 ⟨w.1, hw_lt⟩ hw_leaf with ⟨e, he, he_eq⟩
      have hev : τ e ≠ v := by
        intro h
        apply hw_ne
        have := congrArg Fin.val (he_eq.symm.trans h)
        exact this
      refine ⟨e, he, Fin.ext ?_⟩
      rw [hτ'_ne e he hev, congrArg Fin.val he_eq]
  · -- Edge orders ≤ 3ω
    intro f hf
    rcases exists_pos_of_mem_edgeFinset_parentTree hp' hf with ⟨x, hx_pos, hf_eq⟩
    by_cases hx_lt : x.1 < t
    · -- Old edge `0 < x.1 < t`: its `inSubtree` partition of `E(G)` is unchanged
      let x₀ : Fin t := ⟨x.1, hx_lt⟩
      have hx₀_pos : 0 < x₀.1 := hx_pos
      have hsub_eq : ∀ e ∈ G.edgeFinset,
          inSubtree p' x.1 (τ' e).1 = inSubtree p x₀.1 (τ e).1 := by
        intro e he
        by_cases hev : τ e = v
        · rcases hτ'_eq e he hev with h1 | h2
          · rw [h1, inSubtree_splitLeafParent_left hp ht v.2 hx_lt, hev]
          · rw [h2, inSubtree_splitLeafParent_right hp v.2 hx_lt, hev]
        · rw [hτ'_ne e he hev]
          exact inSubtree_splitLeafParent_of_lt hp v.2 hx_lt (τ e).1 (τ e).2
      let px₀ : Fin t := ⟨p x₀.1, Nat.lt_trans (hp x₀.1 hx₀_pos x₀.2) x₀.2⟩
      have hf₀_mem : s(px₀, x₀) ∈ (parentTree t p).edgeFinset := by
        rw [mem_edgeFinset, mem_edgeSet, parentTree_adj_of_lt hp]
        exact Or.inr ⟨hx₀_pos, rfl⟩
      have hcut_eq :
          treeEdgeCutVerts G (parentTree (t + 2) p') τ'
            s(⟨p' x.1, Nat.lt_trans (hp' x.1 hx_pos x.2) x.2⟩, x) =
          treeEdgeCutVerts G (parentTree t p) τ s(px₀, x₀) := by
        ext w
        rw [mem_treeEdgeCutVerts, mem_treeEdgeCutVerts]
        constructor
        · rintro ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
          rw [parentTree_deleteEdge_reachable_iff (by omega) hp' hx_pos] at hnr
          rw [hsub_eq e₁ he₁, hsub_eq e₂ he₂] at hnr
          rw [← parentTree_deleteEdge_reachable_iff ht hp hx₀_pos] at hnr
          exact ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
        · rintro ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
          rw [parentTree_deleteEdge_reachable_iff ht hp hx₀_pos] at hnr
          rw [← hsub_eq e₁ he₁, ← hsub_eq e₂ he₂] at hnr
          rw [← parentTree_deleteEdge_reachable_iff (by omega) hp' hx_pos] at hnr
          exact ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
      rw [hf_eq]
      unfold treeEdgeOrder
      rw [hcut_eq]
      exact hpart.2.2.2 s(px₀, x₀) hf₀_mem
    · -- New leaf edge `x.1 = t` or `x.1 = t + 1`
      have hconn' : (parentTree (t + 2) p').Connected :=
        parentTree_connected (by omega) hp'
      have hx_lt2 : x.1 < t + 2 := x.2
      rcases (by omega : x.1 = t ∨ x.1 = t + 1) with hxt | hxt1
      · have hx_eq : x = ⟨t, by omega⟩ := Fin.ext hxt
        have hdeg_t : (parentTree (t + 2) p').degree ⟨t, by omega⟩ = 1 :=
          degree_splitLeafParent_left hp ht v
        let pt : Fin (t + 2) := ⟨p' t, Nat.lt_trans (hp' t ht (by omega)) (by omega)⟩
        have hadj_t : (parentTree (t + 2) p').Adj pt ⟨t, by omega⟩ := by
          rw [parentTree_adj_of_lt hp']
          exact Or.inr ⟨ht, rfl⟩
        have hf_eq_t : f = s(pt, ⟨t, by omega⟩) := by
          rw [hf_eq]
          exact congrArg₂ (fun a b => s(a, b)) (Fin.ext (by simp [pt, hxt])) hx_eq
        rw [hf_eq_t]
        unfold treeEdgeOrder
        rw [treeEdgeCutVerts_leaf_eq G hconn' τ' hdeg_t hadj_t]
        exact hord_left
      · have hx_eq : x = ⟨t + 1, by omega⟩ := Fin.ext hxt1
        have hdeg_t1 : (parentTree (t + 2) p').degree ⟨t + 1, by omega⟩ = 1 :=
          degree_splitLeafParent_right hp v
        let pt1 : Fin (t + 2) :=
          ⟨p' (t + 1), Nat.lt_trans (hp' (t + 1) (by omega) (by omega)) (by omega)⟩
        have hadj_t1 : (parentTree (t + 2) p').Adj pt1 ⟨t + 1, by omega⟩ := by
          rw [parentTree_adj_of_lt hp']
          exact Or.inr ⟨by omega, rfl⟩
        have hf_eq_t1 : f = s(pt1, ⟨t + 1, by omega⟩) := by
          rw [hf_eq]
          exact congrArg₂ (fun a b => s(a, b)) (Fin.ext (by simp [pt1, hxt1])) hx_eq
        rw [hf_eq_t1]
        unfold treeEdgeOrder
        rw [treeEdgeCutVerts_leaf_eq G hconn' τ' hdeg_t1 hadj_t1]
        exact hord_right

/-- If `g ∈ G.edgeFinset` and `u₀ ∈ S` is an endpoint of `g`, then the set of vertices incident
with `g` is contained in `insert x S` for some `x : Fin n`. -/
theorem exists_insert_superset_of_mem_edge {n : ℕ} (S : Finset (Fin n)) (g : Sym2 (Fin n))
    {u₀ : Fin n} (hu₀_S : u₀ ∈ S) (hu₀_g : u₀ ∈ g) :
    ∃ x : Fin n, Finset.univ.filter (fun w : Fin n => w ∈ g) ⊆ insert x S := by
  induction g using Sym2.ind with
  | _ a b =>
    rcases Sym2.mem_iff.mp hu₀_g with rfl | rfl
    · refine ⟨b, fun w hw => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
        Finset.mem_insert] at hw ⊢
      rcases hw with rfl | rfl
      · exact Or.inr hu₀_S
      · exact Or.inl rfl
    · refine ⟨a, fun w hw => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
        Finset.mem_insert] at hw ⊢
      rcases hw with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr hu₀_S

/-- Step (3) of Algorithm (3.3) (page 74):
If `|leafCutVerts G τ v| < 3ω`, and `g` is an edge with `τ g = v` (with another edge `e' ≠ g`
also having `τ e' = v`) that is incident with `leafCutVerts G τ v` if `leafCutVerts G τ v` is
nonempty, then splitting leaf `v` into `⟨t, _⟩` (receiving `{g}`) and `⟨t + 1, _⟩` (receiving
all `e ≠ g` with `τ e = v`) preserves `IsPartialBranchDecomp`. -/
theorem isPartialBranchDecomp_step3 {n t : ℕ} {ω : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {p : ℕ → ℕ} (ht : 0 < t) (hp : ∀ z, 0 < z → z < t → p z < z)
    {τ : Sym2 (Fin n) → Fin t}
    (hpart : IsPartialBranchDecomp ω G (parentTree t p) τ)
    {v : Fin t} (hv : v ∈ treeLeaves (parentTree t p))
    (hZ_lt : (leafCutVerts G τ v).card < 3 * ω)
    {g : Sym2 (Fin n)} (hg_mem : g ∈ G.edgeFinset) (hg_v : τ g = v)
    (hother : ∃ e' ∈ G.edgeFinset, τ e' = v ∧ e' ≠ g)
    (hg_inc : (leafCutVerts G τ v).Nonempty → ∃ u₀ ∈ leafCutVerts G τ v, u₀ ∈ g)
    {τ' : Sym2 (Fin n) → Fin (t + 2)}
    (hτ'_ne : ∀ e ∈ G.edgeFinset, τ e ≠ v → (τ' e).1 = (τ e).1)
    (hτ'_g : τ' g = ⟨t, by omega⟩)
    (hτ'_other : ∀ e ∈ G.edgeFinset, τ e = v → e ≠ g → τ' e = ⟨t + 1, by omega⟩) :
    IsPartialBranchDecomp ω G (parentTree (t + 2) (splitLeafParent p t v.1)) τ' := by
  rcases hother with ⟨e', he'_mem, he'_v, he'_ne⟩
  refine isPartialBranchDecomp_splitLeaf ht hp hpart hv hτ'_ne ?_ ⟨g, hg_mem, hτ'_g⟩
    ⟨e', he'_mem, hτ'_other e' he'_mem he'_v he'_ne⟩ ?_ ?_
  · intro e he he_v
    by_cases heg : e = g
    · subst heg; exact Or.inl (congrArg Fin.val hτ'_g)
    · exact Or.inr (congrArg Fin.val (hτ'_other e he he_v heg))
  · -- Order of left new leaf `⟨t, _⟩` ≤ 2 ≤ 3ω
    have hsub : leafCutVerts G τ' ⟨t, by omega⟩ ⊆ Finset.univ.filter (fun w : Fin n => w ∈ g) := by
      intro w hw
      rw [mem_leafCutVerts] at hw
      rcases hw with ⟨⟨e₁, he₁, hw₁, h1⟩, _⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases he₁_g : e₁ = g
      · rwa [← he₁_g]
      · by_cases he₁_v : τ e₁ = v
        · have h1_val : (τ' e₁).1 = t := congrArg Fin.val h1
          have h2_val : (τ' e₁).1 = t + 1 := congrArg Fin.val (hτ'_other e₁ he₁ he₁_v he₁_g)
          omega
        · have := hτ'_ne e₁ he₁ he₁_v
          have h1_val : (τ' e₁).1 = t := congrArg Fin.val h1
          have := (τ e₁).2
          omega
    have hcard := (Finset.card_le_card hsub).trans (card_incident_edge_le_two g)
    omega
  · -- Order of right new leaf `⟨t + 1, _⟩` ≤ 3ω
    by_cases hZ_nonempty : (leafCutVerts G τ v).Nonempty
    · rcases hg_inc hZ_nonempty with ⟨u₀, hu₀_Z, hu₀_g⟩
      rcases exists_insert_superset_of_mem_edge (leafCutVerts G τ v) g hu₀_Z hu₀_g with ⟨x, hx_sub⟩
      have hsub : leafCutVerts G τ' ⟨t + 1, by omega⟩ ⊆ insert x (leafCutVerts G τ v) := by
        intro w hw
        rw [mem_leafCutVerts] at hw
        rcases hw with ⟨⟨e₁, he₁, hw₁, h1⟩, ⟨e₂, he₂, hw₂, h2⟩⟩
        have he₁_v : τ e₁ = v := by
          by_contra hne_v
          have := hτ'_ne e₁ he₁ hne_v
          have h1_val : (τ' e₁).1 = t + 1 := congrArg Fin.val h1
          have := (τ e₁).2
          omega
        by_cases he₂_v : τ e₂ = v
        · have he₂_g : e₂ = g := by
            by_contra hne_g
            exact h2 (hτ'_other e₂ he₂ he₂_v hne_g)
          subst he₂_g
          exact hx_sub (by simp [hw₂])
        · apply Finset.mem_insert_of_mem
          rw [mem_leafCutVerts]
          exact ⟨⟨e₁, he₁, hw₁, he₁_v⟩, ⟨e₂, he₂, hw₂, he₂_v⟩⟩
      have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le x (leafCutVerts G τ v))
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hZ_nonempty
      have hsub : leafCutVerts G τ' ⟨t + 1, by omega⟩ ⊆
          Finset.univ.filter (fun w : Fin n => w ∈ g) := by
        intro w hw
        rw [mem_leafCutVerts] at hw
        rcases hw with ⟨⟨e₁, he₁, hw₁, h1⟩, ⟨e₂, he₂, hw₂, h2⟩⟩
        have he₁_v : τ e₁ = v := by
          by_contra hne_v
          have := hτ'_ne e₁ he₁ hne_v
          have h1_val : (τ' e₁).1 = t + 1 := congrArg Fin.val h1
          have := (τ e₁).2
          omega
        by_cases he₂_v : τ e₂ = v
        · have he₂_g : e₂ = g := by
            by_contra hne_g
            exact h2 (hτ'_other e₂ he₂ he₂_v hne_g)
          subst he₂_g
          simp [hw₂]
        · have hw_Z : w ∈ leafCutVerts G τ v := by
            rw [mem_leafCutVerts]
            exact ⟨⟨e₁, he₁, hw₁, he₁_v⟩, ⟨e₂, he₂, hw₂, he₂_v⟩⟩
          rw [hZ_nonempty] at hw_Z
          exact False.elim (Finset.notMem_empty w hw_Z)
      have hcard := (Finset.card_le_card hsub).trans (card_incident_edge_le_two g)
      omega

/-- The subgraph `R` of `G` in Step (2) of Algorithm (3.3) consisting of edges `e` with `τ e = v`. -/
def leafGraph {n t : ℕ} (G : SimpleGraph (Fin n)) (τ : Sym2 (Fin n) → Fin t) (v : Fin t) :
    SimpleGraph (Fin n) where
  Adj x y := G.Adj x y ∧ τ s(x, y) = v
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun x h => G.loopless.irrefl x h.1⟩

instance instDecidableRelLeafGraphAdj {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Sym2 (Fin n) → Fin t) (v : Fin t) : DecidableRel (leafGraph G τ v).Adj :=
  fun x y => inferInstanceAs (Decidable (G.Adj x y ∧ τ s(x, y) = v))

theorem leafGraph_le {n t : ℕ} (G : SimpleGraph (Fin n)) (τ : Sym2 (Fin n) → Fin t) (v : Fin t) :
    leafGraph G τ v ≤ G :=
  fun _ _ h => h.1

@[simp]
theorem mem_edgeFinset_leafGraph {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (τ : Sym2 (Fin n) → Fin t) (v : Fin t) (e : Sym2 (Fin n)) :
    e ∈ (leafGraph G τ v).edgeFinset ↔ e ∈ G.edgeFinset ∧ τ e = v := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_edgeFinset, mem_edgeSet, mem_edgeFinset, mem_edgeSet]
    rfl

/-- Conditions for a valid partition `(Z₁, Z₂, Z₃)` of `Z` in Step (4) of Algorithm (3.3)
(page 74): `Z₁, Z₂, Z₃` partition `Z` (`|Z| = 3ω`), `|Z₁|, |Z₂| ≤ 2ω - |Z₃|/2` (cleared of
denominators as `2|Z₁| + |Z₃| ≤ 4ω` and `2|Z₂| + |Z₃| ≤ 4ω`), and `|Z₃| ≤ ω`. -/
structure IsValidZPartition {n : ℕ} (ω : ℕ) (Z Z₁ Z₂ Z₃ : Finset (Fin n)) : Prop where
  disj12 : Disjoint Z₁ Z₂
  disj13 : Disjoint Z₁ Z₃
  disj23 : Disjoint Z₂ Z₃
  union_eq : Z₁ ∪ Z₂ ∪ Z₃ = Z
  card_Z : Z.card = 3 * ω
  card_Z1 : 2 * Z₁.card + Z₃.card ≤ 4 * ω
  card_Z2 : 2 * Z₂.card + Z₃.card ≤ 4 * ω
  card_Z3 : Z₃.card ≤ ω

theorem IsValidZPartition.card_sum {n : ℕ} {ω : ℕ} {Z Z₁ Z₂ Z₃ : Finset (Fin n)}
    (h : IsValidZPartition ω Z Z₁ Z₂ Z₃) :
    Z₁.card + Z₂.card + Z₃.card = 3 * ω := by
  have h12 : (Z₁ ∪ Z₂).card = Z₁.card + Z₂.card := Finset.card_union_of_disjoint h.disj12
  have h123 : Disjoint (Z₁ ∪ Z₂) Z₃ := Finset.disjoint_union_left.mpr ⟨h.disj13, h.disj23⟩
  have hsum : (Z₁ ∪ Z₂ ∪ Z₃).card = Z₁.card + Z₂.card + Z₃.card := by
    rw [Finset.card_union_of_disjoint h123, h12]
  rw [← hsum, h.union_eq, h.card_Z]

theorem IsValidZPartition.Z1_nonempty {n : ℕ} {ω : ℕ} {Z Z₁ Z₂ Z₃ : Finset (Fin n)}
    (h : IsValidZPartition ω Z Z₁ Z₂ Z₃) (hω : 1 ≤ ω) :
    Z₁.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hemp
  have hc0 : Z₁.card = 0 := by simp [hemp]
  have hsum := h.card_sum
  have h2 := h.card_Z2
  have h3 := h.card_Z3
  omega

theorem IsValidZPartition.Z2_nonempty {n : ℕ} {ω : ℕ} {Z Z₁ Z₂ Z₃ : Finset (Fin n)}
    (h : IsValidZPartition ω Z Z₁ Z₂ Z₃) (hω : 1 ≤ ω) :
    Z₂.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hemp
  have hc0 : Z₂.card = 0 := by simp [hemp]
  have hsum := h.card_sum
  have h1 := h.card_Z1
  have h3 := h.card_Z3
  omega

/-- Every balanced separation `sep : GraphSeparation G` of order `≤ ω` on `Z` (`|Z| = 3ω`)
induces a valid partition `(Z \ sep.VB, Z \ sep.VA, Z ∩ (sep.VA ∩ sep.VB))` of `Z`. -/
theorem GraphSeparation.to_isValidZPartition {n : ℕ} {ω : ℕ} {G : SimpleGraph (Fin n)}
    (sep : GraphSeparation G) {Z : Finset (Fin n)} (hZ : Z.card = 3 * ω)
    (hord : sep.order ≤ ω) (hbal : sep.IsBalancedQ Z) :
    IsValidZPartition ω Z (Z \ sep.VB) (Z \ sep.VA) (Z ∩ (sep.VA ∩ sep.VB)) := by
  have hnat := (sep.isBalancedQ_iff_isBalancedNat Z).mp hbal
  rcases hnat with ⟨hb1, hb2⟩
  refine ⟨?_, ?_, ?_, ?_, hZ, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_sdiff] at hx1 hx2
    have hcov : x ∈ sep.VA ∪ sep.VB := by rw [sep.union_verts]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp hcov with hA | hB
    · exact hx2.2 hA
    · exact hx1.2 hB
  · rw [Finset.disjoint_left]
    intro x hx1 hx3
    rw [Finset.mem_sdiff] at hx1
    simp only [Finset.mem_inter] at hx3
    exact hx1.2 hx3.2.2
  · rw [Finset.disjoint_left]
    intro x hx2 hx3
    rw [Finset.mem_sdiff] at hx2
    simp only [Finset.mem_inter] at hx3
    exact hx2.2 hx3.2.1
  · ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
    · intro hx
      have hcov : x ∈ sep.VA ∪ sep.VB := by rw [sep.union_verts]; exact Finset.mem_univ x
      by_cases hA : x ∈ sep.VA
      · by_cases hB : x ∈ sep.VB
        · exact Or.inr ⟨hx, hA, hB⟩
        · exact Or.inl (Or.inl ⟨hx, hB⟩)
      · have hB : x ∈ sep.VB := (Finset.mem_union.mp hcov).resolve_left hA
        exact Or.inl (Or.inr ⟨hx, hA⟩)
  · omega
  · omega
  · have hsub : Z ∩ (sep.VA ∩ sep.VB) ⊆ sep.VA ∩ sep.VB := Finset.inter_subset_right
    exact (Finset.card_le_card hsub).trans hord

/-- Neighbor set `N_R(Z_i) \ Z` in `V(G) \ Z` for a subset `Z_i ⊆ Z`. -/
noncomputable def extNeighbors {n : ℕ} (R : SimpleGraph (Fin n))
    (Z Z_part : Finset (Fin n)) : Finset (Fin n) :=
  open Classical in
  (Finset.univ \ Z).filter (fun u : Fin n => ∃ z ∈ Z_part, R.Adj z u)

@[simp]
theorem mem_extNeighbors {n : ℕ} (R : SimpleGraph (Fin n)) [DecidableRel R.Adj]
    (Z Z_part : Finset (Fin n)) (u : Fin n) :
    u ∈ extNeighbors R Z Z_part ↔ u ∉ Z ∧ ∃ z ∈ Z_part, R.Adj z u := by
  classical
  unfold extNeighbors
  simp [Finset.mem_sdiff]

/-- Helper for Step (5) of Algorithm (3.3): if `R.Adj x y`, `x` is on the left side
(`x ∈ Z₁ ∨ (x ∉ Z ∧ x.1 + n ∈ items)`), and `y` is not on the left side, then `y` belongs to
`Z₃ ∪ resCut n items`. -/
theorem mem_Z3_or_resCut_of_adj_inLeftSide {n : ℕ}
    {R : SimpleGraph (Fin n)} [DecidableRel R.Adj]
    {Z Z₁ Z₂ Z₃ : Finset (Fin n)}
    (hunion : Z₁ ∪ Z₂ ∪ Z₃ = Z)
    (hno_edge : ∀ z₁ ∈ Z₁, ∀ z₂ ∈ Z₂, ¬ R.Adj z₁ z₂)
    {used pred succ : Fin n → ℕ} {items : List ℕ}
    (hsys : IsValidPathSystem (restrictGraph R (Finset.univ \ Z))
      (extNeighbors R Z Z₁) (extNeighbors R Z Z₂) used pred succ)
    (hclosed : ∀ a b : Fin (2 * n), a.1 ∈ items →
      ResidualAdj (restrictGraph R (Finset.univ \ Z)) used pred succ a b → b.1 ∈ items)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable (ResidualAdj (restrictGraph R (Finset.univ \ Z)) used pred succ)
        {z | ∃ a ∈ extNeighbors R Z Z₁, z = inNode a} z)
    (hinit : ∀ a ∈ extNeighbors R Z Z₁, a.1 ∈ items)
    (hnoB : ∀ b ∈ extNeighbors R Z Z₂, b.1 + n ∉ items)
    {x y : Fin n} (hadj : R.Adj x y)
    (hx : x ∈ Z₁ ∨ (x ∉ Z ∧ x.1 + n ∈ items))
    (hy : ¬ (y ∈ Z₁ ∨ (y ∉ Z ∧ y.1 + n ∈ items))) :
    y ∈ Z₃ ∪ resCut n items := by
  have hy_not_Z1 : y ∉ Z₁ := fun h => hy (Or.inl h)
  have hy_not_Z2 : y ∉ Z₂ := by
    intro hy2
    rcases hx with hx1 | ⟨hx_notZ, hx_out⟩
    · exact hno_edge x hx1 y hy2 hadj
    · have hx_N2 : x ∈ extNeighbors R Z Z₂ := by
        rw [mem_extNeighbors]
        exact ⟨hx_notZ, y, hy2, hadj.symm⟩
      exact hnoB x hx_N2 hx_out
  by_cases hyZ : y ∈ Z
  · rw [← hunion] at hyZ
    simp only [Finset.mem_union] at hyZ ⊢
    rcases hyZ with (h1 | h2) | h3
    · exact False.elim (hy_not_Z1 h1)
    · exact False.elim (hy_not_Z2 h2)
    · exact Or.inl h3
  · have hy_not_out : y.1 + n ∉ items := fun h => hy (Or.inr ⟨hyZ, h⟩)
    apply Finset.mem_union_right
    rw [mem_resCut]
    refine ⟨?_, hy_not_out⟩
    rcases hx with hx1 | ⟨hx_notZ, hx_out⟩
    · have hy_N1 : y ∈ extNeighbors R Z Z₁ := by
        rw [mem_extNeighbors]
        exact ⟨hyZ, x, hx1, hadj⟩
      exact hinit y hy_N1
    · have hadj_sub : (restrictGraph R (Finset.univ \ Z)).Adj x y := by
        simp [restrictGraph, hadj, hx_notZ, hyZ]
      exact inNode_mem_of_outNode_mem_of_adj hsys hinit hclosed hreach hx_out hadj_sub

/-- Step (5) of Algorithm (3.3) (page 74):
When `(Z₁, Z₂, Z₃)` is a valid partition of `Z = leafCutVerts G τ v`, no edge of
`R = leafGraph G τ v` joins `Z₁` to `Z₂`, and the residual BFS in `R \ Z` between
`N₁ = extNeighbors R Z Z₁` and `N₂ = extNeighbors R Z Z₂` stops at `< ω - |Z₃| + 1` paths with
visited list `items`, splitting leaf `v` into `⟨t, _⟩` (receiving edges of `R` with an endpoint
satisfying `u ∈ Z₁ ∨ (u ∉ Z ∧ u.1 + n ∈ items)`) and `⟨t + 1, _⟩` (receiving the remaining edges
of `R`) preserves `IsPartialBranchDecomp`. -/
theorem isPartialBranchDecomp_step5 {n t : ℕ} {ω : ℕ} (hω : 1 ≤ ω)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {p : ℕ → ℕ} (ht : 0 < t) (hp : ∀ z, 0 < z → z < t → p z < z)
    {τ : Sym2 (Fin n) → Fin t}
    (hpart : IsPartialBranchDecomp ω G (parentTree t p) τ)
    {v : Fin t} (hv : v ∈ treeLeaves (parentTree t p))
    {Z₁ Z₂ Z₃ : Finset (Fin n)}
    (hZ : IsValidZPartition ω (leafCutVerts G τ v) Z₁ Z₂ Z₃)
    (hno_edge : ∀ z₁ ∈ Z₁, ∀ z₂ ∈ Z₂, ¬ (leafGraph G τ v).Adj z₁ z₂)
    {used pred succ : Fin n → ℕ} {items : List ℕ}
    (hsys : IsValidPathSystem
      (restrictGraph (leafGraph G τ v) (Finset.univ \ leafCutVerts G τ v))
      (extNeighbors (leafGraph G τ v) (leafCutVerts G τ v) Z₁)
      (extNeighbors (leafGraph G τ v) (leafCutVerts G τ v) Z₂)
      used pred succ)
    (hcard_lt : (pathStarts used pred).card < ω - Z₃.card + 1)
    (hclosed : IsResPopClosed
      (restrictGraph (leafGraph G τ v) (Finset.univ \ leafCutVerts G τ v))
      used pred succ items items.length)
    (hreach : ∀ z : Fin (2 * n), z.1 ∈ items →
      ResReachable
        (ResidualAdj (restrictGraph (leafGraph G τ v) (Finset.univ \ leafCutVerts G τ v))
          used pred succ)
        {z | ∃ a ∈ extNeighbors (leafGraph G τ v) (leafCutVerts G τ v) Z₁, z = inNode a} z)
    (hinit : ∀ a ∈ extNeighbors (leafGraph G τ v) (leafCutVerts G τ v) Z₁, a.1 ∈ items)
    (hnoB : ∀ b ∈ extNeighbors (leafGraph G τ v) (leafCutVerts G τ v) Z₂, b.1 + n ∉ items)
    {τ' : Sym2 (Fin n) → Fin (t + 2)}
    (hτ'_ne : ∀ e ∈ G.edgeFinset, τ e ≠ v → (τ' e).1 = (τ e).1)
    (hτ'_left : ∀ x y : Fin n, (leafGraph G τ v).Adj x y →
      ((x ∈ Z₁ ∨ (x ∉ leafCutVerts G τ v ∧ x.1 + n ∈ items)) ∨
       (y ∈ Z₁ ∨ (y ∉ leafCutVerts G τ v ∧ y.1 + n ∈ items))) →
      τ' s(x, y) = ⟨t, by omega⟩)
    (hτ'_right : ∀ x y : Fin n, (leafGraph G τ v).Adj x y →
      ¬ ((x ∈ Z₁ ∨ (x ∉ leafCutVerts G τ v ∧ x.1 + n ∈ items)) ∨
         (y ∈ Z₁ ∨ (y ∉ leafCutVerts G τ v ∧ y.1 + n ∈ items))) →
      τ' s(x, y) = ⟨t + 1, by omega⟩) :
    IsPartialBranchDecomp ω G (parentTree (t + 2) (splitLeafParent p t v.1)) τ' := by
  let inL (u : Fin n) : Prop := u ∈ Z₁ ∨ (u ∉ leafCutVerts G τ v ∧ u.1 + n ∈ items)
  have hclosed_all := hclosed.to_closed
  have hZ3_le : Z₃.card ≤ ω := hZ.card_Z3
  have hcut_card : (resCut n items).card + Z₃.card ≤ ω := by
    have hle := card_resCut_le_card_pathStarts hsys hclosed_all
    omega
  refine isPartialBranchDecomp_splitLeaf ht hp hpart hv hτ'_ne ?_ ?_ ?_ ?_ ?_
  · -- Every edge `e` with `τ e = v` maps to `t` or `t + 1`
    intro e he he_v
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      have hadj_R : (leafGraph G τ v).Adj x y := ⟨he, he_v⟩
      by_cases hxy : inL x ∨ inL y
      · exact Or.inl (congrArg Fin.val (hτ'_left x y hadj_R hxy))
      · exact Or.inr (congrArg Fin.val (hτ'_right x y hadj_R hxy))
  · -- Surjectivity onto `⟨t, _⟩` via `Z₁.Nonempty`
    rcases hZ.Z1_nonempty hω with ⟨z₁, hz₁⟩
    have hz₁_Z : z₁ ∈ leafCutVerts G τ v := by
      rw [← hZ.union_eq]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hz₁)
    rcases ((mem_leafCutVerts G τ v z₁).mp hz₁_Z).1 with ⟨e₁, he₁, hz₁_e₁, he₁_v⟩
    refine ⟨e₁, he₁, ?_⟩
    induction e₁ using Sym2.ind with
    | _ x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he₁
      have hadj_R : (leafGraph G τ v).Adj x y := ⟨he₁, he₁_v⟩
      rcases Sym2.mem_iff.mp hz₁_e₁ with rfl | rfl
      · exact hτ'_left z₁ y hadj_R (Or.inl (Or.inl hz₁))
      · exact hτ'_left x z₁ hadj_R (Or.inr (Or.inl hz₁))
  · -- Surjectivity onto `⟨t + 1, _⟩` via `Z₂.Nonempty`
    rcases hZ.Z2_nonempty hω with ⟨z₂, hz₂⟩
    have hz₂_Z : z₂ ∈ leafCutVerts G τ v := by
      rw [← hZ.union_eq]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hz₂)
    rcases ((mem_leafCutVerts G τ v z₂).mp hz₂_Z).1 with ⟨e₂, he₂, hz₂_e₂, he₂_v⟩
    refine ⟨e₂, he₂, ?_⟩
    induction e₂ using Sym2.ind with
    | _ x y =>
      rw [mem_edgeFinset, mem_edgeSet] at he₂
      have hadj_R : (leafGraph G τ v).Adj x y := ⟨he₂, he₂_v⟩
      have hnot_inL_of_adj_z2 : ∀ u : Fin n, (leafGraph G τ v).Adj z₂ u → ¬ inL u := by
        intro u hadj_zu hu
        rcases hu with hu1 | ⟨hu_notZ, hu_out⟩
        · exact hno_edge u hu1 z₂ hz₂ hadj_zu.symm
        · have hu_N2 : u ∈ extNeighbors (leafGraph G τ v) (leafCutVerts G τ v) Z₂ := by
            rw [mem_extNeighbors]
            exact ⟨hu_notZ, z₂, hz₂, hadj_zu⟩
          exact hnoB u hu_N2 hu_out
      have hnot_z2 : ¬ inL z₂ := by
        rintro (hz2_1 | ⟨hz2_notZ, _⟩)
        · exact Finset.disjoint_left.mp hZ.disj12 hz2_1 hz₂
        · exact hz2_notZ hz₂_Z
      rcases Sym2.mem_iff.mp hz₂_e₂ with rfl | rfl
      · exact hτ'_right z₂ y hadj_R (not_or.mpr ⟨hnot_z2, hnot_inL_of_adj_z2 y hadj_R⟩)
      · exact hτ'_right x z₂ hadj_R (not_or.mpr ⟨hnot_inL_of_adj_z2 x hadj_R.symm, hnot_z2⟩)
  · -- Order of `⟨t, _⟩` ≤ 3ω
    have hsub : leafCutVerts G τ' ⟨t, by omega⟩ ⊆ Z₁ ∪ (Z₃ ∪ resCut n items) := by
      intro w hw
      rw [mem_leafCutVerts] at hw
      rcases hw with ⟨⟨e₁, he₁, hw₁, h1⟩, ⟨e₂, he₂, hw₂, h2⟩⟩
      have he₁_v : τ e₁ = v := by
        by_contra hne_v
        have := hτ'_ne e₁ he₁ hne_v
        have h1_val : (τ' e₁).1 = t := congrArg Fin.val h1
        have := (τ e₁).2
        omega
      by_cases hw_L : inL w
      · by_cases he₂_v : τ e₂ = v
        · exfalso
          induction e₂ using Sym2.ind with
          | _ a b =>
            rw [mem_edgeFinset, mem_edgeSet] at he₂
            have hadj_ab : (leafGraph G τ v).Adj a b := ⟨he₂, he₂_v⟩
            rcases Sym2.mem_iff.mp hw₂ with rfl | rfl
            · exact h2 (hτ'_left w b hadj_ab (Or.inl hw_L))
            · exact h2 (hτ'_left a w hadj_ab (Or.inr hw_L))
        · have hw_Z : w ∈ leafCutVerts G τ v := by
            rw [mem_leafCutVerts]
            exact ⟨⟨e₁, he₁, hw₁, he₁_v⟩, ⟨e₂, he₂, hw₂, he₂_v⟩⟩
          rcases hw_L with hw1 | ⟨hw_notZ, _⟩
          · exact Finset.mem_union_left _ hw1
          · exact False.elim (hw_notZ hw_Z)
      · apply Finset.mem_union_right
        induction e₁ using Sym2.ind with
        | _ a b =>
          rw [mem_edgeFinset, mem_edgeSet] at he₁
          have hadj_ab : (leafGraph G τ v).Adj a b := ⟨he₁, he₁_v⟩
          have hab_L : inL a ∨ inL b := by
            by_contra hnot
            have h1_val : (τ' s(a, b)).1 = t := congrArg Fin.val h1
            have h2_val : (τ' s(a, b)).1 = t + 1 :=
              congrArg Fin.val (hτ'_right a b hadj_ab hnot)
            omega
          rcases Sym2.mem_iff.mp hw₁ with rfl | rfl
          · have hb_L : inL b := hab_L.resolve_left hw_L
            exact mem_Z3_or_resCut_of_adj_inLeftSide hZ.union_eq hno_edge hsys hclosed_all
              hreach hinit hnoB hadj_ab.symm hb_L hw_L
          · have ha_L : inL a := hab_L.resolve_right hw_L
            exact mem_Z3_or_resCut_of_adj_inLeftSide hZ.union_eq hno_edge hsys hclosed_all
              hreach hinit hnoB hadj_ab ha_L hw_L
    have hcard1 := (Finset.card_le_card hsub).trans (Finset.card_union_le Z₁ (Z₃ ∪ resCut n items))
    have hcard2 := Finset.card_union_le Z₃ (resCut n items)
    have hZ1_le := hZ.card_Z1
    omega
  · -- Order of `⟨t + 1, _⟩` ≤ 3ω
    have hsub : leafCutVerts G τ' ⟨t + 1, by omega⟩ ⊆ Z₂ ∪ (Z₃ ∪ resCut n items) := by
      intro w hw
      rw [mem_leafCutVerts] at hw
      rcases hw with ⟨⟨e₁, he₁, hw₁, h1⟩, ⟨e₂, he₂, hw₂, h2⟩⟩
      have he₁_v : τ e₁ = v := by
        by_contra hne_v
        have := hτ'_ne e₁ he₁ hne_v
        have h1_val : (τ' e₁).1 = t + 1 := congrArg Fin.val h1
        have := (τ e₁).2
        omega
      have hw_not_L : ¬ inL w := by
        intro hw_L
        induction e₁ using Sym2.ind with
        | _ a b =>
          rw [mem_edgeFinset, mem_edgeSet] at he₁
          have hadj_ab : (leafGraph G τ v).Adj a b := ⟨he₁, he₁_v⟩
          rcases Sym2.mem_iff.mp hw₁ with rfl | rfl
          · have h1_val : (τ' s(w, b)).1 = t + 1 := congrArg Fin.val h1
            have h2_val : (τ' s(w, b)).1 = t :=
              congrArg Fin.val (hτ'_left w b hadj_ab (Or.inl hw_L))
            omega
          · have h1_val : (τ' s(a, w)).1 = t + 1 := congrArg Fin.val h1
            have h2_val : (τ' s(a, w)).1 = t :=
              congrArg Fin.val (hτ'_left a w hadj_ab (Or.inr hw_L))
            omega
      by_cases he₂_v : τ e₂ = v
      · apply Finset.mem_union_right
        induction e₂ using Sym2.ind with
        | _ a b =>
          rw [mem_edgeFinset, mem_edgeSet] at he₂
          have hadj_ab : (leafGraph G τ v).Adj a b := ⟨he₂, he₂_v⟩
          have hab_L : inL a ∨ inL b := by
            by_contra hnot
            exact h2 (hτ'_right a b hadj_ab hnot)
          rcases Sym2.mem_iff.mp hw₂ with rfl | rfl
          · have hb_L : inL b := hab_L.resolve_left hw_not_L
            exact mem_Z3_or_resCut_of_adj_inLeftSide hZ.union_eq hno_edge hsys hclosed_all
              hreach hinit hnoB hadj_ab.symm hb_L hw_not_L
          · have ha_L : inL a := hab_L.resolve_right hw_not_L
            exact mem_Z3_or_resCut_of_adj_inLeftSide hZ.union_eq hno_edge hsys hclosed_all
              hreach hinit hnoB hadj_ab ha_L hw_not_L
      · have hw_Z : w ∈ leafCutVerts G τ v := by
          rw [mem_leafCutVerts]
          exact ⟨⟨e₁, he₁, hw₁, he₁_v⟩, ⟨e₂, he₂, hw₂, he₂_v⟩⟩
        rw [← hZ.union_eq] at hw_Z
        simp only [Finset.mem_union] at hw_Z ⊢
        rcases hw_Z with (h1' | h2') | h3'
        · exact False.elim (hw_not_L (Or.inl h1'))
        · exact Or.inl h2'
        · exact Or.inr (Or.inl h3')
    have hcard1 := (Finset.card_le_card hsub).trans (Finset.card_union_le Z₂ (Z₃ ∪ resCut n items))
    have hcard2 := Finset.card_union_le Z₃ (resCut n items)
    have hZ2_le := hZ.card_Z2
    omega

/-- Any walk in `restrictGraph (leafGraph G τ v) (Finset.univ \ Z)` from `u ∈ G_sep.VA` to
`w ∈ G_sep.VB` contains a vertex in `(G_sep.VA ∩ G_sep.VB) \ Z`. -/
theorem walk_restrictGraph_hits_inter_sdiff {n t : ℕ}
    {G : SimpleGraph (Fin n)} (sep : GraphSeparation G)
    {τ : Sym2 (Fin n) → Fin t} {v : Fin t} {Z : Finset (Fin n)}
    {u w : Fin n}
    (p : (restrictGraph (leafGraph G τ v) (Finset.univ \ Z)).Walk u w)
    (hu : u ∈ sep.VA) (hw : w ∈ sep.VB)
    (hu_notZ : u ∉ Z) :
    ∃ x ∈ (sep.VA ∩ sep.VB) \ Z, x ∈ p.support := by
  induction p with
  | nil =>
    rename_i u
    exact ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hu, hw⟩, hu_notZ⟩, by simp⟩
  | @cons x y z hadj tail ih =>
    have hadj_G : G.Adj x y := hadj.2.2.1
    have hy_notZ : y ∉ Z := by
      have hy_mem := hadj.2.1
      simpa using hy_mem
    by_cases hxB : x ∈ sep.VB
    · exact ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hu, hxB⟩, hu_notZ⟩, by simp⟩
    · have hyA : y ∈ sep.VA := by
        rcases sep.adj_endpoints hadj_G with ⟨_, hyA⟩ | ⟨hxB', _⟩
        · exact hyA
        · exact False.elim (hxB hxB')
      rcases ih hyA hw hy_notZ with ⟨q, hq_mem, hq_supp⟩
      exact ⟨q, hq_mem, by simp [hq_supp]⟩

/-- Step (6) soundness (page 74):
If `|Z| = 3ω` (where `Z = leafCutVerts G τ v`) and for every valid partition `(Z₁, Z₂, Z₃)` of `Z`,
either `leafGraph G τ v` has an edge between `Z₁` and `Z₂` or there exist `ω - |Z₃| + 1`
pairwise vertex-disjoint walks in `restrictGraph (leafGraph G τ v) (Finset.univ \ Z)` from
`extNeighbors (leafGraph G τ v) Z Z₁` to `extNeighbors (leafGraph G τ v) Z Z₂`, then `G` has **no**
separation `sep : GraphSeparation G` of order `≤ ω` satisfying `sep.IsBalancedQ Z`. -/
theorem no_balanced_separation_of_step6 {n t : ℕ} {ω : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {τ : Sym2 (Fin n) → Fin t} {v : Fin t}
    (hZ_card : (leafCutVerts G τ v).card = 3 * ω)
    (hall : ∀ Z₁ Z₂ Z₃ : Finset (Fin n),
      IsValidZPartition ω (leafCutVerts G τ v) Z₁ Z₂ Z₃ →
      (∃ z₁ ∈ Z₁, ∃ z₂ ∈ Z₂, (leafGraph G τ v).Adj z₁ z₂) ∨
      (∃ P : Fin (ω - Z₃.card + 1) →
          ABWalk (restrictGraph (leafGraph G τ v) (Finset.univ \ leafCutVerts G τ v))
            (extNeighbors (leafGraph G τ v) (leafCutVerts G τ v) Z₁)
            (extNeighbors (leafGraph G τ v) (leafCutVerts G τ v) Z₂),
        PairwiseVertexDisjoint P))
    (sep : GraphSeparation G) (hord : sep.order ≤ ω) :
    ¬ sep.IsBalancedQ (leafCutVerts G τ v) := by
  intro hbal
  let Z := leafCutVerts G τ v
  let Z₁ := Z \ sep.VB
  let Z₂ := Z \ sep.VA
  let Z₃ := Z ∩ (sep.VA ∩ sep.VB)
  have hvalid : IsValidZPartition ω Z Z₁ Z₂ Z₃ :=
    sep.to_isValidZPartition hZ_card hord hbal
  rcases hall Z₁ Z₂ Z₃ hvalid with ⟨z₁, hz₁, z₂, hz₂, hadj⟩ | ⟨P, hdisj⟩
  · exact sep.not_adj_sdiff (Finset.mem_sdiff.mp hz₁).2 (Finset.mem_sdiff.mp hz₂).2 hadj.1
  · have hit : ∀ i : Fin (ω - Z₃.card + 1),
        ∃ x ∈ (sep.VA ∩ sep.VB) \ Z, x ∈ (P i).walk.support := by
      intro i
      have hs := (mem_extNeighbors (leafGraph G τ v) Z Z₁ (P i).start).mp (P i).start_mem
      have hf := (mem_extNeighbors (leafGraph G τ v) Z Z₂ (P i).finish).mp (P i).finish_mem
      rcases hs with ⟨hs_notZ, z₁, hz₁, hadj1⟩
      rcases hf with ⟨_, z₂, hz₂, hadj2⟩
      have hz₁_notB : z₁ ∉ sep.VB := (Finset.mem_sdiff.mp hz₁).2
      have hz₂_notA : z₂ ∉ sep.VA := (Finset.mem_sdiff.mp hz₂).2
      have hs_A : (P i).start ∈ sep.VA := by
        rcases sep.adj_endpoints hadj1.1 with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact False.elim (hz₁_notB h)
      have hf_B : (P i).finish ∈ sep.VB := by
        rcases sep.adj_endpoints hadj2.1 with ⟨h, _⟩ | ⟨_, h⟩
        · exact False.elim (hz₂_notA h)
        · exact h
      exact walk_restrictGraph_hits_inter_sdiff sep (P i).walk hs_A hf_B hs_notZ
    choose f hf_mem hf_supp using hit
    have hinj : Function.Injective f := by
      intro i j hij
      by_contra hne
      exact hdisj i j hne (hf_supp i) (hij ▸ hf_supp j)
    have hcard_f : ω - Z₃.card + 1 ≤ ((sep.VA ∩ sep.VB) \ Z).card := by
      have hsub : Finset.univ.image f ⊆ (sep.VA ∩ sep.VB) \ Z := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
        exact hf_mem i
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hinj, Finset.card_fin] at h1
      exact h1
    have hpart_inter :
        ((sep.VA ∩ sep.VB) \ Z).card + Z₃.card = (sep.VA ∩ sep.VB).card := by
      have hZ3_eq : Z₃ = (sep.VA ∩ sep.VB) ∩ Z := Finset.inter_comm _ _
      rw [hZ3_eq, Finset.card_sdiff_add_card_inter]
    have hZ3_le : Z₃.card ≤ ω := hvalid.card_Z3
    unfold GraphSeparation.order at hord
    omega

/-- Step (6) of Algorithm (3.3) (page 74):
Deleting an edge `g ∈ G.edgeFinset` with `τ g = v` when there is another edge `e' ≠ g` with
`τ e' = v` preserves `IsPartialBranchDecomp`. -/
theorem isPartialBranchDecomp_step6 {n t : ℕ} {ω : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Sym2 (Fin n) → Fin t}
    (hpart : IsPartialBranchDecomp ω G T τ)
    {v : Fin t}
    {g : Sym2 (Fin n)} (hg_v : τ g = v)
    (hother : ∃ e' ∈ G.edgeFinset, τ e' = v ∧ e' ≠ g) :
    IsPartialBranchDecomp ω (G.deleteEdges {g}) T τ := by
  have hsub : G.deleteEdges {g} ≤ G := SimpleGraph.deleteEdges_le {g}
  refine ⟨hpart.1, ?_, ?_, ?_⟩
  · intro e he
    rw [mem_edgeFinset] at he
    have he_G : e ∈ G.edgeFinset := by
      rw [mem_edgeFinset]
      exact SimpleGraph.edgeSet_mono hsub he
    exact hpart.2.1 e he_G
  · intro w hw
    by_cases hwv : w = v
    · subst hwv
      rcases hother with ⟨e', he'_G, he'_v, he'_ne⟩
      refine ⟨e', ?_, he'_v⟩
      rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨(mem_edgeFinset.mp he'_G), he'_ne⟩
    · rcases hpart.2.2.1 w hw with ⟨e, he_G, he_w⟩
      have he_ne_g : e ≠ g := by
        intro h
        subst h
        exact hwv (he_w.symm.trans hg_v)
      refine ⟨e, ?_, he_w⟩
      rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
      exact ⟨(mem_edgeFinset.mp he_G), he_ne_g⟩
  · intro f hf
    exact (treeEdgeOrder_mono_subgraph hsub T τ f).trans (hpart.2.2.2 f hf)

end GraphMinor.Compute


