module

public import GraphMinor.Compute.Algorithm86Aux4

/-!
# Subgraph Representations, `GM13` Division Bridge, and Raw Division Equivalence for (8.6)

This file defines the subgraph and boundary structures for GM XIII Algorithm (8.6) (`Alg86Subgraph`,
`alg86Boundary`, `alg86RawDivision`, `alg86Division`), proves their equivalence with `GM13`'s
`coreRawDivision` and `coreDivision`, and proves that the raw pair list `alg86RawPairList` emitted
by `alg86DivisionsProg` decodes to `alg86RawDivision x Z` (`setOf_mem_map_alg86RawPairList`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Subgraphs, Boundaries, Raw Family `𝒜'`, and Quotient Family `𝒜` -/

/-- A subgraph $A = (V(A), E(A))$ of $G : \text{SimpleGraph (Fin } n)$, given by its vertex set
`verts : Finset (Fin n)` and edge relation `graph : SimpleGraph (Fin n)` with `graph ≤ G` and all
edges having both endpoints in `verts`. -/
@[ext]
structure Alg86Subgraph {n : ℕ} (G : SimpleGraph (Fin n)) where
  /-- Vertex set $V(A) \subseteq V(G)$. -/
  verts : Finset (Fin n)
  /-- Edge relation $E(A) \subseteq E(G)$. -/
  graph : SimpleGraph (Fin n)
  /-- Every edge of $A$ is an edge of $G$. -/
  sub : graph ≤ G
  /-- Both endpoints of every edge of $A$ belong to $V(A)$. -/
  adj_verts : ∀ u v : Fin n, graph.Adj u v → u ∈ verts ∧ v ∈ verts

/-- Convert an `Alg86Subgraph G` to a `SimpleGraph.Subgraph G`. -/
def Alg86Subgraph.toSubgraph {n : ℕ} {G : SimpleGraph (Fin n)}
    (A : Alg86Subgraph G) : G.Subgraph where
  verts := (A.verts : Set (Fin n))
  Adj := A.graph.Adj
  adj_sub := fun {_ _} h => A.sub h
  edge_vert := fun {u v} h => (A.adj_verts u v h).1
  symm := A.graph.symm

/-- Boundary $\partial A$ of a subgraph $A$ of $G$ in a society $(G, \Omega)$
(Graph Minors XIII, Section 8, page 95):
"For a subgraph $A$ of $G$ we define $\partial A$ to be the set of all $v \in V(A)$ such that
either $v \in \tilde{\Omega}$ or $v$ is incident with an edge of $G$ not in $A$." -/
noncomputable def alg86Boundary (x : Alg81Input) (A : Alg86Subgraph x.G) : Finset (Fin x.n) :=
  open Classical in
  A.verts.filter (fun v => v ∈ x.omega.toFinset ∨ ∃ w : Fin x.n, x.G.Adj v w ∧ ¬ A.graph.Adj v w)

@[simp]
theorem mem_alg86Boundary (x : Alg81Input) (A : Alg86Subgraph x.G) (v : Fin x.n) :
    v ∈ alg86Boundary x A ↔
      v ∈ A.verts ∧ (v ∈ x.omega.toFinset ∨ ∃ w : Fin x.n, x.G.Adj v w ∧ ¬ A.graph.Adj v w) := by
  classical
  simp [alg86Boundary]

theorem alg86Boundary_subset_verts (x : Alg81Input) (A : Alg86Subgraph x.G) :
    alg86Boundary x A ⊆ A.verts := by
  intro v hv
  exact ((mem_alg86Boundary x A v).mp hv).1

/-- Predicate stating that `K : Finset (Fin n)` is the vertex set of a connected component of
$G \setminus Z$ (`restrictGraph G (Finset.univ \ Z)`). -/
def IsComponentOutsideCore {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n))
    (K : Finset (Fin n)) : Prop :=
  ∃ v₀ : Fin n, v₀ ∉ Z ∧
    ∀ u : Fin n, u ∈ K ↔ u ∉ Z ∧ (restrictGraph G (Finset.univ \ Z)).Reachable v₀ u

theorem IsComponentOutsideCore.nonempty {n : ℕ} {G : SimpleGraph (Fin n)}
    {Z K : Finset (Fin n)} (hK : IsComponentOutsideCore G Z K) :
    K.Nonempty := by
  rcases hK with ⟨v₀, hv₀, hmem⟩
  exact ⟨v₀, (hmem v₀).mpr ⟨hv₀, Reachable.refl v₀⟩⟩

theorem IsComponentOutsideCore.not_mem_Z {n : ℕ} {G : SimpleGraph (Fin n)}
    {Z K : Finset (Fin n)} (hK : IsComponentOutsideCore G Z K) {u : Fin n} (hu : u ∈ K) :
    u ∉ Z := by
  rcases hK with ⟨_, _, hmem⟩
  exact ((hmem u).mp hu).1

theorem IsComponentOutsideCore.disjoint_Z {n : ℕ} {G : SimpleGraph (Fin n)}
    {Z K : Finset (Fin n)} (hK : IsComponentOutsideCore G Z K) :
    Disjoint K Z :=
  Finset.disjoint_left.mpr fun _ hu => hK.not_mem_Z hu

theorem IsComponentOutsideCore.closed_outside_Z {n : ℕ} {G : SimpleGraph (Fin n)}
    {Z K : Finset (Fin n)} (hK : IsComponentOutsideCore G Z K)
    {u w : Fin n} (hu : u ∈ K) (hw : w ∉ Z) (hadj : G.Adj u w) :
    w ∈ K := by
  rcases hK with ⟨v₀, _, hmem⟩
  obtain ⟨huZ, hreach⟩ := (hmem u).mp hu
  have hadj_res : (restrictGraph G (Finset.univ \ Z)).Adj u w := by
    simp [restrictGraph, huZ, hw, hadj]
  exact (hmem w).mpr ⟨hw, hreach.trans hadj_res.reachable⟩

theorem IsComponentOutsideCore.adj_iff_mem_or_mem {n : ℕ} {G : SimpleGraph (Fin n)}
    {Z K : Finset (Fin n)} (hK : IsComponentOutsideCore G Z K) (a b : Fin n) :
    (G.Adj a b ∧ ((a ∈ K ∧ b ∈ K) ∨ (a ∈ K ∧ b ∈ Z) ∨ (a ∈ Z ∧ b ∈ K))) ↔
      (G.Adj a b ∧ (a ∈ K ∨ b ∈ K)) := by
  constructor
  · rintro ⟨hadj, ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨_, hb⟩⟩
    · exact ⟨hadj, Or.inl ha⟩
    · exact ⟨hadj, Or.inl ha⟩
    · exact ⟨hadj, Or.inr hb⟩
  · rintro ⟨hadj, ha | hb⟩
    · by_cases hbZ : b ∈ Z
      · exact ⟨hadj, Or.inr (Or.inl ⟨ha, hbZ⟩)⟩
      · exact ⟨hadj, Or.inl ⟨ha, hK.closed_outside_Z ha hbZ hadj⟩⟩
    · by_cases haZ : a ∈ Z
      · exact ⟨hadj, Or.inr (Or.inr ⟨haZ, hb⟩)⟩
      · exact ⟨hadj, Or.inl ⟨hK.closed_outside_Z hb haZ hadj.symm, hb⟩⟩

/-- Condition (i) of GM XIII (8.6) (page 96):
"$A$ consists of an edge of $G$ with both ends in $V(C)$, and its ends". -/
def IsAlg86TypeI (x : Alg81Input) (Z : Finset (Fin x.n)) (A : Alg86Subgraph x.G) : Prop :=
  ∃ u v : Fin x.n, u ∈ Z ∧ v ∈ Z ∧ x.G.Adj u v ∧
    A.verts = {u, v} ∧
    ∀ a b : Fin x.n, A.graph.Adj a b ↔ (a = u ∧ b = v) ∨ (a = v ∧ b = u)

/-- Condition (ii) of GM XIII (8.6) (page 96):
"$A$ consists of a component of $G \setminus V(C)$, together with all edges of $G$ between this
component and $V(C)$, and their ends". -/
def IsAlg86TypeII (x : Alg81Input) (Z : Finset (Fin x.n)) (A : Alg86Subgraph x.G) : Prop :=
  ∃ K : Finset (Fin x.n),
    IsComponentOutsideCore x.G Z K ∧
    A.verts = K ∪ Z.filter (fun z => ∃ u ∈ K, x.G.Adj u z) ∧
    ∀ a b : Fin x.n, A.graph.Adj a b ↔
      x.G.Adj a b ∧ ((a ∈ K ∧ b ∈ K) ∨ (a ∈ K ∧ b ∈ Z) ∨ (a ∈ Z ∧ b ∈ K))

/-- Condition (iii) of GM XIII (8.6) (page 96):
"$A$ consists of a vertex $v \in \tilde{\Omega}$ incident with no edges of $G$." -/
def IsAlg86TypeIII (x : Alg81Input) (A : Alg86Subgraph x.G) : Prop :=
  ∃ v ∈ x.omega.toFinset, (∀ w : Fin x.n, ¬ x.G.Adj v w) ∧
    A.verts = {v} ∧ A.graph = ⊥

/-- Membership in the raw family $\mathcal{A}'$ of GM XIII (8.6) (page 96):
$A$ satisfies condition (i), (ii), or (iii) with respect to $Z = V(C)$. -/
def IsInAlg86RawDivision (x : Alg81Input) (Z : Finset (Fin x.n)) (A : Alg86Subgraph x.G) : Prop :=
  IsAlg86TypeI x Z A ∨ IsAlg86TypeII x Z A ∨ IsAlg86TypeIII x A

/-- The raw family $\mathcal{A}'$ of subgraphs of $x.G$ in GM XIII (8.6) (page 96). -/
def alg86RawDivision (x : Alg81Input) (Z : Finset (Fin x.n)) : Set (Alg86Subgraph x.G) :=
  { A | IsInAlg86RawDivision x Z A }

/-- Equivalence relation on subgraphs in GM XIII (8.6) (page 96):
"say $A_1, A_2 \in \mathcal{A}'$ are *equivalent* if $\partial A_1 = \partial A_2$". -/
def Alg86BoundaryEquiv (x : Alg81Input) (A₁ A₂ : Alg86Subgraph x.G) : Prop :=
  alg86Boundary x A₁ = alg86Boundary x A₂

/-- The equivalence class in $\mathcal{A}'$ of a subgraph $A_0$ under boundary equality
$\partial A = \partial A_0$. -/
def alg86EquivClass (x : Alg81Input) (Z : Finset (Fin x.n)) (A₀ : Alg86Subgraph x.G) :
    Set (Alg86Subgraph x.G) :=
  { A ∈ alg86RawDivision x Z | Alg86BoundaryEquiv x A A₀ }

/-- Union $\bigcup(A : A \in \mathcal{B})$ of a family $\mathcal{B}$ of subgraphs of $G$. -/
noncomputable def alg86SubgraphUnion {n : ℕ} {G : SimpleGraph (Fin n)}
    (ℬ : Set (Alg86Subgraph G)) : Alg86Subgraph G where
  verts := open Classical in Finset.univ.filter (fun v => ∃ A ∈ ℬ, v ∈ A.verts)
  graph := {
    Adj := fun u v => ∃ A ∈ ℬ, A.graph.Adj u v
    symm := ⟨fun _ _ ⟨A, hA, hadj⟩ => ⟨A, hA, hadj.symm⟩⟩
    loopless := ⟨fun _ ⟨A, _, hadj⟩ => A.graph.loopless.irrefl _ hadj⟩
  }
  sub := fun _ _ ⟨A, _, hadj⟩ => A.sub hadj
  adj_verts := by
    classical
    intro u v ⟨A, hA, hadj⟩
    obtain ⟨hu, hv⟩ := A.adj_verts u v hadj
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u, A, hA, hu⟩,
           Finset.mem_filter.mpr ⟨Finset.mem_univ v, A, hA, hv⟩⟩

@[simp]
theorem mem_verts_alg86SubgraphUnion {n : ℕ} {G : SimpleGraph (Fin n)}
    (ℬ : Set (Alg86Subgraph G)) (v : Fin n) :
    v ∈ (alg86SubgraphUnion ℬ).verts ↔ ∃ A ∈ ℬ, v ∈ A.verts := by
  classical
  simp [alg86SubgraphUnion]

@[simp]
theorem adj_alg86SubgraphUnion {n : ℕ} {G : SimpleGraph (Fin n)}
    (ℬ : Set (Alg86Subgraph G)) (u v : Fin n) :
    (alg86SubgraphUnion ℬ).graph.Adj u v ↔ ∃ A ∈ ℬ, A.graph.Adj u v :=
  Iff.rfl

/-- Membership in the family $\mathcal{A}$ of GM XIII (8.6) (page 96):
$$\mathcal{A} = \left\{ \bigcup(A : A \in \mathcal{A}_i) : 1 \le i \le k \right\}$$
where $\mathcal{A}_1, \dots, \mathcal{A}_k$ are the (non-empty) equivalence classes of
$\mathcal{A}'$ under $\partial A_1 = \partial A_2$. -/
def IsInAlg86Division (x : Alg81Input) (Z : Finset (Fin x.n)) (B : Alg86Subgraph x.G) : Prop :=
  ∃ A₀ ∈ alg86RawDivision x Z, B = alg86SubgraphUnion (alg86EquivClass x Z A₀)

/-- The output family $\mathcal{A}$ of GM XIII (8.6) (page 96). -/
def alg86Division (x : Alg81Input) (Z : Finset (Fin x.n)) : Set (Alg86Subgraph x.G) :=
  { B | IsInAlg86Division x Z B }

/-! ### Section 2: Structural Properties of `𝒜'` and `𝒜` (Claims (2) and (3) of (8.6)) -/

/-- Explicit constructor for a Type (i) subgraph $A \in \mathcal{A}'$ from an edge $uv \in E(G)$
with $u, v \in Z$. -/
def mkAlg86TypeI (x : Alg81Input) {u v : Fin x.n} (hadj : x.G.Adj u v) : Alg86Subgraph x.G where
  verts := {u, v}
  graph := {
    Adj := fun a b => (a = u ∧ b = v) ∨ (a = v ∧ b = u)
    symm := ⟨by
      intro a b h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩⟩
    loopless := ⟨by
      intro a h
      rcases h with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
      · exact x.G.ne_of_adj hadj h2
      · exact x.G.ne_of_adj hadj.symm h2⟩
  }
  sub := by
    intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm
  adj_verts := by
    intro a b h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem isAlg86TypeI_mkAlg86TypeI (x : Alg81Input) (Z : Finset (Fin x.n))
    {u v : Fin x.n} (hu : u ∈ Z) (hv : v ∈ Z) (hadj : x.G.Adj u v) :
    IsAlg86TypeI x Z (mkAlg86TypeI x hadj) :=
  ⟨u, v, hu, hv, hadj, rfl, fun _ _ => Iff.rfl⟩

/-- Explicit constructor for a Type (ii) subgraph $A \in \mathcal{A}'$ from a component $K$ of
$G \setminus Z$. -/
noncomputable def mkAlg86TypeII (x : Alg81Input) (Z K : Finset (Fin x.n))
    (_hK : IsComponentOutsideCore x.G Z K) : Alg86Subgraph x.G where
  verts := open Classical in K ∪ Z.filter (fun z => ∃ u ∈ K, x.G.Adj u z)
  graph := {
    Adj := fun a b => x.G.Adj a b ∧ ((a ∈ K ∧ b ∈ K) ∨ (a ∈ K ∧ b ∈ Z) ∨ (a ∈ Z ∧ b ∈ K))
    symm := ⟨by
      intro a b ⟨hadj, hmem⟩
      refine ⟨hadj.symm, ?_⟩
      rcases hmem with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Or.inl ⟨hb, ha⟩
      · exact Or.inr (Or.inr ⟨hb, ha⟩)
      · exact Or.inr (Or.inl ⟨hb, ha⟩)⟩
    loopless := ⟨fun a ⟨hadj, _⟩ => x.G.loopless.irrefl a hadj⟩
  }
  sub := fun _ _ h => h.1
  adj_verts := by
    classical
    intro a b ⟨hadj, hmem⟩
    rcases hmem with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact ⟨Finset.mem_union_left _ ha, Finset.mem_union_left _ hb⟩
    · exact ⟨Finset.mem_union_left _ ha,
        Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, a, ha, hadj⟩)⟩
    · exact ⟨Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha, b, hb, hadj.symm⟩),
        Finset.mem_union_left _ hb⟩

theorem isAlg86TypeII_mkAlg86TypeII (x : Alg81Input) (Z K : Finset (Fin x.n))
    (hK : IsComponentOutsideCore x.G Z K) :
    IsAlg86TypeII x Z (mkAlg86TypeII x Z K hK) :=
  ⟨K, hK, rfl, fun _ _ => Iff.rfl⟩

/-- Explicit constructor for a Type (iii) subgraph $A \in \mathcal{A}'$ from an isolated vertex
$v \in \tilde{\Omega}$. -/
def mkAlg86TypeIII (x : Alg81Input) (v : Fin x.n) : Alg86Subgraph x.G where
  verts := {v}
  graph := ⊥
  sub := bot_le
  adj_verts := fun _ _ h => False.elim h

theorem isAlg86TypeIII_mkAlg86TypeIII (x : Alg81Input) {v : Fin x.n}
    (hv : v ∈ x.omega.toFinset) (hiso : ∀ w : Fin x.n, ¬ x.G.Adj v w) :
    IsAlg86TypeIII x (mkAlg86TypeIII x v) :=
  ⟨v, hv, hiso, rfl, rfl⟩

/-- **GM XIII (8.6), Claim (2) (converse inclusion)** (page 97):
"let $v \in \partial A$. Then $v \in V(A)$, and we claim that $v \in V(C)$. Since
$\tilde{\Omega} \subseteq V(C)$ we may assume that $v \notin \tilde{\Omega}$, and so there is an
edge $e$ of $G$ incident with $v$, with $e \notin E(A)$. By definition of $\mathcal{A}'$,
$v \in V(C)$ as required." -/
theorem alg86Boundary_subset_inter_Z (x : Alg81Input) (Z : Finset (Fin x.n))
    (hom_sub : x.omega.toFinset ⊆ Z) {A : Alg86Subgraph x.G}
    (hA : A ∈ alg86RawDivision x Z) :
    alg86Boundary x A ⊆ A.verts ∩ Z := by
  intro v hv
  obtain ⟨hvA, hv_om | ⟨w, hadj_vw, hnot_A⟩⟩ := (mem_alg86Boundary x A v).mp hv
  · exact Finset.mem_inter.mpr ⟨hvA, hom_sub hv_om⟩
  · refine Finset.mem_inter.mpr ⟨hvA, ?_⟩
    rcases hA with ⟨u₁, u₂, hu₁Z, hu₂Z, _, hverts, _⟩ | ⟨K, hK, hverts, hadj_iff⟩ |
        ⟨u₀, hu₀_om, _, hverts, _⟩
    · rw [hverts, Finset.mem_insert, Finset.mem_singleton] at hvA
      rcases hvA with rfl | rfl
      · exact hu₁Z
      · exact hu₂Z
    · by_contra hvZ
      rw [hverts, Finset.mem_union, Finset.mem_filter] at hvA
      rcases hvA with hvK | ⟨hvZ', _⟩
      · have hadj_in_A : A.graph.Adj v w := by
          rw [hadj_iff, hK.adj_iff_mem_or_mem]
          exact ⟨hadj_vw, Or.inl hvK⟩
        exact hnot_A hadj_in_A
      · exact hvZ hvZ'
    · rw [hverts, Finset.mem_singleton] at hvA
      subst hvA
      exact hom_sub hu₀_om

/-- **GM XIII (8.6), Claim (2)** (page 97):
For each $A \in \mathcal{A}'$, if $\tilde{\Omega} \subseteq Z$ and $V(A) \cap Z \subseteq \partial A$,
then $\partial A = V(A) \cap Z$. -/
theorem alg86Boundary_eq_inter_Z (x : Alg81Input) (Z : Finset (Fin x.n))
    (hom_sub : x.omega.toFinset ⊆ Z) {A : Alg86Subgraph x.G}
    (hA : A ∈ alg86RawDivision x Z)
    (hinter_sub : A.verts ∩ Z ⊆ alg86Boundary x A) :
    alg86Boundary x A = A.verts ∩ Z :=
  Finset.Subset.antisymm (alg86Boundary_subset_inter_Z x Z hom_sub hA) hinter_sub

/-- **GM XIII (8.6), Claim (3) (upper bound)** (page 97):
"Let $X \subseteq V(G)$, let $\mathcal{B} = \{A \in \mathcal{A}' : \partial A = X\}$, and let
$B = \bigcup(A : A \in \mathcal{B})$. Then $\partial B = X$, if $\mathcal{B} \ne \emptyset$.
*Subproof.* Certainly $\partial B \subseteq X$." -/
theorem alg86Boundary_subgraphUnion_subset (x : Alg81Input)
    (ℬ : Set (Alg86Subgraph x.G)) (X : Finset (Fin x.n))
    (hℬ : ∀ A ∈ ℬ, alg86Boundary x A = X) :
    alg86Boundary x (alg86SubgraphUnion ℬ) ⊆ X := by
  intro v hv
  obtain ⟨hvB, hv_om | ⟨w, hadj_vw, hnot_B⟩⟩ :=
    (mem_alg86Boundary x (alg86SubgraphUnion ℬ) v).mp hv
  · rcases (mem_verts_alg86SubgraphUnion ℬ v).mp hvB with ⟨A, hAℬ, hvA⟩
    rw [← hℬ A hAℬ, mem_alg86Boundary]
    exact ⟨hvA, Or.inl hv_om⟩
  · rcases (mem_verts_alg86SubgraphUnion ℬ v).mp hvB with ⟨A, hAℬ, hvA⟩
    rw [← hℬ A hAℬ, mem_alg86Boundary]
    refine ⟨hvA, Or.inr ⟨w, hadj_vw, fun hadj_A => hnot_B ⟨A, hAℬ, hadj_A⟩⟩⟩

/-- Every edge $uv$ of $x.G$ belongs to some subgraph $A \in \mathcal{A}'$, and hence to some
subgraph $B \in \mathcal{A}$. -/
theorem exists_mem_alg86Division_of_adj (x : Alg81Input) (Z : Finset (Fin x.n))
    {u v : Fin x.n} (hadj : x.G.Adj u v) :
    (∃ A ∈ alg86RawDivision x Z, A.graph.Adj u v) ∧
    (∃ B ∈ alg86Division x Z, B.graph.Adj u v) := by
  have hraw : ∃ A ∈ alg86RawDivision x Z, A.graph.Adj u v := by
    by_cases huZ : u ∈ Z
    · by_cases hvZ : v ∈ Z
      · refine ⟨mkAlg86TypeI x hadj,
          Or.inl (isAlg86TypeI_mkAlg86TypeI x Z huZ hvZ hadj), ?_⟩
        exact Or.inl ⟨rfl, rfl⟩
      · classical
        let K := Finset.univ.filter (fun w : Fin x.n =>
          w ∉ Z ∧ (restrictGraph x.G (Finset.univ \ Z)).Reachable v w)
        have hK : IsComponentOutsideCore x.G Z K :=
          ⟨v, hvZ, fun w => by simp [K]⟩
        have hvK : v ∈ K := by simp [K, hvZ]
        refine ⟨mkAlg86TypeII x Z K hK,
          Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z K hK)), ?_⟩
        exact ⟨hadj, Or.inr (Or.inr ⟨huZ, hvK⟩)⟩
    · classical
      let K := Finset.univ.filter (fun w : Fin x.n =>
        w ∉ Z ∧ (restrictGraph x.G (Finset.univ \ Z)).Reachable u w)
      have hK : IsComponentOutsideCore x.G Z K :=
        ⟨u, huZ, fun w => by simp [K]⟩
      have huK : u ∈ K := by simp [K, huZ]
      refine ⟨mkAlg86TypeII x Z K hK,
        Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z K hK)), ?_⟩
      exact (hK.adj_iff_mem_or_mem u v).mpr ⟨hadj, Or.inl huK⟩
  rcases hraw with ⟨A, hA, hadj_A⟩
  refine ⟨⟨A, hA, hadj_A⟩, ?_⟩
  refine ⟨alg86SubgraphUnion (alg86EquivClass x Z A), ⟨A, hA, rfl⟩, ?_⟩
  exact ⟨A, ⟨hA, rfl⟩, hadj_A⟩

/-! ### Section 2b: Bridge to `GM13.coreRawDivision`, `GM13.coreDivision`, and `GM13.IsRuralDivision` -/

/-- Convert `A : Alg86Subgraph G` to a `Graph (Fin n) (Sym2 (Fin n))` by inducing
`Graph.ofSimpleGraph A.graph` on `(A.verts : Set (Fin n))`. -/
def Alg86Subgraph.toGMGraph {n : ℕ} {G : SimpleGraph (Fin n)}
    (A : Alg86Subgraph G) : Graph (Fin n) (Sym2 (Fin n)) :=
  graphOfFinsetSimpleGraph A.verts A.graph

open scoped Graph in
@[simp]
theorem Alg86Subgraph.vertexSet_toGMGraph {n : ℕ} {G : SimpleGraph (Fin n)}
    (A : Alg86Subgraph G) :
    V(A.toGMGraph) = (A.verts : Set (Fin n)) :=
  rfl

theorem Alg86Subgraph.isLink_toGMGraph_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    (A : Alg86Subgraph G) {e : Sym2 (Fin n)} {u v : Fin n} :
    A.toGMGraph.IsLink e u v ↔ e = s(u, v) ∧ A.graph.Adj u v := by
  rw [Alg86Subgraph.toGMGraph, graphOfFinsetSimpleGraph_isLink]
  exact ⟨fun h => h.1, fun ⟨he, hadj⟩ => ⟨⟨he, hadj⟩, A.adj_verts u v hadj⟩⟩

theorem Alg86Subgraph.adj_toGMGraph_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    (A : Alg86Subgraph G) {u v : Fin n} :
    A.toGMGraph.Adj u v ↔ A.graph.Adj u v := by
  rw [Alg86Subgraph.toGMGraph, graphOfFinsetSimpleGraph_adj]
  exact ⟨fun h => h.1, fun hadj => ⟨hadj, A.adj_verts u v hadj⟩⟩

open scoped Graph in
theorem Alg86Subgraph.mem_edgeSet_toGMGraph_iff {n : ℕ} {G : SimpleGraph (Fin n)}
    (A : Alg86Subgraph G) {e : Sym2 (Fin n)} :
    e ∈ E(A.toGMGraph) ↔ ∃ u v : Fin n, e = s(u, v) ∧ A.graph.Adj u v := by
  constructor
  · intro he
    obtain ⟨u, v, hl⟩ := A.toGMGraph.exists_isLink_of_mem_edgeSet he
    rw [Alg86Subgraph.isLink_toGMGraph_iff] at hl
    exact ⟨u, v, hl.1, hl.2⟩
  · rintro ⟨u, v, he, hadj⟩
    exact ((A.isLink_toGMGraph_iff).mpr ⟨he, hadj⟩).edge_mem

open scoped Graph in
theorem Alg86Subgraph.toGMGraph_le {n : ℕ} {G : SimpleGraph (Fin n)}
    (A : Alg86Subgraph G) :
    A.toGMGraph ≤ Graph.ofSimpleGraph G := by
  refine ⟨fun _ _ => Set.mem_univ _, fun {e u v} hl => ?_⟩
  rw [Alg86Subgraph.isLink_toGMGraph_iff] at hl
  exact ⟨hl.1, hl.1 ▸ G.mem_edgeSet.mpr (A.sub hl.2)⟩

open scoped Graph in
theorem Alg86Subgraph.toGMGraph_injective {n : ℕ} {G : SimpleGraph (Fin n)} :
    Function.Injective (Alg86Subgraph.toGMGraph (G := G)) := by
  intro A₁ A₂ h
  have hV : (A₁.verts : Set (Fin n)) = (A₂.verts : Set (Fin n)) :=
    congrArg Graph.vertexSet h
  ext v u
  · exact Finset.ext_iff.mp (Finset.coe_inj.mp hV) v
  · rw [← A₁.adj_toGMGraph_iff, ← A₂.adj_toGMGraph_iff, h]

open scoped Graph in
theorem divBoundary_toGMGraph (x : Alg81Input) (A : Alg86Subgraph x.G) :
    GM13.divBoundary x.toSociety A.toGMGraph = (alg86Boundary x A : Set (Fin x.n)) := by
  ext v
  simp only [GM13.divBoundary, Set.mem_ofPred_eq, Alg86Subgraph.vertexSet_toGMGraph,
    Finset.mem_coe, mem_alg86Boundary, Alg81Input.toSociety_bar, List.mem_toFinset]
  refine and_congr_right fun _ => or_congr_right ?_
  constructor
  · rintro ⟨e, ⟨heG, heNotA⟩, w, hlink⟩
    rw [Alg81Input.toSociety_G] at hlink
    have hadj : x.G.Adj v w := x.G.mem_edgeSet.mp (hlink.1 ▸ hlink.2)
    refine ⟨w, hadj, fun hadjA => heNotA ?_⟩
    exact ((A.isLink_toGMGraph_iff).mpr ⟨hlink.1, hadjA⟩).edge_mem
  · rintro ⟨w, hadj, hnotA⟩
    have hlink : x.toSociety.G.IsLink s(v, w) v w :=
      ⟨rfl, x.G.mem_edgeSet.mpr hadj⟩
    refine ⟨s(v, w), ⟨hlink.edge_mem, ?_⟩, w, hlink⟩
    intro heA
    rcases A.toGMGraph.exists_isLink_of_mem_edgeSet heA with ⟨a, b, hl⟩
    rw [Alg86Subgraph.isLink_toGMGraph_iff] at hl
    rcases Sym2.eq_iff.mp hl.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hnotA hl.2
    · exact hnotA hl.2.symm

open scoped Graph in
theorem toGMGraph_alg86SubgraphUnion (x : Alg81Input) (ℬ : Set (Alg86Subgraph x.G)) :
    (alg86SubgraphUnion ℬ).toGMGraph =
      GM09.subgraphSUnion x.toSociety.G (Alg86Subgraph.toGMGraph '' ℬ) := by
  have hsub : ∀ H ∈ Alg86Subgraph.toGMGraph '' ℬ, H ≤ Graph.ofSimpleGraph x.G := by
    rintro _ ⟨A, _, rfl⟩
    exact A.toGMGraph_le
  refine (Graph.Compatible.of_le_le (alg86SubgraphUnion ℬ).toGMGraph_le
    (GM09.subgraphSUnion_le hsub)).ext ?_ ?_
  · ext v
    simp only [Alg86Subgraph.vertexSet_toGMGraph, Finset.mem_coe, mem_verts_alg86SubgraphUnion,
      GM09.vertexSet_subgraphSUnion, Set.mem_iUnion, Set.mem_image, exists_prop,
       exists_exists_and_eq_and]
  · ext e
    rw [Alg86Subgraph.mem_edgeSet_toGMGraph_iff, GM09.edgeSet_subgraphSUnion hsub]
    simp only [adj_alg86SubgraphUnion, Set.mem_iUnion, Set.mem_image, exists_prop,
      exists_exists_and_eq_and, Alg86Subgraph.mem_edgeSet_toGMGraph_iff]
    constructor
    · rintro ⟨u, v, rfl, A, hA, hadj⟩
      exact ⟨A, hA, u, v, rfl, hadj⟩
    · rintro ⟨A, hA, u, v, rfl, hadj⟩
      exact ⟨u, v, rfl, A, hA, hadj⟩

open scoped Graph in
theorem reachable_restrictGraph_iff_nonempty_walk_deleteVertices
    {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n))
    {u v : Fin n} (hu : u ∉ Z) (hv : v ∉ Z) :
    (restrictGraph G (Finset.univ \ Z)).Reachable u v ↔
      Nonempty (Surface.GraphWalk
        (GM09.deleteVertices (Graph.ofSimpleGraph G) (Z : Set (Fin n))) u v) := by
  constructor
  · rintro ⟨W⟩
    refine ⟨?_⟩
    induction W with
    | nil =>
      exact .nil ⟨Set.mem_univ _, hu⟩
    | @cons a b c hadj p ih =>
      have ha : a ∉ Z := by
        simp only [restrictGraph, Finset.mem_sdiff, Finset.mem_univ, true_and] at hadj
        exact hadj.1
      have hb : b ∉ Z := by
        simp only [restrictGraph, Finset.mem_sdiff, Finset.mem_univ, true_and] at hadj
        exact hadj.2.1
      have hadjG : G.Adj a b := hadj.2.2
      have hl : (GM09.deleteVertices (Graph.ofSimpleGraph G) (Z : Set (Fin n))).IsLink s(a, b) a b := by
        rw [GM09.deleteVertices_isLink]
        exact ⟨⟨rfl, G.mem_edgeSet.mpr hadjG⟩, ha, hb⟩
      exact .cons hl (ih hb hv)
  · rintro ⟨W⟩
    induction W with
    | nil =>
      exact SimpleGraph.Reachable.refl _
    | @cons a b c e hl r ih =>
      rw [GM09.deleteVertices_isLink] at hl
      have ha : a ∉ Z := hl.2.1
      have hb : b ∉ Z := hl.2.2
      have hadjG : G.Adj a b := G.mem_edgeSet.mp (hl.1.1 ▸ hl.1.2)
      have hadj_res : (restrictGraph G (Finset.univ \ Z)).Adj a b := by
        simp [restrictGraph, ha, hb, hadjG]
      exact hadj_res.reachable.trans (ih hb hv)

open Classical in
open scoped Graph in
theorem isComponentOutsideCore_iff_exists_graphComponent
    {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n)) (K : Finset (Fin n)) :
    IsComponentOutsideCore G Z K ↔
      ∃ K_GM ∈ GM06.graphComponents (GM09.deleteVertices (Graph.ofSimpleGraph G) (Z : Set (Fin n))),
        V(K_GM) = (K : Set (Fin n)) := by
  let G_del := GM09.deleteVertices (Graph.ofSimpleGraph G) (Z : Set (Fin n))
  constructor
  · rintro ⟨v₀, hv₀Z, hmem⟩
    have hv₀_del : v₀ ∈ V(G_del) := ⟨Set.mem_univ v₀, hv₀Z⟩
    refine ⟨GM09.reachableComponent G_del v₀,
      GM09.isGraphComponent_reachableComponent hv₀_del, ?_⟩
    ext u
    have huG : u ∈ V(Graph.ofSimpleGraph G) := Set.mem_univ u
    simp only [GM09.vertexSet_reachableComponent, Set.mem_ofPred_eq, G_del,
      GM09.vertexSet_deleteVertices, Set.mem_sdiff, Finset.mem_coe, hmem u]
    exact ⟨fun ⟨⟨_, huZ⟩, hW⟩ => ⟨huZ,
        (reachable_restrictGraph_iff_nonempty_walk_deleteVertices G Z hv₀Z huZ).mpr hW⟩,
      fun ⟨huZ, hr⟩ => ⟨⟨huG, huZ⟩,
        (reachable_restrictGraph_iff_nonempty_walk_deleteVertices G Z hv₀Z huZ).mp hr⟩⟩
  · rintro ⟨K_GM, hK_GM, hVK⟩
    obtain ⟨v₀, hv₀⟩ := hK_GM.2.1.1
    have hK_eq : K_GM = GM09.reachableComponent G_del v₀ :=
      GM09.isGraphComponent_eq_reachableComponent hK_GM hv₀
    have hv₀_del : v₀ ∈ V(G_del) := hK_GM.1.vertexSet_mono hv₀
    have hv₀Z : v₀ ∉ Z := hv₀_del.2
    refine ⟨v₀, hv₀Z, fun u => ?_⟩
    have huG : u ∈ V(Graph.ofSimpleGraph G) := Set.mem_univ u
    have hu_iff : u ∈ K ↔ u ∈ V(K_GM) := by
      rw [← Finset.mem_coe, hVK]
    rw [hu_iff, hK_eq, GM09.vertexSet_reachableComponent]
    simp only [Set.mem_ofPred_eq, G_del, GM09.vertexSet_deleteVertices, Set.mem_sdiff,
      Finset.mem_coe]
    exact ⟨fun ⟨⟨_, huZ⟩, hW⟩ => ⟨huZ,
        (reachable_restrictGraph_iff_nonempty_walk_deleteVertices G Z hv₀Z huZ).mpr hW⟩,
      fun ⟨huZ, hr⟩ => ⟨⟨huG, huZ⟩,
        (reachable_restrictGraph_iff_nonempty_walk_deleteVertices G Z hv₀Z huZ).mp hr⟩⟩

open scoped Graph in
theorem isAlg86TypeI_iff_exists_singleEdgeSubgraph
    (x : Alg81Input) (Z : Finset (Fin x.n)) (C : SimpleGraph (Fin x.n)) (A : Alg86Subgraph x.G) :
    IsAlg86TypeI x Z A ↔
      ∃ e ∈ E(x.toSociety.G),
        (∀ v, x.toSociety.G.Inc e v → v ∈ V(toCoreGraph Z C)) ∧
        A.toGMGraph = GM13.singleEdgeSubgraph x.toSociety.G e := by
  constructor
  · rintro ⟨u, v, huZ, hvZ, hadj, hverts, hadjA⟩
    have hlink : x.toSociety.G.IsLink s(u, v) u v :=
      ⟨rfl, x.G.mem_edgeSet.mpr hadj⟩
    refine ⟨s(u, v), hlink.edge_mem, ?_, ?_⟩
    · intro w ⟨z, hlw⟩
      rcases hlw.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huZ
      · exact hvZ
    · refine Graph.ext ?_ (fun f a b => ?_)
      · rw [Alg86Subgraph.vertexSet_toGMGraph, hverts,
          GM13.vertexSet_singleEdgeSubgraph_eq_pair hlink]
        simp
      · rw [Alg86Subgraph.isLink_toGMGraph_iff, GM13.singleEdgeSubgraph_isLink, hadjA]
        constructor
        · rintro ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          · exact ⟨rfl, hlink⟩
          · exact ⟨Sym2.eq_swap, hlink.symm⟩
        · rintro ⟨rfl, hlab⟩
          rcases hlab.eq_and_eq_or_eq_and_eq hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨Sym2.eq_swap, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨e, heG, hends, hA_eq⟩
    obtain ⟨u, v, hlink⟩ := x.toSociety.G.exists_isLink_of_mem_edgeSet heG
    have huZ : u ∈ Z := hends u ⟨v, hlink⟩
    have hvZ : v ∈ Z := hends v ⟨u, hlink.symm⟩
    have hadj : x.G.Adj u v := x.G.mem_edgeSet.mp (hlink.1 ▸ hlink.2)
    refine ⟨u, v, huZ, hvZ, hadj, ?_, fun a b => ?_⟩
    · have hV : (A.verts : Set (Fin x.n)) = ({u, v} : Finset (Fin x.n)) := by
        rw [← Alg86Subgraph.vertexSet_toGMGraph, hA_eq,
          GM13.vertexSet_singleEdgeSubgraph_eq_pair hlink]
        simp
      exact Finset.coe_inj.mp hV
    · rw [← A.adj_toGMGraph_iff, hA_eq]
      constructor
      · rintro ⟨f, hlf⟩
        rw [GM13.singleEdgeSubgraph_isLink] at hlf
        exact hlf.2.eq_and_eq_or_eq_and_eq hlink
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨e, GM13.singleEdgeSubgraph_isLink.mpr ⟨rfl, hlink⟩⟩
        · exact ⟨e, GM13.singleEdgeSubgraph_isLink.mpr ⟨rfl, hlink.symm⟩⟩

open Classical in
open scoped Graph in
theorem isAlg86TypeII_iff_exists_coreBridgeSubgraph
    (x : Alg81Input) (Z : Finset (Fin x.n)) (C : SimpleGraph (Fin x.n)) (A : Alg86Subgraph x.G) :
    IsAlg86TypeII x Z A ↔
      ∃ K_GM ∈ GM06.graphComponents (GM09.deleteVertices x.toSociety.G V(toCoreGraph Z C)),
        A.toGMGraph = GM13.coreBridgeSubgraph x.toSociety.G V(toCoreGraph Z C) K_GM := by
  have hZ_sub : V(toCoreGraph Z C) ⊆ V(x.toSociety.G) := fun _ _ => Set.mem_univ _
  constructor
  · rintro ⟨K, hK, hverts, hadjA⟩
    obtain ⟨K_GM, hK_GM, hVK⟩ :=
      (isComponentOutsideCore_iff_exists_graphComponent x.G Z K).mp hK
    refine ⟨K_GM, hK_GM, Graph.ext ?_ (fun e a b => ?_)⟩
    · rw [Alg86Subgraph.vertexSet_toGMGraph, hverts, GM13.vertexSet_coreBridgeSubgraph]
      ext w
      simp only [GM13.coreBridgeVerts, vertexSet_toCoreGraph, hVK, Finset.coe_union,
        Finset.coe_filter, Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq]
      refine or_congr_right (and_congr_right fun _ => exists_congr fun u =>
        and_congr_right fun _ => ?_)
      rw [Alg81Input.toSociety_G]
      exact ⟨fun hadj => ⟨s(u, w), rfl, x.G.mem_edgeSet.mpr hadj⟩,
        fun ⟨f, hf⟩ => x.G.mem_edgeSet.mp (hf.1 ▸ hf.2)⟩
    · rw [Alg86Subgraph.isLink_toGMGraph_iff,
        GM13.coreBridgeSubgraph_isLink_iff hZ_sub hK_GM,
        hadjA, hK.adj_iff_mem_or_mem, hVK]
      simp only [Finset.mem_coe, Alg81Input.toSociety_G]
      exact ⟨fun ⟨he, hadj, hmem⟩ => ⟨⟨he, he ▸ x.G.mem_edgeSet.mpr hadj⟩, hmem⟩,
        fun ⟨⟨he, he_mem⟩, hmem⟩ => ⟨he, x.G.mem_edgeSet.mp (he ▸ he_mem), hmem⟩⟩
  · rintro ⟨K_GM, hK_GM, hA_eq⟩
    let K : Finset (Fin x.n) := V(K_GM).toFinset
    have hVK : V(K_GM) = (K : Set (Fin x.n)) := (Set.coe_toFinset V(K_GM)).symm
    have hK : IsComponentOutsideCore x.G Z K :=
      (isComponentOutsideCore_iff_exists_graphComponent x.G Z K).mpr ⟨K_GM, hK_GM, hVK⟩
    refine ⟨K, hK, ?_, fun a b => ?_⟩
    · ext w
      have hw_iff : w ∈ A.verts ↔ w ∈ V(A.toGMGraph) := Iff.rfl
      rw [hw_iff, hA_eq, GM13.vertexSet_coreBridgeSubgraph]
      simp only [GM13.coreBridgeVerts, vertexSet_toCoreGraph, hVK, Set.mem_union,
        Finset.mem_coe, Set.mem_ofPred_eq, Finset.mem_union, Finset.mem_filter]
      refine or_congr_right (and_congr_right fun _ => exists_congr fun u =>
        and_congr_right fun _ => ?_)
      rw [Alg81Input.toSociety_G]
      exact ⟨fun ⟨f, hf⟩ => x.G.mem_edgeSet.mp (hf.1 ▸ hf.2),
        fun hadj => ⟨s(u, w), rfl, x.G.mem_edgeSet.mpr hadj⟩⟩
    · rw [hK.adj_iff_mem_or_mem, ← A.adj_toGMGraph_iff, hA_eq]
      constructor
      · rintro ⟨e, hl⟩
        rw [GM13.coreBridgeSubgraph_isLink_iff hZ_sub hK_GM, hVK] at hl
        exact ⟨x.G.mem_edgeSet.mp (hl.1.1 ▸ hl.1.2), hl.2⟩
      · rintro ⟨hadj, hmem⟩
        refine ⟨s(a, b), (GM13.coreBridgeSubgraph_isLink_iff hZ_sub hK_GM).mpr ?_⟩
        rw [hVK]
        exact ⟨⟨rfl, x.G.mem_edgeSet.mpr hadj⟩, hmem⟩

open scoped Graph in
theorem isAlg86TypeIII_iff_exists_singleVertexSubgraph
    (x : Alg81Input) (A : Alg86Subgraph x.G) :
    IsAlg86TypeIII x A ↔
      ∃ v ∈ x.toSociety.Ω.bar,
        (∀ e ∈ E(x.toSociety.G), ¬ x.toSociety.G.Inc e v) ∧
        A.toGMGraph = GM13.singleVertexSubgraph x.toSociety.G v := by
  constructor
  · rintro ⟨v, hv_om, hiso, hverts, hgraph⟩
    refine ⟨v, by rw [Alg81Input.toSociety_bar]; exact List.mem_toFinset.mp hv_om, ?_, ?_⟩
    · rintro e _ ⟨w, hl⟩
      exact hiso w (x.G.mem_edgeSet.mp (hl.1 ▸ hl.2))
    · refine Graph.ext ?_ (fun e a b => ?_)
      · rw [Alg86Subgraph.vertexSet_toGMGraph, hverts, GM13.vertexSet_singleVertexSubgraph]
        simp
      · rw [Alg86Subgraph.isLink_toGMGraph_iff, hgraph]
        exact ⟨fun h => False.elim h.2,
          fun hl => False.elim (by
            have he := hl.edge_mem
            rw [GM13.edgeSet_singleVertexSubgraph] at he
            exact he)⟩
  · rintro ⟨v, hv_bar, hiso, hA_eq⟩
    refine ⟨v, List.mem_toFinset.mpr (by rwa [Alg81Input.toSociety_bar] at hv_bar), ?_, ?_, ?_⟩
    · intro w hadj
      have hl : x.toSociety.G.IsLink s(v, w) v w := ⟨rfl, x.G.mem_edgeSet.mpr hadj⟩
      exact hiso s(v, w) hl.edge_mem ⟨w, hl⟩
    · have hV : (A.verts : Set (Fin x.n)) = ({v} : Finset (Fin x.n)) := by
        rw [← Alg86Subgraph.vertexSet_toGMGraph, hA_eq, GM13.vertexSet_singleVertexSubgraph]
        simp
      exact Finset.coe_inj.mp hV
    · ext a b
      rw [← A.adj_toGMGraph_iff, hA_eq]
      simp only [SimpleGraph.bot_adj, iff_false]
      rintro ⟨e, hl⟩
      have he := hl.edge_mem
      rw [GM13.edgeSet_singleVertexSubgraph] at he
      exact he

open Classical in
open scoped Graph in
theorem mem_alg86RawDivision_iff_toGMGraph_mem_coreRawDivision
    (x : Alg81Input) (Z : Finset (Fin x.n)) (C : SimpleGraph (Fin x.n)) (A : Alg86Subgraph x.G) :
    A ∈ alg86RawDivision x Z ↔
      A.toGMGraph ∈ GM13.coreRawDivision x.toSociety (toCoreGraph Z C) := by
  change (IsAlg86TypeI x Z A ∨ IsAlg86TypeII x Z A ∨ IsAlg86TypeIII x A) ↔ _
  rw [isAlg86TypeI_iff_exists_singleEdgeSubgraph x Z C A,
    isAlg86TypeII_iff_exists_coreBridgeSubgraph x Z C A,
    isAlg86TypeIII_iff_exists_singleVertexSubgraph x A]
  rfl

open Classical in
open scoped Graph in
theorem image_toGMGraph_alg86RawDivision
    (x : Alg81Input) (Z : Finset (Fin x.n)) (C : SimpleGraph (Fin x.n)) :
    Alg86Subgraph.toGMGraph '' (alg86RawDivision x Z) =
      GM13.coreRawDivision x.toSociety (toCoreGraph Z C) := by
  ext H
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact (mem_alg86RawDivision_iff_toGMGraph_mem_coreRawDivision x Z C A).mp hA
  · intro hH
    rcases hH with ⟨e, heG, hends, rfl⟩ | ⟨K_GM, hK_GM, rfl⟩ | ⟨v, hv_bar, hiso, rfl⟩
    · obtain ⟨u, v, hlink⟩ := x.toSociety.G.exists_isLink_of_mem_edgeSet heG
      have huZ : u ∈ Z := hends u ⟨v, hlink⟩
      have hvZ : v ∈ Z := hends v ⟨u, hlink.symm⟩
      have hadj : x.G.Adj u v := x.G.mem_edgeSet.mp (hlink.1 ▸ hlink.2)
      let A := mkAlg86TypeI x hadj
      have hA_typeI : IsAlg86TypeI x Z A := isAlg86TypeI_mkAlg86TypeI x Z huZ hvZ hadj
      obtain ⟨e', _, _, hA_eq⟩ :=
        (isAlg86TypeI_iff_exists_singleEdgeSubgraph x Z C A).mp hA_typeI
      have hlink_A : A.toGMGraph.IsLink s(u, v) u v :=
        (A.isLink_toGMGraph_iff).mpr ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
      rw [hA_eq, GM13.singleEdgeSubgraph_isLink] at hlink_A
      have he_eq : e = s(u, v) := hlink.1
      rw [he_eq, hlink_A.1, ← hA_eq]
      exact ⟨A, Or.inl hA_typeI, rfl⟩
    · let K : Finset (Fin x.n) := V(K_GM).toFinset
      have hVK : V(K_GM) = (K : Set (Fin x.n)) := (Set.coe_toFinset V(K_GM)).symm
      have hK : IsComponentOutsideCore x.G Z K :=
        (isComponentOutsideCore_iff_exists_graphComponent x.G Z K).mpr ⟨K_GM, hK_GM, hVK⟩
      let A := mkAlg86TypeII x Z K hK
      have hA_typeII : IsAlg86TypeII x Z A := isAlg86TypeII_mkAlg86TypeII x Z K hK
      have hZ_sub : V(toCoreGraph Z C) ⊆ V(x.toSociety.G) := fun _ _ => Set.mem_univ _
      have hA_eq : A.toGMGraph = GM13.coreBridgeSubgraph x.toSociety.G V(toCoreGraph Z C) K_GM := by
        refine Graph.ext ?_ (fun e a b => ?_)
        · rw [Alg86Subgraph.vertexSet_toGMGraph, GM13.vertexSet_coreBridgeSubgraph]
          ext w
          simp only [A, mkAlg86TypeII, GM13.coreBridgeVerts, vertexSet_toCoreGraph, hVK,
            Finset.coe_union, Finset.coe_filter, Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq]
          refine or_congr_right (and_congr_right fun _ => exists_congr fun u =>
            and_congr_right fun _ => ?_)
          rw [Alg81Input.toSociety_G]
          exact ⟨fun hadj => ⟨s(u, w), rfl, x.G.mem_edgeSet.mpr hadj⟩,
            fun ⟨f, hf⟩ => x.G.mem_edgeSet.mp (hf.1 ▸ hf.2)⟩
        · rw [Alg86Subgraph.isLink_toGMGraph_iff,
            GM13.coreBridgeSubgraph_isLink_iff hZ_sub hK_GM]
          change (e = s(a, b) ∧
              (x.G.Adj a b ∧ ((a ∈ K ∧ b ∈ K) ∨ (a ∈ K ∧ b ∈ Z) ∨ (a ∈ Z ∧ b ∈ K)))) ↔
            x.toSociety.G.IsLink e a b ∧ (a ∈ V(K_GM) ∨ b ∈ V(K_GM))
          rw [hK.adj_iff_mem_or_mem, hVK]
          simp only [Finset.mem_coe, Alg81Input.toSociety_G]
          exact ⟨fun ⟨he, hadj, hmem⟩ => ⟨⟨he, he ▸ x.G.mem_edgeSet.mpr hadj⟩, hmem⟩,
            fun ⟨⟨he, he_mem⟩, hmem⟩ => ⟨he, x.G.mem_edgeSet.mp (he ▸ he_mem), hmem⟩⟩
      exact ⟨A, Or.inr (Or.inl hA_typeII), hA_eq⟩
    · have hv_om : v ∈ x.omega.toFinset :=
        List.mem_toFinset.mpr (by rwa [Alg81Input.toSociety_bar] at hv_bar)
      have hiso' : ∀ w : Fin x.n, ¬ x.G.Adj v w := by
        intro w hadj
        have hl : x.toSociety.G.IsLink s(v, w) v w := ⟨rfl, x.G.mem_edgeSet.mpr hadj⟩
        exact hiso s(v, w) hl.edge_mem ⟨w, hl⟩
      let A := mkAlg86TypeIII x v
      have hA_typeIII : IsAlg86TypeIII x A := isAlg86TypeIII_mkAlg86TypeIII x hv_om hiso'
      obtain ⟨v', _, _, hA_eq⟩ :=
        (isAlg86TypeIII_iff_exists_singleVertexSubgraph x A).mp hA_typeIII
      have hv_eq : v' = v := by
        have hV : V(A.toGMGraph) = V(GM13.singleVertexSubgraph x.toSociety.G v') :=
          congrArg Graph.vertexSet hA_eq
        simp [A, mkAlg86TypeIII] at hV
        exact hV.symm
      rw [← hv_eq, ← hA_eq]
      exact ⟨A, Or.inr (Or.inr hA_typeIII), rfl⟩

open Classical in
open scoped Graph in
theorem image_toGMGraph_alg86EquivClass
    (x : Alg81Input) (Z : Finset (Fin x.n)) (C : SimpleGraph (Fin x.n)) (A₀ : Alg86Subgraph x.G) :
    Alg86Subgraph.toGMGraph '' (alg86EquivClass x Z A₀) =
      {H ∈ GM13.coreRawDivision x.toSociety (toCoreGraph Z C) |
        GM13.divBoundary x.toSociety H = GM13.divBoundary x.toSociety A₀.toGMGraph} := by
  ext H
  constructor
  · rintro ⟨A, ⟨hA_raw, hA_eq⟩, rfl⟩
    refine ⟨(mem_alg86RawDivision_iff_toGMGraph_mem_coreRawDivision x Z C A).mp hA_raw, ?_⟩
    rw [divBoundary_toGMGraph, divBoundary_toGMGraph, hA_eq]
  · rintro ⟨hH_raw, hH_bd⟩
    rw [← image_toGMGraph_alg86RawDivision x Z C] at hH_raw
    rcases hH_raw with ⟨A, hA_raw, rfl⟩
    refine ⟨A, ⟨hA_raw, ?_⟩, rfl⟩
    rw [divBoundary_toGMGraph, divBoundary_toGMGraph] at hH_bd
    exact Finset.coe_inj.mp hH_bd

open Classical in
open scoped Graph in
theorem image_toGMGraph_alg86Division
    (x : Alg81Input) (Z : Finset (Fin x.n)) (C : SimpleGraph (Fin x.n)) :
    Alg86Subgraph.toGMGraph '' (alg86Division x Z) =
      GM13.coreDivision x.toSociety (toCoreGraph Z C) := by
  ext B_GM
  constructor
  · rintro ⟨B, ⟨A₀, hA₀_raw, rfl⟩, rfl⟩
    rw [toGMGraph_alg86SubgraphUnion, image_toGMGraph_alg86EquivClass x Z C A₀]
    exact ⟨GM13.divBoundary x.toSociety A₀.toGMGraph,
      ⟨A₀.toGMGraph,
        (mem_alg86RawDivision_iff_toGMGraph_mem_coreRawDivision x Z C A₀).mp hA₀_raw, rfl⟩,
      rfl⟩
  · rintro ⟨X, ⟨H₀, hH₀_raw, rfl⟩, rfl⟩
    rw [← image_toGMGraph_alg86RawDivision x Z C] at hH₀_raw
    rcases hH₀_raw with ⟨A₀, hA₀_raw, rfl⟩
    refine ⟨alg86SubgraphUnion (alg86EquivClass x Z A₀), ⟨A₀, hA₀_raw, rfl⟩, ?_⟩
    rw [toGMGraph_alg86SubgraphUnion, image_toGMGraph_alg86EquivClass x Z C A₀]

open Classical in
open scoped Graph in
theorem isRuralDivision_image_alg86Division
    (x : Alg81Input) {Z : Finset (Fin x.n)} {C : SimpleGraph (Fin x.n)}
    (htrace : Alg83Trace x Z C) (h4 : IsFourLinkedCore x.omega Z C)
    (hnocross : ¬ HasCrossInSociety x.G x.omega) :
    GM13.IsRuralDivision x.toSociety (Alg86Subgraph.toGMGraph '' (alg86Division x Z)) := by
  rw [image_toGMGraph_alg86Division x Z C]
  exact GM13.isRuralDivision_coreDivision (isFourLinkedCore_toCoreGraph htrace h4)
    (fun h => hnocross ((hasCrossInSociety_iff_hasCross x).mpr h))

/-! ### Section 3: Decoded Subgraph Wrapper and Raw Division Equivalence (`setOf_mem_map_alg86RawPairList`) -/

/-- Wrap a decoded pair `(V, H) : Finset (Fin n) × SimpleGraph (Fin n)` into an `Alg86Subgraph G`
by keeping edges of `H` that belong to `G` and have both endpoints in `V`. -/
def alg86SubgraphOfDecoded {n : ℕ} (G : SimpleGraph (Fin n))
    (p : Finset (Fin n) × SimpleGraph (Fin n)) : Alg86Subgraph G where
  verts := p.1
  graph := {
    Adj := fun u v => G.Adj u v ∧ u ∈ p.1 ∧ v ∈ p.1 ∧ p.2.Adj u v
    symm := ⟨fun _ _ ⟨hG, hu, hv, hH⟩ => ⟨hG.symm, hv, hu, hH.symm⟩⟩
    loopless := ⟨fun _ ⟨hG, _⟩ => G.loopless.irrefl _ hG⟩
  }
  sub := fun _ _ h => h.1
  adj_verts := fun _ _ h => ⟨h.2.1, h.2.2.1⟩

/-- Convert an encoded pair `(V, edges) : Finset (Fin n) × List (Fin n × Fin n)` into an
`Alg86Subgraph G` via `graphOfFlatEdges`. -/
def alg86SubgraphOfPair {n : ℕ} (G : SimpleGraph (Fin n))
    (p : Finset (Fin n) × List (Fin n × Fin n)) : Alg86Subgraph G :=
  alg86SubgraphOfDecoded G (p.1, graphOfFlatEdges n ([n, p.2.length] ++ flatEdges p.2))

@[simp]
theorem verts_alg86SubgraphOfPair {n : ℕ} (G : SimpleGraph (Fin n))
    (p : Finset (Fin n) × List (Fin n × Fin n)) :
    (alg86SubgraphOfPair G p).verts = p.1 :=
  rfl

@[simp]
theorem adj_alg86SubgraphOfPair {n : ℕ} (G : SimpleGraph (Fin n))
    (p : Finset (Fin n) × List (Fin n × Fin n)) (u v : Fin n) :
    (alg86SubgraphOfPair G p).graph.Adj u v ↔
      G.Adj u v ∧ u ∈ p.1 ∧ v ∈ p.1 ∧ ((u, v) ∈ p.2 ∨ (v, u) ∈ p.2) := by
  dsimp only [alg86SubgraphOfPair, alg86SubgraphOfDecoded]
  rw [adj_graphOfFlatEdges_iff]
  exact ⟨fun ⟨hG, hu, hv, _, hmem⟩ => ⟨hG, hu, hv, hmem⟩,
    fun ⟨hG, hu, hv, hmem⟩ => ⟨hG, hu, hv, G.ne_of_adj hG, hmem⟩⟩

theorem mem_alg86TypeIIPairs_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n)) (k : ℕ) (hk_le : k ≤ n)
    (p : Finset (Fin n) × List (Fin n × Fin n)) :
    p ∈ alg86TypeIIPairs G Z edges₀ k ↔
      ∃ r : Fin n,
        r.1 < k ∧ r ∉ Z ∧ (∀ u ∈ alg86K G Z r, r.1 ≤ u.1) ∧
        p = (alg86K G Z r ∪ alg86X G Z r,
          edges₀.filter (alg86KeepEdge (alg86K G Z r) (alg86X G Z r) false)) := by
  induction k with
  | zero => simp [alg86TypeIIPairs]
  | succ k ih =>
    have hk_lt : k < n := by omega
    simp only [alg86TypeIIPairs, hk_lt, ↓reduceDIte]
    split_ifs with hcond
    · rw [List.mem_append, List.mem_singleton, ih (by omega)]
      constructor
      · rintro (⟨r, hr_lt, hrZ, hmin, hp⟩ | rfl)
        · exact ⟨r, by omega, hrZ, hmin, hp⟩
        · exact ⟨⟨k, hk_lt⟩, Nat.lt_succ_self k, hcond.1, hcond.2, rfl⟩
      · rintro ⟨r, hr_lt, hrZ, hmin, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr_lt with hlt' | heq
        · exact Or.inl ⟨r, hlt', hrZ, hmin, hp⟩
        · have hr_eq : r = ⟨k, hk_lt⟩ := Fin.ext heq
          subst hr_eq
          exact Or.inr hp
    · rw [ih (by omega)]
      constructor
      · rintro ⟨r, hr_lt, hrZ, hmin, hp⟩
        exact ⟨r, by omega, hrZ, hmin, hp⟩
      · rintro ⟨r, hr_lt, hrZ, hmin, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr_lt with hlt' | heq
        · exact ⟨r, hlt', hrZ, hmin, hp⟩
        · exfalso
          have hr_eq : r = ⟨k, hk_lt⟩ := Fin.ext heq
          subst hr_eq
          exact hcond ⟨hrZ, hmin⟩

theorem isComponentOutsideCore_alg86K {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) {r : Fin n} (hr : r ∉ Z) :
    IsComponentOutsideCore G Z (alg86K G Z r) := by
  refine ⟨r, hr, fun u => ?_⟩
  constructor
  · intro hu
    have hu_sdiff := alg86K_subset_sdiff_of_not_mem G Z hr hu
    exact ⟨(Finset.mem_sdiff.mp hu_sdiff).2,
      (mem_reachSet (restrictGraph G (Finset.univ \ Z)) r u).mp hu⟩
  · rintro ⟨_, hreach⟩
    exact (mem_reachSet (restrictGraph G (Finset.univ \ Z)) r u).mpr hreach

theorem alg86K_eq_of_isComponentOutsideCore {n : ℕ} (G : SimpleGraph (Fin n))
    (Z K : Finset (Fin n)) (hK : IsComponentOutsideCore G Z K) {r : Fin n} (hrK : r ∈ K) :
    alg86K G Z r = K := by
  rcases hK with ⟨v₀, hv₀Z, hmem⟩
  obtain ⟨hrZ, hreach_r⟩ := (hmem r).mp hrK
  ext u
  rw [alg86K, mem_reachSet, hmem u]
  constructor
  · intro hru
    have hvu : (restrictGraph G (Finset.univ \ Z)).Reachable v₀ u := hreach_r.trans hru
    have hu_K : u ∈ alg86K G Z r := (mem_reachSet _ r u).mpr hru
    have hu_sdiff := alg86K_subset_sdiff_of_not_mem G Z hrZ hu_K
    exact ⟨(Finset.mem_sdiff.mp hu_sdiff).2, hvu⟩
  · rintro ⟨_, hvu⟩
    exact hreach_r.symm.trans hvu

theorem alg86X_eq_filter_Z {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) {r : Fin n} (hr : r ∉ Z) :
    alg86X G Z r = open Classical in Z.filter (fun z => ∃ u ∈ alg86K G Z r, G.Adj u z) := by
  classical
  ext z
  simp only [alg86X, Finset.mem_inter, mem_extNeighborhood, Finset.mem_filter]
  constructor
  · rintro ⟨⟨_, u, huK, hadj⟩, hzZ⟩
    exact ⟨hzZ, u, huK, hadj⟩
  · rintro ⟨hzZ, u, huK, hadj⟩
    have hz_not_K : z ∉ alg86K G Z r := by
      intro hzK
      exact (Finset.mem_sdiff.mp (alg86K_subset_sdiff_of_not_mem G Z hr hzK)).2 hzZ
    exact ⟨⟨hz_not_K, u, huK, hadj⟩, hzZ⟩

theorem alg86SubgraphOfPair_typeI (x : Alg81Input) {e : Fin x.n × Fin x.n}
    (hadj : x.G.Adj e.1 e.2) :
    alg86SubgraphOfPair x.G ({e.1, e.2}, [e]) = mkAlg86TypeI x hadj := by
  ext a b
  · rfl
  · rw [adj_alg86SubgraphOfPair]
    simp only [mkAlg86TypeI, Finset.mem_insert, Finset.mem_singleton, List.mem_singleton,
      Prod.ext_iff]
    constructor
    · rintro ⟨_, _, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hadj, Or.inl rfl, Or.inr rfl, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨hadj.symm, Or.inr rfl, Or.inl rfl, Or.inr ⟨rfl, rfl⟩⟩

theorem alg86SubgraphOfPair_typeII (x : Alg81Input) (Z : Finset (Fin x.n))
    {r : Fin x.n} (hr : r ∉ Z) :
    alg86SubgraphOfPair x.G (alg86K x.G Z r ∪ alg86X x.G Z r,
      (edgeListOf x.G).filter (alg86KeepEdge (alg86K x.G Z r) (alg86X x.G Z r) false)) =
      mkAlg86TypeII x Z (alg86K x.G Z r) (isComponentOutsideCore_alg86K x.G Z hr) := by
  have hedges₀ : IsSimpleEdgeList x.G (edgeListOf x.G) := isSimpleEdgeList_edgeListOf x.G
  have hK : IsComponentOutsideCore x.G Z (alg86K x.G Z r) := isComponentOutsideCore_alg86K x.G Z hr
  have hX_eq := alg86X_eq_filter_Z x.G Z hr
  ext a b
  · simp [mkAlg86TypeII, hX_eq]
  · rw [adj_alg86SubgraphOfPair]
    change (x.G.Adj a b ∧ a ∈ alg86K x.G Z r ∪ alg86X x.G Z r ∧
        b ∈ alg86K x.G Z r ∪ alg86X x.G Z r ∧ _) ↔
      x.G.Adj a b ∧
        ((a ∈ alg86K x.G Z r ∧ b ∈ alg86K x.G Z r) ∨
         (a ∈ alg86K x.G Z r ∧ b ∈ Z) ∨
         (a ∈ Z ∧ b ∈ alg86K x.G Z r))
    rw [hK.adj_iff_mem_or_mem]
    constructor
    · rintro ⟨hadj, _, _, hmem | hmem⟩
      · have hkeep := (List.mem_filter.mp hmem).2
        simp only [alg86KeepEdge, Bool.false_eq_true, false_and, or_false,
          decide_eq_true_eq] at hkeep
        exact ⟨hadj, hkeep⟩
      · have hkeep := (List.mem_filter.mp hmem).2
        simp only [alg86KeepEdge, Bool.false_eq_true, false_and, or_false,
          decide_eq_true_eq] at hkeep
        exact ⟨hadj, hkeep.symm⟩
    · rintro ⟨hadj, hK_ab⟩
      have hverts : a ∈ alg86K x.G Z r ∪ alg86X x.G Z r ∧
          b ∈ alg86K x.G Z r ∪ alg86X x.G Z r := by
        have hmem_m := (hK.adj_iff_mem_or_mem a b).mpr ⟨hadj, hK_ab⟩
        have hadj_v := (mkAlg86TypeII x Z (alg86K x.G Z r) hK).adj_verts a b hmem_m
        simpa [mkAlg86TypeII, hX_eq] using hadj_v
      rcases (hedges₀.2.2 a b).mp hadj with ⟨j, hj, hpair⟩
      refine ⟨hadj, hverts.1, hverts.2, ?_⟩
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        have he_eq : (edgeListOf x.G)[j]'hj = (a, b) := Prod.ext h1 h2
        rw [← he_eq, List.mem_filter]
        refine ⟨List.getElem_mem hj, ?_⟩
        simp [alg86KeepEdge, h1, h2, hK_ab]
      · right
        have he_eq : (edgeListOf x.G)[j]'hj = (b, a) := Prod.ext h1 h2
        rw [← he_eq, List.mem_filter]
        refine ⟨List.getElem_mem hj, ?_⟩
        simp [alg86KeepEdge, h1, h2, hK_ab.symm]

theorem alg86SubgraphOfPair_typeIII (x : Alg81Input) (v : Fin x.n) :
    alg86SubgraphOfPair x.G ({v}, []) = mkAlg86TypeIII x v := by
  ext a b
  · rfl
  · rw [adj_alg86SubgraphOfPair]
    simp [mkAlg86TypeIII]

/-- The raw pair list `alg86RawPairList` emitted by `alg86DivisionsProg` decodes under
`alg86SubgraphOfPair x.G` to the raw division `alg86RawDivision x Z` ($\mathcal{A}'$). -/
theorem setOf_mem_map_alg86RawPairList (x : Alg81Input) (Z : Finset (Fin x.n)) :
    { A | A ∈ (alg86RawPairList x.G Z x.omega.toFinset (edgeListOf x.G)).map
        (alg86SubgraphOfPair x.G) } =
      alg86RawDivision x Z := by
  let edges₀ := edgeListOf x.G
  have hedges₀ : IsSimpleEdgeList x.G edges₀ := isSimpleEdgeList_edgeListOf x.G
  ext A
  simp only [Set.mem_ofPred_eq, alg86RawPairList, List.map_append, List.mem_append,
    List.mem_map, alg86RawDivision, IsInAlg86RawDivision]
  constructor
  · rintro ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩)
    · rw [mem_alg86TypeIPairs_iff Z edges₀ ∅ edges₀.length le_rfl] at hp
      rcases hp with ⟨j, _, huZ, hvZ, _, rfl⟩
      have hadj : x.G.Adj (edges₀[j.1]'j.2).1 (edges₀[j.1]'j.2).2 :=
        (hedges₀.2.2 _ _).mpr ⟨j.1, j.2, Or.inl ⟨rfl, rfl⟩⟩
      rw [alg86SubgraphOfPair_typeI x hadj]
      exact Or.inl (isAlg86TypeI_mkAlg86TypeI x Z huZ hvZ hadj)
    · rw [mem_alg86TypeIIPairs_iff x.G Z edges₀ x.n le_rfl] at hp
      rcases hp with ⟨r, _, hrZ, _, rfl⟩
      rw [alg86SubgraphOfPair_typeII x Z hrZ]
      exact Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z _ _))
    · rw [mem_alg86TypeIIIPairs_iff x.omega.toFinset edges₀ x.n le_rfl] at hp
      rcases hp with ⟨v, _, hv_om, hdeg0, rfl⟩
      rw [alg86SubgraphOfPair_typeIII x v]
      refine Or.inr (Or.inr (isAlg86TypeIII_mkAlg86TypeIII x hv_om (fun w hadj => ?_)))
      have hmem_nb : w.1 ∈ edgeNeighbors edges₀ v :=
        ((isAdjListFamily_edgeNeighbors hedges₀ v).2.2.2 w).mpr hadj
      have hlen_pos : 0 < (edgeNeighbors edges₀ v).length :=
        List.length_pos_of_mem hmem_nb
      omega
  · rintro (hI | hII | hIII)
    · rcases hI with ⟨u, v, huZ, hvZ, hadj, hverts, hadjA⟩
      rcases (hedges₀.2.2 u v).mp hadj with ⟨j, hj, hpair⟩
      left; left
      refine ⟨({(edges₀[j]'hj).1, (edges₀[j]'hj).2}, [edges₀[j]'hj]), ?_, ?_⟩
      · rw [mem_alg86TypeIPairs_iff Z edges₀ ∅ edges₀.length le_rfl]
        refine ⟨⟨j, hj⟩, hj, ?_, ?_, Finset.notMem_empty _, rfl⟩
        · rcases hpair with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> assumption
        · rcases hpair with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> assumption
      · have hadj_e : x.G.Adj (edges₀[j]'hj).1 (edges₀[j]'hj).2 :=
          (hedges₀.2.2 _ _).mpr ⟨j, hj, Or.inl ⟨rfl, rfl⟩⟩
        rw [alg86SubgraphOfPair_typeI x hadj_e]
        ext a b
        · simp only [mkAlg86TypeI, hverts]
          rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1, h2, Finset.pair_comm]
        · simp only [mkAlg86TypeI, hadjA]
          rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1, h2]; exact or_comm
    · rcases hII with ⟨K, hK, hverts, hadjA⟩
      classical
      let r : Fin x.n := K.min' hK.nonempty
      have hrK : r ∈ K := Finset.min'_mem K hK.nonempty
      have hrZ : r ∉ Z := hK.not_mem_Z hrK
      have hK_eq : alg86K x.G Z r = K := alg86K_eq_of_isComponentOutsideCore x.G Z K hK hrK
      have hmin : ∀ u ∈ alg86K x.G Z r, r.1 ≤ u.1 := by
        intro u hu
        rw [hK_eq] at hu
        exact Fin.le_iff_val_le_val.mp (Finset.min'_le K u hu)
      left; right
      refine ⟨(alg86K x.G Z r ∪ alg86X x.G Z r,
          edges₀.filter (alg86KeepEdge (alg86K x.G Z r) (alg86X x.G Z r) false)), ?_, ?_⟩
      · rw [mem_alg86TypeIIPairs_iff x.G Z edges₀ x.n le_rfl]
        exact ⟨r, r.2, hrZ, hmin, rfl⟩
      · rw [alg86SubgraphOfPair_typeII x Z hrZ]
        ext a b
        · simp [mkAlg86TypeII, hK_eq, hverts]
        · simp [mkAlg86TypeII, hK_eq, hadjA]
    · rcases hIII with ⟨v, hv_om, hiso, hverts, hgraph⟩
      right
      refine ⟨({v}, []), ?_, ?_⟩
      · rw [mem_alg86TypeIIIPairs_iff x.omega.toFinset edges₀ x.n le_rfl]
        refine ⟨v, v.2, hv_om, ?_, rfl⟩
        by_contra hne
        have hpos : 0 < (edgeNeighbors edges₀ v).length := Nat.pos_of_ne_zero hne
        let w_val := (edgeNeighbors edges₀ v)[0]'hpos
        have hmem : w_val ∈ edgeNeighbors edges₀ v := List.getElem_mem hpos
        have h_lt := (isAdjListFamily_edgeNeighbors hedges₀ v).1 w_val hmem
        let w : Fin x.n := ⟨w_val, h_lt⟩
        have hadj := ((isAdjListFamily_edgeNeighbors hedges₀ v).2.2.2 w).mp hmem
        exact hiso w hadj
      · rw [alg86SubgraphOfPair_typeIII x v]
        ext a b
        · simp [mkAlg86TypeIII, hverts]
        · simp [mkAlg86TypeIII, hgraph]

end GraphMinor.Compute
