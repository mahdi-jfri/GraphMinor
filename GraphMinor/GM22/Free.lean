module

public import GraphMinor.GM21.Final
public import GraphMinor.GM22.Join21
public import GraphMinor.GM22.Section8a
public import GraphMinor.GM22.Section8c
public import GraphMinor.GM22.Section8To13

/-!
# Graph Minors XXII: Hypothesis-Free Forms of (2.1), (3.1), (4.1), (4.2), (5.3), (7.2), (7.3), (7.4), (8.2), and (8.3)

This file exports the ten numbered results of Graph Minors XXII (`(2.1)`, `(3.1)`, `(4.1)`, `(4.2)`,
`(5.3)`, `(7.2)`, `(7.3)`, `(7.4)`, `(8.2)`, and `(8.3)`), using the proved XXI (1.1) through
`GM21Proved`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Classical
open Graph Hypergraph GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
  GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM19

universe u v w u₁ v₁

/-- **Graph Minors XXII, 2.1** (Section 2, page 531, proved on page 532):
"For every integer $p \ge 0$, there exists $w \ge 0$ such that, if a graph $G$ has a subgraph which
is vital for some $Z \subseteq V(G)$ with $|Z| \le p$, then $G$ has tree-width $\le w$." -/
theorem theorem_2_1_free (p : ℕ) :
    ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G L : Graph α β) (Z : Set α),
      V(G).Finite → E(G).Finite → Z ⊆ V(G) → Z.ncard ≤ p →
      IsVitalFor G L Z → TreeWidthLE G w :=
  theorem_2_1_proof.{u, v} p

/-- **3.1** (Graph Minors XXII, page 534):
"For every integer $p \ge 0$ there exists $h \ge 1$ with the following property. Let $\Gamma, K$
be subgraphs of a graph $G$ with $G = \Gamma \cup K$, and let $\Gamma$ be a drawing in a surface
$\Sigma$. Let $v \in V(\Gamma)$ be $h$-insulated from $V(\Gamma \cap K)$ by $\Gamma$, let
$Z \subseteq V(K)$ with $|Z| \le p$, and let $L \subseteq G$. Then there is a subgraph $L'$ of
$G \setminus \{v\}$ with the same effect on $Z$ as $L$ and with $L' \cap K \subseteq L$." -/
theorem theorem_3_1_free (p : ℕ) :
    ∃ h ≥ 1, ∀ {S : Type w} [TopologicalSpace S] [T2Space S], IsSurface S →
      ∀ {α : Type u} {β : Type v} (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
        Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
        ∀ (D : Surface.Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D.toEmbeddedGraph ιV ιE →
        ∀ v₀ ∈ D.V, IsInsulated D (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
        ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
        ∃ L' ≤ G.deleteVerts {ιV v₀},
          HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L :=
  theorem_3_1_proof.{u, v, w} p

/-- **4.1** (Graph Minors XXII, page 537):
"For every integer $p \ge 0$ there exists $h \ge 1$ with the following property. Let $\Gamma, K$ be
subgraphs of a graph $\Gamma \cup K$, let $\Gamma$ be a drawing in a surface $\Sigma$ and let $T$ be
the set of all points of $\Sigma$ that are $h$-insulated from $V(\Gamma \cap K)$ by $\Gamma$. Let
$\Gamma'$ be a $T$-variant of $\Gamma$ in $\Sigma$ with $\Gamma' \cap K = \Gamma \cap K$, let
$L' \subseteq \Gamma' \cup K$, and let $Z \subseteq V(K)$ with $|Z| \le p$. Then there exists a
subgraph $L$ of $\Gamma \cup K$ with the same effect on $Z$ as $L'$, with $L \cap K \subseteq L'$." -/
theorem theorem_4_1_free (p : ℕ) :
    ∃ h ≥ 1, ∀ (S : Type w) [TopologicalSpace S] [T2Space S], IsSurface S →
      ∀ {α : Type u} {β : Type v} (G Γ K G' Γ' L' : Graph α β),
      V(G).Finite → E(G).Finite → V(G').Finite → E(G').Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      Γ' ≤ G' → K ≤ G' → V(G') = V(Γ') ∪ V(K) → E(G') = E(Γ') ∪ E(K) →
      subgraphInter G Γ K = subgraphInter G' Γ' K →
      ∀ (D D' : Surface.Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β),
      Γ = D.toEmbeddedGraph ιV ιE → Γ' = D'.toEmbeddedGraph ιV ιE →
      IsVariant D D' (insulatedSet D (ιV ⁻¹' (V(Γ) ∩ V(K))) h) →
      ∀ (Z : Set α), Z ⊆ V(K) → Z.ncard ≤ p → L' ≤ G' →
      ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L' :=
  theorem_4_1_proof.{u, v, w} p

/-- **4.2** (Graph Minors XXII, page 538):
"For every integer $p \ge 0$ there exists $h \ge 1$ with the following property. Let $\Gamma, K$ be
subgraphs of a graph $\Gamma \cup K$, let $\Gamma$ be a drawing in a surface $\Sigma$, and let
$$Z \subseteq V(K) \cup (V(\Gamma) \cap \text{bd}(\Sigma)),$$
with $|Z| \le p$. For each cuff $C$ of $\Sigma$ let $S(C)$ be a sleeve for $C$ in $\Gamma$, so that
$S(C_1) \cap S(C_2) = \emptyset$ for all distinct cuffs $C_1, C_2$. Let $S$ be the union of
$\Sigma \cap S(C)$ over all cuffs $C$, and let $T$ be the set of all points of $\Sigma$ that are
$h$-insulated in $\hat{\Sigma}$ from $V(\Gamma \cap K) \cup (V(\Gamma) \cap \text{bd}(\Sigma))$ by
$\Gamma$. Suppose that
(i) for each cuff $C$ there are $|V(\Gamma) \cap C|$ mutually vertex-disjoint paths of $\Gamma$
between $V(\Gamma) \cap C$ and $V(\Gamma) \cap \text{bd}(S(C))$,
(ii) for each cuff $C$, $\text{bd}(S(C)) \subseteq T$ and $S(C) \cap V(\Gamma \cap K) = \emptyset$.
Then for every $(S \cup T)$-variant $\Gamma'$ of $\Gamma$ with $\Gamma' \cap K = \Gamma \cap K$ and
$V(\Gamma') \cap \text{bd}(\Sigma) = V(\Gamma) \cap \text{bd}(\Sigma)$, and for every
$L' \subseteq \Gamma' \cup K$, there exists $L \subseteq \Gamma \cup K$ with the same effect on $Z$
as $L'$, with $L \cap K \subseteq L'$." -/
theorem theorem_4_2_free (p : ℕ) :
    ∃ h ≥ 1, ∀ (S Shat : Type w) [TopologicalSpace S] [T2Space S]
      [TopologicalSpace Shat] [T2Space Shat],
      (hS : IsSurface S) → (cap : GM19.IsCappedSurface S Shat) →
      ∀ {α : Type u} {β : Type v} (G Γ K G' Γ' L' : Graph α β),
      V(G).Finite → E(G).Finite → V(G').Finite → E(G').Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      Γ' ≤ G' → K ≤ G' → V(G') = V(Γ') ∪ V(K) → E(G') = E(Γ') ∪ E(K) →
      subgraphInter G Γ K = subgraphInter G' Γ' K →
      ∀ (D D' : Surface.Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β),
      Γ = D.toEmbeddedGraph ιV ιE → Γ' = D'.toEmbeddedGraph ιV ιE →
      D.U ∩ bd S ⊆ D.V → D'.V ∩ bd S = D.V ∩ bd S →
      ∀ (S_sleeve : Set S → Set Shat),
      (∀ C ∈ cuffs S, IsSleeve cap D C (S_sleeve C)) →
      (∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S, C₁ ≠ C₂ → Disjoint (S_sleeve C₁) (S_sleeve C₂)) →
      (∀ C ∈ cuffs S, ∃ P : ↑(D.V ∩ C) → Graph S (Set S),
        (∀ x : ↑(D.V ∩ C), ∃ y ∈ D.V ∩ cap.emb ⁻¹' subBd (S_sleeve C),
          IsGraphPathWithEnds D.toGraph (P x) x.1 y) ∧
        Pairwise (fun x₁ x₂ => Disjoint V(P x₁) V(P x₂))) →
      (∀ C ∈ cuffs S,
        subBd (S_sleeve C) ⊆
          cap.emb '' (cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
            (cap.emb '' ((ιV ⁻¹' (V(Γ) ∩ V(K))) ∪ (D.V ∩ bd S))) h) ∧
        Disjoint (S_sleeve C) (cap.emb '' (ιV ⁻¹' (V(Γ) ∩ V(K))))) →
      IsVariant D D'
        ((⋃ C ∈ cuffs S, cap.emb ⁻¹' S_sleeve C) ∪
          cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
            (cap.emb '' ((ιV ⁻¹' (V(Γ) ∩ V(K))) ∪ (D.V ∩ bd S))) h) →
      ∀ (Z : Set α), Z ⊆ V(K) ∪ ιV '' (D.V ∩ bd S) → Z.ncard ≤ p → L' ≤ G' →
      ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L' :=
  theorem_4_2_proof.{u, v, w} p

/-- **5.3** (Graph Minors XXII, page 540):
"For every integer $p \ge 0$ there exists $\theta > p$ with the following property. Let $\Gamma, K$
be subgraphs of a graph $\Gamma \cup K$, let $\Gamma$ be a 2-cell drawing in a surface $\Sigma$ with
$\text{bd}(\Sigma) = \emptyset$, and let $\mathcal{T}$ be a respectful tangle in $\Gamma$ of order
$\ge \theta$, with metric $d$. Let $Z \subseteq V(\Gamma \cup K)$ with $|Z| \le p$, and let
$F_1, \ldots, F_t$ be $\Gamma$-normal $O$-arcs, such that
$$(F_1 \cup \cdots \cup F_t) \cap V(\Gamma) \subseteq Z \subseteq
((F_1 \cup \cdots \cup F_t) \cap V(\Gamma)) \cup V(K)$$
and $\text{ins}(F_1), \ldots, \text{ins}(F_t)$ are mutually disjoint. Suppose that
(i) for $1 \le i \le t$, there is no $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with
$|F \cap V(\Gamma)| < |F_i \cap V(\Gamma)|$ and $\text{ins}(F_i) \subseteq \text{ins}(F)$,
(ii) for $1 \le i < j \le t$, $d(\text{ins}(F_i), \text{ins}(F_j)) \ge \theta$,
(iii) for $1 \le i \le k$, $d(\text{ins}(F_i), v) \ge \theta$ for every $v \in V(\Gamma \cap K)$.
Let $R$ be the union of all atoms $z$ of $\Gamma$ with $d(z, v) \ge \theta$ for all
$v \in V(\Gamma \cap K)$, and let
$$\Sigma' = \Sigma \setminus \bigcup_{1 \le i \le t} (\text{ins}(F_i) \setminus F_i).$$
Let $\Gamma'$ be an $(R \cap \Sigma')$-variant of $\Gamma$ in $\Sigma$ with
$\Gamma' \cap K = \Gamma \cap K$ and with $\Gamma \cap \text{ins}(F_i) =
\Gamma' \cap \text{ins}(F_i)$ ($1 \le i \le t$), and let $L' \subseteq (\Gamma' \cap \Sigma') \cup K$.
Then there exists $L \subseteq (\Gamma \cap \Sigma') \cup K$ with the same effect on $Z$ as $L'$,
such that $L \cap K \subseteq L'$." -/
theorem theorem_5_3_free (p : ℕ) :
    ∃ θ : ℕ, p < θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
        {α : Type u} {β : Type v}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (Γ Γ' : Surface.Drawing S) (K L' : Graph α β)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S) (d : Set S → Set S → ℕ)
        (Z : Set α) (t : ℕ) (F : Fin t → Set S),
        IsClosedSurface S →
        V(K).Finite → E(K).Finite →
        (Γ.toEmbeddedGraph ιV ιE).Compatible K →
        Γ.IsTwoCell →
        θ ≤ ord →
        HasTangleMetric Γ ord T d →
        (∀ F₀ : Set S, IsOArc F₀ → Γ.IsNormal F₀ → (F₀ ∩ Γ.V).ncard < ord →
          IsTangleIns Γ T F₀ (ins F₀)) →
        Z ⊆ V(graphUnion (Γ.toEmbeddedGraph ιV ιE) K) →
        Z.ncard ≤ p →
        (∀ i : Fin t, IsOArc (F i) ∧ Γ.IsNormal (F i)) →
        ιV '' ((⋃ i : Fin t, F i) ∩ Γ.V) ⊆ Z →
        Z ⊆ ιV '' ((⋃ i : Fin t, F i) ∩ Γ.V) ∪ V(K) →
        Pairwise (fun i j : Fin t => Disjoint (ins (F i)) (ins (F j))) →
        (∀ i : Fin t, ¬ ∃ F₀ : Set S, IsOArc F₀ ∧ Γ.IsNormal F₀ ∧
          (F₀ ∩ Γ.V).ncard < (F i ∩ Γ.V).ncard ∧ ins (F i) ⊆ ins F₀) →
        (∀ i j : Fin t, i ≠ j → θ ≤ subsetTangleDist Γ ord d (ins (F i)) (ins (F j))) →
        (∀ i : Fin t, ∀ v ∈ Γ.V, ιV v ∈ V(K) →
          θ ≤ subsetTangleDist Γ ord d (ins (F i)) {v}) →
        let R := ⋃ z ∈ {z ∈ Γ.A | ∀ v ∈ Γ.V, ιV v ∈ V(K) → θ ≤ d z {v}}, z
        let S' := Set.univ \ ⋃ i : Fin t, (ins (F i) \ F i)
        IsVariant Γ Γ' (R ∩ S') →
        (Γ'.toEmbeddedGraph ιV ιE).Compatible K →
        (Γ'.toEmbeddedGraph ιV ιE) ⊓ K = (Γ.toEmbeddedGraph ιV ιE) ⊓ K →
        (∀ i : Fin t, Γ.interSet (ins (F i)) = Γ'.interSet (ins (F i))) →
        L' ≤ graphUnion ((Γ'.interSet S').toEmbeddedGraph ιV ιE) K →
        ∃ L ≤ graphUnion ((Γ.interSet S').toEmbeddedGraph ιV ιE) K,
          effectOn L Z = effectOn L' Z ∧ L ⊓ K ≤ L' :=
  theorem_5_3_proof.{u, v, w} p

/-- **Graph Minors XXII, (7.2)** (page 547):
"For all $q, \delta \ge 0$ there exists $\theta \ge 4$ with the following property. Let (J1)–(J6)
hold, and let $\mathcal{A}' \subseteq \mathcal{A}$ be adequate for some model $\phi'$ of
$(H, \chi)$ in $(G, \omega)$, where $d(v^*, D(A)) \ge \theta$ for all $A \in \mathcal{A}'$. Then
there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$." -/
theorem theorem_7_2_free (q δ : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (𝒜 𝒜' : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
        (Γ : Surface.Drawing S) (orient : GM19.SurfaceOrientation S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S) (d : Set S → Set S → ℕ)
        (D : Graph α β → Set S)
        (N K : Graph α β) (Δ : Set S) (v_star : S)
        (R_H : RootedDigraph αH βH q)
        (φV φV' : αH → Graph α β) (φE φE' : βH → β)
        (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
        IsRootedDigraphModel R_G R_H φV' φE' →
        IsAdequateFor ιV ιE W 𝒜 𝒜' Γ K R_H φV' φE' →
        (∀ A ∈ 𝒜', θ ≤ subsetTangleDist Γ ord d {v_star} (D A)) →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
            R_G.roots hJ.roots_mem_deleteVerts_v_star)
          R_H :=
  theorem_7_2_proof.{w, u, v, u₁, v₁} q δ

/-- **Graph Minors XXII, (7.3)** (pages 547–548):
"For all integers $q, \delta, \tau \ge 0$ there exists $\theta \ge 5$ with the following property.
Let (J1)–(J6) hold, and let $\mathcal{B} \subseteq \mathcal{A}$ be adequate for $\phi$. Let
$A_1, \dots, A_t \in \mathcal{B}$ where $t \le \tau$, and let
$d(D(A), \Sigma \setminus \Delta) \ge \theta$ for every
$A \in \mathcal{B} \setminus \{A_1, \dots, A_t\}$. Let $A_1', \dots, A_t' \in \mathcal{A}$, and
suppose that
(i) for $1 \le i \le t$, $(A_i', \pi(A_i') + \omega)$ has the same $\delta$-folio as
$(A_i, \pi(A_i) + \omega)$,
(ii) for $1 \le i \le t$, $D(A_i) \cap \Delta = \emptyset$,
(iii) for $1 \le i \le t$, $d(v^*, D(A_i')) \ge \theta$ and $D(A_i') \cap \Delta = \emptyset$,"
"(iv) for $1 \le i < j \le t$, $d(D(A_i'), D(A_j')) \ge \theta$,
(v) for $1 \le i \le t$, there is no $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with
$|F \cap V(\Gamma)| < |\bar{\pi}(A_i')|$ and with $D(A_i') \subseteq ins(F)$.
Then there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$." -/
theorem theorem_7_3_free (q δ τ : ℕ) :
    ∃ θ : ℕ, 5 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (𝒜 ℬ : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
        (Γ : Surface.Drawing S) (orient : GM19.SurfaceOrientation S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S) (d : Set S → Set S → ℕ)
        (D : Graph α β → Set S)
        (N K : Graph α β) (Δ : Set S) (v_star : S)
        (R_H : RootedDigraph αH βH q)
        (φV : αH → Graph α β) (φE : βH → β)
        (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
        IsAdequateFor ιV ιE W 𝒜 ℬ Γ K R_H φV φE →
        ∀ (t : ℕ) (A_fam A_fam' : Fin t → Graph α β),
        t ≤ τ →
        (∀ i : Fin t, A_fam i ∈ ℬ) →
        (∀ i : Fin t, A_fam' i ∈ 𝒜) →
        (∀ A ∈ ℬ \ Set.range A_fam,
          θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)) →
        ∀ (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i)),
        (∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
          (hπi : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (ιV ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
          (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (fun k : Fin (πLen (A_fam i)) =>
              ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
          HasSameDeltaFolio
            (subRootedDigraph R_G.G (A_fam' i) hA'i
              (seqConcat (fun k : Fin (πLen (A_fam i)) =>
                ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
            (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV ∘ πS (A_fam i)) R_G.roots) hπi) δ) →
        (∀ i : Fin t, Disjoint (D (A_fam i)) Δ) →
        (∀ i : Fin t, θ ≤ subsetTangleDist Γ ord d {v_star} (D (A_fam' i))) →
        (∀ i : Fin t, Disjoint (D (A_fam' i)) Δ) →
        (∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j))) →
        (∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
          (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F) →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
            R_G.roots hJ.roots_mem_deleteVerts_v_star)
          R_H :=
  theorem_7_3_proof q δ τ

/-- **Graph Minors XXII, (7.4)** (pages 552–553):
"For all integers $q, \delta, \tau \ge 0$ there exists $\theta \ge 4$ with the following property.
Let (J1)–(J7) hold, and let $\mathcal{B} \subseteq \mathcal{A}$ be sufficient for $\phi$. Let
$A_1, \ldots, A_t \in \mathcal{B}$ where $t \le \tau$, and let
$d(D(A), \Sigma \setminus \Delta) \ge \theta$ for every
$A \in \mathcal{B} \setminus \{A_1, \ldots, A_t\}$. Let $A'_1, \ldots, A'_t \in \mathcal{A}$, and
suppose that"
"(i) for $1 \le i \le t$, $(A'_i, \pi(A'_i) + \omega)$ has the same $\delta$-folio as
$(A_i, \pi(A_i) + \omega)$,
(ii) for $1 \le i \le t$, $D(A_i) \cap \Delta = \emptyset$,
(iii) for $1 \le i \le t$, $d(v^*, D(A'_i)) \ge \theta$ and $D(A'_i) \cap \Delta = \emptyset$,
(iv) for $1 \le i < j \le t$, $d(D(A'_i), D(A'_j)) \ge \theta$.
Then there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$." -/
theorem theorem_7_4_free (q δ τ : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
        (ιV₀ : S ↪ α) (ιE₀ : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (𝒜 ℬ : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
        (Γ₀ : Surface.Drawing S) (orient : GM19.SurfaceOrientation S)
        (ord₀ : ℕ) (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins₀ : Set S → Set S) (d₀ : Set S → Set S → ℕ)
        (D : Graph α β → Set S)
        (N K : Graph α β) (Δ : Set S) (v_star : S)
        (R_H : RootedDigraph αH βH q)
        (φV₀ : αH → Graph α β) (φE₀ : βH → β)
        (hJ₀ : SystemJ1ToJ6 ιV₀ ιE₀ R_G W 𝒜 πLen πS Γ₀ orient θ ord₀ T₀ ins₀ d₀ D N K Δ v_star δ R_H φV₀ φE₀),
        ConditionJ7 ιV₀ ιE₀ R_G.G.toGraph W 𝒜 πLen πS Γ₀ T₀ →
        IsSufficientFor W 𝒜 ℬ K R_H φV₀ φE₀ →
        ∀ (t : ℕ) (A_fam A_fam' : Fin t → Graph α β),
        t ≤ τ →
        (∀ i : Fin t, A_fam i ∈ ℬ) →
        (∀ i : Fin t, A_fam' i ∈ 𝒜) →
        (∀ A ∈ ℬ \ Set.range A_fam,
          θ ≤ subsetTangleDist Γ₀ ord₀ d₀ (D A) (Set.univ \ Δ)) →
        ∀ (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i)),
        (∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
          (hπi : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (ιV₀ ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
          (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (fun k : Fin (πLen (A_fam i)) =>
              ιV₀ (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
          HasSameDeltaFolio
            (subRootedDigraph R_G.G (A_fam' i) hA'i
              (seqConcat (fun k : Fin (πLen (A_fam i)) =>
                ιV₀ (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
            (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV₀ ∘ πS (A_fam i)) R_G.roots) hπi) δ) →
        (∀ i : Fin t, Disjoint (D (A_fam i)) Δ) →
        (∀ i : Fin t, θ ≤ subsetTangleDist Γ₀ ord₀ d₀ {v_star} (D (A_fam' i))) →
        (∀ i : Fin t, Disjoint (D (A_fam' i)) Δ) →
        (∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ₀ ord₀ d₀ (D (A_fam' i)) (D (A_fam' j))) →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV₀ v_star}) Graph.deleteVerts_le
            R_G.roots hJ₀.roots_mem_deleteVerts_v_star)
          R_H :=
  theorem_7_4_proof q δ τ

/-- **Graph Minors XXII, (8.2)** (Section 8, page 557):
"For all integers $q, \delta, \eta \ge 0$ there exists $\theta \ge 4$ with the following property.
Let (J1)–(J7) hold, and suppose that for every $A \in \mathcal{A}$ with $D(A) \cap \Delta = \emptyset$
and every $v \in V(\Gamma)$ with $v \notin \Delta$, there exists $A' \in \mathcal{A}$ with
$d(v, D(A')) \le \eta$ such that $(A', \pi(A') + \omega)$ has the same $\delta$-folio as
$(A, \pi(A) + \omega)$. Suppose also that $d(v^*, \Delta) \ge \theta$. Then there is a model of
$(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$." -/
theorem theorem_8_2_free (q δ η : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (𝒜 : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
        (Γ : Surface.Drawing S) (orient : GM19.SurfaceOrientation S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S) (d : Set S → Set S → ℕ)
        (D : Graph α β → Set S)
        (N K : Graph α β) (Δ : Set S) (v_star : S)
        (R_H : RootedDigraph αH βH q)
        (φV : αH → Graph α β) (φE : βH → β)
        (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
        ConditionJ7 ιV ιE R_G.G.toGraph W 𝒜 πLen πS Γ T →
        (∀ A ∈ 𝒜, Disjoint (D A) Δ → ∀ v ∈ Γ.V, v ∉ Δ →
          ∃ A' ∈ 𝒜, subsetTangleDist Γ ord d {v} (D A') ≤ η ∧
            ∃ hlen : πLen A' = πLen A,
              ∀ (hA : A ≤ R_G.G.toGraph) (hA' : A' ≤ R_G.G.toGraph)
                (hπ : ∀ k : Fin (πLen A + q),
                  seqConcat (ιV ∘ πS A) R_G.roots k ∈ V(A))
                (hπ' : ∀ k : Fin (πLen A + q),
                  seqConcat (fun k : Fin (πLen A) =>
                    ιV (πS A' (Fin.cast hlen.symm k))) R_G.roots k ∈ V(A')),
                HasSameDeltaFolio
                  (subRootedDigraph R_G.G A' hA'
                    (seqConcat (fun k : Fin (πLen A) =>
                      ιV (πS A' (Fin.cast hlen.symm k))) R_G.roots) hπ')
                  (subRootedDigraph R_G.G A hA
                    (seqConcat (ιV ∘ πS A) R_G.roots) hπ) δ) →
        θ ≤ subsetTangleDist Γ ord d {v_star} Δ →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
            R_G.roots hJ.roots_mem_deleteVerts_v_star)
          R_H :=
  theorem_8_2_proof.{w, u, v, u₁, v₁} q δ η

/-- **Graph Minors XXII, (8.3)** (Section 8, pages 559–560):
"For all $q, \delta \ge 0$ and $h \ge 4$, there exists $\theta \ge h$ with the following property.
Let $G$ be a digraph, let $W \subseteq V(G)$ with $|W| = q$, and let $\omega$ be an ordering of $W$.
Let $\Gamma \subseteq G \setminus W$ satisfy the following."
(i) *$\Gamma$ is a drawing in a sphere $\Sigma$, and $\Gamma$ is a subdivision of a simple
3-connected graph, and there is an orientation of $\Sigma$ called clockwise.*
(ii) *$C_0$ is a circuit of $\Gamma$, and $U(C_0)$ bounds a region of $\Gamma$.*
(iii) *$\Pi \subseteq V(C_0)$ with $|\Pi| = 4$.*
(iv) *$\mathcal{T}$ is a tangle in $\Gamma$ of order $\ge \theta$, and there is no
$(A, B) \in \mathcal{T}$ with order $\le 3$ such that $\Pi \subseteq V(A)$; $d$ is the metric of
$\mathcal{T}$.*
(v) *$J \subseteq G$ has vertex set the union of $W$, $V(\Gamma)$, and the vertex sets of all
components of $G \setminus (V(C_0) \cup W)$ which meet $V(\Gamma)$, and edge set all edges of $G$
with both ends in $V(J)$.*
(vi) *$Z \subseteq V(J) \setminus W$ with $\Pi \subseteq Z$, and $\mathcal{A}$ is a
$(Z \cup W)$-division of $J$, such that $W \subseteq V(A)$ for all $A \in \mathcal{A}$.*
(vii) *For each $A \in \mathcal{A}$, $Z \cap V(A) = \bar{\pi}(A)$, and $|\bar{\pi}(A)| \le 3$, and
$\pi(A)$ is a linear order of $\bar{\pi}(A)$.*
(viii) *For each $A \in \mathcal{A}$, there are $\bar{\pi}(A)$ mutually vertex-disjoint paths of
$J \setminus W$ between $\bar{\pi}(A)$ and $\Pi$, and if $|\bar{\pi}(A)| = 3$ and $\pi(A)$ is
$s_1, s_2, s_3$ say, these three paths can be chosen with ends $s_i, t_i$ ($i = 1, 2, 3$) so that
$t_1, t_2, t_3$ occur in clockwise order in the boundary of the disc containing $U(\Gamma)$ bounded
by $U(C_0)$.*
(ix) *For each $A \in \mathcal{A}$, if $u, v \in \bar{\pi}(A)$ there is a path of $A \setminus W$
between $u$ and $v$ with no internal vertex in $\bar{\pi}(A)$.*
(x) *Let $G'$ be the bipartite graph with vertex set $Z \cup \mathcal{A}$, in which $z \in Z$ and
$A \in \mathcal{A}$ are adjacent if $z \in V(A)$; then $G'$ is planar, and can be drawn in a closed
disc with the vertices of $\Pi$ in the boundary of the disc, in the same order in which they occur
in $U(C_0)$.*
(xi) *For each $A \in \mathcal{A}$, there is a vertex $v(A) \in V(\Gamma)$ such that there is a path
of $G \setminus W$ between $v(A)$ and a vertex of $\bar{\pi}(A)$, with no vertex in $V(\Gamma)$
except $v(A)$.*
(xii) *$D \subseteq \Sigma$ is a closed disc with $\text{bd}(D) \subseteq U(\Gamma)$ including the
region of $\Gamma$ bounded by $U(C_0)$.*
(xiii) *If $A \in \mathcal{A}$ and $v(A) \in \Sigma \setminus D$ then for every
$v \in V(\Gamma) \setminus D$, either $d(v, D) \le h$ or there exists $A' \in \mathcal{A}$ such
that $d(v, v(A')) \le h$ and $(A', \pi(A') + \omega)$ has the same $\delta$-folio as
$(A, \pi(A) + \omega)$.*
(xiv) *$v^* \in V(\Gamma) \setminus D$, and $d(v^*, D) \ge \theta$.*
"Then $(G \setminus \{v^*\}, \omega)$ has the same $\delta$-folio as $(G, \omega)$." -/
theorem theorem_8_3_free (q δ h : ℕ) :
    ∃ θ : ℕ, h ≤ θ ∧ 4 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (Γ C₀ : GM19.Drawing S) (r₀ : Set S) (orient : GM19.SurfaceOrientation S)
        (PiSet : Set S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (J : Graph α β) (Z : Set α) (𝒜 : Set (Graph α β))
        (πLen : Graph α β → ℕ) (πA : ∀ A : Graph α β, Fin (πLen A) → α)
        (vA : Graph α β → S) (D_disc : Set S) (v_star : S)
        (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
          πLen πA vA D_disc v_star),
        HasSameDeltaFolio
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
            R_G.roots h83.roots_mem_deleteVerts_v_star)
          R_G δ :=
  theorem_8_3_proof.{w, u, v} q δ h

/-- **Graph Minors XIII, (10.2)** (`GM13.GM13Theorem102Statement`), proved in Graph Minors XXII,
Section 8 (page 563: "Consequently, Theorem 10.2 of [5] is true."), instantiated at
`GM21.theorem_1_1_proof` with no hypotheses. -/
theorem gm13_theorem_10_2_free :
    GM13.GM13Theorem102Statement.{u, v} :=
  gm13_theorem_10_2.{u, v} gm21Theorem11.{u, v}

end GraphMinor.GM22
