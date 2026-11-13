module

public import GraphMinor.GM22.Defs
public import GraphMinor.GM22.Section2Basic
import GraphMinor.GM12.Section1
import GraphMinor.GM14.Section9a

/-!
# Graph Minors XXII: Statements from Sections 3, 5, and 6 Used in Sections 7 and 8

This file states the results from Sections 3, 5, and 6 of:
N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563
that are used in Sections 7 and 8 (`GM22Theorem31Statement`, `GM22Theorem51Statement`,
`GM22Theorem52Statement`, `GM22Theorem53Statement`, `GM22Theorem61Statement`,
`GM22Theorem62Statement`, `GM22Theorem63Statement`), and proves `gm22_theorem_5_1`,
`gm22_theorem_6_1`, and `gm22_theorem_6_2`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
  GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 Hypergraph

universe w u v u₁ v₁ u₂ v₂

/-! ## Section 3 Statement: 3.1 (page 534) -/

/-- **Graph Minors XXII, (3.1)** (page 534):
"For every integer $p \ge 0$ there exists $h \ge 1$ with the following property. Let $\Gamma, K$ be
subgraphs of a graph $G$ with $G = \Gamma \cup K$, and let $\Gamma$ be a drawing in a surface
$\Sigma$. Let $v \in V(\Gamma)$ be $h$-insulated from $V(\Gamma \cap K)$ by $\Gamma$, let
$Z \subseteq V(K)$ with $|Z| \le p$, and let $L \subseteq G$. Then there is a subgraph $L'$ of
$G \setminus \{v\}$ with the same effect on $Z$ as $L$ and with $L' \cap K \subseteq L$." -/
def GM22Theorem31Statement : Prop :=
  ∀ p : ℕ, ∃ h : ℕ, 1 ≤ h ∧
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
      {α : Type u} {β : Type v}
      (ιV : S ↪ α) (ιE : Set S ↪ β)
      (G K L : Graph α β) (Γ : Drawing S) (v : S) (Z : Set α),
      IsSurface S →
      V(G).Finite → E(G).Finite →
      Γ.toEmbeddedGraph ιV ιE ≤ G → K ≤ G →
      G = graphUnion (Γ.toEmbeddedGraph ιV ιE) K →
      v ∈ Γ.V →
      IsInsulated Γ {x ∈ Γ.V | ιV x ∈ V(K)} h v →
      Z ⊆ V(K) → Z.ncard ≤ p →
      L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v},
        effectOn L' Z = effectOn L Z ∧ L' ⊓ K ≤ L

/-! ## Section 5 Statements: 5.1, 5.2, 5.3 (pages 539–540) -/

/-- **Graph Minors XXII, (5.1)** (page 539):
"Let $\Gamma$ be a 2-cell drawing in a surface $\Sigma$ with $\text{bd}(\Sigma) = \emptyset$, and
let $\mathcal{T}$ be a respectful tangle in $\Gamma$, with metric $d$. Let $z \in A(H)$, and
let $\kappa$ be an integer with $2 \le \kappa \le \text{ord}(\mathcal{T}) - 3$. Then there is a
closed disc $\Delta \subseteq \Sigma$ satisfying
(i) $\text{bd}(\Delta) \subseteq U(\Gamma)$,
(ii) $d(z, x) \le \kappa + 2$ for all $x \in A(\Gamma)$ with $x \cap \Delta \ne \emptyset$,
(iii) $d(z, x) \ge \kappa$ for all $x \in A(\Gamma)$ with $x \nsubseteq \Delta \setminus \text{bd}(\Delta)$ (and in particular, $z \subseteq \Delta \setminus \text{bd}(\Delta)$)."
The print has "$z \in A(H)$", a misprint for $z \in A(\Gamma)$: no $H$ is defined there, and
$d(z, x)$ needs $z$ to be an atom of $\Gamma$. The Lean takes $z \in A(\Gamma)$. See the correction
on page 539 in `corrections/GM22.md`. -/
def GM22Theorem51Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (Γ : Drawing S) (ord κ : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (z : Set S),
    IsClosedSurface S →
    HasTangleMetric Γ ord T d →
    z ∈ Γ.A →
    2 ≤ κ → κ + 3 ≤ ord →
    ∃ Δ : Set S,
      IsClosedDisc Δ ∧
      subBd Δ ⊆ Γ.U ∧
      (∀ x ∈ Γ.A, (x ∩ Δ).Nonempty → d z x ≤ κ + 2) ∧
      (∀ x ∈ Γ.A, ¬ (x ⊆ Δ \ subBd Δ) → κ ≤ d z x) ∧
      z ⊆ Δ \ subBd Δ

/-- Proof of **Graph Minors XXII, (5.1)** (page 539) from Graph Minors XIV, (9.2)
(`GM14.full_of_9_2`). -/
theorem gm22_theorem_5_1 : GM22Theorem51Statement.{w} := by
  intro S _ _ _ Γ ord κ T d z hS hMetric hz hκ2 hκord
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨C, Λ, hCΓ, hC, hbdΛ, hbd_clΛ, hdiffΛ, hZone, hx_sub⟩ :=
    GM14.full_of_9_2 hS inferInstance Γ ord κ T d z hMetric hz hκ2 hκord
  refine ⟨closure Λ, hZone.isClosedDisc_closure, ?_, ?_, ?_, ?_⟩
  · rw [hbd_clΛ]
    exact hCΓ.U_subset
  · intro x hx hx_meet
    have hx_sub_cl : x ⊆ closure Λ := by
      rcases hx with (⟨v, hv, rfl⟩ | he) | hr
      · rcases hx_meet with ⟨_, rfl, hvcl⟩
        exact singleton_subset_iff.mpr hvcl
      · by_cases he_bd : (x ∩ subBd (closure Λ)).Nonempty
        · rcases he_bd with ⟨p, hpx, hpbd⟩
          rw [hbd_clΛ] at hpbd
          have hpU : p ∈ C.U := hpbd
          have hp_not_V : p ∉ C.V := fun hpV => (he.2.1 hpx).2 (hCΓ.1 hpV)
          obtain ⟨e', he'C, hpe'⟩ := C.exists_edge_of_mem hpU hp_not_V
          have he'_eq : e' = x := Γ.edge_eq_of_mem (hCΓ.2 he'C) he hpe' hpx
          subst he'_eq
          have hsub_cl : subBd (closure Λ) ⊆ closure Λ := by
            rw [GM11.subBd_eq_frontier]
            exact frontier_subset_iff_isClosed.mpr isClosed_closure
          exact he'C.2.1.trans (Set.sdiff_subset.trans (by rw [← hbd_clΛ]; exact hsub_cl))
        · have hdis : Disjoint x (frontier (closure Λ)) := by
            rw [← GM11.subBd_eq_frontier, disjoint_iff_inter_eq_empty]
            exact not_nonempty_iff_eq_empty.mp he_bd
          rcases hx_meet with ⟨p, hpx, hpcl⟩
          exact GM12.subset_of_disjoint_frontier
            he.2.2.1.isConnected.isPreconnected isClosed_closure hdis hpx hpcl
      · have hdis : Disjoint x (frontier (closure Λ)) := by
          rw [← GM11.subBd_eq_frontier, hbd_clΛ]
          exact disjoint_left.mpr fun p hpx hpC =>
            region_subset hr hpx (hCΓ.U_subset hpC)
        rcases hx_meet with ⟨p, hpx, hpcl⟩
        exact GM12.subset_of_disjoint_frontier
          (region_isPreconnected hr) isClosed_closure hdis hpx hpcl
    exact hZone.dist_le x hx hx_sub_cl
  · intro x hx hnot
    rw [hbd_clΛ, hdiffΛ] at hnot
    by_contra! hlt
    exact hnot (hx_sub x hx hlt)
  · rw [hbd_clΛ, hdiffΛ]
    exact hx_sub z hz (by rw [GM12.metric_self hMetric hz]; omega)

/-- **Graph Minors XXII, (5.2)** (page 540):
"Let $h \ge 1$ be an integer, let $\Gamma$ be a 2-cell drawing in a surface $\Sigma$ with
$\text{bd}(\Sigma) = \emptyset$, and let $\mathcal{T}$ be a respectful tangle in $\Gamma$ of order
$\ge 2h + 5$, with metric $d$. Let $x \in \Sigma$, and let $Y$ be the union of all atoms
$y \in A(\Gamma)$ with $d(y, z) \ge 2h + 5$, where $z$ is the atom of $\Gamma$ with $x \in z$. Then
$x$ is $h$-insulated from $Y$ by $\Gamma$." -/
def GM22Theorem52Statement : Prop :=
  ∀ {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (h : ℕ) (Γ : Drawing S) (ord : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (x : S) (z Y : Set S),
    1 ≤ h →
    IsClosedSurface S →
    2 * h + 5 ≤ ord →
    HasTangleMetric Γ ord T d →
    z ∈ Γ.A → x ∈ z →
    Y = (⋃ y ∈ {y ∈ Γ.A | 2 * h + 5 ≤ d y z}, y) →
    IsInsulated Γ Y h x

/-- **Graph Minors XXII, (5.3)** (page 540):
"For every integer $p \ge 0$ there exists $\theta > p$ with the following property. Let $\Gamma, K$
be subgraphs of a graph $\Gamma \cup K$, let $\Gamma$ be a 2-cell drawing in a surface $\Sigma$ with
$\text{bd}(\Sigma) = \emptyset$, and let $\mathcal{T}$ be a respectful tangle in $\Gamma$ of order
$\ge \theta$, with metric $d$. Let $Z \subseteq V(\Gamma \cup K)$ with $|Z| \le p$, and let
$F_1, \ldots, F_t$ be $\Gamma$-normal $O$-arcs, such that
$$(F_1 \cup \cdots \cup F_t) \cap V(\Gamma) \subseteq Z \subseteq ((F_1 \cup \cdots \cup F_t) \cap V(\Gamma)) \cup V(K)$$
and $\text{ins}(F_1), \ldots, \text{ins}(F_t)$ are mutually disjoint. Suppose that
(i) for $1 \le i \le t$, there is no $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ with $|F \cap V(\Gamma)| < |F_i \cap V(\Gamma)|$ and $\text{ins}(F_i) \subseteq \text{ins}(F)$,
(ii) for $1 \le i < j \le t$, $d(\text{ins}(F_i), \text{ins}(F_j)) \ge \theta$,
(iii) for $1 \le i \le k$, $d(\text{ins}(F_i), v) \ge \theta$ for every $v \in V(\Gamma \cap K)$.
Let $R$ be the union of all atoms $z$ of $\Gamma$ with $d(z, v) \ge \theta$ for all $v \in V(\Gamma \cap K)$, and let
$$\Sigma' = \Sigma \setminus \bigcup_{1 \le i \le t} (\text{ins}(F_i) \setminus F_i).$$
Let $\Gamma'$ be an $(R \cap \Sigma')$-variant of $\Gamma$ in $\Sigma$ with $\Gamma' \cap K = \Gamma \cap K$ and with $\Gamma \cap \text{ins}(F_i) = \Gamma' \cap \text{ins}(F_i)$ ($1 \le i \le t$), and let $L' \subseteq (\Gamma' \cap \Sigma') \cup K$. Then there exists $L \subseteq (\Gamma \cap \Sigma') \cup K$ with the same effect on $Z$ as $L'$, such that $L \cap K \subseteq L'$." -/
def GM22Theorem53Statement : Prop :=
  ∀ p : ℕ, ∃ θ : ℕ, p < θ ∧
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
      {α : Type u} {β : Type v}
      (ιV : S ↪ α) (ιE : Set S ↪ β)
      (Γ Γ' : Drawing S) (K L' : Graph α β)
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
        effectOn L Z = effectOn L' Z ∧ L ⊓ K ≤ L'

/-! ## Section 6 Statements: 6.1, 6.2, 6.3 (pages 542–545) -/

/-- **Graph Minors XXII, (6.1)** (page 542):
"If $H$ has detail $\le \delta$, every basis for $\phi$ includes a basis of cardinality $\le q + 3\delta$." -/
def GM22Theorem61Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁} {q δ : ℕ}
    (R_G : RootedDigraph α β q) (R_H : RootedDigraph αH βH q)
    (φV : αH → Graph α β) (φE : βH → β) (Z : Set α),
    R_H.HasDetailLE δ →
    IsRootedDigraphModel R_G R_H φV φE →
    IsModelBasis R_G R_H φV φE Z →
    ∃ Z' ⊆ Z, IsModelBasis R_G R_H φV φE Z' ∧ Z'.ncard ≤ q + 3 * δ

/-- Proof of **Graph Minors XXII, (6.1)** (page 542). -/
theorem gm22_theorem_6_1 : GM22Theorem61Statement.{u, v, u₁, v₁} := by
  intro α β αH βH q δ R_G R_H φV φE Z hDet hMod hBasis
  classical
  have hfin_E : E(R_H.G.toGraph).Finite := hDet.2.1
  have hfin_Vdiff : (V(R_H.G.toGraph) \ Set.range R_H.roots).Finite := hDet.1.sdiff
  let Vdiff : Set αH := V(R_H.G.toGraph) \ Set.range R_H.roots
  let pickV : Vdiff → α := fun v =>
    Classical.choose (hBasis.inter_φV_nonempty v.1 v.2.1)
  have hpickV_mem : ∀ v : Vdiff, pickV v ∈ Z ∧ pickV v ∈ V(φV v.1) := by
    intro v
    exact Classical.choose_spec (hBasis.inter_φV_nonempty v.1 v.2.1)
  let Z₁ : Set α := Set.range R_G.roots
  let Z₂h : Set α := (fun e => R_G.G.head (φE e)) '' E(R_H.G.toGraph)
  let Z₂t : Set α := (fun e => R_G.G.tail (φE e)) '' E(R_H.G.toGraph)
  let Z₃ : Set α := Set.range pickV
  let Z' : Set α := Z₁ ∪ Z₂h ∪ Z₂t ∪ Z₃
  have hZ₁_sub : Z₁ ⊆ Z := by
    rintro _ ⟨i, rfl⟩
    exact hBasis.roots_mem i
  have hZ₂h_sub : Z₂h ⊆ Z := by
    rintro _ ⟨e, he, rfl⟩
    exact hBasis.head_mem e he
  have hZ₂t_sub : Z₂t ⊆ Z := by
    rintro _ ⟨e, he, rfl⟩
    exact hBasis.tail_mem e he
  have hZ₃_sub : Z₃ ⊆ Z := by
    rintro _ ⟨v, rfl⟩
    exact (hpickV_mem v).1
  have hZ'_sub : Z' ⊆ Z :=
    union_subset (union_subset (union_subset hZ₁_sub hZ₂h_sub) hZ₂t_sub) hZ₃_sub
  refine ⟨Z', hZ'_sub, ?_, ?_⟩
  · refine ⟨hZ'_sub.trans hBasis.subset_V, ?_, ?_, ?_, ?_⟩
    · intro i
      exact Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))
    · intro e he
      exact Or.inl (Or.inl (Or.inr ⟨e, he, rfl⟩))
    · intro e he
      exact Or.inl (Or.inr ⟨e, he, rfl⟩)
    · intro v hv
      by_cases hroot : v ∈ Set.range R_H.roots
      · rcases hroot with ⟨i, rfl⟩
        exact ⟨R_G.roots i, Or.inl (Or.inl (Or.inl ⟨i, rfl⟩)), hMod.root_mem i⟩
      · let v' : Vdiff := ⟨v, hv, hroot⟩
        exact ⟨pickV v', Or.inr ⟨v', rfl⟩, (hpickV_mem v').2⟩
  · have : Finite Vdiff := hfin_Vdiff.to_subtype
    have hc₁ : Z₁.ncard ≤ q := by
      have h : (R_G.roots '' Set.univ).ncard ≤ (Set.univ : Set (Fin q)).ncard :=
        Set.ncard_image_le Set.finite_univ
      simpa [Z₁, Set.image_univ, Set.ncard_univ, Nat.card_fin] using h
    have hc₂h : Z₂h.ncard ≤ δ := (ncard_image_le hfin_E).trans hDet.2.2.1
    have hc₂t : Z₂t.ncard ≤ δ := (ncard_image_le hfin_E).trans hDet.2.2.1
    have hc₃ : Z₃.ncard ≤ δ := by
      have h : (pickV '' Set.univ).ncard ≤ (Set.univ : Set Vdiff).ncard :=
        Set.ncard_image_le Set.finite_univ
      have hcard_univ : (Set.univ : Set Vdiff).ncard = Vdiff.ncard := by
        rw [Set.ncard_univ, Nat.card_coe_set_eq]
      have h' : Z₃.ncard ≤ Vdiff.ncard := by
        simpa [Z₃, Set.image_univ, hcard_univ] using h
      exact h'.trans hDet.2.2.2
    calc Z'.ncard
      _ ≤ (Z₁ ∪ Z₂h ∪ Z₂t).ncard + Z₃.ncard :=
          ncard_union_le (Z₁ ∪ Z₂h ∪ Z₂t) Z₃
      _ ≤ (Z₁ ∪ Z₂h).ncard + Z₂t.ncard + Z₃.ncard :=
          Nat.add_le_add_right (ncard_union_le (Z₁ ∪ Z₂h) Z₂t) _
      _ ≤ Z₁.ncard + Z₂h.ncard + Z₂t.ncard + Z₃.ncard :=
          Nat.add_le_add_right (Nat.add_le_add_right (ncard_union_le Z₁ Z₂h) _) _
      _ ≤ q + 3 * δ := by omega

/-- **Graph Minors XXII, (6.2)** (page 542):
"Let $\phi$ be a model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$, let $Z$ be a basis
for $\phi$, let $L = \bigcup(\phi(v) : v \in V(H))$, and let $L' \subseteq G \setminus \phi(E(H))$
with the same effect on $Z$ as $L$. Define $\phi'(e) = \phi(e)$ ($e \in E(H)$), and for $v \in V(H)$
let $\phi'(v)$ be the component $T$ of $L'$ with $V(T) \cap Z = V(\phi(v)) \cap Z$. Then $\phi'$ is
a model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$." -/
def GM22Theorem62Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁} {q : ℕ}
    (R_G : RootedDigraph α β q) (R_H : RootedDigraph αH βH q)
    (φV : αH → Graph α β) (φE : βH → β) (Z : Set α) (L L' : Graph α β),
    IsRootedDigraphModel R_G R_H φV φE →
    IsModelBasis R_G R_H φV φE Z →
    L = subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)) →
    L' ≤ R_G.G.toGraph.deleteEdges (φE '' E(R_H.G.toGraph)) →
    effectOn L' Z = effectOn L Z →
    ∃ φ'V : αH → Graph α β,
      (∀ v ∈ V(R_H.G.toGraph), IsGraphComponent (φ'V v) L' ∧
        V(φ'V v) ∩ Z = V(φV v) ∩ Z) ∧
      IsRootedDigraphModel R_G R_H φ'V φE

/-- In $L = \bigcup_{v \in V(H)} \phi(v)$ for a model $\phi$, each $\phi(v)$ ($v \in V(H)$) is a
connected component of $L$. -/
theorem IsRootedDigraphModel.isGraphComponent_φV
    {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁} {q : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hMod : IsRootedDigraphModel R_G R_H φV φE)
    {v : αH} (hv : v ∈ V(R_H.G.toGraph)) :
    IsGraphComponent (φV v) (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))) := by
  let L := subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))
  have hP_le : ∀ P ∈ φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨w, hw, rfl⟩
    exact hMod.subgraph_of_mem w hw
  have hφ_le_L : φV v ≤ L := le_subgraphSUnion hP_le ⟨v, hv, rfl⟩
  have hφ_conn : IsGraphConnected (φV v) := hMod.connected_of_mem v hv
  refine ⟨hφ_le_L, hφ_conn, fun H hle hHL hHconn => ?_⟩
  have hle_V : V(H) ⊆ V(φV v) := by
    obtain ⟨u₀, hu₀⟩ := hφ_conn.1
    intro u hu
    obtain ⟨W⟩ := hHconn.2 u₀ (hle.vertexSet_mono hu₀) u hu
    obtain ⟨W_L, _, _⟩ := exists_walk_up_of_le hHL W
    have hwalk_sub : ∀ {x y : α} (P : GraphWalk L x y), x ∈ V(φV v) → y ∈ V(φV v) := by
      intro x y P
      induction P with
      | nil _ => exact id
      | @cons a b c e hlink rest ih =>
        intro ha
        apply ih
        have heL : e ∈ E(L) := hlink.edge_mem
        rw [edgeSet_subgraphSUnion hP_le, mem_iUnion₂] at heL
        rcases heL with ⟨_, ⟨w, hw, rfl⟩, hew⟩
        obtain ⟨x', y', hlink_w⟩ := (φV w).exists_isLink_of_mem_edgeSet hew
        have hlink_L : L.IsLink e x' y' := hlink_w.mono (le_subgraphSUnion hP_le ⟨w, hw, rfl⟩)
        have ha_w : a ∈ V(φV w) := by
          rcases hlink.left_eq_or_eq hlink_L with rfl | rfl
          · exact hlink_w.left_mem
          · exact hlink_w.right_mem
        have hb_w : b ∈ V(φV w) := by
          rcases hlink.right_eq_or_eq hlink_L with rfl | rfl
          · exact hlink_w.left_mem
          · exact hlink_w.right_mem
        have hvw : v = w := by
          by_contra hne
          exact Disjoint.le_bot (hMod.disjoint_V v hv w hw hne).1 ⟨ha, ha_w⟩
        subst hvw
        exact hb_w
    exact hwalk_sub W_L hu₀
  have hle_E : E(H) ⊆ E(φV v) := by
    intro e he
    obtain ⟨x, y, hxyH⟩ := H.exists_isLink_of_mem_edgeSet he
    have hx_v : x ∈ V(φV v) := hle_V hxyH.left_mem
    have heL : e ∈ E(L) := (hxyH.mono hHL).edge_mem
    rw [edgeSet_subgraphSUnion hP_le, mem_iUnion₂] at heL
    rcases heL with ⟨_, ⟨w, hw, rfl⟩, hew⟩
    obtain ⟨x', y', hlink_w⟩ := (φV w).exists_isLink_of_mem_edgeSet hew
    have hlink_G : R_G.G.toGraph.IsLink e x' y' := hlink_w.mono (hMod.subgraph_of_mem w hw)
    have hxy_G : R_G.G.toGraph.IsLink e x y := hxyH.mono (hHL.trans (subgraphSUnion_le hP_le))
    have hx_w : x ∈ V(φV w) := by
      rcases hxy_G.left_eq_or_eq hlink_G with rfl | rfl
      · exact hlink_w.left_mem
      · exact hlink_w.right_mem
    have hvw : v = w := by
      by_contra hne
      exact Disjoint.le_bot (hMod.disjoint_V v hv w hw hne).1 ⟨hx_v, hx_w⟩
    subst hvw
    exact hew
  have hComp : H.Compatible (φV v) :=
    Compatible.of_le_le (hHL.trans (subgraphSUnion_le hP_le)) (hMod.subgraph_of_mem v hv)
  exact hComp.ext (Subset.antisymm hle_V hle.vertexSet_mono)
    (Subset.antisymm hle_E hle.edgeSet_mono)

/-- Proof of **Graph Minors XXII, (6.2)** (page 542). -/
theorem gm22_theorem_6_2 : GM22Theorem62Statement.{u, v, u₁, v₁} := by
  intro α β αH βH q R_G R_H φV φE Z L L' hMod hBasis hL_eq hL'_le heff
  classical
  have hcomp_exists : ∀ v ∈ V(R_H.G.toGraph),
      ∃ T : Graph α β, IsGraphComponent T L' ∧ V(T) ∩ Z = V(φV v) ∩ Z := by
    intro v hv
    have hC_L : IsGraphComponent (φV v) L := by
      rw [hL_eq]
      exact hMod.isGraphComponent_φV hv
    obtain ⟨z₀, hz₀Z, hz₀φ⟩ := hBasis.inter_φV_nonempty v hv
    have hmem_eff : V(φV v) ∩ Z ∈ effectOn L Z :=
      ⟨⟨z₀, hz₀φ, hz₀Z⟩, φV v, hC_L, rfl⟩
    rw [← heff] at hmem_eff
    rcases hmem_eff with ⟨_, T, hT, hTZ⟩
    exact ⟨T, hT, hTZ.symm⟩
  let φ'V : αH → Graph α β := fun v =>
    if hv : v ∈ V(R_H.G.toGraph) then Classical.choose (hcomp_exists v hv)
    else ⊥
  have hφ'V_spec : ∀ v (hv : v ∈ V(R_H.G.toGraph)),
      IsGraphComponent (φ'V v) L' ∧ V(φ'V v) ∩ Z = V(φV v) ∩ Z := by
    intro v hv
    simp only [φ'V, hv, ↓reduceDIte]
    exact Classical.choose_spec (hcomp_exists v hv)
  refine ⟨φ'V, fun v hv => hφ'V_spec v hv, ?_⟩
  have hL'_G : L' ≤ R_G.G.toGraph := hL'_le.trans Graph.deleteEdges_le
  refine ⟨?_, ?_, ?_, ?_, hMod.edge_mem, hMod.injOn_E, ?_, ?_, ?_⟩
  · intro v hv
    exact (hφ'V_spec v hv).1.1.trans hL'_G
  · intro v hv
    exact (hφ'V_spec v hv).1.2.1
  · intro v₁ hv₁ v₂ hv₂ hne
    obtain ⟨hC₁, hZ₁⟩ := hφ'V_spec v₁ hv₁
    obtain ⟨hC₂, hZ₂⟩ := hφ'V_spec v₂ hv₂
    have hdisV : Disjoint V(φ'V v₁) V(φ'V v₂) := by
      by_contra hnot_disj
      rw [Set.not_disjoint_iff] at hnot_disj
      rcases hnot_disj with ⟨u, hu₁, hu₂⟩
      have hEq : φ'V v₁ = φ'V v₂ :=
        IsGraphComponent.eq_of_mem_mem hC₁ hC₂ hu₁ hu₂
      obtain ⟨z, hzZ, hz₁⟩ := hBasis.inter_φV_nonempty v₁ hv₁
      have hz_mem₁ : z ∈ V(φV v₁) ∩ Z := ⟨hz₁, hzZ⟩
      rw [← hZ₁, hEq, hZ₂] at hz_mem₁
      exact Disjoint.le_bot (hMod.disjoint_V v₁ hv₁ v₂ hv₂ hne).1 ⟨hz₁, hz_mem₁.1⟩
    refine ⟨hdisV, ?_⟩
    rw [Set.disjoint_left]
    intro e he₁ he₂
    obtain ⟨x, y, hxy₁⟩ := (φ'V v₁).exists_isLink_of_mem_edgeSet he₁
    obtain ⟨x', y', hxy₂⟩ := (φ'V v₂).exists_isLink_of_mem_edgeSet he₂
    have hxy₁_L' : L'.IsLink e x y := hxy₁.mono hC₁.1
    have hxy₂_L' : L'.IsLink e x' y' := hxy₂.mono hC₂.1
    have hx_mem₂ : x ∈ V(φ'V v₂) := by
      rcases hxy₁_L'.left_eq_or_eq hxy₂_L' with rfl | rfl
      · exact hxy₂.left_mem
      · exact hxy₂.right_mem
    exact Disjoint.le_bot hdisV ⟨hxy₁.left_mem, hx_mem₂⟩
  · intro i
    have hri := hMod.root_mem i
    have hriZ := hBasis.roots_mem i
    have hmem : R_G.roots i ∈ V(φV (R_H.roots i)) ∩ Z := ⟨hri, hriZ⟩
    rw [← (hφ'V_spec (R_H.roots i) (R_H.roots_mem i)).2] at hmem
    exact hmem.1
  · intro e he v hv he_mem
    have heL' : φE e ∈ E(L') := (hφ'V_spec v hv).1.1.edgeSet_mono he_mem
    have he_del : φE e ∈ E(R_G.G.toGraph.deleteEdges (φE '' E(R_H.G.toGraph))) :=
      hL'_le.edgeSet_mono heL'
    rw [Graph.edgeSet_deleteEdges] at he_del
    exact he_del.2 ⟨e, he, rfl⟩
  · intro e he
    have hhead := hMod.head_mem e he
    have hheadZ := hBasis.head_mem e he
    have hh_mem : R_G.G.head (φE e) ∈ V(φV (R_H.G.head e)) ∩ Z := ⟨hhead, hheadZ⟩
    have hhV : R_H.G.head e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).right_mem
    rw [← (hφ'V_spec _ hhV).2] at hh_mem
    exact hh_mem.1
  · intro e he
    have htail := hMod.tail_mem e he
    have htailZ := hBasis.tail_mem e he
    have ht_mem : R_G.G.tail (φE e) ∈ V(φV (R_H.G.tail e)) ∩ Z := ⟨htail, htailZ⟩
    have htV : R_H.G.tail e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).left_mem
    rw [← (hφ'V_spec _ htV).2] at ht_mem
    exact ht_mem.1

/-- **Graph Minors XXII, (6.3)** (page 543):
"Suppose that the following hold:
• $(G, u_1, \ldots, u_q)$, $(G', u'_1, \ldots, u'_q)$ and $(H, v_1, \ldots, v_q)$ are rooted digraphs;
• $Z \subseteq V(G)$ with $u_1, \ldots, u_q \in Z$; $\{A_0, A_1, \ldots, A_k\}$ is a $Z$-division of $G$ with $Z \subseteq V(A_0)$, and for $1 \le i \le k$, $\pi_i$ is an ordering of $Z \cap V(A_i)$;
• $Z' \subseteq V(G')$ with $u'_1, \ldots, u'_q \in Z'$; $\{A'_0, A'_1, \ldots, A'_k\}$ is a $Z'$-division of $G'$ with $Z' \subseteq V(A'_0)$; and for $1 \le i \le k$, $\pi'_i$ is an ordering of $Z' \cap V(A'_i)$;
• $\delta \ge 0$ is an integer such that $(H, v_1, \ldots, v_q)$ has detail $\le \delta$, and for $1 \le i \le k$, $(A'_i, \pi'_i)$ has the same $\delta$-folio as $(A_i, \pi_i)$;
• $\alpha \colon Z' \to Z$ is a function mapping $Z'$ onto $Z$ and for $1 \le i \le k$ mapping $\pi'_i$ to $\pi_i$;
• $\phi$ is a model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$ such that $\phi(E(H)) \subseteq E(A_1 \cup \dots \cup A_k)$ and $\phi(v) \cap (A_1 \cup \dots \cup A_k)$ is non-null for each $v \in V(H)$;
• there exists $L'_0 \subseteq A'_0$ such that $u, v \in Z'$ are $L'_0$-connected if and only if $\alpha(u), \alpha(v)$ are $(L \cap A_0)$-connected, where $L \subseteq G$ is minimal such that $Z \subseteq V(L)$ and $\phi(v) \subseteq L$ for each $v \in V(H)$.

*Then there is a model $\phi'$ of $(H, v_1, \ldots, v_q)$ in $(G', u'_1, \ldots, u'_q)$ such that*
$$
\phi'(E(H)) \subseteq E(A'_1 \cup \dots \cup A'_k)
$$
*and $\phi'(v) \cap (A'_1 \cup \dots \cup A'_k)$ is non-null for each $v \in V(H)$.*"

Note: Claim (9) of the proof on page 545 uses $\alpha(u'_j) = u_j$ for $1 \le j \le q$, which is
included explicitly below. -/
def GM22Theorem63Statement : Prop :=
  ∀ {α : Type u} {β : Type v} {α' : Type u₂} {αH : Type u₁} {βH : Type v₁}
    {q k δ : ℕ}
    (R_G : RootedDigraph α β q) (R_G' : RootedDigraph α' β q) (R_H : RootedDigraph αH βH q)
    (Z : Set α) (A : Fin (k + 1) → Graph α β)
    (tLen : Fin k → ℕ) (π : ∀ i : Fin k, Fin (tLen i) → α)
    (Z' : Set α') (A' : Fin (k + 1) → Graph α' β)
    (π' : ∀ i : Fin k, Fin (tLen i) → α')
    (α_map : α' → α)
    (φV : αH → Graph α β) (φE : βH → β)
    (L : Graph α β) (L'₀ : Graph α' β),
    V(R_G.G.toGraph).Finite → E(R_G.G.toGraph).Finite →
    V(R_G'.G.toGraph).Finite → E(R_G'.G.toGraph).Finite →
    Z ⊆ V(R_G.G.toGraph) →
    (∀ j : Fin q, R_G.roots j ∈ Z) →
    IsIndexedZDivision R_G.G.toGraph Z A →
    Z ⊆ V(A 0) →
    (∀ i : Fin k, IsOrderingOf (Z ∩ V(A i.succ)) (π i)) →
    Z' ⊆ V(R_G'.G.toGraph) →
    (∀ j : Fin q, R_G'.roots j ∈ Z') →
    IsIndexedZDivision R_G'.G.toGraph Z' A' →
    Z' ⊆ V(A' 0) →
    (∀ i : Fin k, IsOrderingOf (Z' ∩ V(A' i.succ)) (π' i)) →
    R_H.HasDetailLE δ →
    (∀ (i : Fin k) (hA : A i.succ ≤ R_G.G.toGraph) (hA' : A' i.succ ≤ R_G'.G.toGraph)
      (hπ : ∀ j : Fin (tLen i), π i j ∈ V(A i.succ))
      (hπ' : ∀ j : Fin (tLen i), π' i j ∈ V(A' i.succ)),
      HasSameDeltaFolio
        ⟨R_G.G.ofSubgraph (A i.succ) hA, π i, hπ⟩
        ⟨R_G'.G.ofSubgraph (A' i.succ) hA', π' i, hπ'⟩ δ) →
    α_map '' Z' = Z →
    (∀ j : Fin q, α_map (R_G'.roots j) = R_G.roots j) →
    (∀ i : Fin k, ∀ j : Fin (tLen i), α_map (π' i j) = π i j) →
    IsRootedDigraphModel R_G R_H φV φE →
    φE '' E(R_H.G.toGraph) ⊆ (⋃ i : Fin k, E(A i.succ)) →
    (∀ v ∈ V(R_H.G.toGraph), (V(φV v) ∩ ⋃ i : Fin k, V(A i.succ)).Nonempty) →
    L = graphUnion (Graph.noEdge Z β) (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))) →
    L'₀ ≤ A' 0 →
    (∀ u' ∈ Z', ∀ v' ∈ Z',
      (AreConnectedIn L'₀ u' v' ↔ AreConnectedIn (L ⊓ A 0) (α_map u') (α_map v'))) →
    ∃ (φ'V : αH → Graph α' β) (φ'E : βH → β),
      IsRootedDigraphModel R_G' R_H φ'V φ'E ∧
      φ'E '' E(R_H.G.toGraph) ⊆ (⋃ i : Fin k, E(A' i.succ)) ∧
      ∀ v ∈ V(R_H.G.toGraph), (V(φ'V v) ∩ ⋃ i : Fin k, V(A' i.succ)).Nonempty

end GraphMinor.GM22
