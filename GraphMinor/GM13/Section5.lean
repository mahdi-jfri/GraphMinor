module

public import GraphMinor.GM13.Section5c
public import GraphMinor.GM13.Cited
public import GraphMinor.GM09.Basic

/-!
# Graph Minors XIII, Section 5: Generic Folios (Main Theorems (5.3) and (5.4))

This file completes the formalization of Section 5 of N. Robertson and P. D. Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110 (pages 78–83):

- `theorem_5_3_exists_subgraphs` and `theorem_5_3` ((5.3), pages 79–82)
- `theorem_5_4` ((5.4), page 82)

The results (5.5) and (5.6) of page 83 are in `GraphMinor/GM13/Section5d.lean`, because their
proof uses Thomason's bound, whose small cases depend on Section 6.
-/

@[expose] public section


namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16

universe u v w

variable {α : Type u} {β : Type v}

/-- First assertion of **Graph Minors XIII, (5.3)** (pages 79–80):
existence of `0 ≤ μ ≤ ξ` and `κ = k - ⌊(ξ - μ) / 2⌋` mutually vertex-disjoint non-null connected
subgraphs `H₁, …, H_κ` of `G` satisfying Conditions (a) and (b). -/
theorem theorem_5_3_exists_subgraphs {G : Digraph α β} {Z : Set α} {ξ k : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ)
    (hk : (3 * ξ) / 2 ≤ k)
    {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hi : ∀ i : Fin k, (sub i).IsConnected ∨
      ((sub i).vertexSet.Nonempty ∧
        ∀ u ∈ (sub i).vertexSet, ∃ z ∈ Z ∩ (sub i).vertexSet,
          Nonempty (GraphWalk (sub i).toGraph u z)))
    (hii : ∀ i j : Fin k, i < j →
      (((sub i).vertexSet ∩ Z).Nonempty ∧ ((sub j).vertexSet ∩ Z).Nonempty) ∨
        G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hiii : ∀ (i : Fin k) (A B : Digraph α β),
      G.IsSeparation A B → Z ⊆ A.vertexSet → (G.interSub A (sub i)).IsNull →
      ξ ≤ Digraph.separationOrder A B) :
    ∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
      (∀ i, (H i).IsSubdigraph G) ∧
      (∀ i, (H i).IsConnected) ∧
      Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
      (∀ i : Fin (k - (ξ - μ) / 2),
        (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
        (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
      (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
        ¬ G.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ) := by
  suffices hmain : ∀ (n : ℕ) (G : Digraph α β) (Z : Set α) (ξ k : ℕ) (sub : Fin k → Digraph α β),
      G.vertexSet.ncard + G.edgeSet.ncard = n →
      G.IsFinite → Z ⊆ G.vertexSet → Z.ncard = ξ → (3 * ξ) / 2 ≤ k →
      (∀ i : Fin k, (sub i).IsSubdigraph G) →
      Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet) →
      (∀ i : Fin k, (sub i).IsConnected ∨
        ((sub i).vertexSet.Nonempty ∧
          ∀ u ∈ (sub i).vertexSet, ∃ z ∈ Z ∩ (sub i).vertexSet,
            Nonempty (GraphWalk (sub i).toGraph u z))) →
      (∀ i j : Fin k, i < j →
        (((sub i).vertexSet ∩ Z).Nonempty ∧ ((sub j).vertexSet ∩ Z).Nonempty) ∨
          G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet) →
      (∀ (i : Fin k) (A B : Digraph α β),
        G.IsSeparation A B → Z ⊆ A.vertexSet → (G.interSub A (sub i)).IsNull →
        ξ ≤ Digraph.separationOrder A B) →
      ∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
        (∀ i, (H i).IsSubdigraph G) ∧
        (∀ i, (H i).IsConnected) ∧
        Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
        (∀ i : Fin (k - (ξ - μ) / 2),
          (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
          (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
        (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
          ¬ G.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ) from
    hmain (G.vertexSet.ncard + G.edgeSet.ncard) G Z ξ k sub rfl hfin hZ hZcard hk hsub hdisj hi hii hiii
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G Z ξ k sub hn hfin hZ hZcard hk hsub hdisj hi hii hiii
    by_cases hξ0 : ξ = 0
    · subst hξ0
      have hZemp : Z = ∅ := (ncard_eq_zero (hfin.finite_V.subset hZ)).mp hZcard
      refine ⟨0, le_rfl, sub, hsub, fun i => ?_, hdisj, fun i => ?_, fun i j hlt hno => ?_⟩
      · rcases hi i with hconn | ⟨⟨u, hu⟩, hwalk⟩
        · exact hconn
        · rcases hwalk u hu with ⟨z, hz, _⟩
          rw [hZemp, empty_inter] at hz
          exact False.elim hz
      · refine ⟨fun h => by omega, fun _ => by rw [hZemp, inter_empty]⟩
      · rcases hii i j hlt with ⟨⟨z, hz⟩, _⟩ | hedge
        · rw [hZemp, inter_empty] at hz
          exact False.elim hz
        · exact False.elim (hno hedge)
    · by_cases hξ1k1 : ξ = 1 ∧ k = 1
      · rcases hξ1k1 with ⟨rfl, rfl⟩
        rcases ncard_eq_one.mp hZcard with ⟨z, rfl⟩
        have hzG : z ∈ G.vertexSet := hZ (mem_singleton z)
        refine ⟨1, le_rfl, fun _ => G.singletonSub z,
          fun _ => G.singletonSub_isSubdigraph z,
          fun _ => G.singletonSub_isConnected hzG,
          fun i j hij => False.elim (hij (Fin.ext (by omega))),
          fun i => ⟨fun _ => ?_, fun h => by omega⟩,
          fun i j hlt => False.elim (by omega)⟩
        rw [G.singletonSub_vertexSet hzG, inter_self, ncard_singleton]
      · have hξ_lt_k : ξ < k := by omega
        have hex_i₀ : ∃ i₀ : Fin k, (sub i₀).vertexSet ∩ Z = ∅ := by
          by_contra hall
          push Not at hall
          let f (i : Fin k) : α := Classical.choose (hall i)
          have hf (i : Fin k) : f i ∈ (sub i).vertexSet ∩ Z := Classical.choose_spec (hall i)
          have hfinj : Function.Injective f := by
            intro i j heq
            by_contra hij
            exact Set.disjoint_left.mp (hdisj hij) (hf i).1 (heq ▸ (hf j).1)
          have hfrange : Set.range f ⊆ Z := by
            rintro _ ⟨i, rfl⟩; exact (hf i).2
          have hle : k ≤ ξ := by
            have h1 := ncard_le_ncard hfrange (hfin.finite_V.subset hZ)
            rw [ncard_range_of_injective hfinj, Nat.card_fin, hZcard] at h1
            exact h1
          omega
        rcases hex_i₀ with ⟨i₀, hi₀⟩
        by_cases hloop : ∃ e₀ ∈ G.edgeSet, G.head e₀ = G.tail e₀
        · rcases hloop with ⟨e₀, he₀, hht⟩
          refine theorem_5_3_step_loop hsub hdisj hi hii hiii e₀ he₀ hht ?_
          intro G' sub' hG'V hG'E hG'sub hsub' hdisj' hi' hii' hiii'
          have hfin' : G'.IsFinite :=
            ⟨hfin.finite_V.subset hG'sub.vertexSet_subset, hfin.finite_E.subset hG'sub.edgeSet_subset⟩
          have hZ' : Z ⊆ G'.vertexSet := hG'V.symm ▸ hZ
          have hlt : G'.vertexSet.ncard + G'.edgeSet.ncard < n := by
            rw [← hn, hG'V, hG'E, ncard_sdiff_singleton_of_mem he₀]
            have hpos : 0 < G.edgeSet.ncard := (ncard_pos hfin.finite_E).mpr ⟨e₀, he₀⟩
            omega
          exact ih _ hlt G' Z ξ k sub' rfl hfin' hZ' hZcard hk hsub' hdisj' hi' hii' hiii'
        · push Not at hloop
          by_cases hsep_ex : ∃ (i₁ : Fin k) (A B : Digraph α β),
              G.IsSeparation A B ∧ Z ⊆ A.vertexSet ∧ (G.interSub A (sub i₁)).IsNull ∧
              Digraph.separationOrder A B ≤ ξ ∧
              ¬ (A.vertexSet \ B.vertexSet = ∅ ∧ A.edgeSet = ∅)
          · rcases hsep_ex with ⟨i₁, A, B, hsep, hZA, hnull, hord, hnot_triv⟩
            refine theorem_5_3_step_sep hfin hZ hZcard hsub hdisj hi hii hiii
              i₁ A B hsep hZA hnull hord ?_
            intro Z' sub' hfin' hZ' hZ'card hsub' hdisj' hi' hii' hiii'
            have hBV_le : B.vertexSet.ncard ≤ G.vertexSet.ncard :=
              ncard_le_ncard hsep.sub_right.vertexSet_subset hfin.finite_V
            have hBE_le : B.edgeSet.ncard ≤ G.edgeSet.ncard :=
              ncard_le_ncard hsep.sub_right.edgeSet_subset hfin.finite_E
            have hlt : B.vertexSet.ncard + B.edgeSet.ncard < n := by
              rw [← hn]
              by_cases hAV : A.vertexSet \ B.vertexSet = ∅
              · have hAE : A.edgeSet ≠ ∅ := fun h => hnot_triv ⟨hAV, h⟩
                rcases nonempty_iff_ne_empty.mpr hAE with ⟨e, heA⟩
                have heG : e ∈ G.edgeSet := hsep.sub_left.edgeSet_subset heA
                have heNotB : e ∉ B.edgeSet := Set.disjoint_left.mp hsep.edgeSet_disjoint heA
                have hBE_lt : B.edgeSet.ncard < G.edgeSet.ncard :=
                  ncard_lt_ncard ⟨hsep.sub_right.edgeSet_subset, fun h => heNotB (h heG)⟩ hfin.finite_E
                omega
              · rcases nonempty_iff_ne_empty.mpr hAV with ⟨x, hxA, hxNotB⟩
                have hxG : x ∈ G.vertexSet := hsep.sub_left.vertexSet_subset hxA
                have hBV_lt : B.vertexSet.ncard < G.vertexSet.ncard :=
                  ncard_lt_ncard ⟨hsep.sub_right.vertexSet_subset, fun h => hxNotB (h hxG)⟩ hfin.finite_V
                omega
            exact ih _ hlt B Z' ξ k sub' rfl hfin' hZ' hZ'card hk hsub' hdisj' hi' hii' hiii'
          · push Not at hsep_ex
            by_cases hedge_not_between : ∃ e₀ ∈ G.edgeSet,
                ¬ ∃ i j : Fin k, i ≠ j ∧
                  G.head e₀ ∈ (sub i).vertexSet ∧ G.tail e₀ ∈ (sub j).vertexSet
            · rcases hedge_not_between with ⟨e₀, he₀, hnot_between⟩
              refine theorem_5_3_step_contract hfin hZ hZcard hsub hdisj hi hii hiii
                i₀ hi₀ hsep_ex e₀ he₀ (hloop e₀ he₀) hnot_between ?_
              intro u v hv hne hu huNotZ G' sub' hfin' hZ' hsub' hdisj' hi' hii' hiii'
              have hlt : G'.vertexSet.ncard + G'.edgeSet.ncard < n := by
                rw [← hn]
                dsimp [G', Digraph.contractEdge]
                have hV_le : (G.vertexSet \ {u}).ncard ≤ G.vertexSet.ncard :=
                  ncard_le_ncard sdiff_subset hfin.finite_V
                have hE_lt : (G.edgeSet \ {e₀}).ncard < G.edgeSet.ncard :=
                  ncard_lt_ncard ⟨sdiff_subset, fun h => (h he₀).2 rfl⟩ hfin.finite_E
                omega
              exact ih _ hlt G' Z ξ k sub'
                rfl hfin' hZ' hZcard hk hsub' hdisj' hi' hii' hiii'
            · push Not at hedge_not_between
              exact theorem_5_3_base_no_other_edges hfin hZ hZcard hk hsub hdisj hi hii hiii
                i₀ hi₀ hedge_not_between

/-- **Graph Minors XIII, (5.3)** (pages 79–80):
"*Let $G$ be a graph and let $Z \subseteq V(G)$ with $|Z| = \xi$. Let $k \ge \lfloor
\frac{3}{2}\xi \rfloor$ and let $G_1, \dots, G_k$ be subgraphs of $G$, mutually vertex-disjoint,
such that*

(i) *for $1 \le i \le k$, either $G_i$ is connected or every component of $G_i$ has a vertex in
$Z$,*

(ii) *for $1 \le i < j \le k$, either $V(G_i)$ and $V(G_j)$ both meet $Z$ or there is an edge of
$G$ between $G_i$ and $G_j$, and*

(iii) *for $1 \le i \le k$, there is no separation $(A, B)$ of $G$ of order $< \xi$ with $Z
\subseteq V(A)$ and with $A \cap G_i$ null.*

*Then for some $\mu$ with $0 \le \mu \le \xi$ there are $\kappa = k - \lfloor \frac{1}{2}(\xi -
\mu) \rfloor$ non-null connected subgraphs $H_1, \dots, H_\kappa$ of $G$, mutually
vertex-disjoint, such that*

(a) *$|V(H_i) \cap Z| = 1$ ($1 \le i \le \xi$) and $V(H_i) \cap Z = \emptyset$ ($\xi + 1 \le i
\le \kappa$), and*

(b) *for $1 \le i < j \le \kappa$, if there is no edge of $G$ between $H_i$ and $H_j$ then $i, j
\le \mu$.*

*In particular, for any $\delta \ge 0$, if $k \ge \lfloor \frac{5}{2}\xi \rfloor + 3\delta$ and
$G$ is a digraph then the $\delta$-folio of $G$ relative to $Z$ is generic.*"

Here `G` is a digraph from the start, as the second assertion needs. The first assertion only
uses its underlying graph: connectivity, edges between subgraphs and separations ignore the
directions. -/
theorem theorem_5_3_proof [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ k : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ)
    (hk : (3 * ξ) / 2 ≤ k)
    {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hi : ∀ i : Fin k, (sub i).IsConnected ∨
      ((sub i).vertexSet.Nonempty ∧
        ∀ u ∈ (sub i).vertexSet, ∃ z ∈ Z ∩ (sub i).vertexSet,
          Nonempty (GraphWalk (sub i).toGraph u z)))
    (hii : ∀ i j : Fin k, i < j →
      (((sub i).vertexSet ∩ Z).Nonempty ∧ ((sub j).vertexSet ∩ Z).Nonempty) ∨
        G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hiii : ∀ (i : Fin k) (A B : Digraph α β),
      G.IsSeparation A B → Z ⊆ A.vertexSet → (G.interSub A (sub i)).IsNull →
      ξ ≤ Digraph.separationOrder A B) :
    (∃ (μ : ℕ) (_ : μ ≤ ξ) (H : Fin (k - (ξ - μ) / 2) → Digraph α β),
      (∀ i, (H i).IsSubdigraph G) ∧
      (∀ i, (H i).IsConnected) ∧
      Pairwise (fun i j => Disjoint (H i).vertexSet (H j).vertexSet) ∧
      (∀ i : Fin (k - (ξ - μ) / 2),
        (i.1 < ξ → ((H i).vertexSet ∩ Z).ncard = 1) ∧
        (ξ ≤ i.1 → (H i).vertexSet ∩ Z = ∅)) ∧
      (∀ i j : Fin (k - (ξ - μ) / 2), i < j →
        ¬ G.HasEdgeBetween (H i).vertexSet (H j).vertexSet → i.1 < μ ∧ j.1 < μ)) ∧
    (∀ δ : ℕ, (5 * ξ) / 2 + 3 * δ ≤ k → IsGenericDeltaFolioRel G δ Z) := by
  have hex := theorem_5_3_exists_subgraphs hfin hZ hZcard hk hsub hdisj hi hii hiii
  refine ⟨hex, fun δ hk_delta => ?_⟩
  rcases hex with ⟨μ, hμ, H, hH_sub, hH_conn, hH_disj, hH_a, hH_b⟩
  have hdiv_le : (ξ - μ) / 2 ≤ ξ / 2 := Nat.div_le_div_right (Nat.sub_le ξ μ)
  have h5_eq : 2 * ξ + ξ / 2 = (5 * ξ) / 2 := by omega
  have hκ_ge : 2 * ξ + 3 * δ ≤ k - (ξ - μ) / 2 := by omega
  let H₀ (i : Fin (2 * ξ + 3 * δ)) : Digraph α β := H ⟨i.1, lt_of_lt_of_le i.2 hκ_ge⟩
  refine theorem_5_2_proof hZ (hfin.finite_V.subset hZ) hZcard rfl
    (sub := H₀)
    (fun i => hH_sub _)
    (fun i => hH_conn _)
    (fun i j hij => hH_disj (fun h => hij (Fin.ext (Fin.mk.inj_iff.mp h))))
    (fun i hi_lt => by rw [inter_comm]; exact (hH_a _).1 hi_lt)
    (fun i hi_ge => by rw [inter_comm]; exact (hH_a _).2 hi_ge)
    (fun i j hlt hno => ?_)
  have h := hH_b ⟨i.1, lt_of_lt_of_le i.2 hκ_ge⟩ ⟨j.1, lt_of_lt_of_le j.2 hκ_ge⟩ hlt hno
  exact ⟨lt_of_lt_of_le h.1 hμ, lt_of_lt_of_le h.2 hμ⟩

/-- Helper for `(5.4)`: if `J` is a set of indices and `i₀ ∈ J` has an edge of `G` between
`H i₀` and `H j` for every `j ∈ J` with `j ≠ i₀`, where each `H j` (`j ∈ J`) is a connected
subdigraph of `G`, then `G.induce (⋃ j ∈ J, (H j).vertexSet)` is connected. -/
lemma isConnected_induce_biUnion_of_star {κ : ℕ} {G : Digraph α β}
    {H : Fin κ → Digraph α β}
    (hH_sub : ∀ j, (H j).IsSubdigraph G)
    (hH_conn : ∀ j, (H j).IsConnected)
    {J : Set (Fin κ)} {i₀ : Fin κ} (hi₀ : i₀ ∈ J)
    (hstar : ∀ j ∈ J, j ≠ i₀ → G.HasEdgeBetween (H i₀).vertexSet (H j).vertexSet) :
    (G.induce (⋃ j ∈ J, (H j).vertexSet)).IsConnected := by
  let U : Set α := ⋃ j ∈ J, (H j).vertexSet
  have hU_sub : U ⊆ G.vertexSet :=
    iUnion₂_subset (fun j _ => (hH_sub j).vertexSet_subset)
  have hV_ind : (G.induce U).vertexSet = U :=
    inter_eq_self_of_subset_right hU_sub
  have hHj_sub_ind (j : Fin κ) (hj : j ∈ J) : (H j).IsSubdigraph (G.induce U) := {
    vertexSet_subset := fun x hx => ⟨(hH_sub j).vertexSet_subset hx, mem_biUnion hj hx⟩
    edgeSet_subset := fun e he => ⟨(hH_sub j).edgeSet_subset he,
      mem_biUnion hj ((hH_sub j).head_eq he ▸ (H j).head_mem he),
      mem_biUnion hj ((hH_sub j).tail_eq he ▸ (H j).tail_mem he)⟩
    head_eq := fun e he => (hH_sub j).head_eq he
    tail_eq := fun e he => (hH_sub j).tail_eq he
  }
  rcases (hH_conn i₀).1 with ⟨v₀, hv₀⟩
  have hv₀_ind : v₀ ∈ (G.induce U).vertexSet :=
    (hHj_sub_ind i₀ hi₀).vertexSet_subset hv₀
  have hwalk_to_v₀ : ∀ x ∈ (G.induce U).vertexSet,
      Nonempty (GraphWalk (G.induce U).toGraph x v₀) := by
    intro x hx
    rw [hV_ind, mem_iUnion₂] at hx
    rcases hx with ⟨j, hj, hxj⟩
    by_cases hji₀ : j = i₀
    · subst hji₀
      rcases (hH_conn j).2 x hxj v₀ hv₀ with ⟨W⟩
      exact ⟨(hHj_sub_ind j hj).mapWalk W⟩
    · rcases hstar j hj hji₀ with ⟨e, heG, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · -- `G.head e ∈ H i₀`, `G.tail e ∈ H j`
        rcases (hH_conn j).2 x hxj (G.tail e) h2 with ⟨W₁⟩
        rcases (hH_conn i₀).2 (G.head e) h1 v₀ hv₀ with ⟨W₂⟩
        have he_ind : e ∈ (G.induce U).edgeSet :=
          ⟨heG, mem_biUnion hi₀ h1, mem_biUnion hj h2⟩
        have hlink : (G.induce U).toGraph.IsLink e (G.tail e) (G.head e) :=
          ⟨he_ind, Or.inr ⟨rfl, rfl⟩⟩
        exact ⟨GraphWalk.append ((hHj_sub_ind j hj).mapWalk W₁)
          (.cons hlink ((hHj_sub_ind i₀ hi₀).mapWalk W₂))⟩
      · -- `G.head e ∈ H j`, `G.tail e ∈ H i₀`
        rcases (hH_conn j).2 x hxj (G.head e) h1 with ⟨W₁⟩
        rcases (hH_conn i₀).2 (G.tail e) h2 v₀ hv₀ with ⟨W₂⟩
        have he_ind : e ∈ (G.induce U).edgeSet :=
          ⟨heG, mem_biUnion hj h1, mem_biUnion hi₀ h2⟩
        have hlink : (G.induce U).toGraph.IsLink e (G.head e) (G.tail e) :=
          ⟨he_ind, Or.inl ⟨rfl, rfl⟩⟩
        exact ⟨GraphWalk.append ((hHj_sub_ind j hj).mapWalk W₁)
          (.cons hlink ((hHj_sub_ind i₀ hi₀).mapWalk W₂))⟩
  refine ⟨⟨v₀, hv₀_ind⟩, fun x hx y hy => ?_⟩
  rcases hwalk_to_v₀ x hx with ⟨Wx⟩
  rcases hwalk_to_v₀ y hy with ⟨Wy⟩
  exact ⟨GraphWalk.append Wx (GraphWalk.reverse Wy)⟩

/-- **Graph Minors XIII, (5.4)** (page 82):
"Let $G$ be a graph and let $Z \subseteq V(G)$ with $|Z| = \xi$. Let $k \ge \lfloor \frac{3}{2}\xi \rfloor$ and let $G_1, \dots, G_k$ be connected subgraphs of $G$, mutually vertex-disjoint, such that for $1 \le i < j \le k$ there is an edge of $G$ between $G_i$ and $G_j$. Suppose that there is no separation $(A, B)$ of $G$ of order $< |Z|$ with $Z \subseteq V(A)$ and $A \cap G_i$ null for some $i$ ($1 \le i \le k$). Then for every partition $(Z_1, \dots, Z_n)$ of $Z$ into non-empty subsets, there are $n$ connected subgraphs $T_1, \dots, T_n$ of $G$, mutually disjoint and with $V(T_t) \cap Z = Z_t$ ($1 \le t \le n$)." -/
theorem theorem_5_4_proof {G : Digraph α β} {Z : Set α} {ξ k n : ℕ}
    (hfin : G.IsFinite)
    (hZ : Z ⊆ G.vertexSet) (hZcard : Z.ncard = ξ)
    (hk : (3 * ξ) / 2 ≤ k)
    {sub : Fin k → Digraph α β}
    (hsub : ∀ i : Fin k, (sub i).IsSubdigraph G)
    (hconn : ∀ i : Fin k, (sub i).IsConnected)
    (hdisj : Pairwise (fun i j : Fin k => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hadj : ∀ i j : Fin k, i < j → G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet)
    (hno_sep : ∀ (i : Fin k) (A B : Digraph α β),
      G.IsSeparation A B → Z ⊆ A.vertexSet → (G.interSub A (sub i)).IsNull →
      ξ ≤ Digraph.separationOrder A B)
    (Z_part : Fin n → Set α)
    (hZ_nonempty : ∀ t : Fin n, (Z_part t).Nonempty)
    (hZ_disj : Pairwise (fun t₁ t₂ : Fin n => Disjoint (Z_part t₁) (Z_part t₂)))
    (hZ_union : (⋃ t : Fin n, Z_part t) = Z) :
    ∃ T : Fin n → Digraph α β,
      (∀ t : Fin n, (T t).IsSubdigraph G) ∧
      (∀ t : Fin n, (T t).IsConnected) ∧
      Pairwise (fun t₁ t₂ : Fin n => Disjoint (T t₁).vertexSet (T t₂).vertexSet) ∧
      (∀ t : Fin n, (T t).vertexSet ∩ Z = Z_part t) := by
  have hZfin : Z.Finite := hfin.finite_V.subset hZ
  have hZpart_sub (t : Fin n) : Z_part t ⊆ Z :=
    hZ_union ▸ subset_iUnion Z_part t
  obtain ⟨μ, hμ, H, hH_sub, hH_conn, hH_disj, hH_a, hH_b⟩ :=
    theorem_5_3_exists_subgraphs hfin hZ hZcard hk hsub hdisj
      (fun i => Or.inl (hconn i))
      (fun i j hlt => Or.inr (hadj i j hlt))
      hno_sep
  let κ : ℕ := k - (ξ - μ) / 2
  have hξ_le_κ : ξ ≤ κ := by omega
  -- For each `r : Fin ξ`, `(H ⟨r.1, _⟩).vertexSet ∩ Z` is a singleton `{zOf r}`
  have hex_z (r : Fin ξ) : ∃ z : α, (H ⟨r.1, lt_of_lt_of_le r.2 hξ_le_κ⟩).vertexSet ∩ Z = {z} :=
    ncard_eq_one.mp ((hH_a ⟨r.1, lt_of_lt_of_le r.2 hξ_le_κ⟩).1 r.2)
  let zOf (r : Fin ξ) : α := Classical.choose (hex_z r)
  have hzOf_spec (r : Fin ξ) :
      (H ⟨r.1, lt_of_lt_of_le r.2 hξ_le_κ⟩).vertexSet ∩ Z = {zOf r} :=
    Classical.choose_spec (hex_z r)
  have hzOf_mem (r : Fin ξ) :
      zOf r ∈ (H ⟨r.1, lt_of_lt_of_le r.2 hξ_le_κ⟩).vertexSet ∩ Z := by
    rw [hzOf_spec r]; exact mem_singleton _
  have hzOf_inj : Function.Injective zOf := by
    intro r₁ r₂ heq
    by_contra hne
    have hne' : (⟨r₁.1, lt_of_lt_of_le r₁.2 hξ_le_κ⟩ : Fin κ) ≠ ⟨r₂.1, lt_of_lt_of_le r₂.2 hξ_le_κ⟩ :=
      fun h => hne (Fin.ext (Fin.mk.inj_iff.mp h))
    exact Set.disjoint_left.mp (hH_disj hne') (hzOf_mem r₁).1 (heq ▸ (hzOf_mem r₂).1)
  have hrange_zOf : Set.range zOf = Z := by
    apply eq_of_subset_of_ncard_le
    · rintro _ ⟨r, rfl⟩; exact (hzOf_mem r).2
    · rw [ncard_range_of_injective hzOf_inj, Nat.card_fin, hZcard]
    · exact hZfin
  -- Define `I_t t := {i : Fin κ | ((H i).vertexSet ∩ Z_part t).Nonempty}`
  let I_t (t : Fin n) : Set (Fin κ) := {i : Fin κ | ((H i).vertexSet ∩ Z_part t).Nonempty}
  have hI_lt_ξ (t : Fin n) {i : Fin κ} (hi : i ∈ I_t t) : i.1 < ξ := by
    by_contra hge
    have hemp := (hH_a i).2 (by omega)
    rcases hi with ⟨x, hxH, hxZt⟩
    have hx : x ∈ (H i).vertexSet ∩ Z := ⟨hxH, hZpart_sub t hxZt⟩
    rw [hemp] at hx; exact hx
  have hI_singleton (t : Fin n) {i : Fin κ} (hi : i ∈ I_t t) :
      ∃ z ∈ Z_part t, (H i).vertexSet ∩ Z = {z} := by
    have hlt := hI_lt_ξ t hi
    rcases ncard_eq_one.mp ((hH_a i).1 hlt) with ⟨z, hz⟩
    rcases hi with ⟨x, hxH, hxZt⟩
    have hx : x ∈ (H i).vertexSet ∩ Z := ⟨hxH, hZpart_sub t hxZt⟩
    rw [hz, mem_singleton_iff] at hx
    exact ⟨z, hx ▸ hxZt, hz⟩
  have hI_nonempty (t : Fin n) : (I_t t).Nonempty := by
    rcases hZ_nonempty t with ⟨z, hzZt⟩
    have hzZ : z ∈ Z := hZpart_sub t hzZt
    rw [← hrange_zOf] at hzZ
    rcases hzZ with ⟨r, rfl⟩
    exact ⟨⟨r.1, lt_of_lt_of_le r.2 hξ_le_κ⟩, zOf r, (hzOf_mem r).1, hzZt⟩
  have hI_disj : Pairwise (fun t₁ t₂ : Fin n => Disjoint (I_t t₁) (I_t t₂)) := by
    intro t₁ t₂ hne
    rw [Set.disjoint_iff]
    rintro i ⟨hi₁, hi₂⟩
    rcases hI_singleton t₁ hi₁ with ⟨z₁, hz₁, h1⟩
    rcases hI_singleton t₂ hi₂ with ⟨z₂, hz₂, h2⟩
    have heq : z₁ = z₂ := singleton_eq_singleton_iff.mp (h1.symm.trans h2)
    exact Set.disjoint_left.mp (hZ_disj hne) hz₁ (heq ▸ hz₂)
  -- Define `B_set` (those `t` for which `I_t t ⊆ {i | i.1 < μ}` and `2 ≤ (I_t t).ncard`)
  let B_set : Set (Fin n) := {t : Fin n | (∀ i ∈ I_t t, i.1 < μ) ∧ 2 ≤ (I_t t).ncard}
  let E_idx : Set (Fin κ) := {i : Fin κ | ξ ≤ i.1}
  have hB_le_E : B_set.ncard ≤ E_idx.ncard := by
    -- Each `t ∈ B_set` has `I_t t ⊆ {i : Fin κ | i.1 < μ}` and `2 ≤ (I_t t).ncard`.
    let M_idx : Set (Fin κ) := {i : Fin κ | i.1 < μ}
    have hM_card : M_idx.ncard = μ := by
      have hbij : BijOn (fun r : Fin μ => (⟨r.1, by omega⟩ : Fin κ)) Set.univ M_idx := by
        refine ⟨fun r _ => r.2, fun r₁ _ r₂ _ h => Fin.ext (Fin.mk.inj_iff.mp h), ?_⟩
        intro i hi
        exact ⟨⟨i.1, hi⟩, mem_univ _, rfl⟩
      rw [← hbij.ncard_eq, ncard_univ, Nat.card_fin]
    have hE_card : E_idx.ncard = κ - ξ := by
      have hbij : BijOn (fun r : Fin (κ - ξ) => (⟨ξ + r.1, by omega⟩ : Fin κ)) Set.univ E_idx := by
        refine ⟨fun r _ => by dsimp [E_idx]; omega,
          fun r₁ _ r₂ _ h => Fin.ext (by have := Fin.mk.inj_iff.mp h; omega), ?_⟩
        intro i hi
        dsimp [E_idx] at hi
        exact ⟨⟨i.1 - ξ, by omega⟩, mem_univ _, Fin.ext (by dsimp; omega)⟩
      rw [← hbij.ncard_eq, ncard_univ, Nat.card_fin]
    -- `2 * B_set.ncard ≤ M_idx.ncard = μ`:
    -- Pick two distinct elements `p₁ t, p₂ t ∈ I_t t` for each `t ∈ B_set`.
    have hex_pair (t : B_set) : ∃ i₁ i₂ : Fin κ, i₁ ∈ I_t t.1 ∧ i₂ ∈ I_t t.1 ∧ i₁ ≠ i₂ := by
      have h2 := t.2.2
      exact (one_lt_ncard_iff (Set.toFinite _)).mp (by omega)
    let p₁ (t : B_set) : Fin κ := Classical.choose (hex_pair t)
    let p₂ (t : B_set) : Fin κ := Classical.choose (Classical.choose_spec (hex_pair t))
    have hp (t : B_set) : p₁ t ∈ I_t t.1 ∧ p₂ t ∈ I_t t.1 ∧ p₁ t ≠ p₂ t :=
      Classical.choose_spec (Classical.choose_spec (hex_pair t))
    let g : B_set × Bool → M_idx := fun ⟨t, b⟩ =>
      if b then ⟨p₁ t, t.2.1 (p₁ t) (hp t).1⟩ else ⟨p₂ t, t.2.1 (p₂ t) (hp t).2.1⟩
    have hg_inj : Function.Injective g := by
      rintro ⟨t₁, b₁⟩ ⟨t₂, b₂⟩ heq
      have hval : (g ⟨t₁, b₁⟩).1 = (g ⟨t₂, b₂⟩).1 := congrArg Subtype.val heq
      have hmem₁ : (g ⟨t₁, b₁⟩).1 ∈ I_t t₁.1 := by cases b₁ <;> [exact (hp t₁).2.1; exact (hp t₁).1]
      have hmem₂ : (g ⟨t₂, b₂⟩).1 ∈ I_t t₂.1 := by cases b₂ <;> [exact (hp t₂).2.1; exact (hp t₂).1]
      have ht_eq : t₁ = t₂ := by
        by_contra hne
        have hne' : t₁.1 ≠ t₂.1 := fun h => hne (Subtype.ext h)
        exact Set.disjoint_left.mp (hI_disj hne') hmem₁ (hval ▸ hmem₂)
      subst ht_eq
      cases b₁ <;> cases b₂
      · rfl
      · exact False.elim ((hp t₁).2.2 hval.symm)
      · exact False.elim ((hp t₁).2.2 hval)
      · rfl
    have hcard_le : Fintype.card (B_set × Bool) ≤ Fintype.card M_idx :=
      Fintype.card_le_of_injective g hg_inj
    have hB_card_eq : Fintype.card B_set = B_set.ncard :=
      (Nat.card_eq_fintype_card).symm.trans (ncard_def B_set).symm
    have hM_card_eq : Fintype.card M_idx = M_idx.ncard :=
      (Nat.card_eq_fintype_card).symm.trans (ncard_def M_idx).symm
    rw [Fintype.card_prod, Fintype.card_bool, hB_card_eq, hM_card_eq, hM_card] at hcard_le
    rw [hE_card]
    omega
  -- Obtain an injection `f : B_set → E_idx`
  have hcard_BE : Fintype.card B_set ≤ Fintype.card E_idx := by
    have h1 : Fintype.card B_set = B_set.ncard :=
      (Nat.card_eq_fintype_card).symm.trans (ncard_def B_set).symm
    have h2 : Fintype.card E_idx = E_idx.ncard :=
      (Nat.card_eq_fintype_card).symm.trans (ncard_def E_idx).symm
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard_BE
  -- Define `J_t t : Set (Fin κ)` for each `t : Fin n`
  let J_t (t : Fin n) : Set (Fin κ) :=
    if ht : t ∈ B_set then insert (f ⟨t, ht⟩).1 (I_t t) else I_t t
  let T (t : Fin n) : Digraph α β :=
    G.induce (⋃ j ∈ J_t t, (H j).vertexSet)
  have hTV (t : Fin n) : (T t).vertexSet = ⋃ j ∈ J_t t, (H j).vertexSet :=
    inter_eq_self_of_subset_right (iUnion₂_subset (fun j _ => (hH_sub j).vertexSet_subset))
  have hJ_disj : Pairwise (fun t₁ t₂ : Fin n => Disjoint (J_t t₁) (J_t t₂)) := by
    intro t₁ t₂ hne
    rw [Set.disjoint_iff]
    rintro i ⟨hi₁, hi₂⟩
    dsimp [J_t] at hi₁ hi₂
    split_ifs at hi₁ with ht₁ <;> split_ifs at hi₂ with ht₂
    · rcases hi₁ with rfl | hi₁ <;> rcases hi₂ with h | hi₂
      · exact hne (Subtype.mk.inj (f.injective (Subtype.ext h)))
      · have hlt := hI_lt_ξ t₂ hi₂
        have hge : ξ ≤ (f ⟨t₁, ht₁⟩).1.1 := (f ⟨t₁, ht₁⟩).2
        omega
      · have hlt := hI_lt_ξ t₁ hi₁
        have hge : ξ ≤ (f ⟨t₂, ht₂⟩).1.1 := (f ⟨t₂, ht₂⟩).2
        omega
      · exact Set.disjoint_left.mp (hI_disj hne) hi₁ hi₂
    · rcases hi₁ with rfl | hi₁
      · have hlt := hI_lt_ξ t₂ hi₂
        have hge : ξ ≤ (f ⟨t₁, ht₁⟩).1.1 := (f ⟨t₁, ht₁⟩).2
        omega
      · exact Set.disjoint_left.mp (hI_disj hne) hi₁ hi₂
    · rcases hi₂ with rfl | hi₂
      · have hlt := hI_lt_ξ t₁ hi₁
        have hge : ξ ≤ (f ⟨t₂, ht₂⟩).1.1 := (f ⟨t₂, ht₂⟩).2
        omega
      · exact Set.disjoint_left.mp (hI_disj hne) hi₁ hi₂
    · exact Set.disjoint_left.mp (hI_disj hne) hi₁ hi₂
  have hedge_of_ge_μ {i₀ j : Fin κ} (hi₀_ge : μ ≤ i₀.1) (hne : j ≠ i₀) :
      G.HasEdgeBetween (H i₀).vertexSet (H j).vertexSet := by
    by_contra hno
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hno' : ¬ G.HasEdgeBetween (H j).vertexSet (H i₀).vertexSet := by
        rintro ⟨e, he, h⟩; exact hno ⟨e, he, h.symm⟩
      have h := hH_b j i₀ hlt hno'
      omega
    · have h := hH_b i₀ j hgt hno
      omega
  refine ⟨T, fun t => G.induce_isSubdigraph _, fun t => ?_, ?_, fun t => ?_⟩
  · -- `(T t).IsConnected`
    dsimp [T, J_t]
    split_ifs with ht
    · apply isConnected_induce_biUnion_of_star hH_sub hH_conn (mem_insert _ _)
      intro j hj hne
      have hi₀_ge : μ ≤ (f ⟨t, ht⟩).1.1 := le_trans hμ (f ⟨t, ht⟩).2
      exact hedge_of_ge_μ hi₀_ge hne
    · by_cases hall_lt : ∀ i ∈ I_t t, i.1 < μ
      · have hcard_lt : (I_t t).ncard < 2 := by
          by_contra hge
          exact ht ⟨hall_lt, not_lt.mp hge⟩
        rcases hI_nonempty t with ⟨i₀, hi₀⟩
        apply isConnected_induce_biUnion_of_star hH_sub hH_conn hi₀
        intro j hj hne
        have hsub_pair : ({j, i₀} : Set (Fin κ)) ⊆ I_t t := by
          rintro x (rfl | rfl) <;> assumption
        have hpair_le : ({j, i₀} : Set (Fin κ)).ncard ≤ (I_t t).ncard :=
          ncard_le_ncard hsub_pair (Set.toFinite _)
        rw [ncard_pair hne] at hpair_le
        omega
      · push Not at hall_lt
        rcases hall_lt with ⟨i₀, hi₀, hi₀_ge⟩
        apply isConnected_induce_biUnion_of_star hH_sub hH_conn hi₀
        intro j _ hne
        exact hedge_of_ge_μ hi₀_ge hne
  · -- Pairwise disjoint `T t`
    intro t₁ t₂ hne
    rw [hTV, hTV, Set.disjoint_iff]
    rintro x ⟨h1, h2⟩
    rw [mem_iUnion₂] at h1 h2
    rcases h1 with ⟨i₁, hi₁, hx₁⟩
    rcases h2 with ⟨i₂, hi₂, hx₂⟩
    have hi_eq : i₁ = i₂ := by
      by_contra hij
      exact Set.disjoint_left.mp (hH_disj hij) hx₁ hx₂
    subst hi_eq
    exact Set.disjoint_left.mp (hJ_disj hne) hi₁ hi₂
  · -- `(T t).vertexSet ∩ Z = Z_part t`
    rw [hTV]
    ext x
    simp only [mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨⟨i, hiJ, hxi⟩, hxZ⟩
      have hiI : i ∈ I_t t := by
        dsimp [J_t] at hiJ
        split_ifs at hiJ with ht
        · rcases hiJ with rfl | hiI
          · have hge : ξ ≤ (f ⟨t, ht⟩).1.1 := (f ⟨t, ht⟩).2
            have hemp := (hH_a (f ⟨t, ht⟩).1).2 hge
            have hx_mem : x ∈ (H (f ⟨t, ht⟩).1).vertexSet ∩ Z := ⟨hxi, hxZ⟩
            rw [hemp] at hx_mem; exact False.elim hx_mem
          · exact hiI
        · exact hiJ
      rcases hI_singleton t hiI with ⟨z, hzZt, hz_eq⟩
      have hx_mem : x ∈ (H i).vertexSet ∩ Z := ⟨hxi, hxZ⟩
      rw [hz_eq, mem_singleton_iff] at hx_mem
      exact hx_mem ▸ hzZt
    · intro hxZt
      have hxZ : x ∈ Z := hZpart_sub t hxZt
      have hx_range : x ∈ Set.range zOf := hrange_zOf.symm ▸ hxZ
      rcases hx_range with ⟨r, rfl⟩
      let i : Fin κ := ⟨r.1, lt_of_lt_of_le r.2 hξ_le_κ⟩
      have hiI : i ∈ I_t t := ⟨zOf r, (hzOf_mem r).1, hxZt⟩
      have hiJ : i ∈ J_t t := by
        dsimp [J_t]
        split_ifs
        · exact mem_insert_of_mem _ hiI
        · exact hiI
      exact ⟨⟨i, hiJ, (hzOf_mem r).1⟩, hxZ⟩

end GraphMinor.GM13
