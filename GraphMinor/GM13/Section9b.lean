module

public import GraphMinor.Surface.DrawCarry
public import GraphMinor.GM07.Bridge
public import GraphMinor.GM07.CuffSlide
public import GraphMinor.GM07.Section7
public import GraphMinor.GM12.Bridge
public import GraphMinor.GM12.Section4Theorem45
public import GraphMinor.GM13.Section7
public import GraphMinor.GM13.Section7FourProof
import GraphMinor.GM13.Section7Six
import GraphMinor.GM13.Section7ThreeAll
public import GraphMinor.GM13.Section9a
public import GraphMinor.GM13.Section9Subwalls
public import GraphMinor.GM13.Section9Forest
public import GraphMinor.GM13.Section9Claim7
public import GraphMinor.GM13.Section9Claim91
public import GraphMinor.GM13.Parallel

/-!
# Graph Minors XIII, Section 9 (Part b): Crosses over Subwalls (9.1), Non-Dividing Subwalls (9.2), and Algorithm (9.3)–(9.4)

This file formalizes **(9.1)**, **(9.2)** (with Claims (1)–(8)), **(9.3)**, and Algorithm **(9.4)**
from Section 9 ("Finding a Flat Section of a Wall") of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110
(pages 98–102):

- `exists_gm12_theorem_4_5_sphere`, `lemma_9_1_far_from_outer_region`, and `theorem_9_1`
  ((9.1), page 98): Crosses over `k` mutually far-apart subwalls of a wall `H` in `G` yield a
  `K_p`-minor in `G` (from XII (4.5), with the three Graph Minors VII hypotheses supplied from
  `GraphMinor/GM07/`).
- `lemma_9_2_claim_1` through `lemma_9_2_claim_8` and `theorem_9_2`
  ((9.2), pages 99–101): `k` mutually far-apart non-dividing subwalls of `H` in `G` yield either an
  `(l, m)`-star over `H` or a `K_p`-minor in `G`, with the minimal non-dividing forest `F`
  constructed inside the proof.
- `theorem_9_4` and `theorem_9_3` ((9.3)–(9.4), pages 101–102): Given `t` subwalls `H₁, …, H_t` of
  `H` at pairwise distance `≥ r`, finding either a `K_p`-minor in `G` or a vertex set `X ⊆ V(G)`
  with `|X| < binom(p, 2)` and `≥ t - k` subwalls dividing in `(G \ X) ∪ H`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-! ## Basic Vertex and Edge Nonemptiness of Walls and Subwall Distance -/

/-- Every corner `W.corner k` belongs to `V(W.graph)`. -/
theorem Wall.corner_mem_vertexSet (W : Wall α β) (k : Fin 4) :
    W.corner k ∈ V(W.graph) :=
  W.branchVertex_mem_vertexSet _ _

/-- The edge set `E(W.graph)` of any wall `W` is nonempty. -/
theorem Wall.edgeSet_nonempty (W : Wall α β) : E(W.graph).Nonempty := by
  obtain ⟨e₀, he₀⟩ := elementaryWall_edgeSet_nonempty W.two_le_height
  let b := W.baseIso.edgeEquiv ⟨e₀, he₀⟩
  obtain ⟨_, _, _, _, ⟨e', he'⟩, _⟩ := W.path_of_edge b.1 b.2
  refine ⟨e', ?_⟩
  rw [W.edgeSet_eq]
  exact mem_iUnion₂.mpr ⟨b.1, b.2, he'⟩

/-- Any model of `H` in a subgraph `G' ≤ G` is also a model of `H` in `G`. -/
theorem HasGraphModel.mono_right {α' : Type*} {β' : Type*}
    {H : Graph α' β'} {G' G : Graph α β}
    (hG'G : G' ≤ G) (h : HasGraphModel H G') : HasGraphModel H G := by
  rcases h with ⟨vMap, eMap, hMod⟩
  refine ⟨vMap, eMap, {
    sub_of_mem := fun v hv => (hMod.sub_of_mem hv).trans hG'G
    nonempty_of_mem := hMod.nonempty_of_mem
    connected_of_mem := hMod.connected_of_mem
    disjoint_of_ne := hMod.disjoint_of_ne
    edge_mem := fun e he => hG'G.edgeSet_mono (hMod.edge_mem he)
    link_ends_of_ne := fun e u v hlink hne => by
      obtain ⟨x, hx, y, hy, hxy⟩ := hMod.link_ends_of_ne hlink hne
      exact ⟨x, hx, y, hy, hxy.mono hG'G⟩
    loop_ends := fun e u hloop => by
      obtain ⟨hnot, x, hx, y, hy, hxy⟩ := hMod.loop_ends hloop
      exact ⟨hnot, x, hx, y, hy, hxy.mono hG'G⟩
    eMap_injOn := hMod.eMap_injOn
  }⟩

/-- `wallSubgraphDist W H₁ H₂ ≤ W.dist v₁ v₂` for any `v₁ ∈ V(H₁)` and `v₂ ∈ V(H₂)`. -/
theorem wallSubgraphDist_le {W : DrawnWall α β} {H₁ H₂ : Graph α β}
    {v₁ v₂ : α} (hv₁ : v₁ ∈ V(H₁)) (hv₂ : v₂ ∈ V(H₂)) :
    wallSubgraphDist W H₁ H₂ ≤ W.dist v₁ v₂ :=
  Nat.sInf_le ⟨v₁, hv₁, v₂, hv₂, rfl⟩

/-- If `r ≤ wallSubgraphDist W H₁ H₂`, then `r ≤ W.dist v₁ v₂` for all `v₁ ∈ V(H₁)` and
`v₂ ∈ V(H₂)`. -/
theorem le_dist_of_le_wallSubgraphDist {W : DrawnWall α β} {H₁ H₂ : Graph α β} {r : ℕ}
    (hr : r ≤ wallSubgraphDist W H₁ H₂)
    {v₁ v₂ : α} (hv₁ : v₁ ∈ V(H₁)) (hv₂ : v₂ ∈ V(H₂)) :
    r ≤ W.dist v₁ v₂ :=
  hr.trans (wallSubgraphDist_le hv₁ hv₂)

/-- Symmetry of `wallSubgraphDist`. -/
theorem wallSubgraphDist_comm (W : DrawnWall α β) (H₁ H₂ : Graph α β) :
    wallSubgraphDist W H₁ H₂ = wallSubgraphDist W H₂ H₁ := by
  dsimp [wallSubgraphDist]
  congr 1
  ext k
  constructor
  · rintro ⟨v₁, hv₁, v₂, hv₂, hdist⟩
    exact ⟨v₂, hv₂, v₁, hv₁, (W.dist_comm v₂ v₁).trans hdist⟩
  · rintro ⟨v₂, hv₂, v₁, hv₁, hdist⟩
    exact ⟨v₁, hv₁, v₂, hv₂, (W.dist_comm v₁ v₂).trans hdist⟩

/-- If `0 < wallSubgraphDist W H₁ H₂`, then `V(H₁)` and `V(H₂)` are disjoint. -/
theorem disjoint_of_pos_wallSubgraphDist {W : DrawnWall α β} {H₁ H₂ : Graph α β}
    (hpos : 0 < wallSubgraphDist W H₁ H₂) :
    Disjoint V(H₁) V(H₂) := by
  rw [Set.disjoint_left]
  intro v hv₁ hv₂
  have hle : wallSubgraphDist W H₁ H₂ ≤ W.dist v v := wallSubgraphDist_le hv₁ hv₂
  rw [W.dist_self] at hle
  omega

/-! ## (9.1) Crosses over Mutually Far-Apart Subwalls (page 98) -/

/-- Minimum plane distance `d_i = min_{x ∈ V(H_i)} d(s, x)` from a point `s : EuclideanPlane` to the
vertices of a subgraph `H_i` of a drawn wall `W` (proof of (9.1), page 98). -/
noncomputable def pointToSubgraphDist
    (W : DrawnWall α β) (s : EuclideanPlane) (H_i : Graph α β) : ℕ :=
  sInf {k : ℕ | ∃ x ∈ V(H_i), W.planeDist s (W.vertexPoint x) = k}

/-- For every `x ∈ V(H_i)`, `pointToSubgraphDist W s H_i ≤ W.planeDist s (W.vertexPoint x)`. -/
theorem pointToSubgraphDist_le {W : DrawnWall α β} {s : EuclideanPlane} {H_i : Graph α β}
    {x : α} (hx : x ∈ V(H_i)) :
    pointToSubgraphDist W s H_i ≤ W.planeDist s (W.vertexPoint x) :=
  Nat.sInf_le ⟨x, hx, rfl⟩

/-- When `V(H_i)` is nonempty, some `x ∈ V(H_i)` attains `pointToSubgraphDist W s H_i`. -/
theorem exists_mem_eq_pointToSubgraphDist {W : DrawnWall α β} (s : EuclideanPlane)
    {H_i : Graph α β} (hne : V(H_i).Nonempty) :
    ∃ x ∈ V(H_i), W.planeDist s (W.vertexPoint x) = pointToSubgraphDist W s H_i := by
  rcases hne with ⟨x₀, hx₀⟩
  let S : Set ℕ := {k : ℕ | ∃ x ∈ V(H_i), W.planeDist s (W.vertexPoint x) = k}
  have hSne : S.Nonempty := ⟨W.planeDist s (W.vertexPoint x₀), x₀, hx₀, rfl⟩
  simpa [pointToSubgraphDist, S] using Nat.sInf_mem hSne

/-- Triangle-inequality bound from the proof of **(9.1)** (page 98):
"Since for $1 \le i \le t$ we have $r \le d(H_i, H_k) \le d_i + d_k$, it follows that $d_1, \dots, d_t \ge \frac{1}{2}r$." -/
theorem wallSubgraphDist_le_pointToSubgraphDist_add
    {W : DrawnWall α β} (hthin : IsThinPlaneDrawing W.drawingU)
    (s : EuclideanPlane) {H₁ H₂ : Graph α β}
    (hne₁ : V(H₁).Nonempty) (hne₂ : V(H₂).Nonempty) :
    wallSubgraphDist W H₁ H₂ ≤
      pointToSubgraphDist W s H₁ + pointToSubgraphDist W s H₂ := by
  obtain ⟨x₁, hx₁, hd₁⟩ := exists_mem_eq_pointToSubgraphDist (W := W) s hne₁
  obtain ⟨x₂, hx₂, hd₂⟩ := exists_mem_eq_pointToSubgraphDist (W := W) s hne₂
  have hle : wallSubgraphDist W H₁ H₂ ≤ W.dist x₁ x₂ := wallSubgraphDist_le hx₁ hx₂
  have htri : W.dist x₁ x₂ ≤
      W.planeDist (W.vertexPoint x₁) s + W.planeDist s (W.vertexPoint x₂) :=
    planeWallDist_triangle hthin (W.vertexPoint x₁) s (W.vertexPoint x₂)
  have hcomm : W.planeDist (W.vertexPoint x₁) s = W.planeDist s (W.vertexPoint x₁) :=
    planeWallDist_comm W.drawingU (W.vertexPoint x₁) s
  omega

/-- First step in the proof of **Graph Minors XIII, (9.1)** (page 98):
"For $1 \le i \le k$, let $d_i$ be the minimum of $d(s, x)$ taken over all $x \in V(H_i)$. We may
assume that $d_1, \dots, d_t \ge d_k$. Since for $1 \le i \le t$ we have
$r \le d(H_i, H_k) \le d_i + d_k$, it follows that $d_1, \dots, d_t \ge \frac{1}{2}r$." -/
theorem lemma_9_1_far_from_outer_region
    {W : DrawnWall α β} (hthin : IsThinPlaneDrawing W.drawingU)
    (s : EuclideanPlane) {t r : ℕ}
    (H_sub : Fin (t + 1) → Wall α β)
    (hdist : ∀ i j : Fin (t + 1), i ≠ j →
      r ≤ wallSubgraphDist W (H_sub i).graph (H_sub j).graph) :
    ∃ emb : Fin t ↪ Fin (t + 1),
      (∀ a : Fin t, ∀ x ∈ V((H_sub (emb a)).graph),
        r / 2 ≤ W.planeDist s (W.vertexPoint x)) ∧
      (∀ a b : Fin t, a ≠ b →
        r ≤ wallSubgraphDist W (H_sub (emb a)).graph (H_sub (emb b)).graph) := by
  let d : Fin (t + 1) → ℕ := fun i => pointToSubgraphDist W s (H_sub i).graph
  obtain ⟨i₀, _, hi₀_min⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (t + 1))) d Finset.univ_nonempty
  let emb : Fin t ↪ Fin (t + 1) := i₀.succAboveEmb
  refine ⟨emb, ?_, ?_⟩
  · intro a x hx
    have hne : emb a ≠ i₀ := Fin.succAbove_ne i₀ a
    have hr_le : r ≤ wallSubgraphDist W (H_sub (emb a)).graph (H_sub i₀).graph :=
      hdist (emb a) i₀ hne
    have hsum : wallSubgraphDist W (H_sub (emb a)).graph (H_sub i₀).graph ≤
        d (emb a) + d i₀ :=
      wallSubgraphDist_le_pointToSubgraphDist_add hthin s
        (H_sub (emb a)).vertexSet_nonempty (H_sub i₀).vertexSet_nonempty
    have hmin : d i₀ ≤ d (emb a) := hi₀_min (emb a) (Finset.mem_univ _)
    have hx_le : d (emb a) ≤ W.planeDist s (W.vertexPoint x) := pointToSubgraphDist_le hx
    omega
  · intro a b hab
    exact hdist (emb a) (emb b) (emb.injective.ne hab)

/-- Unconditional specialization of **Graph Minors XII, (4.5)** (`GM12.gm15_theorem45`) to the
2-sphere `SurfaceModel 0 0 0`, with the three Graph Minors VII hypotheses (`GM07.gm07_theorem_7_5`,
`GM07.gm07_theorem_5_1`, `GM07.gm07_theorem_5_5`) supplied from `GraphMinor/GM07/`:
"Let $\Sigma$ be a sphere, and for $p$ as given, let $\theta, t$ be as in [19, Theorem (4.5)]."
(page 98). -/
theorem exists_gm12_theorem_4_5_sphere (p : ℕ) :
    let S := SurfaceModel 0 0 0
    have : T2Space S := (isClosedSurface_model 0 0).2.1
    ∃ t θ : ℕ,
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
        (T_star : Set (Hypergraph α β × Hypergraph α β)) (H : Drawing S)
        (η : GM14.SpanEmbedding H G) (θ' : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (hSpan : GM15.IsSigmaSpan G H η θ_star θ' T_star T),
        GM14.HasTangleMetric H θ' T d →
        p ≤ θ_star → θ ≤ θ' →
        GM15.HasIndependentEyes G H η θ' T d t →
        GM12.ControlsMinor
          (Hypergraph.ofGraph G hSpan.isControlling.isTangle_star.finite_V
            hSpan.isControlling.isTangle_star.finite_E)
          θ_star T_star (GM16.completeGraph p) := by
  let S := SurfaceModel 0 0 0
  have hS : IsClosedSurface S := isClosedSurface_model 0 0
  let _ : T2Space S := hS.2.1
  have hConn : ConnectedSpace S := (isSurface_model 0 0 0).2
  have h75 : GM12.GM07Theorem75Statement.{0} :=
    GM07.gm07_theorem_7_5
  have h51 : GM12.GM07Theorem51Statement.{0} := GM07.gm07_theorem_5_1
  have h55 : GM12.GM07Theorem55Statement.{0} := GM07.gm07_theorem_5_5
  exact GM12.gm15_theorem45.{u, v, 0} S hS hConn p

/-- **Graph Minors XIII, (9.1)** (page 98):
"For any integer $p \ge 0$ there exist $k, r \ge 0$ such that the following holds. Let $H$ be a wall
in $G$, and let $H_1, \dots, H_k$ be subwalls of $H$ with $d(H_i, H_j) \ge r$ $(1 \le i < j \le k)$,
where $d$ is the distance function of $H$. For $1 \le i \le k$, let $P_i \cup Q_i$ be a cross over
$H_i$, such that
(i) $(P_i \cup Q_i) \cap H \subseteq H_i$, for $1 \le i \le k$
(ii) $(P_i \cup Q_i) \cap (P_j \cup Q_j)$ is null for $1 \le i < j \le k$.
Then $G$ has a $K_p$-minor. Moreover, a model of $K_p$ in $G$ can be found in time $\le C\varepsilon(G)$, where $C$ depends only on $p$ and the height of $H$." -/
theorem theorem_9_1_proof (p : ℕ) :
    ∃ k r : ℕ,
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β)
        (H_sub : Fin k → Wall α β) (P Q : Fin k → Graph α β),
        H.IsFigure1 →
        IsWallIn G H.toWall →
        (∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall) →
        (∀ i j : Fin k, i ≠ j → r ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
        (∀ i : Fin k, IsCrossOverWall G (H_sub i) (P i) (Q i)) →
        (∀ i : Fin k, (V(P i) ∪ V(Q i)) ∩ V(H.graph) ⊆ V((H_sub i).graph)) →
        Pairwise (fun i j : Fin k => Disjoint (V(P i) ∪ V(Q i)) (V(P j) ∪ V(Q j))) →
        HasGraphModel (GM16.completeGraph p) G := by
  have h75 : GM12.GM07Theorem75Statement.{0} :=
    GM07.gm07_theorem_7_5
  have h51 : GM12.GM07Theorem51Statement.{0} := GM07.gm07_theorem_5_1
  have h55 : GM12.GM07Theorem55Statement.{0} := GM07.gm07_theorem_5_5
  obtain ⟨k₀, N₀, hN₀_pos, h45⟩ :=
    GM12.theorem_4_5_span GM09.isClosedSurface_sphere p
  let t := max k₀ 1
  let θ := 4 * N₀ + 32
  let M := θ
  let k := t + 1
  let r := 12 * M + 26
  refine ⟨k, r, ?_⟩
  intro α β G H H_sub P Q hfig hHG hsub hdist hcross hinter hdisj
  obtain ⟨φ, Γ₀, pos, Γ, hΓ₀, hW_U, hW_v, _, hpos_inj, hpos_bv, hΓU, hΓv, hΓe, hΓe_cl, _⟩ :=
    hfig.exists_fig1Coords_full
  obtain ⟨emb, hfar_s, hdist_emb⟩ :=
    lemma_9_1_far_from_outer_region hfig.isThin (φ (fig1PlaneEquiv (-1, -1))) H_sub hdist
  exact lemma_9_1_tangle_eyes_step p hN₀_pos
    (fun G₀ θstar θ' Tstar Γ' η' T' d hCtrl hm hθ r' P₀ Q₀ =>
      h45 G₀ θstar θ' Tstar Γ' η' T' d hCtrl hm hθ r' P₀ Q₀)
    hΓ₀ hW_U hW_v hpos_inj hpos_bv hΓU hΓv hΓe hΓe_cl hHG
    (fun a => H_sub (emb a)) (fun a => P (emb a)) (fun a => Q (emb a))
    (fun a => hsub (emb a))
    hfar_s
    hdist_emb
    (fun a => hcross (emb a))
    (fun a => hinter (emb a))
    (fun a b hab => hdisj (emb.injective.ne hab))

/-- `GM13Theorem91Statement` holds unconditionally. -/
theorem theorem_9_1_parallel : GM13Theorem91Statement.{u, v} :=
  theorem_9_1_proof

/-! ## Maximal Independent Set Bound on Finite Sets (used in Claims (4), (5), and (8) of (9.2)) -/

/-- Greedy independent-set bound on a `Finset`: if `R` is a symmetric relation on `ι` and every
`x ∈ S` has at most `d` neighbors `y ∈ S` with `y ≠ x ∧ R x y`, then there is a subset `J ⊆ S` with
`S.card ≤ (d + 1) * J.card` such that `¬ R x y` for all distinct `x, y ∈ J`. -/
theorem exists_independent_finset_card_mul_ge {ι : Type*} [DecidableEq ι]
    (R : ι → ι → Prop) [DecidableRel R]
    (hsym : ∀ ⦃x y : ι⦄, R x y → R y x)
    (S : Finset ι) (d : ℕ)
    (hdeg : ∀ x ∈ S, (S.filter (fun y => y ≠ x ∧ R x y)).card ≤ d) :
    ∃ J ⊆ S, S.card ≤ (d + 1) * J.card ∧
      ∀ x ∈ J, ∀ y ∈ J, x ≠ y → ¬ R x y := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hS : S = ∅
    · subst hS
      simp only [Finset.card_empty] at hn
      subst hn
      exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
    · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      let N_out := S.filter (fun y => y ≠ x₀ ∧ R x₀ y)
      let N₀ := insert x₀ N_out
      let S' := S \ N₀
      have hx₀_N₀ : x₀ ∈ N₀ := Finset.mem_insert_self x₀ N_out
      have hS'_sub : S' ⊆ S := Finset.sdiff_subset
      have hx₀_not_S' : x₀ ∉ S' := by
        simp [S', hx₀_N₀]
      have hS'_ssub : S' ⊂ S :=
        Finset.ssubset_iff_of_subset hS'_sub |>.mpr ⟨x₀, hx₀, hx₀_not_S'⟩
      have hS'_lt : S'.card < n := by
        rw [← hn]
        exact Finset.card_lt_card hS'_ssub
      have hdeg' : ∀ x ∈ S', (S'.filter (fun y => y ≠ x ∧ R x y)).card ≤ d := by
        intro x hx
        have hxS : x ∈ S := hS'_sub hx
        have hsub_filter :
            S'.filter (fun y => y ≠ x ∧ R x y) ⊆ S.filter (fun y => y ≠ x ∧ R x y) :=
          Finset.filter_subset_filter _ hS'_sub
        exact (Finset.card_le_card hsub_filter).trans (hdeg x hxS)
      obtain ⟨J', hJ'_sub, hJ'_card, hJ'_ind⟩ := ih S'.card hS'_lt S' hdeg' rfl
      let J := insert x₀ J'
      have hx₀_not_J' : x₀ ∉ J' := fun h => hx₀_not_S' (hJ'_sub h)
      have hJ_card : J.card = J'.card + 1 := Finset.card_insert_of_notMem hx₀_not_J'
      have hN₀_card : N₀.card ≤ d + 1 := by
        have h1 : N₀.card ≤ N_out.card + 1 := Finset.card_insert_le x₀ N_out
        have h2 : N_out.card ≤ d := hdeg x₀ hx₀
        omega
      have hS_le : S.card ≤ S'.card + N₀.card := by
        have hsub_union : S ⊆ S' ∪ N₀ := by
          intro z hz
          by_cases hzN : z ∈ N₀
          · exact Finset.mem_union_right _ hzN
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz, hzN⟩)
        exact (Finset.card_le_card hsub_union).trans (Finset.card_union_le S' N₀)
      refine ⟨J, ?_, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz'
        · exact hx₀
        · exact hS'_sub (hJ'_sub hz')
      · rw [← hn]
        calc
          S.card ≤ S'.card + N₀.card := hS_le
          _ ≤ (d + 1) * J'.card + (d + 1) := Nat.add_le_add hJ'_card hN₀_card
          _ = (d + 1) * (J'.card + 1) := by ring
          _ = (d + 1) * J.card := by rw [hJ_card]
      · intro x hx y hy hxy hRxy
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · exact hxy rfl
          · have hyS' : y ∈ S' := hJ'_sub hy'
            rw [Finset.mem_sdiff] at hyS'
            apply hyS'.2
            exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hyS'.1, hxy.symm, hRxy⟩)
        · rcases Finset.mem_insert.mp hy with rfl | hy'
          · have hxS' : x ∈ S' := hJ'_sub hx'
            rw [Finset.mem_sdiff] at hxS'
            apply hxS'.2
            exact Finset.mem_insert_of_mem
              (Finset.mem_filter.mpr ⟨hxS'.1, hxy, hsym hRxy⟩)
          · exact hJ'_ind x hx' y hy' hxy hRxy

/-! ## Monotonicity and Subgraph Transfer for `(l, m)`-Stars -/

/-- If `3 ≤ l₁ ≤ l₂` and `m₁ ≤ m₂`, any `(l₂, m₂)`-star `S` over `H` in `G` with center `v`
contains an `(l₁, m₁)`-star `S' ≤ S` over `H` in `G` with center `v`. -/
theorem IsLMStarOver.mono_lm {G : Graph α β} {H : DrawnWall α β}
    {l₁ l₂ m₁ m₂ : ℕ} {S : Graph α β} {v : α}
    (hl₁ : 3 ≤ l₁) (hl : l₁ ≤ l₂) (hm : m₁ ≤ m₂)
    (hstar : IsLMStarOver G H l₂ m₂ S v) :
    ∃ S' : Graph α β, S' ≤ G ∧ IsLMStarOver G H l₁ m₁ S' v := by
  rcases hstar with ⟨_, hHG, hvG, P, u, _, hP, hdisj, hdist⟩
  let emb : Fin l₁ ↪ Fin l₂ := Fin.castLEEmb hl
  let P' : Fin l₁ → Graph α β := fun a => P (emb a)
  let u' : Fin l₁ → α := fun a => u (emb a)
  let S' : Graph α β := subgraphSUnion G (Set.range P')
  have hP'_le : ∀ A ∈ Set.range P', A ≤ G := by
    rintro A ⟨a, rfl⟩
    exact (hP (emb a)).1.1
  refine ⟨S', subgraphSUnion_le hP'_le, ⟨hl₁, hHG, hvG, P', u', rfl, ?_, ?_, ?_⟩⟩
  · intro a
    exact hP (emb a)
  · intro a b hab
    exact hdisj (emb a) (emb b) (emb.injective.ne hab)
  · intro a b hab
    exact hm.trans (hdist (emb a) (emb b) (emb.injective.ne hab))

/-- If `G' ≤ G`, `H.graph ≤ G'`, and `S` is an `(l, m)`-star over `H` in `G'` with center `v`,
then `S` is also an `(l, m)`-star over `H` in `G` with center `v`. -/
theorem IsLMStarOver.mono_graph {G' G : Graph α β} {H : DrawnWall α β}
    {l m : ℕ} {S : Graph α β} {v : α}
    (hG'G : G' ≤ G) (hstar : IsLMStarOver G' H l m S v) :
    IsLMStarOver G H l m S v := by
  rcases hstar with ⟨hl, hHG', hvG', P, u, hS_eq, hP, hdisj, hdist⟩
  have hP_le' : ∀ A ∈ Set.range P, A ≤ G' := by
    rintro A ⟨i, rfl⟩
    exact (hP i).1.1
  have hP_le : ∀ A ∈ Set.range P, A ≤ G := fun A hA => (hP_le' A hA).trans hG'G
  have hSUnion_eq : subgraphSUnion G' (Set.range P) = subgraphSUnion G (Set.range P) := by
    refine (Compatible.of_le_le ((subgraphSUnion_le hP_le').trans hG'G)
      (subgraphSUnion_le hP_le)).ext ?_ ?_
    · rw [vertexSet_subgraphSUnion, vertexSet_subgraphSUnion]
    · rw [edgeSet_subgraphSUnion hP_le', edgeSet_subgraphSUnion hP_le]
  refine ⟨hl, hHG'.trans hG'G, hG'G.vertexSet_mono hvG', P, u, hS_eq.trans hSUnion_eq, ?_, hdisj, hdist⟩
  intro i
  rcases hP i with ⟨hPi, hne, hui, hinter, hEdisj⟩
  exact ⟨hPi.mono hG'G, hne, hui, hinter, hEdisj⟩

/-! ## (9.2) Non-Dividing Subwalls Yield an `(l, m)`-Star or a `K_p`-Minor (pages 99–101) -/

/-- Claim (1) in the proof of **Graph Minors XIII, (9.2)** (pages 99–100):
"(1) *For $1 \le j \le t$, if $e \in E(S_j)$ there exists $i$ with $1 \le i \le k$ such that some
leaf $v$ of $S_j$ inside $H_i$ is essential, and every path of $S_j$ between $v$ and another leaf
uses $e$.*" -/
theorem lemma_9_2_claim_1 {G : Graph α β} {H : DrawnWall α β} {k : ℕ}
    {H_sub : Fin k → Wall α β}
    (hHG : H.graph ≤ G)
    (hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall)
    (hdisj : Pairwise (fun i₁ i₂ : Fin k => Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    {F : PartialSpiderForest G H H_sub k} (hmin : F.IsMinimal)
    (j : Fin F.t) {e : β} (he : e ∈ E((F.spiders j).tree)) :
    ∃ (i : Fin k) (v : α), F.isEssential j v i ∧
      ∀ u ∈ (F.spiders j).leaves, u ≠ v → e ∈ E((F.spiders j).leafPath v u) :=
  PartialSpiderForest.claim_1 hHG hsub hdisj hmin j he

/-- Claim (2) in the proof of **Graph Minors XIII, (9.2)** (page 100):
"(2) *For $1 \le j \le t$, at most one vertex of $S_j$ has valency $\ge 3$ in $S_j$; and if $S_j$
has $\ge 3$ leaves they are all essential, and if $S_j$ has two leaves then at least one is
essential.*" -/
theorem lemma_9_2_claim_2 {G : Graph α β} {H : DrawnWall α β} {k : ℕ}
    {H_sub : Fin k → Wall α β}
    (hHG : H.graph ≤ G)
    (hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall)
    (hdisj : Pairwise (fun i₁ i₂ : Fin k => Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    {F : PartialSpiderForest G H H_sub k} (hmin : F.IsMinimal)
    (j : Fin F.t) :
    (3 ≤ (F.spiders j).leaves.card →
      (∀ u ∈ (F.spiders j).leaves, ∃ i : Fin k, F.isEssential j u i) ∧
      ∃ (c : α) (ray : α → Graph α β),
        c ∈ V((F.spiders j).tree) \ V(H.graph) ∧
        (∀ u ∈ (F.spiders j).leaves, ray u ≤ (F.spiders j).tree ∧
          IsGraphPathWithEnds G (ray u) c u ∧
          V(ray u) ∩ V(H.graph) = {u}) ∧
        (∀ u₁ ∈ (F.spiders j).leaves, ∀ u₂ ∈ (F.spiders j).leaves, u₁ ≠ u₂ →
          V(ray u₁) ∩ V(ray u₂) = {c})) ∧
    ((F.spiders j).leaves.card = 2 →
      ∃ u ∈ (F.spiders j).leaves, ∃ i : Fin k, F.isEssential j u i) :=
  PartialSpiderForest.claim_2 hHG hsub hdisj hmin j

/-- Projection of the defining properties of `PartialSpiderForest.isEssential`. -/
theorem PartialSpiderForest.isEssential_spec {G : Graph α β} {H : DrawnWall α β} {k m : ℕ}
    {H_sub : Fin k → Wall α β} {F : PartialSpiderForest G H H_sub m}
    {j : Fin F.t} {v : α} {i : Fin k} (h : F.isEssential j v i) :
    v ∈ (F.spiders j).leaves ∧
    v ∈ (H_sub i).insideVerts ∧
    (∀ j' : Fin F.t, j' ≠ j → v ∉ V((F.spiders j').tree)) ∧
    (∀ j' : Fin F.t, ∀ x ∈ V((F.spiders j').tree), x ∈ (H_sub i).insideVerts → x = v) ∧
    (∀ u ∈ (F.spiders j).leaves, u ≠ v → u ∈ V(H.graph) \ V((H_sub i).graph)) :=
  h.2

/-- Two distinct essential leaves in `F` must lie in distinct subwalls `H_i ≠ H_{i'}`. -/
theorem essential_subwall_ne_of_ne {G : Graph α β} {H : DrawnWall α β} {k : ℕ}
    {H_sub : Fin k → Wall α β}
    (F : PartialSpiderForest G H H_sub k)
    {j₁ j₂ : Fin F.t} {u₁ u₂ : α} {i₁ i₂ : Fin k}
    (h₁ : F.isEssential j₁ u₁ i₁) (h₂ : F.isEssential j₂ u₂ i₂)
    (hne : u₁ ≠ u₂) : i₁ ≠ i₂ := by
  intro hi
  subst hi
  have hu₁ := F.isEssential_spec h₁
  have hu₂ := F.isEssential_spec h₂
  have hu₂_mem : u₂ ∈ V((F.spiders j₂).tree) := by
    have h := (F.spiders j₂).leaves_spec.2
    have h' : u₂ ∈ (↑(F.spiders j₂).leaves : Set α) := hu₂.1
    rw [h] at h'
    exact h'.1
  have heq : u₂ = u₁ := hu₁.2.2.2.1 j₂ u₂ hu₂_mem hu₂.2.1
  exact hne heq.symm

/-- Claim (3) in the proof of **Graph Minors XIII, (9.2)** (page 100):
"(3) *If $r \ge m$ then any vertex of $F$ of valency $\ge l$ (in $F$) is the center of an
$(l, m)$-star in $G$ over $H$.*"
This theorem covers both cases of the subproof of (3):
- Case 1 (`v ∉ V(H.graph)`): `S_j` has `≥ l` leaves; by (2), its unique branch vertex `c` is the
  center of an `(l, m)`-star over `H` in `G`.
- Case 2 (`v ∈ V(H.graph)`): `v` is a leaf of at least `l` distinct trees `S_j`; by (2), each of
  those `S_j` has 2 leaves and its other leaf is essential, so the union of `l` of these `S_j` is
  an `(l, m)`-star over `H` in `G` with center `v`. -/
theorem lemma_9_2_claim_3 {G : Graph α β} {H : DrawnWall α β} {k l m r : ℕ}
    {H_sub : Fin k → Wall α β}
    (hHG : H.graph ≤ G) (hl : 3 ≤ l) (hrm : m ≤ r)
    (hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall)
    (hdisj_subwalls : Pairwise (fun i₁ i₂ : Fin k =>
      Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    (hdist : ∀ i₁ i₂ : Fin k, i₁ ≠ i₂ →
      r ≤ wallSubgraphDist H (H_sub i₁).graph (H_sub i₂).graph)
    {F : PartialSpiderForest G H H_sub k} (hmin : F.IsMinimal)
    (hhigh : (∃ j : Fin F.t, l ≤ (F.spiders j).leaves.card) ∨
      (∃ (v : α) (T : Finset (Fin F.t)), l ≤ T.card ∧ ∀ j ∈ T, v ∈ (F.spiders j).leaves)) :
    ∃ (S : Graph α β) (v : α), IsLMStarOver G H l m S v := by
  rcases hhigh with ⟨j, hlj⟩ | ⟨v, T, hlT, hvT⟩
  · -- Case 1: `S_j` has `≥ l ≥ 3` leaves
    have h3 : 3 ≤ (F.spiders j).leaves.card := hl.trans hlj
    obtain ⟨hclaim2_3, _⟩ := lemma_9_2_claim_2 hHG hsub hdisj_subwalls hmin j
    obtain ⟨hess_all, c, ray, hc_mem, hray_spec, hray_disj⟩ := hclaim2_3 h3
    let embL : Fin l ↪ (F.spiders j).leaves :=
      (Fin.castLEEmb hlj).trans (F.spiders j).leaves.equivFin.symm.toEmbedding
    let u : Fin l → α := fun a => (embL a).1
    let P : Fin l → Graph α β := fun a => ray (u a)
    have hu_mem : ∀ a : Fin l, u a ∈ (F.spiders j).leaves := fun a => (embL a).2
    have hu_inj : Function.Injective u := fun a b hab => embL.injective (Subtype.ext hab)
    let S := subgraphSUnion G (Set.range P)
    refine ⟨S, c, ⟨hl, hHG, (F.spiders j).tree_le.1.vertexSet_mono hc_mem.1, P, u, rfl, ?_, ?_, ?_⟩⟩
    · intro a
      obtain ⟨hray_le, hpath, hinter⟩ := hray_spec (u a) (hu_mem a)
      have hu_H : u a ∈ V(H.graph) := by
        have h : u a ∈ (↑(F.spiders j).leaves : Set α) := hu_mem a
        rw [(F.spiders j).leaves_spec.2] at h
        exact h.2
      have hne : u a ≠ c := fun h => hc_mem.2 (h ▸ hu_H)
      have hinter_sub : V(P a) ∩ V(H.graph) ⊆ {c, u a} := by
        rw [hinter]
        intro x hx
        exact Or.inr hx
      have hE_disj : Disjoint E(P a) E(H.graph) :=
        Disjoint.mono_left hray_le.edgeSet_mono (F.spiders j).tree_le.2
      exact ⟨hpath, hne, hu_H, hinter_sub, hE_disj⟩
    · intro a b hab
      exact hray_disj (u a) (hu_mem a) (u b) (hu_mem b) (hu_inj.ne hab)
    · intro a b hab
      obtain ⟨i_a, h_ia⟩ := hess_all (u a) (hu_mem a)
      obtain ⟨i_b, h_ib⟩ := hess_all (u b) (hu_mem b)
      have hi_ne : i_a ≠ i_b := essential_subwall_ne_of_ne F h_ia h_ib (hu_inj.ne hab)
      have hua_in : u a ∈ V((H_sub i_a).graph) := (F.isEssential_spec h_ia).2.1.1
      have hub_in : u b ∈ V((H_sub i_b).graph) := (F.isEssential_spec h_ib).2.1.1
      exact hrm.trans (le_dist_of_le_wallSubgraphDist (hdist i_a i_b hi_ne) hua_in hub_in)
  · -- Case 2: `v ∈ V(H)` is a leaf of `≥ l ≥ 3` distinct trees `S_j` (`j ∈ T`)
    let embT : Fin l ↪ T := (Fin.castLEEmb hlT).trans T.equivFin.symm.toEmbedding
    let j_of : Fin l → Fin F.t := fun a => (embT a).1
    have hj_inj : Function.Injective j_of := fun a b hab => embT.injective (Subtype.ext hab)
    have hv_leaf : ∀ a : Fin l, v ∈ (F.spiders (j_of a)).leaves := fun a => hvT (j_of a) (embT a).2
    have hv_H : v ∈ V(H.graph) := by
      have h : v ∈ (↑(F.spiders (j_of ⟨0, by omega⟩)).leaves : Set α) := hv_leaf ⟨0, by omega⟩
      rw [(F.spiders _).leaves_spec.2] at h
      exact h.2
    -- `v` cannot be essential in any `S_{j_of a}` because `l ≥ 3 ≥ 2`, so `v` is in another `S_{j_of b}`
    have hv_not_ess : ∀ (a : Fin l) (i : Fin k), ¬ F.isEssential (j_of a) v i := by
      intro a i hess
      let b : Fin l := if a.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hab : b ≠ a := by
        intro h
        have hval : b.val = a.val := congrArg Fin.val h
        by_cases ha0 : a.val = 0
        · simp [b, ha0] at hval
        · simp [b, ha0] at hval
          exact ha0 hval.symm
      have hv_in_b : v ∈ V((F.spiders (j_of b)).tree) := by
        have h : v ∈ (↑(F.spiders (j_of b)).leaves : Set α) := hv_leaf b
        rw [(F.spiders _).leaves_spec.2] at h
        exact h.1
      exact (F.isEssential_spec hess).2.2.1 (j_of b) (hj_inj.ne hab) hv_in_b
    -- Therefore each `S_{j_of a}` has another leaf `u_a ≠ v` that is essential!
    have hex_other : ∀ a : Fin l,
        ∃ (u_a : α) (i_a : Fin k), u_a ∈ (F.spiders (j_of a)).leaves ∧ u_a ≠ v ∧
          F.isEssential (j_of a) u_a i_a := by
      intro a
      have hcard_ge_2 := (F.spiders (j_of a)).leaves_spec.1
      have hclaim2 := lemma_9_2_claim_2 hHG hsub hdisj_subwalls hmin (j_of a)
      by_cases hcard3 : 3 ≤ (F.spiders (j_of a)).leaves.card
      · obtain ⟨i_v, hi_v⟩ := (hclaim2.1 hcard3).1 v (hv_leaf a)
        exact False.elim (hv_not_ess a i_v hi_v)
      · have hcard2 : (F.spiders (j_of a)).leaves.card = 2 := by omega
        obtain ⟨u_a, hu_a, i_a, hess_a⟩ := hclaim2.2 hcard2
        have huv : u_a ≠ v := by
          intro h
          subst h
          exact hv_not_ess a i_a hess_a
        exact ⟨u_a, i_a, hu_a, huv, hess_a⟩
    choose u i_of hu_leaf hu_ne_v hu_ess using hex_other
    let P : Fin l → Graph α β := fun a => (F.spiders (j_of a)).leafPath v (u a)
    let S := subgraphSUnion G (Set.range P)
    refine ⟨S, v, ⟨hl, hHG, hHG.vertexSet_mono hv_H, P, u, rfl, ?_, ?_, ?_⟩⟩
    · intro a
      obtain ⟨_, hHPath⟩ :=
        (F.spiders (j_of a)).leafPath_spec (hv_leaf a) (hu_leaf a) (hu_ne_v a).symm
      rcases hHPath with ⟨_, hPath, _, _, hu_H, hinter, hE_disj⟩
      exact ⟨hPath, hu_ne_v a, hu_H, hinter.subset, hE_disj⟩
    · intro a b hab
      obtain ⟨hPa_le, hHPath_a⟩ :=
        (F.spiders (j_of a)).leafPath_spec (hv_leaf a) (hu_leaf a) (hu_ne_v a).symm
      obtain ⟨hPb_le, hHPath_b⟩ :=
        (F.spiders (j_of b)).leafPath_spec (hv_leaf b) (hu_leaf b) (hu_ne_v b).symm
      ext x
      simp only [mem_inter_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hxa, hxb⟩
        have hx_Sa : x ∈ V((F.spiders (j_of a)).tree) := hPa_le.vertexSet_mono hxa
        have hx_Sb : x ∈ V((F.spiders (j_of b)).tree) := hPb_le.vertexSet_mono hxb
        have hx_H : x ∈ V(H.graph) :=
          F.inter_subset_wall (j_of a) (j_of b) (hj_inj.ne hab) ⟨hx_Sa, hx_Sb⟩
        have hx_ends : x ∈ ({v, u a} : Set α) := by
          rw [← hHPath_a.2.2.2.2.2.1]
          exact ⟨hxa, hx_H⟩
        rcases hx_ends with rfl | rfl
        · rfl
        · exfalso
          exact (F.isEssential_spec (hu_ess a)).2.2.1 (j_of b) (hj_inj.ne hab.symm) hx_Sb
      · rintro rfl
        exact ⟨hHPath_a.2.1.left_mem, hHPath_b.2.1.left_mem⟩
    · intro a b hab
      have hua_ne_ub : u a ≠ u b := by
        intro heq
        have hub_Sb : u b ∈ V((F.spiders (j_of b)).tree) := by
          have h : u b ∈ (↑(F.spiders (j_of b)).leaves : Set α) := hu_leaf b
          rw [(F.spiders _).leaves_spec.2] at h
          exact h.1
        rw [← heq] at hub_Sb
        exact (F.isEssential_spec (hu_ess a)).2.2.1 (j_of b) (hj_inj.ne hab.symm) hub_Sb
      have hi_ne : i_of a ≠ i_of b :=
        essential_subwall_ne_of_ne F (hu_ess a) (hu_ess b) hua_ne_ub
      have hua_in : u a ∈ V((H_sub (i_of a)).graph) :=
        (F.isEssential_spec (hu_ess a)).2.1.1
      have hub_in : u b ∈ V((H_sub (i_of b)).graph) :=
        (F.isEssential_spec (hu_ess b)).2.1.1
      exact hrm.trans (le_dist_of_le_wallSubgraphDist (hdist (i_of a) (i_of b) hi_ne) hua_in hub_in)

/-- Claim (4) in the proof of **Graph Minors XIII, (9.2)** (page 100):
"(4) *For any $n \ge 0$, if $k \ge n(l-1)^2$, then there exist $n$ mutually vertex-disjoint
$H$-paths $Q_1, \dots, Q_n \subseteq F$ with ends $s_i, t_i$ $(1 \le i \le n)$, and we may renumber
$H_1, \dots, H_k$ so that $s_i$ is inside $H_i$, $t_i$ is outside $H_i$, and no other $s_j$ or
$t_j$ is inside $H_i$ $(1 \le i \le n)$.*" -/
theorem lemma_9_2_claim_4 {G : Graph α β} {H : DrawnWall α β} {k l n : ℕ}
    {H_sub : Fin k → Wall α β}
    (hHG : H.graph ≤ G)
    (hl : 3 ≤ l) (hkn : n * (l - 1) ^ 2 ≤ k)
    (hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall)
    (hdisj_subwalls : Pairwise (fun i₁ i₂ : Fin k =>
      Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)))
    {F : PartialSpiderForest G H H_sub k} (hmin : F.IsMinimal)
    (hleaves_le : ∀ j : Fin F.t, (F.spiders j).leaves.card ≤ l - 1)
    (hdeg_le : ∀ v : α, (Finset.univ.filter (fun j : Fin F.t => v ∈ (F.spiders j).leaves)).card ≤ l - 1) :
    ∃ (σ : Fin n ↪ Fin k) (Q : Fin n → Graph α β) (s t : Fin n → α),
      (∀ a : Fin n, (∃ j : Fin F.t, Q a ≤ (F.spiders j).tree) ∧
        IsHPathWithEnds G H.graph (Q a) (s a) (t a)) ∧
      Pairwise (fun a₁ a₂ : Fin n => Disjoint V(Q a₁) V(Q a₂)) ∧
      (∀ a : Fin n, s a ∈ (H_sub (σ a)).insideVerts ∧
        t a ∈ V(H.graph) \ V((H_sub (σ a)).graph)) ∧
      (∀ a b : Fin n, b ≠ a →
        s b ∉ (H_sub (σ a)).insideVerts ∧ t b ∉ (H_sub (σ a)).insideVerts) := by
  -- Step 1: Every `S_j` has at least one essential leaf `v_ess j` inside `H_{i_ess j}`
  have hex_ess : ∀ j : Fin F.t, ∃ v ∈ (F.spiders j).leaves, ∃ i : Fin k, F.isEssential j v i := by
    intro j
    have hcard2 := (F.spiders j).leaves_spec.1
    have hclaim2 := lemma_9_2_claim_2 hHG hsub hdisj_subwalls hmin j
    by_cases hcard3 : 3 ≤ (F.spiders j).leaves.card
    · obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (F.spiders j).leaves.card)
      obtain ⟨i, hi⟩ := (hclaim2.1 hcard3).1 u hu
      exact ⟨u, hu, i, hi⟩
    · have heq2 : (F.spiders j).leaves.card = 2 := by omega
      exact hclaim2.2 heq2
  choose v_ess hv_ess_leaf i_ess hv_ess using hex_ess
  -- Step 2: Each `S_j` has at most one leaf that can belong to any `S_{j'}` with `j' ≠ j`
  have hdeg_conflict : ∀ j ∈ (Finset.univ : Finset (Fin F.t)),
      (Finset.univ.filter (fun j' : Fin F.t =>
        j' ≠ j ∧ ¬ Disjoint V((F.spiders j).tree) V((F.spiders j').tree))).card ≤ l - 2 := by
    intro j _
    have hcard2 := (F.spiders j).leaves_spec.1
    have hclaim2 := lemma_9_2_claim_2 hHG hsub hdisj_subwalls hmin j
    by_cases hcard3 : 3 ≤ (F.spiders j).leaves.card
    · -- All leaves of `S_j` are essential, so `S_j` is disjoint from every `S_{j'}` (`j' ≠ j`)
      have hempty : Finset.univ.filter (fun j' : Fin F.t =>
          j' ≠ j ∧ ¬ Disjoint V((F.spiders j).tree) V((F.spiders j').tree)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j' _ ⟨hne, hndisj⟩
        rw [Set.not_disjoint_iff] at hndisj
        rcases hndisj with ⟨x, hxj, hxj'⟩
        have hxH : x ∈ V(H.graph) := F.inter_subset_wall j j' hne.symm ⟨hxj, hxj'⟩
        have hx_leaf : x ∈ (F.spiders j).leaves := by
          have h : x ∈ (↑(F.spiders j).leaves : Set α) := by
            rw [(F.spiders j).leaves_spec.2]
            exact ⟨hxj, hxH⟩
          exact h
        obtain ⟨i_x, hx_ess⟩ := (hclaim2.1 hcard3).1 x hx_leaf
        exact (F.isEssential_spec hx_ess).2.2.1 j' hne hxj'
      rw [hempty, Finset.card_empty]
      omega
    · -- `(F.spiders j).leaves.card = 2`, and `v_ess j` is essential, so only `w₀` can be shared
      have heq2 : (F.spiders j).leaves.card = 2 := by omega
      have hcard_erase : ((F.spiders j).leaves.erase (v_ess j)).card = 1 := by
        rw [Finset.card_erase_of_mem (hv_ess_leaf j), heq2]
      obtain ⟨w₀, hw₀_eq⟩ := Finset.card_eq_one.mp hcard_erase
      have hw₀_mem : w₀ ∈ (F.spiders j).leaves :=
        Finset.mem_of_mem_erase (hw₀_eq ▸ Finset.mem_singleton_self w₀)
      have hsub_filter :
          Finset.univ.filter (fun j' : Fin F.t =>
            j' ≠ j ∧ ¬ Disjoint V((F.spiders j).tree) V((F.spiders j').tree)) ⊆
          (Finset.univ.filter (fun j' : Fin F.t => w₀ ∈ (F.spiders j').leaves)).erase j := by
        intro j' hj'
        rw [Finset.mem_filter] at hj'
        rcases hj'.2 with ⟨hne, hndisj⟩
        rw [Set.not_disjoint_iff] at hndisj
        rcases hndisj with ⟨x, hxj, hxj'⟩
        have hxH : x ∈ V(H.graph) := F.inter_subset_wall j j' hne.symm ⟨hxj, hxj'⟩
        have hx_leaf_j : x ∈ (F.spiders j).leaves := by
          have h : x ∈ (↑(F.spiders j).leaves : Set α) := by
            rw [(F.spiders j).leaves_spec.2]
            exact ⟨hxj, hxH⟩
          exact h
        have hx_leaf_j' : x ∈ (F.spiders j').leaves := by
          have h : x ∈ (↑(F.spiders j').leaves : Set α) := by
            rw [(F.spiders j').leaves_spec.2]
            exact ⟨hxj', hxH⟩
          exact h
        have hx_ne : x ≠ v_ess j := by
          intro h
          subst h
          exact (F.isEssential_spec (hv_ess j)).2.2.1 j' hne hxj'
        have hx_w₀ : x = w₀ := by
          have hx_er : x ∈ (F.spiders j).leaves.erase (v_ess j) :=
            Finset.mem_erase.mpr ⟨hx_ne, hx_leaf_j⟩
          rw [hw₀_eq, Finset.mem_singleton] at hx_er
          exact hx_er
        subst hx_w₀
        exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨Finset.mem_univ j', hx_leaf_j'⟩⟩
      have hj_in : j ∈ Finset.univ.filter (fun j' : Fin F.t => w₀ ∈ (F.spiders j').leaves) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hw₀_mem⟩
      have hcard_le1 := Finset.card_le_card hsub_filter
      have hcard_er := Finset.card_erase_of_mem hj_in
      have hdeg_w₀ := hdeg_le w₀
      omega
  -- Step 3: Apply `exists_independent_finset_card_mul_ge` with `d = l - 2`
  have hsym : ∀ ⦃j j' : Fin F.t⦄,
      ¬ Disjoint V((F.spiders j).tree) V((F.spiders j').tree) →
        ¬ Disjoint V((F.spiders j').tree) V((F.spiders j).tree) :=
    fun _ _ h hd => h hd.symm
  obtain ⟨J, _, hJ_card, hJ_disj⟩ :=
    exists_independent_finset_card_mul_ge
      (fun j j' : Fin F.t => ¬ Disjoint V((F.spiders j).tree) V((F.spiders j').tree))
      hsym Finset.univ (l - 2) hdeg_conflict
  have hJ_card' : F.t ≤ (l - 1) * J.card := by
    have hd1 : l - 2 + 1 = l - 1 := by omega
    simpa [hd1] using hJ_card
  -- Step 4: Bound `k ≤ (l - 1) * F.t` from `covers_all` and `hleaves_le`
  have hsubwall_has_inside_leaf :
      ∀ i : Fin k, ∃ j : Fin F.t, ∃ v ∈ (F.spiders j).leaves, v ∈ (H_sub i).insideVerts := by
    intro i
    obtain ⟨j, u, w, hu, _, hu_in, _⟩ := F.covers i i.2
    exact ⟨j, u, hu, hu_in⟩
  choose j_sub w_sub hw_sub_leaf hw_sub_in using hsubwall_has_inside_leaf
  have hw_sub_inj : Function.Injective w_sub := by
    intro i₁ i₂ heq
    by_contra hne
    have h₁ : w_sub i₁ ∈ V((H_sub i₁).graph) := (hw_sub_in i₁).1
    have h₂ : w_sub i₁ ∈ V((H_sub i₂).graph) := heq ▸ (hw_sub_in i₂).1
    exact Set.disjoint_left.mp (hdisj_subwalls hne) h₁ h₂
  have hw_sub_mem_biUnion :
      Finset.univ.image w_sub ⊆ Finset.univ.biUnion (fun j : Fin F.t => (F.spiders j).leaves) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨j_sub i, Finset.mem_univ _, hw_sub_leaf i⟩
  have hk_le_t : k ≤ (l - 1) * F.t := by
    calc
      k = (Finset.univ : Finset (Fin k)).card := by simp
      _ = (Finset.univ.image w_sub).card := (Finset.card_image_of_injective _ hw_sub_inj).symm
      _ ≤ (Finset.univ.biUnion (fun j : Fin F.t => (F.spiders j).leaves)).card :=
        Finset.card_le_card hw_sub_mem_biUnion
      _ ≤ ∑ j : Fin F.t, (F.spiders j).leaves.card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin F.t, (l - 1) := Finset.sum_le_sum (fun j _ => hleaves_le j)
      _ = F.t * (l - 1) := by simp
      _ = (l - 1) * F.t := Nat.mul_comm _ _
  have hn_le_J : n ≤ J.card := by
    have hmul : n * (l - 1) ^ 2 ≤ J.card * (l - 1) ^ 2 := by
      calc
        n * (l - 1) ^ 2 ≤ k := hkn
        _ ≤ (l - 1) * F.t := hk_le_t
        _ ≤ (l - 1) * ((l - 1) * J.card) := Nat.mul_le_mul_left (l - 1) hJ_card'
        _ = J.card * (l - 1) ^ 2 := by ring
    have hpos : 0 < (l - 1) ^ 2 := by
      have : 0 < l - 1 := by omega
      positivity
    exact Nat.le_of_mul_le_mul_right hmul hpos
  -- Step 5: Select `n` trees from `J` and extract `Q_a, s_a, t_a`
  let embJ : Fin n ↪ J := (Fin.castLEEmb hn_le_J).trans J.equivFin.symm.toEmbedding
  let j_sel : Fin n → Fin F.t := fun a => (embJ a).1
  have hj_sel_mem : ∀ a : Fin n, j_sel a ∈ J := fun a => (embJ a).2
  have hj_sel_inj : Function.Injective j_sel :=
    fun a b hab => embJ.injective (Subtype.ext hab)
  have hj_sel_disj : ∀ a b : Fin n, a ≠ b →
      Disjoint V((F.spiders (j_sel a)).tree) V((F.spiders (j_sel b)).tree) := by
    intro a b hab
    have hnot := hJ_disj (j_sel a) (hj_sel_mem a) (j_sel b) (hj_sel_mem b) (hj_sel_inj.ne hab)
    exact not_not.mp hnot
  let s : Fin n → α := fun a => v_ess (j_sel a)
  let σ_fun : Fin n → Fin k := fun a => i_ess (j_sel a)
  have hσ_inj : Function.Injective σ_fun := by
    intro a b hab
    by_contra hne
    have hs_ne : s a ≠ s b := by
      intro hseq
      have hsa_in : s a ∈ V((F.spiders (j_sel a)).tree) := by
        have h : s a ∈ (↑(F.spiders (j_sel a)).leaves : Set α) := hv_ess_leaf (j_sel a)
        rw [(F.spiders _).leaves_spec.2] at h
        exact h.1
      have hsb_in : s a ∈ V((F.spiders (j_sel b)).tree) := by
        have h : s b ∈ (↑(F.spiders (j_sel b)).leaves : Set α) := hv_ess_leaf (j_sel b)
        rw [(F.spiders _).leaves_spec.2] at h
        exact hseq ▸ h.1
      exact Set.disjoint_left.mp (hj_sel_disj a b hne) hsa_in hsb_in
    exact essential_subwall_ne_of_ne F (hv_ess (j_sel a)) (hv_ess (j_sel b)) hs_ne hab
  let σ : Fin n ↪ Fin k := ⟨σ_fun, hσ_inj⟩
  -- For each `a : Fin n`, pick a second leaf `t a ∈ (F.spiders (j_sel a)).leaves` with `t a ≠ s a`
  have hex_t : ∀ a : Fin n, ∃ t_a ∈ (F.spiders (j_sel a)).leaves, t_a ≠ s a := by
    intro a
    have hcard2 := (F.spiders (j_sel a)).leaves_spec.1
    have hpos : 0 < ((F.spiders (j_sel a)).leaves.erase (s a)).card := by
      rw [Finset.card_erase_of_mem (hv_ess_leaf (j_sel a))]
      omega
    obtain ⟨t_a, ht_a⟩ := Finset.card_pos.mp hpos
    exact ⟨t_a, Finset.mem_of_mem_erase ht_a, (Finset.mem_erase.mp ht_a).1⟩
  choose t ht_leaf ht_ne_s using hex_t
  let Q : Fin n → Graph α β := fun a => (F.spiders (j_sel a)).leafPath (s a) (t a)
  refine ⟨σ, Q, s, t, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨hQ_le, hHPath⟩ :=
      (F.spiders (j_sel a)).leafPath_spec (hv_ess_leaf (j_sel a)) (ht_leaf a) (ht_ne_s a).symm
    exact ⟨⟨j_sel a, hQ_le⟩, hHPath⟩
  · intro a b hab
    obtain ⟨hQa_le, _⟩ :=
      (F.spiders (j_sel a)).leafPath_spec (hv_ess_leaf (j_sel a)) (ht_leaf a) (ht_ne_s a).symm
    obtain ⟨hQb_le, _⟩ :=
      (F.spiders (j_sel b)).leafPath_spec (hv_ess_leaf (j_sel b)) (ht_leaf b) (ht_ne_s b).symm
    exact Disjoint.mono hQa_le.vertexSet_mono hQb_le.vertexSet_mono (hj_sel_disj a b hab)
  · intro a
    have hspec := F.isEssential_spec (hv_ess (j_sel a))
    exact ⟨hspec.2.1, hspec.2.2.2.2 (t a) (ht_leaf a) (ht_ne_s a)⟩
  · intro a b hba
    have hspec := F.isEssential_spec (hv_ess (j_sel a))
    have hdisj_ab := hj_sel_disj b a hba
    have hsa_in : s a ∈ V((F.spiders (j_sel a)).tree) := by
      have h : s a ∈ (↑(F.spiders (j_sel a)).leaves : Set α) := hv_ess_leaf (j_sel a)
      rw [(F.spiders _).leaves_spec.2] at h
      exact h.1
    have hsb_in : s b ∈ V((F.spiders (j_sel b)).tree) := by
      have h : s b ∈ (↑(F.spiders (j_sel b)).leaves : Set α) := hv_ess_leaf (j_sel b)
      rw [(F.spiders _).leaves_spec.2] at h
      exact h.1
    have htb_in : t b ∈ V((F.spiders (j_sel b)).tree) := by
      have h : t b ∈ (↑(F.spiders (j_sel b)).leaves : Set α) := ht_leaf b
      rw [(F.spiders _).leaves_spec.2] at h
      exact h.1
    constructor
    · intro hsb_inside
      have heq : s b = s a := hspec.2.2.2.1 (j_sel b) (s b) hsb_in hsb_inside
      exact Set.disjoint_left.mp hdisj_ab hsb_in (heq ▸ hsa_in)
    · intro htb_inside
      have heq : t b = s a := hspec.2.2.2.1 (j_sel b) (t b) htb_in htb_inside
      exact Set.disjoint_left.mp hdisj_ab htb_in (heq ▸ hsa_in)

/-- Claim (5) in the proof of **Graph Minors XIII, (9.2)** (pages 100–101):
"(5) *For all sufficiently large $r_1$ and $n_1$, if there exists $I \subseteq \{1, \dots, n\}$ with
$|I| = n_1$ such that $d(s_i, t_i) \ge r_1$ for $i \in I$ and $d(t_i, t_{i'}) \ge r$, for distinct
$i, i' \in I$, then $G$ has a $K_p$-minor.*"

Note on the paper's text: claim (5) prints `$d(t_i, t_{i'}) \ge r$`, whereas:
1. $r_1, n_1$ are chosen to satisfy (5) (`Choose $r_1, n_1$ to satisfy (5).`) *before* $r$ is chosen
   for (6) and (7) (`Choose $n_2, n_3$, and $r$ to satisfy (6) and (7).`),
2. the subproof of (5) (page 101) uses only $d(t_i, t_{i'}) \ge r_1 = 2 r_0$ (so that at most one
   $i' \ne i$ has $d(s_i, t_{i'}) < r_0$), and
3. Claim (7) tests $d(t_i, t_{i_0}) \le r_1$, so Claim (8) produces $d(t_i, t_{i'}) > r_1$ (hence
   $\ge r_1$, not $\ge r$).
Below, `ht_dist` assumes only `2 * r₀ ≤ H.dist (t i) (t i')` (which holds both when
`d(t_i, t_{i'}) ≥ r_1` and when `d(t_i, t_{i'}) ≥ r ≥ r_1`). -/
theorem lemma_9_2_claim_5 {G : Graph α β} {H : DrawnWall α β}
    {r₀ p n : ℕ}
    (hfig : H.IsFigure1)
    (_hHG : H.graph ≤ G)
    (hr₀ : ∀ (P : Fin (p.choose 2) → Graph α β) (s t : Fin (p.choose 2) → α),
      (∀ i, IsHPathWithEnds G H.graph (P i) (s i) (t i)) →
      Pairwise (fun i j => Disjoint V(P i) V(P j)) →
      (∀ i j, i ≠ j →
        r₀ ≤ H.dist (s i) (s j) ∧
        r₀ ≤ H.dist (s i) (t j) ∧
        r₀ ≤ H.dist (t i) (s j) ∧
        r₀ ≤ H.dist (t i) (t j)) →
      (∀ i, r₀ ≤ H.dist (s i) (t i)) →
      HasGraphModel (GM16.completeGraph p) G)
    (Q : Fin n → Graph α β) (s t : Fin n → α)
    (hQ : ∀ i : Fin n, IsHPathWithEnds G H.graph (Q i) (s i) (t i))
    (hQ_disj : Pairwise (fun i₁ i₂ : Fin n => Disjoint V(Q i₁) V(Q i₂)))
    (hs_dist : ∀ i₁ i₂ : Fin n, i₁ ≠ i₂ → 2 * r₀ ≤ H.dist (s i₁) (s i₂))
    (I : Finset (Fin n))
    (hI_card : 3 * p.choose 2 ≤ I.card)
    (hst_dist : ∀ i ∈ I, 2 * r₀ ≤ H.dist (s i) (t i))
    (ht_dist : ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → 2 * r₀ ≤ H.dist (t i) (t i')) :
    HasGraphModel (GM16.completeGraph p) G := by
  have hthin : IsThinPlaneDrawing H.drawingU := hfig.isThin
  let R : Fin n → Fin n → Prop :=
    fun i i' => H.dist (s i) (t i') < r₀ ∨ H.dist (t i) (s i') < r₀
  have hsym : ∀ ⦃i i' : Fin n⦄, R i i' → R i' i := by
    intro i i' h
    rcases h with h1 | h2
    · right
      rw [H.dist_comm]
      exact h1
    · left
      rw [H.dist_comm]
      exact h2
  have hdeg : ∀ i ∈ I, (I.filter (fun i' => i' ≠ i ∧ R i i')).card ≤ 2 := by
    intro i _
    let A₁ := I.filter (fun i' => i' ≠ i ∧ H.dist (s i) (t i') < r₀)
    let A₂ := I.filter (fun i' => i' ≠ i ∧ H.dist (t i) (s i') < r₀)
    have hsub : I.filter (fun i' => i' ≠ i ∧ R i i') ⊆ A₁ ∪ A₂ := by
      intro i' hi'
      rw [Finset.mem_filter] at hi'
      rcases hi' with ⟨hi'I, hne, h1 | h2⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi'I, hne, h1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hi'I, hne, h2⟩)
    have hA₁_le : A₁.card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro i₁ hi₁ i₂ hi₂
      rw [Finset.mem_filter] at hi₁ hi₂
      by_contra hne
      have hfar : 2 * r₀ ≤ H.dist (t i₁) (t i₂) := ht_dist i₁ hi₁.1 i₂ hi₂.1 hne
      have htri : H.dist (t i₁) (t i₂) ≤ H.dist (t i₁) (s i) + H.dist (s i) (t i₂) :=
        H.dist_triangle hthin (t i₁) (s i) (t i₂)
      have h1 : H.dist (t i₁) (s i) < r₀ := by
        rw [H.dist_comm]
        exact hi₁.2.2
      have h2 : H.dist (s i) (t i₂) < r₀ := hi₂.2.2
      omega
    have hA₂_le : A₂.card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro i₁ hi₁ i₂ hi₂
      rw [Finset.mem_filter] at hi₁ hi₂
      have h1 : H.dist (s i₁) (t i) < r₀ := by
        rw [H.dist_comm]
        exact hi₁.2.2
      have h2 : H.dist (s i₂) (t i) < r₀ := by
        rw [H.dist_comm]
        exact hi₂.2.2
      exact at_most_one_leaf_close hthin hs_dist (t i) h1 h2
    calc
      (I.filter (fun i' => i' ≠ i ∧ R i i')).card ≤ (A₁ ∪ A₂).card :=
        Finset.card_le_card hsub
      _ ≤ A₁.card + A₂.card := Finset.card_union_le A₁ A₂
      _ ≤ 1 + 1 := Nat.add_le_add hA₁_le hA₂_le
      _ = 2 := rfl
  obtain ⟨I', hI'_sub, hI'_card, hI'_ind⟩ :=
    exists_independent_finset_card_mul_ge R hsym I 2 hdeg
  have hI'_ge : p.choose 2 ≤ I'.card := by omega
  let emb : Fin (p.choose 2) ↪ I' :=
    (Fin.castLEEmb hI'_ge).trans I'.equivFin.symm.toEmbedding
  let idx : Fin (p.choose 2) → Fin n := fun a => (emb a).1
  have hidx_I' : ∀ a, idx a ∈ I' := fun a => (emb a).2
  have hidx_I : ∀ a, idx a ∈ I := fun a => hI'_sub (hidx_I' a)
  have hidx_inj : Function.Injective idx :=
    fun a b hab => emb.injective (Subtype.ext hab)
  exact hr₀
    (fun a => Q (idx a)) (fun a => s (idx a)) (fun a => t (idx a))
    (fun a => hQ (idx a))
    (fun a b hab => hQ_disj (hidx_inj.ne hab))
    (fun a b hab => by
      have hne : idx a ≠ idx b := hidx_inj.ne hab
      have hnotR : ¬ R (idx a) (idx b) :=
        hI'_ind (idx a) (hidx_I' a) (idx b) (hidx_I' b) hne
      simp only [R, not_or, not_lt] at hnotR
      have hss := hs_dist (idx a) (idx b) hne
      have htt := ht_dist (idx a) (hidx_I a) (idx b) (hidx_I b) hne
      exact ⟨by omega, hnotR.1, hnotR.2, by omega⟩)
    (fun a => by
      have hst := hst_dist (idx a) (hidx_I a)
      omega)

/-- Claim (6) in the proof of **Graph Minors XIII, (9.2)** (page 101):
"(6) *If $n_2$ and $r$ are sufficiently large, and there exists $I \subseteq \{1, \dots, n\}$ with
$|I| = n_2$ such that $d(s_i, t_i) \le r_1$ for all $i \in I$, then $G$ has a $K_p$-minor.*" -/
theorem lemma_9_2_claim_6 {G : Graph α β} {H : DrawnWall α β}
    {k p n r₁ k₉₁ r₉₁ r : ℕ}
    (hfig : H.IsFigure1)
    (hHG : H.graph ≤ G)
    (hr_enlarge : r₉₁ + 12 * r₁ + 64 ≤ r)
    (H_sub : Fin k → Wall α β)
    (hsub : ∀ j : Fin k, (H_sub j).IsSubwallOf H.toWall)
    (hdist : ∀ j₁ j₂ : Fin k, j₁ ≠ j₂ → r ≤ wallSubgraphDist H (H_sub j₁).graph (H_sub j₂).graph)
    (σ : Fin n ↪ Fin k)
    (Q : Fin n → Graph α β) (s t : Fin n → α)
    (hQ_path : ∀ i : Fin n, IsHPathWithEnds G H.graph (Q i) (s i) (t i))
    (hQ_disj : Pairwise (fun i₁ i₂ => Disjoint V(Q i₁) V(Q i₂)))
    (hst_in_out : ∀ i : Fin n,
      s i ∈ (H_sub (σ i)).insideVerts ∧ t i ∈ V(H.graph) \ V((H_sub (σ i)).graph))
    (I : Finset (Fin n))
    (hI_card : k₉₁ + 1 ≤ I.card)
    (hst_le : ∀ i ∈ I, H.dist (s i) (t i) ≤ r₁)
    (h91_step : ∀ (H' : Fin k₉₁ → Wall α β) (P' Q' : Fin k₉₁ → Graph α β),
      (∀ a : Fin k₉₁, (H' a).IsSubwallOf H.toWall) →
      (∀ a b : Fin k₉₁, a ≠ b → r₉₁ ≤ wallSubgraphDist H (H' a).graph (H' b).graph) →
      (∀ a : Fin k₉₁, IsCrossOverWall G (H' a) (P' a) (Q' a)) →
      (∀ a : Fin k₉₁, (V(P' a) ∪ V(Q' a)) ∩ V(H.graph) ⊆ V((H' a).graph)) →
      Pairwise (fun a b : Fin k₉₁ =>
        Disjoint (V(P' a) ∪ V(Q' a)) (V(P' b) ∪ V(Q' b))) →
      HasGraphModel (GM16.completeGraph p) G) :
    HasGraphModel (GM16.completeGraph p) G := by
  let embI : Fin (k₉₁ + 1) ↪ I := (Fin.castLEEmb hI_card).trans I.equivFin.symm.toEmbedding
  let I_all : Fin (k₉₁ + 1) ↪ Fin n := embI.trans (Function.Embedding.subtype _)
  have hthin : IsThinPlaneDrawing H.drawingU := hfig.isThin
  have ⟨φ, Γ, hΓ, hU, hV⟩ := hfig
  let s_out : EuclideanPlane := φ (fig1PlaneEquiv (-1, -1))
  let m_out : ℕ := (2 * r₁ + 8) + 6
  have hle_m : 2 * m_out ≤ r := by dsimp [m_out]; omega
  have hdist_all : ∀ a b : Fin (k₉₁ + 1), a ≠ b →
      2 * m_out ≤
        wallSubgraphDist H (H_sub (σ (I_all a))).graph (H_sub (σ (I_all b))).graph :=
    fun a b hab => hle_m.trans
      (hdist _ _ (σ.injective.ne (I_all.injective.ne hab)))
  obtain ⟨emb_out, hfar_out, _⟩ :=
    lemma_9_1_far_from_outer_region hthin s_out (fun a => H_sub (σ (I_all a))) hdist_all
  let idx : Fin k₉₁ ↪ Fin n := emb_out.trans I_all
  let W₀ : Fin k₉₁ → Wall α β := fun a => H_sub (σ (idx a))
  have hex_a : ∀ a : Fin k₉₁,
      ∃ (W₁ : Wall α β) (P_c Q_c : Graph α β),
        W₁.IsSubwallOf H.toWall ∧
        (∀ u ∈ V(W₁.graph), ∃ v ∈ V((W₀ a).graph), H.dist u v ≤ 6 * r₁ + 30) ∧
        IsCrossOverWall G W₁ P_c Q_c ∧
        V(P_c) ∪ V(Q_c) ⊆ V(W₁.graph) ∪ V(Q (idx a)) ∧
        V(Q (idx a)) ∩ V(H.graph) ⊆ V(W₁.graph) ∧
        (V(P_c) ∪ V(Q_c)) ∩ V(H.graph) ⊆ V(W₁.graph) :=
    fun a => hΓ.exists_enlarged_subwall_and_cross_of_isSubwallOf hU hV hHG
      (hsub (σ (idx a))) (by intro x hx; have := hfar_out a x hx; dsimp [m_out, s_out] at this; omega)
      (hQ_path (idx a))
      (hst_in_out (idx a)).1 (hst_in_out (idx a)).2
      (hst_le (idx a) (embI (emb_out a)).2)
  choose H' P_c Q_c hH'_sub hH'_dist hcross hVPQ_sub hQ_inter_sub hVPQ_inter using hex_a
  have hH'_far_pos : ∀ a b : Fin k₉₁, a ≠ b →
      r₉₁ + 1 ≤ wallSubgraphDist H (H' a).graph (H' b).graph := by
    intro a b hab
    obtain ⟨u₀, hu₀⟩ := (H' a).vertexSet_nonempty
    obtain ⟨v₀, hv₀⟩ := (H' b).vertexSet_nonempty
    obtain ⟨u_a, hu_a, u_b, hu_b, hmin⟩ : ∃ u ∈ V((H' a).graph), ∃ v ∈ V((H' b).graph),
        H.dist u v = wallSubgraphDist H (H' a).graph (H' b).graph := by
      simpa [wallSubgraphDist] using
        Nat.sInf_mem (s := {k : ℕ | ∃ u ∈ V((H' a).graph), ∃ v ∈ V((H' b).graph), H.dist u v = k})
          ⟨H.dist u₀ v₀, u₀, hu₀, v₀, hv₀, rfl⟩
    rw [← hmin]
    obtain ⟨v_a, hv_a, hd_a⟩ := hH'_dist a u_a hu_a
    obtain ⟨v_b, hv_b, hd_b⟩ := hH'_dist b u_b hu_b
    have hd_v : r ≤ H.dist v_a v_b :=
      le_dist_of_le_wallSubgraphDist
        (hdist (σ (idx a)) (σ (idx b)) (σ.injective.ne (idx.injective.ne hab))) hv_a hv_b
    have htri₁ : H.dist v_a v_b ≤ H.dist v_a u_a + H.dist u_a v_b :=
      H.dist_triangle hthin v_a u_a v_b
    have htri₂ : H.dist u_a v_b ≤ H.dist u_a u_b + H.dist u_b v_b :=
      H.dist_triangle hthin u_a u_b v_b
    rw [H.dist_comm v_a u_a] at htri₁
    omega
  have hH'_far : ∀ a b : Fin k₉₁, a ≠ b →
      r₉₁ ≤ wallSubgraphDist H (H' a).graph (H' b).graph :=
    fun a b hab => le_trans (Nat.le_succ _) (hH'_far_pos a b hab)
  have hVPQ_disj : Pairwise (fun a b : Fin k₉₁ =>
      Disjoint (V(P_c a) ∪ V(Q_c a)) (V(P_c b) ∪ V(Q_c b))) := by
    intro a b hab
    have hpos : 0 < wallSubgraphDist H (H' a).graph (H' b).graph :=
      lt_of_lt_of_le (by omega) (hH'_far_pos a b hab)
    have hdisj_H' : Disjoint V((H' a).graph) V((H' b).graph) :=
      disjoint_of_pos_wallSubgraphDist hpos
    have hdisj_Q : Disjoint V(Q (idx a)) V(Q (idx b)) :=
      hQ_disj (idx.injective.ne hab)
    rw [Set.disjoint_left]
    intro z hza hzb
    rcases hVPQ_sub a hza with hza_H' | hza_Q <;> rcases hVPQ_sub b hzb with hzb_H' | hzb_Q
    · exact Set.disjoint_left.mp hdisj_H' hza_H' hzb_H'
    · have hzH : z ∈ V(H.graph) := (hH'_sub a).graph_le'.vertexSet_mono hza_H'
      exact Set.disjoint_left.mp hdisj_H' hza_H' (hQ_inter_sub b ⟨hzb_Q, hzH⟩)
    · have hzH : z ∈ V(H.graph) := (hH'_sub b).graph_le'.vertexSet_mono hzb_H'
      exact Set.disjoint_left.mp hdisj_H' (hQ_inter_sub a ⟨hza_Q, hzH⟩) hzb_H'
    · exact Set.disjoint_left.mp hdisj_Q hza_Q hzb_Q
  exact h91_step H' P_c Q_c hH'_sub hH'_far hcross hVPQ_inter hVPQ_disj

/-- Reindexing the endpoints of a `GraphWalk` along equalities of vertices preserves `.support`
and `.edges`. -/
lemma GraphWalk.exists_copy {G : Graph α β} {u v u' v' : α} (W : GraphWalk G u v)
    (hu : u = u') (hv : v = v') :
    ∃ W' : GraphWalk G u' v', W'.support = W.support ∧ W'.edges = W.edges := by
  subst hu hv
  exact ⟨W, rfl, rfl⟩

/-- A vertex belongs to `(p.append q).support` if and only if it belongs to `p.support` or `q.support`. -/
lemma GraphWalk.mem_support_append_iff {G : Graph α β} {u v w x : α}
    (p : GraphWalk G u v) (q : GraphWalk G v w) :
    x ∈ (p.append q).support ↔ x ∈ p.support ∨ x ∈ q.support := by
  refine ⟨GraphWalk.mem_support_append p q, ?_⟩
  induction p with
  | nil _ =>
    rintro (hx | hx)
    · rw [GraphWalk.support_nil, List.mem_singleton] at hx
      subst hx; exact q.start_mem_support
    · exact hx
  | cons _ r ih =>
    rintro (hx | hx)
    · rw [GraphWalk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih q (Or.inl hx))
    · exact List.mem_cons_of_mem _ (ih q (Or.inr hx))

/-- If `L` is a path in `H` from `s'` to `s` and `H' ≤ H` has `V(L) ∩ V(H') = {s'}`, then
`Disjoint E(L) E(H')`. -/
lemma IsGraphPathWithEnds.disjoint_edgeSet_of_inter_eq_singleton
    {H H' L : Graph α β} {s' s : α}
    (hL : IsGraphPathWithEnds H L s' s) (hH' : H' ≤ H)
    (hinter : V(L) ∩ V(H') = {s'}) :
    Disjoint E(L) E(H') := by
  rw [Set.disjoint_left]
  intro e heL heH'
  obtain ⟨x, y, hxyH'⟩ := H'.exists_isLink_of_mem_edgeSet heH'
  have hxyH : H.IsLink e x y := hxyH'.mono hH'
  have hxyL : L.IsLink e x y := (hL.le.isLink_iff heL).mpr hxyH
  have hx : x = s' := by
    have h : x ∈ V(L) ∩ V(H') := ⟨hxyL.left_mem, hxyH'.left_mem⟩
    rwa [hinter, Set.mem_singleton_iff] at h
  have hy : y = s' := by
    have h : y ∈ V(L) ∩ V(H') := ⟨hxyL.right_mem, hxyH'.right_mem⟩
    rwa [hinter, Set.mem_singleton_iff] at h
  exact ne_of_isLink_of_isGraphPathWithEnds hL hxyL (hx.trans hy.symm)

/-- The hole radius `r_hole_9_2 r₁ = 8 * r₁ + 200` used in Claim (7) of (9.2). -/
def r_hole_9_2 (r₁ : ℕ) : ℕ := 8 * r₁ + 200

/-- The endpoint reconnection radius `R_s_9_2 r₁ = 8 * (4 * r_hole_9_2 r₁ + 6) + 200` in Claim (7). -/
def R_s_9_2 (r₁ : ℕ) : ℕ := 8 * (4 * r_hole_9_2 r₁ + 6) + 200

/-- For each `H.graph`-path `Q` in `G` from `s` to `t` with `H.dist t t₀ ≤ r_hole_9_2 r₁` and
`R_s_9_2 r₁ + r_hole_9_2 r₁ < H.dist s t₀`, there is a vertex `s' ∈ V(H'.graph)` within
`H.dist s' s ≤ R_s_9_2 r₁` and a walk `W_arm : GraphWalk G s' t` extending `Q` to `H'.graph`. -/
lemma exists_arm_walk_to_hole {G : Graph α β} {H H' : DrawnWall α β} {r₁ : ℕ} {t₀ : α}
    (hfig : H.IsFigure1) (hHG : H.graph ≤ G)
    (hH'_fig : H'.IsFigure1) (hH'_le : H'.graph ≤ H.graph)
    (hH'_vp : H'.vertexPoint = H.vertexPoint)
    (hH'_dist : DistGeSub H'.planeDist H.planeDist (4 * r_hole_9_2 r₁ + 4))
    (hH'_hole : ∀ u ∈ V(H'.graph), ¬ H.dist u t₀ ≤ r_hole_9_2 r₁)
    {Q : Graph α β} {s t : α}
    (hQ : IsHPathWithEnds G H.graph Q s t)
    (ht_close : H.dist t t₀ ≤ r_hole_9_2 r₁)
    (hs_far : R_s_9_2 r₁ + r_hole_9_2 r₁ < H.dist s t₀) :
    ∃ (s' : α) (W_arm : GraphWalk G s' t),
      s' ∈ V(H'.graph) ∧
      H.dist s' s ≤ R_s_9_2 r₁ ∧
      {z | z ∈ W_arm.support} ⊆ {w ∈ V(H.graph) | H.dist w s ≤ R_s_9_2 r₁} ∪ V(Q) ∧
      {z | z ∈ W_arm.support} ∩ V(H'.graph) = {s'} ∧
      {z | z ∈ W_arm.support} ∩ {w ∈ V(H.graph) | H.dist w t₀ ≤ r_hole_9_2 r₁} = {t} ∧
      Disjoint {e | e ∈ W_arm.edges} E(H'.graph) := by
  have hthin : IsThinPlaneDrawing H.drawingU := hfig.isThin
  have hs_H : s ∈ V(H.graph) := hQ.2.2.2.1
  have ht_H : t ∈ V(H.graph) := hQ.2.2.2.2.1
  obtain ⟨v', hv'_H', hv'_plane⟩ := hH'_fig.exists_vertex_planeDist_le_two (H.vertexPoint s)
  have hv'_H : v' ∈ V(H.graph) := hH'_le.vertexSet_mono hv'_H'
  have hv'_dist : H.dist v' s ≤ 4 * r_hole_9_2 r₁ + 6 := by
    rw [H.dist_comm]
    have h1 := hH'_dist (H.vertexPoint s) (H.vertexPoint v')
    have h2 : H'.planeDist (H.vertexPoint s) (H.vertexPoint v') ≤ 2 := by
      rwa [hH'_vp] at hv'_plane
    change H.planeDist (H.vertexPoint s) (H.vertexPoint v') ≤ _
    omega
  obtain ⟨W_s, hW_s⟩ := hfig.exists_walk_dist_le hv'_H hs_H
  have hW_s_R : ∀ w ∈ W_s.support, w ∈ V(H.graph) ∧ H.dist w s ≤ R_s_9_2 r₁ := by
    intro w hw
    refine ⟨W_s.mem_vertexSet_of_mem_support hw, ?_⟩
    have h := hW_s w hw
    dsimp [R_s_9_2]; omega
  obtain ⟨s', hs'_H', y, hy_eq, L, _, hVL_sub, hL_ft⟩ :=
    exists_isFromToPathWithEnds_of_walk W_s (X := V(H'.graph)) (Y := ({s} : Set α))
      hv'_H' (Set.mem_singleton s)
  rw [Set.mem_singleton_iff] at hy_eq
  subst y
  rcases hL_ft with ⟨hL_path, hVL_H', _⟩
  have hEL_disj : Disjoint E(L) E(H'.graph) :=
    IsGraphPathWithEnds.disjoint_edgeSet_of_inter_eq_singleton hL_path hH'_le hVL_H'
  have hVL_ball : V(L) ⊆ {w ∈ V(H.graph) | H.dist w s ≤ R_s_9_2 r₁} :=
    fun w hw => hW_s_R w (hVL_sub hw)
  rcases hL_path.mono hHG with ⟨hLG, wL₀, _, hVL_eq, hEL_eq⟩
  obtain ⟨wL, hwL_supp, hwL_edges⟩ := exists_walk_up_of_le hLG wL₀
  rcases hQ.2.1 with ⟨hQG, wQ₀, _, hVQ_eq, hEQ_eq⟩
  obtain ⟨wQ, hwQ_supp, hwQ_edges⟩ := exists_walk_up_of_le hQG wQ₀
  let W_arm := wL.append wQ
  have hsupp_eq : {z | z ∈ W_arm.support} = V(L) ∪ V(Q) := by
    ext z
    simp [W_arm, GraphWalk.mem_support_append_iff, hwL_supp, hwQ_supp, hVL_eq, hVQ_eq]
  have hedges_eq : {e | e ∈ W_arm.edges} = E(L) ∪ E(Q) := by
    ext e
    simp [W_arm, GraphWalk.edges_append, hwL_edges, hwQ_edges, hEL_eq, hEQ_eq]
  refine ⟨s', W_arm, hs'_H', (hVL_ball hL_path.left_mem).2, ?_, ?_, ?_, ?_⟩
  · rw [hsupp_eq]
    exact Set.union_subset_union_left _ hVL_ball
  · rw [hsupp_eq, Set.union_inter_distrib_right, hVL_H']
    ext z
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_singleton_iff]
    refine ⟨?_, fun h => Or.inl h⟩
    rintro (rfl | ⟨hzQ, hzH'⟩)
    · rfl
    · have hz_st : z ∈ ({s, t} : Set α) := by
        rw [← hQ.2.2.2.2.2.1]
        exact ⟨hzQ, hH'_le.vertexSet_mono hzH'⟩
      rcases Set.mem_insert_iff.mp hz_st with rfl | hzt
      · have hs_in : z ∈ V(L) ∩ V(H'.graph) := ⟨hL_path.right_mem, hzH'⟩
        rwa [hVL_H', Set.mem_singleton_iff] at hs_in
      · rw [Set.mem_singleton_iff] at hzt
        subst hzt
        exact False.elim (hH'_hole z hzH' ht_close)
  · rw [hsupp_eq]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨hzL | hzQ, hzH, hz_hole⟩
      · have hzs := (hVL_ball hzL).2
        have htri := H.dist_triangle hthin s z t₀
        rw [H.dist_comm s z] at htri
        omega
      · have hz_st : z ∈ ({s, t} : Set α) := by
          rw [← hQ.2.2.2.2.2.1]
          exact ⟨hzQ, hzH⟩
        rcases Set.mem_insert_iff.mp hz_st with rfl | hzt
        · omega
        · exact Set.mem_singleton_iff.mp hzt
    · rintro rfl
      exact ⟨Or.inr hQ.2.1.right_mem, ht_H, ht_close⟩
  · rw [hedges_eq, Set.disjoint_union_left]
    exact ⟨hEL_disj, hQ.2.2.2.2.2.2.mono_right hH'_le.edgeSet_mono⟩

/-- Claim (7) in the proof of **Graph Minors XIII, (9.2)** (page 101):
"(7) *If $n_3$ and $r$ are sufficiently large, and there exist $i_0$ with $1 \le i_0 \le n$ and
$I \subseteq \{1, \dots, n\} - \{i_0\}$ such that $|I| = n_3$ and $d(t_i, t_{i_0}) \le r_1$ for
$i \in I$, then $G$ has a $K_p$-minor.*" -/
theorem lemma_9_2_claim_7 {G : Graph α β} {H : DrawnWall α β}
    {r₀ p n r₁ r : ℕ}
    (hfig : H.IsFigure1)
    (hHG : H.graph ≤ G)
    (hr₀ : ∀ (H' : DrawnWall α β),
      H'.IsFigure1 →
      IsWallIn G H'.toWall →
      ∀ (P : Fin (p.choose 2) → Graph α β) (s' t' : Fin (p.choose 2) → α),
        (∀ i, IsHPathWithEnds G H'.graph (P i) (s' i) (t' i)) →
        Pairwise (fun i j => Disjoint V(P i) V(P j)) →
        (∀ i j, i ≠ j →
          r₀ ≤ H'.dist (s' i) (s' j) ∧
          r₀ ≤ H'.dist (s' i) (t' j) ∧
          r₀ ≤ H'.dist (t' i) (s' j) ∧
          r₀ ≤ H'.dist (t' i) (t' j)) →
        (∀ i, r₀ ≤ H'.dist (s' i) (t' i)) →
        HasGraphModel (GM16.completeGraph p) G)
    (hn2 : 2 ≤ n)
    (hr_far : r₀ + 2 * R_s_9_2 r₁ + 4 * r_hole_9_2 r₁ + 10 ≤ r)
    (Q : Fin n → Graph α β) (s t : Fin n → α)
    (hQ_path : ∀ i : Fin n, IsHPathWithEnds G H.graph (Q i) (s i) (t i))
    (hQ_disj : Pairwise (fun i₁ i₂ => Disjoint V(Q i₁) V(Q i₂)))
    (hs_dist : ∀ i₁ i₂ : Fin n, i₁ ≠ i₂ → r ≤ H.dist (s i₁) (s i₂))
    (i₀ : Fin n) (ht₀ : t i₀ ∈ V(H.graph))
    (I : Finset (Fin n)) (_hi₀_not_I : i₀ ∉ I) (hI_card : 4 * p.choose 2 + 1 ≤ I.card)
    (ht_close : ∀ i ∈ I, H.dist (t i) (t i₀) ≤ r₁) :
    HasGraphModel (GM16.completeGraph p) G := by
  have hthin : IsThinPlaneDrawing H.drawingU := hfig.isThin
  have hr_punct : 2 * r_hole_9_2 r₁ + 4 ≤ H.height := by
    let idx₀ : Fin n := ⟨0, by omega⟩
    let idx₁ : Fin n := ⟨1, by omega⟩
    have hne : idx₀ ≠ idx₁ := by
      intro h
      have h' : idx₀.val = idx₁.val := congrArg Fin.val h
      dsimp [idx₀, idx₁] at h'
      omega
    have h1 : r ≤ H.dist (s idx₀) (s idx₁) := hs_dist idx₀ idx₁ hne
    have h2 : H.dist (s idx₀) (s idx₁) ≤ H.height + 2 :=
      hfig.dist_le_height_add_two (s idx₀) (s idx₁)
    have hR : 0 < R_s_9_2 r₁ := by dsimp [R_s_9_2]; omega
    omega
  obtain ⟨H', hH'_fig, hH'_le, _, hH'_vp, _, hH'_dist, hH'_hole⟩ :=
    theorem_7_3_proof H (t i₀) (r_hole_9_2 r₁) hfig ht₀ hr_punct
  -- Discard at most one `i ∈ I` with `H.dist (s i) (t i₀) ≤ R_s_9_2 r₁ + r_hole_9_2 r₁`
  let I_bad := I.filter (fun i => H.dist (s i) (t i₀) ≤ R_s_9_2 r₁ + r_hole_9_2 r₁)
  let I' := I.filter (fun i => ¬ H.dist (s i) (t i₀) ≤ R_s_9_2 r₁ + r_hole_9_2 r₁)
  have hI_sum : I_bad.card + I'.card = I.card :=
    Finset.card_filter_add_card_filter_not
      (fun i => H.dist (s i) (t i₀) ≤ R_s_9_2 r₁ + r_hole_9_2 r₁)
  have hI_bad_le : I_bad.card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro i₁ hi₁ i₂ hi₂
    rw [Finset.mem_filter] at hi₁ hi₂
    have hs_sep : ∀ a b : Fin n, a ≠ b →
        2 * (R_s_9_2 r₁ + r_hole_9_2 r₁ + 1) ≤ H.dist (s a) (s b) :=
      fun a b hab => le_trans (by omega) (hs_dist a b hab)
    exact at_most_one_leaf_close hthin hs_sep (t i₀) (by omega) (by omega)
  have hI'_card : 4 * p.choose 2 ≤ I'.card := by omega
  -- Construct the extended arm walks `W_arm i` for `i : I'`
  have hex_arm : ∀ i : I',
      ∃ (s' : α) (W_arm : GraphWalk G s' (t i.1)),
        s' ∈ V(H'.graph) ∧
        H.dist s' (s i.1) ≤ R_s_9_2 r₁ ∧
        {z | z ∈ W_arm.support} ⊆
          {w ∈ V(H.graph) | H.dist w (s i.1) ≤ R_s_9_2 r₁} ∪ V(Q i.1) ∧
        {z | z ∈ W_arm.support} ∩ V(H'.graph) = {s'} ∧
        {z | z ∈ W_arm.support} ∩ {w ∈ V(H.graph) | H.dist w (t i₀) ≤ r_hole_9_2 r₁} = {t i.1} ∧
        Disjoint {e | e ∈ W_arm.edges} E(H'.graph) := by
    intro i
    have hiI : i.1 ∈ I := (Finset.mem_filter.mp i.2).1
    have hi_far : R_s_9_2 r₁ + r_hole_9_2 r₁ < H.dist (s i.1) (t i₀) :=
      Nat.lt_of_not_le (Finset.mem_filter.mp i.2).2
    have ht_le : H.dist (t i.1) (t i₀) ≤ r_hole_9_2 r₁ := by
      have h := ht_close i.1 hiI
      dsimp [r_hole_9_2]; omega
    exact exists_arm_walk_to_hole hfig hHG hH'_fig hH'_le hH'_vp hH'_dist hH'_hole
      (hQ_path i.1) ht_le hi_far
  choose s' W_arm hs'_H' hs'_dist hW_arm_sub hW_arm_H' hW_arm_hole hW_arm_edges using hex_arm
  -- Distinct `i₁ ≠ i₂ : I'` have disjoint arm walk supports
  have hW_arm_disj : ∀ i₁ i₂ : I', i₁ ≠ i₂ →
      Disjoint {z | z ∈ (W_arm i₁).support} {z | z ∈ (W_arm i₂).support} := by
    intro i₁ i₂ hne
    have hne_val : i₁.1 ≠ i₂.1 := Subtype.coe_ne_coe.mpr hne
    have hss : r ≤ H.dist (s i₁.1) (s i₂.1) := hs_dist i₁.1 i₂.1 hne_val
    have hQ_d : Disjoint V(Q i₁.1) V(Q i₂.1) := hQ_disj hne_val
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    have hz₁' := hW_arm_sub i₁ hz₁
    have hz₂' := hW_arm_sub i₂ hz₂
    rcases hz₁' with ⟨hzH, hz_b1⟩ | hz_Q1 <;> rcases hz₂' with ⟨hzH2, hz_b2⟩ | hz_Q2
    · have htri := H.dist_triangle hthin (s i₁.1) z (s i₂.1)
      rw [H.dist_comm (s i₁.1) z] at htri
      omega
    · have hz_st : z ∈ ({s i₂.1, t i₂.1} : Set α) := by
        rw [← (hQ_path i₂.1).2.2.2.2.2.1]
        exact ⟨hz_Q2, hzH⟩
      rcases Set.mem_insert_iff.mp hz_st with rfl | hzt
      · rw [H.dist_comm] at hz_b1; omega
      · rw [Set.mem_singleton_iff] at hzt
        subst hzt
        have hi₁_far : R_s_9_2 r₁ + r_hole_9_2 r₁ < H.dist (s i₁.1) (t i₀) :=
          Nat.lt_of_not_le (Finset.mem_filter.mp i₁.2).2
        have ht₂_le : H.dist (t i₂.1) (t i₀) ≤ r_hole_9_2 r₁ := by
          have h := ht_close i₂.1 (Finset.mem_filter.mp i₂.2).1
          dsimp [r_hole_9_2]; omega
        have htri := H.dist_triangle hthin (s i₁.1) (t i₂.1) (t i₀)
        rw [H.dist_comm (s i₁.1) (t i₂.1)] at htri
        omega
    · have hz_st : z ∈ ({s i₁.1, t i₁.1} : Set α) := by
        rw [← (hQ_path i₁.1).2.2.2.2.2.1]
        exact ⟨hz_Q1, hzH2⟩
      rcases Set.mem_insert_iff.mp hz_st with rfl | hzt
      · omega
      · rw [Set.mem_singleton_iff] at hzt
        subst hzt
        have hi₂_far : R_s_9_2 r₁ + r_hole_9_2 r₁ < H.dist (s i₂.1) (t i₀) :=
          Nat.lt_of_not_le (Finset.mem_filter.mp i₂.2).2
        have ht₁_le : H.dist (t i₁.1) (t i₀) ≤ r_hole_9_2 r₁ := by
          have h := ht_close i₁.1 (Finset.mem_filter.mp i₁.2).1
          dsimp [r_hole_9_2]; omega
        have htri := H.dist_triangle hthin (s i₂.1) (t i₁.1) (t i₀)
        rw [H.dist_comm (s i₂.1) (t i₁.1)] at htri
        omega
    · exact Set.disjoint_left.mp hQ_d hz_Q1 hz_Q2
  -- Pair `{t i.1 | i ∈ I'}` inside the subcubic hole subgraph `K := H.graph.induce U_hole`
  let U_hole : Set α := {w ∈ V(H.graph) | H.dist w (t i₀) ≤ r_hole_9_2 r₁}
  let K : Graph α β := H.graph.induce U_hole
  have hKH : K ≤ H.graph := H.graph.induce_le (fun _ hw => hw.1)
  have hVK : V(K) = U_hole := rfl
  have hK_fin : V(K).Finite := H.toWall.vertexSet_finite.subset hKH.vertexSet_mono
  have hK_deg : ∀ v ∈ V(K), ∀ N : Finset α, (∀ u ∈ N, K.Adj v u) → N.card ≤ 3 :=
    fun v _ N hN => H.toWall.adj_finset_card_le_three hKH v N hN
  have ht₀_K : t i₀ ∈ V(K) := by
    rw [hVK]
    exact ⟨ht₀, by simp⟩
  have ht_inj : Function.Injective t := by
    intro a b hab
    by_contra hne
    have hta : t a ∈ V(Q a) := (hQ_path a).2.1.right_mem
    have htb : t a ∈ V(Q b) := hab ▸ (hQ_path b).2.1.right_mem
    exact Set.disjoint_left.mp (hQ_disj hne) hta htb
  let t_sub : I' → α := fun i => t i.1
  have ht_sub_inj : Function.Injective t_sub :=
    fun i₁ i₂ h => Subtype.ext (ht_inj h)
  let S_hole : Finset α := I'.attach.image t_sub
  have hS_card : 4 * p.choose 2 ≤ S_hole.card := by
    rw [Finset.card_image_of_injective _ ht_sub_inj, Finset.card_attach]
    exact hI'_card
  have hS_reach : ∀ u ∈ S_hole, Nonempty (GraphWalk K (t i₀) u) := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨i, _, rfl⟩
    have ht_H : t i.1 ∈ V(H.graph) := (hQ_path i.1).2.2.2.2.1
    have ht_le : H.dist (t i.1) (t i₀) ≤ r₁ := ht_close i.1 (Finset.mem_filter.mp i.2).1
    obtain ⟨W_t, hW_t⟩ := hfig.exists_walk_dist_le ht_H ht₀
    have hW_t_hole : ∀ w ∈ W_t.reverse.support, w ∈ U_hole := by
      intro w hw
      rw [GraphWalk.support_reverse, List.mem_reverse] at hw
      refine ⟨W_t.mem_vertexSet_of_mem_support hw, ?_⟩
      have h := hW_t w hw
      dsimp [r_hole_9_2]; omega
    have hlink_K : ∀ e x y, e ∈ W_t.reverse.edges → H.graph.IsLink e x y → K.IsLink e x y := by
      intro e x y he hxy
      have hm := walk_isLink_mem_support W_t.reverse he hxy
      rw [Graph.induce_isLink]
      exact ⟨hxy, hW_t_hole x hm.1, hW_t_hole y hm.2⟩
    obtain ⟨W_K_u, _, _⟩ := W_t.reverse.exists_transfer hlink_K hW_t_hole
    exact ⟨W_K_u⟩
  obtain ⟨x_end, y_end, W_K, hxy_mem, hxy_disj⟩ :=
    exists_disjoint_walks_of_subcubic hK_fin hK_deg ht₀_K hS_card hS_reach
  have hWK_disj : ∀ c₁ c₂, c₁ ≠ c₂ →
      ∀ z, z ∈ (W_K c₁).support → z ∉ (W_K c₂).support :=
    fun c₁ c₂ hne z hz₁ hz₂ => Set.disjoint_left.mp (hxy_disj c₁ c₂ hne).2.2.2.2 hz₁ hz₂
  have hex_b : ∀ c : Fin (p.choose 2),
      ∃ b₁ b₂ : I', t_sub b₁ = x_end c ∧ t_sub b₂ = y_end c := by
    intro c
    obtain ⟨b₁, _, hb₁⟩ := Finset.mem_image.mp (hxy_mem c).1
    obtain ⟨b₂, _, hb₂⟩ := Finset.mem_image.mp (hxy_mem c).2.1
    exact ⟨b₁, b₂, hb₁, hb₂⟩
  choose b₁ b₂ hb₁_eq hb₂_eq using hex_b
  have hb_ne : ∀ c, b₁ c ≠ b₂ c := by
    intro c h
    apply (hxy_mem c).2.2
    rw [← hb₁_eq c, ← hb₂_eq c, h]
  have hb_disj : ∀ c₁ c₂, c₁ ≠ c₂ →
      b₁ c₁ ≠ b₁ c₂ ∧ b₁ c₁ ≠ b₂ c₂ ∧ b₂ c₁ ≠ b₁ c₂ ∧ b₂ c₁ ≠ b₂ c₂ := by
    intro c₁ c₂ hne
    obtain ⟨h11, h12, h21, h22, _⟩ := hxy_disj c₁ c₂ hne
    refine ⟨fun h => h11 ?_, fun h => h12 ?_, fun h => h21 ?_, fun h => h22 ?_⟩
    · rw [← hb₁_eq c₁, ← hb₁_eq c₂, h]
    · rw [← hb₁_eq c₁, ← hb₂_eq c₂, h]
    · rw [← hb₂_eq c₁, ← hb₁_eq c₂, h]
    · rw [← hb₂_eq c₁, ← hb₂_eq c₂, h]
  -- Lift each hole walk `W_K c` to `G` and concatenate with `W_arm (b₁ c)` and `(W_arm (b₂ c)).reverse`
  have hex_hole_G : ∀ c : Fin (p.choose 2),
      ∃ W_hole : GraphWalk G (t (b₁ c).1) (t (b₂ c).1),
        {z | z ∈ W_hole.support} = {z | z ∈ (W_K c).support} ∧
        {z | z ∈ W_hole.support} ⊆ U_hole ∧
        Disjoint {e | e ∈ W_hole.edges} E(H'.graph) := by
    intro c
    have hK_G : K ≤ G := hKH.trans hHG
    obtain ⟨W_K', hsupp_K', hedges_K'⟩ :=
      GraphWalk.exists_copy (W_K c) (hb₁_eq c).symm (hb₂_eq c).symm
    obtain ⟨W_hole, hsupp_up, hedges_up⟩ := exists_walk_up_of_le hK_G W_K'
    have hsupp_eq : {z | z ∈ W_hole.support} = {z | z ∈ (W_K c).support} := by
      ext z; simp [hsupp_up, hsupp_K']
    refine ⟨W_hole, hsupp_eq, ?_, ?_⟩
    · intro z hz
      rw [← hVK]
      exact W_K'.mem_vertexSet_of_mem_support (by rwa [← hsupp_up])
    · rw [Set.disjoint_left]
      intro e he_hole he_H'
      rw [ Set.mem_ofPred_eq, hedges_up] at he_hole
      obtain ⟨u, v, huv_H'⟩ := H'.graph.exists_isLink_of_mem_edgeSet he_H'
      have huv_H : H.graph.IsLink e u v := huv_H'.mono hH'_le
      have he_K : e ∈ E(K) := walk_edges_subset_edgeSet W_K' e he_hole
      have huv_K : K.IsLink e u v := (hKH.isLink_iff he_K).mpr huv_H
      have hu_hole : u ∈ U_hole := by rw [← hVK]; exact huv_K.left_mem
      exact hH'_hole u huv_H'.left_mem hu_hole.2
  choose W_hole hW_hole_supp hW_hole_sub hW_hole_edges using hex_hole_G
  -- Construct the simplified `H'.graph`-path `P' c` for each `c : Fin (p.choose 2)`
  let W_total (c : Fin (p.choose 2)) : GraphWalk G (s' (b₁ c)) (s' (b₂ c)) :=
    ((W_arm (b₁ c)).append (W_hole c)).append (W_arm (b₂ c)).reverse
  have hex_P' : ∀ c : Fin (p.choose 2),
      ∃ P' : Graph α β,
        IsHPathWithEnds G H'.graph P' (s' (b₁ c)) (s' (b₂ c)) ∧
        V(P') ⊆ {z | z ∈ (W_arm (b₁ c)).support} ∪
          {z | z ∈ (W_hole c).support} ∪ {z | z ∈ (W_arm (b₂ c)).support} := by
    intro c
    obtain ⟨P', hP'_path, hsupp_sub, hedges_sub⟩ :=
      exists_isGraphPathWithEnds_of_walk (W_total c)
    have hVP'_sub : V(P') ⊆ {z | z ∈ (W_arm (b₁ c)).support} ∪
        {z | z ∈ (W_hole c).support} ∪ {z | z ∈ (W_arm (b₂ c)).support} := by
      intro z hz
      have hz_tot : z ∈ (W_total c).support := hsupp_sub hz
      rcases GraphWalk.mem_support_append _ _ hz_tot with hz_1h | hz_2
      · rcases GraphWalk.mem_support_append _ _ hz_1h with hz_1 | hz_h
        · exact Or.inl (Or.inl hz_1)
        · exact Or.inl (Or.inr hz_h)
      · rw [GraphWalk.support_reverse, List.mem_reverse] at hz_2
        exact Or.inr hz_2
    have hs'_ne : s' (b₁ c) ≠ s' (b₂ c) := by
      intro heq
      have h1 : s' (b₁ c) ∈ (W_arm (b₁ c)).support := (W_arm (b₁ c)).start_mem_support
      have h2 : s' (b₁ c) ∈ (W_arm (b₂ c)).support := by
        rw [heq]; exact (W_arm (b₂ c)).start_mem_support
      exact Set.disjoint_left.mp (hW_arm_disj (b₁ c) (b₂ c) (hb_ne c)) h1 h2
    have hVP'_H' : V(P') ∩ V(H'.graph) = {s' (b₁ c), s' (b₂ c)} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨hzP', hzH'⟩
        rcases hVP'_sub hzP' with (hz1 | hzh) | hz2
        · have h : z ∈ {z | z ∈ (W_arm (b₁ c)).support} ∩ V(H'.graph) := ⟨hz1, hzH'⟩
          rw [hW_arm_H' (b₁ c), Set.mem_singleton_iff] at h
          exact Or.inl h
        · exact False.elim (hH'_hole z hzH' (hW_hole_sub c hzh).2)
        · have h : z ∈ {z | z ∈ (W_arm (b₂ c)).support} ∩ V(H'.graph) := ⟨hz2, hzH'⟩
          rw [hW_arm_H' (b₂ c), Set.mem_singleton_iff] at h
          exact Or.inr h
      · rintro (rfl | rfl)
        · exact ⟨hP'_path.left_mem, hs'_H' (b₁ c)⟩
        · exact ⟨hP'_path.right_mem, hs'_H' (b₂ c)⟩
    have hEP'_H' : Disjoint E(P') E(H'.graph) := by
      rw [Set.disjoint_left]
      intro e heP' heH'
      have he_tot : e ∈ (W_total c).edges := hedges_sub heP'
      simp only [W_total, GraphWalk.edges_append, GraphWalk.edges_reverse,
        List.mem_append, List.mem_reverse] at he_tot
      rcases he_tot with (he1 | heh) | he2
      · exact Set.disjoint_left.mp (hW_arm_edges (b₁ c)) he1 heH'
      · exact Set.disjoint_left.mp (hW_hole_edges c) heh heH'
      · exact Set.disjoint_left.mp (hW_arm_edges (b₂ c)) he2 heH'
    exact ⟨P', ⟨hH'_le.trans hHG, hP'_path, hs'_ne, hs'_H' (b₁ c), hs'_H' (b₂ c),
      hVP'_H', hEP'_H'⟩, hVP'_sub⟩
  choose P' hP' hVP'_sub using hex_P'
  -- Show `Pairwise (Disjoint V(P' c₁) V(P' c₂))`
  have harm_hole_disj : ∀ (b : I') (c : Fin (p.choose 2)),
      t_sub b ∈ (W_K c).support →
      ∀ c' : Fin (p.choose 2), c ≠ c' →
        Disjoint {z | z ∈ (W_arm b).support} {z | z ∈ (W_hole c').support} := by
    intro b c htb_in c' hne
    rw [Set.disjoint_left]
    intro z hz_arm hz_hole
    have hz_in : z ∈ {z | z ∈ (W_arm b).support} ∩ U_hole :=
      ⟨hz_arm, hW_hole_sub c' hz_hole⟩
    rw [hW_arm_hole b, Set.mem_singleton_iff] at hz_in
    subst hz_in
    have htb_c' : t_sub b ∈ (W_K c').support := by
      change t b.1 ∈ {z | z ∈ (W_K c').support}
      rwa [← hW_hole_supp c']
    exact hWK_disj c c' hne (t_sub b) htb_in htb_c'
  have hP'_disj : Pairwise (fun c₁ c₂ => Disjoint V(P' c₁) V(P' c₂)) := by
    intro c₁ c₂ hne
    obtain ⟨h11, h12, h21, h22⟩ := hb_disj c₁ c₂ hne
    have htb1_c1 : t_sub (b₁ c₁) ∈ (W_K c₁).support := by
      rw [hb₁_eq c₁]; exact (W_K c₁).start_mem_support
    have htb2_c1 : t_sub (b₂ c₁) ∈ (W_K c₁).support := by
      rw [hb₂_eq c₁]; exact (W_K c₁).end_mem_support
    have htb1_c2 : t_sub (b₁ c₂) ∈ (W_K c₂).support := by
      rw [hb₁_eq c₂]; exact (W_K c₂).start_mem_support
    have htb2_c2 : t_sub (b₂ c₂) ∈ (W_K c₂).support := by
      rw [hb₂_eq c₂]; exact (W_K c₂).end_mem_support
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    rcases hVP'_sub c₁ hz₁ with (h1a | h1h) | h1b <;>
      rcases hVP'_sub c₂ hz₂ with (h2a | h2h) | h2b
    · exact Set.disjoint_left.mp (hW_arm_disj _ _ h11) h1a h2a
    · exact Set.disjoint_left.mp (harm_hole_disj (b₁ c₁) c₁ htb1_c1 c₂ hne) h1a h2h
    · exact Set.disjoint_left.mp (hW_arm_disj _ _ h12) h1a h2b
    · exact Set.disjoint_left.mp (harm_hole_disj (b₁ c₂) c₂ htb1_c2 c₁ hne.symm) h2a h1h
    · have hz_K1 : z ∈ (W_K c₁).support := by
        change z ∈ {z | z ∈ (W_K c₁).support}
        rwa [← hW_hole_supp c₁]
      have hz_K2 : z ∈ (W_K c₂).support := by
        change z ∈ {z | z ∈ (W_K c₂).support}
        rwa [← hW_hole_supp c₂]
      exact hWK_disj c₁ c₂ hne z hz_K1 hz_K2
    · exact Set.disjoint_left.mp (harm_hole_disj (b₂ c₂) c₂ htb2_c2 c₁ hne.symm) h2b h1h
    · exact Set.disjoint_left.mp (hW_arm_disj _ _ h21) h1b h2a
    · exact Set.disjoint_left.mp (harm_hole_disj (b₂ c₁) c₁ htb2_c1 c₂ hne) h1b h2h
    · exact Set.disjoint_left.mp (hW_arm_disj _ _ h22) h1b h2b
  -- Distance transfer in `H'` between `s' i₁` and `s' i₂` for `i₁ ≠ i₂ : I'`
  have hdist_transfer : ∀ i₁ i₂ : I', i₁ ≠ i₂ → r₀ ≤ H'.dist (s' i₁) (s' i₂) := by
    intro i₁ i₂ hne
    have h1 : r ≤ H.dist (s i₁.1) (s i₂.1) := hs_dist i₁.1 i₂.1 (Subtype.coe_ne_coe.mpr hne)
    have hd1 : H.dist (s' i₁) (s i₁.1) ≤ R_s_9_2 r₁ := hs'_dist i₁
    have hd2 : H.dist (s' i₂) (s i₂.1) ≤ R_s_9_2 r₁ := hs'_dist i₂
    have htri1 := H.dist_triangle hthin (s i₁.1) (s' i₁) (s i₂.1)
    have htri2 := H.dist_triangle hthin (s' i₁) (s' i₂) (s i₂.1)
    rw [H.dist_comm (s i₁.1) (s' i₁)] at htri1
    have h2 : H.dist (s' i₁) (s' i₂) ≤ H'.dist (s' i₁) (s' i₂) + (4 * r_hole_9_2 r₁ + 4) := by
      dsimp [DrawnWall.dist]
      rw [hH'_vp]
      exact hH'_dist (H.vertexPoint (s' i₁)) (H.vertexPoint (s' i₂))
    omega
  exact hr₀ H' hH'_fig (hH'_le.trans hHG) P' (fun c => s' (b₁ c)) (fun c => s' (b₂ c))
    hP' hP'_disj
    (fun c₁ c₂ hne => by
      obtain ⟨h11, h12, h21, h22⟩ := hb_disj c₁ c₂ hne
      exact ⟨hdist_transfer _ _ h11, hdist_transfer _ _ h12,
             hdist_transfer _ _ h21, hdist_transfer _ _ h22⟩)
    (fun c => hdist_transfer _ _ (hb_ne c))

/-- Claim (8) in the proof of **Graph Minors XIII, (9.2)** (page 101):
"(8) *If $n$ is sufficiently large, then there exists $I \subseteq \{1, \dots, n\}$ as in (5), (6),
or (7).*" -/
theorem lemma_9_2_claim_8 {H : DrawnWall α β} {n r₁ n₁ n₂ n₃ : ℕ}
    (hn : n₂ + n₁ * (n₃ + 1) ≤ n)
    (s t : Fin n → α) :
    (∃ I : Finset (Fin n), I.card = n₁ ∧
      (∀ i ∈ I, r₁ ≤ H.dist (s i) (t i)) ∧
      (∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → r₁ ≤ H.dist (t i) (t i'))) ∨
    (∃ I : Finset (Fin n), I.card = n₂ ∧
      ∀ i ∈ I, H.dist (s i) (t i) ≤ r₁) ∨
    (∃ (i₀ : Fin n) (I : Finset (Fin n)), i₀ ∉ I ∧ I.card = n₃ ∧
      ∀ i ∈ I, H.dist (t i) (t i₀) ≤ r₁) := by
  let A := (Finset.univ : Finset (Fin n)).filter (fun i => H.dist (s i) (t i) ≤ r₁)
  let B := (Finset.univ : Finset (Fin n)).filter (fun i => ¬ H.dist (s i) (t i) ≤ r₁)
  have hAB_card : A.card + B.card = n := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => H.dist (s i) (t i) ≤ r₁)
    simpa [A, B] using h
  by_cases hA : n₂ ≤ A.card
  · -- Outcome (6)
    obtain ⟨I, hIA, hI_card⟩ := Finset.exists_subset_card_eq hA
    refine Or.inr (Or.inl ⟨I, hI_card, ?_⟩)
    intro i hi
    exact (Finset.mem_filter.mp (hIA hi)).2
  · have hB_card : n₁ * (n₃ + 1) ≤ B.card := by omega
    by_cases hhigh : ∃ i₀ ∈ B,
        n₃ ≤ (B.filter (fun i => i ≠ i₀ ∧ H.dist (t i₀) (t i) ≤ r₁)).card
    · -- Outcome (7)
      rcases hhigh with ⟨i₀, _, hi₀_deg⟩
      obtain ⟨I, hI_sub, hI_card⟩ := Finset.exists_subset_card_eq hi₀_deg
      refine Or.inr (Or.inr ⟨i₀, I, ?_, hI_card, ?_⟩)
      · intro hi₀I
        exact (Finset.mem_filter.mp (hI_sub hi₀I)).2.1 rfl
      · intro i hi
        have h := (Finset.mem_filter.mp (hI_sub hi)).2.2
        rw [H.dist_comm]
        exact h
    · -- Outcome (5)
      push Not at hhigh
      have hdeg : ∀ i₀ ∈ B,
          (B.filter (fun i => i ≠ i₀ ∧ H.dist (t i₀) (t i) ≤ r₁)).card ≤ n₃ := by
        intro i₀ hi₀
        have hlt := hhigh i₀ hi₀
        omega
      have hsym : ∀ ⦃i i' : Fin n⦄, H.dist (t i) (t i') ≤ r₁ → H.dist (t i') (t i) ≤ r₁ := by
        intro i i' h
        rw [H.dist_comm]
        exact h
      obtain ⟨J, hJB, hJ_card, hJ_ind⟩ :=
        exists_independent_finset_card_mul_ge
          (fun i i' : Fin n => H.dist (t i) (t i') ≤ r₁)
          hsym B n₃ hdeg
      have hn₁_le_J : n₁ ≤ J.card := by
        have hmul : n₁ * (n₃ + 1) ≤ J.card * (n₃ + 1) := by
          calc
            n₁ * (n₃ + 1) ≤ B.card := hB_card
            _ ≤ (n₃ + 1) * J.card := hJ_card
            _ = J.card * (n₃ + 1) := Nat.mul_comm _ _
        exact Nat.le_of_mul_le_mul_right hmul (Nat.succ_pos n₃)
      obtain ⟨I, hIJ, hI_card⟩ := Finset.exists_subset_card_eq hn₁_le_J
      refine Or.inl ⟨I, hI_card, ?_, ?_⟩
      · intro i hi
        have hiB : i ∈ B := hJB (hIJ hi)
        have hnot : ¬ H.dist (s i) (t i) ≤ r₁ := (Finset.mem_filter.mp hiB).2
        omega
      · intro i hi i' hi' hne
        have hnot : ¬ H.dist (t i) (t i') ≤ r₁ :=
          hJ_ind i (hIJ hi) i' (hIJ hi') hne
        omega

/-- **Graph Minors XIII, (9.2)** (page 99):
"For any $l \ge 3$, and $m, p \ge 0$, there exist $k, r \ge 0$ such that the following holds. Let
$H$ be a wall with distance function $d$ in a graph $G$, and let $H_1, \dots, H_k$ be non-dividing
subwalls of $H$, with
$$d(H_i, H_j) \ge r \quad (1 \le i < j \le k).$$
Then either there is an $(l, m)$-star over $H$ or $G$ has a $K_p$-minor. Moreover, there is an algorithm with running time $\le C\varepsilon(G)$, where $C$ depends only on $l, m, p$ and the height of $H$, which given such subwalls $H_1, \dots, H_k$, finds either an $(l, m)$-star over $H$ or a model of $K_p$ in $G$." -/
theorem theorem_9_2_proof
    (l m p : ℕ) (hl : 3 ≤ l) :
    ∃ k r : ℕ,
      ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β)
        (H_sub : Fin k → Wall α β),
        H.IsFigure1 →
        IsWallIn G H.toWall →
        (∀ i : Fin k, IsNonDividingSubwall G H.toWall (H_sub i)) →
        (∀ i j : Fin k, i ≠ j → r ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
        (∃ (S : Graph α β) (v : α), IsLMStarOver G H l m S v) ∨
          HasGraphModel (GM16.completeGraph p) G := by
  let r₀ : ℕ := Classical.choose.{1} (theorem_7_4_proof.{u, v} p)
  let r₁ := 2 * r₀
  let k₉₁ : ℕ := Classical.choose.{1} (theorem_9_1_proof.{u, v} p)
  let r₉₁ : ℕ := Classical.choose.{1} (Classical.choose_spec.{1} (theorem_9_1_proof.{u, v} p))
  let n₁ := 3 * p.choose 2
  let n₂ := k₉₁ + 1
  let n₃ := 4 * p.choose 2 + 1
  let n := n₂ + n₁ * (n₃ + 1)
  let r := max m (max (r₀ + 2 * R_s_9_2 r₁ + 4 * r_hole_9_2 r₁ + 10) (r₉₁ + 12 * r₁ + 64))
  let k := n * (l - 1) ^ 2
  refine ⟨k, r, ?_⟩
  intro α β G H H_sub hfig hHG hnondiv hdist
  by_cases hp : p < 2
  · exact Or.inr (hasGraphModel_completeGraph_of_lt_two hp hHG)
  · have hrm : m ≤ r := le_max_left _ _
    have hr_enlarge : r₉₁ + 12 * r₁ + 64 ≤ r :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hr_pos : 0 < r := by
      have h : 0 < r₉₁ + 12 * r₁ + 64 := by omega
      exact lt_of_lt_of_le h hr_enlarge
    have hsub : ∀ i : Fin k, (H_sub i).IsSubwallOf H.toWall := fun i => (hnondiv i).1
    have hdisj_subwalls : Pairwise (fun i₁ i₂ : Fin k =>
        Disjoint V((H_sub i₁).graph) V((H_sub i₂).graph)) :=
      fun i₁ i₂ hne => disjoint_of_pos_wallSubgraphDist (lt_of_lt_of_le hr_pos (hdist i₁ i₂ hne))
    -- Construct the minimal non-dividing spider forest `F` inside the proof!
    obtain ⟨F, hmin⟩ :=
      PartialSpiderForest.exists_minimal
        (PartialSpiderForest.exists_partialSpiderForest hHG hnondiv hdisj_subwalls k)
    -- Either some vertex of `F` has valency `≥ l` (giving an `(l, m)`-star by Claim (3)),
    -- or all vertices of `F` have valency `< l` (giving `n` paths by Claim (4)).
    by_cases hhigh :
        (∃ j : Fin F.t, l ≤ (F.spiders j).leaves.card) ∨
        (∃ (v : α) (T : Finset (Fin F.t)), l ≤ T.card ∧ ∀ j ∈ T, v ∈ (F.spiders j).leaves)
    · exact Or.inl (lemma_9_2_claim_3 hHG hl hrm hsub hdisj_subwalls hdist hmin hhigh)
    · push Not at hhigh
      have hleaves_le : ∀ j : Fin F.t, (F.spiders j).leaves.card ≤ l - 1 := by
        intro j
        have hlt := hhigh.1 j
        omega
      have hdeg_le : ∀ v : α,
          (Finset.univ.filter (fun j : Fin F.t => v ∈ (F.spiders j).leaves)).card ≤ l - 1 := by
        intro v
        by_contra hgt
        have hge : l ≤ (Finset.univ.filter (fun j : Fin F.t => v ∈ (F.spiders j).leaves)).card := by
          omega
        obtain ⟨j, hj⟩ := hhigh.2 v
          (Finset.univ.filter (fun j : Fin F.t => v ∈ (F.spiders j).leaves)) hge
        exact hj.2 (Finset.mem_filter.mp hj.1).2
      obtain ⟨σ, Q, s, t, hQ_spec, hQ_disj, hst_in_out, _⟩ :=
        lemma_9_2_claim_4 hHG hl le_rfl hsub hdisj_subwalls hmin hleaves_le hdeg_le
      have hQ_path : ∀ a : Fin n, IsHPathWithEnds G H.graph (Q a) (s a) (t a) :=
        fun a => (hQ_spec a).2
      have hs_dist : ∀ a₁ a₂ : Fin n, a₁ ≠ a₂ → r ≤ H.dist (s a₁) (s a₂) := by
        intro a₁ a₂ hne
        have hsa₁ : s a₁ ∈ V((H_sub (σ a₁)).graph) := (hst_in_out a₁).1.1
        have hsa₂ : s a₂ ∈ V((H_sub (σ a₂)).graph) := (hst_in_out a₂).1.1
        exact le_dist_of_le_wallSubgraphDist (hdist (σ a₁) (σ a₂) (σ.injective.ne hne)) hsa₁ hsa₂
      have hr₁_le_r : r₁ ≤ r := by
        have h : r₁ ≤ r₉₁ + 12 * r₁ + 64 := by omega
        exact h.trans hr_enlarge
      have hs_dist_r₁ : ∀ a₁ a₂ : Fin n, a₁ ≠ a₂ → r₁ ≤ H.dist (s a₁) (s a₂) :=
        fun a₁ a₂ hne => hr₁_le_r.trans (hs_dist a₁ a₂ hne)
      -- Apply Claim (8) to split into Claim (5), Claim (6), or Claim (7)
      rcases lemma_9_2_claim_8 (H := H) (r₁ := r₁) (n₁ := n₁) (n₂ := n₂) (n₃ := n₃)
          le_rfl s t with
        ⟨I, hI_card, hst_ge, htt_ge⟩ | ⟨I, hI_card, hst_le⟩ | ⟨i₀, I, hi₀_not, hI_card, ht_close⟩
      · -- Claim (5)
        refine Or.inr (lemma_9_2_claim_5 hfig hHG
          (fun P s' t' hP hP_disj hfar hst' =>
            (Classical.choose_spec.{1} (theorem_7_4_proof.{u, v} p)) G H hfig hHG P s' t' hP hP_disj hfar hst')
          Q s t hQ_path hQ_disj hs_dist_r₁ I (le_of_eq hI_card.symm) hst_ge htt_ge)
      · -- Claim (6)
        refine Or.inr (lemma_9_2_claim_6 hfig hHG hr_enlarge H_sub hsub hdist σ
          Q s t hQ_path hQ_disj hst_in_out I (le_of_eq hI_card.symm) hst_le
          (fun H' P' Q' hH'_sub hH'_far hcross hVPQ_inter hVPQ_disj =>
            (Classical.choose_spec.{1} (Classical.choose_spec.{1} (theorem_9_1_proof.{u, v} p)))
              G H H' P' Q' hfig hHG hH'_sub hH'_far hcross hVPQ_inter hVPQ_disj))
      · -- Claim (7)
        have ht₀_H : t i₀ ∈ V(H.graph) := (hst_in_out i₀).2.1
        have hp_pos : 0 < p.choose 2 := Nat.choose_pos (by omega)
        have hn2 : 2 ≤ n := by
          have h1 : 2 ≤ n₁ := by dsimp [n₁]; omega
          have h2 : n₁ ≤ n₁ * (n₃ + 1) := Nat.le_mul_of_pos_right _ (by omega)
          have h3 : n₁ * (n₃ + 1) ≤ n := Nat.le_add_left _ _
          omega
        have hr_far : r₀ + 2 * R_s_9_2 r₁ + 4 * r_hole_9_2 r₁ + 10 ≤ r :=
          (le_max_left _ _).trans (le_max_right _ _)
        refine Or.inr (lemma_9_2_claim_7 hfig hHG
          (fun H' hH'_fig hH'_G P s' t' hP hP_disj hfar hst' =>
            (Classical.choose_spec.{1} (theorem_7_4_proof.{u, v} p)) G H' hH'_fig hH'_G P s' t' hP hP_disj hfar hst')
          hn2 hr_far Q s t hQ_path hQ_disj hs_dist i₀ ht₀_H I hi₀_not
          (le_of_eq hI_card.symm) ht_close)

/-- `GM13Theorem92Statement` holds. -/
theorem theorem_9_2_parallel :
    GM13Theorem92Statement.{u, v} :=
  theorem_9_2_proof

/-! ## (9.3) and Algorithm (9.4): Finding Many Dividing Subwalls after Deleting `< binom(p, 2)` Vertices (pages 101–102) -/

/-- A subwall `W'` of `W` (`hsub : W'.IsSubwallOf W`) is non-dividing in `G` if and only if it is
not dividing in `G` (Graph Minors XIII, Section 9, page 99). -/
theorem not_isDividingSubwall_iff_isNonDividingSubwall
    {G : Graph α β} {W W' : Wall α β} (hsub : W'.IsSubwallOf W) :
    ¬ IsDividingSubwall G W W' ↔ IsNonDividingSubwall G W W' := by
  dsimp [IsDividingSubwall, IsNonDividingSubwall]
  push Not
  exact ⟨fun h => ⟨hsub, h hsub⟩, fun ⟨_, h⟩ _ => h⟩

/-- In the graph `G' = (G \ X) ∪ H`, every edge of `E(G') \ E(H)` is an edge of `G \ X`, so both of
its endpoints lie in `V(G) \ X`. Consequently, no `(l, m)`-star over `H` in `G'` can have its center
in `X` (proof of (9.3), Step (2), page 102). -/
theorem not_mem_deleted_of_isLMStarOver_union
    {G : Graph α β} {H : DrawnWall α β} {X : Set α} {l m : ℕ} {S : Graph α β} {v : α}
    (hHG : H.graph ≤ G)
    (hstar : IsLMStarOver (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H l m S v) :
    v ∉ X := by
  rcases hstar with ⟨hl, _, _, P, u, _, hP, _, _⟩
  let i₀ : Fin l := ⟨0, by omega⟩
  obtain ⟨hP₀, hu₀_ne, _, _, hE_disj⟩ := hP i₀
  rcases hP₀ with ⟨hP₀_le, w, _, _, _⟩
  cases w with
  | nil _ =>
    exact False.elim (hu₀_ne rfl)
  | @cons _ y _ e hlink _ =>
    have he_P₀ : e ∈ E(P i₀) := hlink.edge_mem
    have he_not_H : e ∉ E(H.graph) := Set.disjoint_left.mp hE_disj he_P₀
    have hlink_G' : (subgraphUnion G (G.induce (V(G) \ X)) H.graph).IsLink e v y :=
      hlink.mono hP₀_le
    have hle_ind : G.induce (V(G) \ X) ≤ G := G.induce_le sdiff_subset
    rw [subgraphUnion_isLink hle_ind hHG] at hlink_G'
    rcases hlink_G' with hlink_ind | hlink_H
    · exact hlink_ind.left_mem.2
    · exact False.elim (he_not_H hlink_H.edge_mem)

/-- **Graph Minors XIII, Algorithm (9.4)** (page 102):
"(9.4) Algorithm.
*Input:* A graph $G$, a wall $H \subseteq G$ with distance function $d$, and subwalls
$H_1, \dots, H_t$ of $H$ with $d(H_i, H_j) \ge r$ ($1 \le i < j \le t$).
*Output:* Either
(i) a model of $K_p$ in $G$, or
(ii) a subset $X \subseteq V(G)$ with $|X| < \binom{p}{2}$ and a subset $I \subseteq \{1, \dots, t\}$
with $|I| \ge t - k$ such that for all $i \in I$, $H_i$ is dividing in $(G \setminus X) \cup H$."

Formalized as the recursive step of Algorithm (9.4): given `s ≤ p.choose 2` `(l, m)`-stars over
`H` in `G` with distinct centers `v : Fin s → α`, the recursion terminates in at most
`p.choose 2 - s` steps with either a `K_p`-model in `G` or a set `X ⊆ V(G)` of `< p.choose 2`
star centers and a subset `I ⊆ Finset.univ` of `≥ t - k` indices such that `H_sub i` is dividing in
`(G \ X) ∪ H` for all `i ∈ I`. -/
theorem theorem_9_4_proof
    {G : Graph α β} {H : DrawnWall α β} {p l m k r t : ℕ}
    (_hp : 2 ≤ p) (_hl : 3 ≤ l)
    (hHG : H.graph ≤ G)
    (H_sub : Fin t → Wall α β)
    (hsub : ∀ i : Fin t, (H_sub i).IsSubwallOf H.toWall)
    (_hdist : ∀ i j : Fin t, i ≠ j → r ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph)
    (h77_step : ∀ (S : Fin (p.choose 2) → Graph α β) (v : Fin (p.choose 2) → α),
      (∀ a, IsLMStarOver G H l m (S a) (v a)) →
      Function.Injective v →
      HasGraphModel (GM16.completeGraph p) G)
    (h92_step : ∀ (X : Set α) (emb : Fin k ↪ Fin t),
      (∀ a : Fin k, IsNonDividingSubwall
        (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H.toWall (H_sub (emb a))) →
      (∃ (S : Graph α β) (v : α),
        IsLMStarOver (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H l m S v) ∨
        HasGraphModel (GM16.completeGraph p) G) :
    ∀ (rem s : ℕ), rem = p.choose 2 - s → s ≤ p.choose 2 →
      ∀ (S : Fin s → Graph α β) (v : Fin s → α),
        (∀ a : Fin s, IsLMStarOver G H l m (S a) (v a)) →
        Function.Injective v →
        HasGraphModel (GM16.completeGraph p) G ∨
          ∃ (X : Set α) (I : Finset (Fin t)),
            X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
            t - k ≤ I.card ∧
            ∀ i ∈ I, IsDividingSubwall
              (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H.toWall (H_sub i) := by
  intro rem
  induction rem with
  | zero =>
    intro s hrem hs S v hstar hv_inj
    have hs_eq : s = p.choose 2 := by omega
    subst hs_eq
    exact Or.inl (h77_step S v hstar hv_inj)
  | succ rem' ih =>
    intro s hrem hs S v hstar hv_inj
    have hs_lt : s < p.choose 2 := by omega
    let X : Set α := Set.range v
    have hX_sub : X ⊆ V(G) := by
      rintro x ⟨a, rfl⟩
      exact (hstar a).center_mem
    have hX_fin : X.Finite := Set.finite_range v
    have hX_ncard : X.ncard < p.choose 2 := by
      have hle : X.ncard ≤ s := by
        have hrange : X = v '' (Set.univ : Set (Fin s)) := Set.image_univ.symm
        rw [hrange]
        exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
      omega
    let G' := subgraphUnion G (G.induce (V(G) \ X)) H.graph
    have hle_ind : G.induce (V(G) \ X) ≤ G := G.induce_le sdiff_subset
    have hG'_le : G' ≤ G := subgraphUnion_le hle_ind hHG
    -- Step (3): Test which `H_i`'s are dividing in `G'`
    let I_div := (Finset.univ : Finset (Fin t)).filter
      (fun i => IsDividingSubwall G' H.toWall (H_sub i))
    let I_nondiv := (Finset.univ : Finset (Fin t)).filter
      (fun i => ¬ IsDividingSubwall G' H.toWall (H_sub i))
    have hcard_sum : I_div.card + I_nondiv.card = t := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin t)))
        (p := fun i => IsDividingSubwall G' H.toWall (H_sub i))
      simpa [I_div, I_nondiv] using h
    by_cases hdiv : t - k ≤ I_div.card
    · refine Or.inr ⟨X, I_div, hX_sub, hX_fin, hX_ncard, hdiv, ?_⟩
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    · -- Step (4): Otherwise `k ≤ I_nondiv.card`; choose `k` non-dividing subwalls and apply (9.2)
      have hk_le : k ≤ I_nondiv.card := by omega
      let embN : Fin k ↪ I_nondiv :=
        (Fin.castLEEmb hk_le).trans I_nondiv.equivFin.symm.toEmbedding
      let emb : Fin k ↪ Fin t := embN.trans (Function.Embedding.subtype _)
      have hnondiv_emb : ∀ a : Fin k, IsNonDividingSubwall G' H.toWall (H_sub (emb a)) := by
        intro a
        have hnot : ¬ IsDividingSubwall G' H.toWall (H_sub (emb a)) :=
          (Finset.mem_filter.mp (embN a).2).2
        exact (not_isDividingSubwall_iff_isNonDividingSubwall (hsub (emb a))).mp hnot
      rcases h92_step X emb hnondiv_emb with ⟨S_new, v_new, hstar_new⟩ | hModel
      · have hv_not_X : v_new ∉ X := not_mem_deleted_of_isLMStarOver_union hHG hstar_new
        have hstar_G : IsLMStarOver G H l m S_new v_new := hstar_new.mono_graph hG'_le
        let S' : Fin (s + 1) → Graph α β := Fin.snoc S S_new
        let v' : Fin (s + 1) → α := Fin.snoc v v_new
        have hstar' : ∀ a : Fin (s + 1), IsLMStarOver G H l m (S' a) (v' a) := by
          intro a
          refine Fin.lastCases ?_ ?_ a
          · simpa [S', v'] using hstar_G
          · intro b
            simpa [S', v'] using hstar b
        have hv'_inj : Function.Injective v' := by
          intro a₁ a₂
          refine Fin.lastCases ?_ (fun b₁ => ?_) a₁
          · refine Fin.lastCases (fun _ => rfl) (fun b₂ heq' => ?_) a₂
            simp only [v', Fin.snoc_last, Fin.snoc_castSucc] at heq'
            exact False.elim (hv_not_X ⟨b₂, heq'.symm⟩)
          · refine Fin.lastCases (fun heq' => ?_) (fun b₂ heq' => ?_) a₂
            · simp only [v', Fin.snoc_last, Fin.snoc_castSucc] at heq'
              exact False.elim (hv_not_X ⟨b₁, heq'⟩)
            · simp only [v', Fin.snoc_castSucc] at heq'
              exact congrArg Fin.castSucc (hv_inj heq')
        exact ih (s + 1) (by omega) (by omega) S' v' hstar' hv'_inj
      · exact Or.inl hModel

/-- **Graph Minors XIII, (9.3)** (page 101):
"For any $p \ge 0$ there exists $k, r \ge 0$ such that there is an algorithm as in (9.4), with
running time $\le C\varepsilon(G)$, where $C$ depends on $p, t$, and the height of $H$." -/
theorem theorem_9_3_proof
    (p : ℕ) :
    ∃ k r : ℕ,
      ∀ {α : Type u} {β : Type v} {t : ℕ} {G : Graph α β} {H : DrawnWall α β}
        (H_sub : Fin t → Wall α β),
        H.IsFigure1 →
        H.graph ≤ G →
        (∀ i : Fin t, (H_sub i).IsSubwallOf H.toWall) →
        (∀ i j : Fin t, i ≠ j → r ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
        HasGraphModel (GM16.completeGraph p) G ∨
          ∃ (X : Set α) (I : Finset (Fin t)),
            X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
            t - k ≤ I.card ∧
            ∀ i ∈ I, IsDividingSubwall
              (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H.toWall (H_sub i) := by
  by_cases hp : p < 2
  · refine ⟨0, 0, ?_⟩
    intro α β t G H H_sub _ hHG _ _
    exact Or.inl (hasGraphModel_completeGraph_of_lt_two hp hHG)
  · have hp2 : 2 ≤ p := by omega
    obtain ⟨l, m, hl, h77_p⟩ := theorem_7_7_proof.{u, v} p hp2
    obtain ⟨k, r, h92_p⟩ := theorem_9_2_proof.{u, v} l m p hl
    refine ⟨k, r, ?_⟩
    intro α β t G H H_sub hfig hHG hsub hdist
    have h77_step : ∀ (S : Fin (p.choose 2) → Graph α β) (v : Fin (p.choose 2) → α),
        (∀ a, IsLMStarOver G H l m (S a) (v a)) →
        Function.Injective v →
        HasGraphModel (GM16.completeGraph p) G :=
      fun S v hstar hv_inj => h77_p G H hfig hHG S v hstar hv_inj
    have h92_step : ∀ (X : Set α) (emb : Fin k ↪ Fin t),
        (∀ a : Fin k, IsNonDividingSubwall
          (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H.toWall (H_sub (emb a))) →
        (∃ (S : Graph α β) (v : α),
          IsLMStarOver (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H l m S v) ∨
          HasGraphModel (GM16.completeGraph p) G := by
      intro X emb hnondiv
      let G' := subgraphUnion G (G.induce (V(G) \ X)) H.graph
      have hle_ind : G.induce (V(G) \ X) ≤ G := G.induce_le sdiff_subset
      have hG'_le : G' ≤ G := subgraphUnion_le hle_ind hHG
      have hHG' : H.graph ≤ G' := le_subgraphUnion_right hle_ind hHG
      have hdist_emb : ∀ a b : Fin k, a ≠ b →
          r ≤ wallSubgraphDist H (H_sub (emb a)).graph (H_sub (emb b)).graph :=
        fun a b hab => hdist (emb a) (emb b) (emb.injective.ne hab)
      rcases h92_p G' H (fun a => H_sub (emb a)) hfig hHG' hnondiv hdist_emb with
        hstar | hMod
      · exact Or.inl hstar
      · exact Or.inr (hMod.mono_right hG'_le)
    exact theorem_9_4_proof hp2 hl hHG H_sub hsub hdist h77_step h92_step
      (p.choose 2) 0 (Nat.sub_zero _) (Nat.zero_le _)
      Fin.elim0 Fin.elim0 (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)

end GraphMinor.GM13
