module

public import GraphMinor.GM13.Section8

/-!
# Graph Minors XIII, Section 9 (Part a): Subwalls, Compasses, and Dividing Subwalls (9.5)

This file formalizes the basic properties of subwalls, compasses, and dividing subwalls from
Section 9 ("Finding a Flat Section of a Wall") of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110
(pages 97–103), culminating in the proof of **(9.5)** (`theorem_9_5`).
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function
open Graph SimpleGraph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM14

universe u v

variable {α : Type u} {β : Type v}

/-! ## Perimeter, Inside Vertices, and Compass of a Wall -/

/-- Every defining path of `W.perimeter` is a subgraph of `W.graph`. -/
theorem Wall.perimeter_paths_le (W : Wall α β) :
    ∀ P ∈ {P : Graph α β | ∃ (e₀ : Sym2 (ℕ × ℕ)) (he₀ : e₀ ∈ E(elementaryWallPerimeter W.height)),
      have he₀' : e₀ ∈ E(elementaryWall W.height) :=
        let ⟨p, q, hpq⟩ := he₀; ⟨p, q, hpq.1.1, hpq.1.2⟩
      P = W.subdivisionPaths (W.baseIso.edgeEquiv ⟨e₀, he₀'⟩).1},
      P ≤ W.graph := by
  rintro P ⟨e₀, he₀, rfl⟩
  have he₀' : e₀ ∈ E(elementaryWall W.height) :=
    let ⟨p, q, hpq⟩ := he₀; ⟨p, q, hpq.1.1, hpq.1.2⟩
  let e_sub := W.baseIso.edgeEquiv ⟨e₀, he₀'⟩
  rcases W.path_of_edge e_sub.1 e_sub.2 with ⟨u, v, _, hpath, _⟩
  exact hpath.1

/-- The perimeter `W.perimeter` is a subgraph of `W.graph`. -/
theorem Wall.perimeter_le (W : Wall α β) : W.perimeter ≤ W.graph :=
  subgraphSUnion_le W.perimeter_paths_le

/-- `V(W.perimeter) ⊆ V(W.graph)`. -/
theorem Wall.perimeter_vertexSet_subset (W : Wall α β) : V(W.perimeter) ⊆ V(W.graph) :=
  W.perimeter_le.vertexSet_mono

/-- `W.insideVerts ⊆ V(W.graph)`. -/
theorem Wall.insideVerts_subset (W : Wall α β) : W.insideVerts ⊆ V(W.graph) :=
  sdiff_subset

/-- `W.insideVerts` and `V(W.perimeter)` are disjoint. -/
theorem Wall.disjoint_insideVerts_perimeter (W : Wall α β) :
    Disjoint W.insideVerts V(W.perimeter) :=
  disjoint_sdiff_left

/-- `W.insideVerts ∪ V(W.perimeter) = V(W.graph)`. -/
theorem Wall.insideVerts_union_perimeter (W : Wall α β) :
    W.insideVerts ∪ V(W.perimeter) = V(W.graph) :=
  sdiff_union_of_subset W.perimeter_vertexSet_subset

/-- If `W` is a wall in `G` (`W.graph ≤ G`), then `wallCompassVerts G W ⊆ V(G)`. -/
theorem wallCompassVerts_subset_vertexSet {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G) :
    wallCompassVerts G W ⊆ V(G) := by
  rintro v (hvP | ⟨hvG, _⟩)
  · exact hW.vertexSet_mono (W.perimeter_vertexSet_subset hvP)
  · exact hvG.1

/-- The compass `wallCompass G W` is an induced subgraph of `G`, hence `wallCompass G W ≤ G`. -/
theorem wallCompass_le {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G) :
    wallCompass G W ≤ G :=
  G.induce_le (wallCompassVerts_subset_vertexSet hW)

/-- If `W.graph ≤ G`, then `V(wallCompass G W) = wallCompassVerts G W`. -/
theorem vertexSet_wallCompass {G : Graph α β} {W : Wall α β} (_hW : W.graph ≤ G) :
    V(wallCompass G W) = wallCompassVerts G W :=
  rfl

/-- `V(W.perimeter) ⊆ V(wallCompass G W)` when `W.graph ≤ G`. -/
theorem perimeter_subset_wallCompass {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G) :
    V(W.perimeter) ⊆ V(wallCompass G W) := by
  rw [vertexSet_wallCompass hW]
  exact subset_union_left

/-- `W.insideVerts ⊆ V(wallCompass G W)` when `W.graph ≤ G`. -/
theorem insideVerts_subset_wallCompass {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G) :
    W.insideVerts ⊆ V(wallCompass G W) := by
  rw [vertexSet_wallCompass hW]
  intro u hu
  refine Or.inr ⟨⟨hW.vertexSet_mono (W.insideVerts_subset hu), hu.2⟩, u, hu, ?_⟩
  have hu_del : u ∈ V(deleteVertices G V(W.perimeter)) := by
    rw [vertexSet_deleteVertices]
    exact ⟨hW.vertexSet_mono (W.insideVerts_subset hu), hu.2⟩
  exact ⟨GraphWalk.nil hu_del⟩

/-- `V(W.graph) ⊆ V(wallCompass G W)` when `W.graph ≤ G`. -/
theorem wall_vertexSet_subset_wallCompass {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G) :
    V(W.graph) ⊆ V(wallCompass G W) := by
  rw [← W.insideVerts_union_perimeter]
  exact union_subset (insideVerts_subset_wallCompass hW) (perimeter_subset_wallCompass hW)

/-- `W.graph ≤ wallCompass G W` when `W.graph ≤ G` (Graph Minors XIII, page 102:
"It follows that $H$ is a subgraph of its compass"). -/
theorem wall_le_wallCompass {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G) :
    W.graph ≤ wallCompass G W := by
  refine ⟨wall_vertexSet_subset_wallCompass hW, fun e x y hlink => ?_⟩
  dsimp [wallCompass]
  rw [induce_isLink]
  exact ⟨hlink.mono hW,
    wall_vertexSet_subset_wallCompass hW hlink.left_mem,
    wall_vertexSet_subset_wallCompass hW hlink.right_mem⟩

/-- Any walk in `G \ V(W.perimeter)` starting at a vertex in `V(wallCompass G W) \ V(W.perimeter)`
has its end in `V(wallCompass G W) \ V(W.perimeter)`. -/
theorem wallCompass_walk_mem {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G)
    {u v : α} (hu : u ∈ V(wallCompass G W) \ V(W.perimeter))
    (w : GraphWalk (deleteVertices G V(W.perimeter)) u v) :
    v ∈ V(wallCompass G W) \ V(W.perimeter) := by
  rw [vertexSet_wallCompass hW] at hu ⊢
  rcases hu with ⟨hu_union, hu_not_P⟩
  rcases hu_union with huP | ⟨_, u₀, hu₀, ⟨w₀⟩⟩
  · exact absurd huP hu_not_P
  · have hv_del : v ∈ V(deleteVertices G V(W.perimeter)) :=
      w.mem_vertexSet_of_mem_support w.end_mem_support
    rw [vertexSet_deleteVertices] at hv_del
    exact ⟨Or.inr ⟨hv_del, u₀, hu₀, ⟨w₀.append w⟩⟩, hv_del.2⟩

/-- Any walk in `G \ V(W.perimeter)` starting at a vertex in `V(wallCompass G W) \ V(W.perimeter)`
has all its support vertices in `V(wallCompass G W) \ V(W.perimeter)`. -/
theorem wallCompass_walk_support_mem {G : Graph α β} {W : Wall α β} (hW : W.graph ≤ G)
    {u v : α} (hu : u ∈ V(wallCompass G W) \ V(W.perimeter))
    (w : GraphWalk (deleteVertices G V(W.perimeter)) u v) :
    ∀ z ∈ w.support, z ∈ V(wallCompass G W) \ V(W.perimeter) := by
  induction w with
  | nil _ =>
    intro z hz
    simp only [GraphWalk.support, List.mem_singleton] at hz
    subst hz
    exact hu
  | @cons u x v e hlink w_tail ih =>
    have hx : x ∈ V(wallCompass G W) \ V(W.perimeter) :=
      wallCompass_walk_mem hW hu (GraphWalk.cons hlink (GraphWalk.nil hlink.right_mem))
    intro z hz
    simp only [GraphWalk.support, List.mem_cons] at hz
    rcases hz with rfl | hz_tail
    · exact hu
    · exact ih hx z hz_tail

/-! ## Simple Walk Loop-Freedom Helper -/

/-- No edge of a simple walk `W : GraphWalk P a b` is a loop in `P`. -/
theorem ne_of_isSimple_of_mem_edges {P : Graph α β} {a b : α}
    (W : GraphWalk P a b) (hW : W.IsSimple)
    {e : β} (he : e ∈ W.edges) {x y : α} (hlink : P.IsLink e x y) :
    x ≠ y := by
  induction W with
  | nil _ =>
    simp [GraphWalk.edges] at he
  | @cons u v c e₀ hlink₀ W_tail ih =>
    have hnd : (u :: W_tail.support).Nodup := hW
    rw [List.nodup_cons] at hnd
    rcases hnd with ⟨hu_not_tail, htail_nd⟩
    have huv : u ≠ v := by
      rintro rfl
      exact hu_not_tail W_tail.start_mem_support
    simp only [GraphWalk.edges, List.mem_cons] at he
    rcases he with rfl | he_tail
    · rcases P.eq_or_eq_of_isLink_of_isLink hlink hlink₀ with h1 | h1
      · have hy := hlink.right_unique (h1 ▸ hlink₀)
        subst h1 hy
        exact huv
      · have hy := hlink.right_unique (h1 ▸ hlink₀.symm)
        subst h1 hy
        exact huv.symm
    · exact ih htail_nd he_tail

/-- No edge of a path `IsGraphPathWithEnds G P a b` is a loop in `P` (or `G`). -/
theorem ne_of_isLink_of_isGraphPathWithEnds {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) {e : β} {x y : α} (hlink : P.IsLink e x y) :
    x ≠ y := by
  rcases hP with ⟨_, W, hW_simple, _, hEP⟩
  have he : e ∈ W.edges := by
    have heP : e ∈ E(P) := hlink.edge_mem
    rwa [hEP, mem_ofPred_eq] at heP
  exact ne_of_isSimple_of_mem_edges W hW_simple he hlink

/-! ## Subwall Separation Properties and Proof of (9.5) -/

/-- A subwall `H₁` of `H` satisfies the standard induced-subgraph and perimeter-separation properties
stated on pages 98 and 102 of Graph Minors XIII:
1. *"It follows that if $H'$ is a subwall of $H$, then $H'$ consists of its perimeter $C$ together
   with the portion of $H$ inside $C$."* In particular, no edge of `H` links a vertex in
   `H₁.insideVerts` directly to a vertex in `V(H.graph) \ V(H₁.graph)`.
2. *"Since $H_1$ is an induced subgraph of $H$, to prove the first claim it suffices to show that
   $V(K_1 \cap H) \subseteq V(H_1)$."* -/
structure IsProperSubwallOf (H₁ H : Wall α β) : Prop extends H₁.IsSubwallOf H where
  graph_le : H₁.graph ≤ H.graph
  induced_eq : H.graph.induce V(H₁.graph) = H₁.graph
  no_edge_inside_to_outside :
    ∀ ⦃e : β⦄ ⦃x y : α⦄, H.graph.IsLink e x y →
      x ∈ H₁.insideVerts → y ∈ V(H₁.graph)

/-- Given a walk `w` in `G \ V(H₁.perimeter)` from `u ∈ H₁.insideVerts` to `t ∈ V(H.graph) \ V(H₁.graph)`,
there exists an `H`-path `P` in `G` with ends `a ∈ H₁.insideVerts` and `b ∈ V(H.graph) \ V(H₁.graph)`. -/
theorem exists_hPath_of_walk_inside_to_outside
    {G : Graph α β} {H H₁ : Wall α β}
    (hHG : H.graph ≤ G) (hsub : IsProperSubwallOf H₁ H)
    {u t : α} (hu : u ∈ H₁.insideVerts) (ht : t ∈ V(H.graph) \ V(H₁.graph))
    (w : GraphWalk (deleteVertices G V(H₁.perimeter)) u t) :
    ∃ P a b, IsHPathWithEnds G H.graph P a b ∧
      a ∈ H₁.insideVerts ∧ b ∈ V(H.graph) \ V(H₁.graph) := by
  obtain ⟨a, ha, b, hb, P, _, _, hP_fromTo⟩ :=
    exists_isFromToPathWithEnds_of_walk w hu ht
  rcases hP_fromTo with ⟨hP_path_del, hP_inter_in, hP_inter_out⟩
  have hP_le_del : P ≤ deleteVertices G V(H₁.perimeter) := hP_path_del.le
  have hP_path_G : IsGraphPathWithEnds G P a b :=
    hP_path_del.mono (deleteVertices_le G V(H₁.perimeter))
  have ha_H : a ∈ V(H.graph) :=
    hsub.graph_le.vertexSet_mono (H₁.insideVerts_subset ha)
  have hb_H : b ∈ V(H.graph) := hb.1
  have hab : a ≠ b := by
    rintro rfl
    exact hb.2 (H₁.insideVerts_subset ha)
  have hVP_inter_H : V(P) ∩ V(H.graph) = {a, b} := by
    ext z
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hzP, hzH⟩
      have hz_del : z ∈ V(deleteVertices G V(H₁.perimeter)) := hP_le_del.vertexSet_mono hzP
      rw [vertexSet_deleteVertices] at hz_del
      by_cases hzH₁ : z ∈ V(H₁.graph)
      · have hz_in : z ∈ H₁.insideVerts := ⟨hzH₁, hz_del.2⟩
        have hz_a : z ∈ V(P) ∩ H₁.insideVerts := ⟨hzP, hz_in⟩
        rw [hP_inter_in, mem_singleton_iff] at hz_a
        exact Or.inl hz_a
      · have hz_out : z ∈ V(H.graph) \ V(H₁.graph) := ⟨hzH, hzH₁⟩
        have hz_b : z ∈ V(P) ∩ (V(H.graph) \ V(H₁.graph)) := ⟨hzP, hz_out⟩
        rw [hP_inter_out, mem_singleton_iff] at hz_b
        exact Or.inr hz_b
    · rintro (rfl | rfl)
      · exact ⟨hP_path_G.left_mem, ha_H⟩
      · exact ⟨hP_path_G.right_mem, hb_H⟩
  have hEP_disj_H : Disjoint E(P) E(H.graph) := by
    rw [Set.disjoint_left]
    intro e heP heH
    obtain ⟨x, y, hlink_P⟩ := P.exists_isLink_of_mem_edgeSet heP
    have hxy_ne : x ≠ y := ne_of_isLink_of_isGraphPathWithEnds hP_path_G hlink_P
    have hlink_G : G.IsLink e x y := hlink_P.mono hP_path_G.le
    have hlink_H : H.graph.IsLink e x y := (hHG.isLink_iff heH).mpr hlink_G
    have hx_ab : x = a ∨ x = b := by
      have : x ∈ V(P) ∩ V(H.graph) := ⟨hlink_P.left_mem, hlink_H.left_mem⟩
      rwa [hVP_inter_H, mem_insert_iff, mem_singleton_iff] at this
    have hy_ab : y = a ∨ y = b := by
      have : y ∈ V(P) ∩ V(H.graph) := ⟨hlink_P.right_mem, hlink_H.right_mem⟩
      rwa [hVP_inter_H, mem_insert_iff, mem_singleton_iff] at this
    rcases hx_ab with rfl | rfl <;> rcases hy_ab with rfl | rfl
    · exact hxy_ne rfl
    · exact hb.2 (hsub.no_edge_inside_to_outside hlink_H ha)
    · exact hb.2 (hsub.no_edge_inside_to_outside hlink_H.symm ha)
    · exact hxy_ne rfl
  exact ⟨P, a, b, ⟨hHG, hP_path_G, hab, ha_H, hb_H, hVP_inter_H, hEP_disj_H⟩, ha, hb⟩

/-- First claim in the proof of **Graph Minors XIII, (9.5)** (page 102):
if `H₁` is a dividing subwall of `H` in `G` with compass `K₁`, then `V(K₁) ∩ V(H) ⊆ V(H₁)`. -/
theorem compass_inter_wall_vertexSet_subset
    {G : Graph α β} {H H₁ : Wall α β}
    (hHG : H.graph ≤ G) (hsub : IsProperSubwallOf H₁ H)
    (hdiv : IsDividingSubwall G H H₁) :
    V(wallCompass G H₁) ∩ V(H.graph) ⊆ V(H₁.graph) := by
  have hH₁G : H₁.graph ≤ G := hsub.graph_le.trans hHG
  rintro t ⟨htK₁, htH⟩
  by_contra ht_not_H₁
  rw [vertexSet_wallCompass hH₁G] at htK₁
  rcases htK₁ with ht_perim | ⟨_, u, hu_in, ⟨w⟩⟩
  · exact ht_not_H₁ (H₁.perimeter_vertexSet_subset ht_perim)
  · obtain ⟨P, a, b, hP, ha_in, hb_out⟩ :=
      exists_hPath_of_walk_inside_to_outside hHG hsub hu_in ⟨htH, ht_not_H₁⟩ w
    exact hdiv.2 P a b hP ⟨ha_in, hb_out⟩

/-- First part of **Graph Minors XIII, (9.5)** (page 102):
"Let $H$ be a wall in a graph $G$. If $H_1$ is a dividing subwall of $H$ with compass $K_1$, then $K_1 \cap H \subseteq H_1$;" -/
theorem compass_inter_wall_le
    {G : Graph α β} {H H₁ : Wall α β}
    (hHG : H.graph ≤ G) (hsub : IsProperSubwallOf H₁ H)
    (hdiv : IsDividingSubwall G H H₁) :
    subgraphInter G (wallCompass G H₁) H.graph ≤ H₁.graph := by
  have hH₁G : H₁.graph ≤ G := hsub.graph_le.trans hHG
  have hK₁G : wallCompass G H₁ ≤ G :=
    G.induce_le (wallCompassVerts_subset_vertexSet hH₁G)
  have hv_sub : V(subgraphInter G (wallCompass G H₁) H.graph) ⊆ V(H₁.graph) := by
    rw [vertexSet_subgraphInter]
    exact compass_inter_wall_vertexSet_subset hHG hsub hdiv
  have hle_ind : subgraphInter G (wallCompass G H₁) H.graph ≤ H.graph.induce V(H₁.graph) := by
    refine ⟨hv_sub, fun e x y hlink => ?_⟩
    rw [induce_isLink]
    have hlink_H : H.graph.IsLink e x y :=
      ((subgraphInter_isLink hK₁G hHG).mp hlink).2
    exact ⟨hlink_H, hv_sub hlink.left_mem, hv_sub hlink.right_mem⟩
  rwa [hsub.induced_eq] at hle_ind

/-- Second part of **Graph Minors XIII, (9.5)** (pages 102–103):
"and if $H_2$ is another dividing subwall of $H$ with compass $K_2$, and $H_1 \cap H_2$ is null,
then $K_1 \cap K_2$ is null." -/
theorem disjoint_compass_of_dividingSubwalls
    {G : Graph α β} {H H₁ H₂ : Wall α β}
    (hHG : H.graph ≤ G)
    (hsub₁ : IsProperSubwallOf H₁ H) (hsub₂ : IsProperSubwallOf H₂ H)
    (hdiv₁ : IsDividingSubwall G H H₁) (hdiv₂ : IsDividingSubwall G H H₂)
    (hdisj : Disjoint V(H₁.graph) V(H₂.graph)) :
    Disjoint V(wallCompass G H₁) V(wallCompass G H₂) := by
  have hH₁G : H₁.graph ≤ G := hsub₁.graph_le.trans hHG
  have hH₂G : H₂.graph ≤ G := hsub₂.graph_le.trans hHG
  have hsub_K₁ : V(wallCompass G H₁) ∩ V(H.graph) ⊆ V(H₁.graph) :=
    compass_inter_wall_vertexSet_subset hHG hsub₁ hdiv₁
  have hsub_K₂ : V(wallCompass G H₂) ∩ V(H.graph) ⊆ V(H₂.graph) :=
    compass_inter_wall_vertexSet_subset hHG hsub₂ hdiv₂
  rw [Set.disjoint_left]
  intro t htK₁ htK₂
  -- First observe `t ∉ V(H.graph)`, otherwise `t ∈ V(H₁.graph) ∩ V(H₂.graph)`
  have ht_not_H : t ∉ V(H.graph) := by
    intro htH
    have ht₁ : t ∈ V(H₁.graph) := hsub_K₁ ⟨htK₁, htH⟩
    have ht₂ : t ∈ V(H₂.graph) := hsub_K₂ ⟨htK₂, htH⟩
    exact Set.disjoint_left.mp hdisj ht₁ ht₂
  -- Thus `t ∉ V(H₁.perimeter)` and `t ∉ V(H₂.perimeter)`
  rw [vertexSet_wallCompass hH₁G] at htK₁
  rw [vertexSet_wallCompass hH₂G] at htK₂
  rcases htK₁ with ht_perim₁ | ⟨_, u₁, hu₁_in, ⟨w₁⟩⟩
  · exact ht_not_H (hsub₁.graph_le.vertexSet_mono (H₁.perimeter_vertexSet_subset ht_perim₁))
  rcases htK₂ with ht_perim₂ | ⟨_, u₂, hu₂_in, ⟨w₂⟩⟩
  · exact ht_not_H (hsub₂.graph_le.vertexSet_mono (H₂.perimeter_vertexSet_subset ht_perim₂))
  -- Every vertex `z ∈ w₂.support` belongs to `V(wallCompass G H₂)`, hence cannot lie in `V(H₁.perimeter)`!
  have hu₂_K₂ : u₂ ∈ V(wallCompass G H₂) \ V(H₂.perimeter) :=
    ⟨insideVerts_subset_wallCompass hH₂G hu₂_in, hu₂_in.2⟩
  have hw₂_mem_K₂ : ∀ z ∈ w₂.support, z ∈ V(wallCompass G H₂) :=
    fun z hz => (wallCompass_walk_support_mem hH₂G hu₂_K₂ w₂ z hz).1
  have hw₂_avoid_perim₁ : ∀ z ∈ w₂.support, z ∉ V(H₁.perimeter) := by
    intro z hz hz_perim₁
    have hz_H₁ : z ∈ V(H₁.graph) := H₁.perimeter_vertexSet_subset hz_perim₁
    have hz_H : z ∈ V(H.graph) := hsub₁.graph_le.vertexSet_mono hz_H₁
    have hz_H₂ : z ∈ V(H₂.graph) := hsub_K₂ ⟨hw₂_mem_K₂ z hz, hz_H⟩
    exact Set.disjoint_left.mp hdisj hz_H₁ hz_H₂
  -- Lift `w₂.reverse` to a walk in `deleteVertices G V(H₁.perimeter)` from `t` to `u₂`
  obtain ⟨w₂_G, hw₂_G_supp, _⟩ :=
    exists_walk_up_of_le (deleteVertices_le G V(H₂.perimeter)) w₂.reverse
  have hw₂_G_verts : ∀ z ∈ w₂_G.support, z ∈ V(deleteVertices G V(H₁.perimeter)) := by
    intro z hz
    rw [hw₂_G_supp, GraphWalk.support_reverse, List.mem_reverse] at hz
    rw [vertexSet_deleteVertices]
    have hz_del₂ : z ∈ V(deleteVertices G V(H₂.perimeter)) :=
      w₂.mem_vertexSet_of_mem_support hz
    rw [vertexSet_deleteVertices] at hz_del₂
    exact ⟨hz_del₂.1, hw₂_avoid_perim₁ z hz⟩
  obtain ⟨w₂_del₁, _, _⟩ :=
    exists_walk_down_of_le (deleteVertices_le G V(H₁.perimeter)) w₂_G hw₂_G_verts (by
      intro e he
      obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet (walk_edges_subset_edgeSet w₂_G e he)
      have hm := walk_isLink_mem_support w₂_G he hxy
      exact ((deleteVertices_isLink G V(H₁.perimeter)).mpr
        ⟨hxy, (hw₂_G_verts x hm.1).2, (hw₂_G_verts y hm.2).2⟩).edge_mem)
  -- Concatenating `w₁` and `w₂_del₁` puts `u₂ ∈ V(wallCompass G H₁)`!
  have hu₂_del₁ : u₂ ∈ V(deleteVertices G V(H₁.perimeter)) :=
    w₂_del₁.mem_vertexSet_of_mem_support w₂_del₁.end_mem_support
  rw [vertexSet_deleteVertices] at hu₂_del₁
  have hu₂_K₁ : u₂ ∈ V(wallCompass G H₁) := by
    rw [vertexSet_wallCompass hH₁G]
    exact Or.inr ⟨hu₂_del₁, u₁, hu₁_in, ⟨w₁.append w₂_del₁⟩⟩
  have hu₂_H₂ : u₂ ∈ V(H₂.graph) := H₂.insideVerts_subset hu₂_in
  have hu₂_H : u₂ ∈ V(H.graph) := hsub₂.graph_le.vertexSet_mono hu₂_H₂
  have hu₂_H₁ : u₂ ∈ V(H₁.graph) := hsub_K₁ ⟨hu₂_K₁, hu₂_H⟩
  exact Set.disjoint_left.mp hdisj hu₂_H₁ hu₂_H₂

/-- **Graph Minors XIII, (9.5)** (page 102):
"Let $H$ be a wall in a graph $G$. If $H_1$ is a dividing subwall of $H$ with compass $K_1$, then
$K_1 \cap H \subseteq H_1$; and if $H_2$ is another dividing subwall of $H$ with compass $K_2$, and
$H_1 \cap H_2$ is null, then $K_1 \cap K_2$ is null." -/
theorem theorem_9_5_proof
    {G : Graph α β} {H H₁ H₂ : Wall α β}
    (hHG : H.graph ≤ G)
    (hsub₁ : IsProperSubwallOf H₁ H) (hdiv₁ : IsDividingSubwall G H H₁) :
    subgraphInter G (wallCompass G H₁) H.graph ≤ H₁.graph ∧
      (IsProperSubwallOf H₂ H →
        IsDividingSubwall G H H₂ →
        Disjoint V(H₁.graph) V(H₂.graph) →
        Disjoint V(wallCompass G H₁) V(wallCompass G H₂) ∧
          V(subgraphInter G (wallCompass G H₁) (wallCompass G H₂)) = ∅) := by
  refine ⟨compass_inter_wall_le hHG hsub₁ hdiv₁, ?_⟩
  intro hsub₂ hdiv₂ hdisj
  have hdisj_K := disjoint_compass_of_dividingSubwalls hHG hsub₁ hsub₂ hdiv₁ hdiv₂ hdisj
  refine ⟨hdisj_K, ?_⟩
  rw [vertexSet_subgraphInter]
  exact hdisj_K.inter_eq

end GraphMinor.GM13