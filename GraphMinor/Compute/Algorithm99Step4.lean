module

public import GraphMinor.Compute.Algorithm99Handoff
import GraphMinor.Compute.Algorithm97Aux

/-!
# Step (4) of Algorithm (9.9): a small compass exists

Step (4) of Algorithm (9.9) of Graph Minors XIII (pages 104–105) reads: "Since
$|Z_i| \le s - 3$, we may choose three of the $H^j$'s, say $H^1$, $H^2$, and $H^3$, such that
$V(K^j) \cap Z_i = \emptyset$ ($1 \le j \le 3$)." After a count it ends: "Choose one of them,
$K^1$ say, so that $\varepsilon(K^1) + d_1 + |X| \le \frac{1}{2}\varepsilon(G_i)$."

The mathematics is `GM13.step4_exists_small_compass`, with the correction recorded there. This file
applies it to the output (ii) of (9.7) on the Word RAM formats (`alg99_step4_exists`). The compass
`K^a` of the wall `H^a` is the compass of the GM wall of `H^a` in `delGraph G' X`, the graph
`G_i \ X`. Its vertex set is the bit set that the program computes in `G'` (`Algorithm99Handoff`),
so the index the program finds by testing these bit sets is the index of the lemma.

The facts needed by `GM13.step4_exists_small_compass` are:
* `delGraph G' X = G_i \ X`, since `G'` and `G_i` agree outside `X`
  (`deleteVertices_wallUnionMultiDigraph`, `delGraph_eq_deleteVertices`);
* the GM wall of `H^a` lies in `G_i \ X` (`toGMWall_le_delGraph`);
* the compasses are pairwise disjoint, by (9.5) (`disjoint_compassFinset_of_isDividingSubwall`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Graph

/-- `(G_i \ X) ∪ H_i` and `G_i` have the same edges outside `X`. -/
theorem deleteVertices_wallUnionMultiDigraph {n h : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (H : WallOfHeight h G) :
    (WallOfHeight.wallUnionMultiDigraph G X H).deleteVertices X = G.deleteVertices X := by
  unfold MultiDigraph.deleteVertices
  congr 1
  funext u v
  rw [WallOfHeight.wallUnionMultiDigraph_edgeMult]
  by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;> simp [hu, hv]

/-- `delGraph G X` is `G \ X` in the GM sense. -/
theorem delGraph_eq_deleteVertices {n : ℕ} (G : MultiDigraph n) (X : Finset (Fin n)) :
    delGraph G X = GM09.deleteVertices G.toGMDigraph.toGraph X.toNatSet := by
  rw [delGraph_eq]
  exact GM13.Digraph.toGraph_deleteVertices _ _

/-- `delGraph` only sees `G \ X`. -/
theorem delGraph_wallUnionMultiDigraph {n h : ℕ} (G : MultiDigraph n) (X : Finset (Fin n))
    (H : WallOfHeight h G) :
    delGraph (WallOfHeight.wallUnionMultiDigraph G X H) X = delGraph G X := by
  unfold delGraph
  rw [deleteVertices_wallUnionMultiDigraph]

/-- The GM wall of a wall of `G \ X` that misses `X` lies in `delGraph G X`. -/
theorem toGMWall_le_delGraph {n h : ℕ} {G : MultiDigraph n} {X : Finset (Fin n)}
    (W : WallOfHeight h (G.deleteVertices X)) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hdisj : Disjoint W.vertexFinset X) :
    (W.toGMWall h2 he hW).graph ≤ delGraph G X := by
  have hle_D : (W.toGMWall h2 he hW).graph ≤ (G.deleteVertices X).toGMDigraph.toGraph :=
    W.isWallIn_toGMWall h2 he hW
  have hsub_D : delGraph G X ≤ (G.deleteVertices X).toGMDigraph.toGraph :=
    GM13.Digraph.IsSubdigraph.toGraph_le
      ((G.deleteVertices X).toGMDigraph.deleteVertices_isSubdigraph _)
  rw [(Compatible.of_le_le hle_D hsub_D).le_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [WallOfHeight.vertexSet_toGMWall_eq h2 he hW] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact (mem_vertexSet_delGraph_iff G X v.1).mpr
      ⟨v.2, Finset.disjoint_left.mp hdisj (Finset.mem_coe.mp hv)⟩
  · intro e he
    rw [edgeSet_delGraph]
    exact hle_D.edgeSet_mono he

/-- **Step (4) of Algorithm (9.9)** (Graph Minors XIII, pages 104–105), on the output (ii) of
(9.7). Let `H^1, …, H^s` (`s = C(p, 2) + 5`) be pairwise disjoint subwalls of `H_i` that miss `X`
and are dividing in `G' = (G_i \ X) ∪ H_i`, with `|X| < C(p, 2)` and `|Z_i| ≤ C(p, 2) + 2`. Then
for some `a` the compass of `H^a` in `G'` (the bit set the program computes) misses `Z_i`, and
the compass `K^a` of the GM wall of `H^a` in `G_i \ X`, whose vertex set is that bit set,
satisfies `2 (ε(K^a) + d_a + |X|) ≤ ε(G_i)`. This is `GM13.step4_exists_small_compass`. -/
theorem alg99_step4_exists {p n h h' : ℕ} {Gi : MultiDigraph n} {Hi : WallOfHeight h' Gi}
    (hHi : Hi.IsValid) (h2' : 2 ≤ h') (he' : Even h') (h2 : 2 ≤ h) (he : Even h)
    {X Z : Finset (Fin n)} (hX : X.card < p.choose 2) (hZ : Z.card ≤ p.choose 2 + 2)
    (W_flat : Fin (p.choose 2 + 5) → WallOfHeight h Gi) (hsub : ∀ a, (W_flat a).IsSubwallOf Hi)
    (hpair : Pairwise fun a b => Disjoint (W_flat a).vertexFinset (W_flat b).vertexFinset)
    (hdisj : ∀ a, Disjoint (W_flat a).vertexFinset X)
    (hdiv : ∀ a, (Hi.castGraph (WallOfHeight.wallUnionMultiDigraph Gi X Hi)).IsDividingSubwall
      ((W_flat a).castGraph (WallOfHeight.wallUnionMultiDigraph Gi X Hi))) :
    ∃ a, ∃ hWa : ((W_flat a).castGraph
        ((WallOfHeight.wallUnionMultiDigraph Gi X Hi).deleteVertices X)).IsValid,
      Disjoint ((W_flat a).castGraph (WallOfHeight.wallUnionMultiDigraph Gi X Hi)).compassFinset Z ∧
      ((W_flat a).castGraph (WallOfHeight.wallUnionMultiDigraph Gi X Hi)).compassFinset.toNatSet =
        V(GM13.wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph Gi X Hi) X)
          (((W_flat a).castGraph
            ((WallOfHeight.wallUnionMultiDigraph Gi X Hi).deleteVertices X)).toGMWall h2 he hWa)) ∧
      2 * (GM13.graphSize (GM13.wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph Gi X Hi) X)
          (((W_flat a).castGraph
            ((WallOfHeight.wallUnionMultiDigraph Gi X Hi).deleteVertices X)).toGMWall h2 he hWa)) +
        (GM13.crossEdgesToSet Gi.toGMDigraph.toGraph
          V(GM13.wallCompass (delGraph (WallOfHeight.wallUnionMultiDigraph Gi X Hi) X)
            (((W_flat a).castGraph
              ((WallOfHeight.wallUnionMultiDigraph Gi X Hi).deleteVertices X)).toGMWall h2 he hWa))
          X.toNatSet).ncard + X.toNatSet.ncard) ≤
        GM13.graphSize Gi.toGMDigraph.toGraph := by
  set G' := WallOfHeight.wallUnionMultiDigraph Gi X Hi with hG'
  set D := G'.deleteVertices X with hD
  have hW : ∀ a, (W_flat a).IsValid := fun a => Hi.isValid_of_isSubwallOf hHi (hsub a)
  have hWD : ∀ a, ((W_flat a).castGraph D).IsValid := fun a =>
    WallOfHeight.isValid_castGraph_deleteVertices_wallUnion (hW a) (hdisj a)
  let H_sub : Fin (p.choose 2 + 5) → GM13.Wall ℕ (ℕ × ℕ × ℕ) := fun a =>
    ((W_flat a).castGraph D).toGMWall h2 he (hWD a)
  let K : Fin (p.choose 2 + 5) → Graph ℕ (ℕ × ℕ × ℕ) := fun a => GM13.wallCompass (delGraph G' X) (H_sub a)
  have hdelG : delGraph G' X = GM09.deleteVertices Gi.toGMDigraph.toGraph X.toNatSet := by
    rw [hG', delGraph_wallUnionMultiDigraph, delGraph_eq_deleteVertices]
  have hH_le : ∀ a, (H_sub a).graph ≤ delGraph G' X := fun a =>
    toGMWall_le_delGraph _ h2 he (hWD a) (hdisj a)
  -- The vertex set of `K a` is the compass bit set of `H^a` in `G'`.
  have hVK : ∀ a, V(K a) = ((W_flat a).castGraph G').compassFinset.toNatSet := by
    intro a
    have h1 := WallOfHeight.toNatSet_compassFinset_eq_wallCompass_delGraph
      ((W_flat a).castGraph D) h2 he (hWD a) (hdisj a)
    rw [WallOfHeight.compassFinset_castGraph_deleteVertices_wallUnion hHi h2' he' (hW a) h2
      (hdisj a) (hdiv a)] at h1
    exact h1.symm
  have hHi' := WallOfHeight.isValid_castGraph_wallUnionMultiDigraph X hHi
  have hK_disj : Pairwise fun a b => Disjoint V(K a) V(K b) := by
    intro a b hab
    rw [hVK a, hVK b]
    unfold Finset.toNatSet
    rw [Set.disjoint_image_iff Fin.val_injective, Finset.disjoint_coe]
    exact WallOfHeight.disjoint_compassFinset_of_isDividingSubwall h2' he' hHi' (hdiv a) (hdiv b)
      (hpair hab)
  have hK_le_del : ∀ a, K a ≤ delGraph G' X := fun a => GM13.wallCompass_le (hH_le a)
  have hK_le_Gi : ∀ a, K a ≤ Gi.toGMDigraph.toGraph := fun a =>
    (hK_le_del a).trans (hdelG ▸ GM09.deleteVertices_le _ _)
  have hK_disj_X : ∀ a, Disjoint V(K a) X.toNatSet := by
    intro a
    rw [Set.disjoint_left]
    intro x hx hxX
    have hx' := (hK_le_del a).vertexSet_mono hx
    rw [vertexSet_delGraph] at hx'
    exact hx'.2 hxX
  have hX_sub : X.toNatSet ⊆ V(Gi.toGMDigraph.toGraph) := toNatSet_subset_lt X
  obtain ⟨j, hjZ, hj⟩ := GM13.step4_exists_small_compass (p := p) (Z_i := Z.toNatSet)
    (Gi.isFinite_toGMDigraph.finite_V) (Gi.isFinite_toGMDigraph.finite_E) hX_sub
    (by rw [ncard_toNatSet]; exact hX) (Z.finite_toSet.image _) (by rw [ncard_toNatSet]; exact hZ)
    H_sub K (fun a => GM13.wall_le_wallCompass (hH_le a)) hK_le_Gi hK_disj_X hK_disj
  refine ⟨j, hWD j, ?_, (hVK j).symm, hj⟩
  rw [hVK j] at hjZ
  unfold Finset.toNatSet at hjZ
  rwa [Set.disjoint_image_iff Fin.val_injective, Finset.disjoint_coe] at hjZ

end GraphMinor.Compute
