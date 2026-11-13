module

public import GraphMinor.GM02.Section4Split
public import GraphMinor.GM02.Section4Routes

/-!
# Topological containment gives disjoint paths in the split graph

This is the forward direction of Graph Minors II, (4.5), page 319. Suppose
that `G` topologically contains `H`. Then a subgraph `K` of `G` turns into `H`
by suppressions, and `Section4Routes.lean` gives each edge `eᵢ` of `H` a route
in `K` from `uᵢ` to `vᵢ`. The inner vertices of the routes are not vertices of
`H`, so they are vertices of `G'`, and different routes share none of them.
Replacing the ends `uᵢ, vᵢ` of the `i`-th route by `sᵢ, tᵢ` gives a path of `G'`
from `sᵢ` to `tᵢ`, since `g` maps it back to the route. These paths are
disjoint.

This direction needs none of the hypotheses of (4.5).
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Relation SimpleGraph Classical

universe u v

variable {α : Type u} {β : Type v}

/-- The index `i` of a pair `(sᵢ, tᵢ)` of the termination. -/
noncomputable def splitIndex (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H))
    (p : {p // p ∈ (splitTermination G H edge).pairs}) : Fin k :=
  (Finset.mem_image.1 p.2).choose

theorem splitIndex_spec (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H))
    (p : {p // p ∈ (splitTermination G H edge).pairs}) :
    s(splitS (splitIndex G H edge p), splitT (splitIndex G H edge p)) = p.val :=
  (Finset.mem_image.1 p.2).choose_spec.2

theorem splitIndex_injective (G H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) :
    Function.Injective (splitIndex G H edge) := by
  intro p q h
  apply Subtype.ext
  rw [← splitIndex_spec G H edge p, ← splitIndex_spec G H edge q, h]

/-- The list `sᵢ, y₁, …, y_m, tᵢ` built from the inner vertices `y₁, …, y_m`. -/
def splitList {k : ℕ} (i : Fin k) (ys : List α) : List (α ⊕ (Fin k × Bool)) :=
  splitS i :: (ys.map Sum.inl ++ [splitT i])

theorem mem_splitList {k : ℕ} {i : Fin k} {ys : List α} {a : α ⊕ (Fin k × Bool)} :
    a ∈ splitList i ys ↔ a = splitS i ∨ (∃ y ∈ ys, a = Sum.inl y) ∨ a = splitT i := by
  simp only [splitList, List.mem_cons, List.mem_append, List.mem_map,
    List.not_mem_nil, or_false]
  constructor
  · rintro (h | ⟨y, hy, rfl⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨y, hy, rfl⟩)
    · exact Or.inr (Or.inr h)
  · rintro (h | ⟨y, hy, rfl⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨y, hy, rfl⟩)
    · exact Or.inr (Or.inr h)

theorem splitList_nodup {k : ℕ} (i : Fin k) {ys : List α} (hys : ys.Nodup) :
    (splitList i ys).Nodup := by
  rw [splitList, List.nodup_cons, List.nodup_append]
  refine ⟨?_, hys.map Sum.inl_injective, List.nodup_singleton _, ?_⟩
  · simp [splitS, splitT]
  · intro a ha b hb hab
    subst hab
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
    simp [splitT] at hb

theorem map_splitList (H : Graph α β) {k : ℕ} (edge : Fin k ≃ E(H)) (i : Fin k)
    (ys : List α) :
    (splitList i ys).map (splitMap H edge) =
      (⟨(splitEnds H edge i).1, ys, (splitEnds H edge i).2⟩ : Route α).list := by
  simp [splitList, Route.list, splitS, splitT, splitMap, List.map_map, Function.comp_def]

/-- A list with a chain of adjacencies and no repetitions gives a path. -/
theorem exists_pairPath_of_splitList {k : ℕ} {F : SimpleGraph (α ⊕ (Fin k × Bool))} (i : Fin k)
    {ys : List α} (hn : (splitList i ys).Nodup) (hc : (splitList i ys).IsChain F.Adj) :
    ∃ P : PairPath F s(splitS i, splitT i), ∀ a, a ∈ P.vertices ↔ a ∈ splitList i ys := by
  have hne : splitList i ys ≠ [] := List.cons_ne_nil _ _
  have hlast : (splitList i ys).getLast hne = splitT i := by simp [splitList]
  let W := (Walk.ofSupport (splitList i ys) hne hc).copy rfl hlast
  have hW : W.support = splitList i ys := by
    simp only [W, Walk.support_copy, Walk.support_ofSupport]
  refine ⟨⟨splitS i, splitT i, rfl, W, Walk.IsPath.mk' (hW ▸ hn)⟩, fun a => ?_⟩
  change a ∈ W.support ↔ _
  rw [hW]

/-- The forward direction of Graph Minors II, (4.5), page 319: if `G`
topologically contains `H`, then `(G', 𝒜)` is feasible. -/
theorem splitFeasible_of_topologicallyContains {G H : Graph α β} {k : ℕ} (edge : Fin k ≃ E(H))
    (h : TopologicallyContains G H) :
    (splitTermination G H edge).Feasible (splitGraph G H edge) := by
  obtain ⟨K, hK, L, hs, σ, hV, hbij, hlink⟩ := topologicallyContains_iff_isoFix.1 h
  by_cases hα : Nonempty α
  swap
  · refine ⟨fun p => (hα ⟨(splitEnds H edge (splitIndex G H edge p)).1⟩).elim, ?_⟩
    intro p
    exact (hα ⟨(splitEnds H edge (splitIndex G H edge p)).1⟩).elim
  obtain ⟨r, hok, hdisj⟩ := exists_routeSystem hs
  -- The route of `eᵢ`, turned to start at `uᵢ`.
  have hf : ∀ i, σ (edge i) ∈ E(L) := fun i => hbij.mapsTo (edge i).2
  have hlinkL : ∀ i, L.IsLink (σ (edge i)) (splitEnds H edge i).1 (splitEnds H edge i).2 :=
    fun i => (hlink _ (edge i).2 _ _).1 (splitEnds_isLink H edge i)
  let ρ : Fin k → Route α := fun i => (r (σ (edge i))).orient (splitEnds H edge i).1
  have hρok : ∀ i, RouteOK K L (ρ i) (σ (edge i)) := fun i => (hok _ (hf i)).orient _
  have hρends : ∀ i, (ρ i).start = (splitEnds H edge i).1 ∧
      (ρ i).finish = (splitEnds H edge i).2 := fun i => (hok _ (hf i)).orient_ends (hlinkL i)
  have hρeq : ∀ i, ρ i = ⟨(splitEnds H edge i).1, (ρ i).inner, (splitEnds H edge i).2⟩ := by
    intro i
    rw [← (hρends i).1, ← (hρends i).2]
  -- The inner vertices are vertices of `G'`.
  have hinner : ∀ i, ∀ y ∈ (ρ i).inner, y ∈ V(G) ∧ y ∉ V(H) := by
    intro i y hy
    obtain ⟨hyK, hyL⟩ := (hρok i).2.2.2 y hy
    exact ⟨hK.vertexSet_mono hyK, fun h => hyL (hV ▸ h)⟩
  have hpath : ∀ i, ∃ P : PairPath (pathGraph (splitGraph G H edge)) s(splitS i, splitT i),
      ∀ a, a ∈ P.vertices ↔ a ∈ splitList i (ρ i).inner := by
    intro i
    have hn := splitList_nodup i (hρok i).2.2.1
    apply exists_pairPath_of_splitList i hn
    -- Adjacency in `G'` comes from adjacency in `K`, through `g`.
    have hcK := (hρok i).2.1
    rw [hρeq i, ← map_splitList H edge i, List.isChain_map] at hcK
    have hcG : (splitList i (ρ i).inner).IsChain
        fun a b => G.Adj (splitMap H edge a) (splitMap H edge b) :=
      hcK.imp fun _ _ h => h.mono hK
    have hcne := isChain_and hcG (List.Pairwise.isChain hn)
    refine hcne.imp_of_mem_imp fun a b ha hb hab => ?_
    have hV' : ∀ c ∈ splitList i (ρ i).inner, c ∈ splitVertexSet G H k := by
      intro c hc
      rcases mem_splitList.1 hc with rfl | ⟨y, hy, rfl⟩ | rfl
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl ⟨y, hinner i y hy, rfl⟩
      · exact Or.inr ⟨_, rfl⟩
    exact ⟨(splitGraph_adj_iff G H edge a b).2 ⟨hV' a ha, hV' b hb, hab.2, hab.1⟩, hab.2⟩
  choose P hP using hpath
  refine ⟨fun p => (splitIndex_spec G H edge p) ▸ P (splitIndex G H edge p), ?_⟩
  intro p q hpq
  have hij : splitIndex G H edge p ≠ splitIndex G H edge q :=
    fun h => hpq (splitIndex_injective G H edge h)
  have hverts : ∀ p, ((splitIndex_spec G H edge p) ▸ P (splitIndex G H edge p)).vertices =
      (P (splitIndex G H edge p)).vertices := by
    intro p
    generalize (splitIndex_spec G H edge p) = e
    generalize p.val = c at e
    subst e
    rfl
  rw [hverts p, hverts q, Set.disjoint_left]
  intro a ha hb
  rw [hP] at ha hb
  set i := splitIndex G H edge p
  set j := splitIndex G H edge q
  have hσ : σ (edge i) ≠ σ (edge j) := by
    intro h
    have := hbij.injOn (edge i).2 (edge j).2 h
    exact hij (edge.injective (Subtype.ext this))
  rcases mem_splitList.1 ha with rfl | ⟨y, hy, rfl⟩ | rfl <;>
    rcases mem_splitList.1 hb with h | ⟨z, hz, h⟩ | h
  all_goals first
    | (simp only [splitS, splitT, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at h;
        first | exact hij h.1 | exact hij h | skip)
    | skip
  · exact hdisj _ (hf i) _ (hf j) hσ y (Route.mem_inner_orient.1 hy)
      (Route.mem_inner_orient.1 (Sum.inl_injective h ▸ hz))

end GraphMinor.GM02
