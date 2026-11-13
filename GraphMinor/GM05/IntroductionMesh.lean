module

public import GraphMinor.GM05.Section5
public import GraphMinor.GM05.SeriesParallelDefs
import GraphMinor.GM05.ShadowMinor

/-!
# The mesh form of the introduction's grid theorem

Graph Minors V, (1.6), follows from (5.3) by choosing enough components
of each subgraph. We first check that a smaller grid is a minor of a larger
one, so the even grid size used in Sections 2–5 covers every requested size.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set GM01

universe u v

private theorem grid_minor_grid {m n : ℕ} (hmn : m ≤ n) :
    IsIsoMinor (gridGraph m) (gridGraph n) := by
  classical
  let f : Fin m × Fin m → Fin n × Fin n :=
    fun x ↦ (Fin.castLE hmn x.1, Fin.castLE hmn x.2)
  have hf : Function.Injective f := by
    intro x y h
    exact Prod.ext (Fin.castLE_injective hmn (congrArg Prod.fst h))
      (Fin.castLE_injective hmn (congrArg Prod.snd h))
  let G := SimpleGraph.toSubgraph (pathGraph n □ pathGraph n) le_top
  change IsIsoMinor (Graph.ofSimpleGraph (pathGraph m □ pathGraph m)) _
  change IsIsoMinor (Graph.ofSimpleGraph (pathGraph m □ pathGraph m))
    (Graph.ofSimpleGraph (pathGraph n □ pathGraph n))
  rw [ofSimpleGraph_eq_toGraph (pathGraph n □ pathGraph n)]
  apply isIsoMinor_ofSimpleGraph_of_connected_subgraphs _ (G := G) (finite_univ)
    (fun x ↦ (⊤ : SimpleGraph (Fin n × Fin n)).singletonSubgraph (f x))
  · intro x
    exact (singletonSubgraph_le_iff _ _).2 (mem_univ _)
  · intro x
    exact Subgraph.singletonSubgraph_connected
  · intro x y hxy
    change Disjoint ({f x} : Set _) {f y}
    exact Set.disjoint_singleton.mpr (hf.ne hxy)
  · intro x y hxy
    refine ⟨f x, rfl, f y, rfl, ?_⟩
    change (pathGraph n □ pathGraph n).Adj (f x) (f y)
    simpa only [boxProd_adj, pathGraph_adj, f, Fin.val_castLE, Fin.castLE_inj] using hxy

/-- Graph Minors V, (1.6), page 93:
"For any positive integer $\theta$ there exists an integer $\theta'$ such that if $G$ has subgraphs $H$ and $K$, each with $\ge \theta'$ components, and if each component of $H$ meets each component of $K$, then $G$ contains a $\theta$-grid minor."

Here the host `G` is a finite simple graph.
The components selected from the two subgraphs form the mesh excluded by
(5.3), as indicated on page 102. -/
theorem theorem_1_6_simple {θ : ℕ} (_hθ : 0 < θ) :
    ∃ θ' : ℕ, ∀ {V : Type u} {G : (⊤ : SimpleGraph V).Subgraph},
      G.verts.Finite → ∀ {H K : (⊤ : SimpleGraph V).Subgraph},
      H ≤ G → K ≤ G → θ' ≤ numComponents H → θ' ≤ numComponents K →
      (∀ C D, IsComponentOf C H → IsComponentOf D K →
        (C.verts ∩ D.verts).Nonempty) →
      IsIsoMinor (gridGraph θ) (toGraph G) := by
  classical
  let n := 2 * (θ + 3)
  have hn : 6 ≤ n := by omega
  have heven : Even n := ⟨θ + 3, by omega⟩
  refine ⟨max (θ₅ n) (θ₆ n), ?_⟩
  intro V G hG H K hHG hKG hH hK hmeet
  have hHfin := hG.subset hHG.1
  have hKfin := hG.subset hKG.1
  let : Finite H.verts := hHfin.to_subtype
  let : Finite K.verts := hKfin.to_subtype
  let : Fintype H.coe.ConnectedComponent := Fintype.ofFinite _
  let : Fintype K.coe.ConnectedComponent := Fintype.ofFinite _
  have hHcard : Fintype.card (Fin (θ₅ n)) ≤ Fintype.card H.coe.ConnectedComponent := by
    simpa only [Fintype.card_fin, numComponents, Nat.card_eq_fintype_card] using
      (le_trans (le_max_left _ _) hH)
  have hKcard : Fintype.card (Fin (θ₆ n)) ≤ Fintype.card K.coe.ConnectedComponent := by
    simpa only [Fintype.card_fin, numComponents, Nat.card_eq_fintype_card] using
      (le_trans (le_max_right _ _) hK)
  let a := Classical.choice (Function.Embedding.nonempty_of_card_le hHcard)
  let b := Classical.choice (Function.Embedding.nonempty_of_card_le hKcard)
  have hdisj {L : (⊤ : SimpleGraph V).Subgraph} {c d : L.coe.ConnectedComponent}
      (hcd : c ≠ d) : Disjoint (componentSubgraph L c).verts (componentSubgraph L d).verts := by
    rw [Set.disjoint_left]
    rintro v ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hxy : y = x := Subtype.ext heq
    exact hcd (hx.symm.trans (hxy ▸ hy))
  have hlarge : IsIsoMinor (gridGraph n) (toGraph G) := by
    by_contra hno
    apply theorem_5_3_simple hn heven hG hno
    refine ⟨fun i ↦ componentSubgraph H (a i), fun j ↦ componentSubgraph K (b j), ?_⟩
    exact {
      le_left := fun _ ↦ (componentSubgraph_le H _).trans hHG
      le_right := fun _ ↦ (componentSubgraph_le K _).trans hKG
      connected_left := fun _ ↦ connected_componentSubgraph H _
      connected_right := fun _ ↦ connected_componentSubgraph K _
      disjoint_left := fun _ _ h ↦ hdisj (a.injective.ne h)
      disjoint_right := fun _ _ h ↦ hdisj (b.injective.ne h)
      meets := fun _ _ ↦ hmeet _ _ (isComponentOf_componentSubgraph H _)
        (isComponentOf_componentSubgraph K _) }
  exact (grid_minor_grid (show θ ≤ n by omega)).trans hlarge

/-- Graph Minors V, (1.6), page 93:
"For any positive integer $\theta$ there exists an integer $\theta'$ such that if $G$ has subgraphs $H$ and $K$, each with $\ge \theta'$ components, and if each component of $H$ meets each component of $K$, then $G$ contains a $\theta$-grid minor."

Components are represented by their vertex sets in the simple shadow.
`graphConnected_iff_simpleShadow_connected` proves that these are the same
connected pieces. The simple shadow is a minor of the original multigraph,
so the mesh argument transfers without changing the requested grid. -/
theorem theorem_1_6_proof {θ : ℕ} (hθ : 0 < θ) :
    ∃ θ' : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β),
      G.vertexSet.Finite → G.edgeSet.Finite → ∀ {H K : Graph α β},
      H ≤ G → K ≤ G → θ' ≤ numComponents (simpleShadow H) →
      θ' ≤ numComponents (simpleShadow K) →
      (∀ C D, IsComponentOf C (simpleShadow H) → IsComponentOf D (simpleShadow K) →
        (C.verts ∩ D.verts).Nonempty) →
      IsIsoMinor (gridGraph θ) G := by
  obtain ⟨θ', h⟩ := theorem_1_6_simple.{u} hθ
  refine ⟨θ', ?_⟩
  intro α β G hV hE H K hHG hKG hH hK hmeet
  have hm := h (G := simpleShadow G) (H := simpleShadow H) (K := simpleShadow K)
    hV (simpleShadow_mono hHG) (simpleShadow_mono hKG) hH hK hmeet
  exact hm.trans (simpleShadow_isIsoMinor G hV hE)

end GraphMinor.GM05
