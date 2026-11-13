module

public import GraphMinor.GM05.FullWebIteration
import GraphMinor.GM05.FullWebValency
import GraphMinor.GM05.FullBipartite

/-!
# Excluding a large web with actual multigraph edges

Restrict the host to the edges of the web, where actual valency is at most
four. Iterate (4.5) from zero spiders to θ₁ spiders. The terminal web has
θ²/2 A paths, so full (4.2) gives the same contradiction as in the paper.
-/

public section
namespace GraphMinor.GM05.Full
open Graph Set SimpleGraph GM01
variable {α β : Type*}

/-- The actual graph of a path is connected. -/
theorem Path.connected (P : Path α β) : GraphConnected P.toGraph := by
  apply (graphConnected_iff_simpleShadow_connected _).mpr
  rw [P.shadow_eq]
  exact P.seq.connected_toSubgraph

/-- Graph Minors V, (4.6), page 100, for hosts with loops and parallel edges.
There is no `(θ₂ θ, θ₂ θ)`-web using actual disjoint edges in a graph
excluding the grid. `GM05.theorem_4_6_simple` is the simple-host version. -/
theorem theorem_4_6_proof {G : Graph α β} {θ : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (gridGraph θ) G) : ¬ HasWeb G (θ₂ θ) (θ₂ θ) := by
  rintro ⟨A, B, hw⟩
  let F : Set β := (⋃ i, (A i).edgeSet) ∪ ⋃ j, (B j).edgeSet
  let G' := G.restrict F
  have hle : G' ≤ G := Graph.restrict_le
  have hV' : V(G').Finite := hV.subset hle.vertexSet_mono
  have hE' : E(G').Finite := hE.subset hle.edgeSet_mono
  have hno' : ¬ IsIsoMinor (gridGraph θ) G' := by
    rintro ⟨K, hK, C, hC, hIso⟩
    exact hno ⟨K, hK.trans hle, C, hC, hIso⟩
  have hdeg : ∀ x ∈ V(G'), valency G' x ≤ 4 :=
    fun x _ => hw.restrict_valency_le_four x
  have hw' : IsWeb G' A B := by
    refine ⟨?_, ?_, hw.disjoint_left, hw.disjoint_right, hw.meets, hw.edge_disjoint⟩
    · intro i
      refine ⟨(hw.isIn_left i).vertexSet_mono, fun e x y he => ?_⟩
      exact ⟨Or.inl (Set.mem_iUnion.mpr ⟨i, he.edge_mem⟩), he.mono (hw.isIn_left i)⟩
    · intro j
      refine ⟨(hw.isIn_right j).vertexSet_mono, fun e x y he => ?_⟩
      exact ⟨Or.inr (Set.mem_iUnion.mpr ⟨j, he.edge_mem⟩), he.mono (hw.isIn_right j)⟩
  have hzero : HasWebWithSpiders G' (φ θ 0) (ψ θ 0) 0 := by
    have hm : φ θ 0 ≤ θ₂ θ := φ_zero_le_θ₂ θ
    have hn : ψ θ 0 ≤ θ₂ θ := (ψ_zero θ).le
    exact ⟨fun i => A (Fin.castLE hm i), fun j => B (Fin.castLE hn j), Fin.elim0,
      hw'.subweb (Fin.castLEEmb hm) (Fin.castLEEmb hn),
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  have hiter : ∀ k ≤ θ₁ θ, HasWebWithSpiders G' (φ θ k) (ψ θ k) k := by
    intro k
    induction k with
    | zero => exact fun _ => hzero
    | succ k ih =>
      intro hk
      exact theorem_4_5_proof hθ heven hV' hE' hno' (Nat.lt_of_succ_le hk)
        (ih (Nat.le_of_succ_le hk))
  obtain ⟨Aend, Bend, Cend, hwend, hsp, hd⟩ := hiter (θ₁ θ) le_rfl
  let e : Fin (θ ^ 2 / 2) ≃ Fin (φ θ (θ₁ θ)) := (finCongr (φ_θ₁ θ)).symm
  have hbound := theorem_4_2_proof hθ heven hV' hE' hno'
    (fun i => (Aend (e i)).toGraph) Cend
    (fun i => hwend.isIn_left (e i)) (fun i => (Aend (e i)).connected)
    (fun i j hij => by
      dsimp only
      rw [(Aend (e i)).vertexSet_eq, (Aend (e j)).vertexSet_eq]
      exact hwend.disjoint_left (e.injective.ne hij))
    (fun i => (hsp i).le) (fun i => (hsp i).connected) hd
    (fun i j => by
      obtain ⟨x, hx, hl⟩ := (hsp j).unique_leaf (e i)
      refine ⟨x, ?_, hl⟩
      rw [(Aend (e i)).vertexSet_eq, Set.inter_comm]
      exact hx) hdeg
  exact Nat.lt_irrefl _ hbound

end GraphMinor.GM05.Full
