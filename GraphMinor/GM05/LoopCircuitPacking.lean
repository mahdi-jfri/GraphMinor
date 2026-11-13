module

public import GraphMinor.GM05.LoopCopies
public import GraphMinor.GM05.CircuitPackingDefs
import GraphMinor.Minor.Basic
import GraphMinor.GM09.Basic
import GraphMinor.GM09.NestUncrossing
import GraphMinor.GM14.FewCircuits

/-!
# Extracting disjoint circuits from a loop minor

For each modelled loop, both ends of its representing edge lie in the same
connected branch set. A path in that branch set, together with the edge,
contains a circuit. Different branches give vertex-disjoint circuits. This
is the minor-to-packing step of Graph Minors V, (8.1).
-/

public section

namespace GraphMinor.GM05

open Graph Set GM09 Surface

variable {α β : Type*}

private lemma walk_of_reachable {G : Graph α β} {x y : α}
    (hx : x ∈ V(G)) (h : Relation.ReflTransGen G.Adj x y) : Nonempty (GraphWalk G x y) := by
  induction h with
  | refl => exact ⟨.nil hx⟩
  | @tail y z h hyz ih =>
    obtain ⟨W⟩ := ih
    obtain ⟨e, he⟩ := hyz
    exact ⟨W.append (.cons he (.nil he.right_mem))⟩

private lemma circuit_in_loop_branch {k : ℕ} {G : Graph α β}
    {ηv : Fin k → Set α} {ηe : Fin k → β} (hm : IsMinorModel (loopCopies k) G ηv ηe)
    (i : Fin k) : ∃ C, IsGraphCircuit G C ∧ V(C) ⊆ ηv i := by
  have heG := hm.edge_mem i (mem_univ i)
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet heG
  have hall := (hm.isLoopAt_iff i (mem_univ i) i (mem_univ i)).mp
    ((loopCopies_isLoopAt i i).mpr rfl)
  have hx : x ∈ ηv i := hall x hxy.inc_left
  have hy : y ∈ ηv i := hall y hxy.inc_right
  by_cases hEq : x = y
  · subst y
    refine ⟨_, GM14.isGraphCircuit_of_isLoop hxy, ?_⟩
    rw [vertexSet_walkSubgraph]
    intro z hz
    have he : z = x := by simpa [GraphWalk.support] using hz
    exact he ▸ hx
  · obtain ⟨K, hK, hKV, hconn⟩ := hm.connected i (mem_univ i)
    have hKG : K ≤ G := hK.trans Graph.deleteEdges_le
    have hxK : x ∈ V(K) := hKV.symm ▸ hx
    have hyK : y ∈ V(K) := hKV.symm ▸ hy
    obtain ⟨W⟩ := walk_of_reachable hxK (hconn.2 x hxK y hyK)
    obtain ⟨P, hP, hVP, hEP⟩ := exists_isGraphPathWithEnds_of_walk W
    let Q := walkSubgraph (GraphWalk.cons hxy (GraphWalk.nil hxy.right_mem))
    have hQ : IsGraphPathWithEnds G Q x y := GM14.isGraphPathWithEnds_edge hxy hEq
    have hVQ : V(Q) = {x, y} := by
      ext z
      simp [Q, vertexSet_walkSubgraph, GraphWalk.support]
    have hEQ : E(Q) = {ηe i} := by simp [Q, edgeSet_walkSubgraph, GraphWalk.edges]
    have hPV : V(P) ∩ V(Q) = {x, y} := by
      rw [hVQ]
      apply subset_antisymm inter_subset_right
      intro z hz
      refine ⟨?_, hz⟩
      rcases hz with rfl | rfl
      · exact hP.left_mem
      · exact hP.right_mem
    have hPE : Disjoint E(P) E(Q) := by
      rw [hEQ, disjoint_singleton_right]
      intro hi
      have hiK := hP.le.edgeSet_mono hi
      have hiOut := (hK.edgeSet_mono hiK).2
      exact hiOut ⟨i, mem_univ i, rfl⟩
    refine ⟨subgraphUnion G P Q,
      isGraphCircuit_subgraphUnion (hP.mono hKG) hQ hEq hPV hPE, ?_⟩
    rw [vertexSet_subgraphUnion]
    apply union_subset
    · exact fun z hz ↦ hKV ▸ hP.le.vertexSet_mono hz
    · rw [hVQ]
      exact pair_subset hx hy

/-- A minor consisting of `k` disjoint loops yields `k` vertex-disjoint
circuits, with loops and parallel-edge circuits included. -/
theorem disjointCircuits_of_loopCopies_minor {k : ℕ} {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) (hminor : IsIsoMinor (loopCopies k) G) :
    HasDisjointCircuits G k := by
  classical
  by_cases hk : k = 0
  · subst k
    exact ⟨Fin.elim0, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  · have hβ : Nonempty β := by
      obtain ⟨G', hG', C, hC, ⟨e⟩⟩ := hminor
      let f : Fin k := ⟨0, by omega⟩
      exact ⟨(e.edgeEquiv ⟨f, mem_univ f⟩).1⟩
    let : Nonempty β := hβ
    obtain ⟨ηv, ηe, hm⟩ := exists_isMinorModel_of_isIsoMinor hV hE hminor
    choose C hC hCV using circuit_in_loop_branch hm
    refine ⟨C, hC, fun i j hij ↦ ?_⟩
    exact (hm.vertex_disjoint i (mem_univ i) j (mem_univ j) hij).mono (hCV i) (hCV j)

end GraphMinor.GM05
