module

public import GraphMinor.Thomason.CliqueMinorOfBranches
import GraphMinor.Minor.Basic
import GraphMinor.GM05.ShadowMinor

/-!
# Recovering connected clique branches from a minor

A clique minor has disjoint connected branch graphs. Their vertex sets
are finite and induce connected simple graphs in the host. Recovering
these sets lets the neighbourhood-centre step apply after arbitrary
minor reductions, as required in Thomason's Lemma 1 (1984), p. 262.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset Graph Set
universe u

/-- A clique-minor witness in a finite non-null simple graph supplies
finite connected branches with explicit adjacent endpoints. -/
theorem exists_branches_of_clique_isIsoMinor {W : Type u} [Fintype W] [Nonempty W]
    (J : SimpleGraph W) {q : ℕ}
    (hm : IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph J)) :
    ∃ T : Fin q → Finset W,
      (∀ i, (J.induce (T i : Set W)).Connected) ∧
      (Pairwise fun i j => Disjoint (T i) (T j)) ∧
      (∀ i j, i ≠ j → ∃ v ∈ T i, ∃ w ∈ T j, J.Adj v w) := by
  classical
  let : Nonempty (Sym2 W) := ⟨s(Classical.arbitrary W, Classical.arbitrary W)⟩
  obtain ⟨ηv, ηe, h⟩ := exists_isMinorModel_of_isIsoMinor (Set.toFinite _) (Set.toFinite _) hm
  let T : Fin q → Finset W := fun i => (ηv i).toFinset
  refine ⟨T, ?_, ?_, ?_⟩
  · intro i
    change (J.induce (((ηv i).toFinset : Finset W) : Set W)).Connected
    rw [Set.coe_toFinset]
    obtain ⟨K, hle, hverts, hconn⟩ := h.connected i (Set.mem_univ _)
    have hKG : K ≤ Graph.ofSimpleGraph J := hle.trans Graph.deleteEdges_le
    have hc := (GM05.graphConnected_iff_simpleShadow_connected K).mp hconn
    let f : (GM05.simpleShadow K).coe →g J.induce (ηv i) := {
      toFun := fun x => ⟨x.val, hverts ▸ x.property⟩
      map_rel' := fun {x y} hxy => (Graph.ofSimpleGraph_adj_iff (G := J) x.val y.val).mp
        (Graph.Adj.mono hKG hxy.2) }
    apply hc.coe.map f
    intro x
    have hxK : x.val ∈ V(K) := by rw [hverts]; exact x.property
    exact ⟨⟨x.val, hxK⟩, Subtype.ext rfl⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp
      (h.vertex_disjoint i (mem_univ _) j (mem_univ _) hij)
      (Set.mem_toFinset.mp hx) (Set.mem_toFinset.mp hy)
  · intro i j hij
    let e : Sym2 (Fin q) := s(i, j)
    have hl : (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))).IsLink e i j :=
      ⟨rfl, (SimpleGraph.mem_edgeSet _).mpr hij⟩
    obtain ⟨x, hx, hincx⟩ := (h.inc_iff i hl.left_mem e hl.edge_mem).mp hl.inc_left
    obtain ⟨y, hy, hincy⟩ := (h.inc_iff j hl.right_mem e hl.edge_mem).mp hl.inc_right
    obtain ⟨z, hz⟩ := hincx
    have hxy : x ≠ y := (h.vertex_disjoint i hl.left_mem j hl.right_mem hij).ne_of_mem hx hy
    have hyz : y = z := hincy.eq_of_isLink_of_ne_left hz hxy.symm
    have hlink : (Graph.ofSimpleGraph J).IsLink (ηe e) x y := hyz ▸ hz
    exact ⟨x, Set.mem_toFinset.mpr hx, y, Set.mem_toFinset.mpr hy,
      (Graph.ofSimpleGraph_adj_iff _ _).mp hlink.adj⟩

end GraphMinor.Thomason
