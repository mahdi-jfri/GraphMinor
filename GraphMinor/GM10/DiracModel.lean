module

public import GraphMinor.GM10.Section4K4
public import GraphMinor.GM10.DiracCyclePaths
import GraphMinor.GM01.Basic
import Mathlib.Tactic.FinCases

/-!
# The four branch sets for the low-valency input

A connected set adjacent to three distinct vertices of a disjoint cycle
gives a `K₄` minor. One cycle vertex is a branch set by itself. The
remaining cycle path is split into two disjoint connected pieces, each
containing one of the other attachment vertices. Together with the
outside connected set these give the four branch sets.
-/

public section

namespace GraphMinor.GM10

open Graph Hypergraph SimpleGraph Classical

universe u

/-- The complete graph used in X is the graph of the complete simple graph. -/
theorem completeGraphGraph_eq_ofSimpleGraph_top (n : ℕ) :
    completeGraphGraph n = Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin n)) := by
  ext e x y
  · rfl
  · change (x ≠ y ∧ e = s(x, y)) ↔
      (e = s(x, y) ∧ e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet)
    constructor
    · rintro ⟨hxy, rfl⟩
      exact ⟨rfl, (SimpleGraph.mem_edgeSet _).2 hxy⟩
    · rintro ⟨rfl, he⟩
      exact ⟨(SimpleGraph.mem_edgeSet _).1 he, rfl⟩

/-- Four pairwise disjoint connected vertex sets with all six joining
edges give the complete graph on four vertices as a minor. -/
theorem isIsoMinor_completeGraphGraph_four_of_connected_sets
    {V : Type u} [Fintype V] (G : SimpleGraph V) (S : Fin 4 → Set V)
    (hconn : ∀ i, (G.induce (S i)).Connected)
    (hdisj : Pairwise fun i j ↦ Disjoint (S i) (S j))
    (hlinks : ∀ i j, i ≠ j → ∃ a ∈ S i, ∃ b ∈ S j, G.Adj a b) :
    IsIsoMinor (completeGraphGraph 4) (Graph.ofSimpleGraph G) := by
  classical
  let Γ := SimpleGraph.toSubgraph G le_top
  let K : Fin 4 → (⊤ : SimpleGraph V).Subgraph := fun i ↦ Γ.induce (S i)
  rw [completeGraphGraph_eq_ofSimpleGraph_top, GM01.ofSimpleGraph_eq_toGraph G]
  apply GM01.isIsoMinor_ofSimpleGraph_of_connected_subgraphs
    (⊤ : SimpleGraph (Fin 4)) (Set.toFinite Γ.verts) K
  · intro i
    exact ⟨fun _ _ ↦ trivial, fun _ _ h ↦ h.2.2⟩
  · intro i
    apply SimpleGraph.Subgraph.connected_iff'.2
    let f : G.induce (S i) →g (K i).coe := {
      toFun := id
      map_rel' := by
        intro a b hab
        exact ⟨a.property, b.property, hab⟩ }
    exact SimpleGraph.Connected.map f (fun x ↦ ⟨x, rfl⟩) (hconn i)
  · exact hdisj
  · intro i j hij
    exact hlinks i j hij

/-- A connected set with three distinct attachments to a disjoint cycle
contains a `K₄` minor, the final configuration in the low-valency proof. -/
theorem isIsoMinor_completeGraphGraph_four_of_cycle_attachments
    {V : Type u} [Fintype V] (G : SimpleGraph V) (H : Set V)
    (hH : (G.induce H).Connected) {z : V} (p : G.Walk z z) (hp : p.IsCycle)
    (havoid : ∀ v ∈ p.support, v ∉ H) (hzH : ∃ a ∈ H, G.Adj a z)
    {x y : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxH : ∃ a ∈ H, G.Adj a x) (hyH : ∃ a ∈ H, G.Adj a y) :
    IsIsoMinor (completeGraphGraph 4) (Graph.ofSimpleGraph G) := by
  classical
  obtain ⟨a, b, q, hq, hzq, hza, hbz, hqp, hpq⟩ := cycle_without_base_path p hp
  obtain ⟨c, d, P, Q, hP, hQ, hcd, hPQ, hPq, hQq, hmarks⟩ :=
    path_split_between_marked_vertices q hq (hpq x hx hxz) (hpq y hy hyz) hxy
  let SP : Set V := {v | v ∈ P.support}
  let SQ : Set V := {v | v ∈ Q.support}
  have hPp : ∀ v ∈ SP, v ∈ p.support := fun v hv ↦ hqp v (hPq v hv)
  have hQp : ∀ v ∈ SQ, v ∈ p.support := fun v hv ↦ hqp v (hQq v hv)
  have hHP : Disjoint H SP := by
    rw [Set.disjoint_left]
    intro v hvH hvP
    exact havoid v (hPp v hvP) hvH
  have hHQ : Disjoint H SQ := by
    rw [Set.disjoint_left]
    intro v hvH hvQ
    exact havoid v (hQp v hvQ) hvH
  have hHz : Disjoint H {z} := by
    rw [Set.disjoint_singleton_right]
    exact havoid z p.start_mem_support
  have hzP : Disjoint ({z} : Set V) SP := by
    rw [Set.disjoint_singleton_left]
    exact fun hv ↦ hzq (hPq z hv)
  have hzQ : Disjoint ({z} : Set V) SQ := by
    rw [Set.disjoint_singleton_left]
    exact fun hv ↦ hzq (hQq z hv)
  have hPC : ∃ v ∈ SP, ∃ w ∈ H, G.Adj w v := by
    rcases hmarks with ⟨hxP, _⟩ | ⟨hyP, _⟩
    · obtain ⟨w, hw, hwx⟩ := hxH
      exact ⟨x, hxP, w, hw, hwx⟩
    · obtain ⟨w, hw, hwy⟩ := hyH
      exact ⟨y, hyP, w, hw, hwy⟩
  have hQC : ∃ v ∈ SQ, ∃ w ∈ H, G.Adj w v := by
    rcases hmarks with ⟨_, hyQ⟩ | ⟨_, hxQ⟩
    · obtain ⟨w, hw, hwy⟩ := hyH
      exact ⟨y, hyQ, w, hw, hwy⟩
    · obtain ⟨w, hw, hwx⟩ := hxH
      exact ⟨x, hxQ, w, hw, hwx⟩
  let S : Fin 4 → Set V := fun i ↦ match i.val with
    | 0 => H
    | 1 => {z}
    | 2 => SP
    | _ => SQ
  apply isIsoMinor_completeGraphGraph_four_of_connected_sets G S ?_ ?_ ?_
  · intro i
    fin_cases i
    · exact hH
    · let : Nonempty ({z} : Set V) := ⟨⟨z, Set.mem_singleton z⟩⟩
      exact (SimpleGraph.IsTree.of_subsingleton : (G.induce ({z} : Set V)).IsTree).connected
    · exact P.connected_induce_support
    · exact Q.connected_induce_support
  · intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp only [S]
    all_goals first
      | exact (hij rfl).elim
      | exact hHz
      | exact hHP
      | exact hHQ
      | exact hzP
      | exact hzQ
      | exact hPQ
      | exact hHz.symm
      | exact hHP.symm
      | exact hHQ.symm
      | exact hzP.symm
      | exact hzQ.symm
      | exact hPQ.symm
  · have h01 : ∃ a ∈ H, ∃ b ∈ ({z} : Set V), G.Adj a b := by
      obtain ⟨w, hw, hwz⟩ := hzH
      exact ⟨w, hw, z, Set.mem_singleton z, hwz⟩
    have h02 : ∃ a ∈ H, ∃ b ∈ SP, G.Adj a b := by
      obtain ⟨v, hv, w, hw, hwv⟩ := hPC
      exact ⟨w, hw, v, hv, hwv⟩
    have h03 : ∃ a ∈ H, ∃ b ∈ SQ, G.Adj a b := by
      obtain ⟨v, hv, w, hw, hwv⟩ := hQC
      exact ⟨w, hw, v, hv, hwv⟩
    have h12 : ∃ a ∈ ({z} : Set V), ∃ b ∈ SP, G.Adj a b :=
      ⟨z, Set.mem_singleton z, a, P.start_mem_support, hza⟩
    have h13 : ∃ a ∈ ({z} : Set V), ∃ b ∈ SQ, G.Adj a b :=
      ⟨z, Set.mem_singleton z, b, Q.end_mem_support, hbz.symm⟩
    have h23 : ∃ a ∈ SP, ∃ b ∈ SQ, G.Adj a b :=
      ⟨c, P.end_mem_support, d, Q.start_mem_support, hcd⟩
    have hflip : ∀ {A B : Set V}, (∃ a ∈ A, ∃ b ∈ B, G.Adj a b) →
        ∃ a ∈ B, ∃ b ∈ A, G.Adj a b := by
      rintro A B ⟨a, ha, b, hb, hab⟩
      exact ⟨b, hb, a, ha, hab.symm⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp only [S]
    all_goals first
      | exact (hij rfl).elim
      | exact h01
      | exact h02
      | exact h03
      | exact h12
      | exact h13
      | exact h23
      | exact hflip h01
      | exact hflip h02
      | exact hflip h03
      | exact hflip h12
      | exact hflip h13
      | exact hflip h23

end GraphMinor.GM10
