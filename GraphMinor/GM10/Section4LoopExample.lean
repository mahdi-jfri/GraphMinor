module

public import GraphMinor.GM10.Section4Minors
public import GraphMinor.Minor.Basic
import Mathlib.Tactic.FinCases

/-!
# The loop case in the proof of Graph Minors X, (4.2)(ii)

The proof on page 165 mentions only the two-edge circuit and the
three-edge path as minor obstructions. With loops allowed, two vertices
joined by one edge, with a loop at each vertex, give an extra case.
Both vertices have valency at least two, but neither named obstruction
is a minor: a minor cannot have two non-loop edges when the original
graph has only one. This explains the direct leaf-cut argument used
for the forward direction of (4.2)(ii) in `Section4Minors`.
-/

public section

namespace GraphMinor.GM10

open Graph SimpleGraph

/-- One non-loop edge with a loop at each end, the loop case omitted
by the named minor obstructions in the proof of X, (4.2)(ii), page 165. -/
@[expose] def loopBridgeLoop : Graph (Fin 2) (Fin 3) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y :=
    (e = 0 ∧ x = 0 ∧ y = 0) ∨ (e = 1 ∧ x ≠ y) ∨ (e = 2 ∧ x = 1 ∧ y = 1)
  isLink_symm _ _ := ⟨by decide +revert⟩
  eq_or_eq_of_isLink_of_isLink := by decide +revert
  edge_mem_iff_exists_isLink := by decide +revert
  left_mem_of_isLink _ _ _ _ := Set.mem_univ _

private theorem loopBridgeLoop_edge_eq_one_of_inc_ne
    (e : Fin 3) (x y : Fin 2) (hx : loopBridgeLoop.Inc e x)
    (hy : loopBridgeLoop.Inc e y) (hne : x ≠ y) : e = 1 := by
  dsimp [Graph.Inc, loopBridgeLoop] at hx hy
  decide +revert

/-- No graph with two distinct non-loop edges is a minor of the loop
example. A minor model would send both of these edges to its sole
non-loop edge, contrary to injectivity on edges. -/
theorem not_isIsoMinor_loopBridgeLoop_of_two_nonloop_edges
    {α β : Type*} {H : Graph α β} {d e : β} {a b c f : α}
    (hd : H.IsLink d a b) (hab : a ≠ b)
    (he : H.IsLink e c f) (hcf : c ≠ f) (hde : d ≠ e) :
    ¬ IsIsoMinor H loopBridgeLoop := by
  intro hm
  classical
  obtain ⟨ηv, ηe, hmodel⟩ := exists_isMinorModel_of_isIsoMinor
    (Set.finite_univ : V(loopBridgeLoop).Finite)
    (Set.finite_univ : E(loopBridgeLoop).Finite) hm
  have hbridge : ∀ {k x y}, H.IsLink k x y → x ≠ y → ηe k = 1 := by
    intro k x y hxy hne
    obtain ⟨p, hp, hpi⟩ := (hmodel.inc_iff x hxy.left_mem k hxy.edge_mem).1 hxy.inc_left
    obtain ⟨q, hq, hqi⟩ := (hmodel.inc_iff y hxy.right_mem k hxy.edge_mem).1 hxy.inc_right
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact (hmodel.vertex_disjoint x hxy.left_mem y hxy.right_mem hne).notMem_of_mem_left hp hq
    exact loopBridgeLoop_edge_eq_one_of_inc_ne (ηe k) p q hpi hqi hpq
  exact hde (hmodel.edge_injOn hd.edge_mem he.edge_mem
    ((hbridge hd hab).trans (hbridge he hcf).symm))

/-- The two-edge circuit used in the proof of X, (4.2)(ii). -/
def twoEdgeCircuit : Graph (Fin 2) (Fin 2) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink _ x y := x ≠ y
  isLink_symm _ _ := ⟨fun _ _ h ↦ h.symm⟩
  eq_or_eq_of_isLink_of_isLink := by decide +revert
  edge_mem_iff_exists_isLink := by decide +revert
  left_mem_of_isLink _ _ _ _ := Set.mem_univ _

/-- The loop example has neither of the two minors mentioned in the
proof of Graph Minors X, (4.2)(ii), page 165. -/
theorem loopBridgeLoop_has_neither_named_minor :
    ¬ IsIsoMinor twoEdgeCircuit loopBridgeLoop ∧
      ¬ IsIsoMinor (Graph.ofSimpleGraph (pathGraph 4)) loopBridgeLoop := by
  constructor
  · exact not_isIsoMinor_loopBridgeLoop_of_two_nonloop_edges
      (d := (0 : Fin 2)) (e := (1 : Fin 2)) (a := 0) (b := 1) (c := 0) (f := 1)
      (by change (0 : Fin 2) ≠ 1; decide) (by decide)
      (by change (0 : Fin 2) ≠ 1; decide) (by decide) (by decide)
  · exact not_isIsoMinor_loopBridgeLoop_of_two_nonloop_edges
      (d := s((0 : Fin 4), 1)) (e := s((1 : Fin 4), 2))
      (a := 0) (b := 1) (c := 1) (f := 2)
      (by exact ⟨rfl, (SimpleGraph.mem_edgeSet _).2 (by rw [pathGraph_adj]; decide)⟩)
      (by decide)
      (by exact ⟨rfl, (SimpleGraph.mem_edgeSet _).2 (by rw [pathGraph_adj]; decide)⟩)
      (by decide) (by decide)

private theorem two_le_ncard_incident_of_pair (a b : Fin 3) (x : Fin 2)
    (hab : a ≠ b) (ha : loopBridgeLoop.Inc a x) (hb : loopBridgeLoop.Inc b x) :
    2 ≤ {e ∈ E(loopBridgeLoop) | loopBridgeLoop.Inc e x}.ncard := by
  have hsub : ({a, b} : Set (Fin 3)) ⊆
      {e ∈ E(loopBridgeLoop) | loopBridgeLoop.Inc e x} := by
    rintro e (rfl | rfl)
    · exact ⟨Set.mem_univ _, ha⟩
    · exact ⟨Set.mem_univ _, hb⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rwa [Set.ncard_pair hab] at hle

/-- Both vertices of the loop example have at least two incident edges. -/
theorem loopBridgeLoop_two_high_valency_vertices (x : Fin 2) :
    2 ≤ {e ∈ E(loopBridgeLoop) | loopBridgeLoop.Inc e x}.ncard := by
  fin_cases x
  · apply two_le_ncard_incident_of_pair 0 1 0 (by decide)
    · dsimp [Graph.Inc, loopBridgeLoop]
      decide
    · dsimp [Graph.Inc, loopBridgeLoop]
      decide
  · apply two_le_ncard_incident_of_pair 1 2 1 (by decide)
    · dsimp [Graph.Inc, loopBridgeLoop]
      decide
    · dsimp [Graph.Inc, loopBridgeLoop]
      decide

/-- The loop example has branch-width greater than one, although it has
neither of the named minor obstructions from the proof of X, (4.2)(ii). -/
theorem loopBridgeLoop_not_branchWidth_le_one :
    ¬ branchWidth (Hypergraph.ofGraph loopBridgeLoop Set.finite_univ Set.finite_univ) ≤ 1 := by
  intro hwidth
  let G := Hypergraph.ofGraph loopBridgeLoop Set.finite_univ Set.finite_univ
  have hinc : ∀ x : Fin 2, loopBridgeLoop.Inc 1 x := by
    dsimp [Graph.Inc, loopBridgeLoop]
    decide
  have hcomponent : IsConnectedComponent G G := by
    refine ⟨⟨le_rfl, ⟨0, Set.mem_univ _⟩, ?_⟩, ?_⟩
    · intro x _ y _
      by_cases hxy : x = y
      · exact hxy ▸ SimpleGraph.Reachable.refl x
      · exact SimpleGraph.Adj.reachable ⟨hxy, 1, hinc x, hinc y⟩
    · intro H hH hle
      exact le_antisymm hle hH.1
  have hbound := (branchWidth_le_one_iff_components_le_one_deg_ge_two
    (G := loopBridgeLoop) Set.finite_univ Set.finite_univ).1 hwidth G hcomponent
  have hset : {x ∈ G.vertexSet |
      2 ≤ {e ∈ G.edgeSet | G.Inc e x}.ncard} = Set.univ := by
    ext x
    exact ⟨fun _ ↦ Set.mem_univ _, fun _ ↦
      ⟨Set.mem_univ _, loopBridgeLoop_two_high_valency_vertices x⟩⟩
  rw [hset, Set.ncard_univ, Nat.card_fin] at hbound
  omega

end GraphMinor.GM10
