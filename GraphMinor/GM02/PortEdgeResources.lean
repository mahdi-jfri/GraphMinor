module

public import GraphMinor.GM02.PortTermination
import GraphMinor.GM02.OrientPairPath

/-!
# Feasible split paths use different original host edges

Each terminal has a unique neighbor, the vertex of its chosen host edge.
A path to the other terminal must contain that neighbor. Vertex-disjoint
paths for different pattern pairs consequently cannot choose the same
host edge at any of their ends. This supplies the edge-resource condition
missing from the printed split test for parallel pattern edges in (4.6).
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set SimpleGraph Classical
universe u v

private theorem first_neighbor_mem {V : Type*} {F : SimpleGraph V} {a b x : V}
    (w : F.Walk a b) (hne : a ≠ b) (hunique : ∀ y, F.Adj a y → y = x) : x ∈ w.support := by
  cases w with
  | nil => exact (hne rfl).elim
  | @cons _ y _ h rest =>
    rw [← hunique y h]
    exact List.mem_cons_of_mem _ rest.start_mem_support

/-- The pair of split terminals belonging to one pattern edge. -/
def portPair {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (i : Fin k) :
    {p // p ∈ (portTermination G H choice).pairs} :=
  ⟨s(portTerminal (i, false), portTerminal (i, true)), Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩

/-- Different pattern-edge indices give different prescribed pairs. -/
theorem portPair_injective {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) : Function.Injective (portPair G H choice) := by
  intro i j h
  have he := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp he with ⟨he, _⟩ | ⟨he, _⟩
  · simpa only [portTerminal, Sum.inr.injEq, Prod.mk.injEq, and_true] using he
  · simp only [portTerminal, Sum.inr.injEq, Prod.mk.injEq, Bool.false_eq_true, and_false] at he

/-- A prescribed split path contains the vertex of each chosen endpoint edge. -/
theorem portPath_chosenEdge_mem {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends) (i : Fin k)
    (P : PairPath (pathGraph (portGraph G H choice)) (portPair G H choice i).val) (side : Bool) :
    portEdge (choice.edge (i, side)).val ∈ P.vertices := by
  obtain ⟨w, hw⟩ := P.exists_oriented_walk
  cases side with
  | false =>
    have hne : (portTerminal (i, false) : PortVertex α β k) ≠ portTerminal (i, true) := by simp [portTerminal]
    have hm := first_neighbor_mem w hne (fun y hy =>
      (portTerminal_adj_iff G H choice (i, false) y).1 hy.1)
    exact hw.le hm
  | true =>
    have hne : (portTerminal (i, true) : PortVertex α β k) ≠ portTerminal (i, false) := by simp [portTerminal]
    have hm := first_neighbor_mem w.reverse hne (fun y hy =>
      (portTerminal_adj_iff G H choice (i, true) y).1 hy.1)
    rw [Walk.support_reverse] at hm
    exact hw.le (List.mem_reverse.1 hm)

/-- Feasibility prohibits different pattern edges from reusing one original host edge. -/
theorem portChoice_edges_ne_of_feasible {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hfeas : (portTermination G H choice).Feasible (portGraph G H choice))
    (i j : Fin k) (hij : i ≠ j) (left right : Bool) :
    (choice.edge (i, left)).val ≠ (choice.edge (j, right)).val := by
  obtain ⟨P, hDisj⟩ := hfeas
  intro he
  have hPi := portPath_chosenEdge_mem G H choice i (P (portPair G H choice i)) left
  have hPj := portPath_chosenEdge_mem G H choice j (P (portPair G H choice j)) right
  have hPairs : portPair G H choice i ≠ portPair G H choice j :=
    fun h => hij (portPair_injective G H choice h)
  have hD := hDisj _ _ hPairs
  rw [← he] at hPj
  exact Set.disjoint_left.1 hD hPi hPj

end GraphMinor.GM02
