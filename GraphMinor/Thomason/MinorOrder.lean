module

public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Data.Fintype.Card
import GraphMinor.Minor.Basic

/-!
# Vertex counts in simple-graph minors

Choose a vertex from every branch of a minor model. Disjointness makes
this choice injective, so a minor has at most as many vertices as its
non-null host. This controls the order in Thomason's potential reduction.
-/

public section

namespace GraphMinor.Thomason

open Graph Set

universe u v

/-- A minor of a non-null finite simple graph has at most as many vertices.
The injection chooses one vertex in each branch of its minor model. -/
theorem card_le_of_isIsoMinor_ofSimpleGraph {V : Type u} {W : Type v}
    [Fintype V] [Fintype W] [Nonempty V] {G : SimpleGraph V} {H : SimpleGraph W}
    (hm : IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G)) :
    Fintype.card W ≤ Fintype.card V := by
  classical
  have : Nonempty (Sym2 V) := ⟨s(Classical.arbitrary V, Classical.arbitrary V)⟩
  obtain ⟨a, b, hmodel⟩ := exists_isMinorModel_of_isIsoMinor
    (Set.toFinite _) (Set.toFinite _) hm
  choose f hf using fun w : W => hmodel.vertex_nonempty w (Set.mem_univ _)
  apply Fintype.card_le_of_injective f
  intro x y hxy
  by_contra hne
  exact Set.disjoint_left.mp
    (hmodel.vertex_disjoint x (Set.mem_univ _) y (Set.mem_univ _) hne)
    (hf x) (hxy.symm ▸ hf y)

end GraphMinor.Thomason
