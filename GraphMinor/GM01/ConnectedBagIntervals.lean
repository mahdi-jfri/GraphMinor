module

public import GraphMinor.GM01.PathWidth
public import GraphMinor.Minor.Model
import Mathlib.Order.Fin.Basic

/-!
# Bags meeting a connected subgraph form an interval

The minor monotonicity observation in Graph Minors I, page 40,
replaces each bag by the minor vertices whose connected branches
meet it. To check the interval condition, follow a path within one
branch. If the branch avoided an intermediate bag, edge coverage
would force every vertex reached from its early end to occur in an
early bag. The late end would then violate the interval condition.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- A connected subgraph meeting two bags also meets each intermediate
bag. This proves the interval step in the minor observation on page 40
of Graph Minors I. -/
theorem PathDecomposition.connected_meets_middle {α β : Type*}
    {G K : Graph α β} (D : PathDecomposition G) (hKG : K ≤ G)
    (hKC : GraphConnected K) {i j k : Fin D.length} (hij : i ≤ j) (hjk : j ≤ k)
    (hi : (V(K) ∩ D.bag i).Nonempty) (hk : (V(K) ∩ D.bag k).Nonempty) :
    (V(K) ∩ D.bag j).Nonempty := by
  by_contra hNo
  have hAvoid : ∀ x ∈ V(K), x ∉ D.bag j := by
    intro x hx hxj
    exact hNo ⟨x, hx, hxj⟩
  obtain ⟨x, hxK, hxi⟩ := hi
  obtain ⟨y, hyK, hyk⟩ := hk
  have hReach := hKC.2 x hxK y hyK
  have hEarly : ∃ l : Fin D.length, l ≤ j ∧ y ∈ D.bag l := by
    clear hyK hyk
    induction hReach with
    | refl => exact ⟨i, hij, hxi⟩
    | @tail z w hpath hzw ih =>
      obtain ⟨l, hlj, hzl⟩ := ih
      obtain ⟨e, he⟩ := hzw
      obtain ⟨t, hzt, hwt⟩ := D.edge_covered e z w (he.mono hKG)
      by_cases ht : t ≤ j
      · exact ⟨t, ht, hwt⟩
      · exact False.elim (hAvoid z he.left_mem
          (D.interval l j t hlj (le_of_not_ge ht) ⟨hzl, hzt⟩))
  obtain ⟨l, hlj, hyl⟩ := hEarly
  exact hAvoid y hyK (D.interval l j k hlj hjk ⟨hyl, hyk⟩)

end GraphMinor.GM01
