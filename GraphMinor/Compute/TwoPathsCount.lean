module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Nodup

/-!
# Counting the recursive calls of Algorithm 5.1

Humeau and Pous, proof of Proposition 5.9 (page 24): "It is not difficult to see that the union
$\mathcal{C}$ of all cycles passed as arguments of $\mathbf{2DP}$ is a planar graph ... The number
$p$ of calls to $\mathbf{2DP}$ is bounded by the number of edges of this planar graph, meaning
$p=O(n)$." and "The number of such searches among all calls to $\mathbf{P\_completion}$ in a run
of $\mathbf{2DP}$ is bounded by the sum of $p$ with the number of edges added by
$\mathbf{P\_completion}$. Both are bounded by the number of edges in $\mathcal{C}$ which is a
$O(n)$."

We count directly instead of using planarity and Euler's formula. The paper only asserts that the
union of the cycles is planar, and the direct count is short. An instance has a vertex set `S` and
a cycle `C ⊆ S`. A split along `P' = a m b` with
`C = a A b B` gives the instances `(S₁, a A b m⁻¹)` and `(S₂, b B a m)` with `S₁ ∪ S₂ = S` and
`S₁ ∩ S₂ = P'`. Then `|S₁| + |S₂| = |S| + |m| + 2` (`card_add_card_sides`), and so:
* `2|S| - |C| - 3` drops by exactly one at each split (`potential_split`). It is at least `0` for
  every instance, so a run makes at most `2N` splits and `4N + 1` calls;
* `|S| - |C|`, the number of vertices of the instance off its cycle, drops by exactly `|m|`
  (`offCycle_split`). It is at most `N`, so the paths `P'` of all splits of a run have at most
  `N` inner vertices in total. Since a completion adds fewer edges than `P'` has vertices, all
  completions of a run add at most `N + 4N` edges and run at most that many searches.
-/

public section

namespace GraphMinor.Compute.TwoPaths

variable {V : Type*} [DecidableEq V]

/-- The two sides of a split meet in the vertices of `P' = a m b`, so their sizes add up to
`|S| + |m| + 2`. -/
theorem card_add_card_sides {S S₁ S₂ : Finset V} {a b : V} {m : List V}
    (hnd : (a :: m ++ [b]).Nodup) (hU : S₁ ∪ S₂ = S) (hI : S₁ ∩ S₂ = (a :: m ++ [b]).toFinset) :
    S₁.card + S₂.card = S.card + m.length + 2 := by
  have h := Finset.card_union_add_card_inter S₁ S₂
  rw [hU, hI, List.toFinset_card_of_nodup hnd] at h
  simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil] at h
  omega

/-- **The potential of the splits.** With `|C| = |A| + |B| + 2`, `|C₁| = |A| + |m| + 2` and
`|C₂| = |B| + |m| + 2`, the potential `2|S| - |C| - 3` is the sum of the potentials of the two
sides plus one. -/
theorem potential_split {S S₁ S₂ : Finset V} {a b : V} {A B m : List V}
    (hnd : (a :: m ++ [b]).Nodup) (hU : S₁ ∪ S₂ = S) (hI : S₁ ∩ S₂ = (a :: m ++ [b]).toFinset)
    (h₁ : (a :: A ++ b :: m.reverse).length + 3 ≤ 2 * S₁.card)
    (h₂ : (b :: B ++ a :: m).length + 3 ≤ 2 * S₂.card) :
    (2 * S₁.card - (a :: A ++ b :: m.reverse).length - 3) +
        (2 * S₂.card - (b :: B ++ a :: m).length - 3) + 1 =
      2 * S.card - (a :: A ++ b :: B).length - 3 := by
  have h := card_add_card_sides hnd hU hI
  simp only [List.cons_append, List.length_cons, List.length_append, List.length_reverse] at h₁ h₂ ⊢
  omega

/-- **The vertices off the cycle.** The number of vertices of an instance off its cycle is the sum
of these numbers for the two sides plus the number `|m|` of inner vertices of `P'`. -/
theorem offCycle_split {S S₁ S₂ : Finset V} {a b : V} {A B m : List V}
    (hnd : (a :: m ++ [b]).Nodup) (hU : S₁ ∪ S₂ = S) (hI : S₁ ∩ S₂ = (a :: m ++ [b]).toFinset)
    (h₁ : (a :: A ++ b :: m.reverse).length ≤ S₁.card)
    (h₂ : (b :: B ++ a :: m).length ≤ S₂.card) :
    (S₁.card - (a :: A ++ b :: m.reverse).length) + (S₂.card - (b :: B ++ a :: m).length) +
        m.length = S.card - (a :: A ++ b :: B).length := by
  have h := card_add_card_sides hnd hU hI
  simp only [List.cons_append, List.length_cons, List.length_append, List.length_reverse] at h₁ h₂ ⊢
  omega

/-- A cycle `C` with at least three distinct vertices inside `S` has `2|S| - |C| - 3 ≥ |S| - 3`,
so the potential of a side is defined without truncation: `|C| + 3 ≤ 2|S|`. -/
theorem length_add_three_le {S : Finset V} {C : List V} (hnd : C.Nodup) (h3 : 3 ≤ C.length)
    (hC : ∀ v ∈ C, v ∈ S) : C.length + 3 ≤ 2 * S.card := by
  have : C.toFinset ⊆ S := fun v hv => hC v (List.mem_toFinset.mp hv)
  have := Finset.card_le_card this
  rw [List.toFinset_card_of_nodup hnd] at this
  omega

end GraphMinor.Compute.TwoPaths
