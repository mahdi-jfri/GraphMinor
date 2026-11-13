module

public import GraphMinor.Thomason.DominatingSets
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Many vertices dominate half of a chosen set

Thomason's Lemma 3, page 263 (1984), counts pairs consisting of a vertex
of a chosen set and a vertex which does not dominate it. Counting by the
first coordinate gives an upper bound from minimum degree. If too few
vertices dominate half the set, counting by the second coordinate gives
a larger lower bound. We formalize both counts, including the empty set.
-/

@[expose] public section

namespace GraphMinor.Thomason

open SimpleGraph Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices that leave at most half of `X` undominated. Equivalently,
they dominate at least half of `X`. -/
def verticesDominatingHalf (X : Finset V) : Finset V :=
  univ.filter (fun v => 2 * (X ∩ undominatedVertices G {v}).card ≤ X.card)

/-- Leaving at most half of `X` undominated means dominating at least half. -/
theorem mem_verticesDominatingHalf_iff (X : Finset V) (v : V) :
    v ∈ verticesDominatingHalf G X ↔
      X.card ≤ 2 * (X ∩ dominatedVertices G {v}).card := by
  have heq : X ∩ undominatedVertices G {v} = X \ dominatedVertices G {v} := by
    ext x
    simp only [undominatedVertices, mem_inter, mem_sdiff, mem_univ, true_and]
  have hc := Finset.card_sdiff_add_card_inter X (dominatedVertices G {v})
  simp only [verticesDominatingHalf, mem_filter, mem_univ, true_and]
  rw [heq]
  omega

/-- Domination is a symmetric relation between two individual vertices. -/
private theorem mem_undominated_singleton_comm (x v : V) :
    x ∈ undominatedVertices G {v} ↔ v ∈ undominatedVertices G {x} := by
  simp only [undominatedVertices, dominatedVertices_singleton, mem_sdiff,
    mem_univ, true_and, mem_insert, G.mem_neighborFinset, not_or]
  exact and_congr ne_comm (not_congr (G.adj_comm v x))

/-- Count the pairs missed by a single vertex in the two possible orders. -/
theorem sum_card_inter_undominatedVertices_singleton (X : Finset V) :
    (∑ v : V, (X ∩ undominatedVertices G {v}).card) =
      ∑ x ∈ X, (undominatedVertices G {x}).card := by
  let R : V → V → Prop := fun x v => x ∈ undominatedVertices G {v}
  have hrow (x : V) : (univ : Finset V).bipartiteAbove R x = undominatedVertices G {x} := by
    ext v
    simp only [mem_bipartiteAbove, mem_univ, true_and, R]
    exact mem_undominated_singleton_comm G x v
  have hcol (v : V) : X.bipartiteBelow R v = X ∩ undominatedVertices G {v} := by
    ext x
    simp only [mem_bipartiteBelow, mem_inter, R]
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R (s := X) (t := univ)
  simp only [hrow, hcol] at h
  exact h.symm

/-- Thomason (1984), Lemma 3, p. 263. If twice every degree is at least
`n+m` and `m+3≤n`, at least `m+3` vertices dominate half of any subset.
The order condition is written without truncated subtraction. -/
theorem card_verticesDominatingHalf (m : ℕ)
    (hm : m + 3 ≤ Fintype.card V)
    (hdeg : ∀ v : V, Fintype.card V + m ≤ 2 * G.degree v) (X : Finset V) :
    m + 3 ≤ (verticesDominatingHalf G X).card := by
  classical
  let n := Fintype.card V
  let k := X.card
  let δ := G.minDegree
  let B := univ.filter (fun v => ¬ (2 * (X ∩ undominatedVertices G {v}).card ≤ k))
  let S := ∑ v : V, (X ∩ undominatedVertices G {v}).card
  have hVpos : 0 < Fintype.card V := by omega
  have : Nonempty V := Fintype.card_pos_iff.mp hVpos
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  have hδ : n + m ≤ 2 * δ := by simpa only [n, δ, hv] using hdeg v
  have hδn : δ + 1 ≤ n := by
    have h := G.degree_lt_card_verts v
    dsimp only [δ, n]
    rw [hv]
    omega
  have hsum : S ≤ k * (n - δ - 1) := by
    dsimp only [S]
    rw [sum_card_inter_undominatedVertices_singleton G X]
    calc
      (∑ x ∈ X, (undominatedVertices G {x}).card) ≤ ∑ _ ∈ X, (n - δ - 1) := by
        apply Finset.sum_le_sum
        intro x _
        rw [card_undominatedVertices_singleton]
        have hx := G.minDegree_le_degree x
        dsimp only [n, δ] at *
        omega
      _ = k * (n - δ - 1) := by simp [k]
  have hpartition : (verticesDominatingHalf G X).card + B.card = n := by
    simpa only [verticesDominatingHalf, B, k, card_univ, n] using
      card_filter_add_card_filter_not (s := (univ : Finset V))
        (fun v => 2 * (X ∩ undominatedVertices G {v}).card ≤ X.card)
  by_contra hsmall
  have hBsize : n - m - 2 ≤ B.card := by omega
  have ha : 0 < n - m - 2 := by omega
  have hBad (v : V) (hv : v ∈ B) : k + 1 ≤ 2 * (X ∩ undominatedVertices G {v}).card := by
    have h := (mem_filter.mp hv).2
    omega
  have hlower : B.card * (k + 1) ≤ 2 * S := by
    calc
      B.card * (k + 1) = ∑ _ ∈ B, (k + 1) := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ B, 2 * (X ∩ undominatedVertices G {v}).card :=
        Finset.sum_le_sum fun v hv => hBad v hv
      _ ≤ ∑ v : V, 2 * (X ∩ undominatedVertices G {v}).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (subset_univ B) (fun _ _ _ => Nat.zero_le _)
      _ = 2 * S := by rw [Finset.mul_sum]
  have hfactor : 2 * (n - δ - 1) ≤ n - m - 2 := by omega
  have hupper : 2 * S ≤ k * (n - m - 2) := by
    calc
      2 * S ≤ 2 * (k * (n - δ - 1)) := Nat.mul_le_mul_left 2 hsum
      _ = k * (2 * (n - δ - 1)) := by ring
      _ ≤ k * (n - m - 2) := Nat.mul_le_mul_left k hfactor
  have hprod : (n - m - 2) * (k + 1) ≤ k * (n - m - 2) :=
    (Nat.mul_le_mul_right (k + 1) hBsize).trans (hlower.trans hupper)
  nlinarith only [hprod, ha]

end GraphMinor.Thomason
