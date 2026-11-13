module

public import GraphMinor.Compute.MultiDigraph
import Mathlib.Data.List.Sort

/-!
# The order within each tail bucket

The input graph lists an upper pair followed by its reverse. Although this is
not row order, all pairs with a fixed tail already have increasing heads. This
file proves that fact and identifies each filtered row with the usual vertex
order. This is the order needed by output (i) of Algorithm (9.9).
-/

@[expose] public section
namespace GraphMinor.Compute

private theorem pairwise_allPairs99 (n : ℕ) :
    (allPairs n).Pairwise (fun p q => p.1 ≤ q.1 ∧ (p.1 = q.1 → p.2 ≤ q.2)) := by
  unfold allPairs
  apply List.pairwise_flatMap.2
  constructor
  · intro u _
    rw [List.pairwise_map]
    exact (List.pairwise_le_finRange n).imp (fun h => ⟨le_rfl, fun _ => h⟩)
  · apply (List.pairwise_lt_finRange n).imp
    intro u v huv x hx y hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hy
    exact ⟨Nat.le_of_lt huv, fun h => (ne_of_lt huv h).elim⟩

private def pairBlock99 {n : ℕ} (p : Fin n × Fin n) : List (Fin n × Fin n) :=
  if p.1 = p.2 then [(p.1, p.1)] else [(p.1, p.2), (p.2, p.1)]

private theorem mem_pairBlock99 {n : ℕ} {p x : Fin n × Fin n}
    (hx : x ∈ pairBlock99 p) : x = p ∨ x = (p.2, p.1) := by
  by_cases he : p.1 = p.2
  · left
    have h := hx
    simp only [pairBlock99, he, ↓reduceIte, List.mem_singleton] at h
    exact h.trans (Prod.ext he.symm rfl)
  · simpa [pairBlock99, he] using hx

/-- In the canonical pair stream, equal tails occur with nondecreasing heads. -/
theorem pairwise_same_tail_allDirectedPairs99 (n : ℕ) :
    (allDirectedPairs n).Pairwise (fun p q => p.1 = q.1 → p.2 ≤ q.2) := by
  change ((upperPairs n).flatMap pairBlock99).Pairwise _
  apply List.pairwise_flatMap.2
  constructor
  · intro p _
    unfold pairBlock99
    split_ifs with he
    · simp
    · simp [he]
  · have hupper := (pairwise_allPairs99 n).filter
        (fun p => decide (p.1.1 ≤ p.2.1))
    apply hupper.imp_of_mem
    intro p q hp hq hpq x hx y hy hxy
    have hp' := ((mem_upperPairs p).1 hp)
    have hq' := ((mem_upperPairs q).1 hq)
    have hfirst := hpq.1
    have hsecond := hpq.2
    have hs : p.1.1 = q.1.1 → p.2.1 ≤ q.2.1 := fun h => hsecond (Fin.ext h)
    rcases mem_pairBlock99 hx with hx' | hx' <;>
      rcases mem_pairBlock99 hy with hy' | hy' <;>
      rw [hx', hy'] at hxy ⊢ <;>
      (try dsimp only at hxy ⊢) <;> omega

/-- Filtering the canonical pair stream by a fixed tail gives its heads in
vertex order, with no missing or repeated pair. -/
theorem filter_allDirectedPairs_tail99 {n : ℕ} (u : Fin n) :
    (allDirectedPairs n).filter (fun p => decide (p.1 = u)) =
      (List.finRange n).map (fun v => (u, v)) := by
  let lhs := (allDirectedPairs n).filter (fun p => decide (p.1 = u))
  let rhs := (List.finRange n).map (fun v => (u, v))
  have hmem : ∀ p, p ∈ lhs ↔ p ∈ rhs := by
    intro p
    simp only [lhs, rhs, List.mem_filter, mem_allDirectedPairs, true_and,
      decide_eq_true_eq, List.mem_map, List.mem_finRange, true_and]
    constructor
    · intro h
      exact ⟨p.2, Prod.ext h.symm rfl⟩
    · rintro ⟨v, h⟩
      exact (congrArg Prod.fst h).symm
  have hperm : lhs.Perm rhs :=
    (List.perm_ext_iff_of_nodup ((nodup_allDirectedPairs n).filter _)
      ((List.nodup_finRange n).map (fun a b h => congrArg Prod.snd h))).2 hmem
  apply hperm.eq_of_pairwise (le := fun p q => p.2 ≤ q.2)
  · intro p q hp hq hpq hqp
    have hp' : p.1 = u := by simpa [lhs] using hp
    have hq' : q.1 = u := by
      obtain ⟨v, _, h⟩ := List.mem_map.1 hq
      exact (congrArg Prod.fst h).symm
    exact Prod.ext (hp'.trans hq'.symm) (le_antisymm hpq hqp)
  · apply ((pairwise_same_tail_allDirectedPairs99 n).filter _).imp_of_mem
    intro p q hp hq hpq
    have hp' : p.1 = u := by simpa [lhs] using hp
    have hq' : q.1 = u := by simpa [lhs] using hq
    exact hpq (hp'.trans hq'.symm)
  · simpa only [rhs, List.pairwise_map] using List.pairwise_le_finRange n

/-- The active pairs in a tail bucket are exactly the active heads in vertex
order. Zero multiplicities are omitted on both sides. -/
theorem MultiDigraph.filter_activePairsList_tail99 {n : ℕ} (G : MultiDigraph n) (u : Fin n) :
    G.activePairsList.filter (fun p => decide (p.1 = u)) =
      ((List.finRange n).filter (fun v => decide (0 < G.edgeMult u v))).map
        (fun v => (u, v)) := by
  unfold MultiDigraph.activePairsList
  rw [List.filter_comm, filter_allDirectedPairs_tail99, List.filter_map]
  rfl

end GraphMinor.Compute
