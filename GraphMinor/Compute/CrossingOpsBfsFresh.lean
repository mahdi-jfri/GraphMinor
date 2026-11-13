module

public import GraphMinor.Compute.CrossingOpsBfsParentArray

/-!
# The newly discovered prefix of a BFS neighbour list

During one scan, the new queue entries are exactly the neighbours outside the queue history
at the start of the scan. Distinct adjacency-list entries ensure that later entries have not
already been added by an earlier entry of the same scan.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The new neighbours found in the first `j` entries of a neighbour list. -/
def bfsFresh {N : ℕ} (items nbrs : List (Fin N)) (j : ℕ) : List (Fin N) :=
  (nbrs.take j).filter (fun v => v ∉ items)

/-- Extending the scanned prefix adds exactly its next neighbour when that neighbour is new. -/
theorem bfsFresh_succ {N : ℕ} (items nbrs : List (Fin N)) {j : ℕ} (hj : j < nbrs.length) :
    bfsFresh items nbrs (j + 1) = bfsFresh items nbrs j ++
      (if nbrs[j] ∈ items then [] else [nbrs[j]]) := by
  rw [bfsFresh, List.take_succ_eq_append_getElem hj, List.filter_append]
  by_cases h : nbrs[j] ∈ items <;> simp [bfsFresh, h]

/-- The old queue followed by the newly discovered prefix is duplicate-free. -/
theorem bfsFresh_nodup {N : ℕ} (items nbrs : List (Fin N)) (hi : items.Nodup)
    (hn : nbrs.Nodup) (j : ℕ) : (items ++ bfsFresh items nbrs j).Nodup := by
  apply hi.append ((show (nbrs.take j).Nodup from hn.take).filter _)
  intro v hv hf
  have hnot : v ∉ items := of_decide_eq_true (List.mem_filter.mp hf).2
  exact hnot hv

/-- Before the next neighbour is processed, membership in the queue still agrees with
membership before this scan. An adjacency list contains no repeated vertex. -/
theorem bfsFresh_next_mem_iff {N : ℕ} (items nbrs : List (Fin N)) (hn : nbrs.Nodup)
    {j : ℕ} (hj : j < nbrs.length) :
    nbrs[j] ∈ items ++ bfsFresh items nbrs j ↔ nbrs[j] ∈ items := by
  have ht : nbrs[j] ∉ nbrs.take j := by
    intro hm
    have hidx := (List.mem_take_iff_idxOf_lt (List.getElem_mem hj)).mp hm
    rw [hn.idxOf_getElem j hj] at hidx
    exact Nat.lt_irrefl j hidx
  have hf : nbrs[j] ∉ bfsFresh items nbrs j := fun hm => ht (List.mem_filter.mp hm).1
  simp only [List.mem_append, hf, or_false]

/-- No discovery edge has a child outside the old queue followed by the scanned fresh prefix. -/
theorem bfsFresh_edge_child {N : ℕ} (items nbrs : List (Fin N)) (edges : List (Fin N × Fin N))
    (u : Fin N) (j : ℕ) (hchild : ∀ p c, (p, c) ∈ edges → c ∈ items) :
    ∀ p c, (p, c) ∈ edges ++ (bfsFresh items nbrs j).map (fun v => (u, v)) →
      c ∈ items ++ bfsFresh items nbrs j := by
  intro p c he
  rcases List.mem_append.mp he with he | he
  · exact List.mem_append_left _ (hchild p c he)
  · obtain ⟨v, hv, hpair⟩ := List.mem_map.mp he
    have heq : v = c := congrArg Prod.snd hpair
    exact List.mem_append_right _ (heq ▸ hv)

end GraphMinor.Compute.Crossing
