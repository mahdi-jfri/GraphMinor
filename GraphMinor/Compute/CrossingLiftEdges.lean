module

public import GraphMinor.Compute.Parse

/-!
# One orientation of the recorded search edges

Replacement records store both orientations of every edge in the recorded component and
boundary. The existing graph parser expects each undirected edge only once. Keeping just
the pairs whose first label is smaller gives the same graph and meets that parser's input
condition. Filtering does not increase the record size.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Keep the increasing orientation of each recorded edge. -/
def liftSearchEdges {N : ℕ} (E : List (Fin N × Fin N)) : List (Fin N × Fin N) :=
  E.filter (fun p => decide (p.1.val < p.2.val))

/-- Removing reverse orientations cannot increase the edge count. -/
theorem liftSearchEdges_length {N : ℕ} (E : List (Fin N × Fin N)) :
    (liftSearchEdges E).length ≤ E.length := List.length_filter_le _ _

/-- An increasing pair survives exactly when it was recorded. -/
theorem mem_liftSearchEdges {N : ℕ} (E : List (Fin N × Fin N)) (p : Fin N × Fin N) :
    p ∈ liftSearchEdges E ↔ p ∈ E ∧ p.1.val < p.2.val := by
  simp [liftSearchEdges]

/-- A duplicate-free list containing both orientations of exactly the graph's edges becomes
an input to the existing simple-graph parser by keeping increasing pairs. -/
theorem liftSearchEdges_simple {N : ℕ} (G : SimpleGraph (Fin N))
    (E : List (Fin N × Fin N)) (hnd : E.Nodup)
    (hE : ∀ a b, (a, b) ∈ E ↔ G.Adj a b) :
    IsSimpleEdgeList G (liftSearchEdges E) := by
  let F := liftSearchEdges E
  have hFnd : F.Nodup := hnd.filter _
  have hinc : ∀ i (hi : i < F.length), F[i].1.val < F[i].2.val := by
    intro i hi
    exact ((mem_liftSearchEdges E _).mp (List.getElem_mem hi)).2
  refine ⟨?_, ?_, ?_⟩
  · intro k hk h
    have := hinc k hk
    rw [h] at this
    exact Nat.lt_irrefl _ this
  · intro i j hij hj h
    have hi : i < F.length := hij.trans hj
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have he : F[i] = F[j] := Prod.ext ha hb
      exact (Nat.ne_of_lt hij) (hFnd.getElem_inj_iff.mp he)
    · have hi' := hinc i hi
      have hj' := hinc j hj
      rw [ha, hb] at hi'
      exact (Nat.lt_asymm hi' hj')
  · intro u v
    constructor
    · intro huv
      have hne : u.val ≠ v.val := fun h => G.ne_of_adj huv (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have hm : (u, v) ∈ F := (mem_liftSearchEdges E _).mpr ⟨(hE u v).mpr huv, hlt⟩
        obtain ⟨k, hk, he⟩ := List.getElem_of_mem hm
        exact ⟨k, hk, Or.inl ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩⟩
      · have hm : (v, u) ∈ F := (mem_liftSearchEdges E _).mpr ⟨(hE v u).mpr huv.symm, hgt⟩
        obtain ⟨k, hk, he⟩ := List.getElem_of_mem hm
        exact ⟨k, hk, Or.inr ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩⟩
    · rintro ⟨k, hk, h | h⟩
      · have hm := ((mem_liftSearchEdges E _).mp (List.getElem_mem hk)).1
        have he : F[k] = (u, v) := Prod.ext h.1 h.2
        rw [he] at hm
        exact (hE u v).mp hm
      · have hm := ((mem_liftSearchEdges E _).mp (List.getElem_mem hk)).1
        have he : F[k] = (v, u) := Prod.ext h.1 h.2
        rw [he] at hm
        exact ((hE v u).mp hm).symm

end GraphMinor.Compute.Crossing
