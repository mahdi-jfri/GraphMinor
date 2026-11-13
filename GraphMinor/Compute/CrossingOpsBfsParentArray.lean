module

public import GraphMinor.Compute.CrossingOpsBfsPush

/-!
# Encoding BFS discovery edges by parent words

A parent array has one word per vertex. A word below `N` names the parent, and the
sentinel `N` means that the vertex has no parent. This file relates array writes to adding
discovery edges, so that the queue history proof applies to the graph stored by the program.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Parent words encode directed discovery edges. The sentinel `N` records no incoming edge. -/
def IsBfsParentsAt {N : ℕ} (a : ℕ) (edges : List (Fin N × Fin N)) (s : State) : Prop :=
  ∃ hlen : (s.arrs a).length = N,
    (∀ i (hi : i < N), (s.arrs a)[i]'(by omega) ≤ N) ∧
    ∀ p c : Fin N, (s.arrs a)[c.val]'(by omega) = p.val ↔ (p, c) ∈ edges

/-- The parent encoding is unchanged when its array is unchanged. -/
theorem IsBfsParentsAt.of_arrs_eq {N a : ℕ} {edges : List (Fin N × Fin N)} {s s' : State}
    (h : IsBfsParentsAt a edges s) (ha : s'.arrs a = s.arrs a) : IsBfsParentsAt a edges s' := by
  rcases h with ⟨hlen, hbound, hmem⟩
  exact ⟨by simpa only [ha] using hlen, by simpa only [ha] using hbound,
    by simpa only [ha] using hmem⟩

/-- Filling all parent words with the sentinel encodes the empty discovery graph. -/
theorem isBfsParentsAt_empty {N a : ℕ} {s : State}
    (ha : s.arrs a = List.replicate N N) : IsBfsParentsAt a ([] : List (Fin N × Fin N)) s := by
  refine ⟨by simp [ha], ?_, ?_⟩
  · intro i hi
    simp only [ha, List.getElem_replicate]
    exact le_rfl
  · intro p c
    simp only [ha, List.getElem_replicate, List.not_mem_nil, iff_false]
    exact Nat.ne_of_gt p.isLt

/-- Writing the parent of a vertex that has no earlier incoming discovery edge appends
exactly the new directed edge to the parent encoding. -/
theorem IsBfsParentsAt.write_fresh {N a : ℕ} {edges : List (Fin N × Fin N)} {s : State}
    (h : IsBfsParentsAt a edges s) (p v : Fin N) (hfresh : ∀ q, (q, v) ∉ edges) :
    IsBfsParentsAt a (edges ++ [(p, v)]) (s.writeArr a v.val p.val) := by
  classical
  obtain ⟨hlen, hbound, hmem⟩ := h
  refine ⟨by simpa only [State.writeArr_arrs_length] using hlen, ?_, ?_⟩
  · intro i hi
    simp only [State.writeArr_arrs_self, List.getElem_set]
    split_ifs
    · exact p.isLt.le
    · exact hbound i hi
  · intro q c
    simp only [State.writeArr_arrs_self, List.getElem_set, List.mem_append, List.mem_singleton]
    by_cases hcv : c = v
    · subst c
      simp only [ite_true, hfresh q, false_or, Prod.mk.injEq, and_true]
      exact Fin.val_injective.eq_iff.trans eq_comm
    · have hidx : v.val ≠ c.val := fun e => hcv (Fin.ext e.symm)
      simp only [hidx, ite_false]
      have hpair : (q, c) ≠ (p, v) := fun e => hcv (congrArg Prod.snd e)
      simp only [hpair, or_false]
      exact hmem q c

/-- The discovery command updates both the queue history and its parent encoding. Freshness
of the incoming edge is supplied by the current BFS history when this command is used. -/
theorem tryPushReg_forest_parents_exec {w N : ℕ} (a_vis a_par a_q R : ℕ)
    {items : List (Fin N)} {edges : List (Fin N × Fin N)} {head : ℕ} {s : State} (v p : Fin N)
    (hvp : a_vis ≠ a_par) (hvq : a_vis ≠ a_q) (hpq : a_par ≠ a_q)
    (hvis : s.arrs a_vis = bfsMarks items) (hparents : IsBfsParentsAt a_par edges s)
    (hq : IsQueueHistory a_q (R + 2) (R + 3) N (items.map Fin.val) head s)
    (hnd : items.Nodup) (hv : s.regs (R + 7) = v.val) (hp : s.regs (R + 4) = p.val)
    (hfresh : v ∉ items → ∀ q, (q, v) ∉ edges)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (tryPushReg a_vis a_par a_q (R + 3) (R + 8) (R + 7) (R + 4)) s s' t ∧
      t ≤ 17 ∧
      IsQueueHistory a_q (R + 2) (R + 3) N
        ((items ++ if v ∈ items then [] else [v]).map Fin.val) head s' ∧
      s'.arrs a_vis = bfsMarks (items ++ if v ∈ items then [] else [v]) ∧
      IsBfsParentsAt a_par (edges ++ if v ∈ items then [] else [(p, v)]) s' ∧
      (∀ a, a ≠ a_vis → a ≠ a_par → a ≠ a_q → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 3 → r ≠ R + 8 → s'.regs r = s.regs r) := by
  obtain ⟨s', t, hex, ht, hq', hvis', hpar', ha, hr⟩ := tryPushReg_forest_exec (w := w)
    a_vis a_par a_q R v p hvp hvq hpq hvis hparents.1 hq hnd hv hp hN hw
  refine ⟨s', t, hex, ht, hq', hvis', ?_, ha, hr⟩
  classical
  by_cases hvm : v ∈ items
  · simp only [hvm, ite_true, List.append_nil] at hpar' ⊢
    exact hparents.of_arrs_eq hpar'
  · simp only [hvm, ite_false] at hpar' ⊢
    exact (hparents.write_fresh p v (hfresh hvm)).of_arrs_eq
      (by simpa only [State.writeArr_arrs_self] using hpar')

end GraphMinor.Compute.Crossing
