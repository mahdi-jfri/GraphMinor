module

public import GraphMinor.Compute.CrossingOpsResidualLists

/-!
# Rebuilding every residual adjacency list

The vertex loop filters each old adjacency list against the parent words and records
the new offsets. Its running time sums the old list lengths, counting each old edge twice.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Filter the lists against the parent words and store their new offsets. -/
def residualVertexLoop (A B R : ℕ) : Cmd :=
  vertexLoopProg R (R + 8) (R + 4) B (B + 1)
    (filterListProg A (A + 1) (A + 2) (B + 3) R (withoutParentTest (A + 4) R (R + 3)))

/-- The residual vertex loop runs in linear time and produces the packed residual lists. -/
theorem residualVertexLoop_exec {w N cap : ℕ} (A B R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {edges : List (Fin N × Fin N)} {s : State}
    (hAB : A + 5 ≤ B) (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hp : IsBfsParentsAt (A + 4) edges s) (hentries : (s.arrs (A + 2)).length ≤ cap)
    (hx : s.regs R = 0) (hN : s.regs (R + 8) = N)
    (hst : s.arrs B = List.replicate N 0) (hen : s.arrs (B + 1) = List.replicate N 0)
    (hb : IsBuf (B + 3) (R + 4) [] cap s)
    (hcap : (flatUpTo (residualList lists edges) N).length ≤ cap)
    (hw : N + cap + 2 < 2 ^ w) :
    ∃ s' t, Exec w (residualVertexLoop A B R) s s' t ∧
      t ≤ 3 + 22 * N + 60 * G.edgeSet.ncard ∧
      IsBuf (B + 3) (R + 4) (flatUpTo (residualList lists edges) N)
        (cap - (flatUpTo (residualList lists edges) N).length) s' ∧
      s'.arrs B = (List.range N).map (fun x => (flatUpTo (residualList lists edges) x).length) ∧
      s'.arrs (B + 1) = (List.range N).map (fun x => (flatUpTo (residualList lists edges) (x + 1)).length) ∧
      s'.regs (R + 8) = N := by
  let L := residualList lists edges
  let P : State → Prop := fun z => IsAdjList G A (A + 1) (A + 2) lists z ∧
    IsBfsParentsAt (A + 4) edges z ∧ z.arrs (A + 2) = s.arrs (A + 2) ∧
    (z.arrs (B + 3)).length = cap
  obtain ⟨s', t, he, ht, hP, hN', hb', hst', hen'⟩ := vertexLoopProg_exec (w := w)
    R (R + 8) (R + 4) B (B + 1) (B + 3)
    (filterListProg A (A + 1) (A + 2) (B + 3) R (withoutParentTest (A + 4) R (R + 3)))
    L (fun x => 9 + 30 * (listOf lists x).length) P (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hcap
    (fun z z' h ha _ => ⟨h.1.of_arrs_eq (ha _ (by omega) (by omega))
      (ha _ (by omega) (by omega)) (ha _ (by omega) (by omega)),
      h.2.1.of_arrs_eq (ha _ (by omega) (by omega)),
      (ha _ (by omega) (by omega)).trans h.2.2.1, by
        rw [ha _ (by omega) (by omega)]; exact h.2.2.2⟩)
    (fun x hxN z k h hxr hNr hbuf hk => by
      obtain ⟨st, en, hl⟩ := h.1.1.2.2 ⟨x, hxN⟩
      have hll : IsListAt A (A + 1) (A + 2) x st en (listOf lists x) z := by
        simpa only [listOf, dif_pos hxN] using hl
      have htotal : (flatUpTo L x).length + k = cap := by
        have hh := h.2.2.2
        rw [hbuf.1] at hh
        simpa only [List.length_append, List.length_replicate] using hh
      have henword : en < 2 ^ w := by
        have hh := hl.2.2.1
        rw [h.2.2.1] at hh
        omega
      obtain ⟨z', t', he', ht', hb'', ha, hr⟩ := residualListProg_exec
        A (A + 1) (A + 2) (A + 4) (B + 3) R (by omega) (by omega)
        h.1.2 hxN hll h.2.1 hxr hbuf hk (by omega) henword (by omega) (by omega)
      refine ⟨z', t', he', ht', ⟨?_, ?_, ?_, ?_⟩,
        (hr R (by omega) (by omega) (by omega) (by omega)).trans hxr,
        (hr (R + 8) (by omega) (by omega) (by omega) (by omega)).trans hNr,
        ?_, ha B (by omega), ha (B + 1) (by omega)⟩
      · exact h.1.of_arrs_eq (ha _ (by omega)) (ha _ (by omega)) (ha _ (by omega))
      · exact h.2.1.of_arrs_eq (ha _ (by omega))
      · exact (ha _ (by omega)).trans h.2.2.1
      · rw [hb''.1]
        simp only [List.length_append, List.length_replicate]
        change (flatUpTo L x).length + (L x).length + (k - (L x).length) = cap
        omega
      · rw [flatUpTo_succ]; exact hb'')
    ⟨hadj, hp, rfl, by simp [hb.1]⟩ hx hN hst hen hb
  have hsum : (∑ x ∈ Finset.range N, (listOf lists x).length) = 2 * G.edgeSet.ncard := by
    rw [← length_flatUpTo]
    exact length_flatUpTo_eq (fun u => by simpa [listOf_fin] using hadj.2 u)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum, hsum] at ht
  exact ⟨s', t, he, by omega, hb', hst', hen', hN'⟩

end GraphMinor.Compute.Crossing
