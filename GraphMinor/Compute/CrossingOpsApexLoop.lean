module

public import GraphMinor.Compute.CrossingOpsApexBody

/-!
# Packing every apex adjacency list

The vertex loop runs through the old indices and the one new apex index. It records
the packed offsets and sums the old adjacency-list lengths and the cycle length.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Build the numerical apex lists and record their offsets. -/
def apexVertexLoop (a_D A B R : ℕ) : Cmd :=
  vertexLoopProg R (R + 8) (R + 4) B (B + 1) (apexBody a_D (A + 3) A (B + 3) R)

/-- The apex vertex loop stores the exact list layout with a linear running-time bound. -/
theorem apexVertexLoop_exec {w N cap : ℕ} (a_D A B R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {D : List (Fin N)} {s : State}
    (hDA : a_D < A) (hAB : A + 7 ≤ B)
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hD : s.arrs a_D = D.map Fin.val) (hDnd : D.Nodup)
    (hm : s.arrs (A + 3) = setAt (List.replicate N 0) (D.map Fin.val) 1)
    (hx : s.regs R = 0) (hN : s.regs (R + 8) = N + 1) (hNold : s.regs (R + 9) = N)
    (hst : s.arrs B = List.replicate (N + 1) 0) (hen : s.arrs (B + 1) = List.replicate (N + 1) 0)
    (hb : IsBuf (B + 3) (R + 4) [] cap s)
    (hcap : (flatUpTo (apexList lists D) (N + 1)).length ≤ cap)
    (hw : N + 1 + (s.arrs (A + 2)).length + cap + 2 < 2 ^ w) :
    ∃ s' t, Exec w (apexVertexLoop a_D A B R) s s' t ∧
      t ≤ 3 + 56 * (N + 1) + 36 * G.edgeSet.ncard ∧
      IsBuf (B + 3) (R + 4) (flatUpTo (apexList lists D) (N + 1))
        (cap - (flatUpTo (apexList lists D) (N + 1)).length) s' ∧
      s'.arrs B = (List.range (N + 1)).map (fun x => (flatUpTo (apexList lists D) x).length) ∧
      s'.arrs (B + 1) = (List.range (N + 1)).map (fun x => (flatUpTo (apexList lists D) (x + 1)).length) ∧
      s'.regs (R + 8) = N + 1 := by
  let L := apexList lists D
  let P : State → Prop := fun z => IsAdjList G A (A + 1) (A + 2) lists z ∧
    z.arrs a_D = D.map Fin.val ∧
    z.arrs (A + 3) = setAt (List.replicate N 0) (D.map Fin.val) 1 ∧
    z.regs (R + 9) = N ∧ z.arrs (A + 2) = s.arrs (A + 2) ∧ (z.arrs (B + 3)).length = cap
  obtain ⟨s', t, he, ht, hP, hN', hb', hst', hen'⟩ := vertexLoopProg_exec (w := w)
    R (R + 8) (R + 4) B (B + 1) (B + 3) (apexBody a_D (A + 3) A (B + 3) R)
    L (fun x => 25 + 18 * (if x < N then (listOf lists x).length else D.length)) P
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hcap
    (fun z z' h ha hr => ⟨h.1.of_arrs_eq (ha _ (by omega) (by omega))
      (ha _ (by omega) (by omega)) (ha _ (by omega) (by omega)),
      (ha _ (by omega) (by omega)).trans h.2.1,
      (ha _ (by omega) (by omega)).trans h.2.2.1,
      (hr _ (by omega)).trans h.2.2.2.1,
      (ha _ (by omega) (by omega)).trans h.2.2.2.2.1, by
        rw [ha _ (by omega) (by omega)]; exact h.2.2.2.2.2⟩)
    (fun x hxN z k h hxr hNr hbuf hk => by
      have htotal : (flatUpTo L x).length + k = cap := by
        have hh := h.2.2.2.2.2
        rw [hbuf.1] at hh
        simpa only [List.length_append, List.length_replicate] using hh
      obtain ⟨z', t', he', ht', hb'', ha, hr⟩ := apexBody_exec (w := w)
        a_D (A + 3) A (B + 3) R (by omega) (by omega) (by omega)
        h.1 h.2.1 hDnd h.2.2.1 hxr hxN h.2.2.2.1 hbuf hk
        (by rw [h.2.2.2.2.1]; omega)
      refine ⟨z', t', he', ht', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
        (hr R (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hxr,
        (hr (R + 8) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hNr,
        ?_, ha B (by omega), ha (B + 1) (by omega)⟩
      · exact h.1.of_arrs_eq (ha _ (by omega)) (ha _ (by omega)) (ha _ (by omega))
      · exact (ha _ (by omega)).trans h.2.1
      · exact (ha _ (by omega)).trans h.2.2.1
      · exact (hr (R + 9) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.2.2.2.1
      · exact (ha _ (by omega)).trans h.2.2.2.2.1
      · rw [hb''.1]
        simp only [List.length_append, List.length_replicate]
        change (flatUpTo L x).length + (L x).length + (k - (L x).length) = cap
        omega
      · rw [flatUpTo_succ]; exact hb'')
    ⟨hadj, hD, hm, hNold, rfl, by simp [hb.1]⟩ hx hN hst hen hb
  have hsumOld : (∑ x ∈ Finset.range N, (listOf lists x).length) = 2 * G.edgeSet.ncard := by
    rw [← length_flatUpTo]
    exact length_flatUpTo_eq (fun u => by simpa [listOf_fin] using hadj.2 u)
  have hsum : (∑ x ∈ Finset.range (N + 1),
      (if x < N then (listOf lists x).length else D.length)) = 2 * G.edgeSet.ncard + D.length := by
    rw [Finset.sum_range_succ]
    simp only [lt_self_iff_false, ite_false]
    have hh : (∑ x ∈ Finset.range N, (if x < N then (listOf lists x).length else D.length)) =
        ∑ x ∈ Finset.range N, (listOf lists x).length :=
      Finset.sum_congr rfl (fun x hx => by rw [if_pos (Finset.mem_range.mp hx)])
    rw [hh, hsumOld]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum, hsum] at ht
  have hDlen : D.length ≤ N := by simpa using hDnd.length_le_card
  exact ⟨s', t, he, by omega, hb', hst', hen', hN'⟩

end GraphMinor.Compute.Crossing
