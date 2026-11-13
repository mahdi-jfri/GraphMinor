module

public import GraphMinor.Compute.CrossingOpsReplBody

/-!
# Rebuilding all replacement lists

The vertex loop applies the replacement body at every vertex, recording the start and end
of each new list. Its cost sums the old adjacency-list lengths, which count each edge twice.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The vertex loop builds the packed replacement lists in linear time. The start and end
arrays and the buffer are initially zero, and the input lists and membership marks are ready. -/
theorem replVertexLoop_exec {w N cap : ℕ} (a_bd a_st a_en A R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {dl bl : List ℕ} {s : State}
    (hbd : a_bd < A) (hst : a_st < A) (hen : a_en < A)
    (hse : a_st ≠ a_en) (hbs : a_bd ≠ a_st) (hbe : a_bd ≠ a_en)
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hbl : s.arrs a_bd = bl) (hsmall : bl.length ≤ 3)
    (hblnd : bl.Nodup) (hblt : ∀ y ∈ bl, y < N)
    (hdel : s.arrs (A + 3) = setAt (List.replicate N 0) dl 1)
    (hboundary : s.arrs (A + 9) = setAt (List.replicate N 0) bl 1)
    (hx : s.regs R = 0) (hN : s.regs (R + 8) = N)
    (hst0 : s.arrs a_st = List.replicate N 0) (hen0 : s.arrs a_en = List.replicate N 0)
    (hb : IsBuf (A + 4) (R + 4) [] cap s)
    (hcap : (flatUpTo (replList lists dl bl) N).length ≤ cap)
    (hw : N + (s.arrs (A + 2)).length + cap + 2 < 2 ^ w) :
    ∃ s' t, Exec w (vertexLoopProg R (R + 8) (R + 4) a_st a_en (replBody a_bd A R)) s s' t ∧
      t ≤ 3 + 133 * N + 130 * G.edgeSet.ncard ∧
      IsBuf (A + 4) (R + 4) (flatUpTo (replList lists dl bl) N)
        (cap - (flatUpTo (replList lists dl bl) N).length) s' ∧
      s'.arrs a_st = (List.range N).map (fun x => (flatUpTo (replList lists dl bl) x).length) ∧
      s'.arrs a_en = (List.range N).map (fun x => (flatUpTo (replList lists dl bl) (x + 1)).length) ∧
      s'.regs (R + 8) = N := by
  let L := replList lists dl bl
  let P : State → Prop := fun z =>
    IsAdjList G A (A + 1) (A + 2) lists z ∧ z.arrs a_bd = bl ∧
    z.arrs (A + 3) = setAt (List.replicate N 0) dl 1 ∧
    z.arrs (A + 9) = setAt (List.replicate N 0) bl 1 ∧
    z.arrs (A + 2) = s.arrs (A + 2) ∧ (z.arrs (A + 4)).length = cap
  obtain ⟨s', t, hex, ht, hP, hN', hb', hst', hen'⟩ := vertexLoopProg_exec (w := w)
    R (R + 8) (R + 4) a_st a_en (A + 4) (replBody a_bd A R) L
    (fun x => 120 + 65 * (listOf lists x).length) P hse (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hcap
    (fun z z' h ha _ => by
      have h0 := ha A (by omega) (by omega)
      have h1 := ha (A + 1) (by omega) (by omega)
      have h2 := ha (A + 2) (by omega) (by omega)
      refine ⟨h.1.of_arrs_eq h0 h1 h2, ?_, ?_, ?_, h2.trans h.2.2.2.2.1, ?_⟩
      · exact (ha a_bd hbs hbe).trans h.2.1
      · exact (ha (A + 3) (by omega) (by omega)).trans h.2.2.1
      · exact (ha (A + 9) (by omega) (by omega)).trans h.2.2.2.1
      · rw [ha (A + 4) (by omega) (by omega)]; exact h.2.2.2.2.2)
    (fun x hx z k h hxr hNr hbuf hk => by
      have htotal : (flatUpTo L x).length + k = cap := by
        have hlen := h.2.2.2.2.2
        rw [hbuf.1] at hlen
        simpa only [List.length_append, List.length_replicate] using hlen
      obtain ⟨z', t', hex', ht', hb'', ha, hr⟩ := replBody_exec (w := w) a_bd A R hbd h.1 h.2.1
        hsmall hblnd hblt h.2.2.1 h.2.2.2.1 hxr hx hbuf hk
        (by rw [h.2.2.2.2.1]; omega)
      refine ⟨z', t', hex', ht', ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · exact h.1.of_arrs_eq (ha A (by omega)) (ha (A + 1) (by omega)) (ha (A + 2) (by omega))
      · exact (ha a_bd (by omega)).trans h.2.1
      · exact (ha (A + 3) (by omega)).trans h.2.2.1
      · exact (ha (A + 9) (by omega)).trans h.2.2.2.1
      · exact (ha (A + 2) (by omega)).trans h.2.2.2.2.1
      · rw [hb''.1]
        simp only [List.length_append, List.length_replicate]
        change (flatUpTo L x).length + (L x).length + (k - (L x).length) = cap
        omega
      · exact (hr R (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)).trans hxr
      · exact (hr (R + 8) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)).trans hNr
      · rw [flatUpTo_succ]; exact hb''
      · exact ha a_st (by omega)
      · exact ha a_en (by omega))
    ⟨hadj, hbl, hdel, hboundary, rfl, by simp [hb.1]⟩ hx hN hst0 hen0 hb
  have hsum : (∑ x ∈ Finset.range N, (listOf lists x).length) = 2 * G.edgeSet.ncard := by
    have hlen := length_flatUpTo_eq (H := G) (L := listOf lists) (by
      intro x; simpa [listOf_fin] using hadj.2 x)
    rw [← hlen, length_flatUpTo]
  refine ⟨s', t, hex, ?_, hb', hst', hen', hN'⟩
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum, hsum] at ht
  omega

end GraphMinor.Compute.Crossing
