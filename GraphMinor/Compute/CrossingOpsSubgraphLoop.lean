module

public import GraphMinor.Compute.CrossingOpsSubgraphLists
public import GraphMinor.Compute.CrossingOpsFilterContext

/-!
# Packing a subgraph with a read-only edge test

The vertex loop filters each source list, records its new offsets, and preserves all
input arrays below the output block. Two saved registers carry the cutoff row and
cycle length through the filtering program.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Filter every source list with the edge test and record the packed offsets. -/
def subgraphVertexLoop (a_s a_e a_ent B R : ℕ) (test : Expr) : Cmd :=
  vertexLoopProg R (R + 8) (R + 4) B (B + 1) (filterListProg a_s a_e a_ent (B + 3) R test)

/-- The common vertex loop for a subgraph filter. The test premise specifies its expression
on unchanged input arrays and saved registers, rather than assuming a program execution. -/
theorem subgraphVertexLoop_exec {w N cap : ℕ} (a_s a_e a_ent B R : ℕ) (test : Expr)
    {G H : SimpleGraph (Fin N)} [DecidableRel H.Adj] {lists : Fin N → List ℕ} {s : State}
    (hs : a_s < B) (he : a_e < B) (hent : a_ent < B)
    (hadj : IsAdjList G a_s a_e a_ent lists s) (hHG : H ≤ G)
    (hx : s.regs R = 0) (hN : s.regs (R + 8) = N)
    (hst : s.arrs B = List.replicate N 0) (hen : s.arrs (B + 1) = List.replicate N 0)
    (hb : IsBuf (B + 3) (R + 4) [] cap s)
    (hcap : (flatUpTo (graphFilterList lists H) N).length ≤ cap)
    (hw : N + (s.arrs a_ent).length + cap + 2 < 2 ^ w)
    (htest : ∀ z (u v : Fin N), (∀ a, a < B → z.arrs a = s.arrs a) →
      z.regs (R + 15) = s.regs (R + 15) → z.regs (R + 16) = s.regs (R + 16) →
      z.regs R = u.val → z.regs (R + 3) = v.val → G.Adj u v →
      test.eval w z = some (if H.Adj u v then 1 else 0)) :
    ∃ s' t, Exec w (subgraphVertexLoop a_s a_e a_ent B R test) s s' t ∧
      t ≤ 3 + 22 * N + (17 + test.cost) * (2 * G.edgeSet.ncard) ∧
      IsBuf (B + 3) (R + 4) (flatUpTo (graphFilterList lists H) N)
        (cap - (flatUpTo (graphFilterList lists H) N).length) s' ∧
      s'.arrs B = (List.range N).map (fun x => (flatUpTo (graphFilterList lists H) x).length) ∧
      s'.arrs (B + 1) = (List.range N).map (fun x => (flatUpTo (graphFilterList lists H) (x + 1)).length) ∧
      s'.regs (R + 8) = N ∧ (∀ a, a < B → s'.arrs a = s.arrs a) ∧
      s'.regs (R + 15) = s.regs (R + 15) ∧ s'.regs (R + 16) = s.regs (R + 16) := by
  let L := graphFilterList lists H
  let P : State → Prop := fun z => (∀ a, a < B → z.arrs a = s.arrs a) ∧
    z.regs (R + 15) = s.regs (R + 15) ∧ z.regs (R + 16) = s.regs (R + 16) ∧
    (z.arrs (B + 3)).length = cap
  obtain ⟨s', t, hex, ht, hP, hN', hb', hst', hen'⟩ := vertexLoopProg_exec (w := w)
    R (R + 8) (R + 4) B (B + 1) (B + 3) (filterListProg a_s a_e a_ent (B + 3) R test)
    L (fun x => 9 + (listOf lists x).length * (17 + test.cost)) P
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hcap
    (fun z z' h ha hr => ⟨fun a hh => (ha a (by omega) (by omega)).trans (h.1 a hh),
      (hr _ (by omega)).trans h.2.1, (hr _ (by omega)).trans h.2.2.1, by
        rw [ha _ (by omega) (by omega)]; exact h.2.2.2⟩)
    (fun x hxN z k h hxr hNr hbuf hk => by
      let u : Fin N := ⟨x, hxN⟩
      have hadjz := hadj.of_arrs_eq (h.1 a_s hs) (h.1 a_e he) (h.1 a_ent hent)
      obtain ⟨st, en, hl⟩ := hadjz.1.2.2 u
      have hll : IsListAt a_s a_e a_ent x st en (listOf lists x) z := by simpa [listOf, hxN, u] using hl
      have htotal : (flatUpTo L x).length + k = cap := by
        have hh := h.2.2.2
        rw [hbuf.1] at hh
        simpa only [List.length_append, List.length_replicate] using hh
      have hlt : ∀ y ∈ listOf lists x, y < N := by simpa [listOf, hxN, u] using (hadj.2 u).1
      obtain ⟨z', t', he', ht', hb'', ha, hr⟩ := filterListProg_context_exec (w := w)
        a_s a_e a_ent (B + 3) R test (graphFilterKeep H x) (by omega)
        hll hxr hbuf hk (fun y hy => (hlt y hy).trans (show N < 2 ^ w by omega)) (by omega)
        (by have hh := hl.2.2.1; rw [h.1 a_ent hent] at hh; omega) (by omega) (by omega)
        (fun zz y hy ha hr hry => by
          let v : Fin N := ⟨y, hlt y hy⟩
          have hGuv : G.Adj u v := ((hadj.2 u).2.2.2 v).mp (by simpa [listOf, hxN, u] using hy)
          have hh := htest zz u v (fun a hab => (ha a (by omega)).trans (h.1 a hab))
            ((hr _ (by omega) (by omega) (by omega) (by omega)).trans h.2.1)
            ((hr _ (by omega) (by omega) (by omega) (by omega)).trans h.2.2.1)
            ((hr _ (by omega) (by omega) (by omega) (by omega)).trans hxr) hry hGuv
          simpa only [graphFilterKeep, hxN, hlt y hy, dite_true, decide_eq_true_eq] using hh)
      refine ⟨z', t', he', ht', ⟨fun a hh => (ha a (by omega)).trans (h.1 a hh),
        (hr _ (by omega) (by omega) (by omega) (by omega)).trans h.2.1,
        (hr _ (by omega) (by omega) (by omega) (by omega)).trans h.2.2.1, ?_⟩,
        (hr _ (by omega) (by omega) (by omega) (by omega)).trans hxr,
        (hr _ (by omega) (by omega) (by omega) (by omega)).trans hNr,
        ?_, ha _ (by omega), ha _ (by omega)⟩
      · rw [hb''.1]
        simp only [List.length_append, List.length_replicate]
        change (flatUpTo L x).length + (L x).length + (k - (L x).length) = cap
        omega
      · rw [flatUpTo_succ]; exact hb'')
    ⟨fun _ _ => rfl, rfl, rfl, by simp [hb.1]⟩ hx hN hst hen hb
  have hsum : (∑ x ∈ Finset.range N, (listOf lists x).length) = 2 * G.edgeSet.ncard := by
    rw [← length_flatUpTo]
    exact length_flatUpTo_eq (fun u => by simpa only [listOf_fin] using hadj.2 u)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.sum_mul, hsum] at ht
  refine ⟨s', t, hex, ?_, hb', hst', hen', hN', hP.1, hP.2.1, hP.2.2.1⟩
  have hm : (2 * G.edgeSet.ncard) * (17 + test.cost) = (17 + test.cost) * (2 * G.edgeSet.ncard) := Nat.mul_comm _ _
  rw [hm] at ht
  omega

end GraphMinor.Compute.Crossing
