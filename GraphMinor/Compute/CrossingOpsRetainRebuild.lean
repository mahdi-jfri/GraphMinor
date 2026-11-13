module

public import GraphMinor.Compute.CrossingOpsSubgraphRebuild
public import GraphMinor.Compute.CrossingOpsRetainTest

/-!
# Rebuilding the sparsified graph

The parent arrays, cycle positions, and extra-edge marks are immutable while the
program filters the old adjacency lists. Applying the verified retention expression
to the subgraph builder yields the exact graph specified in Section 7.2.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Rebuild using four parent arrays from consecutive forest blocks. -/
def retainRebuildProg (a_s a_e a_ent pbase a_pos a_mark B R : ℕ) : Cmd :=
  subgraphRebuildProg a_s a_e a_ent B R
    (retainedTest [pbase + 4, pbase + 14, pbase + 24, pbase + 34]
      a_pos a_mark (R + 15) (R + 16) R (R + 3))

/-- The retention program builds the exact sparsified graph in linear time, preserving
all arrays below the output block. Its hypotheses are the encoded graph, computed parent
words, cycle positions, the selected-prefix marks, their saved indices, and word bounds. -/
theorem retainRebuildProg_exec {w N : ℕ} (a_s a_e a_ent pbase a_pos a_mark B R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {D : List (Fin N)}
    {ess : List (List (Fin (N + 1) × Fin (N + 1)))} {s : State}
    (cut : Fin N) (q k : ℕ)
    [DecidableRel (sparsifyGraph G D (apexForests ess) (edgePrefixSet lists k)).Adj]
    (hs : a_s < B) (he : a_e < B) (hent : a_ent < B) (hposB : a_pos < B) (hmarkB : a_mark < B)
    (hadj : IsAdjList G a_s a_e a_ent lists s)
    (hentries : (s.arrs a_ent).length = 2 * G.edgeSet.ncard)
    (hD : D.Nodup) (hDpos : 0 < D.length)
    (hp : List.Forall₂ (fun a edges => a < B ∧ IsBfsParentsAt a edges s)
      [pbase + 4, pbase + 14, pbase + 24, pbase + 34] ess)
    (hq : q ≤ (edgeRow lists cut).length) (hk : (edgeRowsBefore lists cut.val).length + q = k)
    (hpos : s.arrs a_pos = cyclePositions D D.length)
    (hm : s.arrs a_mark = setAt (List.replicate N 0) (edgeBoundaryList lists cut q) 1)
    (hc : s.regs (R + 15) = cut.val) (hlen : s.regs (R + 16) = D.length)
    (hN : s.regs (R + 8) = N) (hw : N + 4 * G.edgeSet.ncard + 2 < 2 ^ w) :
    let H := sparsifyGraph G D (apexForests ess) (edgePrefixSet lists k)
    ∃ s' t, Exec w (retainRebuildProg a_s a_e a_ent pbase a_pos a_mark B R) s s' t ∧
      t ≤ 500 * (N + G.edgeSet.ncard + 1) ∧
      IsAdjList H B (B + 1) (B + 2) (fun u => graphFilterList lists H u.val) s' ∧
      (s'.arrs (B + 2)).length = 2 * H.edgeSet.ncard ∧
      (∀ a, a < B → s'.arrs a = s.arrs a) := by
  classical
  let H := sparsifyGraph G D (apexForests ess) (edgePrefixSet lists k)
  obtain ⟨s', t, hex, ht, hadj', hent', ha, h15, h16⟩ := subgraphRebuildProg_exec (w := w)
    a_s a_e a_ent B R
    (retainedTest [pbase + 4, pbase + 14, pbase + 24, pbase + 34]
      a_pos a_mark (R + 15) (R + 16) R (R + 3))
    hs he hent hadj (show H ≤ G from fun _ _ hh => hh.1) hentries hN hw
    (fun z u v ha h15 h16 hx hy had => by
      have hpz := hp.imp (fun _ _ hh => hh.2.of_arrs_eq (ha _ hh.1))
      exact eval_retainedTest hadj.2 hD hDpos hpz cut u v q k hq hk had
        ((ha _ hposB).trans hpos) ((ha _ hmarkB).trans hm)
        (h15.trans hc) (h16.trans hlen) hx hy (by omega) (by omega))
  rw [retainedTest_four_cost] at ht
  exact ⟨s', t, hex, by omega, hadj', hent', ha⟩

end GraphMinor.Compute.Crossing
