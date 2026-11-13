module

public import GraphMinor.Compute.CrossingOpsBfsForest
public import GraphMinor.Compute.CrossingOpsReplLists

/-!
# BFS directly from an adjacency-list encoding

An adjacency-list encoding already supplies all hypotheses of the BFS forest program.
Converting its numerical entries to finite vertices gives the typed histories, and the
degree sum turns the running-time bound into a bound in vertices and edges.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing SimpleGraph

/-- The BFS program works on an arbitrary valid CSR encoding and returns a scan-first
forest in at most `23 + 58*N + 54*|E|` steps. -/
theorem bfsForestProg_encoded_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)}
    (S : Finset (Fin N)) {lists : Fin N → List ℕ} {s : State}
    (hG : HP25.IsSupportedOn G (↑S)) (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hactive : s.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hN : N < 2 ^ w) (hent : (s.arrs (A + 2)).length < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t edges, Exec w (bfsForestProg A R) s s' t ∧
      t ≤ 23 + 58 * N + 54 * G.edgeSet.ncard ∧
      IsScanFirstForest G (↑S) (bfsDiscoveryForest edges) ∧
      IsBfsParentsAt (A + 4) edges s' ∧
      (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < R ∨ R + 9 ≤ r → s'.regs r = s.regs r) := by
  classical
  let nbrs := fun u => toFin N (lists u)
  have hmap : ∀ u, (nbrs u).map Fin.val = lists u := fun u => map_val_toFin (hadj.2 u).1
  obtain ⟨s', t, edges, he, ht, hf, hp, ha, hr⟩ := bfsForestProg_exec A R S nbrs hG
    (fun u => nodup_toFin (hadj.2 u).2.1 (hadj.2 u).1)
    (fun u v => mem_toFin.trans ((hadj.2 u).2.2.2 v))
    (fun u => by
      obtain ⟨st, en, hl⟩ := hadj.1.2.2 u
      exact ⟨st, en, by simpa only [hmap] using hl, hl.2.2.1.trans_lt hent⟩)
    hactive hN hw
  have hlength : ∀ u, (nbrs u).length = (lists u).length := fun u => by
    have hh := congrArg List.length (hmap u)
    simpa only [List.length_map] using hh
  have hsum : (∑ u : Fin N, (lists u).length) = 2 * G.edgeSet.ncard := by
    have hh : ∀ u, (lists u).length = G.degree u := length_eq_degree hadj.2
    simp only [hh]
    rw [sum_degrees_eq_twice_card_edges, ← Set.ncard_coe_finset, coe_edgeFinset]
  simp only [hlength] at ht
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum, hsum] at ht
  exact ⟨s', t, edges, he, by omega, hf, hp, ha, hr⟩

end GraphMinor.Compute.Crossing
