module

public import GraphMinor.Compute.CrossingOpsBfsInit

/-!
# A BFS program producing a scan-first forest

The command initializes its storage and tests every possible root. Its completed discovery
history gives the scan order and the first scanned neighbour of each non-root vertex.
The stored parent array therefore represents a scan-first forest, with time linear in
the number of vertices and the sum of adjacency-list lengths.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Compute a BFS forest using CSR arrays `A,A+1,A+2`, active marks `A+6`, and scratch
marks, parent words, and queue at `A+3,A+4,A+5`. The command reads its size from memory. -/
def bfsForestProg (A R : ℕ) : Cmd := .seq (bfsForestInit A R) (bfsRootsLoop A R)

/-- The BFS program computes a parent array representing a scan-first forest. Its
hypotheses describe only the input graph encoding and word bounds. -/
theorem bfsForestProg_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)}
    (S : Finset (Fin N)) (nbrs : Fin N → List (Fin N)) {s : State}
    (hG : HP25.IsSupportedOn G (↑S))
    (hnd : ∀ v, (nbrs v).Nodup) (hn : ∀ u v, v ∈ nbrs u ↔ G.Adj u v)
    (hl : ∀ u, ∃ st en, IsListAt A (A + 1) (A + 2) u.val st en ((nbrs u).map Fin.val) s ∧ en < 2 ^ w)
    (hactive : s.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t edges, Exec w (bfsForestProg A R) s s' t ∧
      t ≤ 23 + 39 * N + ∑ v : Fin N, (19 + 27 * (nbrs v).length) ∧
      IsScanFirstForest G (↑S) (bfsDiscoveryForest edges) ∧
      IsBfsParentsAt (A + 4) edges s' ∧
      (∀ a, a ≠ A + 3 → a ≠ A + 4 → a ≠ A + 5 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < R ∨ R + 9 ≤ r → s'.regs r = s.regs r) := by
  obtain ⟨s1, t1, he1, ht1, hr1, hrN1, hq1, hv1, hp1, ha1, hregs1⟩ :=
    bfsForestInit_exec A R (s := s) (by simp [hactive]) hN hw
  have hl1 : ∀ u, ∃ st en, IsListAt A (A + 1) (A + 2) u.val st en
      ((nbrs u).map Fin.val) s1 ∧ en < 2 ^ w := by
    intro u
    obtain ⟨st, en, hh, hw'⟩ := hl u
    exact ⟨st, en, hh.of_arrs_eq (ha1 _ (by omega) (by omega) (by omega))
      (ha1 _ (by omega) (by omega) (by omega))
      (ha1 _ (by omega) (by omega) (by omega)), hw'⟩
  have hact1 : s1.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0) :=
    (ha1 _ (by omega) (by omega) (by omega)).trans hactive
  obtain ⟨s2, t2, items2, edges2, he2, ht2, htr2, -, hcover2, hq2, hv2, hp2, ha2, hr2⟩ :=
    bfsRootsLoop_exec A R S nbrs hG hnd hn hN hw (i := 0) (by omega)
      BfsScanTrace.nil (fun _ _ hh => by omega) hl1 hq1 hv1 hp1 hact1 hr1 hrN1
  have hbound := bfsScannedWork_le nbrs items2 items2.length htr2.nodup
  have hzero : bfsScannedWork nbrs [] 0 = 0 := by simp [bfsScannedWork]
  refine ⟨s2, t1 + t2, edges2, .seq he1 he2, ?_,
    htr2.isScanFirstForest hG hcover2, hp2, ?_, ?_⟩
  · simp only [hzero, Nat.add_zero, Nat.sub_zero] at ht2
    omega
  · intro a h3 h4 h5
    exact (ha2 a h3 h4 h5).trans (ha1 a h3 h4 h5)
  · intro r hh
    exact (hr2 r hh).trans (hregs1 r (by omega))

/-- Parent words determine the forest adjacency relation by comparing the two endpoints. -/
theorem bfsDiscoveryForest_adj_of_parents {N a : ℕ} {edges : List (Fin N × Fin N)}
    {s : State} (hp : IsBfsParentsAt a edges s) (u v : Fin N) :
    (bfsDiscoveryForest edges).Adj u v ↔ u ≠ v ∧
      ((s.arrs a)[v.val]'(by have := hp.1; omega) = u.val ∨
       (s.arrs a)[u.val]'(by have := hp.1; omega) = v.val) := by
  simp only [bfsDiscoveryForest, SimpleGraph.fromRel_adj, hp.2.2]

end GraphMinor.Compute.Crossing
