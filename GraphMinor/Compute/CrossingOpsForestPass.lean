module

public import GraphMinor.Compute.CrossingOpsResidualPass

/-!
# One forest and residual pass

A pass computes a BFS forest, retains its parent words, and prepares the next residual
graph in a fresh array block. No parent words from earlier blocks are overwritten.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Compute one scan-first forest and prepare the next residual graph. -/
def forestPassProg (A R : ℕ) : Cmd := .seq (bfsForestProg A R) (residualPassProg A R)

/-- Deleting any graph's edges cannot increase the edge count. -/
theorem edge_ncard_sdiff_le {N : ℕ} (G F : SimpleGraph (Fin N)) :
    (G \ F).edgeSet.ncard ≤ G.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono (show G \ F ≤ G from fun _ _ h => h.1))

/-- One pass returns its scan-first forest, its stored parent words, and the exact residual
input for the next pass. All hypotheses concern the encoded input graph and word size. -/
theorem forestPassProg_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)}
    (S : Finset (Fin N)) {lists : Fin N → List ℕ} {s : State}
    (hG : HP25.IsSupportedOn G (↑S)) (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hentries : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hactive : s.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hw : N + 2 * G.edgeSet.ncard + 2 < 2 ^ w) :
    ∃ s' t edges, Exec w (forestPassProg A R) s s' t ∧
      t ≤ 200 * (N + G.edgeSet.ncard + 1) ∧
      IsScanFirstForest G (↑S) (bfsDiscoveryForest edges) ∧
      IsBfsParentsAt (A + 4) edges s' ∧
      IsAdjList (G \ bfsDiscoveryForest edges) (A + 10) (A + 11) (A + 12)
        (fun u => residualList lists edges u.val) s' ∧
      (s'.arrs (A + 12)).length = 2 * (G \ bfsDiscoveryForest edges).edgeSet.ncard ∧
      s'.arrs (A + 16) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0) ∧
      (∀ a, a < A → s'.arrs a = s.arrs a) ∧
      (∀ r, r < R ∨ R + 15 ≤ r → s'.regs r = s.regs r) := by
  obtain ⟨s1, t1, edges, he1, ht1, hf1, hp1, ha1, hr1⟩ := bfsForestProg_encoded_exec
    (w := w) A R S hG hadj hactive (by omega) (by omega) (by omega)
  have hadj1 := hadj.of_arrs_eq (ha1 A (by omega) (by omega) (by omega))
    (ha1 (A + 1) (by omega) (by omega) (by omega)) (ha1 (A + 2) (by omega) (by omega) (by omega))
  have hent1 : (s1.arrs (A + 2)).length = 2 * G.edgeSet.ncard := by
    rw [ha1 _ (by omega) (by omega) (by omega)]; exact hentries
  have hal1 : s1.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0) :=
    (ha1 _ (by omega) (by omega) (by omega)).trans hactive
  obtain ⟨s2, t2, he2, ht2, hadj2, hent2, hal2, ha2, hr2⟩ :=
    residualPassProg_exec A R S hadj1 hp1 hent1 hal1 hw
  refine ⟨s2, t1 + t2, edges, .seq he1 he2, by omega, hf1,
    hp1.of_arrs_eq (ha2 _ (by omega)), hadj2, hent2, hal2, ?_, ?_⟩
  · intro a hh
    exact (ha2 a (by omega)).trans (ha1 a (by omega) (by omega) (by omega))
  · intro r hh
    exact (hr2 r hh).trans (hr1 r (by omega))

end GraphMinor.Compute.Crossing
