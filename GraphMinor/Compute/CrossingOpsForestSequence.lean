module

public import GraphMinor.Compute.CrossingOpsForestPass

/-!
# Successive BFS forests of residual graphs

Each pass computes a forest and removes its edges before the next pass. Fresh array
blocks retain every parent array. Four passes give the scan-first sequence required
by the sparse-certificate construction in Section 7.1.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Run a fixed number of forest passes, using a new block of ten arrays each time. -/
def forestSequenceProg : ℕ → ℕ → ℕ → Cmd
  | 0, _, _ => .skip
  | n + 1, A, R => .seq (forestPassProg A R) (forestSequenceProg n (A + 10) R)

/-- Successive passes produce a scan-first sequence and retain its parent arrays.
The number of passes is fixed in the command, while the vertex count is read from memory. -/
theorem forestSequenceProg_exec {w N : ℕ} (n A R : ℕ) {G : SimpleGraph (Fin N)}
    (S : Finset (Fin N)) {lists : Fin N → List ℕ} {s : State}
    (hG : HP25.IsSupportedOn G (↑S)) (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hentries : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hactive : s.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hw : N + 2 * G.edgeSet.ncard + 2 < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (ess : List (List (Fin N × Fin N))), Exec w (forestSequenceProg n A R) s s' t ∧
      t ≤ 1 + 200 * n * (N + G.edgeSet.ncard + 1) ∧ ess.length = n ∧
      IsScanFirstSequence G (↑S) (ess.map bfsDiscoveryForest) ∧
      (∀ i (hi : i < ess.length), IsBfsParentsAt (A + 10 * i + 4) ess[i] s') ∧
      (∀ a, a < A → s'.arrs a = s.arrs a) ∧
      (∀ r, r < R ∨ R + 15 ≤ r → s'.regs r = s.regs r) := by
  induction n generalizing A G lists s with
  | zero =>
    refine ⟨s, 1, [], .skip s, by simp, rfl, trivial, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    intro i hi
    simp at hi
  | succ n ih =>
    obtain ⟨s1, t1, edges, he1, ht1, hf1, hp1, hadj1, hent1, hal1, ha1, hr1⟩ :=
      forestPassProg_exec A R S hG hadj hentries hactive hw
    have hG1 : HP25.IsSupportedOn (G \ bfsDiscoveryForest edges) (↑S) := fun _ _ h => hG h.1
    have hcard := edge_ncard_sdiff_le G (bfsDiscoveryForest edges)
    obtain ⟨s2, t2, ess, he2, ht2, hlen, hseq, hparents, ha2, hr2⟩ :=
      ih (A + 10) hG1 hadj1 hent1 hal1 (by omega)
    have hbudget : 200 * n * (N + (G \ bfsDiscoveryForest edges).edgeSet.ncard + 1) ≤
        200 * n * (N + G.edgeSet.ncard + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    refine ⟨s2, t1 + t2, edges :: ess, .seq he1 he2, ?_, by simp [hlen],
      ⟨hf1, hseq⟩, ?_, ?_, ?_⟩
    · calc
        t1 + t2 ≤ 200 * (N + G.edgeSet.ncard + 1) +
          (1 + 200 * n * (N + G.edgeSet.ncard + 1)) := by omega
        _ = 1 + 200 * (n + 1) * (N + G.edgeSet.ncard + 1) := by ring
    · intro i hi
      cases i with
      | zero => exact hp1.of_arrs_eq (ha2 _ (by omega))
      | succ i =>
        have hi' : i < ess.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
        have heq : A + 10 * (i + 1) + 4 = (A + 10) + 10 * i + 4 := by omega
        simpa only [List.getElem_cons_succ, heq] using hparents i hi'
    · intro a ha
      exact (ha2 a (by omega)).trans (ha1 a ha)
    · intro r hh
      exact (hr2 r hh).trans (hr1 r hh)

/-- Four BFS passes give the four successive scan-first forests of Section 7.1, with
all four parent arrays stored in memory. -/
theorem fourForestProg_exec {w N : ℕ} (A R : ℕ) {G : SimpleGraph (Fin N)}
    (S : Finset (Fin N)) {lists : Fin N → List ℕ} {s : State}
    (hG : HP25.IsSupportedOn G (↑S)) (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hentries : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hactive : s.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hw : N + 2 * G.edgeSet.ncard + 2 < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (ess : List (List (Fin N × Fin N))), Exec w (forestSequenceProg 4 A R) s s' t ∧
      t ≤ 1 + 800 * (N + G.edgeSet.ncard + 1) ∧ ess.length = 4 ∧
      IsScanFirstSequence G (↑S) (ess.map bfsDiscoveryForest) ∧
      (∀ i (hi : i < ess.length), IsBfsParentsAt (A + 10 * i + 4) ess[i] s') ∧
      (∀ a, a < A → s'.arrs a = s.arrs a) ∧
      (∀ r, r < R ∨ R + 15 ≤ r → s'.regs r = s.regs r) := by
  simpa only [show 200 * 4 = 800 from rfl] using
    forestSequenceProg_exec 4 A R S hG hadj hentries hactive hw

end GraphMinor.Compute.Crossing
