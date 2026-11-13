module

public import GraphMinor.Compute.CrossingOpsApexPrepare
public import GraphMinor.Compute.CrossingOpsApexTransport
public import GraphMinor.Compute.CrossingOpsForestSequence

/-!
# Computing the four apex forests

The command prepares the augmented graph and then runs four BFS passes, deleting each
forest before the next pass. The numerical forests are renamed to the apex interface,
and all four parent arrays remain available for the edge-retention phase.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Interpret numerical discovery forests on the interface's apex vertices. -/
def apexForests {N : ℕ} (ess : List (List (Fin (N + 1) × Fin (N + 1)))) :
    List (SimpleGraph (Option (Fin N))) :=
  (ess.map bfsDiscoveryForest).map (fun F => F.comap (apexIndexEquiv N).symm)

/-- Prepare the apex and compute four successive BFS forests of its residual graphs. -/
def apexFourForestProg (a_D A R : ℕ) : Cmd :=
  .seq (apexPrepareProg a_D A (A + 10) R) (forestSequenceProg 4 (A + 10) R)

/-- The four-forest command implements Section 7.1 on the apex graph, with time linear
in the old graph size. The input hypotheses are support, an exact CSR encoding, active
marks, distinct cycle vertices, their membership in the active set, and the word bound. -/
theorem apexFourForestProg_exec {w N : ℕ} (a_D A R : ℕ)
    {G : SimpleGraph (Fin N)} (S : Finset (Fin N)) {lists : Fin N → List ℕ}
    {D : List (Fin N)} {s : State} (hDA : a_D < A)
    (hG : HP25.IsSupportedOn G (↑S)) (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hentries : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hD : s.arrs a_D = D.map Fin.val) (hDnd : D.Nodup) (hDmem : ∀ v ∈ D, v ∈ S)
    (hactive : s.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hw : 10 * (N + G.edgeSet.ncard + 1) < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (ess : List (List (Fin (N + 1) × Fin (N + 1)))),
      Exec w (apexFourForestProg a_D A R) s s' t ∧ t ≤ 2000 * (N + G.edgeSet.ncard + 1) ∧
      ess.length = 4 ∧ IsScanFirstSequence (apex G D) (apexVerts (↑S)) (apexForests ess) ∧
      (apexForests ess).length = 4 ∧
      (∀ i (hi : i < ess.length), IsBfsParentsAt (A + 10 + 10 * i + 4) ess[i] s') ∧
      (∀ a, a < A → s'.arrs a = s.arrs a) := by
  obtain ⟨s1, t1, he1, ht1, hadj1, hent1, hal1, ha1⟩ :=
    apexPrepareProg_exec a_D A (A + 10) R S hDA (by omega) hadj hentries hD hDnd hactive hw
  have hsize := apexFinGraph_edge_ncard hadj.2 D hDnd
  have hDlen : D.length ≤ N := by simpa using hDnd.length_le_card
  obtain ⟨s2, t2, ess, he2, ht2, hlen, hseq, hp, ha2, hr2⟩ := fourForestProg_exec (w := w)
    (A + 10) R (apexFinVerts S) (apexFinGraph_supported S hG hDmem) hadj1 hent1 hal1 (by omega)
  refine ⟨s2, t1 + t2, ess, .seq he1 he2, by omega, hlen,
    apex_isScanFirstSequence S hseq, by simp [apexForests, hlen], hp, ?_⟩
  intro a hh
  exact (ha2 a (by omega)).trans (ha1 a hh)

end GraphMinor.Compute.Crossing
