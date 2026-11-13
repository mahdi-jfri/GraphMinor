module

public import GraphMinor.Compute.CrossingClassSweep

/-!
# Generating and detecting alternating bridge candidates

This file assembles the generation of the candidates of Section 5.1 of
`docs/crossing/crossing_extractor.tex`, the two stable counting sorts, and the block-stack sweep of
Section 5.2 (steps 1–4, which keep invariants 1–3). The program reads all lengths from memory.
The execution theorem starts with the bridge attachment lists and returns the sweep result.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.Crossing

/-- Generate the candidates of every bridge (Section 5.1), sort them by increasing left endpoint
and decreasing right endpoint, and sweep them with steps 1–4 of Section 5.2. -/
def detectBridgeCandidatesProg : Cmd :=
  .seq candGenProg
    (.seq sortCandProg
      (.seq (.assign rCandCap (.reg rNumCand)) sweepProg))

/-- From attachment lists, compute the alternating candidate pair in linear time.
The hypotheses describe the input arrays, size registers, and word bounds. -/
theorem detectBridgeCandidatesProg_exec {w n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (T : List (Fin n)) (bridges : List (BridgeData (Fin n)))
    (s : State)
    (hrB : s.regs rNumBridges = bridges.length)
    (hrTot : s.regs rTotAtt = totalAttachments H T bridges)
    (hrC : s.regs TwoPaths.rk = T.length)
    (hatt : IsListFamily bridges.length aAttSt aAttEn aAttEnt
      (fun γ : Fin bridges.length => (bridges[γ.1]'γ.2).attachmentIndices H T) s)
    (hw : 2 < 2 ^ w) (hB : bridges.length < 2 ^ w)
    (hcap : 2 * totalAttachments H T bridges < 2 ^ w)
    (hent : (s.arrs aAttEnt).length + 2 < 2 ^ w) (hT : T.length < 2 ^ w) :
    ∃ s' t, Exec w detectBridgeCandidatesProg s s' t ∧
      t ≤ 111 + 29 * bridges.length + 156 * T.length +
        1918 * totalAttachments H T bridges ∧
      (∀ r < 105, s'.regs r = s.regs r) ∧
      (∀ a < 112, s'.arrs a = s.arrs a) ∧
      match sweepCandidates (sortCandidates T.length (allBridgeCandidates H T bridges)) with
      | none => s'.regs rSweepFound = 0
      | some (J, I) =>
        s'.regs rSweepFound = 1 ∧
        s'.regs rOutI1L = J.l ∧ s'.regs rOutI1R = J.r ∧ s'.regs rOutI1G = J.γ ∧
        s'.regs rOutI2L = I.l ∧ s'.regs rOutI2R = I.r ∧ s'.regs rOutI2G = I.γ := by
  let cs := allBridgeCandidates H T bridges
  have hlen : cs.length ≤ 2 * totalAttachments H T bridges :=
    length_allBridgeCandidates_le H T bridges
  have hbounds : ∀ I ∈ cs, I.l < T.length ∧ I.r < T.length ∧ I.γ < 2 ^ w := by
    intro I hI
    obtain ⟨hg, hlr, hr, _, _⟩ := mem_allBridgeCandidates_spec H hI
    exact ⟨lt_trans hlr hr, hr, lt_trans hg hB⟩
  have hends : ∀ I ∈ cs, I.l < T.length ∧ I.r < T.length :=
    fun I hI => ⟨(hbounds I hI).1, (hbounds I hI).2.1⟩
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hc₁⟩ :=
    candGenProg_exec H T bridges s hrB hrTot hatt hw hB hcap hent hT
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hc₂⟩ :=
    sortCandProg_exec T.length (2 * totalAttachments H T bridges) cs s₁
      ((hk₁.1 TwoPaths.rk (by decide)).trans hrC) hc₁ hbounds (by omega) hT (by omega)
  have hperm := sortCandidates_perm hends
  have hlenSort : (sortCandidates T.length cs).length = cs.length := hperm.length_eq
  let s₃ := s₂.setReg rCandCap cs.length
  have hex₃ : Exec w (.assign rCandCap (.reg rNumCand)) s₂ s₃ 2 := by
    apply Exec.assign
    exact TwoPaths.reg_eval (hc₂.1.trans hlenSort) (by omega)
  have hc₃ : IsCandArray (sortCandidates T.length cs) cs.length
      aCandL aCandR aCandG rNumCand s₃ :=
    hc₂.of_eq (by simp [s₃]) rfl rfl rfl
  have hwords : ∀ I ∈ sortCandidates T.length cs,
      I.l < 2 ^ w ∧ I.r < 2 ^ w ∧ I.γ < 2 ^ w := by
    intro I hI
    obtain ⟨hl, hr, hg⟩ := hbounds I (hperm.subset hI)
    exact ⟨lt_trans hl hT, lt_trans hr hT, hg⟩
  obtain ⟨s₄, t₄, hex₄, ht₄, _, hr₄, ha₄, hout⟩ :=
    sweepProg_exec cs.length (sortCandidates T.length cs) s₃ (by omega) (by omega)
      hc₃ (by simp [s₃]) hwords (sortCandidates_pairwise hends)
      (boundedActivePerColor_sortCandidates_allBridgeCandidates H T bridges)
  have hsortCost := sortCandidatesSteps_le T.length cs
  rw [hlenSort] at ht₄
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by omega, ?_, ?_, hout⟩
  · intro r hr
    dsimp only [Reg] at hr
    rw [hr₄ r hr]
    have hrne : r ≠ rCandCap := by dsimp [rCandCap, Reg]; omega
    rw [State.setReg_regs_ne _ _ hrne, hk₂.1 r ?_, hk₁.1 r ?_]
    all_goals simp only [sortCandRegs, candGenRegs, List.mem_cons, List.not_mem_nil,
      or_false, not_or]; dsimp [rG, rM, rTmp1, rTmp2, rTmp3, rTmp4, rNumCand, rCandCap, Reg] at *
              omega
  · intro a ha
    dsimp only [Arr] at ha
    rw [ha₄ a (Nat.lt_trans ha (by decide))]
    change s₂.arrs a = s.arrs a
    rw [hk₂.2 a ?_, hk₁.2 a ?_]
    all_goals simp only [sortCandArrs, candGenArrs, List.mem_cons, List.not_mem_nil,
      or_false, not_or]; dsimp [aCandL, aCandR, aCandG, aSortL, aSortR, aSortG,
        aBucketLen, aBucketPos, Arr] at *
              omega

/-- An unsuccessful sweep on a complete bridge list rules out every crossing in distinct
bridges. This is the negative answer of Section 5.2. -/
theorem no_distinct_bridge_crossing_of_sweep_eq_none {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] {T : List (Fin n)} (hT : T.Nodup)
    {bridges : List (BridgeData (Fin n))}
    (hB : Crossing.ValidBridgeList H (List.finRange n) T bridges)
    (hnone : sweepCandidates (sortCandidates T.length (allBridgeCandidates H T bridges)) = none) :
    ∀ L₁ L₂, IsCrossingPair H T L₁ L₂ → ¬ InDistinctBridges H T L₁ L₂ := by
  let : HP25.WalkSearch (Fin n) := HP25.findWalkInSearch
  let : HP25.LawfulWalkSearch (Fin n) := HP25.findWalkInSearch_lawful
  apply Crossing.not_inDistinctBridges_of_bridgeCrossWith_eq_none H
    (S := Set.univ) (verts := List.finRange n)
    (fun {_ _} _ => Set.mem_univ _) (fun {_ _} _ => List.mem_finRange _)
    (fun _ _ => List.mem_finRange _) hT hB
  exact Crossing.bridgeCrossWith_eq_none_of_sweep H T bridges hnone

/-- A successful sweep selects candidates from different bridges whose endpoints alternate
in the order `J.l < I.l < J.r < I.r`. -/
theorem selected_bridge_candidates_spec {n : ℕ} (H : SimpleGraph (Fin n))
    [DecidableRel H.Adj] (T : List (Fin n)) (bridges : List (BridgeData (Fin n)))
    {J I : Candidate}
    (hfound : sweepCandidates (sortCandidates T.length (allBridgeCandidates H T bridges)) =
      some (J, I)) :
    J ∈ allBridgeCandidates H T bridges ∧ I ∈ allBridgeCandidates H T bridges ∧
      InterleavingDiffColor J I := by
  have hb : ∀ K ∈ allBridgeCandidates H T bridges, K.l < T.length ∧ K.r < T.length := by
    intro K hK
    obtain ⟨_, hlr, hr, _, _⟩ := mem_allBridgeCandidates_spec H hK
    exact ⟨lt_trans hlr hr, hr⟩
  obtain ⟨hJ, hI, hcross⟩ := sweepCandidates_sound (sortCandidates_pairwise hb) hfound
  exact ⟨(sortCandidates_perm hb).subset hJ, (sortCandidates_perm hb).subset hI, hcross⟩

end GraphMinor.Compute
