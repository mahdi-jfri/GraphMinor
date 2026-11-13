module

public import GraphMinor.Compute.Case3StepsScanInterior
public import GraphMinor.Compute.Case3StepsScanNoninterior
public import GraphMinor.Compute.Case3StepsScanHistory
public import GraphMinor.Compute.Case3StepsScanInputs
public import GraphMinor.Compute.Case3StepsScanWordBounds
public import GraphMinor.Compute.Case3StepsScanLoopCost
import GraphMinor.Compute.Case3StepsMultigraphComponents

/-!
# One scan iteration preserves the retained history

The history contains only valid branch codes for earlier interior labels.
Its buffer, used length, and record count describe the exact stored bytes.
Every next candidate is either skipped, appends one fresh valid record, or
returns a wall. The two skipping cases extend coverage without adding a
record. The interior case extends coverage by the new selected candidate.
-/

public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

private theorem noninterior_charge (b k a c m N : ℕ) :
    97 * k + 83 * a + 146 ≤ 500 * (b + k + a + c + m + N + 1) := by omega

/-- All three cases of one numeric iteration preserve valid retained
codes and coverage, or produce the exact original-label wall output.
The history assumptions describe only the already processed labels. -/
theorem case3MemberScanBody_history_exec (ω h : ℕ) (h2 : 2 ≤ h) (heven : Even h)
    (P72 : Cmd)
    (h72 : ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h)
      P72 (fun s => s)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
        (om : List (Fin S.card)) (hom : om.Nodup),
      let x := case3SimpleSocietyInput D om hom
      ∀ d : Alg86DivisionOutput x, IsValidAlg86DivisionOutput x d →
      GM13.IsSocietyDivision x.toSociety (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z) →
      ∀ P : Finset (Fin S.card),
      let L := x.n + (case3InputEdges x).length
      let cap := 24 * (N + D.numEdges + 1)
      let enc := case3SelectedRecordsEncoding x D d.core.Z (S.orderEmbOfFin rfl).toEmbedding
      let Hist := fun (k : ℕ) (entries : List (Case3SelectedGroup x d.core.Z × List ℕ)) (st : State) =>
        (∀ p ∈ entries, IsValidBranchDecompCode ω (case3CompactMember x D d.core.Z p.1) p.2) ∧
        (entries.map Prod.fst).Nodup ∧
        (∀ p ∈ entries, Disjoint (case3SelectedMember x d.core.Z p.1).verts P ∧ case3RawIndexLabel x p.1.1 < k) ∧
        (∀ i : Case3SelectedGroup x d.core.Z,
          Disjoint (case3SelectedMember x d.core.Z i).verts P → case3RawIndexLabel x i.1 < k →
            i ∈ entries.map Prod.fst) ∧
        (enc entries).length ≤ cap ∧
        st.arrs 57 = enc entries ++ List.replicate (cap - (enc entries).length) 0 ∧
        st.regs 1 = (enc entries).length ∧ st.regs 2 = entries.length
      let WallOut := fun st : State => ∃ i : Case3SelectedGroup x d.core.Z,
        Disjoint (case3SelectedMember x d.core.Z i).verts P ∧
        let A := case3SelectedMember x d.core.Z i
        let Q := case3PushMultigraph S (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1))
        let V := A.verts.image (S.orderEmbOfFin rfl)
        st.arrs 54 = Q.enc ∧ IsBitSet V 55 st ∧
          IsBitSet ((case3GroupBoundary x d.core.Z i.1).image (S.orderEmbOfFin rfl)) 56 st ∧
        ∃ WA : WallOfHeight h (Q.deleteVerticesCompact Vᶜ), WA.IsValid ∧
          ∃ hnext : (WA.moveOrig Q (compactEmb Vᶜ)).IsValid,
            ((WA.moveOrig Q (compactEmb Vᶜ)).toGMWall h2 heven hnext).graph ≤
              Q.toGMDigraph.toGraph.induce V.toNatSet ∧
            st.arrs 46 = (WA.moveOrig Q (compactEmb Vᶜ)).encList
      ∀ w : ℕ, wordSize c ((N + 1) * (D.numEdges + N + 1)) ≤ w →
      ∀ (k : ℕ), k < L →
      ∀ (entries : List (Case3SelectedGroup x d.core.Z × List ℕ)) (s : State),
        Hist k entries s →
        (∀ a ∈ case3RoutingArrayIndices, s.arrs a = case3RoutingArray x D d.core.Z a) →
        s.arrs 20 = bitSetList P → s.arrs 32 = case3ScanInverseLabels S →
        (s.arrs 2).length = N → s.regs 14 = S.card → s.regs 52 = L → s.regs 54 = k → s.regs 0 = 0 →
        ∃ s' t, Exec w (case3MemberScanBody h P72) s s' t ∧
          t ≤ 7 + C * case3CandidateCostNat x d.core.Z (case3MemberScanCharge x D d.core.Z N) k ∧
          s'.regs 54 = k + 1 ∧
          ((s'.regs 0 = 0 ∧ ∃ entries', Hist (k + 1) entries' s') ∨ (s'.regs 0 = 1 ∧ WallOut s')) ∧
          (∀ a ∈ case3MemberScanKeepArrays, s'.arrs a = s.arrs a) ∧
          s'.regs 14 = S.card ∧ s'.regs 52 = L := by
  obtain ⟨C, c, hC, hc, hinterior⟩ := case3MemberScanBody_interior_exec ω h h2 heven P72 h72
  refine ⟨C + 500, max 4 (2 * c), by omega, by omega, ?_⟩
  intro N S D om hom x d hd hdiv P L cap enc Hist WallOut w hw k hk entries s hHist
    hroutes hP h32 hrank hrn hlimit hindex hflag
  classical
  have hkn : x.n ≤ N := by simpa only [x, case3SimpleSocietyInput, Fintype.card_fin] using Finset.card_le_univ S
  let V := (N + 1) * (D.numEdges + N + 1)
  have hw4 : wordSize 4 V ≤ w := (wordSize_mono_left (Nat.le_max_left 4 (2 * c)) V).trans hw
  have hpow : (V + 2) ^ 4 < 2 ^ w :=
    (pow_lt_two_pow_wordSize (by decide) V).trans_le (Nat.pow_le_pow_right (by decide) hw4)
  have hsimple := (case3InputEdges_length_le x D rfl).trans D.numActivePairs_le_numEdges
  obtain ⟨hw6, hcard, hN, hkeys, hm, hsize, he, hencE, hcap, _⟩ :=
    case3Scan_word_bounds hkn (Nat.le_refl D.numEdges) hsimple hpow
  change cap < 2 ^ w at hcap
  have hDA : 2 + 3 * D.numActivePairs < 2 ^ w := by have hle := D.numActivePairs_le_numEdges; omega
  have hD : s.arrs 3 = D.enc := hroutes 3 (by decide)
  have hin : s.arrs 16 = encGraph x.G := hroutes 16 (by decide)
  have hZ : IsBitSet d.core.Z 10 s := IsBitSet.of_bitSetList _ _ _ (hroutes 10 (by decide))
  have htab : s.arrs 26 = case3AttachmentKeys x d.core.Z := hroutes 26 (by decide)
  have hreps : s.arrs 27 = case3ComponentRepList x d.core.Z := hroutes 27 (by decide)
  have hheads : s.arrs 35 = case3BucketHeads (case3ActivePairOwner x D d.core.Z) L 0 := hroutes 35 (by decide)
  have hnext : s.arrs 36 = case3BucketNext (case3ActivePairOwner x D d.core.Z) 0 := hroutes 36 (by decide)
  have hcounts : s.arrs 37 = case3BucketCounts (case3ActivePairOwner x D d.core.Z) L 0 := hroutes 37 (by decide)
  have hmask : s.arrs 29 = bitSetList (case3GroupLabelSet x d.core.Z) := hroutes 29 (by decide)
  rcases hHist with ⟨hcodes, hnodup, hlabels, hcover, hpre, hbuf, hused, hnum⟩
  have hskipHist (st : State) (hb : st.arrs 57 = s.arrs 57)
      (hu : st.regs 1 = s.regs 1) (hn : st.regs 2 = s.regs 2)
      (hskip : ∀ j : Case3SelectedGroup x d.core.Z,
        Disjoint (case3SelectedMember x d.core.Z j).verts P → case3RawIndexLabel x j.1 ≠ k) :
      Hist (k + 1) entries st := by
    refine ⟨hcodes, hnodup, ?_, case3ScanHistory_coverage_skip x d.core.Z P k entries hcover hskip,
      hpre, hb.trans hbuf, hu.trans hused, hn.trans hnum⟩
    intro p hp
    exact ⟨(hlabels p hp).1, (hlabels p hp).2.trans (Nat.lt_succ_self k)⟩
  let j : Fin L := ⟨k, hk⟩
  by_cases hj : j ∈ case3GroupLabelSet x d.core.Z
  · let raw := (case3GroupLabelEquiv x).symm j
    have hactive : case3GroupActive x d.core.Z raw :=
      (mem_case3GroupLabelSet x d.core.Z raw).mp (by simpa only [raw, Equiv.apply_symm_apply] using hj)
    let i : Case3SelectedGroup x d.core.Z := ⟨raw, hactive⟩
    have hilabel : case3RawIndexLabel x i.1 = k := by
      have hv := congrArg Fin.val ((case3GroupLabelEquiv x).apply_symm_apply j)
      exact (case3GroupLabelEquiv_val x raw).symm.trans hv
    have hfresh : i ∉ entries.map Prod.fst :=
      case3ScanHistory_fresh x d.core.Z k entries (fun p hp => (hlabels p hp).2) i hilabel
    have hremaining := case3ScanHistory_fresh_capacity x D rfl d hd hdiv
      (S.orderEmbOfFin rfl).toEmbedding hkn entries hcodes hnodup i hfresh
    change case3SelectedRecordCapacity x D d.core.Z i ≤ cap - (enc entries).length at hremaining
    have hcount := (case3ScanHistory_count_succ_le x d.core.Z entries hnodup i hfresh).trans_lt hsize
    have hcap' : (enc entries).length + (cap - (enc entries).length) < 2 ^ w := by omega
    have hcost := case3CandidateCostNat_selected x d.core.Z (case3MemberScanCharge x D d.core.Z N) i
    rw [hilabel] at hcost
    by_cases hint : Disjoint (case3SelectedMember x d.core.Z i).verts P
    · have hcallword : wordSize c (algorithm72Size (case3MemberAlgorithm72Input x D d.core.Z i)) ≤ w :=
        (case3MemberCall_wordSize_le x D rfl d.core.Z hdiv i c N hkn).trans
          ((wordSize_mono_left (Nat.le_max_right 4 (2 * c)) V).trans hw)
      obtain ⟨hRA, hRe, hCA, hCe⟩ := case3SelectedMember_word_bounds x D rfl d.core.Z hdiv i he hencE
      obtain ⟨st, t, hex, ht, hidx, hresult, harr, hreg⟩ :=
        hinterior S D om hom d hd i w hcallword hw6 hcard hN hkeys hm hsize he hDA hRA hRe hCA hCe
          (enc entries) (cap - (enc entries).length) entries.length P hint hremaining hcap' hcount s
          hD hin hZ htab hreps hheads hnext hcounts hrn (hindex.trans hilabel.symm)
          (IsBitSet.of_bitSetList _ _ _ hP) hmask hrank
          (by rw [h32, case3ScanInverseLabels_length]; exact hkn)
          (by rw [h32]; exact case3ScanInverseLabels_getD S)
          (by rw [h32]; exact case3ScanInverseLabels_words S hN) hbuf hused hnum
      have ht' : t ≤ 7 + (C + 500) * case3CandidateCostNat x d.core.Z
          (case3MemberScanCharge x D d.core.Z N) k := by
        change t ≤ C * case3MemberScanCharge x D d.core.Z N i at ht
        rw [hcost]
        have hmul := Nat.mul_le_mul_right (case3MemberScanCharge x D d.core.Z N i) (Nat.le_add_right C 500)
        omega
      refine ⟨st, t, hex, ht', hidx.trans (congrArg (fun q => q + 1) hilabel), ?_, ?_, ?_, ?_⟩
      · rcases hresult with ⟨code, hcode, hzero, hu, hn, hb⟩ | ⟨hone, hgraph, hV, hBd, hwall⟩
        · let entries' := entries ++ [(i, code)]
          let r := case3SelectedRecord x D d.core.Z (S.orderEmbOfFin rfl).toEmbedding i code
          change st.regs 1 = (enc entries).length + r.enc.length at hu
          change st.arrs 57 = enc entries ++ r.enc ++
            List.replicate (cap - (enc entries).length - r.enc.length) 0 at hb
          have happ : enc entries' = enc entries ++ r.enc :=
            case3SelectedRecordsEncoding_append_singleton x D d.core.Z (S.orderEmbOfFin rfl).toEmbedding entries i code
          have hlen : (enc entries').length = (enc entries).length + r.enc.length := by rw [happ, List.length_append]
          have hrlen : r.enc.length ≤ case3SelectedRecordCapacity x D d.core.Z i :=
            case3SelectedRecord_length_le x D d.core.Z (S.orderEmbOfFin rfl).toEmbedding i code hcode
          have hpre' : (enc entries').length ≤ cap := by omega
          have hrem : cap - (enc entries).length - r.enc.length = cap - (enc entries').length := by omega
          have hb' : st.arrs 57 = enc entries' ++ List.replicate (cap - (enc entries').length) 0 := by
            rw [hb, ← happ, hrem]
          refine Or.inl ⟨hzero, entries', ?_, case3ScanHistory_nodup_append entries hnodup i code hfresh,
            ?_, case3ScanHistory_coverage_append x d.core.Z P k entries hcover i hilabel code,
            hpre', hb', hu.trans hlen.symm, ?_⟩
          · intro q hq
            rcases List.mem_append.mp hq with hq | hq
            · exact hcodes q hq
            · have hqi : q = (i, code) := List.mem_singleton.mp hq
              exact hqi ▸ hcode
          · intro q hq
            rcases List.mem_append.mp hq with hq | hq
            · exact ⟨(hlabels q hq).1, (hlabels q hq).2.trans (Nat.lt_succ_self k)⟩
            · have hqi : q = (i, code) := List.mem_singleton.mp hq
              subst q
              exact ⟨hint, by rw [hilabel]; exact Nat.lt_succ_self _⟩
          · simpa only [entries', List.length_append, List.length_cons, List.length_nil, Nat.zero_add] using hn
        · exact Or.inr ⟨hone, i, hint, hgraph, hV, hBd, hwall⟩
      · intro a ha
        have hb := case3MemberScanKeepArrays_bounds ha
        exact harr a hb.1 hb.2
      · exact (hreg 14 (by romega) (by romega) (by romega) (Or.inr (Or.inl rfl))).trans hrn
      · exact (hreg 52 (by romega) (by romega) (by romega) (Or.inr (Or.inr (Or.inr rfl)))).trans hlimit
    · obtain ⟨st, t, hex, ht, hidx, harr, hreg, h52, h14⟩ :=
        case3MemberScanBody_noninterior_exec (w := w) (h := h) P72 x D d hd i
          (by omega) hcard hkeys hm hsize he hDA hD hin hZ htab hreps hheads hnext hcounts
          hrn (hindex.trans hilabel.symm) P (IsBitSet.of_bitSetList _ _ _ hP) hint hmask
      have hsmall := noninterior_charge
        (algorithm72Size (case3MemberAlgorithm72Input x D d.core.Z i)) x.n
        (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numActivePairs
        (case3CompactMember x D d.core.Z i).numActivePairs (case3CompactMember x D d.core.Z i).numEdges N
      have ht' : t ≤ 7 + (C + 500) * case3CandidateCostNat x d.core.Z
          (case3MemberScanCharge x D d.core.Z N) k := by
        change _ ≤ 500 * case3MemberScanCharge x D d.core.Z N i at hsmall
        rw [hcost]
        have hmul := Nat.mul_le_mul_right (case3MemberScanCharge x D d.core.Z N i) (Nat.le_add_left 500 C)
        omega
      refine ⟨st, t, hex, ht', hidx.trans (congrArg (fun q => q + 1) hilabel),
        Or.inl ⟨(hreg 0 (by romega)).trans hflag, entries, ?_⟩, ?_, h14.trans hrn, h52.trans hlimit⟩
      · apply hskipHist st (harr 57 (by decide) (by decide) (by decide) (by decide))
          (hreg 1 (by romega)) (hreg 2 (by romega))
        intro q hq heq
        have hqi : q = i := Subtype.ext (case3RawIndexLabel_injective x (heq.trans hilabel.symm))
        exact hint (hqi ▸ hq)
      · intro a ha
        have hb := (case3MemberScanKeepArrays_bounds ha).2
        have hne (q : ℕ) (hq : q ∈ [25, 30, 31, 38, 39, 40, 41, 42, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]) : a ≠ q :=
          fun heq => hb (heq ▸ hq)
        exact harr a (hne 25 (by decide)) (hne 30 (by decide)) (hne 31 (by decide)) (hne 39 (by decide))
  · let st := s.setReg 54 (k + 1)
    have hex : Exec w (case3MemberScanBody h P72) s st 7 :=
      case3MemberScanBody_inactive_exec P72 x d.core.Z j hj (by omega) hsize hmask hindex
    have hcost := case3CandidateCostNat_unselected x d.core.Z (case3MemberScanCharge x D d.core.Z N) j hj
    refine ⟨st, 7, hex, by rw [hcost, Nat.mul_zero, Nat.add_zero], State.setReg_regs_self ..,
      Or.inl ⟨?_, entries, ?_⟩, fun _ _ => rfl, ?_, ?_⟩
    · exact (State.setReg_regs_ne s _ (show (0 : Reg) ≠ 54 by decide)).trans hflag
    · apply hskipHist st rfl
        (State.setReg_regs_ne s _ (show (1 : Reg) ≠ 54 by decide))
        (State.setReg_regs_ne s _ (show (2 : Reg) ≠ 54 by decide))
      intro q _ heq
      have hqj : case3GroupLabelEquiv x q.1 = j := Fin.ext ((case3GroupLabelEquiv_val x q.1).trans heq)
      exact hj (hqj ▸ (mem_case3GroupLabelSet x d.core.Z q.1).mpr q.2)
    · exact (State.setReg_regs_ne s _ (show (14 : Reg) ≠ 54 by decide)).trans hrn
    · exact (State.setReg_regs_ne s _ (show (52 : Reg) ≠ 54 by decide)).trans hlimit

end GraphMinor.Compute
