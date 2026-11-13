module

public import GraphMinor.Compute.Case3StepsNoninteriorScanMember
public import GraphMinor.Compute.Case3StepsNoninteriorHistory
public import GraphMinor.Compute.Case3StepsScanInputs
public import GraphMinor.Compute.Case3StepsScanWordBounds
public import GraphMinor.Compute.Case3StepsScanLoopCost
import GraphMinor.Compute.Case3StepsMultigraphComponents

/-!
# History preservation in the noninterior scan

Retained interior entries have valid returned codes. Retained noninterior
entries have the prescribed placeholder code and an earlier label. The
next noninterior candidate is fresh, fits its reserved capacity, and
extends coverage. The skipping cases retain the same record bytes.
-/

public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

private theorem keep_not_work {a : ℕ} (ha : a ∈ case3MemberScanKeepArrays) :
    a ∉ [25, 30, 31, 38, 39, 40, 41, 42, 47, 48, 49, 50, 51, 52, 53, 57, 128] := by
  simp only [case3MemberScanKeepArrays, case3RoutingArrayIndices, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem skip_time (b k a c m N : ℕ) :
    97 * k + 83 * a + 142 ≤ 2500 * (b + k + a + c + m + N + 1) := by omega

/-- One second-scan body preserves the valid/placeholder classification,
uniqueness, and coverage of the retained record history. -/
theorem case3NoninteriorScanBody_history_exec {w N : ℕ} (ω : ℕ)
    (x : Alg81Input) (D : MultiDigraph x.n) (hG : D.toSimpleGraph = x.G)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z))
    (e : Fin x.n ↪ Fin N) (P : Finset (Fin x.n)) :
    let L := x.n + (case3InputEdges x).length
    let cap := 24 * (N + D.numEdges + 1)
    let enc := case3SelectedRecordsEncoding x D d.core.Z e
    let CodeOK := fun p : Case3SelectedGroup x d.core.Z × List ℕ =>
      (Disjoint (case3SelectedMember x d.core.Z p.1).verts P ∧
        IsValidBranchDecompCode ω (case3CompactMember x D d.core.Z p.1) p.2) ∨
      (¬ Disjoint (case3SelectedMember x d.core.Z p.1).verts P ∧
        p.2 = case3PlaceholderCode (case3CompactMember x D d.core.Z p.1).numEdges)
    let Hist := fun (k : ℕ) (entries : List (Case3SelectedGroup x d.core.Z × List ℕ)) (st : State) =>
      (∀ p ∈ entries, CodeOK p) ∧ (entries.map Prod.fst).Nodup ∧
      (∀ p ∈ entries, ¬ Disjoint (case3SelectedMember x d.core.Z p.1).verts P →
        case3RawIndexLabel x p.1.1 < k) ∧
      (∀ i : Case3SelectedGroup x d.core.Z,
        Disjoint (case3SelectedMember x d.core.Z i).verts P ∨ case3RawIndexLabel x i.1 < k →
          i ∈ entries.map Prod.fst) ∧
      (enc entries).length ≤ cap ∧
      st.arrs 57 = enc entries ++ List.replicate (cap - (enc entries).length) 0 ∧
      st.regs 1 = (enc entries).length ∧ st.regs 2 = entries.length
    wordSize 4 ((N + 1) * (D.numEdges + N + 1)) ≤ w →
    ∀ k < L, ∀ (entries : List (Case3SelectedGroup x d.core.Z × List ℕ)) (s : State),
      Hist k entries s →
      (∀ a ∈ case3RoutingArrayIndices, s.arrs a = case3RoutingArray x D d.core.Z a) →
      s.arrs 20 = bitSetList P → s.regs 14 = x.n → s.regs 52 = L → s.regs 54 = k →
      x.n ≤ (s.arrs 32).length →
      (∀ u : Fin x.n, (s.arrs 32).getD u.1 0 = (e u).1) →
      (∀ z ∈ s.arrs 32, z < 2 ^ w) →
      ∃ s' t, Exec w case3NoninteriorScanBody s s' t ∧
        t ≤ 3 + 2500 * case3CandidateCostNat x d.core.Z (case3MemberScanCharge x D d.core.Z N) k ∧
        s'.regs 54 = k ∧ (∃ entries', Hist (k + 1) entries' s') ∧
        (∀ a ∈ case3MemberScanKeepArrays, s'.arrs a = s.arrs a) ∧
        s'.regs 0 = s.regs 0 ∧ s'.regs 14 = x.n ∧ s'.regs 52 = L := by
  intro L cap enc CodeOK Hist hw k hk entries s hHist hroutes hP hrn hlimit hindex hlistlen hlist hwords
  classical
  have hkn : x.n ≤ N := by
    have hc := Fintype.card_le_of_injective e e.injective
    simpa only [Fintype.card_fin] using hc
  let V := (N + 1) * (D.numEdges + N + 1)
  have hpow : (V + 2) ^ 4 < 2 ^ w :=
    (pow_lt_two_pow_wordSize (c := 4) (by decide) V).trans_le (Nat.pow_le_pow_right (by decide) hw)
  have hsimple := (case3InputEdges_length_le x D hG).trans D.numActivePairs_le_numEdges
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
  have hbounds : ∀ p ∈ entries, (case3SelectedRecord x D d.core.Z e p.1 p.2).enc.length ≤
      case3SelectedRecordCapacity x D d.core.Z p.1 := by
    intro p hp
    rcases hcodes p hp with ⟨_, hc⟩ | ⟨_, hc⟩
    · exact case3SelectedRecord_length_le x D d.core.Z e p.1 p.2 hc
    · rw [hc]
      exact case3SelectedRecord_placeholder_length_le x D d.core.Z e p.1
  have hskipHist (st : State) (hb : st.arrs 57 = s.arrs 57)
      (hu : st.regs 1 = s.regs 1) (hn : st.regs 2 = s.regs 2)
      (hskip : ∀ j : Case3SelectedGroup x d.core.Z, case3RawIndexLabel x j.1 = k →
        Disjoint (case3SelectedMember x d.core.Z j).verts P) : Hist (k + 1) entries st := by
    refine ⟨hcodes, hnodup, ?_, case3NoninteriorHistory_coverage_skip x d.core.Z P k entries hcover hskip,
      hpre, hb.trans hbuf, hu.trans hused, hn.trans hnum⟩
    intro p hp hn
    exact (hlabels p hp hn).trans (Nat.lt_succ_self k)
  let j : Fin L := ⟨k, hk⟩
  by_cases hj : j ∈ case3GroupLabelSet x d.core.Z
  · let raw := (case3GroupLabelEquiv x).symm j
    have hactive : case3GroupActive x d.core.Z raw :=
      (mem_case3GroupLabelSet x d.core.Z raw).mp (by simpa only [raw, Equiv.apply_symm_apply] using hj)
    let i : Case3SelectedGroup x d.core.Z := ⟨raw, hactive⟩
    have hilabel : case3RawIndexLabel x i.1 = k := by
      have hv := congrArg Fin.val ((case3GroupLabelEquiv x).apply_symm_apply j)
      exact (case3GroupLabelEquiv_val x raw).symm.trans hv
    have hcost := case3CandidateCostNat_selected x d.core.Z (case3MemberScanCharge x D d.core.Z N) i
    rw [hilabel] at hcost
    by_cases hint : Disjoint (case3SelectedMember x d.core.Z i).verts P
    · obtain ⟨st, t, hex, ht, harr, hreg⟩ :=
        case3NoninteriorScanBody_interior_exec x D d hd i (by omega) hcard hkeys hm hsize he hDA
          hD hin hZ htab hreps hheads hnext hcounts hrn (hindex.trans hilabel.symm)
          P (IsBitSet.of_bitSetList _ _ _ hP) hint hmask
      have hsmall := skip_time (algorithm72Size (case3MemberAlgorithm72Input x D d.core.Z i)) x.n
        (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numActivePairs
        (case3CompactMember x D d.core.Z i).numActivePairs (case3CompactMember x D d.core.Z i).numEdges N
      change _ ≤ 2500 * case3MemberScanCharge x D d.core.Z N i at hsmall
      refine ⟨st, t, hex, by rw [hcost]; omega, (hreg 54 (by romega)).trans hindex,
        ⟨entries, ?_⟩, ?_, hreg 0 (by romega), (hreg 14 (by romega)).trans hrn, (hreg 52 (by romega)).trans hlimit⟩
      · apply hskipHist st (harr 57 (by decide) (by decide) (by decide) (by decide))
          (hreg 1 (by romega)) (hreg 2 (by romega))
        intro q heq
        have hqi : q = i := Subtype.ext (case3RawIndexLabel_injective x (heq.trans hilabel.symm))
        exact hqi ▸ hint
      · intro a ha
        have hb := keep_not_work ha
        have hne (q : ℕ) (hq : q ∈ [25, 30, 31, 38, 39, 40, 41, 42, 47, 48, 49, 50, 51, 52, 53, 57, 128]) : a ≠ q :=
          fun heq => hb (heq ▸ hq)
        exact harr a (hne 25 (by decide)) (hne 30 (by decide)) (hne 31 (by decide)) (hne 39 (by decide))
    · have hfresh := case3NoninteriorHistory_fresh x d.core.Z P k entries hlabels i hint hilabel
      have hremaining := case3NoninteriorHistory_fresh_capacity x D hG d hd hdiv e hkn entries hbounds hnodup i hfresh
      change case3SelectedRecordCapacity x D d.core.Z i ≤ cap - (enc entries).length at hremaining
      have hcount := (case3ScanHistory_count_succ_le x d.core.Z entries hnodup i hfresh).trans_lt hsize
      have hcap' : (enc entries).length + (cap - (enc entries).length) < 2 ^ w := by omega
      obtain ⟨hRA, hRe, hCA, hCe⟩ := case3SelectedMember_word_bounds x D hG d.core.Z hdiv i he hencE
      obtain ⟨st, t, hex, ht, hb, hu, hn, harr, hreg⟩ :=
        case3NoninteriorScanBody_member_exec (w := w) (count := entries.length)
          (remaining := cap - (enc entries).length) x D d hd i (by omega) hcard hkeys hm hsize he hDA
          hD hin hZ htab hreps hheads hnext hcounts hrn (hindex.trans hilabel.symm)
          e (enc entries) P (IsBitSet.of_bitSetList _ _ _ hP) hint hmask hN hRA hRe hCA hCe
          hremaining hcap' hcount hlistlen hlist hwords hbuf hused hnum
      have hbasic : x.n + (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numActivePairs +
          (case3CompactMember x D d.core.Z i).numActivePairs + (case3CompactMember x D d.core.Z i).numEdges + 1 ≤
          case3MemberScanCharge x D d.core.Z N i := by unfold case3MemberScanCharge; omega
      have hmul := Nat.mul_le_mul_left 2500 hbasic
      let code := case3PlaceholderCode (case3CompactMember x D d.core.Z i).numEdges
      let r := case3SelectedRecord x D d.core.Z e i code
      let entries' := entries ++ [(i, code)]
      change st.arrs 57 = enc entries ++ r.enc ++ List.replicate (cap - (enc entries).length - r.enc.length) 0 at hb
      change st.regs 1 = (enc entries).length + r.enc.length at hu
      have happ : enc entries' = enc entries ++ r.enc :=
        case3SelectedRecordsEncoding_append_singleton x D d.core.Z e entries i code
      have hlen : (enc entries').length = (enc entries).length + r.enc.length := by rw [happ, List.length_append]
      have hrlen : r.enc.length ≤ case3SelectedRecordCapacity x D d.core.Z i :=
        case3SelectedRecord_placeholder_length_le x D d.core.Z e i
      have hpre' : (enc entries').length ≤ cap := by omega
      have hrem : cap - (enc entries).length - r.enc.length = cap - (enc entries').length := by omega
      refine ⟨st, t, hex, by rw [hcost]; omega,
        (hreg 54 (by romega) (by romega) (by romega)).trans hindex,
        ⟨entries', ?_, case3ScanHistory_nodup_append entries hnodup i code hfresh, ?_,
          case3NoninteriorHistory_coverage_append x d.core.Z P k entries hcover i hilabel code,
          hpre', ?_, hu.trans hlen.symm, ?_⟩,
        fun a ha => harr a (keep_not_work ha), hreg 0 (by romega) (by romega) (by romega),
        (hreg 14 (by romega) (by romega) (by romega)).trans hrn,
        (hreg 52 (by romega) (by romega) (by romega)).trans hlimit⟩
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hcodes q hq
        · have hqi : q = (i, code) := List.mem_singleton.mp hq
          subst q
          exact Or.inr ⟨hint, rfl⟩
      · intro q hq hnon
        rcases List.mem_append.mp hq with hq | hq
        · exact (hlabels q hq hnon).trans (Nat.lt_succ_self k)
        · have hqi : q = (i, code) := List.mem_singleton.mp hq
          subst q
          rw [hilabel]
          exact Nat.lt_succ_self _
      · rw [hb, ← happ, hrem]
      · simpa only [entries', List.length_append, List.length_cons, List.length_nil, Nat.zero_add] using hn
  · have hex : Exec w case3NoninteriorScanBody s s 3 :=
      case3NoninteriorScanBody_inactive_exec x d.core.Z j hj (by omega) hsize hmask hindex
    have hcost := case3CandidateCostNat_unselected x d.core.Z (case3MemberScanCharge x D d.core.Z N) j hj
    refine ⟨s, 3, hex, by rw [hcost, Nat.mul_zero, Nat.add_zero], hindex, ⟨entries, ?_⟩,
      fun _ _ => rfl, rfl, hrn, hlimit⟩
    apply hskipHist s rfl rfl rfl
    intro q heq
    have hqj : case3GroupLabelEquiv x q.1 = j := Fin.ext ((case3GroupLabelEquiv_val x q.1).trans heq)
    exact False.elim (hj (hqj ▸ (mem_case3GroupLabelSet x d.core.Z q.1).mpr q.2))

end GraphMinor.Compute
