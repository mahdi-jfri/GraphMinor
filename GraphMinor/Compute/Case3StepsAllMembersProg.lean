module

public import GraphMinor.Compute.Case3StepsScanExec
public import GraphMinor.Compute.Case3StepsFillNoninterior
import GraphMinor.Compute.Case3StepsMultigraphComponents

/-!
# Composing both member scans

The stopping scan first treats the interior members. If it finds a wall,
the program stops with that member's data. Otherwise the second scan keeps
all returned decompositions and fills the noninterior placeholders. The
complete record history is established by execution from empty storage.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Treat interior members and, on exhaustion, fill every other record. -/
def case3AllMembersProg (h : ℕ) (P72 : Cmd) : Cmd :=
  .seq (case3MemberScanProg h P72) (.ite (.reg 0) .skip case3FillNoninteriorProg)

/-- Both scans execute from the routing inputs, and return either a wall
or one permitted record for every selected member. -/
theorem case3AllMembersProg_exec (ω h : ℕ) (h2 : 2 ≤ h) (heven : Even h)
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
      let CodeOK := fun p : Case3SelectedGroup x d.core.Z × List ℕ =>
        (Disjoint (case3SelectedMember x d.core.Z p.1).verts P ∧
          IsValidBranchDecompCode ω (case3CompactMember x D d.core.Z p.1) p.2) ∨
        (¬ Disjoint (case3SelectedMember x d.core.Z p.1).verts P ∧
          p.2 = case3PlaceholderCode (case3CompactMember x D d.core.Z p.1).numEdges)
      let Records := fun (entries : List (Case3SelectedGroup x d.core.Z × List ℕ)) (st : State) =>
        (∀ p ∈ entries, CodeOK p) ∧ (entries.map Prod.fst).Nodup ∧
        (∀ i : Case3SelectedGroup x d.core.Z, i ∈ entries.map Prod.fst) ∧
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
      ∀ s : State,
        (∀ a ∈ case3RoutingArrayIndices, s.arrs a = case3RoutingArray x D d.core.Z a) →
        s.arrs 20 = bitSetList P → s.arrs 32 = case3ScanInverseLabels S →
        (s.arrs 2).length = N → s.regs 14 = S.card → s.regs 52 = L →
        ∃ s' t, Exec w (case3AllMembersProg h P72) s s' t ∧
          t ≤ C * ((N + 1) * (D.numEdges + N + 1)) ∧
          ((s'.regs 0 = 0 ∧ ∃ entries, Records entries s') ∨
            (s'.regs 0 = 1 ∧ WallOut s')) ∧
          (∀ a ∈ case3MemberScanKeepArrays, s'.arrs a = s.arrs a) ∧
          s'.regs 14 = S.card ∧ s'.regs 52 = L := by
  obtain ⟨C, c, hC, hc, hscan⟩ := case3MemberScanProg_exec ω h h2 heven P72 h72
  refine ⟨C + 40002, max 4 c, by omega, by omega, ?_⟩
  intro N S D om hom x d hd hdiv P L cap enc CodeOK Records WallOut w hw s hroutes hP h32 hrank hrn hlimit
  have hw4 := (wordSize_mono_left (Nat.le_max_left 4 c) ((N + 1) * (D.numEdges + N + 1))).trans hw
  have hwc := (wordSize_mono_left (Nat.le_max_right 4 c) ((N + 1) * (D.numEdges + N + 1))).trans hw
  have hkn : x.n ≤ N := by
    simpa only [x, case3SimpleSocietyInput, Fintype.card_fin] using Finset.card_le_univ S
  have hpow : (((N + 1) * (D.numEdges + N + 1)) + 2) ^ 4 < 2 ^ w :=
    (pow_lt_two_pow_wordSize (c := 4) (by decide) _).trans_le (Nat.pow_le_pow_right (by decide) hw4)
  have hNw : N < 2 ^ w := (case3Scan_word_bounds hkn (Nat.le_refl D.numEdges)
    ((case3InputEdges_length_le x D rfl).trans D.numActivePairs_le_numEdges) hpow).2.2.1
  obtain ⟨s₁, t₁, hex₁, ht₁, hresult, harr₁, h14₁, h52₁⟩ :=
    hscan S D om hom d hd hdiv P w hwc s hroutes hP h32 hrank hrn hlimit
  rcases hresult with ⟨hzero, _, entries, hhist⟩ | ⟨hone, hwall⟩
  · rcases hhist with ⟨hcodes, hnd, hinter, hcover, hcap, hbuf, hused, hnum⟩
    have hcodes' : ∀ p ∈ entries, CodeOK p :=
      fun p hp => Or.inl ⟨(hinter p hp).1, hcodes p hp⟩
    have hprior : ∀ p ∈ entries, ¬ Disjoint (case3SelectedMember x d.core.Z p.1).verts P →
        case3RawIndexLabel x p.1.1 < 0 := by
      intro p hp hnot
      exact False.elim (hnot (hinter p hp).1)
    have hcoverage : ∀ i : Case3SelectedGroup x d.core.Z,
        Disjoint (case3SelectedMember x d.core.Z i).verts P ∨ case3RawIndexLabel x i.1 < 0 →
          i ∈ entries.map Prod.fst := by
      intro i hi
      rcases hi with hi | hi
      · exact hcover i hi (case3RawIndexLabel_lt x i.1)
      · omega
    have h32₁ : s₁.arrs 32 = case3ScanInverseLabels S := (harr₁ 32 (by decide)).trans h32
    obtain ⟨s₂, t₂, hex₂, ht₂, ⟨entries', hhist', hcover'⟩, harr₂, hzero₂, h14₂, h52₂, _⟩ :=
      case3FillNoninteriorProg_exec ω x D rfl d hd hdiv (S.orderEmbOfFin rfl).toEmbedding P hw4
        entries s₁ ⟨hcodes', hnd, hprior, hcoverage, hcap, hbuf, hused, hnum⟩
        (fun a ha => (harr₁ a (List.mem_append_right [2, 20, 32] ha)).trans (hroutes a ha))
        ((harr₁ 20 (by decide)).trans hP) h14₁ h52₁
        (by rw [h32₁, case3ScanInverseLabels_length]; exact hkn)
        (by rw [h32₁]; exact case3ScanInverseLabels_getD S)
        (by rw [h32₁]; exact case3ScanInverseLabels_words S hNw)
    rcases hhist' with ⟨hcodes', hnd', _, _, hcap', hbuf', hused', hnum'⟩
    have hexIf : Exec w (.ite (.reg 0) .skip case3FillNoninteriorProg) s₁ s₂ (1 + t₂) :=
      .ite_false (by simp only [Expr.eval, checkWord, hzero, Nat.two_pow_pos, ↓reduceIte]) hex₂
    refine ⟨s₂, t₁ + (1 + t₂), .seq hex₁ hexIf, ?_,
      Or.inl ⟨hzero₂.trans hzero, entries', hcodes', hnd', hcover', hcap', hbuf', hused', hnum'⟩,
      fun a ha => (harr₂ a ha).trans (harr₁ a ha), h14₂, h52₂⟩
    have hv : 1 ≤ (N + 1) * (D.numEdges + N + 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
    nlinarith only [ht₁, ht₂, hv]
  · have h1w : 1 < 2 ^ w := by
      have hp : 1 < (((N + 1) * (D.numEdges + N + 1)) + 2) ^ 4 := by
        have : 1 < ((N + 1) * (D.numEdges + N + 1)) + 2 := by omega
        exact Nat.one_lt_pow (by decide) this
      omega
    have hexIf : Exec w (.ite (.reg 0) .skip case3FillNoninteriorProg) s₁ s₁ (1 + 1) :=
      .ite_true (v := 1) (by simp only [Expr.eval, checkWord, hone, h1w, ↓reduceIte]) (by decide) (.skip s₁)
    refine ⟨s₁, t₁ + 2, .seq hex₁ hexIf, ?_, Or.inr ⟨hone, hwall⟩, harr₁, h14₁, h52₁⟩
    have hv : 1 ≤ (N + 1) * (D.numEdges + N + 1) := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
    nlinarith only [ht₁, hv]

end GraphMinor.Compute
