module

public import GraphMinor.Compute.Case3StepsNoninteriorStepHistory
import GraphMinor.Compute.Case3StepsMultigraphComponents

/-!
# Filling all noninterior records

Initialize a second counting scan while retaining the interior record
buffer. Its history keeps the returned interior codes and adds exactly
the prescribed placeholders. At the end every selected member occurs
once, all interior codes remain valid, and the complete record prefix has
linear size. The scan has a fixed ambient product time bound.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Complete the member list with records for the noninterior candidates. -/
def case3FillNoninteriorProg : Cmd :=
  .seq (.assign 54 (.const 0)) (forUp 54 (.reg 52) case3NoninteriorScanBody)

private theorem sum_cost (L : ℕ) (f : ℕ → ℕ) :
    3 + (∑ k ∈ Finset.range L, (7 + (3 + 2500 * f k))) =
      3 + 10 * L + 2500 * (∑ k ∈ Finset.range L, f k) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, ← Finset.mul_sum]
  omega

/-- The second scan fills every selected member while retaining the
interior records from step (6), with a fixed linear-product time bound. -/
theorem case3FillNoninteriorProg_exec {w N : ℕ} (ω : ℕ)
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
    ∀ (entries : List (Case3SelectedGroup x d.core.Z × List ℕ)) (s : State),
      Hist 0 entries s →
      (∀ a ∈ case3RoutingArrayIndices, s.arrs a = case3RoutingArray x D d.core.Z a) →
      s.arrs 20 = bitSetList P → s.regs 14 = x.n → s.regs 52 = L →
      x.n ≤ (s.arrs 32).length →
      (∀ u : Fin x.n, (s.arrs 32).getD u.1 0 = (e u).1) →
      (∀ z ∈ s.arrs 32, z < 2 ^ w) →
      ∃ s' t, Exec w case3FillNoninteriorProg s s' t ∧
        t ≤ 40000 * ((N + 1) * (D.numEdges + N + 1)) ∧
        (∃ entries', Hist L entries' s' ∧ ∀ i : Case3SelectedGroup x d.core.Z, i ∈ entries'.map Prod.fst) ∧
        (∀ a ∈ case3MemberScanKeepArrays, s'.arrs a = s.arrs a) ∧
        s'.regs 0 = s.regs 0 ∧ s'.regs 14 = x.n ∧ s'.regs 52 = L ∧ s'.regs 54 = L := by
  intro L cap enc CodeOK Hist hw entries s hHist hroutes hP hrn hlimit hlistlen hlist hwords
  classical
  have hkn : x.n ≤ N := by
    have hc := Fintype.card_le_of_injective e e.injective
    simpa only [Fintype.card_fin] using hc
  let V := (N + 1) * (D.numEdges + N + 1)
  have hpow : (V + 2) ^ 4 < 2 ^ w :=
    (pow_lt_two_pow_wordSize (c := 4) (by decide) V).trans_le (Nat.pow_le_pow_right (by decide) hw)
  have hsimple := (case3InputEdges_length_le x D hG).trans D.numActivePairs_le_numEdges
  obtain ⟨hw6, _, _, _, _, hL, _, _, _, _⟩ :=
    case3Scan_word_bounds hkn (Nat.le_refl D.numEdges) hsimple hpow
  change L < 2 ^ w at hL
  have hw1 : 1 < 2 ^ w := by omega
  let s₀ := s.setReg 54 0
  have hex₀ : Exec w (.assign 54 (.const 0)) s s₀ 2 :=
    .assign (by simp only [Expr.eval, checkWord, Nat.two_pow_pos, ↓reduceIte])
  let Frame := fun st : State =>
    (∀ a ∈ case3MemberScanKeepArrays, st.arrs a = s.arrs a) ∧
    st.regs 0 = s.regs 0 ∧ st.regs 14 = x.n ∧ st.regs 52 = L
  let I := fun (k : ℕ) (st : State) => Frame st ∧ st.regs 54 = k ∧ ∃ entries, Hist k entries st
  let stepCost := fun k : ℕ => 3 + 2500 * case3CandidateCostNat x d.core.Z
    (case3MemberScanCharge x D d.core.Z N) k
  have hFrame₀ : Frame s₀ := by
    refine ⟨fun _ _ => rfl, State.setReg_regs_ne s _ (by decide), ?_, ?_⟩
    · exact (State.setReg_regs_ne s _ (show (14 : Reg) ≠ 54 by decide)).trans hrn
    · exact (State.setReg_regs_ne s _ (show (52 : Reg) ≠ 54 by decide)).trans hlimit
  have hI₀ : I 0 s₀ := ⟨hFrame₀, State.setReg_regs_self .., entries, hHist⟩
  have hhi : ∀ k ≤ L, ∀ st, I k st → st.regs 54 = k ∧ (Expr.reg 52).eval w st = some L := by
    intro k _ st hI
    exact ⟨hI.2.1, by simp only [Expr.eval, checkWord, hI.1.2.2.2, hL, ↓reduceIte]⟩
  have hbody : ∀ k < L, Triple w (I k) case3NoninteriorScanBody
      (fun st => I (k + 1) (st.setReg 54 (k + 1)) ∧ st.regs 54 = k) (fun _ => stepCost k) := by
    intro k hk st hI
    rcases hI with ⟨hframe, hindex, entries, hhist⟩
    have hkeeproute {a : ℕ} (ha : a ∈ case3RoutingArrayIndices) : a ∈ case3MemberScanKeepArrays :=
      List.mem_append_right [2, 20, 32] ha
    have hroutes' : ∀ a ∈ case3RoutingArrayIndices, st.arrs a = case3RoutingArray x D d.core.Z a :=
      fun a ha => (hframe.1 a (hkeeproute ha)).trans (hroutes a ha)
    obtain ⟨st', t, hex, ht, hidx, ⟨entries', hhist'⟩, harr, hzero, h14, h52⟩ :=
      case3NoninteriorScanBody_history_exec ω x D hG d hd hdiv e P hw k hk entries st hhist hroutes'
        ((hframe.1 20 (by decide)).trans hP) hframe.2.2.1 hframe.2.2.2 hindex
        (by rw [hframe.1 32 (by decide)]; exact hlistlen)
        (by rw [hframe.1 32 (by decide)]; exact hlist)
        (by rw [hframe.1 32 (by decide)]; exact hwords)
    have hFrame' : Frame (st'.setReg 54 (k + 1)) := by
      refine ⟨fun a ha => (harr a ha).trans (hframe.1 a ha), ?_, ?_, ?_⟩
      · exact (State.setReg_regs_ne st' _ (show (0 : Reg) ≠ 54 by decide)).trans (hzero.trans hframe.2.1)
      · exact (State.setReg_regs_ne st' _ (show (14 : Reg) ≠ 54 by decide)).trans h14
      · exact (State.setReg_regs_ne st' _ (show (52 : Reg) ≠ 54 by decide)).trans h52
    exact ⟨st', t, hex, ht, ⟨hFrame', State.setReg_regs_self .., entries', hhist'⟩, hidx⟩
  obtain ⟨st, t, hex, ht, hI⟩ :=
    (Triple.forUp_sum I L stepCost (r_i := 54) (hi := .reg 52) (body := case3NoninteriorScanBody)
      hw1 hL hhi hbody) s₀ hI₀
  change t ≤ 3 + ∑ k ∈ Finset.range L, (7 + stepCost k) at ht
  change t ≤ 3 + ∑ k ∈ Finset.range L, (7 + (3 + 2500 * case3CandidateCostNat x d.core.Z
    (case3MemberScanCharge x D d.core.Z N) k)) at ht
  rw [sum_cost, case3CandidateCostNat_sum] at ht
  have hsum := case3MemberScanCharge_sum_le x D hG d hd hdiv N hkn
  change (∑ i : Case3SelectedGroup x d.core.Z, case3MemberScanCharge x D d.core.Z N i) ≤ 13 * V at hsum
  have hscaled := Nat.mul_le_mul_left 2500 hsum
  have hbase : N + D.numEdges + 1 ≤ V := by
    have hm := Nat.mul_le_mul_right (D.numEdges + N + 1) (show 1 ≤ N + 1 by omega)
    dsimp only [V]
    omega
  have hLV : L ≤ V := by dsimp only [L]; omega
  have hV : 1 ≤ V := by dsimp only [V]; exact Nat.mul_pos (by omega) (by omega)
  have htime : 2 + t ≤ 40000 * V := by omega
  rcases hI with ⟨hframe, hidx, entries', hhist⟩
  refine ⟨st, 2 + t, .seq hex₀ hex, htime, ⟨entries', hhist, ?_⟩,
    hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2, hidx⟩
  intro i
  exact hhist.2.2.2.1 i (Or.inr (case3RawIndexLabel_lt x i.1))

end GraphMinor.Compute
