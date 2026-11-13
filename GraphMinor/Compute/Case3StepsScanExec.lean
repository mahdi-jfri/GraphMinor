module

public import GraphMinor.Compute.Case3StepsScanStepHistory
public import GraphMinor.Compute.Case3StepsMemberScan
import GraphMinor.Compute.Case3StepsMultigraphComponents

/-!
# Executing the complete stopping member scan

The loop invariant keeps the routing inputs and valid records for exactly
the processed interior labels. Initialization establishes it with an empty
history. The proved iteration theorem preserves it, and the decreasing
candidate count gives termination. The weighted while bound is the page
106 sum, including a possible early wall result.
-/

public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

private theorem init_time_le (A E V cap t : ℕ) (hA : A ≤ E) (hE : E ≤ V)
    (hcap : cap ≤ 24 * V) (hV : 1 ≤ V) (ht : t ≤ 22 * A + cap + 30) : t ≤ 76 * V := by
  omega

/-- The complete step (6) scan executes from the routing and perimeter
inputs, with no history assumed initially. On exhaustion its retained
codes cover every interior selected member. Otherwise it returns a wall. -/
theorem case3MemberScanProg_exec (ω h : ℕ) (h2 : 2 ≤ h) (heven : Even h)
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
      ∀ s : State,
        (∀ a ∈ case3RoutingArrayIndices, s.arrs a = case3RoutingArray x D d.core.Z a) →
        s.arrs 20 = bitSetList P → s.arrs 32 = case3ScanInverseLabels S →
        (s.arrs 2).length = N → s.regs 14 = S.card → s.regs 52 = L →
        ∃ s' t, Exec w (case3MemberScanProg h P72) s s' t ∧
          t ≤ C * ((N + 1) * (D.numEdges + N + 1)) ∧
          ((s'.regs 0 = 0 ∧ s'.regs 54 = L ∧ ∃ entries, Hist L entries s') ∨
            (s'.regs 0 = 1 ∧ WallOut s')) ∧
          (∀ a ∈ case3MemberScanKeepArrays, s'.arrs a = s.arrs a) ∧
          s'.regs 14 = S.card ∧ s'.regs 52 = L := by
  obtain ⟨C, c, hC, hc, hstep⟩ := case3MemberScanBody_history_exec ω h h2 heven P72 h72
  refine ⟨13 * C + 100, max 4 c, by omega, by omega, ?_⟩
  intro N S D om hom x d hd hdiv P L cap enc Hist WallOut w hw s hroutes hP h32 hrank hrn hlimit
  classical
  let V := (N + 1) * (D.numEdges + N + 1)
  have hkn : x.n ≤ N := by simpa only [x, case3SimpleSocietyInput, Fintype.card_fin] using Finset.card_le_univ S
  have hw4 : wordSize 4 V ≤ w := (wordSize_mono_left (Nat.le_max_left 4 c) V).trans hw
  have hword : wordSize c V ≤ w := (wordSize_mono_left (Nat.le_max_right 4 c) V).trans hw
  have hpow : (V + 2) ^ 4 < 2 ^ w :=
    (pow_lt_two_pow_wordSize (c := 4) (by decide) V).trans_le (Nat.pow_le_pow_right (by decide) hw4)
  have hsimple := (case3InputEdges_length_le x D rfl).trans D.numActivePairs_le_numEdges
  obtain ⟨hw6, hcard, _, _, _, hL, he, hencE, hcap, _⟩ :=
    case3Scan_word_bounds hkn (Nat.le_refl D.numEdges) hsimple hpow
  change L < 2 ^ w at hL
  have hw1 : 1 < 2 ^ w := by omega
  have hDA : 2 + 3 * D.numActivePairs < 2 ^ w := by have hle := D.numActivePairs_le_numEdges; omega
  have hD : s.arrs 3 = D.enc := hroutes 3 (by decide)
  obtain ⟨s₀, t₀, hex₀, ht₀, hbuf₀, hflag₀, hused₀, hnum₀, hidx₀, harr₀, hreg₀⟩ :=
    case3InitMemberScanProg_exec (w := w) D (by omega) (by change x.n < 2 ^ w; omega) hDA hcap hD hrank
  let Frame := fun st : State =>
    (∀ a ∈ case3MemberScanKeepArrays, st.arrs a = s.arrs a) ∧ st.regs 14 = S.card ∧ st.regs 52 = L
  let I := fun st : State => Frame st ∧ st.regs 54 ≤ L ∧
    ((st.regs 0 = 0 ∧ ∃ entries, Hist (st.regs 54) entries st) ∨ (st.regs 0 = 1 ∧ WallOut st))
  let measure := fun st : State => if st.regs 0 = 0 then L - st.regs 54 else 0
  let stepCost := fun r : ℕ => 7 + C * case3CandidateCostNat x d.core.Z
    (case3MemberScanCharge x D d.core.Z N) (L - r)
  have hframe₀ : Frame s₀ := by
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have hne : a ≠ 57 := by
        intro heq
        subst a
        exact (case3MemberScanKeepArrays_bounds ha).2 (by decide)
      exact harr₀ a hne
    · exact (hreg₀ 14 (by romega) (by romega) (by romega) (by romega) (by romega)).trans hrn
    · exact (hreg₀ 52 (by romega) (by romega) (by romega) (by romega) (by romega)).trans hlimit
  have hhist₀ : Hist 0 [] s₀ := by
    refine ⟨?_, List.nodup_nil, ?_, ?_, Nat.zero_le cap, ?_, hused₀, hnum₀⟩
    · intro p hp
      exact False.elim (List.not_mem_nil hp)
    · intro p hp
      exact False.elim (List.not_mem_nil hp)
    · intro i _ hi
      exact False.elim (Nat.not_lt_zero _ hi)
    · exact hbuf₀
  have hI₀ : I s₀ := by
    refine ⟨hframe₀, ?_, Or.inl ⟨hflag₀, [], ?_⟩⟩
    · rw [hidx₀]
      exact Nat.zero_le _
    · simpa only [hidx₀] using hhist₀
  have hcond : ∀ st, I st → ∃ v, case3MemberScanCond.eval w st = some v ∧
      (v ≠ 0 → 0 < measure st) := by
    intro st hI
    rcases hI with ⟨hframe, hidx, hresult⟩
    have hkw : st.regs 54 < 2 ^ w := hidx.trans_lt hL
    rcases hresult with ⟨hzero, _⟩ | ⟨hone, _⟩
    · have ht := case3MemberScanCond_eval (w := w) (k := st.regs 54) (L := L) (b := 0)
        hw1 hkw hL (by decide) rfl hframe.2.2 hzero
      simp only [and_true] at ht
      by_cases hk : st.regs 54 < L
      · rw [ite_eq_left hk] at ht
        refine ⟨1, ht, fun _ => ?_⟩
        dsimp only [measure]
        rw [ite_eq_left hzero]
        omega
      · rw [ite_eq_right hk] at ht
        exact ⟨0, ht, fun hn => False.elim (hn rfl)⟩
    · have ht := case3MemberScanCond_eval (w := w) (k := st.regs 54) (L := L) (b := 1)
        hw1 hkw hL (by decide) rfl hframe.2.2 hone
      simp only [Nat.one_ne_zero, and_false, ↓reduceIte] at ht
      exact ⟨0, ht, fun hn => False.elim (hn rfl)⟩
  have hbody : ∀ r > 0, Triple w
      (fun st => I st ∧ measure st = r ∧ ∃ v, case3MemberScanCond.eval w st = some v ∧ v ≠ 0)
      (case3MemberScanBody h P72) (fun st => I st ∧ measure st < r) (fun _ => stepCost r) := by
    intro r hr st hst
    rcases hst with ⟨⟨hframe, hk, hresult⟩, hm, _⟩
    have hzero : st.regs 0 = 0 := by
      by_cases hz : st.regs 0 = 0
      · exact hz
      · have hm0 : measure st = 0 := by simp only [measure, hz, ↓reduceIte]
        omega
    have hm' : L - st.regs 54 = r := by simpa only [measure, hzero, ↓reduceIte] using hm
    have hklt : st.regs 54 < L := by omega
    have hback : L - r = st.regs 54 := by omega
    have hkeeproute {a : ℕ} (ha : a ∈ case3RoutingArrayIndices) : a ∈ case3MemberScanKeepArrays :=
      List.mem_append_right [2, 20, 32] ha
    have hroutes' : ∀ a ∈ case3RoutingArrayIndices, st.arrs a = case3RoutingArray x D d.core.Z a :=
      fun a ha => (hframe.1 a (hkeeproute ha)).trans (hroutes a ha)
    rcases hresult with ⟨_, entries, hhist⟩ | ⟨hone, _⟩
    · obtain ⟨st', t, hex, ht, hidx, hresult', harr, h14, h52⟩ :=
        hstep S D om hom d hd hdiv P w hword (st.regs 54) hklt entries st hhist hroutes'
          ((hframe.1 20 (by decide)).trans hP) ((hframe.1 32 (by decide)).trans h32)
          (by rw [hframe.1 2 (by decide)]; exact hrank) hframe.2.1 hframe.2.2 rfl hzero
      have hframe' : Frame st' :=
        ⟨fun a ha => (harr a ha).trans (hframe.1 a ha), h14, h52⟩
      have hI' : I st' := by
        refine ⟨hframe', ?_, ?_⟩
        · rw [hidx]
          omega
        · simpa only [hidx] using hresult'
      have hmeasure : measure st' ≤ L - st'.regs 54 := by
        dsimp only [measure]
        split
        · exact le_rfl
        · exact Nat.zero_le _
      have hdist : L - st'.regs 54 < r := by rw [hidx]; omega
      refine ⟨st', t, hex, ?_, hI', hmeasure.trans_lt hdist⟩
      simpa only [stepCost, hback] using ht
    · omega
  obtain ⟨st, tw, hexw, htw, hI, hstop⟩ := (Triple.while I measure stepCost hcond hbody) s₀ hI₀
  have hmeasure₀ : measure s₀ = L := by simp only [measure, hflag₀, ↓reduceIte, hidx₀, Nat.sub_zero]
  change tw ≤ whileCost case3MemberScanCond.cost stepCost (measure s₀) at htw
  rw [hmeasure₀, show case3MemberScanCond.cost = 7 by rfl] at htw
  have hwhile : tw ≤ (13 * C + 21) * V :=
    htw.trans (case3MemberScan_whileCost_le x D rfl d hd hdiv N C hkn)
  have hbase : N + D.numEdges + 1 ≤ V := by
    have hm := Nat.mul_le_mul_right (D.numEdges + N + 1) (show 1 ≤ N + 1 by omega)
    dsimp only [V]
    omega
  have hV : 1 ≤ V := by dsimp only [V]; exact Nat.mul_pos (by omega) (by omega)
  have hcapV : cap ≤ 24 * V := Nat.mul_le_mul_left 24 hbase
  have hE : D.numEdges ≤ V := by omega
  change t₀ ≤ 22 * D.numActivePairs + cap + 30 at ht₀
  have hinit := init_time_le D.numActivePairs D.numEdges V cap t₀ D.numActivePairs_le_numEdges hE hcapV hV ht₀
  have htime : t₀ + tw ≤ (13 * C + 100) * V := by
    calc
      _ ≤ 76 * V + (13 * C + 21) * V := Nat.add_le_add hinit hwhile
      _ = (13 * C + 97) * V := by ring
      _ ≤ _ := Nat.mul_le_mul_right V (by omega)
  rcases hI with ⟨hframe, hidx, hresult⟩
  refine ⟨st, t₀ + tw, .seq hex₀ hexw, htime, ?_, hframe.1, hframe.2.1, hframe.2.2⟩
  rcases hresult with ⟨hzero, entries, hhist⟩ | ⟨hone, hwall⟩
  · have ht := case3MemberScanCond_eval (w := w) (k := st.regs 54) (L := L) (b := 0)
      hw1 (hidx.trans_lt hL) hL (by decide) rfl hframe.2.2 hzero
    have hnot : ¬ st.regs 54 < L := by
      intro hlt
      simp only [hlt, and_self, ↓reduceIte] at ht
      rw [hstop] at ht
      exact Nat.zero_ne_one (Option.some.inj ht)
    have hlast : st.regs 54 = L := by omega
    exact Or.inl ⟨hzero, hlast, entries, hlast ▸ hhist⟩
  · exact Or.inr ⟨hone, hwall⟩

end GraphMinor.Compute
