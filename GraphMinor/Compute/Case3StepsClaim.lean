module

public import GraphMinor.Compute.Algorithm99Case3Claim
public import GraphMinor.Compute.Case3StepsProg
import GraphMinor.Compute.Case3StepsCoreGroupingOrdered
import GraphMinor.Compute.Case3StepsFinishOutputAExec
import GraphMinor.Compute.Case3StepsPublishWallExec
import GraphMinor.Compute.Case3StepsBlockSize
import GraphMinor.Compute.Case3StepsBlockWords
import GraphMinor.Compute.Case3StepsStateShift
import GraphMinor.Compute.Algorithm94Init

/-!
# Steps (5) through (7) of Algorithm (9.9)

Compute the rural compass division by (8.6), restore all directed copies,
and scan its interior members with (7.2). A returned wall is published
immediately. Otherwise fill the other member records and publish the
case (iii) block. The private-contribution sum of p. 106 bounds all calls
and record work. The program preserves the caller frame in both cases.
-/

public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The frozen specification of XIII (9.9), steps (5)--(7), is realized by
`case3StepsProg`, using only the supplied (8.6) and (7.2) computations. -/
theorem case3StepsClaim_proved : Case3StepsClaim := by
  intro h h' B h2 heven h2' heven' shiloachProg h86 P72 h72
  obtain ⟨Cg, cg, _, hcg, hcore⟩ := case3CoreGroupingProg_ordered_exec h h2 heven shiloachProg h86
  obtain ⟨Cm, cm, _, hcm, hscan⟩ := case3AllMembersProg_exec B h' h2' heven' P72 h72
  let cA := h + elemWallNumVerts h + (elemWallEdges h).length + 5
  let cB := h' + elemWallNumVerts h' + (elemWallEdges h').length + 5
  let c := max (max cg cm) (max cA cB)
  let C := Cg + Cm + 200200 + 214 * elemWallNumVerts h
  refine ⟨C, 40, c, ?_⟩
  intro a_G a_X a_W a_VK a_out a_bd a_wall a_A_enc a_base r_tag r_base hindices hnd _hdisjoint hrtag
  refine ⟨case3StepsProg h2 h' shiloachProg P72 a_G a_X a_W a_VK a_out a_bd a_wall a_A_enc
    a_base r_tag r_base, ?_⟩
  intro w N G X W hW _hdisjW hflat havoid _hcompass hw s hin hX hwall hVK
  classical
  let V := (N + 1) * (G.numEdges + N + 1)
  have hV : N + G.numEdges + 1 ≤ V := by
    dsimp only [V]
    nlinarith only [Nat.zero_le (N * (G.numEdges + N + 1))]
  have hVpos : 1 ≤ V := by omega
  have hcA : cA ≤ c := (Nat.le_max_left cA cB).trans (Nat.le_max_right _ _)
  have hcB : cB ≤ c := (Nat.le_max_right cA cB).trans (Nat.le_max_right _ _)
  have hccg : cg ≤ c := (Nat.le_max_left cg cm).trans (Nat.le_max_left _ _)
  have hccm : cm ≤ c := (Nat.le_max_right cg cm).trans (Nat.le_max_left _ _)
  have hc4 : 4 ≤ c := (by dsimp only [cA]; omega : 4 ≤ cA).trans hcA
  have hwA := (wordSize_mono_left hcA V).trans hw
  have hwB := (wordSize_mono_left hcB V).trans hw
  have hwcg := (wordSize_mono_left hccg V).trans hw
  have hwcm := (wordSize_mono_left hccm V).trans hw
  have hw4 := (wordSize_mono_left hc4 V).trans hw
  have hpow : (V + 2) ^ 4 < 2 ^ w :=
    (pow_lt_two_pow_wordSize (c := 4) (by decide) V).trans_le (Nat.pow_le_pow_right (by decide) hw4)
  obtain ⟨hw6, _, hN, _, _, _, _, _, hcapw, _⟩ :=
    case3Scan_word_bounds (k := N) (A := G.numEdges) (m := 0)
      (Nat.le_refl N) (Nat.le_refl G.numEdges) (Nat.zero_le _) hpow
  have hconst := case3WordSize_exponent_lt (by dsimp only [cA]; omega : 1 ≤ cA) hwA
  have hidx : 3 + elemWallNumVerts h < 2 ^ w := by dsimp only [cA] at hconst; omega
  have hWlen := WallOfHeight.length_encList_le hW
  have haG : a_G < a_base := hindices a_G (by simp)
  have haX : a_X < a_base := hindices a_X (by simp)
  have haW : a_W < a_base := hindices a_W (by simp)
  have haVK : a_VK < a_base := hindices a_VK (by simp)
  have haout : a_out < a_base := hindices a_out (by simp)
  have hawall : a_wall < a_base := hindices a_wall (by simp)
  have houts : a_out ≠ a_wall := by
    intro heq
    exact (List.nodup_cons.mp hnd).1 (by simp [heq])
  obtain ⟨S, hS, D, hD, om, hom, homEq, s₁, t₁, d, hex₁, ht₁, hd, hroutes₁, hrank₁, hregs₁, harr₁, hreg₁⟩ :=
    hcore a_G a_VK a_W a_base r_base haG haVK haW w N G X W hW hflat havoid hwcg s hin hVK hwall
  let x := case3SimpleSocietyInput D om hom
  let P := case3PullbackBits (S.orderEmbOfFin rfl) W.perimeterFinset
  let L := x.n + (case3InputEdges x).length
  have hR := case3OrderedCompass_isRuralDivision G X W h2 heven hW S hS D hD om hom homEq d hd
  have hDE := (case3OrderedCompass_numEdges_le G X W S hS D hD).trans (G.numEdges_deleteVertices_le X)
  have hkn : S.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hknW : compassCard W ≤ N := by simpa only [hS, compassCard] using hkn
  have h14₁ : s₁.regs (r_base + 14) = S.card := hregs₁ 14 (by decide)
  have h52₁ : s₁.regs (r_base + 52) = L := hregs₁ 52 (by decide)
  obtain ⟨s₂, t₂, hex₂, ht₂, hP₂, h32₂, harr₂, hreg₂⟩ :=
    case3PrepareInteriorProg_exec (G.deleteVertices X) W h2 hW a_W a_VK a_base r_base haW haVK
      (by omega) (by omega) hidx (by omega)
      ((harr₁ a_W haW).trans hwall) ((harr₁ a_VK haVK).trans hVK)
      (by rw [hrank₁, List.length_ofFn]) (by simpa only [hS, compassCard] using h14₁)
  have hrouteSafe : ∀ a ∈ case3RoutingArrayIndices, a ≠ 20 ∧ a ≠ 32 ∧ a ≠ 44 ∧ a ≠ 45 := by
    intro a ha
    simp only [case3RoutingArrayIndices, List.mem_cons, List.not_mem_nil, or_false] at ha
    omega
  have hroutes₂ : ∀ a ∈ case3RoutingArrayIndices,
      (s₂.unshift a_base r_base).arrs a = case3RoutingArray x D d.core.Z a := by
    intro a ha
    have hs := hrouteSafe a ha
    rw [State.unshift_arrs, Nat.add_comm a a_base, harr₂ _ (by romega) (by romega) (by romega) (by romega)]
    exact hroutes₁ a ha
  have hP₂' : (s₂.unshift a_base r_base).arrs 20 = bitSetList P := by
    rw [State.unshift_arrs, Nat.add_comm 20 a_base]
    have hbits : bitSetList P = bitSetList (case3PullbackBits (compassEmb W) W.perimeterFinset) := by
      subst S
      rfl
    exact hP₂.arr_eq_bitSetList.trans hbits.symm
  have h32₂' : (s₂.unshift a_base r_base).arrs 32 = case3ScanInverseLabels S := by
    rw [State.unshift_arrs, Nat.add_comm 32 a_base, h32₂]
    simp only [case3ScanInverseLabels, hS, compassCard]
  have hrank₂ : ((s₂.unshift a_base r_base).arrs 2).length = N := by
    rw [State.unshift_arrs, Nat.add_comm 2 a_base, harr₂ _ (by romega) (by romega) (by romega) (by romega),
      hrank₁, List.length_ofFn]
  have h14₂ : (s₂.unshift a_base r_base).regs 14 = S.card := by
    rw [State.unshift_regs, Nat.add_comm 14 r_base, hreg₂ _ (by romega)]
    exact h14₁
  have h52₂ : (s₂.unshift a_base r_base).regs 52 = L := by
    rw [State.unshift_regs, Nat.add_comm 52 r_base, hreg₂ _ (by romega)]
    exact h52₁
  have hVD : (N + 1) * (D.numEdges + N + 1) ≤ V :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right hDE N) 1)
  have hwscan := (wordSize_mono_right cm hVD).trans hwcm
  obtain ⟨u₃, t₃, hex₃, ht₃, hresult, harr₃, h14₃, h52₃⟩ :=
    hscan S D om hom d hd hR.isDivision P w hwscan (s₂.unshift a_base r_base)
      hroutes₂ hP₂' h32₂' hrank₂ h14₂ h52₂
  let s₃ := s₂.applyShifted a_base r_base u₃
  have hex₃' : Exec w ((case3AllMembersProg h' P72).shift a_base r_base) s₂ s₃ t₃ :=
    Exec.shift_from a_base r_base hex₃
  have hbeforeArr : ∀ a < a_base, s₃.arrs a = s.arrs a := by
    intro a ha
    rw [State.applyShifted_arrs_lt _ _ _ _ ha, harr₂ a (by romega) (by romega) (by romega) (by romega)]
    exact harr₁ a ha
  have hbeforeReg : ∀ r < r_base, s₃.regs r = s.regs r := by
    intro r hr
    rw [State.applyShifted_regs_lt _ _ _ _ hr, hreg₂ r (by romega)]
    exact hreg₁ r hr
  have ht₁' : t₁ ≤ Cg * V := by simpa only [V, Nat.mul_assoc] using ht₁
  have ht₃' : t₃ ≤ Cm * V := ht₃.trans (Nat.mul_le_mul_left Cm hVD)
  have ht₂' : t₂ ≤ (70 + 214 * elemWallNumVerts h) * V := by
    have hp := parseWallCost_le_mul h N V hVpos (by omega)
    nlinarith only [ht₂, hp, hknW, hV, hVpos]
  rcases hresult with ⟨hzero, entries, hrecords⟩ | ⟨hone, hwallResult⟩
  · rcases hrecords with ⟨hcodes, hnd', hcover, hcap, hbuf, hused, hnum⟩
    have hG₃ : s₃.arrs (a_base + 3) = D.enc := by
      rw [Nat.add_comm a_base 3, State.applyShifted_arrs_add, harr₃ 3 (by decide)]
      exact hroutes₂ 3 (by decide)
    have h32₃ : s₃.arrs (a_base + 32) = case3ScanInverseLabels S := by
      rw [Nat.add_comm a_base 32, State.applyShifted_arrs_add, harr₃ 32 (by decide)]
      exact h32₂'
    obtain ⟨s₄, t₄, hex₄, ht₄, htag, hout, harr₄, hreg₄⟩ :=
      case3FinishOutputAProg_exec G X W h2 heven hW hflat S hS D hD om hom homEq
        d hd entries hnd' hcover hcodes hcap a_W a_X a_out a_wall a_base r_tag r_base
        haW haX haout hawall houts
        hrtag hwA s₃ ((hbeforeArr a_W haW).trans hwall) ((hbeforeArr a_X haX).trans hX) hG₃ h32₃
        (by rw [Nat.add_comm r_base 14, State.applyShifted_regs_add]; exact h14₃)
        (by rw [Nat.add_comm a_base 57, State.applyShifted_arrs_add]; exact hbuf)
        (by rw [Nat.add_comm r_base 1, State.applyShifted_regs_add]; exact hused)
        (by rw [Nat.add_comm r_base 2, State.applyShifted_regs_add]; exact hnum)
    have hz : s₃.regs r_base = 0 := by
      simpa only [Nat.zero_add] using
        (State.applyShifted_regs_add a_base r_base s₂ u₃ 0).trans hzero
    have hcond : (Expr.reg r_base).eval w s₃ = some 0 := by
      simp only [Expr.eval, checkWord, hz, Nat.two_pow_pos, ↓reduceIte]
    have hex : Exec w (case3StepsProg h2 h' shiloachProg P72 a_G a_X a_W a_VK a_out a_bd a_wall a_A_enc a_base r_tag r_base)
        s s₄ (t₁ + (t₂ + (t₃ + (1 + t₄)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃' (.ite_false hcond hex₄)))
    refine ⟨s₄, _, hex, ?_, ?_, ?_, Or.inl ⟨htag, hout⟩⟩
    · change t₁ + (t₂ + (t₃ + (1 + t₄))) ≤ C * (N + 1) * (G.numEdges + N + 1)
      rw [Nat.mul_assoc]
      change t₁ + (t₂ + (t₃ + (1 + t₄))) ≤ C * V
      dsimp only [C]
      change t₄ ≤ 200000 * V at ht₄
      nlinarith only [ht₁', ht₂', ht₃', ht₄, hVpos]
    · intro a ha hno _hnBd hnW _hnE
      exact (harr₄ a ha hno hnW).trans (hbeforeArr a ha)
    · intro r hr hne
      exact (hreg₄ r hr hne).trans (hbeforeReg r hr)
  · rcases hwallResult with ⟨i, hint, hQ, hVs, hBds, WA, hWA, hnext, hsub, hwall₃⟩
    obtain ⟨s₄, t₄, hex₄, ht₄, htag, hout, harr₄, hreg₄⟩ :=
      case3PublishWallProg_exec G X W h2 heven hW h2' heven' havoid S hS D hD om hom homEq
        d hd i hint WA hWA hnext hsub a_out a_bd a_wall a_A_enc a_base r_tag r_base
        (fun a ha => hindices a (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using Or.inr (Or.inr (Or.inr (Or.inr ha)))))
        hnd hrtag hwB s₃
        (by rw [Nat.add_comm a_base 55, State.applyShifted_arrs_add]; exact hVs.arr_eq_bitSetList)
        (by rw [Nat.add_comm a_base 56, State.applyShifted_arrs_add]; exact hBds.arr_eq_bitSetList)
        (by rw [Nat.add_comm a_base 46, State.applyShifted_arrs_add]; exact hwall₃)
        (by rw [Nat.add_comm a_base 54, State.applyShifted_arrs_add]; exact hQ)
    have ho : s₃.regs r_base = 1 := by
      simpa only [Nat.zero_add] using
        (State.applyShifted_regs_add a_base r_base s₂ u₃ 0).trans hone
    have hcond : (Expr.reg r_base).eval w s₃ = some 1 := by
      simp only [Expr.eval, checkWord, ho, show 1 < 2 ^ w by omega, ↓reduceIte]
    have hex : Exec w (case3StepsProg h2 h' shiloachProg P72 a_G a_X a_W a_VK a_out a_bd a_wall a_A_enc a_base r_tag r_base)
        s s₄ (t₁ + (t₂ + (t₃ + (1 + t₄)))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃' (.ite_true hcond (by decide) hex₄)))
    refine ⟨s₄, _, hex, ?_, ?_, ?_, Or.inr ⟨htag, hout⟩⟩
    · rw [Nat.mul_assoc]
      change t₁ + (t₂ + (t₃ + (1 + t₄))) ≤ C * V
      dsimp only [C]
      change t₄ ≤ 2000 * V at ht₄
      nlinarith only [ht₁', ht₂', ht₃', ht₄, hVpos]
    · intro a ha hno hnb hnw hne
      exact (harr₄ a ha hno hnb hnw hne).trans (hbeforeArr a ha)
    · intro r hr hne
      exact (hreg₄ r hr hne).trans (hbeforeReg r hr)

end GraphMinor.Compute
