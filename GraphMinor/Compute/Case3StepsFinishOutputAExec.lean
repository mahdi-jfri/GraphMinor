module

public import GraphMinor.Compute.Case3StepsProg
public import GraphMinor.Compute.Case3StepsSelectedBlock
public import GraphMinor.Compute.Case3StepsOrderedFacts
import GraphMinor.Compute.Case3StepsBlockSize
import GraphMinor.Compute.Case3StepsBlockWords
import GraphMinor.Compute.Case3StepsStateShift
import GraphMinor.Compute.Algorithm94Init

/-!
# Executing the final output-(a) branch

A complete retained history supplies every member record. Stage the
original wall and deletion bitset, compute the compass lists, assemble the
block, and publish its raw and tagged forms. All graph semantics follow
from the valid division and retained codes, and the copying operations
preserve the caller frame.
-/

public section

namespace GraphMinor.Compute

open GraphMinor.Transport

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The output-(a) branch executes from a complete retained record history,
with the exact frozen output specification and the caller frame. -/
theorem case3FinishOutputAProg_exec {h N w B : ℕ} (G : MultiDigraph N)
    (X : Finset (Fin N)) (W : WallOfHeight h (G.deleteVertices X))
    (h2 : 2 ≤ h) (heven : Even h) (hW : W.IsValid) (hflat : W.IsFlatWall h2)
    (S : Finset (Fin N)) (hS : S = W.compassFinset) (D : MultiDigraph S.card)
    (hD : HEq D (case3CompactCompassMultigraph (G.deleteVertices X) W))
    (om : List (Fin S.card)) (hom : om.Nodup)
    (homEq : HEq om (List.ofFn (compactCorner W h2 heven))) :
    let x := case3SimpleSocietyInput D om hom
    ∀ (d : Alg86DivisionOutput x), IsValidAlg86DivisionOutput x d →
    ∀ entries : List (Case3SelectedGroup x d.core.Z × List ℕ),
    (entries.map Prod.fst).Nodup → (∀ i, i ∈ entries.map Prod.fst) →
    (∀ q ∈ entries,
      (Disjoint (case3SelectedMember x d.core.Z q.1).verts
          (case3PullbackBits (S.orderEmbOfFin rfl) W.perimeterFinset) ∧
        IsValidBranchDecompCode B (case3CompactMember x D d.core.Z q.1) q.2) ∨
      (¬ Disjoint (case3SelectedMember x d.core.Z q.1).verts
          (case3PullbackBits (S.orderEmbOfFin rfl) W.perimeterFinset) ∧
        q.2 = case3PlaceholderCode (case3CompactMember x D d.core.Z q.1).numEdges)) →
    let enc := case3SelectedRecordsEncoding x D d.core.Z (S.orderEmbOfFin rfl).toEmbedding entries
    let cap := 24 * (N + D.numEdges + 1)
    enc.length ≤ cap →
    ∀ (a_W a_X a_out a_wall a_base r_tag r_base : ℕ),
    a_W < a_base → a_X < a_base → a_out < a_base → a_wall < a_base →
    a_out ≠ a_wall → r_tag < r_base →
    wordSize (h + elemWallNumVerts h + (elemWallEdges h).length + 5)
      ((N + 1) * (G.numEdges + N + 1)) ≤ w →
    ∀ s : State, s.arrs a_W = W.encList → s.arrs a_X = bitSetList X →
    s.arrs (a_base + 3) = D.enc →
    s.arrs (a_base + 32) = case3ScanInverseLabels S → s.regs (r_base + 14) = S.card →
    s.arrs (a_base + 57) = enc ++ List.replicate (cap - enc.length) 0 →
    s.regs (r_base + 1) = enc.length → s.regs (r_base + 2) = entries.length →
    ∃ s' t, Exec w (case3FinishOutputAProg h2 a_W a_X a_out a_wall a_base r_tag r_base) s s' t ∧
      t ≤ 200000 * ((N + 1) * (G.numEdges + N + 1)) ∧ s'.regs r_tag = 0 ∧
      IsCase3StepsOutputA h B G X W h2 heven hW 40 w a_out a_wall s' ∧
      (∀ a < a_base, a ≠ a_out → a ≠ a_wall → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_tag → s'.regs r = s.regs r) := by
  intro x d hd entries hnd hcover hcodes enc cap hcap a_W a_X a_out a_wall a_base r_tag r_base
    haW haX haout hawall houts hrtag hw s hwall hX hG h32 hrn hbuf hused hnum
  let V := (N + 1) * (G.numEdges + N + 1)
  let members := case3SelectedRecordList x D d.core.Z (S.orderEmbOfFin rfl).toEmbedding entries
  let Kv := List.ofFn (fun u : Fin S.card => ((S.orderEmbOfFin rfl).toEmbedding u).1)
  let Ke := D.multiEdgeTriples.map (origEdgeEmb (S.orderEmbOfFin rfl).toEmbedding (S.orderEmbOfFin rfl).toEmbedding.injective)
  let corners := List.ofFn (fun i : Fin 4 => (W.cornerVert h2 i).1)
  let block := encCase3Block W Kv Ke corners members
  have hc : 4 ≤ h + elemWallNumVerts h + (elemWallEdges h).length + 5 := by omega
  have hw4 := (wordSize_mono_left hc V).trans hw
  have hpow : (V + 2) ^ 4 < 2 ^ w :=
    (pow_lt_two_pow_wordSize (c := 4) (by decide) V).trans_le (Nat.pow_le_pow_right (by decide) hw4)
  have hconst := case3WordSize_exponent_lt (by omega : 1 ≤ h + elemWallNumVerts h + (elemWallEdges h).length + 5) hw
  have hV : N + G.numEdges + 1 ≤ V := by
    dsimp only [V]
    nlinarith only [Nat.zero_le (N * (G.numEdges + N + 1))]
  have hDE := case3OrderedCompass_numEdges_le G X W S hS D hD
  have hdelE := G.numEdges_deleteVertices_le X
  have hDEG := hDE.trans hdelE
  have hkn : S.card ≤ N := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  obtain ⟨hw6, _, hN, _, _, _, hE, henc, hcapw, _⟩ :=
    case3Scan_word_bounds (k := N) (A := G.numEdges) (m := 0)
      (Nat.le_refl N) (Nat.le_refl G.numEdges) (Nat.zero_le _) hpow
  have hDA := D.numActivePairs_le_numEdges
  have hh : h < 2 ^ w := by omega
  have hv : elemWallNumVerts h < 2 ^ w := by omega
  have he : (elemWallEdges h).length < 2 ^ w := by omega
  have hidx : 3 + elemWallNumVerts h < 2 ^ w := by omega
  have hWlen := WallOfHeight.length_encList_le hW
  have hWwords := case3Wall_encList_words W hW hN hh hv he
  have hrec : (members.flatMap Case3MemberRecord.enc).length ≤ 24 * (N + (G.deleteVertices X).numEdges + 1) := by
    change enc.length ≤ _
    dsimp only [cap] at hcap
    omega
  obtain ⟨hblen, hbwords, hsem⟩ := case3SelectedBlock_outputA G X W h2 heven hW hflat
    S hS D hD om hom homEq d hd entries hnd hcover hcodes hrec hN (by omega) (by omega)
      (by omega) hh hv he
  change block.length ≤ _ at hblen
  change ∀ z ∈ block, z < 2 ^ w at hbwords
  have htaglen : 1 + N + block.length < 2 ^ w :=
    case3Block_tagged_length_lt_two_pow block (hblen.trans (Nat.mul_le_mul_left 40 (by have := G.numEdges_deleteVertices_le X; omega))) hw4
  have h1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hwall₁, harr₁, hreg₁⟩ :=
    copyArrLoopProg_exec a_W (a_base + 59) (r_base + 132) (r_base + 133)
      (by romega) (by romega) h1 s (by rw [hwall]; omega) (by rw [hwall]; exact hWwords)
  obtain ⟨s₂, t₂, hex₂, ht₂, hX₂, harr₂, hreg₂⟩ :=
    copyArrLoopProg_exec a_X (a_base + 61) (r_base + 132) (r_base + 133)
      (by romega) (by romega) h1 s₁
      (by rw [harr₁ a_X (by romega), hX, length_bitSetList]; exact hN)
      (by rw [harr₁ a_X (by romega), hX]; exact all_lt_bitSetList X h1)
  have hframeArr (a : ℕ) (h59 : a ≠ a_base + 59) (h61 : a ≠ a_base + 61) : s₂.arrs a = s.arrs a :=
    (harr₂ a h61).trans (harr₁ a h59)
  have hframeReg (r : ℕ) (hr : r < r_base + 120) : s₂.regs r = s.regs r :=
    (hreg₂ r (by romega) (by romega)).trans (hreg₁ r (by romega) (by romega))
  let u := s₂.unshift a_base r_base
  obtain ⟨u₃, t₃, hex₃, ht₃, hblock₃, harr₃, hreg₃⟩ :=
    case3FinishBlockProg_exec D (G.deleteVertices X) W h2
      (S.orderEmbOfFin rfl).toEmbedding (S.orderEmbOfFin rfl).toEmbedding.injective
      (List.replicate (N - S.card) 0) (List.replicate (cap - enc.length) 0) members
      (by omega) (by omega) hN (by omega) (by omega) hidx (by change block.length < 2 ^ w; omega) hbwords
      (s := u)
      (by rw [State.unshift_arrs, Nat.add_comm 3 a_base, hframeArr _ (by omega) (by omega)]; exact hG)
      (by rw [State.unshift_arrs, Nat.add_comm 32 a_base, hframeArr _ (by omega) (by omega), h32,
        case3ScanInverseLabels_eq_ofFn])
      (by rw [State.unshift_regs, Nat.add_comm 14 r_base, hframeReg _ (by omega)]; exact hrn)
      (by rw [State.unshift_arrs, Nat.add_comm 59 a_base, harr₂ (a_base + 59) (by romega)]; exact hwall₁.trans hwall)
      (by rw [State.unshift_arrs, Nat.add_comm 57 a_base, hframeArr _ (by omega) (by omega)]; exact hbuf)
      (by rw [State.unshift_regs, Nat.add_comm 1 r_base, hframeReg _ (by omega)]; exact hused)
      (by
        rw [State.unshift_regs, Nat.add_comm 2 r_base, hframeReg (r_base + 2) (by omega), hnum]
        simp only [members, case3SelectedRecordList, List.length_map])
  have hbits₃ : u₃.arrs 61 = bitSetList X := by
    rw [harr₃ 61 (by decide), State.unshift_arrs, Nat.add_comm 61 a_base]
    exact hX₂.trans ((harr₁ a_X (by romega)).trans hX)
  obtain ⟨u₄, t₄, hex₄, ht₄, hraw₄, htag₄, _, _⟩ :=
    case3WriteOutputAProg_exec (bitSetList X) block (by omega)
      (by simpa only [length_bitSetList] using htaglen) (all_lt_bitSetList X h1) hbwords hbits₃ hblock₃
  let s₄ := s₂.applyShifted a_base r_base u₄
  let s₃ := s₂.applyShifted a_base r_base u₃
  have hex₃' : Exec w ((case3FinishBlockProg h2).shift a_base r_base) s₂ s₃ t₃ :=
    Exec.shift_from a_base r_base hex₃
  have hex₄' : Exec w (case3WriteOutputAProg.shift a_base r_base) s₃ s₄ t₄ := by
    have hlocal : Exec w case3WriteOutputAProg (s₃.unshift a_base r_base) u₄ t₄ := by
      rw [case3State_unshift_applyShifted]
      exact hex₄
    have hx := Exec.shift_from a_base r_base hlocal
    simpa only [s₃, case3State_applyShifted_overwrite] using hx
  have hsraw : s₄.arrs (a_base + 62) = block := by
    rw [Nat.add_comm a_base 62, State.applyShifted_arrs_add]
    exact hraw₄
  have hstag : s₄.arrs (a_base + 63) = 2 :: (bitSetList X ++ block) := by
    rw [Nat.add_comm a_base 63, State.applyShifted_arrs_add]
    exact htag₄
  let pairs := [(a_base + 63, a_out), (a_base + 62, a_wall)]
  have hpairs : ∀ q ∈ pairs, a_base ≤ q.1 ∧ q.2 < a_base := by
    intro q hq
    simp only [pairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp only <;> omega
  have hlens : ∀ q ∈ pairs, (s₄.arrs q.1).length < 2 ^ w := by
    intro q hq
    simp only [pairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rw [hstag, List.length_cons, List.length_append, length_bitSetList]
      omega
    · rw [hsraw]
      omega
  have hwords : ∀ q ∈ pairs, ∀ z ∈ s₄.arrs q.1, z < 2 ^ w := by
    intro q hq
    simp only [pairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · rw [hstag]
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · omega
      · rcases List.mem_append.mp hz with hz | hz
        · exact all_lt_bitSetList X h1 z hz
        · exact hbwords z hz
    · rw [hsraw]
      exact hbwords
  obtain ⟨s₅, t₅, hex₅, ht₅, hcopy₅, harr₅, hreg₅⟩ :=
    case3PublishArraysProg_exec pairs a_base r_base hpairs
      (by simp [pairs, houts]) h1 s₄ hlens hwords
  let s₆ := s₅.setReg r_tag 0
  have hex₆ : Exec w (.assign r_tag (.const 0)) s₅ s₆ 2 :=
    .assign (by simp only [Expr.eval, checkWord, Nat.two_pow_pos, ↓reduceIte])
  have hex : Exec w (case3FinishOutputAProg h2 a_W a_X a_out a_wall a_base r_tag r_base) s s₆
      (t₁ + (t₂ + (t₃ + (t₄ + (t₅ + 2))))) := by
    exact .seq hex₁ (.seq hex₂ (.seq hex₃' (.seq hex₄' (.seq hex₅ hex₆))))
  refine ⟨s₆, _, hex, ?_, State.setReg_regs_self .., ?_, ?_, ?_⟩
  · rw [hwall] at ht₁
    rw [harr₁ a_X (by romega), hX, length_bitSetList] at ht₂
    change t₃ ≤ 2000 * (S.card + D.numActivePairs + D.numEdges + block.length + 1) at ht₃
    rw [length_bitSetList] at ht₄
    simp only [pairs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      hstag, hsraw, List.length_cons, List.length_append, length_bitSetList] at ht₅
    have hdelE := G.numEdges_deleteVertices_le X
    nlinarith only [ht₁, ht₂, ht₃, ht₄, ht₅, hWlen, hblen, hDEG, hDA, hkn, hV, hdelE]
  · apply hsem a_out a_wall s₆
    · exact (hcopy₅ (a_base + 63, a_out) (by simp [pairs])).trans hstag
    · exact (hcopy₅ (a_base + 62, a_wall) (by simp [pairs])).trans hsraw
  · intro a ha hneout hnewall
    rw [State.setReg_arrs, harr₅ a (by simp [pairs, hneout, hnewall]),
      State.applyShifted_arrs_lt _ _ _ _ ha, hframeArr a (by romega) (by romega)]
  · intro r hr hne
    rw [State.setReg_regs_ne _ _ hne, hreg₅ r hr,
      State.applyShifted_regs_lt _ _ _ _ hr, hframeReg r (by romega)]

end GraphMinor.Compute
