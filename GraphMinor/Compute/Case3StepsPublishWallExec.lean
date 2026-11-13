module

public import GraphMinor.Compute.Case3StepsProg
public import GraphMinor.Compute.Algorithm99Case3Claim
public import GraphMinor.Compute.Case3StepsOrderedFacts
import GraphMinor.Compute.Case3StepsWallOutputSemantics
import GraphMinor.Compute.Case3StepsBlockSize
import GraphMinor.Compute.Case3StepsBlockWords
import GraphMinor.Compute.Case3StepsEncodingWords
import GraphMinor.Compute.Algorithm94Init

/-!
# Publishing an interior wall result

A wall returned by the stopping scan is already restored to original
labels. Its member multigraph lies in the deleted ambient graph, so its
encoding and wall words fit the same ambient bound. Copy the member bits,
boundary bits, wall, and multigraph encoding to the caller and set tag 1.
The restored-division theorem gives the exact frozen output-(b) semantics.
-/

public section

namespace GraphMinor.Compute

open GraphMinor.Transport

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The four private wall-result buffers can be published with their exact
output-(b) meaning and the caller frame, in linear ambient work. -/
theorem case3PublishWallProg_exec {h h' N w : ℕ} (G : MultiDigraph N)
    (X : Finset (Fin N)) (W : WallOfHeight h (G.deleteVertices X))
    (h2 : 2 ≤ h) (heven : Even h) (hW : W.IsValid)
    (h2' : 2 ≤ h') (heven' : Even h') (havoid : Disjoint W.compassFinset X)
    (S : Finset (Fin N)) (hS : S = W.compassFinset) (D : MultiDigraph S.card)
    (hD : HEq D (case3CompactCompassMultigraph (G.deleteVertices X) W))
    (om : List (Fin S.card)) (hom : om.Nodup)
    (homEq : HEq om (List.ofFn (compactCorner W h2 heven))) :
    let x := case3SimpleSocietyInput D om hom
    ∀ (d : Alg86DivisionOutput x), IsValidAlg86DivisionOutput x d →
    ∀ i : Case3SelectedGroup x d.core.Z,
    Disjoint (case3SelectedMember x d.core.Z i).verts
      (case3PullbackBits (S.orderEmbOfFin rfl) W.perimeterFinset) →
    let R := case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)
    let Q := case3PushMultigraph S R
    let Vs := (case3SelectedMember x d.core.Z i).verts.image (S.orderEmbOfFin rfl)
    ∀ (WA : WallOfHeight h' (Q.deleteVerticesCompact Vsᶜ)), WA.IsValid →
    ∀ hnext : (WA.moveOrig Q (compactEmb Vsᶜ)).IsValid,
    ((WA.moveOrig Q (compactEmb Vsᶜ)).toGMWall h2' heven' hnext).graph ≤
      Q.toGMDigraph.toGraph.induce Vs.toNatSet →
    ∀ (a_out a_bd a_wall a_A_enc a_base r_tag r_base : ℕ),
    (∀ a ∈ [a_out, a_bd, a_wall, a_A_enc], a < a_base) →
    [a_out, a_bd, a_wall, a_A_enc].Nodup → r_tag < r_base →
    wordSize (h' + elemWallNumVerts h' + (elemWallEdges h').length + 5)
      ((N + 1) * (G.numEdges + N + 1)) ≤ w →
    ∀ s : State, s.arrs (a_base + 55) = bitSetList Vs →
    s.arrs (a_base + 56) = bitSetList ((case3GroupBoundary x d.core.Z i.1).image (S.orderEmbOfFin rfl)) →
    s.arrs (a_base + 46) = (WA.moveOrig Q (compactEmb Vsᶜ)).encList →
    s.arrs (a_base + 54) = Q.enc →
    ∃ s' t, Exec w (case3PublishWallProg a_out a_bd a_wall a_A_enc a_base r_tag r_base) s s' t ∧
      t ≤ 2000 * ((N + 1) * (G.numEdges + N + 1)) ∧ s'.regs r_tag = 1 ∧
      IsCase3StepsOutputB h h' G X W h2 heven hW h2' heven' a_out a_bd a_wall a_A_enc s' ∧
      (∀ a < a_base, a ≠ a_out → a ≠ a_bd → a ≠ a_wall → a ≠ a_A_enc → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_tag → s'.regs r = s.regs r) := by
  intro x d hd i hint R Q Vs WA hWA hnext hsub a_out a_bd a_wall a_A_enc a_base r_tag r_base
    hindices hnd hrtag hw s hVs hBds hWall hQenc
  have hsem : ∀ (st : State), st.arrs a_out = bitSetList Vs →
      st.arrs a_bd = bitSetList ((case3GroupBoundary x d.core.Z i.1).image (S.orderEmbOfFin rfl)) →
      st.arrs a_wall = (WA.moveOrig Q (compactEmb Vsᶜ)).encList → st.arrs a_A_enc = Q.enc →
      IsCase3StepsOutputB h h' G X W h2 heven hW h2' heven' a_out a_bd a_wall a_A_enc st := by
    subst S
    cases hD
    cases homEq
    intro st hV hBd hwall henc
    exact case3SelectedWall_isOutputB G X W h2 heven hW d hd i h2' heven' havoid hint
      WA hWA hnext hsub hV hBd hwall henc
  let V := (N + 1) * (G.numEdges + N + 1)
  have hV : N + G.numEdges + 1 ≤ V := by
    dsimp only [V]
    nlinarith only [Nat.zero_le (N * (G.numEdges + N + 1))]
  have hw4 := (wordSize_mono_left (by omega : 4 ≤ h' + elemWallNumVerts h' + (elemWallEdges h').length + 5) V).trans hw
  have hpow : (V + 2) ^ 4 < 2 ^ w :=
    (pow_lt_two_pow_wordSize (c := 4) (by decide) V).trans_le (Nat.pow_le_pow_right (by decide) hw4)
  have hconst := case3WordSize_exponent_lt (by omega : 1 ≤ h' + elemWallNumVerts h' + (elemWallEdges h').length + 5) hw
  obtain ⟨hw6, _, hN, _, _, _, hE, henc, hcap, _⟩ :=
    case3Scan_word_bounds (k := N) (A := G.numEdges) (m := 0)
      (Nat.le_refl N) (Nat.le_refl G.numEdges) (Nat.zero_le _) hpow
  have h1 : 1 < 2 ^ w := by omega
  have hRle : R ≤ (G.deleteVertices X).induce (S.orderEmbOfFin rfl) := by
    subst S
    cases hD
    exact case3RoutedMember_le _ _ _ _
  have hQle := case3PushMultigraph_le S R (G.deleteVertices X) hRle
  have hQE := (MultiDigraph.numEdges_mono hQle).trans (G.numEdges_deleteVertices_le X)
  change Q.numEdges ≤ G.numEdges at hQE
  have hQA := Q.numActivePairs_le_numEdges.trans hQE
  have hQwords := case3Multigraph_enc_words_lt Q hN (by omega) (by omega)
  have hWlen := WallOfHeight.length_encList_le hnext
  have hWwords := case3Wall_encList_words (WA.moveOrig Q (compactEmb Vsᶜ)) hnext hN
    (by omega) (by omega) (by omega)
  let pairs := [(a_base + 55, a_out), (a_base + 56, a_bd),
    (a_base + 46, a_wall), (a_base + 54, a_A_enc)]
  have hpairs : ∀ q ∈ pairs, a_base ≤ q.1 ∧ q.2 < a_base := by
    intro q hq
    simp only [pairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals exact ⟨by omega, hindices _ (by simp)⟩
  have hlens : ∀ q ∈ pairs, (s.arrs q.1).length < 2 ^ w := by
    intro q hq
    simp only [pairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rw [hVs, length_bitSetList]; exact hN
    · rw [hBds, length_bitSetList]; exact hN
    · rw [hWall]; omega
    · rw [hQenc, Q.length_enc]; omega
  have hwords : ∀ q ∈ pairs, ∀ z ∈ s.arrs q.1, z < 2 ^ w := by
    intro q hq
    simp only [pairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rw [hVs]; exact all_lt_bitSetList Vs h1
    · rw [hBds]; exact all_lt_bitSetList _ h1
    · rw [hWall]; exact hWwords
    · rw [hQenc]; exact hQwords
  obtain ⟨s₁, t₁, hex₁, ht₁, hcopy, harr₁, hreg₁⟩ :=
    case3PublishArraysProg_exec pairs a_base r_base hpairs (by simpa only [pairs, List.map_cons, List.map_nil] using hnd)
      h1 s hlens hwords
  let s₂ := s₁.setReg r_tag 1
  have hex₂ : Exec w (.assign r_tag (.const 1)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h1, ↓reduceIte])
  refine ⟨s₂, t₁ + 2, .seq hex₁ hex₂, ?_, State.setReg_regs_self .., ?_, ?_, ?_⟩
  · simp only [pairs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      hVs, hBds, hWall, hQenc, length_bitSetList, Q.length_enc] at ht₁
    nlinarith only [ht₁, hWlen, hQA, hV]
  · apply hsem s₂
    · exact (hcopy (a_base + 55, a_out) (by simp [pairs])).trans hVs
    · exact (hcopy (a_base + 56, a_bd) (by simp [pairs])).trans hBds
    · exact (hcopy (a_base + 46, a_wall) (by simp [pairs])).trans hWall
    · exact (hcopy (a_base + 54, a_A_enc) (by simp [pairs])).trans hQenc
  · intro a ha hno hnb hnw hne
    rw [State.setReg_arrs, harr₁ a (by simp [pairs, hno, hnb, hnw, hne])]
  · intro r hr hne
    rw [State.setReg_regs_ne _ _ hne, hreg₁ r hr]

end GraphMinor.Compute
