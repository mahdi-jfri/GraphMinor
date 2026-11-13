module

public import GraphMinor.Compute.Case3StepsSimpleProg
public import GraphMinor.Compute.Case3StepsCornerProg
public import GraphMinor.Compute.Case3StepsLoopOwner

/-!
# Writing the full (8.6) input in step (5)

We restrict the original input graph to the compass, renumber its vertices,
write the underlying simple graph and append its four corner numbers. The
result is exactly `encAlg81In`, ready for the shifted (8.6) call. Every array
and register below the chosen bases is preserved.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The compact simple compass with its four corners, as an input of (8.6). -/
noncomputable abbrev case3CompactSocietyInput {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) : Alg81Input :=
  case3SimpleSocietyInput (case3CompactCompassMultigraph D W)
    (List.ofFn (compactCorner W h2 he))
    (List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW))

/-- Write the full society input in `a_base + 8`. The compact multigraph and
rank array remain in `a_base + 3` and `a_base + 2`. -/
def case3SocietyInputProg {h : ℕ} (h2 : 2 ≤ h)
    (a_G a_VK a_W a_base r_base : ℕ) : Cmd :=
  .seq (case3SimpleCompassProg a_G a_VK a_base r_base)
    (.seq (case3CornerRanksProg h2 a_W (a_base + 2) (a_base + 6))
      (.seq (.assign r_base (.op .add (.const 2) (.op .mul (.const 2) (.reg (r_base + 3)))))
        (.seq (.assign (r_base + 1) (.const 5))
          (appendArrProg (a_base + 8) (a_base + 6) (a_base + 7)
            r_base (r_base + 1) (r_base + 4)))))

/-- Step (5)'s input construction runs in linear time in the original graph
encoding and keeps all low arrays and registers. The compass is disjoint from
`X`, so the graph can be restricted before separately deleting `X`. -/
theorem case3SocietyInputProg_exec {h n w : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h (G.deleteVertices X))
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) (hdisj : Disjoint W.compassFinset X)
    (a_G a_VK a_W a_base r_base : ℕ)
    (haG : a_G < a_base) (haVK : a_VK < a_base) (haW : a_W < a_base)
    (hn : n < 2 ^ w) (hm : 8 + 3 * G.numActivePairs < 2 ^ w)
    (hedges : G.numEdges < 2 ^ w) (hidx : 3 + elemWallNumVerts h < 2 ^ w)
    {s : State} (hG : s.arrs a_G = G.enc) (hVK : s.arrs a_VK = bitSetList W.compassFinset)
    (hWall : s.arrs a_W = W.encList) :
    ∃ s' t,
      Exec w (case3SocietyInputProg h2 a_G a_VK a_W a_base r_base) s s' t ∧
      t ≤ 400 * G.numActivePairs + 40 * n + 500 ∧
      s'.arrs (a_base + 8) = encAlg81In (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) ∧
      s'.arrs (a_base + 3) = (case3CompactCompassMultigraph (G.deleteVertices X) W).enc ∧
      s'.arrs (a_base + 2) = List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1) ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  let C := G.deleteVerticesCompact W.compassFinsetᶜ
  let suffix := 4 :: (List.ofFn (compactCorner W h2 he)).map Fin.val
  have hw5 : 5 < 2 ^ w := by romega
  have hw3 : 3 < 2 ^ w := by romega
  have h0 : 0 < 2 ^ w := by romega
  have h2w : 2 < 2 ^ w := by romega
  have hw : 1 < 2 ^ w := by romega
  have hN : W.compassFinsetᶜᶜ.card ≤ n := (Finset.card_le_univ _).trans (Finset.card_fin n).le
  have hM : C.numActivePairs ≤ G.numActivePairs := by
    rw [G.numActivePairs_deleteVerticesCompact]
    exact G.numActivePairs_deleteVertices_le _
  have hsimple : (edgeListOf C.toSimpleGraph).length ≤ G.numActivePairs := by
    apply le_trans (b := C.numActivePairs) ?_ hM
    rw [← MultiDigraph.toSimplePairsAux_activePairsList]
    exact length_toSimplePairsAux_le _ _ _
  have hlen : (encGraph C.toSimpleGraph).length = 2 + 2 * (edgeListOf C.toSimpleGraph).length :=
    length_encGraph _
  have hencw : ∀ z ∈ encGraph C.toSimpleGraph, z < 2 ^ w := by
    intro z hz
    unfold encGraph at hz
    rcases List.mem_append.mp hz with hz | hz
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact hN.trans_lt hn
      · omega
    · exact all_lt_flatEdges _ (hN.trans_lt hn) z hz
  have hsuflen : suffix.length = 5 := by simp only [suffix, List.length_cons, List.length_map, List.length_ofFn]
  have hsufw : ∀ z ∈ suffix, z < 2 ^ w := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · omega
    · obtain ⟨u, _, rfl⟩ := List.mem_map.mp hz
      exact u.2.trans_le (by change W.compassFinset.card ≤ n; exact (Finset.card_le_univ _).trans (Finset.card_fin n).le) |>.trans hn
  obtain ⟨s₁, t₁, hex₁, ht₁, hsimple₁, hcompact₁, hrank₁, hn₁, hm₁, harr₁, hreg₁⟩ :=
    case3SimpleCompassProg_exec G W.compassFinset a_G a_VK a_base r_base haG haVK hw3 hn
      (by romega) hedges hG hVK
  have hWall₁ : s₁.arrs a_W = W.encList := (harr₁ a_W haW).trans hWall
  obtain ⟨s₂, hex₂, hsuffix₂, harr₂, hreg₂⟩ :=
    case3CornerRanksProg_exec W h2 he a_W (a_base + 2) (a_base + 6) (by romega) (by romega)
      hn hidx hw5 hWall₁ hrank₁
  have hm₂ : s₂.regs (r_base + 3) = (edgeListOf C.toSimpleGraph).length :=
    (hreg₂ _).trans hm₁
  have hsimple₂ : s₂.arrs (a_base + 8) = encGraph C.toSimpleGraph :=
    (harr₂ _ (by romega)).trans hsimple₁
  let s₃ := s₂.setReg r_base (encGraph C.toSimpleGraph).length
  have hex₃ : Exec w (.assign r_base (.op .add (.const 2) (.op .mul (.const 2) (.reg (r_base + 3)))))
      s₂ s₃ 6 := by
    have hew : (edgeListOf C.toSimpleGraph).length < 2 ^ w := by omega
    have h2ew : 2 * (edgeListOf C.toSimpleGraph).length < 2 ^ w := by omega
    have hlenw : 2 + 2 * (edgeListOf C.toSimpleGraph).length < 2 ^ w := by omega
    dsimp only [s₃]
    rw [hlen]
    exact .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hm₂, h2w, hew, h2ew, hlenw])
  let s₄ := s₃.setReg (r_base + 1) 5
  have hex₄ : Exec w (.assign (r_base + 1) (.const 5)) s₃ s₄ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hw5, ↓reduceIte])
  obtain ⟨s₅, t₅, hex₅, ht₅, hout₅, hlen₅, harr₅, hreg₅⟩ :=
    appendArrProg_exec (s := s₄) (a_base + 8) (a_base + 6) (a_base + 7)
      r_base (r_base + 1) (r_base + 4) (by romega) (by romega) (by romega)
      (by romega) (by romega) (by romega) (encGraph C.toSimpleGraph) suffix hencw hsufw hw
      (by rw [hlen, hsuflen]; omega)
      (by simpa only [s₄, s₃, State.setReg_arrs] using hsimple₂)
      (by simpa only [s₄, s₃, State.setReg_arrs] using hsuffix₂)
      (by simp only [s₄, s₃, State.setReg_regs_ne _ _ (show r_base ≠ r_base + 1 by romega), State.setReg_regs_self])
      (by rw [hsuflen]; exact State.setReg_regs_self _ _ _)
  refine ⟨s₅, t₁ + (29 + (6 + (2 + t₅))), .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by rw [hlen, hsuflen] at ht₅; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hout₅, case3CompactCompass_simpleEnc_eq_of_deleteVertices G X W hdisj]
    simp only [encAlg81In, case3CompactSocietyInput, case3SimpleSocietyInput,
      List.length_ofFn, List.append_assoc, List.cons_append, List.nil_append, suffix]
  · rw [harr₅ (a_base + 3) (by romega) (by romega)]
    simp only [s₄, s₃, State.setReg_arrs]
    rw [harr₂ (a_base + 3) (by romega), hcompact₁]
    exact case3CompactCompass_enc_eq_of_deleteVertices G X W hdisj
  · rw [harr₅ (a_base + 2) (by romega) (by romega)]
    simp only [s₄, s₃, State.setReg_arrs]
    rw [harr₂ (a_base + 2) (by romega)]
    exact hrank₁
  · intro a ha
    rw [harr₅ a (by romega) (by romega)]
    simp only [s₄, s₃, State.setReg_arrs]
    rw [harr₂ a (by romega)]
    exact harr₁ a ha
  · intro r hr
    rw [hreg₅ r (Or.inl (by romega)) (by romega)]
    simp only [s₄, s₃, State.setReg_regs_ne _ _ (show r ≠ r_base + 1 by romega),
      State.setReg_regs_ne _ _ (show r ≠ r_base by romega)]
    rw [hreg₂ r]
    exact hreg₁ r hr

end GraphMinor.Compute
