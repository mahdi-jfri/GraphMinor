module

public import GraphMinor.Compute.Case3StepsInteriorMemberExec
public import GraphMinor.Compute.Case3StepsScanRecords

/-!
# A selected interior iteration

The numeric scan constructs its selected member, checks the perimeter,
and runs the complete member program. The candidate index advances in
both returned cases. The retained record is the original-label record
used by the scan history, and all routing tables survive.
-/

public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

private theorem scan_interior_time (C b k a c m N p q r : ℕ)
    (hp : p ≤ 78 * k + 83 * a + 129) (hq : q ≤ 19 * k + 9)
    (hr : r ≤ C * (b + k + a + c + m + N + 1)) :
    2 + (p + (q + (1 + r))) + 4 ≤
      (C + 500) * (b + k + a + c + m + N + 1) := by
  have hsmall : 97 * k + 83 * a + 145 ≤ 500 * (b + k + a + c + m + N + 1) := by omega
  rw [Nat.add_mul]
  omega

/-- A selected interior candidate executes the full scan body with
constants chosen from the supplied (7.2) specification before all data. -/
theorem case3MemberScanBody_interior_exec (ω h : ℕ) (h2 : 2 ≤ h) (heven : Even h)
    (P72 : Cmd)
    (h72 : ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h)
      P72 (fun s => s)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
        (om : List (Fin S.card)) (hom : om.Nodup),
      let x := case3SimpleSocietyInput D om hom
      ∀ (d : Alg86DivisionOutput x), IsValidAlg86DivisionOutput x d →
      ∀ i : Case3SelectedGroup x d.core.Z,
      let A := case3SelectedMember x d.core.Z i
      let R := case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)
      let Gm := case3CompactMember x D d.core.Z i
      let B := algorithm72Size (case3MemberAlgorithm72Input x D d.core.Z i)
      ∀ w : ℕ, wordSize c B ≤ w →
        6 < 2 ^ w → S.card + 1 < 2 ^ w → N < 2 ^ w →
        S.card * 4 < 2 ^ w → 2 + 2 * (case3InputEdges x).length < 2 ^ w →
        S.card + (case3InputEdges x).length < 2 ^ w →
        D.numEdges < 2 ^ w → 2 + 3 * D.numActivePairs < 2 ^ w →
        2 + 3 * R.numActivePairs < 2 ^ w → R.numEdges < 2 ^ w →
        2 + 3 * Gm.numActivePairs < 2 ^ w → Gm.numEdges < 2 ^ w →
        ∀ (pre : List ℕ) (remaining count : ℕ) (P : Finset (Fin S.card)),
        Disjoint A.verts P → A.verts.card + 6 * Gm.numEdges + 4 ≤ remaining →
        pre.length + remaining < 2 ^ w → count + 1 < 2 ^ w →
        ∀ s : State,
        s.arrs 3 = D.enc → s.arrs 16 = encGraph x.G → IsBitSet d.core.Z 10 s →
        s.arrs 26 = case3AttachmentKeys x d.core.Z → s.arrs 27 = case3ComponentRepList x d.core.Z →
        s.arrs 35 = case3BucketHeads (case3ActivePairOwner x D d.core.Z)
          (S.card + (case3InputEdges x).length) 0 →
        s.arrs 36 = case3BucketNext (case3ActivePairOwner x D d.core.Z) 0 →
        s.arrs 37 = case3BucketCounts (case3ActivePairOwner x D d.core.Z)
          (S.card + (case3InputEdges x).length) 0 →
        s.regs 14 = S.card → s.regs 54 = case3RawIndexLabel x i.1 →
        IsBitSet P 20 s → s.arrs 29 = bitSetList (case3GroupLabelSet x d.core.Z) →
        (s.arrs 2).length = N → S.card ≤ (s.arrs 32).length →
        (∀ u : Fin S.card, (s.arrs 32).getD u.1 0 = (S.orderEmbOfFin rfl u).1) →
        (∀ z ∈ s.arrs 32, z < 2 ^ w) →
        s.arrs 57 = pre ++ List.replicate remaining 0 →
        s.regs 1 = pre.length → s.regs 2 = count →
        ∃ s' t, Exec w (case3MemberScanBody h P72) s s' t ∧
          t ≤ C * (B + S.card + R.numActivePairs + Gm.numActivePairs + Gm.numEdges + N + 1) ∧
          s'.regs 54 = case3RawIndexLabel x i.1 + 1 ∧
          ((∃ code : List ℕ, IsValidBranchDecompCode ω Gm code ∧
            let r := case3SelectedRecord x D d.core.Z (S.orderEmbOfFin rfl).toEmbedding i code
            s'.regs 0 = 0 ∧ s'.regs 1 = pre.length + r.enc.length ∧ s'.regs 2 = count + 1 ∧
            s'.arrs 57 = pre ++ r.enc ++ List.replicate (remaining - r.enc.length) 0) ∨
          (s'.regs 0 = 1 ∧
            let Q := case3PushMultigraph S R
            let V := A.verts.image (S.orderEmbOfFin rfl)
            s'.arrs 54 = Q.enc ∧ IsBitSet V 55 s' ∧
              IsBitSet ((case3GroupBoundary x d.core.Z i.1).image (S.orderEmbOfFin rfl)) 56 s' ∧
            (∃ WA : WallOfHeight h (Q.deleteVerticesCompact Vᶜ), WA.IsValid ∧
              ∃ hnext : (WA.moveOrig Q (compactEmb Vᶜ)).IsValid,
                ((WA.moveOrig Q (compactEmb Vᶜ)).toGMWall h2 heven hnext).graph ≤
                  Q.toGMDigraph.toGraph.induce V.toNatSet ∧
                s'.arrs 46 = (WA.moveOrig Q (compactEmb Vᶜ)).encList))) ∧
          (∀ a < 128, a ∉ [25, 30, 31, 38, 39, 40, 41, 42, 46, 47, 48, 49, 50, 51, 52, 53,
            54, 55, 56, 57] → s'.arrs a = s.arrs a) ∧
          (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 →
            (r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52) → s'.regs r = s.regs r) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := case3InteriorMemberProg_exec ω h h2 heven P72 h72
  refine ⟨C + 500, c, by omega, hc, ?_⟩
  intro N S D om hom x d hd i A R Gm B w hw hw6 hcard hN hkeys hm hsize he hDA hRA hRe hCA hCe
    pre remaining count P hint hremaining hcapacity hcount s hD hin hZ htab hreps hheads hnext hcounts
    hrn hindex hP hmask hrank hlistlen hlist hwords hbuf hused hnum
  obtain ⟨s₁, t₁, hex₁, ht₁, hkey, hverts, hmember, hmembercount, henc, harr₁, hreg₁⟩ :=
    case3MemberEncodingProg_exec x D d hd i (by omega) hcard hkeys hm hsize he hDA
      hD hin hZ htab hreps hheads hnext hcounts hrn hindex
  obtain ⟨s₂, t₂, hex₂, ht₂, htest, harr₂, hreg₂⟩ :=
    case3InteriorProg_exec (w := w) (s := s₁) A.verts P (by omega) (by change S.card < 2 ^ w; omega)
      (IsBitSet.of_bitSetList _ _ _ hverts)
      (hP.of_arr_eq (harr₁ 20 (by decide) (by decide) (by decide) (by decide)))
      ((hreg₁ 14 (by decide)).trans hrn)
  have h100 : s₂.regs 100 = 1 := by simpa only [hint, ↓reduceIte] using htest
  have heval : (Expr.reg 100).eval w s₂ = some 1 := by
    simp only [Expr.eval, checkWord, h100, show 1 < 2 ^ w by omega, ↓reduceIte]
  obtain ⟨s₃, t₃, hex₃, ht₃, hresult, harr₃, hreg₃⟩ :=
    hrun S D om hom d.core.Z i w hw (case3GroupBoundary_card_le_three x d hd i.1)
      hw6 hcard hN hRA hRe hCA hCe pre remaining count hremaining hcapacity hcount s₂
      ((harr₂ 30).trans hverts) ((harr₂ 39).trans henc)
      ((hreg₂ 14 (by decide)).trans ((hreg₁ 14 (by decide)).trans hrn))
      ((harr₂ 31).trans hmember) ((hreg₂ 62 (by decide)).trans hmembercount)
      (by rw [harr₂ 2, harr₁ 2 (by decide) (by decide) (by decide) (by decide)]; exact hrank)
      (by rw [harr₂ 32, harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hlistlen)
      (by rw [harr₂ 32, harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hlist)
      (by rw [harr₂ 32, harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hwords)
      ((harr₂ 25).trans hkey)
      (by rw [harr₂ 57, harr₁ 57 (by decide) (by decide) (by decide) (by decide)]; exact hbuf)
      ((hreg₂ 1 (by decide)).trans ((hreg₁ 1 (by decide)).trans hused))
      ((hreg₂ 2 (by decide)).trans ((hreg₁ 2 (by decide)).trans hnum))
  have h54 : s₃.regs 54 = case3RawIndexLabel x i.1 :=
    (hreg₃ 54 (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)
      (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)).trans
      ((hreg₂ 54 (by decide)).trans ((hreg₁ 54 (by decide)).trans hindex))
  have hiw : case3RawIndexLabel x i.1 < 2 ^ w := (case3RawIndexLabel_lt x i.1).trans hsize
  have hi1 : case3RawIndexLabel x i.1 + 1 < 2 ^ w := lt_of_le_of_lt (case3RawIndexLabel_lt x i.1) hsize
  let s₄ := s₃.setReg 54 (case3RawIndexLabel x i.1 + 1)
  have hex₄ : Exec w (.assign 54 (.op .add (.reg 54) (.const 1))) s₃ s₄ 4 :=
    .assign (by simp only [Expr.eval, checkWord, h54, hiw, show 1 < 2 ^ w by omega,
      BinOp.eval, BinOp.raw, hi1, ↓reduceIte])
  have hmasktest := case3MemberMask_eval (w := w) (s := s) (case3GroupLabelSet x d.core.Z)
    (case3GroupLabelEquiv x i.1) (by omega) hsize hmask
    (by rw [case3GroupLabelEquiv_val]; exact hindex)
  rw [ite_eq_left ((mem_case3GroupLabelSet x d.core.Z i.1).mpr i.2)] at hmasktest
  refine ⟨s₄, (2 + (t₁ + (t₂ + (1 + t₃)))) + 4,
    .seq (.ite_true hmasktest (by decide) (.seq hex₁ (.seq hex₂ (.ite_true heval (by decide) hex₃)))) hex₄,
    scan_interior_time C B S.card R.numActivePairs Gm.numActivePairs Gm.numEdges N t₁ t₂ t₃ ht₁ ht₂ ht₃,
    State.setReg_regs_self .., hresult, ?_, ?_⟩
  · intro a ha hnot
    have hne (q : ℕ) (hq : q ∈ [25, 30, 31, 38, 39, 40, 41, 42, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]) : a ≠ q :=
      fun heq => hnot (heq ▸ hq)
    exact (harr₃ a ha (hne 38 (by decide)) (hne 40 (by decide)) (hne 41 (by decide)) (hne 42 (by decide))
      (hne 46 (by decide)) (hne 47 (by decide)) (hne 48 (by decide)) (hne 49 (by decide))
      (hne 50 (by decide)) (hne 51 (by decide)) (hne 52 (by decide)) (hne 53 (by decide))
      (hne 54 (by decide)) (hne 55 (by decide)) (hne 56 (by decide)) (hne 57 (by decide))).trans
      ((harr₂ a).trans (harr₁ a (hne 25 (by decide)) (hne 30 (by decide)) (hne 31 (by decide)) (hne 39 (by decide))))
  · intro r h0 h1 h2ne hr
    dsimp only [Reg] at hr
    have hr70 : r < 70 := by rcases hr with hr | hr | hr | hr <;> romega
    rw [State.setReg_regs_ne _ _ (by dsimp only [Reg]; omega), hreg₃ r hr70 h0 h1 h2ne,
      hreg₂ r (by romega)]
    exact hreg₁ r (hr.elim Or.inl (fun h => h.elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim (fun h => Or.inr (Or.inr (Or.inl h)))
        (fun h => Or.inr (Or.inr (Or.inr (Or.inl h)))))))

end GraphMinor.Compute
