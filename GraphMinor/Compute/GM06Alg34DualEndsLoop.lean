module

public import GraphMinor.Compute.GM06Alg34DualEndpointEmit

/-!
# Serializing all dual endpoint pairs

Scan the old edge labels in order. For each edge compute its two dual
sides from the supplied incidence matrix and append them. The loop
proof follows the remaining finite source labels and preserves the
previous output prefix and every array outside its two buffers.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- The dual endpoint words contributed by a list of original edge labels. -/
def gm06DualEndpointWords (x : GM06DrawingData) (hR : 0 < x.regions.length)
    (L : List (Fin x.ends.length)) : List ℕ :=
  L.flatMap (fun e => let p := (x.dualEdgeEnds e).getD (⟨0, hR⟩, ⟨0, hR⟩); [p.1.val, p.2.val])

/-- Each source edge contributes two endpoint words. -/
theorem gm06DualEndpointWords_length (x : GM06DrawingData) (hR : 0 < x.regions.length)
    (L : List (Fin x.ends.length)) : (gm06DualEndpointWords x hR L).length = 2 * L.length := by
  induction L with
  | nil => simp only [gm06DualEndpointWords, List.flatMap_nil, List.length_nil, Nat.mul_zero]
  | cons e L ih =>
    simp only [gm06DualEndpointWords, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at *
    omega

/-- Scan the remaining edge count 7702, starting at old label 7701. -/
def gm06DualEndsLoopProg : Cmd :=
  .while (.reg 7702) (.seq (.assign 7600 (.reg 7701))
    (.seq gm06DualEndpointEmitProg
      (.seq (.assign 7701 (.op .add (.reg 7701) (.const 1)))
        (.assign 7702 (.op .sub (.reg 7702) (.const 1))))))

/-- The edge scan appends precisely the finite dual endpoint section,
with a linear incidence-query cost per source edge. -/
theorem gm06DualEndsLoopProg_exec {w i cap : ℕ} (x : GM06DrawingData)
    (hR : 0 < x.regions.length) (L : List (Fin x.ends.length))
    (hlabels : L.map Fin.val = List.range' i L.length) (hfitLabels : i + L.length ≤ x.ends.length)
    {pre : List ℕ} {s : State} (hw : 2 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hspan : x.regions.length + 2 < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hsource : s.arrs 52 = List.range x.regions.length)
    (hindex : s.regs 7701 = i) (hleft : s.regs 7702 = L.length)
    (hbuf : IsBuf 55 7804 pre cap s) (hcap : 2 * L.length ≤ cap)
    (hfit : pre.length + 2 * L.length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualEndsLoopProg s s' t ∧
      t ≤ (100 * (x.regions.length + 1) + 37) * L.length + 1 ∧
      IsBuf 55 7804 (pre ++ gm06DualEndpointWords x hR L) (cap - 2 * L.length) s' ∧
      s'.regs 7701 = i + L.length ∧ s'.regs 7702 = 0 ∧
      (∀ A : ℕ, A ≠ 54 → A ≠ 55 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7600 ∨ 7702 < r → r ≠ 7804 → s'.regs r = s.regs r) := by
  have hmN : x.ends.length ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
  have hmw := hmN.trans_lt hN
  have hw1 : 1 < 2 ^ w := by omega
  induction L generalizing i cap pre s with
  | nil =>
    have hz : s.regs 7702 = 0 := hleft
    refine ⟨s, 1, .while_false (by simp [Expr.eval, checkWord, hz, Nat.zero_lt_of_lt hw]),
      by simp, ?_, by simpa using hindex, hz, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    simpa only [gm06DualEndpointWords, List.flatMap_nil, List.length_nil, Nat.mul_zero,
      List.append_nil, Nat.sub_zero] using hbuf
  | cons e L ih =>
    have hcons := List.cons.inj (by
      simpa only [List.map_cons, List.length_cons, List.range'_succ] using hlabels)
    have heval : e.val = i := hcons.1
    have htail : L.map Fin.val = List.range' (i + 1) L.length := hcons.2
    have hiw : i < 2 ^ w := heval ▸ e.isLt.trans hmw
    have hi1w : i + 1 < 2 ^ w := (by simp only [List.length_cons] at hfitLabels; omega : i + 1 ≤ x.ends.length).trans_lt hmw
    have hleftw : L.length + 1 < 2 ^ w := (by simp only [List.length_cons] at hfitLabels; omega : L.length + 1 ≤ x.ends.length).trans_lt hmw
    let s₀ := s.setReg 7600 i
    have he₀ : Exec w (.assign 7600 (.reg 7701)) s s₀ 2 :=
      .assign (eval_reg hindex hiw)
    obtain ⟨s₁, t₁, he₁, ht₁, hb₁, ha₁, hg₁⟩ :=
      gm06DualEndpointEmitProg_exec (s := s₀) x hR e hw hN hsquare hspan hmat hstride hn hm
        (by simpa [s₀] using heval.symm) hsource hbuf (by simp only [List.length_cons] at hcap; omega)
        (by simp only [List.length_cons] at hfit; omega)
    let p := (x.dualEdgeEnds e).getD (⟨0, hR⟩, ⟨0, hR⟩)
    have hi₁ : s₁.regs 7701 = i :=
      (hg₁ 7701 (Or.inr (by decide)) (by decide)).trans hindex
    have hl₁ : s₁.regs 7702 = L.length + 1 :=
      (hg₁ 7702 (Or.inr (by decide)) (by decide)).trans hleft
    let s₂ := s₁.setReg 7701 (i + 1)
    have he₂ : Exec w (.assign 7701 (.op .add (.reg 7701) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi₁, hiw, hi1w, hw1])
    let s₃ := s₂.setReg 7702 L.length
    have hl₂ : s₂.regs 7702 = L.length + 1 := hl₁
    have he₃ : Exec w (.assign 7702 (.op .sub (.reg 7702) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hl₂, hleftw,
        show L.length < 2 ^ w by omega, hw1])
    obtain ⟨s₄, t₄, he₄, ht₄, hb₄, hi₄, hz₄, ha₄, hg₄⟩ :=
      ih (s := s₃) (i := i + 1) (cap := cap - 2) (pre := pre ++ [p.1.val, p.2.val])
        htail (by simp only [List.length_cons] at hfitLabels; omega)
        ((ha₁ 12 (by decide) (by decide)).trans hmat)
        ((hg₁ 170 (Or.inl (by decide)) (by decide)).trans hstride)
        ((hg₁ 100 (Or.inl (by decide)) (by decide)).trans hn)
        ((hg₁ 101 (Or.inl (by decide)) (by decide)).trans hm)
        ((ha₁ 52 (by decide) (by decide)).trans hsource)
        (by simp [s₃, s₂]) (by simp [s₃]) hb₁
        (by simp only [List.length_cons] at hcap; omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil];
            simp only [List.length_cons] at hfit; omega)
    have hcond : (Expr.reg 7702).eval w s = some (L.length + 1) := by
      simp [Expr.eval, checkWord, hleft, hleftw]
    refine ⟨s₄, 1 + (2 + (t₁ + (4 + 4))) + t₄,
      .while_true hcond (by omega) (.seq he₀ (.seq he₁ (.seq he₂ he₃))) he₄,
      ?_, ?_, ?_, hz₄, ?_, ?_⟩
    · change _ ≤ (100 * (x.regions.length + 1) + 37) * (L.length + 1) + 1
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · have hcapEq : cap - 2 - 2 * L.length = cap - 2 * (e :: L).length := by simp only [List.length_cons]; omega
      simpa only [gm06DualEndpointWords, List.flatMap_cons, List.append_assoc, hcapEq] using hb₄
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hi₄
    · intro A h54 h55
      exact (ha₄ A h54 h55).trans (ha₁ A h54 h55)
    · intro r hr h7804
      have h7600 : r ≠ 7600 := by omega
      have h7701 : r ≠ 7701 := by omega
      have h7702 : r ≠ 7702 := by omega
      exact (hg₄ r hr h7804).trans (by
        simp only [s₃, s₂, s₀, State.setReg, Function.update_of_ne h7702,
          Function.update_of_ne h7701]
        exact (hg₁ r (by omega) h7804).trans (State.setReg_regs_ne _ _ h7600))

end GraphMinor.Compute
