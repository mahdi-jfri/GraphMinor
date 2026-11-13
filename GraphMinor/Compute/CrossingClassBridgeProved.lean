module

public import GraphMinor.Compute.CrossingClassCore
public import GraphMinor.Compute.Algorithm101Defs
public import GraphMinor.Compute.F92GraphCopy
import GraphMinor.Compute.SpecsCrossingReduction

/-!
# The proved `BridgeCross` program

This file places the `BridgeCross` program (Section 5 of `docs/crossing/crossing_extractor.tex`)
above the caller's memory.
It copies the adjacency lists with bounded reads, copies the cycle, runs the shifted program,
and copies a successful pair back to the caller's output arrays. Bounded reads allow unused
adjacency-array entries to contain arbitrary values. The classification of Section 6 uses this
program.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing GraphMinor.Compute.TwoPaths

/-- The full program with the interface's input and output arrays. -/
def bridgeCrossProg (a : InstArrs) (aQ aR a_base r_base : ℕ) : Cmd :=
  let B := a_base + r_base + 1
  .seq (.assign r_base (.len a.alive))
    (.seq (Alg92.f92GraphCopyProg a.st a.en a.ent r_base B)
      (.seq (copyArr a.cyc (B + 43) (B + 150))
        (.seq (bridgeCrossCoreProg.shiftMem B B)
          (.ite (.reg (B + 100))
            (.seq (copyArr (B + 100) aQ (B + 150))
              (.seq (copyArr (B + 101) aR (B + 150)) (.assign r_base (.const 1))))
            (.assign r_base (.const 0))))))

private theorem copy_words_exec {w : ℕ} (src dst ri : ℕ) (L : List ℕ) (s : State)
    (hne : dst ≠ src) (hw : 1 < 2 ^ w) (hlen : L.length < 2 ^ w)
    (hwords : ∀ v ∈ L, v < 2 ^ w) (hsrc : s.arrs src = L) :
    ∃ s' t, Exec w (copyArr src dst ri) s s' t ∧ t ≤ 6 + 12 * L.length ∧
      s'.arrs dst = L ∧ (∀ a ≠ dst, s'.arrs a = s.arrs a) ∧
      (∀ r ≠ ri, s'.regs r = s.regs r) := by
  obtain ⟨s', t, hex, ht, hout, _⟩ :=
    Triple.copyArr_spec src dst ri L hne hw hlen hwords s hsrc
  refine ⟨s', t, hex, by simpa only [Nat.add_comm] using ht, hout, ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [copyArr, forUp, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [copyArr, forUp, Cmd.writtenRegs, hr])

/-- The linear-time `BridgeCross` program of Section 5, with no algorithmic hypotheses. -/
theorem bridgeCrossProgClaim_proved : BridgeCrossProgClaim := by
  intro a aQ aR a_base r_base ha
  refine ⟨bridgeCrossProg a aQ aR a_base r_base, 12000, 19, ?_⟩
  intro w N G S D s hw hinst hD
  let _ : DecidableRel G.Adj := Classical.decRel G.Adj
  let B := a_base + r_base + 1
  have hBa : a_base < B := by dsimp [B]; omega
  have hBr : r_base < B := by dsimp [B]; omega
  have hlt (v : ℕ) (hv : v ∈ a.list ++ [aQ, aR]) : v < B :=
    lt_trans (ha.2 v hv) hBa
  have hSt : a.st < B := hlt _ (by simp [InstArrs.list])
  have hEn : a.en < B := hlt _ (by simp [InstArrs.list])
  have hEnt : a.ent < B := hlt _ (by simp [InstArrs.list])
  have hCyc : a.cyc < B := hlt _ (by simp [InstArrs.list])
  have hQb : aQ < B := hlt _ (by simp)
  have hRb : aR < B := hlt _ (by simp)
  have hQR : aQ ≠ aR := by
    have h := (List.nodup_append.1 ha.1).2.1
    simpa using h
  obtain ⟨lists, hadj⟩ := hinst.2.2.1
  have hsize : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hbig (v : ℕ) (hv : v ≤ 16 * (instSize N G + 1)) : v < 2 ^ w :=
    lt_two_pow_of_le_mul hv hw
  have hw1 : 1 < 2 ^ w := hbig 1 (by omega)
  have hN : N < 2 ^ w := hbig N (by omega)
  have hMlen : (s.arrs a.ent).length = 2 * G.edgeSet.ncard := hinst.2.2.2.1
  have hMword : (s.arrs a.ent).length < 2 ^ w := by rw [hMlen]; exact hbig _ (by omega)
  have htot : totalAdjEntries lists = (s.arrs a.ent).length := by
    rw [totalAdjEntries_eq_two_mul_card_edgeFinset hadj.2, hMlen, ncard_edgeSet_eq G]
  have hDlen : D.length ≤ N := by simpa using hD.2.1.length_le_card
  have hDword : (D.map Fin.val).length < 2 ^ w := by simp only [List.length_map]; omega
  have hDwords : ∀ v ∈ D.map Fin.val, v < 2 ^ w := by
    intro v hv; obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv; exact lt_trans u.2 hN
  let s₁ := s.setReg r_base N
  have hex₁ : Exec w (.assign r_base (.len a.alive)) s s₁ 2 :=
    .assign (by simp [Expr.eval, hinst.2.1, checkWord, hN])
  obtain ⟨s₂, t₂, hex₂, ht₂, hadj₂, hn₂, hlen₂, ha₂, hr₂⟩ :=
    Alg92.f92GraphCopyProg_exec G lists a.st a.en a.ent r_base B hSt hEn hEnt hBr
      hw1 hN (s := s₁) hadj hMword (by simp [s₁])
  change t₂ ≤ 30 + 34 * N + 17 * (s.arrs a.ent).length at ht₂
  rw [hMlen] at ht₂
  have hcyc₂ : s₂.arrs a.cyc = D.map Fin.val := (ha₂ _ hCyc).trans hinst.2.2.2.2
  obtain ⟨s₃, t₃, hex₃, ht₃, hcyc₃, ha₃, hr₃⟩ :=
    copy_words_exec a.cyc (B + 43) (B + 150) (D.map Fin.val) s₂
      (Nat.ne_of_gt (Nat.lt_of_lt_of_le hCyc (Nat.le_add_right B 43))) hw1 hDword hDwords hcyc₂
  have hadj₃ : IsAdjList G (B + 40) (B + 41) (B + 42) lists s₃ :=
    hadj₂.of_arrs_eq (ha₃ _ (by omega)) (ha₃ _ (by omega)) (ha₃ _ (by omega))
  have hn₃ : s₃.regs (B + 40) = N := (hr₃ _ (by omega)).trans hn₂
  have hlen₃ : (s₃.arrs (B + 42)).length = (s.arrs a.ent).length := by
    rw [ha₃ _ (by omega), hlen₂]; rfl
  let sd := s₃.shiftDown B B
  have hadjD : IsAdjList G aStart aEnd aEnt lists sd := hadj₃
  have hcycD : sd.arrs aCyc = D.map Fin.val := hcyc₃
  have hnD : sd.regs 40 = N := hn₃
  have hlenD : (sd.arrs aEnt).length = (s.arrs a.ent).length := hlen₃
  have hwordD : 4 * (N + (sd.arrs aEnt).length + 2) < 2 ^ w := by
    rw [hlenD, hMlen]; exact hbig _ (by omega)
  obtain ⟨sc, tc, hexc, htc, _, _, hout⟩ :=
    bridgeCrossCoreProg_exec G lists D hD.2.1 sd hadjD hcycD hnD
      (by rw [hlenD]; exact Nat.le_of_eq htot) hwordD
  let s₄ := s₃.shiftUp B B sc
  have hex₄ : Exec w (bridgeCrossCoreProg.shiftMem B B) s₃ s₄ tc := hexc.shiftMem
  have hr₄ (r : ℕ) (hr : r < B) : s₄.regs r = s₃.regs r :=
    State.regs_shiftUp_lt _ _ _ _ hr
  have ha₄ (x : ℕ) (hx : x < B) : s₄.arrs x = s₃.arrs x :=
    State.arrs_shiftUp_lt _ _ _ _ hx
  have hcallerR (r : ℕ) (hr : r < r_base) : s₄.regs r = s.regs r := by
    rw [hr₄ r (lt_trans hr hBr), hr₃ r (Nat.ne_of_lt (Nat.lt_of_lt_of_le (lt_trans hr hBr) (Nat.le_add_right B 150))),
      hr₂ r (lt_trans hr hBr)]
    simp [s₁, Nat.ne_of_lt hr]
  have hcallerA (x : ℕ) (hx : x < a_base) : s₄.arrs x = s.arrs x := by
    rw [ha₄ x (lt_trans hx hBa), ha₃ x (Nat.ne_of_lt (Nat.lt_of_lt_of_le (lt_trans hx hBa) (Nat.le_add_right B 43))),
      ha₂ x (lt_trans hx hBa)]
    rfl
  have hflag : s₄.regs (B + 100) = sc.regs rFoundCross :=
    State.regs_shiftUp_add B B s₃ sc 100
  rcases hout with ⟨hyes, L₁, L₂, hpair, hQ, hR⟩ | ⟨hno, hnone⟩
  · have hc : (Expr.reg (B + 100)).eval w s₄ = some 1 := by simp [Expr.eval, hflag, hyes, checkWord, hw1]
    have hQ₄ : s₄.arrs (B + 100) = L₁.map Fin.val :=
      (State.arrs_shiftUp_add B B s₃ sc 100).trans hQ
    have hR₄ : s₄.arrs (B + 101) = L₂.map Fin.val :=
      (State.arrs_shiftUp_add B B s₃ sc 101).trans hR
    have hL₁ : L₁.length ≤ N := by simpa using hpair.1.1.2.1.length_le_card
    have hL₂ : L₂.length ≤ N := by simpa using hpair.2.1.1.2.1.length_le_card
    have hwords (L : List (Fin N)) : ∀ v ∈ L.map Fin.val, v < 2 ^ w := by
      intro v hv; obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv; exact lt_trans u.2 hN
    obtain ⟨s₅, t₅, hex₅, ht₅, hQout, ha₅, hr₅⟩ :=
      copy_words_exec (B + 100) aQ (B + 150) (L₁.map Fin.val) s₄
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le hQb (Nat.le_add_right B 100))) hw1
        (by simp only [List.length_map]; omega) (hwords L₁) hQ₄
    obtain ⟨s₆, t₆, hex₆, ht₆, hRout, ha₆, hr₆⟩ :=
      copy_words_exec (B + 101) aR (B + 150) (L₂.map Fin.val) s₅
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le hRb (Nat.le_add_right B 101))) hw1
        (by simp only [List.length_map]; omega) (hwords L₂)
        ((ha₅ _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hQb (Nat.le_add_right B 101)))).trans hR₄)
    let s₇ := s₆.setReg r_base 1
    have he : (Expr.const 1).eval w s₆ = some 1 := by simp [checkWord, hw1]
    refine ⟨s₇, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄
      (.ite_true hc (by decide) (.seq hex₅ (.seq hex₆ (.assign he))))))), ?_, ⟨?_, ?_⟩,
      Or.inl ⟨by simp [s₇], L₁, L₂, hpair, ?_, hRout⟩⟩
    · rw [hlenD, hMlen] at htc
      simp only [List.length_map] at ht₃ ht₅ ht₆
      dsimp only [Expr.cost]
      omega
    · intro r hr _
      have hne : r ≠ B + 150 := Nat.ne_of_lt (Nat.lt_of_lt_of_le (lt_trans hr hBr) (Nat.le_add_right B 150))
      rw [State.setReg_regs_ne _ _ (Nat.ne_of_lt hr), hr₆ r hne, hr₅ r hne]
      exact hcallerR r hr
    · intro x hx hnot
      have hxQ : x ≠ aQ := fun h => hnot (by simp [h])
      have hxR : x ≠ aR := fun h => hnot (by simp [h])
      change s₆.arrs x = s.arrs x
      rw [ha₆ x hxR, ha₅ x hxQ]
      exact hcallerA x hx
    · change s₆.arrs aQ = L₁.map Fin.val
      rw [ha₆ aQ hQR]; exact hQout
  · have hc : (Expr.reg (B + 100)).eval w s₄ = some 0 := by simp [Expr.eval, hflag, hno, checkWord]
    let s₅ := s₄.setReg r_base 0
    have he : (Expr.const 0).eval w s₄ = some 0 := by simp [checkWord]
    refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.ite_false hc (.assign he))))),
      ?_, ⟨?_, ?_⟩, Or.inr ⟨by simp [s₅], hnone⟩⟩
    · rw [hlenD, hMlen] at htc
      simp only [List.length_map] at ht₃
      dsimp only [Expr.cost]
      omega
    · intro r hr _
      rw [State.setReg_regs_ne _ _ (Nat.ne_of_lt hr)]
      exact hcallerR r hr
    · intro x hx _
      exact hcallerA x hx

end GraphMinor.Compute.Crossing
