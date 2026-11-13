module

public import GraphMinor.Compute.TwoPathsSetup
public import GraphMinor.Compute.Cited

/-!
# The two disjoint paths program, from the completion step

This file proves `twoPaths_shiloach80Statement_of_completion`: the interface `CompletionStatement`
(the completion step of Algorithm 5.2 and the extraction step of Section 5.3 of Humeau and Pous)
gives `Shiloach80Statement`. The program `shiloachProg` is
1. the setup (`setupProg`, `TwoPathsSetup.lean`): the first instance, `G` with the four edges of
   the cycle `T = s₁ s₂ t₁ t₂` (Section 1.2), in the memory of the driver;
2. the driver loop of Algorithm 5.1 (`driverLoop`, `TwoPathsDriver.lean`), which answers whether
   `T` is crossed and writes a crossing when it is;
3. the output (`outProg`): the answer into register `35`, and for the answer `True` the two
   paths of the crossing into arrays `33` and `34`. A crossing of `T` in `G` plus the frame is a
   pair of disjoint paths of `G` with the same vertex lists (`exists_paths_of_isCrossing`).

**The time.** The setup takes `O(N² + M)` steps and allocates a heap of `c_H (N + 1) W` entries,
where `W = N + E + 1` and `E = 2M + N |F₀| + 3N` is the budget of edges (`F₀` the new edges of the
frame, at most `8` entries). The driver takes `drvTime + c N W + 14` steps (`driverLoop_exec`),
which is `O((c + 1) (N + 1) W)` by `drvTime_le`. Since `W ≤ 12 (M + N + 1)`, the total is
`O((c + 1) (N + 1) (M + N + 1))`. The word size grows by a constant factor
(`wordSize_le_of_le_mul'`).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-- The output: the answer into register `35`, and for the answer `True` the crossing into
arrays `33` and `34`. -/
def outProg : Cmd :=
  .seq (.assign 35 (.reg rRes))
    (.ite (.op .eq (.reg rRes) (.const 1)) (.seq (copyProg 33 aQ) (copyProg 34 aR)) .skip)

/-- **The two disjoint paths program**: the setup, the driver loop, the output. -/
def shiloachProg (comp ext : Cmd) (cH : ℕ) : Cmd :=
  .seq (setupProg cH) (.seq (driverLoop comp ext) outProg)

/-- The constant of the heap. -/
def shiloachCH (c : ℕ) : ℕ := 300 + 200 * c

/-- The constant of the time. -/
def shiloachC (c : ℕ) : ℕ := 1000000 * (c + 1)

/-- The constant of the word size. -/
def shiloachCW (c c_w : ℕ) : ℕ := 15 * c_w + 12 * shiloachCH c + 103

/-- **The two disjoint paths program from the completion step.** The interface
`CompletionStatement` gives `Shiloach80Statement`. -/
theorem twoPaths_shiloach80Statement_of_completion : CompletionStatement → Shiloach80Statement := by
  rw [completionStatement_iff]
  rintro ⟨comp, ext, c, c_w, hc, hcw, hcomp, hext⟩
  refine ⟨shiloachProg comp ext (shiloachCH c), shiloachC c, shiloachCW c c_w,
    by unfold shiloachC; omega, by unfold shiloachCW; omega, ?_⟩
  intro N G _ lists s₁ t₁ s₂ t₂ h₁ h₂ h₃ h₄ h₅ h₆ w hw s hadj hent h30 h31 h32 h33 h34
  set cH := shiloachCH c with hcH
  set M := G.edgeFinset.card with hM
  obtain ⟨F₀, hF₀⟩ : ∃ F, F = pairsList (newFramePairs G s₁ s₂ t₁ t₂) := ⟨_, rfl⟩
  let _ : DecidableRel (G ⊔ pairGraph N F₀).Adj := Classical.decRel _
  have hF8 : F₀.length ≤ 8 := by
    rw [hF₀, length_pairsList]
    have : (newFramePairs G s₁ s₂ t₁ t₂).length ≤ 4 := by
      simp only [newFramePairs]
      exact (List.length_filter_le _ _).trans (by simp [framePairs])
    omega
  have hN4 : 4 ≤ N := by
    have := length_le_of_nodup (l := [s₁, s₂, t₁, t₂]) (by
      simp [h₂, h₁, h₃, Ne.symm h₄, h₅, h₆])
    simpa using this
  have hNF : N * F₀.length ≤ N * 8 := Nat.mul_le_mul_left _ hF8
  -- The word size.
  set K₀ := (N + 1) * (M + N + 1) with hK₀
  have hNK : N + 1 ≤ K₀ := Nat.le_mul_of_pos_right _ (by omega)
  have hMK : M + 1 ≤ K₀ := by
    have : M + N + 1 ≤ K₀ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hNNK : N * N ≤ K₀ := Nat.mul_le_mul (by omega) (by omega)
  have hP12 : (N + 1) * (2 * M + 12 * N + 1) ≤ 12 * K₀ := by
    rw [hK₀, Nat.mul_left_comm]; exact Nat.mul_le_mul_left _ (by omega)
  have hcHP : cH * ((N + 1) * (2 * M + 12 * N + 1)) ≤ cH * (12 * K₀) :=
    Nat.mul_le_mul_left _ hP12
  have hbig : cH * (N + 1) * (2 * M + 12 * N + 1) + 4 * M + 40 * (N * N) + 40 * N + 100 <
      2 ^ w := by
    apply lt_two_pow_of_le_mul (K := 12 * cH + 100) (n := K₀) _
      ((wordSize_mono_left (by unfold shiloachCW; omega) _).trans hw)
    rw [Nat.mul_assoc]; nlinarith
  have hn : 4 * N + 4 < 2 ^ w := by omega
  set E := 2 * M + N * F₀.length + 3 * N with hE
  have hwE : wordSize c_w ((N + 1) * (E + N + 1)) ≤ w := by
    have h1 : (N + 1) * (E + N + 1) ≤ 12 * (K₀ + 1) :=
      ((Nat.mul_le_mul_left _ (by omega)).trans hP12).trans (by omega)
    exact (wordSize_le_of_le_mul' h1).trans
      ((wordSize_mono_left (by unfold shiloachCW; omega) _).trans hw)
  have hcapE : 2 * E + N * (2 * N + 1) < 2 ^ w := by
    have : N * (2 * N + 1) = 2 * (N * N) + N := by ring
    omega
  -- The setup.
  obtain ⟨sX, tX, hexX, htX, hrX, haX, hX⟩ := setup_exec (c := c) (cH := cH) (by rw [hcH, shiloachCH]) F₀ hF₀
    h₁ h₂ h₃ h₄ h₅ h₆ hadj hent h30 h31 h32 h33 h34 hbig
  rw [← hM] at htX
  -- The driver.
  obtain ⟨sD, tD, hexD, hlowD, hout⟩ := driverLoop_exec hcomp hext hn hwE hcapE hX
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  have hTl : [s₁, s₂, t₁, t₂].length = 4 := rfl
  rw [hcard, hTl] at hout
  have hdt := drvTime_le (N := N) (E := E) (c := c) (Φ := 2 * N - 4 - 3) (Ψ := N - 4)
    (f := F₀.length) (by omega) (by omega) hF8
  have hP : (N + 1) * (N + E + 1) ≤ 12 * K₀ := (Nat.mul_le_mul_left _ (by omega)).trans hP12
  have hdt' : (70000 + 21000 * c) * ((N + 1) * (N + E + 1)) ≤ (70000 + 21000 * c) * (12 * K₀) :=
    Nat.mul_le_mul_left _ hP
  have hL : cH * (N + 1) * (2 * M + N * F₀.length + 4 * N + 1) ≤ cH * (12 * K₀) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left _ (by omega)).trans hP12)
  have hcN : c * N * (N + E + 1) ≤ c * (12 * K₀) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_right _ (by omega)).trans hP)
  have hfin : ∀ t, t ≤ 29 + 24 * N →
      tX + (tD + t) ≤ shiloachC c * (N + 1) * (M + N + 1) := by
    intro t ht
    have hD : tD ≤ (70000 + 21000 * c) * (12 * K₀) + c * (12 * K₀) + 14 := by
      rcases hout with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega
    have e1 : cH * (12 * K₀) = 3600 * K₀ + 2400 * (c * K₀) := by
      rw [hcH]; unfold shiloachCH; ring
    have e2 : (70000 + 21000 * c) * (12 * K₀) + c * (12 * K₀) =
        840000 * K₀ + 252012 * (c * K₀) := by ring
    have e3 : shiloachC c * (N + 1) * (M + N + 1) = 1000000 * K₀ + 1000000 * (c * K₀) := by
      rw [hK₀]; unfold shiloachC; ring
    omega
  have hw1 : 1 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := by omega
  have hv : ∀ (L : List (Fin N)), ∀ x ∈ L.map Fin.val, x < 2 ^ w := fun L x hx => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; have := v.2; omega
  have hlowXD : ∀ r : ℕ, r < 40 → sD.regs r = s.regs r := fun r hr => by
    rw [hlowD.1 r (by omega), hrX r hr]
  have haXD : ∀ x : ℕ, x < 40 → sD.arrs x = s.arrs x := fun x hx => by
    rw [hlowD.2 x hx, haX x hx]
  rcases hout with ⟨h0, hnc, -⟩ | ⟨h1, hcr, -⟩
  · -- The answer `False`.
    set s₁' := sD.setReg 35 0 with hs₁'
    have hexO : Exec w outProg sD s₁' ((1 + 1) + ((1 + 1 + 1) + 1)) :=
      .seq (.assign (reg_eval h0 (by omega)))
        (.ite_false (by
          rw [eqc_eval hw1 (v := 0) (by rw [State.setReg_regs_ne _ _ (by decide)]; exact h0)
            (by omega) 1 (by omega)]; rfl)
          (.skip _))
    refine ⟨s₁', _, .seq hexX (.seq hexD hexO), hfin _ (by omega), fun (r : ℕ) (hr : r < 30) => ?_,
      fun (x : ℕ) (hx : x < 33) => ?_, Or.inr ⟨by simp [s₁'], fun P₁ P₂ hP₁ hP₂ hd => hnc ?_⟩⟩
    · rw [hs₁', State.setReg_regs_ne _ _ (show (r : ℕ) ≠ 35 by omega)]; exact hlowXD r (by omega)
    · rw [hs₁', State.setReg_arrs]; exact haXD x (by omega)
    · rw [hF₀, sup_pairGraph_frame]
      exact (isCrossed_frame_iff h₁ h₂ h₃ h₄ h₅).mpr ⟨P₁, P₂, hP₁, hP₂, hd⟩
  · -- The answer `True`: the two paths.
    rw [hF₀, sup_pairGraph_frame] at hcr
    obtain ⟨x, y, z, t, Q, R, hQR, hQ, hR⟩ := hcr
    obtain ⟨P₁, P₂, hP₁, hP₂, hd, hs₁, hs₂⟩ := exists_paths_of_isCrossing h₁ h₂ h₃ h₄ h₅ hQR
    simp only [List.map_id] at hs₁ hs₂
    set s₁' := sD.setReg 35 1 with hs₁'
    have hlenP : ∀ {a b : Fin N} (P : G.Walk a b), P.IsPath → P.support.length ≤ N :=
      fun P hP => length_le_of_nodup hP.support_nodup
    obtain ⟨s₂', t₂', hx₂, ht₂, hk₂, hd₂⟩ := copyProg_exec (dst := 33) (src := aQ) (by decide)
      (P₁.support.map Fin.val) s₁' hw1 (by rw [List.length_map]; have := hlenP P₁ hP₁; omega)
      (hv _) (by rw [hs₁', State.setReg_arrs, hQ, ← hs₁])
    obtain ⟨s₃', t₃', hx₃, ht₃, hk₃, hd₃⟩ := copyProg_exec (dst := 34) (src := aR) (by decide)
      (P₂.support.map Fin.val) s₂' hw1 (by rw [List.length_map]; have := hlenP P₂ hP₂; omega)
      (hv _) (by rw [hk₂.2 aR (by decide), hs₁', State.setReg_arrs, hR, ← hs₂])
    have hexO : Exec w outProg sD s₃' ((1 + 1) + ((1 + 1 + 1) + (t₂' + t₃'))) :=
      .seq (.assign (reg_eval h1 (by omega)))
        (.ite_true (eqc_eval hw1 (v := 1)
          (by rw [State.setReg_regs_ne _ _ (by decide)]; exact h1) (by omega) 1 (by omega))
          (by simp)
          (.seq hx₂ hx₃))
    have hreg : ∀ r : ℕ, r ≠ 98 → s₃'.regs r = s₁'.regs r := fun r hr => by
      rw [hk₃.1 r (by simp [hr]), hk₂.1 r (by simp [hr])]
    simp only [List.length_map] at ht₂ ht₃
    refine ⟨s₃', _, .seq hexX (.seq hexD hexO), hfin _ ?_, fun (r : ℕ) (hr : r < 30) => ?_,
      fun (x : ℕ) (hx : x < 33) => ?_,
      Or.inl ⟨?_, P₁, P₂, hP₁, hP₂, hd, by rw [hk₃.2 33 (by decide)]; exact hd₂, hd₃⟩⟩
    · have := hlenP P₁ hP₁; have := hlenP P₂ hP₂; omega
    · rw [hreg r (by omega), hs₁', State.setReg_regs_ne _ _ (show (r : ℕ) ≠ 35 by omega)]
      exact hlowXD r (by omega)
    · rw [hk₃.2 x (by simp; omega), hk₂.2 x (by simp; omega), hs₁', State.setReg_arrs]
      exact haXD x (by omega)
    · rw [hreg 35 (by decide)]; simp [s₁']

end GraphMinor.Compute.TwoPaths
