module

public import GraphMinor.Compute.GM06Alg511Loop
public import GraphMinor.Compute.GM06LinkageRowsEncoding
public import GraphMinor.GM06.Alg511RoundBound
import GraphMinor.GM06.Alg511Progress
import Mathlib.Tactic

/-!
# The linkage invariant and call bound of the feasibility loop

VI (5.11), pages 134–135, repeatedly asks for the next linkage.
After r successful calls, the stored ordinary-dart rows describe
an actual linkage with winding equal to the initial winding plus
r divided by the path count. The input drawing tables stay fixed.
Theorem (5.12) bounds r by the number of vertices divided by the
path count. A failed call excludes the target by (5.8), and equality
returns the stored linkage itself.

This file applies the actual while-loop execution theorem to this
invariant. Its successor command is a parameter with the Boolean
and ordinary-dart output contract of Theorem 20 of our proof of (5.7)
(outlined in `Alg57Algorithm.lean`). Instantiating that parameter with the proved (5.7) program is
required before obtaining the numbered theorem (5.11).
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- The winding after the stated number of successful successor
calls, represented by adding one to the positive numerator part. -/
@[expose] noncomputable def alg511RoundTheta (p q k r : ℕ) : ℝ :=
  ((p : ℝ) - q) / k + (r : ℝ) / k

/-- Given the actual successor execution interface, the implemented
loop decides the target and retains an encoded witnessing linkage
on success. Its call bound is derived from (5.12), and its rejection
rule from (5.8). This is a conditional command-composition theorem. -/
theorem alg511_loop_exec_of_successor_exec
    {w p q a b k d B n : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    (tables : List (Arr × List ℕ)) (successor : Cmd)
    (L₀ : CylinderLinkage k G) (rows₀ : List (List ℕ))
    (hθ₀ : L₀.HasTheta (((p : ℝ) - q) / k))
    (hrows₀ : GM06LinkageRowsEncoding L₀ tagged vertex edge rows₀)
    (hd : 0 < d) (hw : 1 < 2 ^ w)
    (hpfit : p + G.V.ncard / k + 1 < 2 ^ w) (hqfit : q < 2 ^ w)
    (hafit : a < 2 ^ w) (hbfit : b < 2 ^ w)
    (hkfit : k < 2 ^ w) (hdfit : d < 2 ^ w)
    (hlfit : (p + G.V.ncard / k + 1) * d + b * k < 2 ^ w)
    (hrfit : q * d + a * k < 2 ^ w)
    (hgrid : ∃ z : ℤ, (k : ℝ) * (((a : ℝ) - b) / d) = z)
    (hle : ((p : ℝ) - q) / k ≤ ((a : ℝ) - b) / d)
    (hcall : ∀ (r : ℕ) (L : CylinderLinkage k G) (rows : List (List ℕ)) (s : State),
      r ≤ G.V.ncard / k → alg511RoundTheta p q k r < ((a : ℝ) - b) / d →
      L.HasTheta (alg511RoundTheta p q k r) →
      GM06LinkageRowsEncoding L tagged vertex edge rows → s.arrs 8 = gm06EncodeRows rows →
      (∀ field ∈ tables, s.arrs field.1 = field.2) →
      GM06Alg511LoopRegisters p q a b k d r s →
      ∃ t u, Exec w successor s t u ∧ u ≤ B ∧
        (∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j) ∧
        (∀ field ∈ tables, t.arrs field.1 = field.2) ∧
        ((t.regs 0 = 0 ∧ ¬ IsThetaFeasible k G (alg511RoundTheta p q k r + 1 / (k : ℝ))) ∨
          (t.regs 0 = 1 ∧ ∃ (L' : CylinderLinkage k G) (rows' : List (List ℕ)),
            L'.HasTheta (alg511RoundTheta p q k r + 1 / (k : ℝ)) ∧
            GM06LinkageRowsEncoding L' tagged vertex edge rows' ∧ t.arrs 8 = gm06EncodeRows rows')))
    (s : State) (h8 : s.arrs 8 = gm06EncodeRows rows₀)
    (htables : ∀ field ∈ tables, s.arrs field.1 = field.2)
    (hregs : s.regs 54 = p ∧ s.regs 55 = q ∧ s.regs 62 = a ∧ s.regs 63 = b ∧
      s.regs 52 = k ∧ s.regs 66 = d) :
    ∃ t u calls, Exec w (gm06Alg511LoopProg successor) s t u ∧
      calls ≤ 1 + G.V.ncard / k ∧
      u ≤ 21 + (1 + G.V.ncard / k) * (B + 22) ∧
      (t.regs 0 = 0 ↔ ¬ IsThetaFeasible k G (((a : ℝ) - b) / d)) ∧
      (t.regs 0 = 1 ↔ IsThetaFeasible k G (((a : ℝ) - b) / d)) ∧
      (t.regs 0 = 1 → ∃ (L' : CylinderLinkage k G) (rows' : List (List ℕ)),
        L'.HasTheta (((a : ℝ) - b) / d) ∧ GM06LinkageRowsEncoding L' tagged vertex edge rows' ∧
          t.arrs 8 = gm06EncodeRows rows' ∧ ∀ field ∈ tables, t.arrs field.1 = field.2) := by
  have hk := hG.1
  have hstart : IsThetaFeasible k G (((p : ℝ) - q) / k) := ⟨L₀, hθ₀⟩
  have hstartgrid : ∃ z : ℤ, (k : ℝ) * (((p : ℝ) - q) / k) = z := by
    refine ⟨(p : ℤ) - q, ?_⟩
    push_cast
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hk.ne')
  obtain ⟨steps, hsteps⟩ := alg511_target_eq_after_steps hk hstartgrid hgrid hle
  let I : ℕ → (Arr → List ℕ) → Prop := fun r arrays =>
    (∀ field ∈ tables, arrays field.1 = field.2) ∧
      ∃ (L : CylinderLinkage k G) (rows : List (List ℕ)),
        L.HasTheta (alg511RoundTheta p q k r) ∧ GM06LinkageRowsEncoding L tagged vertex edge rows ∧
          arrays 8 = gm06EncodeRows rows
  have hbound (r : ℕ) (arrays : Arr → List ℕ) (h : I r arrays) : r ≤ G.V.ncard / k := by
    obtain ⟨_, L, _, hθ, _⟩ := h
    have hf : IsThetaFeasible k G (((p : ℝ) - q) / k + (r : ℝ) / k) := ⟨L, hθ⟩
    exact (Nat.le_div_iff_mul_le hk).mpr (alg511_successful_rounds_mul_le hG hstart hf)
  have hcompose : ∀ r s, r < steps → I r s.arrs → GM06Alg511LoopRegisters p q a b k d r s →
      ∃ t u, Exec w successor s t u ∧ u ≤ B ∧
        (∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j) ∧
        ((t.regs 0 = 0 ∧ ¬ IsThetaFeasible k G (((a : ℝ) - b) / d)) ∨
          (t.regs 0 = 1 ∧ I (r + 1) t.arrs)) := by
    intro r s hr hI hs
    have hlimit := hbound r s.arrs hI
    obtain ⟨hfixed, L, rows, hθ, henc, harr⟩ := hI
    have hlt : alg511RoundTheta p q k r < ((a : ℝ) - b) / d := by
      have hdiv : (r : ℝ) / (k : ℝ) < (steps : ℝ) / (k : ℝ) :=
        (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hk : (0 : ℝ) < (k : ℝ))).mpr
          (Nat.cast_lt.mpr hr)
      rw [hsteps]
      simpa only [alg511RoundTheta, add_comm] using add_lt_add_left hdiv (((p : ℝ) - q) / k)
    obtain ⟨t, u, he, ht, hkeep, hfixed', hout⟩ :=
      hcall r L rows s hlimit hlt hθ henc harr hfixed hs
    refine ⟨t, u, he, ht, hkeep, ?_⟩
    rcases hout with ⟨hzero, hnot⟩ | ⟨hone, L', rows', hθ', henc', harr'⟩
    · exact Or.inl ⟨hzero, alg511_reject_of_no_successor hG ⟨L, hθ⟩ hlt hnot⟩
    · have heq : alg511RoundTheta p q k (r + 1) = alg511RoundTheta p q k r + 1 / (k : ℝ) := by
        simp only [alg511RoundTheta, Nat.cast_add, Nat.cast_one]
        ring
      exact Or.inr ⟨hone, hfixed', L', rows', heq.symm ▸ hθ', henc', harr'⟩
  have hI₀ : I 0 s.arrs :=
    ⟨htables, L₀, rows₀, by simpa [alg511RoundTheta] using hθ₀, hrows₀, h8⟩
  obtain ⟨t, u, calls, he, hcalls, ht, hout⟩ := gm06Alg511LoopProg_exec_of_successor
    successor I (¬ IsThetaFeasible k G (((a : ℝ) - b) / d)) hw hk hd hpfit hqfit hafit hbfit
    hkfit hdfit hlfit hrfit hsteps hbound hcompose s hI₀ hregs
  have hcalls' : calls ≤ 1 + G.V.ncard / k := by omega
  have htime : u ≤ 21 + (1 + G.V.ncard / k) * (B + 22) :=
    ht.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (B + 22) hcalls') 21)
  refine ⟨t, u, calls, he, hcalls', htime, ?_, ?_, ?_⟩
  · rcases hout with ⟨hzero, hnot⟩ | ⟨hone, ⟨_, L, rows, hθ, _, _⟩, _⟩
    · exact ⟨fun _ => hnot, fun _ => hzero⟩
    · have hf : IsThetaFeasible k G (((a : ℝ) - b) / d) := ⟨L, hsteps.symm ▸ hθ⟩
      exact ⟨fun hz => False.elim (by omega), fun hn => False.elim (hn hf)⟩
  · rcases hout with ⟨hzero, hnot⟩ | ⟨hone, ⟨_, L, rows, hθ, _, _⟩, _⟩
    · exact ⟨fun ho => False.elim (by omega), fun hf => False.elim (hnot hf)⟩
    · exact ⟨fun _ => ⟨L, hsteps.symm ▸ hθ⟩, fun _ => hone⟩
  · intro hone
    rcases hout with ⟨hzero, _⟩ | ⟨_, hI, _⟩
    · omega
    · obtain ⟨hfixed, L, rows, hθ, henc, harr⟩ := hI
      exact ⟨L, rows, hsteps.symm ▸ hθ, henc, harr, hfixed⟩

/-- A polynomial bound for one successor call gives a polynomial
bound for the whole loop. The extra factor pays for the at most
one-plus-vertex-count calls established above. -/
theorem alg511_loop_polynomial_bound (size vertices k B C degree : ℕ)
    (hvertices : vertices ≤ size) (hB : B ≤ C * (size + 1) ^ degree) :
    21 + (1 + vertices / k) * (B + 22) ≤ (C + 43) * (size + 1) ^ (degree + 1) := by
  have hv : 1 + vertices / k ≤ size + 1 := by
    have hh : vertices / k ≤ vertices := Nat.div_le_self _ _
    omega
  have hp : 1 ≤ (size + 1) ^ degree := Nat.one_le_pow _ _ (by omega)
  have hB' : B + 22 ≤ (C + 22) * (size + 1) ^ degree := by nlinarith only [hB, hp]
  calc
    21 + (1 + vertices / k) * (B + 22) ≤
        21 + (size + 1) * ((C + 22) * (size + 1) ^ degree) :=
      Nat.add_le_add_left (Nat.mul_le_mul hv hB') 21
    _ ≤ (C + 43) * (size + 1) ^ (degree + 1) := by
      rw [pow_succ]
      have hsize : 1 ≤ size + 1 := by omega
      nlinarith only [hp, hsize, mul_le_mul hp hsize (by omega) (by omega)]

end GraphMinor.GM06
