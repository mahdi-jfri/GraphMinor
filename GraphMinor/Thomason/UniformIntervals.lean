module
public import GraphMinor.Thomason.UniformIntervalCheck
public import GraphMinor.Thomason.UniformReduction
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Accepted intervals of the interval certificate

Let `L ≤ p ≤ U` lie in an interval accepted by `intervalOK`. We use the
density `c = ⌊D⌋` with `D = (67/25) p (log₂ p) ^ (1/2)`, which is the
coefficient `2.68` of Graph Minors XIII (5.5), and `R = ⌊25c/67⌋ - 1`.
The integer bounds `2 ^ aL ≤ L ^ 1000` and `U ^ 1000 ≤ 2 ^ aU` give
`sL ≤ (log₂ p) ^ (1/2) ≤ sU`. As in Section 5 of the note
`docs/thomason/uniform_minor_bound.tex`, `R ≥ ρ D`, so the normalized order `x = n / D`
of a reduced graph lies in `[ρ, 1]`, hence in one of the cells, and
`cell_bound_of_cellOK` gives enough blocks for a `K_{p-2}` minor.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset SimpleGraph
universe u

/-- The cells of an accepted interval cover `[a, 1]`. -/
theorem cellsOK_cover (I : Interval) :
    ∀ (cs : List Cell) (an ad : ℕ), cellsOK I an ad cs = true → 0 < ad →
      ∀ x : ℝ, (an : ℝ) / ad ≤ x → x ≤ 1 → ((an : ℝ) / ad < x ∨ an ≠ ad) →
      ∃ an' ad' c, cellOK I an' ad' c = true ∧ (an' : ℝ) / ad' ≤ x ∧ x ≤ (c.bn : ℝ) / c.bd
  | [], an, ad, h, had, x, hax, hx1, hne => by
    simp only [cellsOK, beq_iff_eq] at h
    subst h
    have : (an : ℝ) / an = 1 := div_self (by positivity)
    rcases hne with hne | hne
    · linarith
    · exact absurd rfl hne
  | c :: cs, an, ad, h, had, x, hax, hx1, hne => by
    simp only [cellsOK, Bool.and_eq_true] at h
    by_cases hxb : x ≤ (c.bn : ℝ) / c.bd
    · exact ⟨an, ad, c, h.1, hax, hxb⟩
    · have hbd : 0 < c.bd := by
        have := h.1
        simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at this
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hbd⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := this
        exact hbd
      exact cellsOK_cover I cs c.bn c.bd h.2 hbd x (le_of_lt (not_le.mp hxb)) hx1
        (Or.inl (not_le.mp hxb))

/-- A cleared inequality between fractions: if `x d ≤ 0` with `d > 0`, then
`x ≤ 0`. -/
private theorem nonpos_of_mul_pos {x d : ℝ} (hd : 0 < d) (h : x * d ≤ 0) : x ≤ 0 := by
  have := div_nonpos_of_nonpos_of_nonneg h hd.le
  rwa [mul_div_cancel_right₀ _ hd.ne'] at this

/-- `2 ^ a ≤ m ^ 1000` gives `a / 1000 ≤ log₂ m`. -/
theorem div_le_logb_of_pow_le {m a : ℕ} (h : 2 ^ a ≤ m ^ 1000) :
    (a : ℝ) / 1000 ≤ Real.logb 2 m := by
  have hR : (2 : ℝ) ^ a ≤ (m : ℝ) ^ 1000 := by exact_mod_cast h
  have h2 := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) (by positivity) hR
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  push_cast at h2
  linarith

/-- `m ^ 1000 ≤ 2 ^ a` gives `log₂ m ≤ a / 1000`. -/
theorem logb_le_div_of_le_pow {m a : ℕ} (hm : 1 ≤ m) (h : m ^ 1000 ≤ 2 ^ a) :
    Real.logb 2 m ≤ (a : ℝ) / 1000 := by
  have hR : (m : ℝ) ^ 1000 ≤ (2 : ℝ) ^ a := by exact_mod_cast h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num) (by positivity) hR
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  push_cast at h2
  linarith

/-- The bounds `sL ≤ (log₂ p) ^ (1/2) ≤ sU` of an accepted interval. -/
theorem sqrt_bounds_of_intervalOK {I : Interval} (hI : intervalOK I = true) {p : ℕ}
    (hpL : I.L ≤ p) (hpU : p ≤ I.U) :
    (I.sLn : ℝ) / I.sLd ≤ Real.sqrt (Real.logb 2 p) ∧
      Real.sqrt (Real.logb 2 p) ≤ (I.sUn : ℝ) / I.sUd := by
  simp only [intervalOK, Bool.and_eq_true, decide_eq_true_eq] at hI
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, -⟩, hpowL⟩, hpowU⟩, -⟩, hsLd⟩, hsUd⟩, hsL2⟩, hsU2⟩, -⟩, -⟩, -⟩, -⟩ :=
    hI
  have hpLR : (I.L : ℝ) ≤ p := by exact_mod_cast hpL
  have hpUR : (p : ℝ) ≤ I.U := by exact_mod_cast hpU
  have hL1 : (1 : ℝ) ≤ I.L := by exact_mod_cast (show 1 ≤ I.L by omega)
  have hsLd' : (0 : ℝ) < I.sLd := by exact_mod_cast hsLd
  have hsUd' : (0 : ℝ) < I.sUd := by exact_mod_cast hsUd
  constructor
  · have h1 := div_le_logb_of_pow_le hpowL
    have h2 : Real.logb 2 I.L ≤ Real.logb 2 p :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hpLR
    have h3 : ((I.sLn : ℝ) / I.sLd) ^ 2 - (I.aL : ℝ) / 1000 ≤ 0 := by
      have h : ((I.sLn ^ 2 * 1000 : ℕ) : ℝ) ≤ ((I.aL * I.sLd ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hsL2
      push_cast at h
      refine nonpos_of_mul_pos (d := 1000 * (I.sLd : ℝ) ^ 2) (by positivity) ?_
      have e : (((I.sLn : ℝ) / I.sLd) ^ 2 - (I.aL : ℝ) / 1000) * (1000 * (I.sLd : ℝ) ^ 2) =
          (I.sLn : ℝ) ^ 2 * 1000 - I.aL * (I.sLd : ℝ) ^ 2 := by
        field_simp
      rw [e]; linarith
    exact Real.le_sqrt_of_sq_le (by linarith)
  · have h1 := logb_le_div_of_le_pow (show 1 ≤ I.U by omega) hpowU
    have h2 : Real.logb 2 p ≤ Real.logb 2 I.U :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hpUR
    have h3 : (I.aU : ℝ) / 1000 - ((I.sUn : ℝ) / I.sUd) ^ 2 ≤ 0 := by
      have h : ((I.aU * I.sUd ^ 2 : ℕ) : ℝ) ≤ ((I.sUn ^ 2 * 1000 : ℕ) : ℝ) := by
        exact_mod_cast hsU2
      push_cast at h
      refine nonpos_of_mul_pos (d := 1000 * (I.sUd : ℝ) ^ 2) (by positivity) ?_
      have e : ((I.aU : ℝ) / 1000 - ((I.sUn : ℝ) / I.sUd) ^ 2) * (1000 * (I.sUd : ℝ) ^ 2) =
          I.aU * (I.sUd : ℝ) ^ 2 - (I.sUn : ℝ) ^ 2 * 1000 := by
        field_simp
      rw [e]; linarith
    have h4 : Real.sqrt (Real.logb 2 p) ≤ Real.sqrt (((I.sUn : ℝ) / I.sUd) ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_sq (by positivity)] at h4

/-- The test on `ρ` of an accepted interval: for every `D ≥ (67/25) L sL`,
`67 ρ D + 159 ≤ 25 D`. -/
theorem rho_bound_of_intervalOK {I : Interval} (hI : intervalOK I = true) {D : ℝ}
    (hD : 67 / 25 * I.L * ((I.sLn : ℝ) / I.sLd) ≤ D) :
    67 * ((I.rn : ℝ) / I.rd) * D + 159 ≤ 25 * D := by
  simp only [intervalOK, Bool.and_eq_true, decide_eq_true_eq] at hI
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, -⟩, -⟩, -⟩, hsLn⟩, hsLd⟩, -⟩, -⟩, -⟩, -⟩, hrd⟩, hrho⟩, -⟩ := hI
  have hsLd' : (0 : ℝ) < I.sLd := by exact_mod_cast hsLd
  have hsLn' : (0 : ℝ) < I.sLn := by exact_mod_cast hsLn
  have hrd' : (0 : ℝ) < I.rd := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hrd)
  have hLR : (0 : ℝ) < I.L := by exact_mod_cast (show 0 < I.L by omega)
  generalize hρ : (I.rn : ℝ) / I.rd = ρ
  generalize hsL : (I.sLn : ℝ) / I.sLd = sL at hD
  have hsL0 : 0 < sL := by rw [← hsL]; positivity
  -- the test, divided by `rd sLd`
  have h : 67 * ρ * (4489 * I.L * sL) + 67 * 3975 - 25 * (4489 * I.L * sL) ≤ 0 := by
    have h0 : ((67 * (I.rn * 4489 * I.L * I.sLn + 3975 * I.sLd * I.rd) : ℕ) : ℝ) ≤
        ((25 * I.rd * 4489 * I.L * I.sLn : ℕ) : ℝ) := by exact_mod_cast hrho
    push_cast at h0
    refine nonpos_of_mul_pos (d := (I.rd : ℝ) * I.sLd) (by positivity) ?_
    rw [← hρ, ← hsL]
    have e : (67 * ((I.rn : ℝ) / I.rd) * (4489 * I.L * ((I.sLn : ℝ) / I.sLd)) + 67 * 3975 -
        25 * (4489 * I.L * ((I.sLn : ℝ) / I.sLd))) * (I.rd * I.sLd) =
        67 * (I.rn * 4489 * I.L * I.sLn + 3975 * I.sLd * I.rd) -
          25 * I.rd * 4489 * I.L * I.sLn := by
      field_simp
    rw [e]; linarith
  generalize hT : 4489 * (I.L : ℝ) * sL = T at h
  have hT0 : 0 < T := by rw [← hT]; positivity
  have hTD : 67 * T ≤ 25 * 4489 * D := by rw [← hT]; linarith
  have h1 : 0 ≤ 25 - 67 * ρ := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hTD h1]

/-- `R = ⌊25c/67⌋ - 1` is at least `(25c - 133)/67`. -/
theorem cast_R_ge (c : ℕ) (hc : 3 ≤ c) :
    (25 * (c : ℝ) - 133) / 67 ≤ ((25 * c / 67 - 1 : ℕ) : ℝ) := by
  have h := Nat.div_add_mod (25 * c) 67
  have hm := Nat.mod_lt (25 * c) (by norm_num : 0 < 67)
  have h1 : 1 ≤ 25 * c / 67 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have h' : ((67 * (25 * c / 67) + 25 * c % 67 : ℕ) : ℝ) = ((25 * c : ℕ) : ℝ) := by rw [h]
  push_cast at h'
  have hm' : ((25 * c % 67 : ℕ) : ℝ) ≤ 66 := by exact_mod_cast Nat.le_of_lt_succ hm
  rw [Nat.cast_sub h1]
  push_cast
  linarith

/-- The non-neighbour proportion in a cell: if `2q ≤ n - R`, `ρ D ≤ R`,
`n ≤ b D` and `b ≤ 2 π b + ρ`, then `q ≤ π n`. -/
theorem q_le_of_cell {n R q ρ b π D : ℝ} (h2q : 2 * q ≤ n - R) (hR : ρ * D ≤ R)
    (hn : n ≤ b * D) (hb : b ≤ 2 * π * b + ρ) (hb0 : 0 < b) (hρ : 0 ≤ ρ) (hn0 : 0 ≤ n) :
    q ≤ π * n := by
  have h1 : ρ * n ≤ ρ * (b * D) := mul_le_mul_of_nonneg_left hn hρ
  have h2 : (b - ρ) * n ≤ 2 * π * b * n := mul_le_mul_of_nonneg_right (by linarith) hn0
  nlinarith

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- One accepted cell gives a `K_{p-2}` minor, by the random block lemma
with blocks of size `k` and `A = (k + 1)/(k P)`. -/
theorem clique_of_cellOK {I : Interval} {an ad : ℕ} {c : Cell} (hc : cellOK I an ad c = true)
    {p : ℕ} (hpL : I.L ≤ p) (hpU : p ≤ I.U) (hp2 : 2 ≤ p) (hL1 : 1 ≤ I.L) (hU3 : 3 ≤ I.U) (hsL : 0 < I.sLn)
    (hsLd : 0 < I.sLd) (hsUd : 0 < I.sUd) (H : SimpleGraph W) [DecidableRel H.Adj] (q : ℕ)
    (hq : ∀ v, (nonNbr H v).card ≤ q)
    (hnlo : (an : ℝ) / ad * (67 / 25) * p * ((I.sLn : ℝ) / I.sLd) ≤ Fintype.card W)
    (hnhi : (Fintype.card W : ℝ) ≤ 67 / 25 * I.U * ((I.sUn : ℝ) / I.sUd) * ((c.bn : ℝ) / c.bd))
    (hqπ : (q : ℝ) ≤ (c.qn : ℝ) / c.qd * Fintype.card W) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (p - 2)))) (Graph.ofSimpleGraph H) := by
  have hmain := cell_bound_of_cellOK hc p (Fintype.card W) q hL1 hpL hpU hnlo hnhi hqπ
    hsL hsLd hsUd hU3
  have hc' := hc
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, -⟩, -⟩, -⟩, -⟩, -⟩, hpn⟩, hpd⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc'
  have hA : (0 : ℝ) < ((c.k : ℝ) + 1) / (c.k * ((c.pn : ℝ) / c.pd)) := by
    have : (0 : ℝ) < (c.pn : ℝ) / c.pd := by positivity
    positivity
  refine clique_isIsoMinor_of_two_sizes H q hq c.k 1 (Fintype.card W / c.k) 0 hk le_rfl
    (by simpa using Nat.div_mul_le_self (Fintype.card W) c.k) _ 1 hA one_pos (p - 2) ?_
  rw [Nat.cast_sub hp2]
  simp only [Nat.cast_zero, zero_mul, mul_zero, sub_zero, add_zero, Nat.cast_ofNat]
  linarith

/-- The reduced graphs for `p` in an accepted interval have a `K_{p-2}`
minor. -/
theorem reduced_clique_of_intervalOK {I : Interval} (hI : intervalOK I = true) {p : ℕ}
    (hpL : I.L ≤ p) (hpU : p ≤ I.U) [Nonempty W] (J : SimpleGraph W) [DecidableRel J.Adj]
    (hW : Fintype.card W ≤ ⌊(67 / 25 : ℝ) * p * Real.sqrt (Real.logb 2 p)⌋₊)
    (hdeg : ∀ v, 2 * (nonNbr J v).card +
      (25 * ⌊(67 / 25 : ℝ) * p * Real.sqrt (Real.logb 2 p)⌋₊ / 67 - 1) ≤ Fintype.card W) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (p - 2)))) (Graph.ofSimpleGraph J) := by
  have hI' := hI
  simp only [intervalOK, Bool.and_eq_true, decide_eq_true_eq] at hI'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hL, -⟩, -⟩, -⟩, hsLn⟩, hsLd⟩, hsUd⟩, -⟩, -⟩, hrn⟩, hrd⟩, -⟩, hcells⟩ := hI'
  obtain ⟨hsL, hsU⟩ := sqrt_bounds_of_intervalOK hI hpL hpU
  have hpLR : (I.L : ℝ) ≤ p := by exact_mod_cast hpL
  have hpUR : (p : ℝ) ≤ I.U := by exact_mod_cast hpU
  have hsLd' : (0 : ℝ) < I.sLd := by exact_mod_cast hsLd
  have hsUd' : (0 : ℝ) < I.sUd := by exact_mod_cast hsUd
  have hsLn' : (0 : ℝ) < I.sLn := by exact_mod_cast hsLn
  have hrd' : (0 : ℝ) < I.rd := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hrd)
  have hrn' : (0 : ℝ) < I.rn := by exact_mod_cast hrn
  have hρ1 : (I.rn : ℝ) / I.rd < 1 := by rw [div_lt_one hrd']; exact_mod_cast hrd
  generalize hs : Real.sqrt (Real.logb 2 p) = s at hW hdeg hsL hsU
  generalize hsLdef : (I.sLn : ℝ) / I.sLd = sL at hsL
  generalize hsUdef : (I.sUn : ℝ) / I.sUd = sU at hsU
  generalize hρdef : (I.rn : ℝ) / I.rd = ρ at hρ1
  have hsL0 : 0 < sL := by rw [← hsLdef]; positivity
  have hρ0 : 0 < ρ := by rw [← hρdef]; positivity
  -- the scale `D`
  have hDL : 67 / 25 * I.L * sL ≤ 67 / 25 * p * s := by
    have : (I.L : ℝ) * sL ≤ p * s := mul_le_mul hpLR hsL hsL0.le (by linarith)
    linarith
  have hρD := rho_bound_of_intervalOK hI (hsLdef ▸ hDL)
  rw [hρdef] at hρD
  generalize hD : 67 / 25 * (p : ℝ) * s = D at hW hdeg hDL hρD
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDL
  have hD6 : 6 < D := by nlinarith
  have hcD : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le hD0.le
  have hDc : D < ⌊D⌋₊ + 1 := Nat.lt_floor_add_one D
  generalize hc : ⌊D⌋₊ = c at hW hdeg hcD hDc
  have hc3 : 3 ≤ c := by
    have : (3 : ℝ) < c := by linarith
    exact_mod_cast this.le
  have hR := cast_R_ge c hc3
  generalize hRdef : 25 * c / 67 - 1 = R at hdeg hR
  have hRD : ρ * D ≤ R := by nlinarith
  -- the order `n` of `J` and the non-neighbour bound `q`
  generalize hn : Fintype.card W = n at hW hdeg
  obtain ⟨v₀⟩ := ‹Nonempty W›
  have hRn : R ≤ n := by have := hdeg v₀; omega
  have hq (v : W) : (nonNbr J v).card ≤ (n - R) / 2 := by have := hdeg v; omega
  have h2q : 2 * (((n - R) / 2 : ℕ) : ℝ) ≤ n - R := by
    have h : 2 * ((n - R) / 2) ≤ n - R := by omega
    have h' : ((2 * ((n - R) / 2) : ℕ) : ℝ) ≤ ((n - R : ℕ) : ℝ) := by exact_mod_cast h
    push_cast [Nat.cast_sub hRn] at h'
    exact h'
  have hnc : (n : ℝ) ≤ c := by exact_mod_cast hW
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the cell containing `x = n / D`
  have hxρ : ρ ≤ n / D := by rw [le_div_iff₀ hD0]; linarith
  have hx1 : (n : ℝ) / D ≤ 1 := by rw [div_le_one hD0]; linarith
  obtain ⟨an, ad, cell, hcell, hax, hxb⟩ := cellsOK_cover I I.cells I.rn I.rd hcells
    (lt_of_le_of_lt (Nat.zero_le _) hrd) (n / D) (hρdef ▸ hxρ) hx1
    (by
      rcases eq_or_lt_of_le hxρ with h | h
      · right; exact Nat.ne_of_lt hrd
      · left; rw [hρdef]; exact h)
  have hcell' := hcell
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at hcell'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, han⟩, had⟩, hbd⟩, -⟩, -⟩, -⟩, -⟩, hqd⟩, hπb⟩, -⟩, -⟩, -⟩, -⟩ := hcell'
  have hbd' : (0 : ℝ) < cell.bd := by exact_mod_cast hbd
  have hqd' : (0 : ℝ) < cell.qd := by exact_mod_cast hqd
  have ha0 : (0 : ℝ) < (an : ℝ) / ad := by
    have : (0 : ℝ) < an := by exact_mod_cast han
    have : (0 : ℝ) < ad := by exact_mod_cast had
    positivity
  have hb0 : (0 : ℝ) < (cell.bn : ℝ) / cell.bd := lt_of_lt_of_le ha0 (hax.trans hxb)
  have hnlo : (an : ℝ) / ad * D ≤ n := by
    have := mul_le_mul_of_nonneg_right hax hD0.le
    rwa [div_mul_cancel₀ _ hD0.ne'] at this
  have hnhi : (n : ℝ) ≤ (cell.bn : ℝ) / cell.bd * D := by
    have := mul_le_mul_of_nonneg_right hxb hD0.le
    rwa [div_mul_cancel₀ _ hD0.ne'] at this
  -- `b ≤ 2 π b + ρ` from the cell test
  have hπb' : (cell.bn : ℝ) / cell.bd ≤ 2 * ((cell.qn : ℝ) / cell.qd) * ((cell.bn : ℝ) / cell.bd) +
      ρ := by
    rw [← hρdef, ← sub_nonpos]
    have h : ((cell.bn * cell.qd * I.rd : ℕ) : ℝ) ≤
        ((2 * cell.qn * cell.bn * I.rd + I.rn * cell.bd * cell.qd : ℕ) : ℝ) := by
      exact_mod_cast hπb
    push_cast at h
    refine nonpos_of_mul_pos (d := (cell.bd : ℝ) * cell.qd * I.rd) (by positivity) ?_
    have e : ((cell.bn : ℝ) / cell.bd - (2 * ((cell.qn : ℝ) / cell.qd) *
        ((cell.bn : ℝ) / cell.bd) + (I.rn : ℝ) / I.rd)) * (cell.bd * cell.qd * I.rd) =
        cell.bn * cell.qd * I.rd - (2 * cell.qn * cell.bn * I.rd + I.rn * cell.bd * cell.qd) := by
      field_simp
    rw [e]; linarith
  have hqπ := q_le_of_cell h2q hRD hnhi hπb' hb0 hρ0.le hn0
  subst hn
  refine clique_of_cellOK hcell hpL hpU (by omega) (by omega) (by omega) hsLn hsLd hsUd J _ hq ?_ ?_ hqπ
  · rw [hsLdef]
    have : (an : ℝ) / ad * (67 / 25) * p * sL ≤ (an : ℝ) / ad * D := by
      rw [← hD]
      have : (p : ℝ) * sL ≤ p * s := mul_le_mul_of_nonneg_left hsL (by positivity)
      nlinarith
    linarith
  · rw [hsUdef]
    have hs0 : 0 ≤ s := by rw [← hs]; exact Real.sqrt_nonneg _
    have hDU : D ≤ 67 / 25 * I.U * sU := by
      rw [← hD]
      have : (p : ℝ) * s ≤ I.U * sU := mul_le_mul hpUR hsU hs0 (by linarith)
      linarith
    calc (Fintype.card W : ℝ) ≤ (cell.bn : ℝ) / cell.bd * D := hnhi
      _ ≤ (cell.bn : ℝ) / cell.bd * (67 / 25 * I.U * sU) := mul_le_mul_of_nonneg_left hDU hb0.le
      _ = 67 / 25 * I.U * sU * ((cell.bn : ℝ) / cell.bd) := by ring

/-- For `p` in an accepted interval, the density `⌊(67/25) p (log₂ p) ^ (1/2)⌋`
is at least `3`. -/
theorem three_le_floor_of_intervalOK {I : Interval} (hI : intervalOK I = true) {p : ℕ}
    (hpL : I.L ≤ p) (hpU : p ≤ I.U) :
    3 ≤ ⌊(67 / 25 : ℝ) * p * Real.sqrt (Real.logb 2 p)⌋₊ := by
  have hI' := hI
  simp only [intervalOK, Bool.and_eq_true, decide_eq_true_eq] at hI'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hsLn⟩, hsLd⟩, -⟩, -⟩, -⟩, hrn⟩, -⟩, -⟩, -⟩ := hI'
  obtain ⟨hsL, -⟩ := sqrt_bounds_of_intervalOK hI hpL hpU
  have hpLR : (I.L : ℝ) ≤ p := by exact_mod_cast hpL
  have hsL0 : (0 : ℝ) < (I.sLn : ℝ) / I.sLd := by
    have : (0 : ℝ) < I.sLn := by exact_mod_cast hsLn
    have : (0 : ℝ) < I.sLd := by exact_mod_cast hsLd
    positivity
  have hρ0 : (0 : ℝ) ≤ (I.rn : ℝ) / I.rd := by positivity
  have hDL : 67 / 25 * I.L * ((I.sLn : ℝ) / I.sLd) ≤
      67 / 25 * p * Real.sqrt (Real.logb 2 p) := by
    have : (I.L : ℝ) * ((I.sLn : ℝ) / I.sLd) ≤ p * Real.sqrt (Real.logb 2 p) :=
      mul_le_mul hpLR hsL hsL0.le (by positivity)
    linarith
  have hρD := rho_bound_of_intervalOK hI hDL
  generalize 67 / 25 * (p : ℝ) * Real.sqrt (Real.logb 2 p) = D at hρD hDL ⊢
  have hD0 : 0 ≤ D := le_trans (by positivity) hDL
  have hD6 : 6 < D := by nlinarith
  have := Nat.lt_floor_add_one D
  have : (3 : ℝ) < ⌊D⌋₊ := by linarith
  exact_mod_cast this.le

/-- For `p` in an accepted interval, density `2.68 p (log₂ p) ^ (1/2)` forces
a `K_p` minor. -/
theorem clique_isIsoMinor_of_intervalOK {I : Interval} (hI : intervalOK I = true) {p : ℕ}
    (hpL : I.L ≤ p) (hpU : p ≤ I.U) {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : ⌊(67 / 25 : ℝ) * p * Real.sqrt (Real.logb 2 p)⌋₊ * Fintype.card V ≤
      G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin p))) (Graph.ofSimpleGraph G) := by
  have hL : 110 ≤ I.L := by
    simp only [intervalOK, Bool.and_eq_true, decide_eq_true_eq] at hI
    exact hI.1.1.1.1.1.1.1.1.1.1.1.1
  have h := clique_isIsoMinor_of_reduced G _ (p - 2) (three_le_floor_of_intervalOK hI hpL hpU) hden
    fun J _ hW hdeg => reduced_clique_of_intervalOK hI hpL hpU J hW hdeg
  rwa [show p - 2 + 2 = p by omega] at h

/-- A chain of accepted intervals that covers `s ≤ p ≤ e`: the first interval
starts at `s`, each next one starts right after the previous one ends, and
the last one ends at `e`. -/
@[expose] def segOK : ℕ → List Interval → ℕ → Bool
  | s, [], e => s == e + 1
  | s, I :: Is, e => (I.L == s) && intervalOK I && segOK (I.U + 1) Is e

/-- Every `p` covered by an accepted chain lies in an accepted interval. -/
theorem exists_interval_of_segOK :
    ∀ (Is : List Interval) (s e : ℕ), segOK s Is e = true → ∀ p, s ≤ p → p ≤ e →
      ∃ I, intervalOK I = true ∧ I.L ≤ p ∧ p ≤ I.U
  | [], s, e, h, p, h1, h2 => by
    simp only [segOK, beq_iff_eq] at h
    omega
  | I :: Is, s, e, h, p, h1, h2 => by
    simp only [segOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hL, hI⟩, hrest⟩ := h
    by_cases hp : p ≤ I.U
    · exact ⟨I, hI, by omega, hp⟩
    · exact exists_interval_of_segOK Is (I.U + 1) e hrest p (by omega) h2

end GraphMinor.Thomason.Uniform
