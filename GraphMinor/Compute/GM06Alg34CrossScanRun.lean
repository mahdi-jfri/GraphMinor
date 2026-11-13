module

public import GraphMinor.Compute.GM06Alg34ScanFour

/-!
# Correctness and quartic cost of the RAM crossing scan

The four counted loops visit exactly all four-position comparisons of
the finite cuff scan. Initialize the answer to one and clear it upon
any crossing. The result is the finite cross-free predicate, with an
explicit quartic time bound and no assumptions about scratch registers.
-/

@[expose] public section
namespace GraphMinor.Compute

private theorem gm06AnyPrefix_fin_eq_false {N : ℕ} (f : Fin N → Bool) :
    gm06AnyPrefix (fun v => if h : v < N then f ⟨v, h⟩ else false) N = false ↔
      ∀ i, f i = false := by
  rw [gm06AnyPrefix_eq_false]
  constructor
  · intro h i
    simpa only [dif_pos i.isLt] using h i.val i.isLt
  · intro h i hi
    simpa only [dif_pos hi] using h ⟨i, hi⟩

/-- The nested-loop flag is false exactly when the finite crossing scan accepts. -/
theorem gm06ScanFourFlag_eq_false_iff (x : GM06DrawingData) (L : List (Fin x.n)) :
    gm06ScanFourFlag x L = false ↔ gm06CrossScan x.division L = true := by
  rw [gm06CrossScan_eq_true_iff]
  exact (gm06AnyPrefix_fin_eq_false (fun i => gm06ScanThreeFlag x L i)).trans
    (forall_congr' fun i =>
      (gm06AnyPrefix_fin_eq_false (fun j => gm06ScanTwoFlag x L i j)).trans
        (forall_congr' fun j =>
          (gm06AnyPrefix_fin_eq_false (fun k => gm06ScanOneFlag x L i j k)).trans
            (forall_congr' fun k => gm06AnyPrefix_fin_eq_false
              (fun l => gm06QuadTest x.division L i j k l))))

private theorem gm06_scan_time (n : ℕ) :
    5 + n * (7 + (5 + n * (7 + (5 + n * (7 + (5 + n * 207)))))) ≤
      250 * (n + 1) ^ 4 := by
  ring_nf
  omega

/-- Initialize the answer register and scan all four cuff positions. -/
def gm06CrossScanProg : Cmd := .seq (.assign 0 (.const 1)) gm06ScanFourProg

/-- The RAM crossing scan computes the finite cross-free check in at
most `252 * (cuffLength + 1)^4` steps. All arrays and all registers outside
0 and 120–125 are preserved. -/
theorem gm06CrossScanProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) :
    ∃ s' t, Exec w gm06CrossScanProg s s' t ∧ t ≤ 252 * (L.length + 1) ^ 4 ∧
      s'.regs 0 = (if gm06CrossScan x.division L then 1 else 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 120 → q ≠ 121 → q ≠ 122 → q ≠ 123 →
        q ≠ 124 → q ≠ 125 → s'.regs q = s.regs q) := by
  let s₀ := s.setReg 0 1
  have hex₀ : Exec w (.assign 0 (.const 1)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, show 1 < 2 ^ w by omega])
  obtain ⟨s', t, hex, ht, hans, harr, hreg⟩ := gm06ScanFourProg_exec x L (s := s₀)
    hw hk hn hd hL hD (by simpa [s₀] using hbound)
  have htime := ht.trans (gm06_scan_time L.length)
  have hpow : 1 ≤ (L.length + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  refine ⟨s', 2 + t, .seq hex₀ hex, by omega, ?_, harr, ?_⟩
  · rw [hans]
    have hiff := gm06ScanFourFlag_eq_false_iff x L
    cases hf : gm06ScanFourFlag x L <;> cases hc : gm06CrossScan x.division L <;>
      simp_all [s₀]
  · intro q hq hq120 hq121 hq122 hq123 hq124 hq125
    exact (hreg q hq hq120 hq121 hq122 hq123 hq124 hq125).trans
      (State.setReg_regs_ne _ _ hq)

end GraphMinor.Compute
