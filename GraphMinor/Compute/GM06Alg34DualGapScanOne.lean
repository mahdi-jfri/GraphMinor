module

public import GraphMinor.Compute.GM06Alg34DualGapQuad
public import GraphMinor.Compute.GM06Alg34ScanLoop

/-!
# Scanning primal pairs against two fixed gaps

Fix two gaps and one primal position and run the proved gap-separation comparison
once for each second primal position. The counted-loop invariant preserves
the input tables and the fixed gaps and primal position. The answer is cleared
exactly when at least one of these comparisons separates the gaps.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The innermost cuff-position loop. -/
def gm06GapScanOneProg : Cmd := gm06ScanLoop 123 gm06GapQuadProg

/-- Whether a second primal position separates the fixed gaps. -/
def gm06GapScanOneFlag (x : GM06DrawingData) (L : List (Fin x.n))
    (i j k : Fin L.length) : Bool :=
  gm06AnyPrefix (fun l => if h : l < L.length then
    gm06GapQuadTest x L i j k ⟨l, h⟩ else false) L.length

/-- The innermost scan computes the existential second-position test,
preserves all arrays, and costs at most `5 + 207 * cuffLength` steps. -/
theorem gm06GapScanOneProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (i j k : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w) (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length)
    (hi : s.regs 120 = i.val) (hj : s.regs 121 = j.val) (hkk : s.regs 122 = k.val) :
    ∃ s' t, Exec w gm06GapScanOneProg s s' t ∧ t ≤ 5 + L.length * 207 ∧
      s'.regs 0 = (if gm06GapScanOneFlag x L i j k then 0 else s.regs 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 123 → q ≠ 124 → q ≠ 125 → s'.regs q = s.regs q) := by
  let P := fun s' : State => s'.arrs 2 = L.map Fin.val ∧
    s'.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0) ∧
    s'.regs 105 = L.length ∧ s'.regs 120 = i.val ∧ s'.regs 121 = j.val ∧ s'.regs 122 = k.val
  let f := fun l => if h : l < L.length then gm06GapQuadTest x L i j k ⟨l, h⟩ else false
  have hp : P s := ⟨hL, hD, hbound, hi, hj, hkk⟩
  have hset : ∀ s' v, P s' → P (s'.setReg 123 v) := by
    intro s' v h; simpa only [P, State.setReg_arrs,
      State.setReg_regs_ne _ _ (by decide : 105 ≠ 123),
      State.setReg_regs_ne _ _ (by decide : 120 ≠ 123),
      State.setReg_regs_ne _ _ (by decide : 121 ≠ 123),
      State.setReg_regs_ne _ _ (by decide : 122 ≠ 123)] using h
  have hb : ∀ l < L.length, ∀ s', P s' → s'.regs 123 = l →
      ∃ s'' t, Exec w gm06GapQuadProg s' s'' t ∧ t ≤ 200 ∧ P s'' ∧ s''.regs 123 = l ∧
        s''.regs 0 = (if f l then 0 else s'.regs 0) := by
    intro l hl s' hp' hcounter
    obtain ⟨s'', t, hex, ht, hans, harr, hreg⟩ := gm06GapQuadProg_exec x L i j k ⟨l, hl⟩ hw hk hdouble hn hd
      hp'.1 hp'.2.1 hp'.2.2.2.1 hp'.2.2.2.2.1 hp'.2.2.2.2.2 hcounter
    have hp'' : P s'' := by
      dsimp only [P]
      rw [harr 2, harr 3, hreg 105 (by decide) (by decide) (by decide),
        hreg 120 (by decide) (by decide) (by decide),
        hreg 121 (by decide) (by decide) (by decide),
        hreg 122 (by decide) (by decide) (by decide)]
      exact hp'
    exact ⟨s'', t, hex, ht, hp'',
      (hreg 123 (by decide) (by decide) (by decide)).trans hcounter,
      by simpa only [f, dif_pos hl] using hans⟩
  obtain ⟨s', t, hex, ht, _, _, hans⟩ := gm06ScanLoop_exec gm06GapQuadProg f P (by decide)
    (by omega) hk hset (fun _ h => h.2.2.1) hb hp
  refine ⟨s', t, hex, ht, hans, ?_, ?_⟩
  · intro a
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [gm06ScanLoop, forUp, gm06GapQuadProg, gm06BetweenExpressionsProg, Cmd.writtenArrs])
  · intro q hq hq123 hq124 hq125
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [gm06ScanLoop, forUp, gm06GapQuadProg, gm06BetweenExpressionsProg, Cmd.writtenRegs,
        hq, hq123, hq124, hq125])

end GraphMinor.Compute
