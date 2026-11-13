module

public import GraphMinor.Compute.GM06Alg34QuadRun
public import GraphMinor.Compute.GM06Alg34ScanLoop

/-!
# Scanning the fourth cuff position

Fix the first three positions and run the proved crossing comparison
once for each fourth position. The counted-loop invariant preserves
the input tables and the three fixed positions. The answer is cleared
exactly when at least one of these comparisons finds a crossing.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The innermost cuff-position loop. -/
def gm06ScanOneProg : Cmd := gm06ScanLoop 123 gm06QuadProg

/-- Whether some fourth cuff position gives a crossing with the fixed three. -/
def gm06ScanOneFlag (x : GM06DrawingData) (L : List (Fin x.n))
    (i j k : Fin L.length) : Bool :=
  gm06AnyPrefix (fun l => if h : l < L.length then
    gm06QuadTest x.division L i j k ⟨l, h⟩ else false) L.length

/-- The innermost scan computes the existential fourth-position test,
preserves all arrays, and costs at most `5 + 207 * cuffLength` steps. -/
theorem gm06ScanOneProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (i j k : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length)
    (hi : s.regs 120 = i.val) (hj : s.regs 121 = j.val) (hkk : s.regs 122 = k.val) :
    ∃ s' t, Exec w gm06ScanOneProg s s' t ∧ t ≤ 5 + L.length * 207 ∧
      s'.regs 0 = (if gm06ScanOneFlag x L i j k then 0 else s.regs 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 123 → q ≠ 124 → q ≠ 125 → s'.regs q = s.regs q) := by
  let P := fun s' : State => s'.arrs 2 = L.map Fin.val ∧
    s'.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0) ∧
    s'.regs 105 = L.length ∧ s'.regs 120 = i.val ∧ s'.regs 121 = j.val ∧ s'.regs 122 = k.val
  let f := fun l => if h : l < L.length then gm06QuadTest x.division L i j k ⟨l, h⟩ else false
  have hp : P s := ⟨hL, hD, hbound, hi, hj, hkk⟩
  have hset : ∀ s' v, P s' → P (s'.setReg 123 v) := by
    intro s' v h; simpa only [P, State.setReg_arrs,
      State.setReg_regs_ne _ _ (by decide : 105 ≠ 123),
      State.setReg_regs_ne _ _ (by decide : 120 ≠ 123),
      State.setReg_regs_ne _ _ (by decide : 121 ≠ 123),
      State.setReg_regs_ne _ _ (by decide : 122 ≠ 123)] using h
  have hb : ∀ l < L.length, ∀ s', P s' → s'.regs 123 = l →
      ∃ s'' t, Exec w gm06QuadProg s' s'' t ∧ t ≤ 200 ∧ P s'' ∧ s''.regs 123 = l ∧
        s''.regs 0 = (if f l then 0 else s'.regs 0) := by
    intro l hl s' hp' hcounter
    obtain ⟨s'', t, hex, ht, hans, harr, hreg⟩ := gm06QuadProg_exec x L i j k ⟨l, hl⟩ hw hk hn hd
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
  obtain ⟨s', t, hex, ht, _, _, hans⟩ := gm06ScanLoop_exec gm06QuadProg f P (by decide)
    (by omega) hk hset (fun _ h => h.2.2.1) hb hp
  refine ⟨s', t, hex, ht, hans, ?_, ?_⟩
  · intro a
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [gm06ScanLoop, forUp, gm06QuadProg, gm06BetweenProg, Cmd.writtenArrs])
  · intro q hq hq123 hq124 hq125
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [gm06ScanLoop, forUp, gm06QuadProg, gm06BetweenProg, Cmd.writtenRegs,
        hq, hq123, hq124, hq125])

end GraphMinor.Compute
