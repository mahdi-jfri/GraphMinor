module

public import GraphMinor.Compute.GM06Alg34ScanTwo

/-!
# Scanning 3 cuff positions

Nest the verified scan of 2 positions inside one counted loop.
The invariant preserves the supplied tables and the fixed outer positions.
The resulting flag records whether any of the visited comparisons found
a crossing, and the time bound follows by summing the inner bound.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Scan the final 3 cuff positions. -/
def gm06ScanThreeProg : Cmd := gm06ScanLoop 121 gm06ScanTwoProg

/-- Whether a crossing occurs for some choice of the final 3 positions. -/
def gm06ScanThreeFlag (x : GM06DrawingData) (L : List (Fin x.n))
    (i : Fin L.length) : Bool :=
  gm06AnyPrefix (fun v => if hv : v < L.length then
    gm06ScanTwoFlag x L i ⟨v, hv⟩ else false) L.length

/-- The concrete nested scan computes its crossing flag and preserves
all arrays and all registers outside its counters and flags. -/
theorem gm06ScanThreeProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (i : Fin L.length) {s : State}
    (hw : 2 < 2 ^ w) (hk : L.length < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length)
    (hi : s.regs 120 = i.val)
    : ∃ s' t, Exec w gm06ScanThreeProg s s' t ∧ t ≤ 5 + L.length * (7 + (5 + L.length * (7 + (5 + L.length * 207)))) ∧
      s'.regs 0 = (if gm06ScanThreeFlag x L i then 0 else s.regs 0) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 121 → q ≠ 122 → q ≠ 123 → q ≠ 124 → q ≠ 125 → s'.regs q = s.regs q) := by
  let P := fun s' : State => s'.arrs 2 = L.map Fin.val ∧
    s'.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0) ∧
    s'.regs 105 = L.length ∧ s'.regs 120 = i.val
  let f := fun v => if hv : v < L.length then gm06ScanTwoFlag x L i ⟨v, hv⟩ else false
  have hp : P s := ⟨hL, hD, hbound, hi⟩
  have hset : ∀ s' v, P s' → P (s'.setReg 121 v) := by
    intro s' v h; simpa only [P, State.setReg_arrs,
      State.setReg_regs_ne _ _ (by decide : 105 ≠ 121),
      State.setReg_regs_ne _ _ (by decide : 120 ≠ 121)] using h
  have hb : ∀ v < L.length, ∀ s', P s' → s'.regs 121 = v →
      ∃ s'' t, Exec w gm06ScanTwoProg s' s'' t ∧ t ≤ 5 + L.length * (7 + (5 + L.length * 207)) ∧ P s'' ∧ s''.regs 121 = v ∧
        s''.regs 0 = (if f v then 0 else s'.regs 0) := by
    intro v hv s' hp' hcounter
    obtain ⟨s'', t, hex, ht, hans, harr, hreg⟩ := gm06ScanTwoProg_exec x L i ⟨v, hv⟩ hw hk hn hd
      hp'.1 hp'.2.1 hp'.2.2.1 hp'.2.2.2 hcounter
    have hp'' : P s'' := by
      dsimp only [P]
      rw [harr 2, harr 3, hreg 105 (by decide) (by decide) (by decide) (by decide) (by decide),
        hreg 120 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hp'
    exact ⟨s'', t, hex, ht, hp'',
      (hreg 121 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcounter,
      by simpa only [f, dif_pos hv] using hans⟩
  obtain ⟨s', t, hex, ht, _, _, hans⟩ := gm06ScanLoop_exec gm06ScanTwoProg f P (by decide)
    (by omega) hk hset (fun _ h => h.2.2.1) hb hp
  refine ⟨s', t, hex, ht, hans, ?_, ?_⟩
  · intro a
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [gm06ScanLoop, forUp, gm06ScanTwoProg, gm06ScanOneProg, gm06QuadProg, gm06BetweenProg, Cmd.writtenArrs])
  · intro q hq hq121 hq122 hq123 hq124 hq125
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [gm06ScanLoop, forUp, gm06ScanTwoProg, gm06ScanOneProg, gm06QuadProg, gm06BetweenProg, Cmd.writtenRegs,
        hq, hq121, hq122, hq123, hq124, hq125])

end GraphMinor.Compute
